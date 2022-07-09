## [2018-09-29 09:32:55-04:00](https://github.com/leanprover-community/mathlib/commit/b5d8fbe)
fix(data/nat/prime): fix build, add simp attr
#### Estimated changes
Modified data/nat/basic.lean

Modified data/nat/prime.lean



## [2018-09-29 07:48:43-04:00](https://github.com/leanprover-community/mathlib/commit/6997caf)
feat(data/nat/basic): remove superfluous assumptions
#### Estimated changes
Modified data/nat/basic.lean
- \+ *lemma* pred_le_iff
- \+ *lemma* lt_pred_iff
- \- *lemma* lt_pred_of_succ_lt
- \+/\- *theorem* sub_le_left_iff_le_add
- \+/\- *theorem* sub_le_right_iff_le_add
- \+/\- *theorem* sub_le_left_iff_le_add
- \+/\- *theorem* sub_le_right_iff_le_add



## [2018-09-24 21:31:25+02:00](https://github.com/leanprover-community/mathlib/commit/6434658)
feat(analysis/topology): locally compact spaces and the compact-open topology
#### Estimated changes
Created analysis/topology/compact_open.lean
- \+ *lemma* locally_compact_of_compact_nhds
- \+ *lemma* locally_compact_of_compact
- \+ *lemma* continuous_induced
- \+ *lemma* continuous_ev
- \+ *lemma* image_coev
- \+ *lemma* continuous_coev
- \+ *def* compact_open_gen
- \+ *def* compact_open
- \+ *def* continuous_map.induced
- \+ *def* ev
- \+ *def* coev

Modified analysis/topology/topological_space.lean
- \+ *lemma* compact_inter
- \+ *lemma* compact_diff
- \+/\- *lemma* compact_of_is_closed_subset
- \+/\- *lemma* compact_of_is_closed_subset



## [2018-09-24 15:33:35+02:00](https://github.com/leanprover-community/mathlib/commit/68acd76)
feat(group_theory/perm): perm.fintype and card_perm (closed [#366](https://github.com/leanprover-community/mathlib/pull/366))
#### Estimated changes
Modified data/fintype.lean
- \+ *lemma* length_perms_of_list
- \+ *lemma* mem_perms_of_list_of_mem
- \+ *lemma* mem_of_mem_perms_of_list
- \+ *lemma* mem_perms_of_list_iff
- \+ *lemma* nodup_perms_of_list
- \+ *lemma* mem_perms_of_finset_iff
- \+ *lemma* card_perms_of_finset
- \+ *lemma* fintype.card_perm
- \+ *lemma* fintype.card_equiv
- \+ *def* perms_of_list
- \+ *def* perms_of_finset
- \+ *def* fintype_perm

Modified group_theory/perm.lean



## [2018-09-24 08:48:09+02:00](https://github.com/leanprover-community/mathlib/commit/cbfe372)
fix(category_theory/functor): make obj_eq_coe a rfl-lemma
This is needed to, for example, let `dsimp` turn `𝟙 (F.obj X)` into `𝟙 (F X)`.
#### Estimated changes
Modified category_theory/functor.lean
- \+/\- *lemma* obj_eq_coe
- \+/\- *lemma* obj_eq_coe



## [2018-09-23 19:54:43-04:00](https://github.com/leanprover-community/mathlib/commit/ce43eae)
fix(topological_structures): fix imports
#### Estimated changes
Modified analysis/topology/topological_structures.lean



## [2018-09-23 18:55:03-04:00](https://github.com/leanprover-community/mathlib/commit/8c76cac)
fix(*): tweaks to 7944cc
#### Estimated changes
Modified analysis/topology/topological_space.lean

Modified linear_algebra/submodule.lean
- \+ *def* le_order_embedding
- \+ *def* lt_order_embedding
- \- *def* submodule_lt_equiv

Modified order/basic.lean

Modified order/order_iso.lean
- \+ *def* lt_embedding_of_le_embedding



## [2018-09-23 09:40:57+02:00](https://github.com/leanprover-community/mathlib/commit/e7c7552)
feat(analysis/topology/continuity): compactness and embeddings
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* embedding.continuous
- \+ *lemma* compact_iff_compact_image_of_embedding
- \+ *lemma* quotient_map.continuous
- \+ *lemma* compact_iff_compact_in_subtype
- \+ *lemma* compact_iff_compact_univ



## [2018-09-23 09:40:57+02:00](https://github.com/leanprover-community/mathlib/commit/ab20b5f)
style(analysis/topology/continuity): minor reorganizations
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+/\- *lemma* nhds_induced_eq_comap
- \+/\- *lemma* map_nhds_induced_eq
- \+/\- *lemma* closure_induced
- \+/\- *lemma* embedding.map_nhds_eq
- \+/\- *lemma* embedding.tendsto_nhds_iff
- \+/\- *lemma* embedding.continuous_iff
- \+/\- *lemma* quotient_map.continuous_iff
- \+/\- *lemma* closure_subtype
- \+/\- *lemma* nhds_induced_eq_comap
- \+/\- *lemma* map_nhds_induced_eq
- \+/\- *lemma* embedding.map_nhds_eq
- \+/\- *lemma* closure_induced
- \+/\- *lemma* embedding.tendsto_nhds_iff
- \+/\- *lemma* embedding.continuous_iff
- \+/\- *lemma* closure_subtype
- \+/\- *lemma* quotient_map.continuous_iff
- \+/\- *theorem* is_open_induced
- \+/\- *theorem* is_open_induced



## [2018-09-21 17:57:07+02:00](https://github.com/leanprover-community/mathlib/commit/ca7f118)
fix(docs/tactics.md): missing backquote, formatting
I think I never previewed when I updated the `linarith` doc before, sorry.
#### Estimated changes
Modified docs/tactics.md



## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/9a7a611)
feat(analysis/topology, order/filter): theorems for the applicative structure on filter; add list topology
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* nhds_mk_of_nhds
- \+ *lemma* nhds_list
- \+/\- *lemma* quotient_dense_of_dense
- \+/\- *lemma* quotient_dense_of_dense

Modified order/filter.lean
- \+ *lemma* mem_map_sets_iff
- \+ *lemma* comap_supr
- \+ *lemma* comap_Sup
- \+ *lemma* le_map
- \+/\- *lemma* mem_pure_sets
- \+ *lemma* singleton_mem_pure_sets
- \+/\- *lemma* pure_neq_bot
- \+ *lemma* mem_seq_sets_def
- \+ *lemma* mem_seq_sets_iff
- \+ *lemma* seq_mem_seq_sets
- \+ *lemma* le_seq
- \+/\- *lemma* seq_mono
- \+ *lemma* pure_seq_eq_map
- \+ *lemma* map_pure
- \+ *lemma* seq_pure
- \+ *lemma* seq_assoc
- \+ *lemma* prod_map_seq_comm
- \+ *lemma* {l}
- \+ *lemma* mem_traverse_sets
- \+ *lemma* mem_traverse_sets_iff
- \+ *lemma* sequence_mono
- \+/\- *lemma* seq_mono
- \+/\- *lemma* mem_pure_sets
- \+/\- *lemma* pure_neq_bot



## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/568a15f)
refactor(category/traversable): proofs about list instance for traverse, simplify multiset.traverse
#### Estimated changes
Modified category/traversable/instances.lean
- \+ *lemma* traverse_nil
- \+ *lemma* traverse_cons
- \+/\- *lemma* traverse_append
- \+ *lemma* mem_traverse
- \+/\- *lemma* traverse_append

Modified data/list/basic.lean
- \+ *lemma* forall₂.mp
- \+ *lemma* forall₂.flip
- \+ *lemma* forall₂_and_left
- \- *lemma* forall₂_flip

Modified data/list/perm.lean

Modified data/multiset.lean
- \- *lemma* coe_append_eq_add_coe
- \- *lemma* coe_list_cons_eq_cons_coe
- \- *lemma* coe_traverse_cons
- \- *lemma* coe_traverse_cons_swap
- \+/\- *def* traverse
- \+/\- *def* traverse



## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/618aac9)
feat(data/set): add set.seq (use it for the appliative.seq instance for set)
#### Estimated changes
Modified data/set/lattice.lean
- \+ *lemma* seq_def
- \+/\- *lemma* mem_seq_iff
- \+ *lemma* seq_subset
- \+ *lemma* seq_mono
- \+ *lemma* singleton_seq
- \+ *lemma* seq_singleton
- \+ *lemma* seq_seq
- \+ *lemma* image_seq
- \+ *lemma* prod_eq_seq
- \+ *lemma* prod_image_seq_comm
- \+ *lemma* seq_eq_set_seq
- \+ *lemma* pure_def
- \+/\- *lemma* mem_seq_iff
- \+ *def* seq



## [2018-09-21 17:46:47+02:00](https://github.com/leanprover-community/mathlib/commit/a62ec36)
refactor(order/filter): remove monad instance on filters; add applicative instance inducing the expected products
#### Estimated changes
Modified analysis/topology/topological_space.lean

Modified order/filter.lean
- \- *lemma* mem_return_sets
- \+ *def* seq



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
- \+ *def* pi_equiv_subtype_sigma

Modified data/equiv/list.lean
- \+ *def* fintype_arrow
- \+ *def* fintype_pi

Modified data/finset.lean
- \+ *lemma* set_of_mem

Modified data/fintype.lean
- \+ *lemma* coe_univ

Modified data/set/basic.lean
- \+ *lemma* sep_set_of
- \+ *lemma* set_of_mem
- \+ *lemma* sep_univ
- \+ *lemma* pi_empty_index
- \+ *lemma* pi_insert_index
- \+ *lemma* pi_singleton_index
- \+ *lemma* pi_if
- \+ *def* pi

Modified data/set/countable.lean
- \+ *lemma* countable_pi

Modified data/set/lattice.lean
- \+ *lemma* pi_def

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
- \+/\- *theorem* coe_coe_fn
- \+/\- *theorem* coe_coe_fn

Modified set_theory/cofinality.lean

Modified set_theory/ordinal.lean
- \+/\- *theorem* coe_coe_fn
- \+/\- *theorem* coe_coe_fn
- \+/\- *theorem* coe_coe_fn'
- \+/\- *theorem* coe_coe_fn
- \+/\- *theorem* coe_coe_fn
- \+/\- *theorem* coe_coe_fn'



## [2018-09-21 00:09:04-04:00](https://github.com/leanprover-community/mathlib/commit/2485d8e)
fix(*): fix build
#### Estimated changes
Modified analysis/topology/topological_space.lean

Modified linear_algebra/basic.lean

Modified linear_algebra/submodule.lean

Modified logic/function.lean
- \+/\- *theorem* inv_fun_on_eq'
- \+/\- *theorem* inv_fun_on_eq'

Modified order/basic.lean
- \+/\- *def* order.preimage
- \+/\- *def* order.preimage



## [2018-09-20 19:46:48-04:00](https://github.com/leanprover-community/mathlib/commit/a4108eb)
fix(algebra/pi_instances): bugfix
#### Estimated changes
Modified algebra/pi_instances.lean

Modified linear_algebra/prod_module.lean



## [2018-09-20 19:21:02-04:00](https://github.com/leanprover-community/mathlib/commit/9aec1d1)
refactor(algebra/pi_instances): move prod instances to pi_instances file
#### Estimated changes
Modified algebra/group.lean

Modified algebra/pi_instances.lean
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
- \+ *def* inl
- \+ *def* inr

Modified linear_algebra/prod_module.lean
- \- *lemma* fst_mul
- \- *lemma* snd_mul
- \- *lemma* fst_one
- \- *lemma* snd_one
- \- *lemma* fst_inv
- \- *lemma* snd_inv
- \- *lemma* fst_prod
- \- *lemma* snd_prod
- \- *lemma* injective_inl
- \- *lemma* injective_inr
- \- *lemma* inl_eq_inl
- \- *lemma* inr_eq_inr
- \- *lemma* inl_eq_inr
- \- *lemma* inr_eq_inl
- \- *lemma* fst_inl
- \- *lemma* snd_inl
- \- *lemma* fst_inr
- \- *lemma* snd_inr
- \- *def* inl
- \- *def* inr



## [2018-09-20 17:49:40-04:00](https://github.com/leanprover-community/mathlib/commit/3ba4e82)
feat(data/set/finite): finite_subset_Union, disjoint_mono
#### Estimated changes
Modified data/set/finite.lean
- \+ *lemma* finite_subset_Union
- \+ *theorem* finite_range

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
- \+ *lemma* diff_self

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
- \+ *theorem* coe_fn_coe_trans
- \+ *theorem* coe_fn_coe_base
- \+ *theorem* coe_sort_coe_trans
- \+ *theorem* coe_sort_coe_base



## [2018-09-20 17:44:42-04:00](https://github.com/leanprover-community/mathlib/commit/0d6bae7)
refactor(order/filter): move directed to order.basic, swap definition
directed means containing upper bounds, not lower bounds
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *theorem* directed.finset_le

Modified order/basic.lean
- \+ *theorem* is_refl.swap
- \+/\- *theorem* is_irrefl.swap
- \+/\- *theorem* is_trans.swap
- \+ *theorem* is_antisymm.swap
- \+ *theorem* is_asymm.swap
- \+ *theorem* is_total.swap
- \+/\- *theorem* is_trichotomous.swap
- \+ *theorem* is_preorder.swap
- \+/\- *theorem* is_strict_order.swap
- \+ *theorem* is_partial_order.swap
- \+ *theorem* is_total_preorder.swap
- \+ *theorem* is_linear_order.swap
- \+ *theorem* directed_on_iff_directed
- \+ *theorem* directed_comp
- \+ *theorem* directed_mono
- \+/\- *theorem* is_irrefl.swap
- \+/\- *theorem* is_trans.swap
- \+/\- *theorem* is_strict_order.swap
- \+/\- *theorem* is_trichotomous.swap
- \+ *def* order.preimage
- \+ *def* directed
- \+ *def* directed_on

Modified order/filter.lean
- \+/\- *lemma* directed_on_Union
- \+/\- *lemma* infi_sets_eq
- \+/\- *lemma* infi_sets_eq'
- \+/\- *lemma* map_infi_eq
- \+/\- *lemma* directed_on_Union
- \+/\- *lemma* infi_sets_eq
- \+/\- *lemma* infi_sets_eq'
- \+/\- *lemma* map_infi_eq
- \+/\- *theorem* directed_of_chain
- \+/\- *theorem* directed_of_chain
- \- *def* directed
- \- *def* directed_on

Modified order/order_iso.lean
- \- *def* order.preimage



## [2018-09-20 17:41:18-04:00](https://github.com/leanprover-community/mathlib/commit/e054277)
feat(order/bounded_lattice): eq_top_mono
#### Estimated changes
Modified order/bounded_lattice.lean
- \+ *theorem* eq_top_mono
- \+ *theorem* eq_bot_mono



## [2018-09-20 17:40:57-04:00](https://github.com/leanprover-community/mathlib/commit/84024be)
feat(order/zorn): more zorn's lemma variants
#### Estimated changes
Modified order/zorn.lean
- \+ *theorem* chain.directed_on
- \+ *theorem* zorn_subset



## [2018-09-20 16:00:07+02:00](https://github.com/leanprover-community/mathlib/commit/1da8cc5)
feat(analysis/topology/uniform_structure): uniform_space.comap extra
lemmas
#### Estimated changes
Modified analysis/topology/uniform_space.lean
- \+ *lemma* uniform_space_comap_id
- \+ *lemma* uniform_space.comap_comap_comp
- \+ *lemma* uniform_continuous_iff



## [2018-09-20 10:45:52+02:00](https://github.com/leanprover-community/mathlib/commit/d0f1b21)
feat(data/prod): add id_prod
#### Estimated changes
Modified data/prod.lean
- \+ *lemma* id_prod



## [2018-09-19 11:24:25+02:00](https://github.com/leanprover-community/mathlib/commit/318ec36)
feat(group_theory/perm): sign_cycle and sign_bij ([#347](https://github.com/leanprover-community/mathlib/pull/347))
#### Estimated changes
Modified algebra/group_power.lean
- \+ *lemma* units_pow_two
- \+ *lemma* units_pow_eq_pow_mod_two

Modified data/equiv/basic.lean
- \+/\- *theorem* swap_apply_left
- \+/\- *theorem* swap_apply_right
- \+/\- *theorem* swap_swap
- \+/\- *theorem* swap_apply_left
- \+/\- *theorem* swap_apply_right
- \+/\- *theorem* swap_swap

Modified group_theory/perm.lean
- \+ *lemma* eq_inv_iff_eq
- \+ *lemma* inv_eq_iff_eq
- \+ *lemma* exists_int_pow_eq_of_is_cycle
- \+ *lemma* of_subtype_subtype_perm
- \+ *lemma* of_subtype_apply_of_not_mem
- \+ *lemma* mem_iff_of_subtype_apply_mem
- \+ *lemma* subtype_perm_of_subtype
- \+ *lemma* pow_apply_eq_of_apply_apply_eq_self_nat
- \+ *lemma* pow_apply_eq_of_apply_apply_eq_self_int
- \+ *lemma* mem_support
- \+ *lemma* swap_mul_eq_mul_swap
- \+ *lemma* mul_swap_eq_swap_mul
- \+ *lemma* is_swap_of_subtype
- \+ *lemma* sign_mul
- \+ *lemma* sign_one
- \+ *lemma* sign_inv
- \+ *lemma* sign_aux3_symm_trans_trans
- \+ *lemma* sign_symm_trans_trans
- \+ *lemma* sign_prod_list_swap
- \+ *lemma* sign_subtype_perm
- \+ *lemma* sign_of_subtype
- \+ *lemma* sign_eq_sign_of_equiv
- \+ *lemma* sign_bij
- \+ *lemma* is_cycle_swap
- \+ *lemma* is_cycle_inv
- \+ *lemma* is_cycle_swap_mul_aux₁
- \+ *lemma* is_cycle_swap_mul_aux₂
- \+ *lemma* eq_swap_of_is_cycle_of_apply_apply_eq_self
- \+ *lemma* is_cycle_swap_mul
- \+ *lemma* support_swap_mul_cycle
- \+ *lemma* support_swap
- \+ *lemma* card_support_swap
- \+ *lemma* sign_cycle
- \+ *def* subtype_perm
- \+ *def* of_subtype
- \+ *def* is_cycle
- \+ *def* support



## [2018-09-19 11:19:01+02:00](https://github.com/leanprover-community/mathlib/commit/ad9309f)
feat(data/polynomial): C_inj and dvd_iff_is_root ([#359](https://github.com/leanprover-community/mathlib/pull/359))
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* C_inj
- \+ *lemma* dvd_iff_is_root



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
- \+/\- *theorem* zero_val
- \+/\- *theorem* neg_val
- \+/\- *theorem* add_val
- \+/\- *theorem* zero_val
- \+/\- *theorem* neg_val
- \+/\- *theorem* add_val



## [2018-09-18 17:03:51-04:00](https://github.com/leanprover-community/mathlib/commit/5260ab8)
feat(ring_theory/matrix): diagonal matrices
Joint work with Johan Commelin
#### Estimated changes
Modified ring_theory/matrix.lean
- \+ *theorem* diagonal_val_eq
- \+ *theorem* diagonal_val_ne
- \+ *theorem* diagonal_val_ne'
- \+ *theorem* diagonal_zero
- \+ *theorem* diagonal_one
- \+/\- *theorem* one_val_eq
- \+/\- *theorem* one_val_ne
- \+/\- *theorem* one_val_ne'
- \+ *theorem* diagonal_add
- \+/\- *theorem* mul_val
- \+ *theorem* mul_eq_mul
- \+/\- *theorem* mul_val'
- \+ *theorem* diagonal_neg
- \+ *theorem* diagonal_mul
- \+ *theorem* mul_diagonal
- \+ *theorem* diagonal_mul_diagonal'
- \+ *theorem* diagonal_mul_diagonal
- \+/\- *theorem* one_val_eq
- \+/\- *theorem* one_val_ne
- \+/\- *theorem* one_val_ne'
- \+/\- *theorem* mul_val
- \+/\- *theorem* mul_val'
- \+ *def* diagonal



## [2018-09-18 13:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/a72807f)
feat(ring_theory/matrix): (finally!) adding matrices ([#334](https://github.com/leanprover-community/mathlib/pull/334))
Joint work by: Ellen Arlt, Blair Shi, Sean Leather, Scott Morrison, Johan Commelin, Kenny Lau, Johannes Hölzl, Mario Carneiro
#### Estimated changes
Created ring_theory/matrix.lean
- \+ *theorem* ext_iff
- \+ *theorem* ext
- \+ *theorem* zero_val
- \+ *theorem* one_val
- \+ *theorem* one_val_eq
- \+ *theorem* one_val_ne
- \+ *theorem* one_val_ne'
- \+ *theorem* neg_val
- \+ *theorem* add_val
- \+ *theorem* mul_val
- \+ *theorem* mul_val'
- \+ *theorem* mul_zero
- \+ *theorem* zero_mul
- \+ *theorem* mul_add
- \+ *theorem* add_mul
- \+ *def* matrix



## [2018-09-18 15:20:04+02:00](https://github.com/leanprover-community/mathlib/commit/7dedf3c)
feat(analysis/topology): injective_separated_pure_cauchy
#### Estimated changes
Modified analysis/topology/uniform_space.lean
- \+ *lemma* injective_separated_pure_cauchy

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
- \+/\- *lemma* fpow_inv
- \+/\- *lemma* fpow_add
- \+/\- *lemma* pow_le_max_of_min_le
- \+/\- *lemma* fpow_inv
- \+/\- *lemma* fpow_add
- \+/\- *lemma* pow_le_max_of_min_le
- \+/\- *def* fpow
- \+/\- *def* fpow

Modified algebra/order_functions.lean
- \+/\- *lemma* min_add
- \+/\- *lemma* min_sub
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
- \+ *def* ulift_down
- \+ *def* ulift_up

Modified category_theory/natural_isomorphism.lean
- \+ *def* ulift_down_up
- \+ *def* ulift_up_down



## [2018-09-15 17:30:09+02:00](https://github.com/leanprover-community/mathlib/commit/04c4abf)
fix(algebra/group): fix bit0_zero to use (0 : alpha) not (0 : nat)
#### Estimated changes
Modified algebra/group.lean



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
- \+ *theorem* prod_punit_apply
- \+ *theorem* punit_prod_apply
- \- *theorem* prod_unit_apply
- \- *theorem* unit_prod_apply
- \+ *def* empty_equiv_pempty
- \+ *def* pempty_of_not_nonempty
- \+ *def* true_equiv_punit
- \+ *def* arrow_punit_equiv_punit
- \+ *def* punit_arrow_equiv
- \+ *def* empty_arrow_equiv_punit
- \+ *def* pempty_arrow_equiv_punit
- \+ *def* false_arrow_equiv_punit
- \+ *def* prod_punit
- \+ *def* punit_prod
- \+ *def* bool_equiv_punit_sum_punit
- \+ *def* option_equiv_sum_punit
- \+ *def* nat_equiv_nat_sum_punit
- \+ *def* nat_sum_punit_equiv_nat
- \+ *def* equiv_sigma_subtype
- \- *def* arrow_unit_equiv_unit
- \- *def* unit_arrow_equiv
- \- *def* empty_arrow_equiv_unit
- \- *def* pempty_arrow_equiv_unit
- \- *def* false_arrow_equiv_unit
- \- *def* prod_unit
- \- *def* unit_prod
- \- *def* bool_equiv_unit_sum_unit
- \- *def* option_equiv_sum_unit
- \- *def* nat_equiv_nat_sum_unit
- \- *def* nat_sum_unit_equiv_nat

Modified data/equiv/encodable.lean

Modified data/fintype.lean
- \+ *theorem* fintype.univ_punit
- \+ *theorem* fintype.card_punit

Modified linear_algebra/basic.lean
- \+ *lemma* is_basis.linear_equiv

Modified linear_algebra/dimension.lean
- \+ *theorem* basis_le_span
- \+ *theorem* mk_eq_mk_of_basis
- \+ *theorem* dim_eq_of_linear_equiv
- \+ *theorem* dim_prod
- \+ *theorem* dim_quotient
- \+ *theorem* dim_im_add_dim_ker

Modified linear_algebra/quotient_module.lean
- \+ *theorem* quotient_prod_linear_equiv

Modified set_theory/cardinal.lean
- \+ *lemma* finset_card
- \+ *theorem* mk_empty
- \+ *theorem* mk_pempty
- \+ *theorem* mk_empty'
- \+ *theorem* mk_plift_false
- \+ *theorem* mk_unit
- \+ *theorem* mk_punit
- \+ *theorem* mk_singleton
- \+ *theorem* mk_plift_true
- \+ *theorem* mk_bool
- \+ *theorem* mk_Prop
- \+ *theorem* mk_option
- \+ *theorem* mk_eq_of_injective
- \+ *theorem* mk_list_eq_sum_pow
- \+ *theorem* mk_Union_le_sum_mk
- \+ *theorem* mk_union_add_mk_inter
- \+ *theorem* mk_union_of_disjiont

Modified set_theory/cofinality.lean

Modified set_theory/ordinal.lean
- \+ *theorem* pow_le
- \+ *theorem* mk_list_eq_mk



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
- \+ *lemma* int.coe_nat_bit0
- \+ *lemma* int.coe_nat_bit1
- \+ *lemma* nat_eq_subst
- \+ *lemma* nat_le_subst
- \+ *lemma* nat_lt_subst

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
- \+ *lemma* concrete_category_id
- \+ *lemma* concrete_category_comp

Modified category_theory/examples/topological_spaces.lean
- \+ *lemma* map_id_obj
- \+/\- *def* nbhd
- \+/\- *def* nbhds
- \+ *def* map
- \+ *def* map_id
- \+ *def* map_iso
- \+ *def* map_iso_id
- \+/\- *def* nbhd
- \+/\- *def* nbhds

Modified category_theory/natural_isomorphism.lean
- \+ *lemma* mk_app
- \+ *lemma* mk_app'
- \+/\- *lemma* naturality_1
- \+/\- *lemma* naturality_2
- \+/\- *lemma* naturality_1
- \+/\- *lemma* naturality_2
- \+/\- *def* of_components
- \+ *def* of_components.app
- \+ *def* of_components.hom_app
- \+ *def* of_components.inv_app
- \+ *def* id_comp
- \+ *def* comp_id
- \+ *def* assoc
- \+/\- *def* of_components



## [2018-09-13 13:42:52-04:00](https://github.com/leanprover-community/mathlib/commit/a770ee5)
fix(data/padics/padic_rationals): fix proof
#### Estimated changes
Modified data/padics/padic_rationals.lean
- \+/\- *lemma* stationary
- \+/\- *lemma* norm_nonzero_of_not_equiv_zero
- \+/\- *lemma* cast_eq_of_rat
- \+/\- *lemma* zero_def
- \+/\- *lemma* sub_rev
- \+/\- *lemma* exi_rat_seq_conv
- \+/\- *lemma* stationary
- \+/\- *lemma* norm_nonzero_of_not_equiv_zero
- \+/\- *lemma* cast_eq_of_rat
- \+/\- *lemma* zero_def
- \+/\- *lemma* sub_rev
- \+/\- *lemma* exi_rat_seq_conv
- \+/\- *theorem* norm_equiv
- \+/\- *theorem* nonarchimedean
- \+/\- *theorem* rat_dense
- \+/\- *theorem* complete
- \+/\- *theorem* norm_equiv
- \+/\- *theorem* nonarchimedean
- \+/\- *theorem* rat_dense
- \+/\- *theorem* complete
- \+/\- *def* mk
- \+/\- *def* padic_norm_e
- \+/\- *def* mk
- \+/\- *def* padic_norm_e



## [2018-09-13 12:28:42-04:00](https://github.com/leanprover-community/mathlib/commit/46502df)
feat(algebra/ordered_ring): mul_self_pos
#### Estimated changes
Modified algebra/ordered_ring.lean
- \+/\- *lemma* mul_le_one
- \+ *lemma* mul_self_pos
- \+/\- *lemma* mul_le_one



## [2018-09-13 12:07:41-04:00](https://github.com/leanprover-community/mathlib/commit/bebe170)
feat(data/int/order): delete int.order and prove all commented out lemmas ([#348](https://github.com/leanprover-community/mathlib/pull/348))
#### Estimated changes
Modified algebra/archimedean.lean

Modified data/int/basic.lean
- \+ *lemma* coe_nat_succ_pos
- \+ *lemma* units_inv_eq_self

Deleted data/int/order.lean
- \- *lemma* of_nat_le_of_nat_of_le
- \- *lemma* le_of_of_nat_le_of_nat
- \- *theorem* coe_nat_nonneg
- \- *theorem* coe_nat_pos
- \- *theorem* coe_nat_succ_pos
- \- *theorem* exists_eq_coe_nat
- \- *theorem* exists_eq_neg_coe_nat
- \- *theorem* coe_nat_nat_abs_of_nonneg
- \- *theorem* coe_nat_nat_abs_of_nonpos
- \- *theorem* coe_nat_nat_abs
- \- *theorem* nat_abs_abs
- \- *theorem* lt_of_add_one_le
- \- *theorem* add_one_le_of_lt
- \- *theorem* lt_add_one_of_le
- \- *theorem* le_of_lt_add_one
- \- *theorem* sub_one_le_of_lt
- \- *theorem* lt_of_sub_one_le
- \- *theorem* le_sub_one_of_lt
- \- *theorem* lt_of_le_sub_one
- \- *theorem* sign_of_succ
- \- *theorem* exists_eq_neg_succ_coe_nat
- \- *theorem* eq_one_of_mul_eq_one_right
- \- *theorem* eq_one_of_mul_eq_one_left
- \- *theorem* eq_one_of_mul_eq_self_left
- \- *theorem* eq_one_of_mul_eq_self_right
- \- *theorem* eq_one_of_dvd_one
- \- *theorem* exists_least_of_bdd
- \- *theorem* exists_greatest_of_bdd



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

Created core/data/list.lean
- \+ *def* partition_map

Created core/default.lean

Modified data/list/basic.lean
- \+/\- *theorem* index_of_eq_length
- \+/\- *theorem* erase_diff_erase_sublist_of_sublist
- \+/\- *theorem* index_of_eq_length
- \+/\- *theorem* erase_diff_erase_sublist_of_sublist

Modified data/sum.lean
- \+ *def* map

Modified docs/tactics.md

Modified tactic/ext.lean
- \+ *def* ext_param_type

Modified tactic/pi_instances.lean



## [2018-09-11 10:07:59+02:00](https://github.com/leanprover-community/mathlib/commit/6557f51)
feat(tactic/ext): add indexing of extensionality lemmas
#### Estimated changes
Modified category_theory/isomorphism.lean
- \+/\- *lemma* hom_inv_id
- \+/\- *lemma* inv_hom_id
- \+/\- *lemma* hom_inv_id
- \+/\- *lemma* inv_hom_id
- \+/\- *def* symm
- \+/\- *def* refl
- \+/\- *def* trans
- \+/\- *def* inv
- \+/\- *def* hom_inv_id
- \+/\- *def* inv_hom_id
- \+/\- *def* symm
- \+/\- *def* refl
- \+/\- *def* trans
- \+/\- *def* inv
- \+/\- *def* hom_inv_id
- \+/\- *def* inv_hom_id

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
Created category_theory/natural_isomorphism.lean
- \+ *lemma* comp_app
- \+ *lemma* hom_eq_coe
- \+ *lemma* inv_eq_symm_coe
- \+ *lemma* naturality_1
- \+ *lemma* naturality_2
- \+ *def* app
- \+ *def* of_components

Modified category_theory/types.lean
- \+ *lemma* types.iso_mk_coe

Created category_theory/yoneda.lean
- \+ *lemma* obj_obj
- \+ *lemma* obj_map
- \+ *lemma* map_app
- \+ *lemma* obj_map_id
- \+ *lemma* naturality
- \+ *lemma* yoneda_evaluation_map_down
- \+ *lemma* yoneda_pairing_map
- \+ *def* yoneda
- \+ *def* ext
- \+ *def* yoneda_evaluation
- \+ *def* yoneda_pairing
- \+ *def* yoneda_lemma



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
- \+/\- *theorem* omega_is_regular
- \+/\- *theorem* omega_is_regular



## [2018-09-10 22:44:42+02:00](https://github.com/leanprover-community/mathlib/commit/0e06944)
feat(data/equiv/basic): quot_equiv_of_quot(')
quot_equiv_of_quot matches matches the existing subtype_equiv_of_subtype,
but quot_equiv_of_quot' is useful in practice and this definition is careful
to use eq.rec only in proofs.
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *def* quot_equiv_of_quot'
- \+ *def* quot_equiv_of_quot



## [2018-09-10 22:40:31+02:00](https://github.com/leanprover-community/mathlib/commit/61f4827)
fix(logic/basic): remove unnecessary hypothesis from proof_irrel_heq
#### Estimated changes
Modified logic/basic.lean
- \+/\- *theorem* proof_irrel_heq
- \+/\- *theorem* proof_irrel_heq



## [2018-09-10 13:57:55-04:00](https://github.com/leanprover-community/mathlib/commit/b33764d)
feat(algebra/module): semimodules
#### Estimated changes
Modified algebra/module.lean
- \+ *lemma* smul_smul'
- \+ *lemma* smul_eq_mul'
- \+ *theorem* smul_add'
- \+ *theorem* add_smul'
- \+ *theorem* mul_smul'
- \+ *theorem* one_smul'
- \+ *theorem* zero_smul'
- \+ *theorem* smul_zero'
- \+/\- *theorem* mul_smul
- \+/\- *theorem* mul_smul

Modified analysis/measure_theory/outer_measure.lean
- \- *theorem* smul_add
- \- *theorem* add_smul
- \- *theorem* mul_smul
- \- *theorem* one_smul
- \- *theorem* zero_smul
- \- *theorem* smul_zero
- \- *def* smul

Modified tactic/abel.lean



## [2018-09-10 03:23:58-04:00](https://github.com/leanprover-community/mathlib/commit/56c4919)
feat(tactic/abel): decision procedure for comm groups
#### Estimated changes
Modified algebra/group_power.lean
- \+/\- *theorem* one_gpow
- \+ *theorem* gsmul_zero
- \+ *theorem* mul_gpow
- \+ *theorem* gsmul_add
- \+/\- *theorem* one_gpow

Created tactic/abel.lean
- \+ *lemma* unfold_sub
- \+ *lemma* subst_into_smul
- \+ *lemma* subst_into_smulg
- \+ *theorem* const_add_term
- \+ *theorem* const_add_termg
- \+ *theorem* term_add_const
- \+ *theorem* term_add_constg
- \+ *theorem* term_add_term
- \+ *theorem* term_add_termg
- \+ *theorem* zero_term
- \+ *theorem* zero_termg
- \+ *theorem* term_neg
- \+ *theorem* zero_smul
- \+ *theorem* zero_smulg
- \+ *theorem* term_smul
- \+ *theorem* term_smulg
- \+ *theorem* term_atom
- \+ *theorem* term_atomg
- \+ *theorem* unfold_smul
- \+ *theorem* unfold_smulg
- \+ *theorem* unfold_gsmul
- \+ *def* term
- \+ *def* termg
- \+ *def* smul
- \+ *def* smulg

Modified tactic/norm_num.lean
- \+ *lemma* subst_into_neg

Modified tactic/ring.lean
- \- *lemma* subst_into_neg
- \+/\- *theorem* add_neg_eq_sub
- \+/\- *theorem* add_neg_eq_sub
- \+/\- *def* horner
- \+/\- *def* horner

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

Created tests/ring.lean



## [2018-09-09 20:45:05-04:00](https://github.com/leanprover-community/mathlib/commit/181905e)
refactor(tactic/linarith): refactoring
#### Estimated changes
Modified data/prod.lean

Modified meta/rb_map.lean

Modified tactic/linarith.lean
- \+/\- *lemma* add_subst
- \+/\- *lemma* sub_subst
- \+/\- *lemma* mul_subst
- \+/\- *lemma* add_subst
- \+/\- *lemma* sub_subst
- \+/\- *lemma* mul_subst
- \+/\- *def* ineq.is_lt
- \+/\- *def* ineq.to_string
- \+/\- *def* ineq.is_lt
- \+/\- *def* ineq.to_string
- \- *def* alist_lt
- \- *def* reduce_pair_option



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
- \+ *def* mk_ob

Modified category_theory/embedding.lean
- \+/\- *lemma* image_preimage
- \+/\- *lemma* preimage_iso_coe
- \+/\- *lemma* preimage_iso_symm_coe
- \+/\- *lemma* image_preimage
- \+/\- *lemma* preimage_iso_coe
- \+/\- *lemma* preimage_iso_symm_coe
- \+ *def* injectivity
- \+/\- *def* preimage
- \+/\- *def* preimage

Modified category_theory/examples/measurable_space.lean
- \+/\- *def* Meas
- \+/\- *def* Meas

Created category_theory/examples/monoids.lean
- \+ *def* Mon
- \+ *def* CommMon
- \+ *def* is_comm_monoid_hom
- \+ *def* forget_to_Mon

Modified category_theory/examples/rings.lean
- \- *lemma* comm_ring_hom.map_mul
- \- *lemma* comm_ring_hom.map_add
- \- *lemma* comm_ring_hom.map_one
- \+ *def* Ring
- \+ *def* CommRing
- \+ *def* forget_to_CommMon
- \- *def* {u}

Modified category_theory/examples/topological_spaces.lean
- \+/\- *def* Top
- \+/\- *def* Top

Modified category_theory/functor.lean
- \+ *def* bundled.map

Modified category_theory/types.lean
- \+/\- *def* forget
- \+/\- *def* forget



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
- \+/\- *lemma* leading_coeff_X_pow
- \+/\- *lemma* leading_coeff_X_pow



## [2018-09-08 19:25:06-04:00](https://github.com/leanprover-community/mathlib/commit/fc1fd3d)
feat(set_theory/cofinality): sum_lt_of_is_regular
#### Estimated changes
Modified set_theory/cardinal.lean
- \+/\- *theorem* sup_le
- \+/\- *theorem* sup_le

Modified set_theory/cofinality.lean
- \+ *theorem* sup_lt_of_is_regular
- \+ *theorem* sum_lt_of_is_regular

Modified set_theory/ordinal.lean
- \+ *theorem* sup_ord
- \+ *theorem* mul_lt_of_lt
- \+ *theorem* add_lt_of_lt



## [2018-09-08 20:54:21+02:00](https://github.com/leanprover-community/mathlib/commit/73abe2e)
fix(category_theory/products): fix types of inl/inr/fst/snd ([#320](https://github.com/leanprover-community/mathlib/pull/320))
#### Estimated changes
Modified category_theory/products.lean
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* fst
- \+/\- *def* snd



## [2018-09-08 20:17:26+02:00](https://github.com/leanprover-community/mathlib/commit/5613d2e)
feat(tactic): add support for quotients to rcases
#### Estimated changes
Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* tendsto_multiset_sum
- \+/\- *lemma* continuous_multiset_sum
- \+/\- *lemma* tendsto_multiset_sum
- \+/\- *lemma* continuous_multiset_sum

Modified data/equiv/encodable.lean

Modified data/multiset.lean
- \+/\- *theorem* cons_inj_right
- \+/\- *theorem* cons_inj_right

Modified data/quot.lean
- \+/\- *lemma* exact'
- \+/\- *lemma* exact'

Modified docs/tactics.md

Modified group_theory/free_group.lean
- \+/\- *def* to_word.mk
- \+/\- *def* to_word.inj
- \+/\- *def* to_word.mk
- \+/\- *def* to_word.inj

Modified ring_theory/associated.lean
- \+/\- *theorem* mul_zero
- \+/\- *theorem* zero_mul
- \+/\- *theorem* mul_zero
- \+/\- *theorem* zero_mul

Modified ring_theory/unique_factorization_domain.lean

Modified set_theory/cardinal.lean
- \+/\- *theorem* zero_le
- \+/\- *theorem* add_le_add
- \+/\- *theorem* mul_le_mul
- \+/\- *theorem* power_le_power_left
- \+/\- *theorem* cantor
- \+/\- *theorem* zero_le
- \+/\- *theorem* add_le_add
- \+/\- *theorem* mul_le_mul
- \+/\- *theorem* power_le_power_left
- \+/\- *theorem* cantor

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
- \+ *lemma* nhds_induced_eq_comap
- \+ *lemma* nhds_subtype_eq_comap
- \+ *lemma* tendsto_comap_nhds_nhds
- \+ *lemma* comap_nhds_neq_bot
- \- *lemma* nhds_induced_eq_vmap
- \- *lemma* nhds_subtype_eq_vmap
- \- *lemma* tendsto_vmap_nhds_nhds
- \- *lemma* vmap_nhds_neq_bot

Modified analysis/topology/infinite_sum.lean

Modified analysis/topology/topological_space.lean

Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* filter.map_neg
- \+/\- *lemma* filter.map_neg

Modified analysis/topology/uniform_space.lean
- \+ *lemma* nhds_eq_comap_uniformity
- \+ *lemma* cauchy_comap
- \+ *lemma* comap_quotient_le_uniformity
- \+ *lemma* comap_quotient_eq_uniformity
- \+/\- *lemma* separated_of_uniform_continuous
- \+/\- *lemma* eq_of_separated_of_uniform_continuous
- \+ *lemma* uniform_continuous_comap
- \+ *lemma* uniform_continuous_comap'
- \+/\- *lemma* uniform_continuous.prod_mk
- \- *lemma* nhds_eq_vmap_uniformity
- \- *lemma* cauchy_vmap
- \- *lemma* vmap_quotient_le_uniformity
- \- *lemma* vmap_quotient_eq_uniformity
- \+/\- *lemma* separated_of_uniform_continuous
- \+/\- *lemma* eq_of_separated_of_uniform_continuous
- \- *lemma* uniform_continuous_vmap
- \- *lemma* uniform_continuous_vmap'
- \+/\- *lemma* uniform_continuous.prod_mk
- \+ *theorem* to_topological_space_comap
- \- *theorem* to_topological_space_vmap
- \+ *def* uniform_space.comap
- \- *def* uniform_space.vmap

Modified data/analysis/filter.lean

Modified order/filter.lean
- \+ *lemma* comap_id
- \+ *lemma* comap_comap_comp
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+/\- *lemma* map_mono
- \+ *lemma* comap_mono
- \+ *lemma* monotone_comap
- \+/\- *lemma* map_bot
- \+/\- *lemma* map_sup
- \+ *lemma* comap_top
- \+ *lemma* comap_inf
- \+ *lemma* comap_infi
- \+ *lemma* map_comap_le
- \+ *lemma* le_comap_map
- \+ *lemma* comap_bot
- \+ *lemma* comap_sup
- \+ *lemma* le_map_comap'
- \+ *lemma* le_map_comap
- \+ *lemma* comap_map
- \+ *lemma* comap_neq_bot
- \+ *lemma* comap_neq_bot_of_surj
- \+ *lemma* sInter_comap_sets
- \+ *lemma* map_eq_comap_of_inverse
- \+ *lemma* map_swap_eq_comap_swap
- \+ *lemma* tendsto_iff_comap
- \+ *lemma* tendsto_comap
- \+ *lemma* tendsto_comap_iff
- \+ *lemma* tendsto_comap''
- \+ *lemma* comap_eq_of_inverse
- \+ *lemma* comap_lift_eq
- \+ *lemma* prod_comap_comap_eq
- \+/\- *lemma* prod_comm'
- \- *lemma* vmap_id
- \- *lemma* vmap_vmap_comp
- \- *lemma* map_le_iff_le_vmap
- \- *lemma* gc_map_vmap
- \+/\- *lemma* map_mono
- \- *lemma* vmap_mono
- \- *lemma* monotone_vmap
- \+/\- *lemma* map_bot
- \+/\- *lemma* map_sup
- \- *lemma* vmap_top
- \- *lemma* vmap_inf
- \- *lemma* vmap_infi
- \- *lemma* map_vmap_le
- \- *lemma* le_vmap_map
- \- *lemma* vmap_bot
- \- *lemma* vmap_sup
- \- *lemma* le_map_vmap'
- \- *lemma* le_map_vmap
- \- *lemma* vmap_map
- \- *lemma* vmap_neq_bot
- \- *lemma* vmap_neq_bot_of_surj
- \- *lemma* sInter_vmap_sets
- \- *lemma* map_eq_vmap_of_inverse
- \- *lemma* map_swap_eq_vmap_swap
- \- *lemma* tendsto_iff_vmap
- \- *lemma* tendsto_vmap
- \- *lemma* tendsto_vmap_iff
- \- *lemma* tendsto_vmap''
- \- *lemma* vmap_eq_of_inverse
- \- *lemma* vmap_lift_eq
- \- *lemma* prod_vmap_vmap_eq
- \+/\- *lemma* prod_comm'
- \+ *theorem* mem_comap_sets
- \+ *theorem* preimage_mem_comap
- \+ *theorem* comap_principal
- \+ *theorem* comap_lift_eq2
- \+ *theorem* comap_lift'_eq
- \+ *theorem* comap_lift'_eq2
- \+ *theorem* comap_eq_lift'
- \- *theorem* mem_vmap_sets
- \- *theorem* preimage_mem_vmap
- \- *theorem* vmap_principal
- \- *theorem* vmap_lift_eq2
- \- *theorem* vmap_lift'_eq
- \- *theorem* vmap_lift'_eq2
- \- *theorem* vmap_eq_lift'
- \+ *def* comap
- \- *def* vmap



## [2018-09-07 17:32:23+02:00](https://github.com/leanprover-community/mathlib/commit/2524dba)
fix(algebra/big_operators): change name of `sum_attach` to `finset.sum_attach`
#### Estimated changes
Modified algebra/big_operators.lean



## [2018-09-07 17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/8f89324)
style(linear_algebra/submodule): changed import order; added product construction
#### Estimated changes
Modified linear_algebra/submodule.lean
- \+ *lemma* coe_prod
- \+ *def* prod



## [2018-09-07 17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/085c012)
refactor(linear_algebra, ring_theory): rework submodules; move them to linear_algebra
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* subtype.mem
- \+ *lemma* preimage_eq_preimage
- \+ *lemma* surjective_preimage
- \+ *lemma* image_eq_image
- \+ *lemma* image_subset_image_iff
- \+ *lemma* injective_image
- \+ *theorem* set.set_coe_eq_subtype
- \+/\- *theorem* set_coe.forall
- \+/\- *theorem* set_coe.exists
- \+/\- *theorem* set_coe_cast
- \+ *theorem* set_coe.ext
- \+ *theorem* set_coe.ext_iff
- \- *theorem* set_coe_eq_subtype
- \+/\- *theorem* set_coe.forall
- \+/\- *theorem* set_coe.exists
- \+/\- *theorem* set_coe_cast

Modified linear_algebra/linear_map_module.lean
- \- *lemma* some_spec2

Modified linear_algebra/quotient_module.lean
- \+ *lemma* coe_eq_zero

Created linear_algebra/submodule.lean
- \+ *lemma* coe_map
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* injective_map
- \+ *lemma* coe_comap
- \+ *lemma* comap_id
- \+ *lemma* comap_comp
- \+ *lemma* injective_comap
- \+ *lemma* comap_map_eq
- \+ *lemma* map_subtype_subset
- \+ *lemma* map_subtype_embedding_eq
- \+ *lemma* subset_comap_quotient
- \+ *theorem* mem_coe
- \+ *theorem* ext
- \+ *theorem* span_subset_iff
- \+ *theorem* sInter_set
- \+ *theorem* bot_set
- \+ *theorem* span_empty
- \+ *theorem* top_set
- \+ *theorem* Union_set_of_directed
- \+ *theorem* span_union
- \+ *def* span
- \+ *def* map
- \+ *def* comap
- \+ *def* map_subtype
- \+ *def* map_subtype.order_iso
- \+ *def* map_subtype.le_order_embedding
- \+ *def* submodule_lt_equiv
- \+ *def* lt_order_embedding
- \+ *def* comap_quotient
- \+ *def* comap_quotient.order_iso

Modified linear_algebra/subtype_module.lean
- \+ *lemma* coe_add
- \+ *lemma* coe_zero
- \+ *lemma* coe_neg
- \+ *lemma* coe_smul
- \+/\- *lemma* sub_val
- \+ *lemma* is_linear_map_coe
- \+/\- *lemma* is_linear_map_subtype_val
- \- *lemma* add_val
- \- *lemma* zero_val
- \- *lemma* neg_val
- \- *lemma* smul_val
- \+/\- *lemma* sub_val
- \+/\- *lemma* is_linear_map_subtype_val
- \- *lemma* is_submodule.is_linear_map_inclusion

Modified logic/basic.lean
- \+ *lemma* some_spec2

Modified order/basic.lean
- \+ *def* preorder.lift
- \+ *def* partial_order.lift
- \+ *def* linear_order.lift

Deleted ring_theory/correspondence_theorem.lean

Modified ring_theory/noetherian.lean
- \- *def* univ

Deleted ring_theory/submodule.lean
- \- *lemma* embedding_eq
- \- *theorem* mem_coe
- \- *theorem* ext
- \- *theorem* eq
- \- *theorem* span_subset_iff
- \- *theorem* sInter_set
- \- *theorem* bot_set
- \- *theorem* span_empty
- \- *theorem* top_set
- \- *theorem* Union_set_of_directed
- \- *theorem* span_union
- \- *def* pushforward_injective_of_injective
- \- *def* pullback_injective_of_surjective
- \- *def* span

Modified set_theory/ordinal.lean



## [2018-09-07 17:30:25+02:00](https://github.com/leanprover-community/mathlib/commit/4421f46)
feat(ring_theory): submodules and quotients of Noetherian modules are Noetherian
#### Estimated changes
Modified algebra/order.lean
- \+ *lemma* le_iff_le_of_strict_mono

Modified data/set/basic.lean
- \+/\- *theorem* union_singleton
- \+ *theorem* singleton_union
- \+/\- *theorem* union_singleton

Modified data/set/finite.lean
- \+ *theorem* finite.exists_finset_coe

Modified linear_algebra/basic.lean

Modified linear_algebra/quotient_module.lean
- \+ *lemma* quotient.exists_rep

Modified linear_algebra/subtype_module.lean
- \+ *lemma* is_submodule.is_linear_map_inclusion

Modified order/conditionally_complete_lattice.lean

Modified order/order_iso.lean

Created ring_theory/correspondence_theorem.lean

Created ring_theory/noetherian.lean
- \+ *theorem* fg_def
- \+ *theorem* is_noetherian_iff_well_founded
- \+ *theorem* is_noetherian_of_submodule_of_noetherian
- \+ *theorem* is_noetherian_of_quotient_of_noetherian
- \+ *def* is_fg
- \+ *def* fg
- \+ *def* univ
- \+ *def* is_noetherian
- \+ *def* is_noetherian_ring

Created ring_theory/submodule.lean
- \+ *lemma* embedding_eq
- \+ *theorem* mem_coe
- \+ *theorem* ext
- \+ *theorem* eq
- \+ *theorem* span_subset_iff
- \+ *theorem* sInter_set
- \+ *theorem* bot_set
- \+ *theorem* span_empty
- \+ *theorem* top_set
- \+ *theorem* Union_set_of_directed
- \+ *theorem* span_union
- \+ *def* pushforward_injective_of_injective
- \+ *def* pullback_injective_of_surjective
- \+ *def* span



## [2018-09-07 17:27:38+02:00](https://github.com/leanprover-community/mathlib/commit/dce0e64)
fix(algebra/big_operators): change name of `sum_eq_single` to `finset.sum_eq_single` ([#321](https://github.com/leanprover-community/mathlib/pull/321))
#### Estimated changes
Modified algebra/big_operators.lean

Modified data/polynomial.lean



## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/4085ca1)
feat(category_theory): add measurable space example
#### Estimated changes
Created category_theory/examples/measurable_space.lean
- \+ *def* Meas
- \+ *def* Borel



## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/c2a4cf9)
feat(category_theory): lift morphism map proof to concrete categories
#### Estimated changes
Modified category_theory/examples/topological_spaces.lean

Modified category_theory/functor.lean
- \+ *def* concrete_functor



## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/93e9043)
style(category_theory): concrete categories as type class
#### Estimated changes
Modified category_theory/category.lean
- \- *def* concrete_category

Modified category_theory/examples/rings.lean
- \+/\- *lemma* comm_ring_hom.map_mul
- \+/\- *lemma* comm_ring_hom.map_add
- \+/\- *lemma* comm_ring_hom.map_one
- \+/\- *lemma* comm_ring_hom.map_mul
- \+/\- *lemma* comm_ring_hom.map_add
- \+/\- *lemma* comm_ring_hom.map_one
- \- *lemma* comm_ring_hom.id_map
- \- *lemma* comm_ring_hom.comp_map
- \- *lemma* comm_ring_hom.ext
- \+ *def* {u}
- \+ *def* is_comm_ring_hom
- \- *def* CommRing
- \- *def* comm_ring_hom.id
- \- *def* comm_ring_hom.comp

Modified category_theory/examples/topological_spaces.lean
- \- *lemma* continuous_map.ext
- \+/\- *def* Top
- \+/\- *def* Top

Modified category_theory/functor.lean
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+/\- *lemma* mk_obj
- \+/\- *lemma* mk_map
- \+/\- *lemma* comp_map
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+/\- *lemma* mk_obj
- \+/\- *lemma* mk_map
- \+/\- *lemma* comp_map

Modified category_theory/types.lean
- \+/\- *lemma* types_hom
- \+/\- *lemma* map_id
- \+/\- *lemma* naturality
- \+/\- *lemma* types_hom
- \+/\- *lemma* map_id
- \+/\- *lemma* naturality
- \+ *def* ulift_functor
- \+ *def* forget



## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/5c48489)
feat(category_theory): construction for a concrete category
#### Estimated changes
Modified category_theory/category.lean
- \+/\- *lemma* cancel_epi
- \+/\- *lemma* cancel_mono
- \+/\- *lemma* cancel_epi
- \+/\- *lemma* cancel_mono
- \+ *def* concrete_category



## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/840a733)
removing unnecessary class
#### Estimated changes
Modified analysis/topology/topological_structures.lean



## [2018-09-07 11:42:25+02:00](https://github.com/leanprover-community/mathlib/commit/d91428c)
feat(category_theory): the category of topological spaces, and of neighbourhoods of a point. also the category of commutative rings
#### Estimated changes
Modified analysis/topology/topological_structures.lean

Created category_theory/examples/rings.lean
- \+ *lemma* comm_ring_hom.map_mul
- \+ *lemma* comm_ring_hom.map_add
- \+ *lemma* comm_ring_hom.map_one
- \+ *lemma* comm_ring_hom.id_map
- \+ *lemma* comm_ring_hom.comp_map
- \+ *lemma* comm_ring_hom.ext
- \+ *def* CommRing
- \+ *def* comm_ring_hom.id
- \+ *def* comm_ring_hom.comp

Created category_theory/examples/topological_spaces.lean
- \+ *lemma* continuous_map.ext
- \+ *def* Top
- \+ *def* nbhd
- \+ *def* nbhds



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
- \+/\- *lemma* prod_finset_sum_index
- \+ *lemma* multiset_sum_sum_index
- \+ *lemma* multiset_map_sum
- \+ *lemma* multiset_sum_sum
- \+/\- *lemma* map_domain_finset_sum
- \+/\- *lemma* prod_single
- \+/\- *lemma* prod_finset_sum_index
- \+/\- *lemma* map_domain_finset_sum
- \+/\- *lemma* prod_single



## [2018-09-05 14:19:36+02:00](https://github.com/leanprover-community/mathlib/commit/92b9a00)
feat(data/finsupp): to_/of_multiset, curry/uncurry
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* mem_subtype

Modified data/finsupp.lean
- \+ *lemma* single_multiset_sum
- \+ *lemma* single_finset_sum
- \+ *lemma* single_sum
- \+/\- *lemma* sum_zero
- \+/\- *lemma* sum_add
- \+/\- *lemma* sum_neg
- \+/\- *lemma* prod_add_index
- \+/\- *lemma* sum_sub_index
- \+/\- *lemma* prod_finset_sum_index
- \+/\- *lemma* prod_sum_index
- \+/\- *lemma* map_domain_finset_sum
- \+/\- *lemma* prod_map_domain_index
- \+ *lemma* count_to_multiset
- \+ *lemma* of_multiset_apply
- \+ *lemma* mem_support_multiset_sum
- \+ *lemma* mem_support_finset_sum
- \+ *lemma* mem_support_single
- \+ *lemma* sum_curry_index
- \- *lemma* mem_subtype
- \+/\- *lemma* sum_zero
- \+/\- *lemma* sum_add
- \+/\- *lemma* sum_neg
- \+/\- *lemma* prod_add_index
- \+/\- *lemma* sum_sub_index
- \+/\- *lemma* prod_finset_sum_index
- \+/\- *lemma* prod_sum_index
- \+/\- *lemma* map_domain_finset_sum
- \+/\- *lemma* prod_map_domain_index
- \+ *def* to_multiset
- \+ *def* of_multiset
- \+ *def* equiv_multiset
- \+ *def* finsupp_prod_equiv



## [2018-09-05 14:05:50+02:00](https://github.com/leanprover-community/mathlib/commit/e105c9e)
feat(data/multiset): add prod_map_add
#### Estimated changes
Modified data/multiset.lean
- \+ *lemma* prod_map_add



## [2018-09-05 14:04:54+02:00](https://github.com/leanprover-community/mathlib/commit/abd6ab5)
refactor(data/prod): add map_fst, map_snd
#### Estimated changes
Modified data/prod.lean
- \+ *lemma* map_fst
- \+ *lemma* map_snd



## [2018-09-05 13:15:42+02:00](https://github.com/leanprover-community/mathlib/commit/ac4f7b1)
Revert "doc(docs/elan.md): Clarify instructions for leanpkg build"
This reverts commit 89e8cfee313b8bffe70362949577bd575cd09ea5.
#### Estimated changes
Modified docs/elan.md



## [2018-09-05 11:54:07+02:00](https://github.com/leanprover-community/mathlib/commit/9ea38e1)
feat(data/finset): option.to_finset
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* to_finset_none
- \+ *theorem* to_finset_some
- \+ *theorem* mem_to_finset
- \+ *def* to_finset



## [2018-09-05 11:53:36+02:00](https://github.com/leanprover-community/mathlib/commit/2997ce6)
feat(logic/embedding): embedding into option
#### Estimated changes
Modified data/option.lean
- \+ *theorem* injective_some

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
- \+ *lemma* coe_zero
- \+ *lemma* coe_smul
- \+ *lemma* coe_add
- \+/\- *lemma* is_linear_map_quotient_mk
- \- *lemma* quotient_rel_eq
- \+/\- *lemma* is_linear_map_quotient_mk
- \+/\- *def* quotient
- \+ *def* mk
- \+/\- *def* quotient

Modified ring_theory/ideals.lean



## [2018-09-05 11:49:04+02:00](https://github.com/leanprover-community/mathlib/commit/681c98f)
feat(category_theory): full subcategories, preorders, Aut, and End
#### Estimated changes
Modified category_theory/category.lean
- \+ *def* End

Created category_theory/full_subcategory.lean
- \+ *def* full_subcategory_embedding

Modified category_theory/isomorphism.lean
- \+ *def* Aut



## [2018-09-05 09:08:50+02:00](https://github.com/leanprover-community/mathlib/commit/600d3cf)
cleanup(data/polynomial): shorten some proofs
#### Estimated changes
Modified data/finsupp.lean
- \+ *lemma* support_add_eq

Modified data/polynomial.lean
- \+ *lemma* degree_le_nat_degree
- \+/\- *lemma* le_degree_of_ne_zero
- \+ *lemma* le_nat_degree_of_ne_zero
- \+ *lemma* degree_le_degree
- \+ *lemma* apply_nat_degree_eq_zero_of_degree_lt
- \+/\- *lemma* le_degree_of_ne_zero



## [2018-09-04 19:56:23+02:00](https://github.com/leanprover-community/mathlib/commit/76de588)
feat(data/polynomial): prove degree_derivative_eq
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* prod_eq_single

Modified data/polynomial.lean
- \+ *lemma* nat_degree_zero
- \+ *lemma* derivative_apply
- \+ *lemma* mem_support_derivative
- \+ *lemma* degree_derivative_eq
- \- *lemma* degree_derivative



## [2018-09-04 10:43:33+02:00](https://github.com/leanprover-community/mathlib/commit/eb20fd0)
feat(data/polynomial): derivative on polynomials
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* sum_C_mul_X_eq
- \+ *lemma* derivative_zero
- \+ *lemma* derivative_monomial
- \+ *lemma* derivative_C
- \+ *lemma* derivative_X
- \+ *lemma* derivative_one
- \+ *lemma* derivative_add
- \+ *lemma* derivative_sum
- \+ *lemma* derivative_mul
- \+ *lemma* degree_derivative
- \+ *def* derivative



## [2018-09-04 02:25:20-04:00](https://github.com/leanprover-community/mathlib/commit/fd43fe0)
fix(data/polynomial): fix proofs
#### Estimated changes
Modified data/polynomial.lean
- \+/\- *lemma* map_C
- \+/\- *lemma* map_X
- \+/\- *lemma* map_C
- \+/\- *lemma* map_X



## [2018-09-04 01:53:38-04:00](https://github.com/leanprover-community/mathlib/commit/7a4125b)
feat(algebra/field): field homs
#### Estimated changes
Modified algebra/field.lean
- \+ *lemma* map_ne_zero
- \+ *lemma* map_eq_zero
- \+ *lemma* map_inv'
- \+ *lemma* map_div'
- \+ *lemma* map_inv
- \+ *lemma* map_div
- \+ *def* is_field_hom



## [2018-09-04 01:49:52-04:00](https://github.com/leanprover-community/mathlib/commit/2dd78b8)
feat(data/polynomial): add eval2 for univariate polys
#### Estimated changes
Modified algebra/group_power.lean
- \+/\- *theorem* int.coe_nat_pow
- \+ *theorem* is_semiring_hom.map_pow
- \+/\- *theorem* int.coe_nat_pow

Modified data/polynomial.lean
- \+ *lemma* eval₂_C
- \+ *lemma* eval₂_X
- \+ *lemma* eval₂_zero
- \+ *lemma* eval₂_add
- \+ *lemma* eval₂_one
- \+ *lemma* eval₂_mul
- \+ *lemma* eval₂_pow
- \+/\- *lemma* eval_C
- \+/\- *lemma* eval_X
- \+/\- *lemma* eval_zero
- \+/\- *lemma* eval_add
- \+/\- *lemma* eval_one
- \+/\- *lemma* eval_mul
- \+/\- *lemma* eval_pow
- \+ *lemma* map_C
- \+ *lemma* map_X
- \+ *lemma* map_zero
- \+ *lemma* map_add
- \+ *lemma* map_one
- \+ *lemma* map_mul
- \+ *lemma* map_pow
- \+/\- *lemma* eval_C
- \+/\- *lemma* eval_X
- \+/\- *lemma* eval_zero
- \+/\- *lemma* eval_add
- \+/\- *lemma* eval_one
- \+/\- *lemma* eval_mul
- \+/\- *lemma* eval_pow
- \+ *def* eval₂
- \+/\- *def* eval
- \+ *def* map
- \+/\- *def* eval

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
- \+ *lemma* unfold_sub
- \+ *lemma* unfold_div



## [2018-09-03 16:58:38-04:00](https://github.com/leanprover-community/mathlib/commit/1edb79a)
refactor(ring_theory/associated): rename associated_elements
#### Estimated changes
Renamed ring_theory/associated_elements.lean to ring_theory/associated.lean
- \+ *theorem* is_unit_iff_dvd_one
- \+ *theorem* is_unit_iff_forall_dvd
- \+ *theorem* is_unit_of_dvd_unit
- \+/\- *theorem* is_unit_nat
- \+ *theorem* of_irreducible_mul
- \+ *theorem* irreducible_or_factor
- \+/\- *theorem* is_unit_nat
- \+/\- *def* irreducible
- \+/\- *def* irreducible

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
- \+/\- *lemma* denom_neg_eq_denom
- \+/\- *lemma* num_zero
- \+/\- *lemma* num_denom_mk
- \+/\- *lemma* denom_neg_eq_denom
- \+/\- *lemma* num_zero
- \+/\- *lemma* num_denom_mk

Modified data/real/nnreal.lean

Modified set_theory/ordinal.lean

Modified tactic/interactive.lean



## [2018-09-03 12:33:54+02:00](https://github.com/leanprover-community/mathlib/commit/36dd78e)
feat(category_theory): full and faithful functors, switching products
also the evaluation functor, and replace the ↝ arrow with ⥤, by request
#### Estimated changes
Modified category_theory/category.lean

Created category_theory/embedding.lean
- \+ *lemma* image_preimage
- \+ *lemma* preimage_iso_coe
- \+ *lemma* preimage_iso_symm_coe
- \+ *def* preimage
- \+ *def* preimage_iso

Modified category_theory/functor.lean
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+/\- *lemma* obj_eq_coe
- \+/\- *lemma* comp_obj
- \+/\- *lemma* comp_map
- \+/\- *lemma* map_id
- \+/\- *lemma* map_comp
- \+/\- *lemma* obj_eq_coe
- \+/\- *lemma* comp_obj
- \+/\- *lemma* comp_map
- \+/\- *def* map
- \+/\- *def* comp
- \+/\- *def* map
- \+/\- *def* comp

Modified category_theory/functor_category.lean
- \+/\- *lemma* id_app
- \+/\- *lemma* comp_app
- \+/\- *lemma* app_naturality
- \+/\- *lemma* naturality_app
- \+/\- *lemma* id_app
- \+/\- *lemma* comp_app
- \+/\- *lemma* app_naturality
- \+/\- *lemma* naturality_app

Modified category_theory/isomorphism.lean
- \+/\- *lemma* on_iso_hom
- \+/\- *lemma* on_iso_inv
- \+/\- *lemma* eq_to_iso
- \+/\- *lemma* on_iso_hom
- \+/\- *lemma* on_iso_inv
- \+/\- *lemma* eq_to_iso
- \+/\- *def* on_iso
- \+/\- *def* on_iso

Modified category_theory/natural_transformation.lean
- \+/\- *lemma* app_eq_coe
- \+/\- *lemma* mk_app
- \+/\- *lemma* naturality
- \+/\- *lemma* id_app
- \+/\- *lemma* hcomp_app
- \+/\- *lemma* exchange
- \+/\- *lemma* app_eq_coe
- \+/\- *lemma* mk_app
- \+/\- *lemma* naturality
- \+/\- *lemma* id_app
- \+/\- *lemma* hcomp_app
- \+/\- *lemma* exchange
- \+/\- *def* hcomp
- \+/\- *def* hcomp

Modified category_theory/opposites.lean
- \+/\- *lemma* opposite_obj
- \+/\- *lemma* opposite_map
- \+/\- *lemma* opposite_obj
- \+/\- *lemma* opposite_map

Modified category_theory/products.lean
- \+/\- *lemma* prod_obj
- \+/\- *lemma* prod_map
- \+/\- *lemma* prod_app
- \+/\- *lemma* prod_obj
- \+/\- *lemma* prod_map
- \+/\- *lemma* prod_app
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* fst
- \+/\- *def* snd
- \+ *def* swap
- \+ *def* symmetry
- \+ *def* evaluation
- \+/\- *def* prod
- \+/\- *def* prod
- \+/\- *def* inl
- \+/\- *def* inr
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* prod
- \+/\- *def* prod

Modified category_theory/types.lean

Modified docs/theories/category_theory.md



## [2018-09-03 12:32:04+02:00](https://github.com/leanprover-community/mathlib/commit/6ddc3fc)
feat(data/finset): max_of_ne_empty, min_of_ne_empty
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* max_of_ne_empty
- \+ *theorem* min_of_ne_empty



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
- \+ *lemma* cancel_epi
- \+ *lemma* cancel_mono

Modified category_theory/functor.lean
- \+ *lemma* obj_eq_coe

Modified category_theory/functor_category.lean

Created category_theory/isomorphism.lean
- \+ *lemma* ext
- \+ *lemma* hom_inv_id
- \+ *lemma* inv_hom_id
- \+ *lemma* hom_eq_coe
- \+ *lemma* inv_eq_coe
- \+ *lemma* refl_coe
- \+ *lemma* refl_symm_coe
- \+ *lemma* trans_coe
- \+ *lemma* trans_symm_coe
- \+ *lemma* refl_symm
- \+ *lemma* trans_symm
- \+ *lemma* on_iso_hom
- \+ *lemma* on_iso_inv
- \+ *lemma* eq_to_iso_refl
- \+ *lemma* eq_to_iso_trans
- \+ *lemma* eq_to_iso
- \+ *def* symm
- \+ *def* refl
- \+ *def* trans
- \+ *def* inv
- \+ *def* hom_inv_id
- \+ *def* inv_hom_id
- \+ *def* on_iso
- \+ *def* eq_to_iso

Modified category_theory/natural_transformation.lean
- \+ *lemma* app_eq_coe
- \+/\- *lemma* vcomp_assoc
- \+/\- *lemma* vcomp_assoc

Modified category_theory/opposites.lean

Modified category_theory/products.lean

Modified category_theory/types.lean

Modified docs/theories.md

Renamed docs/theories/categories.md to docs/theories/category_theory.md



## [2018-09-03 00:10:15+02:00](https://github.com/leanprover-community/mathlib/commit/0df6f77)
style(linear_algebra/tensor_product): rename of -> tmul and ⊗ₛ -> ⊗ₜ; some cleanup in free_abelian_group
#### Estimated changes
Modified group_theory/free_abelian_group.lean
- \- *lemma* to_add_comm_group.add
- \- *lemma* to_add_comm_group.neg
- \- *lemma* to_add_comm_group.sub
- \- *lemma* to_add_comm_group.zero
- \- *lemma* to_add_comm_group.of
- \- *lemma* to_add_comm_group.coe
- \- *theorem* coe_def
- \- *theorem* to_add_comm_group.unique
- \- *theorem* to_add_comm_group.ext
- \+/\- *def* to_add_comm_group
- \+/\- *def* to_add_comm_group
- \- *def* to_add_comm_group.is_add_group_hom

Modified linear_algebra/tensor_product.lean
- \+ *lemma* tmul.add_left
- \+ *lemma* tmul.add_right
- \+ *lemma* tmul.smul
- \+ *lemma* add_tmul
- \+ *lemma* tmul_add
- \+ *lemma* smul_tmul
- \+ *lemma* tmul_smul
- \+ *lemma* to_module.tmul
- \- *lemma* of.add_left
- \- *lemma* of.add_right
- \- *lemma* of.smul
- \- *lemma* add_of
- \- *lemma* of_add
- \- *lemma* smul_of
- \- *lemma* of_smul
- \- *lemma* to_module.of
- \+/\- *theorem* bilinear
- \+/\- *theorem* bilinear
- \+ *def* tmul
- \- *def* of



## [2018-09-02 23:49:36+02:00](https://github.com/leanprover-community/mathlib/commit/40ef7a2)
doc(ring_theory/unique_factorization_domain): add document strings
#### Estimated changes
Modified ring_theory/unique_factorization_domain.lean
- \+/\- *def* {u}
- \+/\- *def* {u}



## [2018-09-02 16:35:13-04:00](https://github.com/leanprover-community/mathlib/commit/b3afef5)
perf(tactic/ring): fix long-running mk_app invocations
#### Estimated changes
Modified tactic/ring.lean



## [2018-09-02 20:50:34+02:00](https://github.com/leanprover-community/mathlib/commit/dd0c0ae)
feat(ring_theory): add unique factorization domain
#### Estimated changes
Created ring_theory/unique_factorization_domain.lean
- \+ *lemma* factor_set.sup_add_inf_eq_add
- \+ *lemma* sup_mul_inf
- \+ *theorem* unique'
- \+ *theorem* prod_le_prod_iff_le
- \+ *theorem* factor_set.coe_add
- \+ *theorem* map_subtype_val_factors'
- \+ *theorem* factors'_cong
- \+ *theorem* factors_0
- \+ *theorem* factors_mk
- \+ *theorem* prod_top
- \+ *theorem* prod_coe
- \+ *theorem* prod_factors
- \+ *theorem* factors_prod
- \+ *theorem* eq_of_factors_eq_factors
- \+ *theorem* eq_of_prod_eq_prod
- \+ *theorem* prod_add
- \+ *theorem* prod_mono
- \+ *theorem* factors_mul
- \+ *theorem* factors_mono
- \+ *theorem* factors_le
- \+ *theorem* prod_le
- \+ *def* {u}
- \+ *def* factors'
- \+ *def* factors
- \+ *def* factor_set.prod
- \+ *def* unique_factorization_domain.to_gcd_domain



## [2018-09-02 20:50:34+02:00](https://github.com/leanprover-community/mathlib/commit/5f8fafc)
feat(ring_theory): add associated elements
#### Estimated changes
Modified algebra/ring.lean

Modified data/multiset.lean
- \+ *theorem* map_eq_map
- \+ *theorem* injective_map
- \+ *theorem* map_mk_eq_map_mk_of_rel
- \+ *theorem* exists_multiset_eq_map_quot_mk
- \+ *theorem* induction_on_multiset_quot

Modified data/nat/basic.lean

Modified order/bounded_lattice.lean
- \+ *lemma* coe_inf
- \+ *lemma* coe_sup

Created ring_theory/associated_elements.lean
- \+ *lemma* out_mk
- \+ *lemma* out_one
- \+ *lemma* out_mul
- \+ *lemma* dvd_out_iff
- \+ *lemma* out_dvd_iff
- \+ *lemma* out_top
- \+ *lemma* norm_unit_out
- \+ *theorem* not_is_unit_zero
- \+ *theorem* is_unit_nat
- \+ *theorem* is_unit_one
- \+ *theorem* units.is_unit_of_mul_one
- \+ *theorem* is_unit_mul_units
- \+ *theorem* not_irreducible_one
- \+ *theorem* not_irreducible_zero
- \+ *theorem* irreducible_iff_nat_prime
- \+ *theorem* unit_associated_one
- \+ *theorem* associated_one_iff_is_unit
- \+ *theorem* associated_zero_iff_eq_zero
- \+ *theorem* associated_one_of_mul_eq_one
- \+ *theorem* associated_one_of_associated_mul_one
- \+ *theorem* associated_of_dvd_dvd
- \+ *theorem* mk_eq_mk_iff_associated
- \+ *theorem* quotient_mk_eq_mk
- \+ *theorem* quot_mk_eq_mk
- \+ *theorem* forall_associated
- \+ *theorem* one_eq_mk_one
- \+ *theorem* mk_mul_mk
- \+ *theorem* prod_mk
- \+ *theorem* rel_associated_iff_map_eq_map
- \+ *theorem* mul_eq_one_iff
- \+ *theorem* prod_eq_one_iff
- \+ *theorem* coe_unit_eq_one
- \+ *theorem* is_unit_iff_eq_one
- \+ *theorem* is_unit_mk
- \+ *theorem* mul_mono
- \+ *theorem* one_le
- \+ *theorem* prod_le_prod
- \+ *theorem* le_mul_right
- \+ *theorem* le_mul_left
- \+ *theorem* mk_zero_eq
- \+ *theorem* mul_zero
- \+ *theorem* zero_mul
- \+ *theorem* mk_eq_zero_iff_eq_zero
- \+ *theorem* dvd_of_mk_le_mk
- \+ *theorem* mk_le_mk_of_dvd
- \+ *theorem* mk_le_mk_iff_dvd_iff
- \+ *theorem* zero_ne_one
- \+ *theorem* mul_eq_zero_iff
- \+ *theorem* prod_eq_zero_iff
- \+ *theorem* irreducible_mk_iff
- \+ *def* is_unit
- \+ *def* irreducible
- \+ *def* associated
- \+ *def* associates
- \+ *def* associates_int_equiv_nat

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
- \+/\- *theorem* index_of_eq_length
- \+/\- *theorem* index_of_eq_length
- \+ *def* reduce_option

Modified docs/tactics.md

Created meta/rb_map.lean

Modified tactic/basic.lean

Created tactic/linarith.lean
- \+ *lemma* eq_of_eq_of_eq
- \+ *lemma* le_of_eq_of_le
- \+ *lemma* lt_of_eq_of_lt
- \+ *lemma* le_of_le_of_eq
- \+ *lemma* lt_of_lt_of_eq
- \+ *lemma* mul_neg
- \+ *lemma* mul_nonpos
- \+ *lemma* mul_eq
- \+ *lemma* eq_of_not_lt_of_not_gt
- \+ *lemma* add_subst
- \+ *lemma* sub_subst
- \+ *lemma* neg_subst
- \+ *lemma* mul_subst
- \+ *lemma* div_subst
- \+ *lemma* sub_into_lt
- \+ *def* ineq.max
- \+ *def* ineq.is_lt
- \+ *def* ineq.to_string
- \+ *def* alist_lt
- \+ *def* reduce_pair_option
- \+ *def* tree.repr

Created tests/linarith_tests.lean



## [2018-09-02 19:58:41+02:00](https://github.com/leanprover-community/mathlib/commit/8c19da7)
feat(data/polynomial): has_repr for polynomials ([#302](https://github.com/leanprover-community/mathlib/pull/302))
Not sure if I should change this so that it will always return a string that will not cause any problems if copied and pasted into a lemma. It does this for rationals and integers, although for rationals, it returns something equal to the polynomial you would like, but probably not the polynomial you actually want, i.e. `(2 / 3 : polynomial ℚ)` more or less gives you `(C 2 / C 3)`, rather than `C (2 / 3)`. These expressions are def eq, but not in any reasonable amount of time as soon as the size gets slightly larger.
#### Estimated changes
Modified data/polynomial.lean



## [2018-09-02 19:54:22+02:00](https://github.com/leanprover-community/mathlib/commit/2594f48)
style(linear_algebra/tensor_product): renaming and changing some proofs
#### Estimated changes
Modified group_theory/free_abelian_group.lean
- \+ *lemma* to_add_comm_group.sub
- \+ *lemma* to_add_comm_group.coe

Modified linear_algebra/tensor_product.lean
- \+ *lemma* of.add_left
- \+ *lemma* of.add_right
- \+ *lemma* of.smul
- \+ *lemma* smul.is_add_group_hom
- \+/\- *lemma* add_of
- \+/\- *lemma* of_add
- \+/\- *lemma* smul_of
- \+/\- *lemma* of_smul
- \+/\- *lemma* add_of
- \+/\- *lemma* of_add
- \+/\- *lemma* smul_of
- \+/\- *lemma* of_smul
- \+ *theorem* zero_left
- \+ *theorem* zero_right
- \+ *theorem* neg_left
- \+ *theorem* neg_right
- \+ *theorem* linear_left
- \+ *theorem* linear_right
- \+ *theorem* comm
- \+ *theorem* comp
- \- *theorem* is_bilinear_map.zero_pair
- \- *theorem* is_bilinear_map.pair_zero
- \- *theorem* is_bilinear_map.neg_pair
- \- *theorem* is_bilinear_map.pair_neg
- \- *theorem* is_bilinear_map.linear_pair
- \- *theorem* is_bilinear_map.pair_linear
- \- *theorem* is_bilinear_map.comm
- \- *theorem* is_bilinear_map.comp
- \+/\- *def* tensor_product
- \+/\- *def* tensor_product
- \- *def* smul.is_add_group_hom



## [2018-09-02 19:54:22+02:00](https://github.com/leanprover-community/mathlib/commit/4b5ad0e)
feat(linear_algebra,group_theory): add tensor product and supporting material
#### Estimated changes
Modified algebra/group.lean

Modified algebra/ring.lean

Created group_theory/abelianization.lean
- \+ *lemma* to_comm_group.of
- \+ *theorem* to_comm_group.unique
- \+ *def* commutator
- \+ *def* abelianization
- \+ *def* of
- \+ *def* to_comm_group
- \+ *def* to_comm_group.is_group_hom

Modified group_theory/coset.lean
- \+ *lemma* induction_on
- \+ *lemma* induction_on'

Created group_theory/free_abelian_group.lean
- \+ *lemma* to_add_comm_group.add
- \+ *lemma* to_add_comm_group.neg
- \+ *lemma* to_add_comm_group.zero
- \+ *lemma* to_add_comm_group.of
- \+ *theorem* coe_def
- \+ *theorem* to_add_comm_group.unique
- \+ *theorem* to_add_comm_group.ext
- \+ *def* free_abelian_group
- \+ *def* of
- \+ *def* to_add_comm_group
- \+ *def* to_add_comm_group.is_add_group_hom
- \+ *def* UMP

Modified group_theory/quotient_group.lean

Modified group_theory/subgroup.lean

Created linear_algebra/tensor_product.lean
- \+ *lemma* add_of
- \+ *lemma* of_add
- \+ *lemma* smul_of
- \+ *lemma* of_smul
- \+ *lemma* to_module.add
- \+ *lemma* to_module.smul
- \+ *lemma* to_module.of
- \+ *theorem* is_bilinear_map.zero_pair
- \+ *theorem* is_bilinear_map.pair_zero
- \+ *theorem* is_bilinear_map.neg_pair
- \+ *theorem* is_bilinear_map.pair_neg
- \+ *theorem* is_bilinear_map.linear_pair
- \+ *theorem* is_bilinear_map.pair_linear
- \+ *theorem* is_bilinear_map.comm
- \+ *theorem* is_bilinear_map.comp
- \+ *theorem* bilinear
- \+ *theorem* to_module.unique
- \+ *theorem* to_module.ext
- \+ *def* relators
- \+ *def* tensor_product
- \+ *def* of
- \+ *def* smul.aux
- \+ *def* smul
- \+ *def* smul.is_add_group_hom
- \+ *def* to_module
- \+ *def* to_module.linear
- \+ *def* to_module.equiv



## [2018-09-02 13:36:43-04:00](https://github.com/leanprover-community/mathlib/commit/dd6b035)
feat(data/option): add simp lemmas for orelse
#### Estimated changes
Modified data/option.lean
- \+ *theorem* some_orelse'
- \+ *theorem* some_orelse
- \+ *theorem* none_orelse'
- \+ *theorem* none_orelse
- \+/\- *theorem* orelse_none'
- \+/\- *theorem* orelse_none
- \- *theorem* orelse_some'
- \- *theorem* orelse_some
- \+/\- *theorem* orelse_none'
- \+/\- *theorem* orelse_none



## [2018-09-02 17:21:22](https://github.com/leanprover-community/mathlib/commit/3de3cfb)
feat(tactic/subtype_instance): generating subtype instances
#### Estimated changes
Modified data/list/basic.lean
- \+ *def* map_head
- \+ *def* map_last

Modified data/string.lean
- \+ *def* map_tokens

Created field_theory/subfield.lean

Modified group_theory/subgroup.lean

Modified group_theory/submonoid.lean

Created ring_theory/subring.lean

Created tactic/algebra.lean

Modified tactic/basic.lean

Created tactic/subtype_instance.lean
- \+ *def* mk_mem_name



## [2018-09-01 13:10:14+02:00](https://github.com/leanprover-community/mathlib/commit/b7b05fb)
style(ring_theory): rename PID to principal_ideal_domain
#### Estimated changes
Renamed ring_theory/PID.lean to ring_theory/principal_ideal_domain.lean

