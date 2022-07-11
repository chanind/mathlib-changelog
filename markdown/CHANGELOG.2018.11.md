## [2018-11-29 22:13:08-05:00](https://github.com/leanprover-community/mathlib/commit/2a86b06)
fix(order/filter): tendsto_at_top only requires preorder not partial_order
#### Estimated changes
Modified order/filter.lean
- \+/\- *lemma* tendsto_at_top



## [2018-11-29 17:33:38-05:00](https://github.com/leanprover-community/mathlib/commit/9e6572f)
fix(group_theory/group_action): make is_group_action Prop
#### Estimated changes
Modified group_theory/group_action.lean




## [2018-11-28 05:03:07-05:00](https://github.com/leanprover-community/mathlib/commit/1c0c39c)
fix(category_theory/equivalences): fixed import
(and some docs, and some clumsy proofs)
#### Estimated changes
Modified category_theory/equivalence.lean


Modified category_theory/yoneda.lean




## [2018-11-28 04:36:21-05:00](https://github.com/leanprover-community/mathlib/commit/b02bea6)
feat(category_theory/equivalence): equivalences, slice tactic ([#479](https://github.com/leanprover-community/mathlib/pull/479))
#### Estimated changes
Modified category_theory/category.lean


Created category_theory/equivalence.lean
- \+ *lemma* fun_inv_map
- \+ *lemma* inv_fun_map
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans
- \+ *def* inv
- \+ *def* fun_inv_id
- \+ *def* inv_fun_id
- \+ *def* as_equivalence
- \+ *def* obj_preimage
- \+ *def* fun_obj_preimage_iso
- \+ *def* ess_surj_of_equivalence
- \+ *def* equivalence_of_fully_faithfully_ess_surj

Modified category_theory/natural_isomorphism.lean
- \+ *lemma* hom_vcomp_inv
- \+ *lemma* inv_vcomp_hom
- \+ *lemma* hom_app_inv_app_id
- \+ *lemma* inv_app_hom_app_id

Created tactic/slice.lean




## [2018-11-28 01:31:22-05:00](https://github.com/leanprover-community/mathlib/commit/131b46f)
feat(data/list): separate out list defs into `data.lists.defs`
#### Estimated changes
Modified data/list/basic.lean
- \- *theorem* pairwise_cons
- \- *theorem* chain_cons
- \- *def* split_at
- \- *def* concat
- \- *def* head'
- \- *def* to_array
- \- *def* inth
- \- *def* modify_nth_tail
- \- *def* modify_head
- \- *def* modify_nth
- \- *def* insert_nth
- \- *def* take'
- \- *def* take_while
- \- *def* scanl
- \- *def* scanr_aux
- \- *def* scanr
- \- *def* prod
- \- *def* find
- \- *def* find_indexes_aux
- \- *def* find_indexes
- \- *def* lookmap
- \- *def* indexes_of
- \- *def* countp
- \- *def* count
- \- *def* is_prefix
- \- *def* is_suffix
- \- *def* is_infix
- \- *def* inits
- \- *def* tails
- \- *def* sublists'_aux
- \- *def* sublists'
- \- *def* sublists_aux
- \- *def* sublists
- \- *def* sublists_aux₁
- \- *def* transpose_aux
- \- *def* transpose
- \- *def* sections
- \- *def* permutations_aux2
- \- *def* permutations_aux.rec
- \- *def* permutations_aux
- \- *def* permutations
- \- *def* erasep
- \- *def* extractp
- \- *def* revzip
- \- *def* product
- \- *def* of_fn_aux
- \- *def* of_fn
- \- *def* of_fn_nth_val
- \- *def* disjoint
- \- *def* pw_filter
- \- *def* nodup
- \- *def* erase_dup
- \- *def* range'
- \- *def* reduce_option
- \- *def* map_head
- \- *def* map_last
- \- *def* last'
- \- *def* tfae
- \- *def* choose_x
- \- *def* choose

Created data/list/defs.lean
- \+ *theorem* pairwise_cons
- \+ *theorem* chain_cons
- \+ *def* split_at
- \+ *def* concat
- \+ *def* head'
- \+ *def* to_array
- \+ *def* inth
- \+ *def* modify_nth_tail
- \+ *def* modify_head
- \+ *def* modify_nth
- \+ *def* insert_nth
- \+ *def* take'
- \+ *def* take_while
- \+ *def* scanl
- \+ *def* scanr_aux
- \+ *def* scanr
- \+ *def* prod
- \+ *def* find
- \+ *def* find_indexes_aux
- \+ *def* find_indexes
- \+ *def* lookmap
- \+ *def* indexes_of
- \+ *def* countp
- \+ *def* count
- \+ *def* is_prefix
- \+ *def* is_suffix
- \+ *def* is_infix
- \+ *def* inits
- \+ *def* tails
- \+ *def* sublists'_aux
- \+ *def* sublists'
- \+ *def* sublists_aux
- \+ *def* sublists
- \+ *def* sublists_aux₁
- \+ *def* transpose_aux
- \+ *def* transpose
- \+ *def* sections
- \+ *def* permutations_aux2
- \+ *def* permutations_aux.rec
- \+ *def* permutations_aux
- \+ *def* permutations
- \+ *def* erasep
- \+ *def* extractp
- \+ *def* revzip
- \+ *def* product
- \+ *def* of_fn_aux
- \+ *def* of_fn
- \+ *def* of_fn_nth_val
- \+ *def* disjoint
- \+ *def* pw_filter
- \+ *def* nodup
- \+ *def* erase_dup
- \+ *def* range'
- \+ *def* reduce_option
- \+ *def* map_head
- \+ *def* map_last
- \+ *def* last'
- \+ *def* tfae
- \+ *def* choose_x
- \+ *def* choose



## [2018-11-27 05:19:28-05:00](https://github.com/leanprover-community/mathlib/commit/98eacf8)
feat(tactic/basic,tactic/interactive): generalize use tactic ([#497](https://github.com/leanprover-community/mathlib/pull/497))
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/interactive.lean




## [2018-11-24 03:58:50-05:00](https://github.com/leanprover-community/mathlib/commit/452c9a2)
feat(data/polynomial): nat_degree_comp ([#477](https://github.com/leanprover-community/mathlib/pull/477))
#### Estimated changes
Modified algebra/group_power.lean
- \+ *lemma* with_bot.coe_smul
- \+ *lemma* smul_le_smul_of_le_right
- \+ *theorem* smul_le_smul

Modified algebra/ordered_group.lean
- \+/\- *lemma* coe_add
- \+ *lemma* coe_zero

Modified data/polynomial.lean
- \+ *lemma* nat_degree_one
- \+ *lemma* nat_degree_pow_eq'
- \+ *lemma* nat_degree_comp_le
- \+ *lemma* nat_degree_pow_eq
- \+ *lemma* coeff_comp_degree_mul_degree
- \+ *lemma* nat_degree_comp
- \+ *lemma* leading_coeff_comp



## [2018-11-24 03:57:05-05:00](https://github.com/leanprover-community/mathlib/commit/e628a2c)
feat(data/finmap): finite maps ([#487](https://github.com/leanprover-community/mathlib/pull/487))
* feat(data/list/basic): erasep
* feat(data/list/basic): lookup, ndkeys
* feat(data/list/sigma,alist): basic functions on association lists
* feat(data/finmap): finite maps on multisets
* doc(data/finmap): docstrings [ci-skip]
* refactor(data/list/{alist,sigma},data/finmap): renaming
* knodup -> nodupkeys
* val -> entries
* nd -> nodupkeys
* feat(data/finmap): change keys to finset
* fix(data/list/basic): fix build
* fix(analysis/{emetric-space,measure-theory/integration}): fix build
#### Estimated changes
Modified analysis/emetric_space.lean


Modified analysis/measure_theory/integration.lean


Created data/finmap.lean
- \+ *theorem* coe_nodupkeys
- \+ *theorem* alist.to_finmap_eq
- \+ *theorem* alist.to_finmap_entries
- \+ *theorem* lift_on_to_finmap
- \+ *theorem* induction_on
- \+ *theorem* ext
- \+ *theorem* mem_def
- \+ *theorem* mem_to_finmap
- \+ *theorem* keys_val
- \+ *theorem* keys_ext
- \+ *theorem* mem_keys
- \+ *theorem* empty_to_finmap
- \+ *theorem* not_mem_empty_entries
- \+ *theorem* not_mem_empty
- \+ *theorem* keys_empty
- \+ *theorem* keys_singleton
- \+ *theorem* lookup_to_finmap
- \+ *theorem* lookup_is_some
- \+ *theorem* insert_to_finmap
- \+ *theorem* insert_of_pos
- \+ *theorem* insert_entries_of_neg
- \+ *theorem* mem_insert
- \+ *theorem* replace_to_finmap
- \+ *theorem* keys_replace
- \+ *theorem* mem_replace
- \+ *theorem* erase_to_finmap
- \+ *theorem* keys_erase_to_finset
- \+ *theorem* keys_erase
- \+ *theorem* mem_erase
- \+ *theorem* extract_eq_lookup_erase
- \+ *def* nodupkeys
- \+ *def* alist.to_finmap
- \+ *def* lift_on
- \+ *def* keys
- \+ *def* singleton
- \+ *def* lookup
- \+ *def* insert
- \+ *def* replace
- \+ *def* foldl
- \+ *def* erase
- \+ *def* extract

Created data/list/alist.lean
- \+ *theorem* ext
- \+ *theorem* mem_def
- \+ *theorem* mem_of_perm
- \+ *theorem* mem_keys
- \+ *theorem* keys_nodup
- \+ *theorem* not_mem_empty_entries
- \+ *theorem* not_mem_empty
- \+ *theorem* keys_empty
- \+ *theorem* keys_singleton
- \+ *theorem* lookup_is_some
- \+ *theorem* perm_lookup
- \+ *theorem* insert_of_pos
- \+ *theorem* insert_entries_of_neg
- \+ *theorem* keys_insert
- \+ *theorem* mem_insert
- \+ *theorem* perm_insert
- \+ *theorem* keys_replace
- \+ *theorem* mem_replace
- \+ *theorem* perm_replace
- \+ *theorem* keys_erase
- \+ *theorem* mem_erase
- \+ *theorem* perm_erase
- \+ *theorem* extract_eq_lookup_erase
- \+ *def* keys
- \+ *def* singleton
- \+ *def* lookup
- \+ *def* insert
- \+ *def* replace
- \+ *def* foldl
- \+ *def* erase
- \+ *def* extract

Modified data/list/basic.lean
- \+ *theorem* lookmap_nil
- \+ *theorem* lookmap_cons_none
- \+ *theorem* lookmap_cons_some
- \+ *theorem* lookmap_some
- \+ *theorem* lookmap_none
- \+ *theorem* lookmap_congr
- \+ *theorem* lookmap_of_forall_not
- \+ *theorem* lookmap_map_eq
- \+ *theorem* lookmap_id'
- \+ *theorem* length_lookmap
- \+ *theorem* erasep_nil
- \+ *theorem* erasep_cons
- \+ *theorem* erasep_cons_of_pos
- \+ *theorem* erasep_cons_of_neg
- \+ *theorem* erasep_of_forall_not
- \+ *theorem* exists_of_erasep
- \+ *theorem* exists_or_eq_self_of_erasep
- \+ *theorem* length_erasep_of_mem
- \+ *theorem* erasep_append_left
- \+ *theorem* erasep_append_right
- \+ *theorem* erasep_sublist
- \+ *theorem* erasep_subset
- \+ *theorem* erasep_sublist_erasep
- \+ *theorem* mem_of_mem_erasep
- \+ *theorem* mem_erasep_of_neg
- \+ *theorem* erasep_map
- \+ *theorem* extractp_eq_find_erasep
- \+ *theorem* erase_eq_erasep
- \+/\- *theorem* erase_append_left
- \+/\- *theorem* erase_append_right
- \+/\- *theorem* erase_sublist_erase
- \+/\- *theorem* map_erase
- \+ *theorem* forall_of_forall_of_pairwise
- \+ *theorem* nodup_repeat
- \+ *def* lookmap
- \+ *def* erasep
- \+ *def* extractp

Modified data/list/perm.lean
- \+ *theorem* perm.swap'
- \+ *theorem* perm_option_to_list
- \+ *theorem* perm_lookmap
- \+ *theorem* perm_erasep

Created data/list/sigma.lean
- \+ *theorem* nodupkeys_iff_pairwise
- \+ *theorem* nodupkeys_nil
- \+ *theorem* nodupkeys_cons
- \+ *theorem* nodupkeys.eq_of_fst_eq
- \+ *theorem* nodupkeys.eq_of_mk_mem
- \+ *theorem* nodupkeys_singleton
- \+ *theorem* nodupkeys_of_sublist
- \+ *theorem* nodup_of_nodupkeys
- \+ *theorem* perm_nodupkeys
- \+ *theorem* nodupkeys_join
- \+ *theorem* nodup_enum_map_fst
- \+ *theorem* lookup_nil
- \+ *theorem* lookup_cons_eq
- \+ *theorem* lookup_cons_ne
- \+ *theorem* lookup_is_some
- \+ *theorem* lookup_eq_none
- \+ *theorem* of_mem_lookup
- \+ *theorem* map_lookup_eq_find
- \+ *theorem* mem_lookup_iff
- \+ *theorem* perm_lookup
- \+ *theorem* lookup_all_nil
- \+ *theorem* lookup_all_cons_eq
- \+ *theorem* lookup_all_cons_ne
- \+ *theorem* lookup_all_eq_nil
- \+ *theorem* head_lookup_all
- \+ *theorem* mem_lookup_all
- \+ *theorem* lookup_all_sublist
- \+ *theorem* lookup_all_length_le_one
- \+ *theorem* lookup_all_eq_lookup
- \+ *theorem* lookup_all_nodup
- \+ *theorem* perm_lookup_all
- \+ *theorem* kreplace_of_forall_not
- \+ *theorem* kreplace_self
- \+ *theorem* kreplace_map_fst
- \+ *theorem* kreplace_nodupkeys
- \+ *theorem* perm_kreplace
- \+ *theorem* kerase_sublist
- \+ *theorem* kerase_map_fst
- \+ *theorem* kerase_nodupkeys
- \+ *theorem* perm_kerase
- \+ *theorem* kextract_eq_lookup_kerase
- \+ *def* nodupkeys
- \+ *def* lookup
- \+ *def* lookup_all
- \+ *def* kreplace
- \+ *def* kerase
- \+ *def* kextract

Modified data/option.lean
- \+/\- *theorem* ext

Modified logic/basic.lean
- \+ *lemma* congr_arg_heq



## [2018-11-24 03:56:32-05:00](https://github.com/leanprover-community/mathlib/commit/e19cd0f)
fix(*): adding a few @[simp] attributes ([#492](https://github.com/leanprover-community/mathlib/pull/492))
* some additional simp lemmas
* nat.add_sub_cancel
#### Estimated changes
Modified data/multiset.lean
- \+/\- *theorem* add_sub_cancel_left
- \+/\- *theorem* add_sub_cancel

Modified data/nat/basic.lean


Modified data/rat.lean
- \+/\- *theorem* cast_pow

Modified number_theory/pell.lean




## [2018-11-24 03:53:52-05:00](https://github.com/leanprover-community/mathlib/commit/beff80a)
feat(category_theory): preliminaries for limits ([#488](https://github.com/leanprover-community/mathlib/pull/488))
* style(category_theory): avoid long lines
* style(category_theory): rename embedding -> fully_faithful
* feat(category_theory/opposites): opposite of a functor
* style(category_theory/yoneda): minor changes
* make category argument implicit
* reverse order of arguments in yoneda_lemma
* avoid long lines
* feat(category_theory/functor_category): functor.flip
* feat(category_theory/isomorphism): eq_to_hom
* feat(category_theory/comma): comma categories
* feat(category_theory): pempty, punit categories
* feat(category_theory/products): add curried evaluation bifunctor
It will be used later, to prove that (co)limits in diagram categories
are computed pointwise.
* fixing order of definitions in opposites
* constructing fully_faithful instances
#### Estimated changes
Modified category_theory/category.lean
- \+/\- *lemma* concrete_category_id
- \+/\- *lemma* concrete_category_comp

Created category_theory/comma.lean
- \+ *lemma* ext
- \+ *lemma* fst_obj
- \+ *lemma* snd_obj
- \+ *lemma* fst_map
- \+ *lemma* snd_map
- \+ *def* fst
- \+ *def* snd
- \+ *def* nat_trans
- \+ *def* map_left
- \+ *def* map_right

Modified category_theory/examples/monoids.lean
- \+/\- *def* forget_to_Mon

Modified category_theory/examples/rings.lean


Modified category_theory/examples/topological_spaces.lean


Modified category_theory/full_subcategory.lean
- \+ *def* full_subcategory_inclusion
- \- *def* full_subcategory_embedding

Renamed category_theory/embedding.lean to category_theory/fully_faithful.lean
- \+/\- *lemma* image_preimage
- \+/\- *lemma* preimage_iso_hom
- \+/\- *lemma* preimage_iso_inv
- \+/\- *def* preimage

Modified category_theory/functor.lean
- \+/\- *def* bundled.map

Modified category_theory/functor_category.lean
- \+ *lemma* flip_obj_map

Modified category_theory/isomorphism.lean
- \+ *lemma* eq_to_hom_refl
- \+ *lemma* eq_to_hom_trans
- \+ *lemma* eq_to_iso.hom
- \+/\- *lemma* eq_to_iso_refl
- \+/\- *lemma* eq_to_iso_trans
- \+/\- *lemma* eq_to_iso
- \+ *def* eq_to_hom
- \+/\- *def* eq_to_iso

Modified category_theory/opposites.lean
- \+ *lemma* op_obj
- \+ *lemma* op_map
- \+ *lemma* unop_obj
- \+ *lemma* unop_map
- \+ *lemma* op_hom.obj
- \+ *lemma* op_hom.map_app
- \+ *lemma* op_inv.obj
- \+ *lemma* op_inv.map_app
- \+/\- *lemma* hom_pairing_map
- \- *lemma* opposite_obj
- \- *lemma* opposite_map
- \+ *def* op_op

Created category_theory/pempty.lean
- \+ *def* empty

Modified category_theory/products.lean
- \+/\- *lemma* prod_comp
- \+ *lemma* prod_id_fst
- \+ *lemma* prod_id_snd
- \+ *lemma* prod_comp_fst
- \+ *lemma* prod_comp_snd
- \+/\- *def* evaluation
- \+ *def* evaluation_uncurried

Created category_theory/punit.lean
- \+ *lemma* of_obj_obj
- \+ *def* of_obj

Modified category_theory/types.lean


Modified category_theory/yoneda.lean
- \+/\- *lemma* obj_obj
- \+/\- *lemma* obj_map
- \+/\- *lemma* map_app
- \+/\- *lemma* obj_map_id
- \+/\- *lemma* naturality
- \+/\- *def* yoneda_evaluation
- \+/\- *def* yoneda_pairing
- \+/\- *def* yoneda_lemma

Modified docs/theories/category_theory.md




## [2018-11-22 23:51:18-05:00](https://github.com/leanprover-community/mathlib/commit/de8985c)
fix(finsupp): remove superfluous typeclass argument ([#490](https://github.com/leanprover-community/mathlib/pull/490))
#### Estimated changes
Modified data/finsupp.lean
- \+/\- *lemma* filter_pos_add_filter_neg



## [2018-11-21 09:56:05-05:00](https://github.com/leanprover-community/mathlib/commit/e793967)
feat(tactic/interactive): add use tactic ([#486](https://github.com/leanprover-community/mathlib/pull/486))
#### Estimated changes
Modified docs/tactics.md


Modified tactic/basic.lean


Modified tactic/interactive.lean




## [2018-11-21 05:53:45-05:00](https://github.com/leanprover-community/mathlib/commit/0d56447)
fix(tactic/linarith): nat preprocessing was rejecting negated hypotheses ([#485](https://github.com/leanprover-community/mathlib/pull/485))
#### Estimated changes
Modified tactic/linarith.lean


Modified tests/linarith.lean




## [2018-11-19 16:03:29-05:00](https://github.com/leanprover-community/mathlib/commit/bfe7318)
* feat(tactic/mono): new mono and ac_mono tactics ([#85](https://github.com/leanprover-community/mathlib/pull/85))
* feat(tactic/mono): new mono and ac_mono tactics
* docs(tactic/mono): improve explanation, examples and syntax
* feat(tactic/mono): cache the list of mono lemma to facilitate matching
* fix(tactic/mono): fix conflict with `has_lt`
* update mathlib
* move lemmas from ordered ring to monotonicity
* rename `monotonic` attribute to `mono`
* address PR comments
* fix build
#### Estimated changes
Modified algebra/group.lean


Modified algebra/order.lean
- \+ *lemma* le_implies_le_of_le_of_le

Modified algebra/order_functions.lean
- \+ *theorem* abs_le_abs

Modified algebra/ordered_group.lean


Modified data/list/basic.lean


Modified data/option.lean
- \+ *theorem* not_is_some
- \+/\- *theorem* is_none_iff_eq_none

Modified data/set/disjointed.lean


Modified data/set/lattice.lean


Modified docs/tactics.md


Modified logic/basic.lean
- \+ *lemma* imp_imp_imp

Modified meta/rb_map.lean


Modified order/bounded_lattice.lean
- \+/\- *theorem* some_lt_some

Modified tactic/basic.lean


Modified tactic/default.lean


Modified tactic/interactive.lean


Created tactic/monotonicity/basic.lean
- \+ *def* last_two
- \+ *def* mono_key

Created tactic/monotonicity/default.lean


Created tactic/monotonicity/interactive.lean
- \+ *lemma* apply_rel
- \+ *def* list.minimum_on

Created tactic/monotonicity/lemmas.lean
- \+ *lemma* mul_mono_nonneg
- \+ *lemma* gt_of_mul_lt_mul_neg_right
- \+ *lemma* mul_mono_nonpos
- \+ *lemma* nat.sub_mono_left_strict
- \+ *lemma* nat.sub_mono_right_strict

Modified tactic/norm_num.lean


Created tests/monotonicity.lean
- \+ *lemma* list.le_refl
- \+ *lemma* list.le_trans
- \+ *lemma* list_le_mono_left
- \+ *lemma* list_le_mono_right
- \+ *lemma* bar_bar'
- \+ *lemma* bar_bar''
- \+ *lemma* bar_bar
- \+ *lemma* P_mono
- \+ *lemma* Q_mono
- \+ *def* list.le'
- \+ *def* P
- \+ *def* Q

Created tests/monotonicity/test_cases.lean




## [2018-11-17 21:37:06-05:00](https://github.com/leanprover-community/mathlib/commit/8c385bc)
feat(category_theory): associator and unitors for functors ([#478](https://github.com/leanprover-community/mathlib/pull/478))
also check pentagon and triangle
#### Estimated changes
Modified category_theory/whiskering.lean
- \+ *lemma* triangle
- \+ *lemma* pentagon
- \+ *def* left_unitor
- \+ *def* right_unitor
- \+ *def* associator



## [2018-11-16 19:49:32-05:00](https://github.com/leanprover-community/mathlib/commit/1c60f5b)
fix(ring_theory/subring): unnecessary classical ([#482](https://github.com/leanprover-community/mathlib/pull/482))
#### Estimated changes
Modified ring_theory/subring.lean




## [2018-11-15 23:08:53+01:00](https://github.com/leanprover-community/mathlib/commit/47b3477)
feat(category_theory/whiskering): more whiskering lemmas
#### Estimated changes
Modified category_theory/whiskering.lean
- \+ *lemma* whisker_left_id
- \+ *lemma* whisker_right_id



## [2018-11-15 23:02:43+01:00](https://github.com/leanprover-community/mathlib/commit/c834715)
style(category_theory/natural_transformation): fix hcomp/vcomp notation ([#470](https://github.com/leanprover-community/mathlib/pull/470))
#### Estimated changes
Modified category_theory/natural_transformation.lean
- \+/\- *lemma* vcomp_assoc

Modified category_theory/whiskering.lean




## [2018-11-15 15:29:36-05:00](https://github.com/leanprover-community/mathlib/commit/fce8e7c)
refactor(algebra/euclidean_domain): euclidean_domain extends nonzero_comm_ring ([#476](https://github.com/leanprover-community/mathlib/pull/476))
The euclidean domain axioms imply integral domain, given `nonzero_comm_ring`. Therefore it should extend `nonzero_comm_ring` instead, and an `integral_domain` instance is proven for Euclidean domains.
#### Estimated changes
Modified algebra/euclidean_domain.lean




## [2018-11-14 20:17:14-05:00](https://github.com/leanprover-community/mathlib/commit/c7c0d2a)
fix(analysis/topology/topological_structures): remove useless decidability assumption ([#475](https://github.com/leanprover-community/mathlib/pull/475))
#### Estimated changes
Modified analysis/topology/topological_structures.lean




## [2018-11-14 15:24:47+01:00](https://github.com/leanprover-community/mathlib/commit/baf59c8)
refactor(order/complete_lattice): define supr and infi with range ([#474](https://github.com/leanprover-community/mathlib/pull/474))
#### Estimated changes
Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/continuity.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/uniform_space.lean


Modified data/set/lattice.lean


Modified linear_algebra/basic.lean


Modified order/complete_lattice.lean
- \+/\- *lemma* Sup_range
- \+/\- *lemma* Inf_range
- \+/\- *def* supr
- \+/\- *def* infi

Modified order/filter.lean




## [2018-11-13 18:48:00+01:00](https://github.com/leanprover-community/mathlib/commit/291015d)
fix(tactic/basic): use `lean.parser.of_tactic'` instead of builtin
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/explode.lean


Modified tests/tactics.lean




## [2018-11-13 18:45:11+01:00](https://github.com/leanprover-community/mathlib/commit/3e78b85)
refactor(order/complete_lattice): make supr and infi available in has_Sup and has_Inf ([#472](https://github.com/leanprover-community/mathlib/pull/472))
#### Estimated changes
Modified linear_algebra/lc.lean


Modified order/complete_lattice.lean
- \+/\- *theorem* supr_congr_Prop
- \+/\- *theorem* infi_congr_Prop
- \+/\- *def* supr
- \+/\- *def* infi



## [2018-11-10 18:16:37+01:00](https://github.com/leanprover-community/mathlib/commit/4a013fb)
feat(analysis): sequential completeness
#### Estimated changes
Modified analysis/metric_space.lean
- \+/\- *theorem* exists_delta_of_continuous
- \+ *theorem* tendsto_nhds_topo_metric
- \+ *theorem* continuous_topo_metric
- \+ *theorem* tendsto_at_top_metric
- \+ *theorem* cauchy_seq_metric
- \+ *theorem* cauchy_seq_metric'

Modified analysis/topology/uniform_space.lean
- \+ *theorem* cauchy_seq_tendsto_of_complete
- \+ *def* cauchy_seq

Modified data/real/cau_seq_filter.lean
- \+ *lemma* cauchy_seq_of_dist_tendsto_0
- \+/\- *lemma* le_nhds_cau_filter_lim
- \+/\- *lemma* tendsto_limit
- \+/\- *lemma* cauchy_of_filter_cauchy
- \+/\- *lemma* filter_cauchy_of_cauchy
- \+ *lemma* cau_seq_iff_cauchy_seq
- \- *lemma* is_cau_seq_of_dist_tendsto_0
- \- *lemma* cau_seq_of_cau_filter_mem_set_seq
- \- *lemma* cau_filter_lim_spec
- \+ *theorem* complete_of_cauchy_seq_tendsto
- \- *theorem* cauchy_complete_of_complete_space



## [2018-11-10 17:25:26+01:00](https://github.com/leanprover-community/mathlib/commit/b83fe1e)
feat(analysis): metric spaces are first countable
#### Estimated changes
Modified analysis/metric_space.lean




## [2018-11-09 13:51:33+01:00](https://github.com/leanprover-community/mathlib/commit/891dfbb)
chore(*): clean up uses of zorn
#### Estimated changes
Modified analysis/metric_space.lean


Modified analysis/topology/topological_space.lean


Modified linear_algebra/basic.lean


Modified linear_algebra/basis.lean


Modified logic/schroeder_bernstein.lean


Modified order/order_iso.lean


Modified order/zorn.lean
- \+/\- *theorem* zorn_partial_order₀

Modified ring_theory/ideal_operations.lean


Modified ring_theory/ideals.lean




## [2018-11-09 10:43:01+01:00](https://github.com/leanprover-community/mathlib/commit/4fc67f8)
feat(data/fintype): add choose_unique and construct inverses to bijections ([#421](https://github.com/leanprover-community/mathlib/pull/421))
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* choose_spec
- \+ *lemma* choose_mem
- \+ *lemma* choose_property
- \+ *def* choose_x
- \+ *def* choose

Modified data/fintype.lean
- \+ *lemma* choose_spec
- \+ *lemma* left_inverse_bij_inv
- \+ *lemma* right_inverse_bij_inv
- \+ *lemma* bijective_bij_inv
- \+ *def* choose_x
- \+ *def* choose
- \+ *def* bij_inv

Modified data/list/basic.lean
- \+ *lemma* choose_spec
- \+ *lemma* choose_mem
- \+ *lemma* choose_property
- \+ *def* choose_x
- \+ *def* choose

Modified data/multiset.lean
- \+ *lemma* choose_spec
- \+ *lemma* choose_mem
- \+ *lemma* choose_property
- \+ *def* choose_x
- \+ *def* choose



## [2018-11-09 10:22:08+01:00](https://github.com/leanprover-community/mathlib/commit/9f5099e)
refactor(analysis): add uniform_embedding_comap
#### Estimated changes
Modified analysis/emetric_space.lean
- \- *theorem* induced_uniform_embedding

Modified analysis/metric_space.lean
- \- *theorem* metric_space.induced_uniform_embedding

Modified analysis/real.lean


Modified analysis/topology/uniform_space.lean
- \+ *lemma* uniform_embedding_comap



## [2018-11-09 10:22:08+01:00](https://github.com/leanprover-community/mathlib/commit/6273837)
feat(analysis): add emetric spaces
#### Estimated changes
Modified algebra/ordered_ring.lean
- \+ *lemma* coe_nat
- \+ *lemma* nat_ne_top
- \+ *lemma* top_ne_nat

Created analysis/emetric_space.lean
- \+ *lemma* cauchy_of_emetric
- \+ *theorem* uniformity_dist_of_mem_uniformity
- \+ *theorem* edist_eq_zero
- \+ *theorem* zero_eq_edist
- \+ *theorem* edist_triangle_left
- \+ *theorem* edist_triangle_right
- \+ *theorem* uniformity_edist'
- \+ *theorem* uniformity_edist''
- \+ *theorem* mem_uniformity_edist
- \+ *theorem* edist_mem_uniformity
- \+ *theorem* uniform_continuous_of_emetric
- \+ *theorem* uniform_embedding_of_emetric
- \+ *theorem* eq_of_forall_edist_le
- \+ *theorem* induced_uniform_embedding
- \+ *theorem* subtype.edist_eq
- \+ *def* emetric_space.uniform_space_of_edist
- \+ *def* replace_uniformity
- \+ *def* induced

Modified analysis/ennreal.lean


Modified analysis/metric_space.lean
- \+ *lemma* edist_eq_nndist
- \+ *lemma* nndist_eq_edist
- \+ *lemma* edist_ne_top
- \+ *lemma* nndist_eq_dist
- \+ *lemma* dist_eq_nndist
- \+ *lemma* dist_eq_edist
- \+ *lemma* edist_eq_dist
- \+ *lemma* mem_uniformity_dist_edist
- \- *lemma* coe_dist
- \+ *theorem* edist_dist
- \+ *theorem* uniformity_edist'
- \+ *theorem* uniformity_edist
- \- *theorem* uniformity_dist_of_mem_uniformity

Modified data/complex/exponential.lean


Modified data/finset.lean
- \+ *lemma* sup_lt
- \+ *lemma* comp_sup_eq_sup_comp
- \+ *lemma* lt_inf
- \+ *lemma* comp_inf_eq_inf_comp

Modified data/nat/cast.lean
- \+/\- *theorem* cast_pos

Modified data/real/basic.lean


Modified data/real/cau_seq_filter.lean


Modified data/real/ennreal.lean
- \+ *lemma* zero_to_nnreal
- \+ *lemma* to_nnreal_eq_zero_iff
- \+/\- *lemma* coe_nat
- \+ *lemma* nat_ne_top
- \+ *lemma* top_ne_nat
- \+ *lemma* add_lt_add
- \+ *lemma* coe_div
- \+ *lemma* div_add_div_same
- \+ *lemma* div_self
- \+ *lemma* add_halves
- \+ *lemma* div_pos_iff

Modified data/real/nnreal.lean
- \+ *lemma* of_real_eq_zero
- \+ *lemma* div_add_div_same
- \+ *lemma* add_halves

Modified order/bounded_lattice.lean
- \+ *lemma* lt_top_iff_ne_top
- \+ *lemma* bot_lt_iff_ne_bot



## [2018-11-09 09:39:52+01:00](https://github.com/leanprover-community/mathlib/commit/ff8bd5b)
fix(data/multiset): remove unused argument from `range_zero` ([#466](https://github.com/leanprover-community/mathlib/pull/466))
#### Estimated changes
Modified data/multiset.lean
- \+/\- *theorem* range_zero



## [2018-11-08 10:16:03+01:00](https://github.com/leanprover-community/mathlib/commit/b0564b2)
feat(category_theory): propose removing coercions from category_theory/ ([#463](https://github.com/leanprover-community/mathlib/pull/463))
#### Estimated changes
Modified category_theory/embedding.lean
- \+/\- *lemma* image_preimage
- \+ *lemma* preimage_iso_hom
- \+ *lemma* preimage_iso_inv
- \- *lemma* preimage_iso_coe
- \- *lemma* preimage_iso_symm_coe
- \+/\- *def* preimage
- \+/\- *def* preimage_iso

Modified category_theory/examples/topological_spaces.lean
- \+/\- *lemma* map_id_obj

Modified category_theory/full_subcategory.lean
- \+/\- *def* full_subcategory_embedding

Modified category_theory/functor.lean
- \+/\- *lemma* id_obj
- \+/\- *lemma* comp_obj
- \- *lemma* map_id
- \- *lemma* map_comp
- \- *lemma* obj_eq_coe
- \- *lemma* mk_obj
- \- *lemma* mk_map
- \- *def* map

Modified category_theory/functor_category.lean
- \+/\- *lemma* id_app
- \+/\- *lemma* comp_app
- \+/\- *lemma* app_naturality
- \+/\- *lemma* naturality_app

Modified category_theory/isomorphism.lean
- \+ *lemma* symm_hom
- \+ *lemma* symm_inv
- \+ *lemma* refl_hom
- \+ *lemma* refl_inv
- \+ *lemma* trans_hom
- \+ *lemma* trans_inv
- \+/\- *lemma* refl_symm
- \+/\- *lemma* trans_symm
- \+/\- *lemma* on_iso_hom
- \+/\- *lemma* on_iso_inv
- \- *lemma* hom_inv_id
- \- *lemma* inv_hom_id
- \- *lemma* hom_eq_coe
- \- *lemma* inv_eq_coe
- \- *lemma* refl_coe
- \- *lemma* refl_symm_coe
- \- *lemma* trans_coe
- \- *lemma* trans_symm_coe
- \+/\- *def* on_iso

Modified category_theory/natural_isomorphism.lean
- \+/\- *lemma* comp_app
- \+ *lemma* app_hom
- \+ *lemma* app_inv
- \+/\- *lemma* naturality_1
- \+/\- *lemma* naturality_2
- \- *lemma* mk_app
- \- *lemma* mk_app'
- \- *lemma* hom_eq_coe
- \- *lemma* inv_eq_symm_coe
- \+/\- *def* app
- \+/\- *def* of_components
- \+/\- *def* of_components.app
- \+/\- *def* of_components.hom_app
- \+/\- *def* of_components.inv_app
- \+/\- *def* id_comp
- \+/\- *def* comp_id
- \+/\- *def* assoc

Modified category_theory/natural_transformation.lean
- \+/\- *lemma* id_app
- \+/\- *lemma* ext
- \+/\- *lemma* vcomp_app
- \+/\- *lemma* hcomp_app
- \+/\- *lemma* exchange
- \- *lemma* app_eq_coe
- \- *lemma* mk_app
- \- *lemma* naturality

Modified category_theory/opposites.lean
- \+/\- *lemma* opposite_obj
- \+/\- *lemma* hom_obj

Modified category_theory/products.lean
- \+/\- *lemma* prod_obj
- \+/\- *lemma* prod_map
- \+/\- *lemma* prod_app
- \+/\- *def* evaluation

Modified category_theory/types.lean
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_id
- \+/\- *lemma* naturality
- \+/\- *lemma* vcomp
- \+/\- *lemma* hcomp
- \- *lemma* types.iso_mk_coe
- \+/\- *def* forget

Modified category_theory/whiskering.lean
- \+/\- *lemma* whisker_left.app
- \+/\- *lemma* whisker_left_vcomp
- \+/\- *lemma* whisker_right_vcomp
- \+/\- *def* whiskering_left
- \+/\- *def* whisker_right

Modified category_theory/yoneda.lean
- \+/\- *lemma* obj_obj
- \+/\- *lemma* obj_map
- \+/\- *lemma* map_app
- \+/\- *lemma* obj_map_id
- \+/\- *lemma* naturality
- \+/\- *def* yoneda
- \+/\- *def* yoneda_evaluation
- \+/\- *def* yoneda_pairing
- \+/\- *def* yoneda_lemma

Modified docs/theories/category_theory.md




## [2018-11-08 09:29:40+01:00](https://github.com/leanprover-community/mathlib/commit/2f38ed7)
feat(ring_theory/ideal_operations): define ideal operations (multiplication and radical) ([#462](https://github.com/leanprover-community/mathlib/pull/462))
#### Estimated changes
Modified group_theory/free_abelian_group.lean


Modified linear_algebra/basic.lean
- \+ *theorem* mem_map_of_mem
- \+ *theorem* mem_Sup_of_directed

Modified linear_algebra/tensor_product.lean


Modified order/order_iso.lean


Modified order/zorn.lean
- \+ *theorem* zorn_partial_order₀

Created ring_theory/ideal_operations.lean
- \+ *lemma* add_eq_sup
- \+ *lemma* zero_eq_bot
- \+ *lemma* one_eq_top
- \+ *theorem* mem_annihilator
- \+ *theorem* mem_annihilator'
- \+ *theorem* annihilator_bot
- \+ *theorem* annihilator_eq_top_iff
- \+ *theorem* annihilator_mono
- \+ *theorem* annihilator_supr
- \+ *theorem* mem_colon
- \+ *theorem* mem_colon'
- \+ *theorem* colon_mono
- \+ *theorem* infi_colon_supr
- \+ *theorem* smul_mem_smul
- \+ *theorem* smul_le
- \+ *theorem* smul_induction_on
- \+ *theorem* smul_le_right
- \+ *theorem* smul_mono
- \+ *theorem* smul_mono_left
- \+ *theorem* smul_mono_right
- \+ *theorem* smul_bot
- \+ *theorem* bot_smul
- \+ *theorem* top_smul
- \+ *theorem* smul_sup
- \+ *theorem* sup_smul
- \+ *theorem* smul_assoc
- \+ *theorem* span_smul_span
- \+ *theorem* mul_mem_mul
- \+ *theorem* mul_mem_mul_rev
- \+ *theorem* mul_le
- \+ *theorem* span_mul_span
- \+ *theorem* mul_le_inf
- \+ *theorem* mul_eq_inf_of_coprime
- \+ *theorem* mul_bot
- \+ *theorem* bot_mul
- \+ *theorem* mul_top
- \+ *theorem* top_mul
- \+ *theorem* mul_mono
- \+ *theorem* mul_mono_left
- \+ *theorem* mul_mono_right
- \+ *theorem* mul_sup
- \+ *theorem* sup_mul
- \+ *theorem* le_radical
- \+ *theorem* radical_top
- \+ *theorem* radical_mono
- \+ *theorem* radical_idem
- \+ *theorem* radical_eq_top
- \+ *theorem* is_prime.radical
- \+ *theorem* radical_sup
- \+ *theorem* radical_inf
- \+ *theorem* radical_mul
- \+ *theorem* is_prime.radical_le_iff
- \+ *theorem* radical_eq_Inf
- \+ *theorem* radical_pow
- \+ *theorem* map_mono
- \+ *theorem* mem_map_of_mem
- \+ *theorem* map_le_iff_le_comap
- \+ *theorem* mem_comap
- \+ *theorem* comap_mono
- \+ *theorem* comap_ne_top
- \+ *theorem* map_bot
- \+ *theorem* map_top
- \+ *theorem* comap_top
- \+ *theorem* map_sup
- \+ *theorem* map_mul
- \+ *theorem* comap_inf
- \+ *theorem* comap_radical
- \+ *theorem* map_inf_le
- \+ *theorem* map_radical_le
- \+ *theorem* le_comap_sup
- \+ *theorem* le_comap_mul
- \+ *def* annihilator
- \+ *def* colon
- \+ *def* radical
- \+ *def* map
- \+ *def* comap

Modified ring_theory/ideals.lean
- \+ *theorem* is_prime.mem_of_pow_mem
- \- *theorem* mem_comap
- \- *theorem* comap_ne_top
- \- *def* comap



## [2018-11-08 09:28:27+01:00](https://github.com/leanprover-community/mathlib/commit/41e8eb3)
feat(ring_theory/localization): quotient ring of integral domain is discrete field
#### Estimated changes
Modified ring_theory/localization.lean
- \+/\- *def* quotient_ring.field.of_integral_domain



## [2018-11-06 12:40:58+01:00](https://github.com/leanprover-community/mathlib/commit/89431cf)
feat(linear_algebra): direct sum
#### Estimated changes
Created data/dfinsupp.lean
- \+ *lemma* zero_apply
- \+ *lemma* ext
- \+ *lemma* map_range_apply
- \+ *lemma* zip_with_apply
- \+ *lemma* add_apply
- \+ *lemma* neg_apply
- \+ *lemma* sub_apply
- \+ *lemma* smul_apply
- \+ *lemma* filter_apply
- \+ *lemma* filter_apply_pos
- \+ *lemma* filter_apply_neg
- \+ *lemma* filter_pos_add_filter_neg
- \+ *lemma* subtype_domain_zero
- \+ *lemma* subtype_domain_apply
- \+ *lemma* subtype_domain_add
- \+ *lemma* subtype_domain_neg
- \+ *lemma* subtype_domain_sub
- \+ *lemma* finite_supp
- \+ *lemma* mk_apply
- \+ *lemma* single_apply
- \+ *lemma* single_zero
- \+ *lemma* single_eq_same
- \+ *lemma* single_eq_of_ne
- \+ *lemma* erase_apply
- \+ *lemma* erase_same
- \+ *lemma* erase_ne
- \+ *lemma* single_add
- \+ *lemma* single_add_erase
- \+ *lemma* erase_add_single
- \+ *lemma* induction₂
- \+ *lemma* mk_add
- \+ *lemma* mk_zero
- \+ *lemma* mk_neg
- \+ *lemma* mk_sub
- \+ *lemma* mk_smul
- \+ *lemma* single_smul
- \+ *lemma* lmk_apply
- \+ *lemma* lsingle_apply
- \+ *lemma* support_zero
- \+ *lemma* mem_support_iff
- \+ *lemma* support_eq_empty
- \+ *lemma* support_subset_iff
- \+ *lemma* support_single_ne_zero
- \+ *lemma* support_single_subset
- \+ *lemma* map_range_def
- \+ *lemma* support_map_range
- \+ *lemma* map_range_single
- \+ *lemma* zip_with_def
- \+ *lemma* support_zip_with
- \+ *lemma* erase_def
- \+ *lemma* support_erase
- \+ *lemma* filter_def
- \+ *lemma* support_filter
- \+ *lemma* subtype_domain_def
- \+ *lemma* support_subtype_domain
- \+ *lemma* support_add
- \+ *lemma* support_neg
- \+ *lemma* prod_map_range_index
- \+ *lemma* prod_zero_index
- \+ *lemma* prod_single_index
- \+ *lemma* prod_neg_index
- \+ *lemma* sum_apply
- \+ *lemma* support_sum
- \+ *lemma* sum_zero
- \+ *lemma* sum_add
- \+ *lemma* sum_neg
- \+ *lemma* prod_add_index
- \+ *lemma* sum_sub_index
- \+ *lemma* prod_finset_sum_index
- \+ *lemma* prod_sum_index
- \+ *lemma* sum_single
- \+ *lemma* prod_subtype_domain_index
- \+ *lemma* subtype_domain_sum
- \+ *lemma* subtype_domain_finsupp_sum
- \+ *theorem* mk_inj
- \+ *theorem* support_mk_subset
- \+ *theorem* mem_support_to_fun
- \+ *theorem* eq_mk_support
- \+ *def* decidable_zero_symm
- \+ *def* dfinsupp
- \+ *def* map_range
- \+ *def* zip_with
- \+ *def* to_has_scalar
- \+ *def* to_module
- \+ *def* filter
- \+ *def* subtype_domain
- \+ *def* mk
- \+ *def* single
- \+ *def* erase
- \+ *def* lmk
- \+ *def* lsingle
- \+ *def* support
- \+ *def* sum
- \+ *def* prod

Modified data/finset.lean
- \+ *lemma* to_finset_zero
- \+ *lemma* to_finset_add
- \+/\- *lemma* mem_subtype

Created linear_algebra/direct_sum_module.lean
- \+ *lemma* to_module_apply
- \+ *lemma* to_module.of
- \+ *theorem* mk_inj
- \+ *theorem* of_inj
- \+ *theorem* to_module_aux.add
- \+ *theorem* to_module_aux.smul
- \+ *theorem* to_module.unique
- \+ *theorem* to_module.ext
- \+ *def* direct_sum
- \+ *def* mk
- \+ *def* of
- \+ *def* to_module_aux
- \+ *def* to_module
- \+ *def* set_to_set

Modified linear_algebra/tensor_product.lean
- \+ *def* direct_sum



## [2018-11-05 13:32:36-05:00](https://github.com/leanprover-community/mathlib/commit/0963290)
fix(data/real/irrational): fix build
#### Estimated changes
Modified data/real/irrational.lean




## [2018-11-05 17:58:46+01:00](https://github.com/leanprover-community/mathlib/commit/21d4d1c)
feat(field_theory/perfect_closure): define the perfect closure of a field
#### Estimated changes
Modified data/nat/basic.lean
- \+ *theorem* iterate₀
- \+ *theorem* iterate₁
- \+ *theorem* iterate₂
- \+ *theorem* iterate_cancel
- \+ *theorem* iterate_inj

Created field_theory/perfect_closure.lean
- \+ *theorem* frobenius_pth_root
- \+ *theorem* pth_root_frobenius
- \+ *theorem* is_ring_hom.pth_root
- \+ *theorem* mk_zero
- \+ *theorem* r.sound
- \+ *theorem* eq_iff'
- \+ *theorem* eq_iff
- \+ *theorem* frobenius_mk
- \+ *theorem* frobenius_equiv_apply
- \+ *theorem* nat_cast
- \+ *theorem* int_cast
- \+ *theorem* nat_cast_eq_iff
- \+ *theorem* eq_pth_root
- \+ *def* perfect_closure
- \+ *def* frobenius_equiv
- \+ *def* of
- \+ *def* UMP



## [2018-11-05 17:58:46+01:00](https://github.com/leanprover-community/mathlib/commit/8eac03c)
feat(algebra/char_p): define the characteristic of a semiring
#### Estimated changes
Created algebra/char_p.lean
- \+ *theorem* char_p.cast_eq_zero
- \+ *theorem* char_p.eq
- \+ *theorem* char_p.exists
- \+ *theorem* char_p.exists_unique
- \+ *theorem* ring_char.spec
- \+ *theorem* ring_char.eq
- \+ *theorem* add_pow_char
- \+ *theorem* frobenius_def
- \+ *theorem* frobenius_mul
- \+ *theorem* frobenius_one
- \+ *theorem* is_monoid_hom.map_frobenius
- \+ *theorem* frobenius_zero
- \+ *theorem* frobenius_add
- \+ *theorem* frobenius_neg
- \+ *theorem* frobenius_sub
- \+ *theorem* frobenius_inj
- \+ *theorem* frobenius_nat_cast
- \+ *def* frobenius

Modified algebra/group_power.lean
- \+ *theorem* pow_eq_zero
- \+/\- *theorem* pow_ne_zero



## [2018-11-05 17:46:35+01:00](https://github.com/leanprover-community/mathlib/commit/53d4883)
refactor(cau_seq): unify real.lim, complex.lim and cau_seq.lim ([#433](https://github.com/leanprover-community/mathlib/pull/433))
#### Estimated changes
Modified analysis/real.lean


Modified data/complex/basic.lean
- \+ *lemma* lim_eq_lim_im_add_lim_re
- \+ *lemma* lim_re
- \+ *lemma* lim_im
- \+/\- *lemma* is_cau_seq_conj
- \+/\- *lemma* lim_conj
- \+/\- *lemma* lim_abs
- \- *lemma* re_const_equiv_of_const_equiv
- \- *lemma* im_const_equiv_of_const_equiv
- \- *lemma* eq_lim_of_const_equiv
- \- *lemma* lim_eq_of_equiv_const
- \- *lemma* lim_eq_lim_of_equiv
- \- *lemma* lim_const
- \- *lemma* lim_add
- \- *lemma* lim_mul_lim
- \- *lemma* lim_mul
- \- *lemma* lim_neg
- \- *lemma* lim_eq_zero_iff
- \- *lemma* lim_inv
- \+ *theorem* equiv_lim_aux
- \- *theorem* equiv_lim

Modified data/complex/exponential.lean


Modified data/padics/hensel.lean


Modified data/padics/padic_integers.lean


Modified data/padics/padic_numbers.lean


Modified data/real/basic.lean
- \- *lemma* eq_lim_of_const_equiv
- \- *lemma* lim_eq_of_equiv_const
- \- *lemma* lim_eq_lim_of_equiv
- \- *lemma* lim_const
- \- *lemma* lim_add
- \- *lemma* lim_mul_lim
- \- *lemma* lim_mul
- \- *lemma* lim_neg
- \- *lemma* lim_eq_zero_iff
- \- *lemma* lim_inv
- \- *lemma* lim_le
- \- *lemma* le_lim
- \- *lemma* lt_lim
- \- *lemma* lim_lt
- \- *theorem* equiv_lim

Modified data/real/cau_seq.lean
- \+ *theorem* mul_lim_zero_right
- \+ *theorem* mul_lim_zero_left
- \+/\- *theorem* const_equiv
- \- *theorem* mul_lim_zero

Modified data/real/cau_seq_completion.lean
- \+/\- *lemma* complete
- \+ *lemma* equiv_lim
- \+ *lemma* eq_lim_of_const_equiv
- \+ *lemma* lim_eq_of_equiv_const
- \+ *lemma* lim_eq_lim_of_equiv
- \+ *lemma* lim_const
- \+ *lemma* lim_add
- \+ *lemma* lim_mul_lim
- \+ *lemma* lim_mul
- \+ *lemma* lim_neg
- \+ *lemma* lim_eq_zero_iff
- \+ *lemma* lim_inv
- \+ *lemma* lim_le
- \+ *lemma* le_lim
- \+ *lemma* lt_lim
- \+ *lemma* lim_lt
- \- *lemma* lim_spec

Modified data/real/cau_seq_filter.lean




## [2018-11-05 17:44:01+01:00](https://github.com/leanprover-community/mathlib/commit/17da277)
feat(group_theory/eckmann_hilton): add Eckmann-Hilton ([#335](https://github.com/leanprover-community/mathlib/pull/335))
#### Estimated changes
Created group_theory/eckmann_hilton.lean
- \+ *lemma* group.is_unital
- \+ *lemma* one
- \+ *lemma* mul
- \+ *lemma* mul_comm
- \+ *lemma* mul_assoc
- \+ *def* comm_monoid
- \+ *def* comm_group



## [2018-11-05 17:40:57+01:00](https://github.com/leanprover-community/mathlib/commit/efcb1fb)
feat(analysis/topology/topological_space): more about discrete spaces
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* eq_top_of_singletons_open



## [2018-11-05 17:40:31+01:00](https://github.com/leanprover-community/mathlib/commit/1a4d938)
hotifx(analysis/topology/continuity): difference with disjoint and `s ∩ t = ∅`
#### Estimated changes
Modified analysis/topology/continuity.lean




## [2018-11-05 17:00:44+01:00](https://github.com/leanprover-community/mathlib/commit/14d99a3)
hotfix(data/real/irrational): cast problem
#### Estimated changes
Modified data/real/irrational.lean
- \+/\- *theorem* irr_sqrt_two



## [2018-11-05 10:47:04-05:00](https://github.com/leanprover-community/mathlib/commit/a12d5a1)
feat(linear_algebra,ring_theory): refactoring modules ([#456](https://github.com/leanprover-community/mathlib/pull/456))
Co-authored with Kenny Lau. See also
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/module.20refactoring for discussion.
Major changes made:
- `semimodule α β` and `module α β` and `vector_space α β` now take one more argument, that `β` is an `add_comm_group`, i.e. before making an instance of a module, you need to prove that it's an abelian group first.
- vector space is no longer over a field, but a discrete field.
- The idiom for making an instance `module α β` (after proving that `β` is an abelian group) is `module.of_core { smul := sorry, smul_add  := sorry, add_smul := sorry, mul_smul := sorry, one_smul := sorry }`.
- `is_linear_map` and `linear_map` are now both structures, and they are independent, meaning that `linear_map` is no longer defined as `subtype is_linear_map`. The idiom for making `linear_map` from `is_linear_map` is `is_linear_map.mk' (f : M -> N) (sorry : is_linear_map f)`, and the idiom for making `is_linear_map` from `linear_map` is `f.is_linear` (i.e. `linear_map.is_linear f`).
- `is_linear_map.add` etc no longer exist. instead, you can now add two linear maps together, etc.
- the class`is_submodule` is gone, replaced by the structure `submodule` which contains a carrier, i.e. if `N : submodule R M` then `N.carrier` is a type. And there is an instance `module R N` in the same situation.
- similarly, the class `is_ideal` is gone, replaced by the structure `ideal`, which also contains a carrier.
- endomorphism ring and general linear group are defined.
- submodules form a complete lattice. the trivial ideal is now idiomatically the bottom element, and the universal ideal the top element.
- `linear_algebra/quotient_module.lean` is deleted, and it's now `submodule.quotient` (so if `N : submodule R M` then `submodule R N.quotient`) Similarly, `quotient_ring.quotient` is replaced by `ideal.quotient`. The canonical map from `N` to `N.quotient` is `submodule.quotient.mk`, and the canonical map from the ideal `I` to `I.quotient` is `ideal.quotient.mk I`.
- `linear_equiv` is now based on a linear map and an equiv, and the difference being that now you need to prove that the inverse is also linear, and there is currently no interface to get around that.
- Everything you want to know about linear independence and basis is now in the newly created file `linear_algebra/basis.lean`.
- Everything you want to know about linear combinations is now in the newly created file `linear_algebra/lc.lean`.
- `linear_algebra/linear_map_module.lean` and `linear_algebra/prod_module.lean` and `linear_algebra/quotient_module.lean` and `linear_algebra/submodule.lean` and `linear_algebra/subtype_module.lean` are deleted (with their contents placed elsewhere).
squashed commits:
* feat(linear_algebra/basic): product modules, cat/lat structure
* feat(linear_algebra/basic): refactoring quotient_module
* feat(linear_algebra/basic): merge in submodule.lean
* feat(linear_algebra/basic): merge in linear_map_module.lean
* refactor(linear_algebra/dimension): update for new modules
* feat(ring_theory/ideals): convert ideals
* refactor tensor product
* simplify local ring proof for Zp
* refactor(ring_theory/noetherian)
* refactor(ring_theory/localization)
* refactor(linear_algebra/tensor_product)
* feat(data/polynomial): lcoeff
#### Estimated changes
Modified algebra/module.lean
- \+/\- *lemma* smul_smul
- \+/\- *lemma* smul_eq_mul
- \+/\- *lemma* map_add
- \+ *lemma* map_smul
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_sum
- \+ *lemma* comp_apply
- \+ *lemma* id_apply
- \+ *lemma* zero_mem
- \+ *lemma* add_mem
- \+ *lemma* smul_mem
- \+ *lemma* neg_mem
- \+ *lemma* sub_mem
- \+ *lemma* neg_mem_iff
- \+ *lemma* add_mem_iff_left
- \+ *lemma* add_mem_iff_right
- \+ *lemma* sum_mem
- \+ *lemma* coe_add
- \+ *lemma* coe_zero
- \+ *lemma* coe_neg
- \+ *lemma* coe_smul
- \+ *lemma* coe_sub
- \+ *lemma* mul_mem_left
- \+ *lemma* mul_mem_right
- \- *lemma* smul_smul'
- \- *lemma* smul_eq_mul'
- \- *lemma* zero
- \- *lemma* neg
- \- *lemma* sub
- \- *lemma* sum
- \- *lemma* comp
- \- *lemma* id
- \- *lemma* inverse
- \- *lemma* map_smul_right
- \- *lemma* map_smul_left
- \- *lemma* add
- \- *lemma* smul_ne_0
- \- *lemma* Inter_submodule
- \+/\- *theorem* smul_add
- \+/\- *theorem* add_smul
- \+/\- *theorem* mul_smul
- \+/\- *theorem* one_smul
- \+/\- *theorem* zero_smul
- \+/\- *theorem* smul_zero
- \+ *theorem* is_linear
- \+ *theorem* ext
- \+ *theorem* ext_iff
- \+ *theorem* mk'_apply
- \+ *theorem* mem_coe
- \+ *theorem* ext'
- \+ *theorem* subtype_apply
- \+ *theorem* smul_mem_iff
- \- *theorem* smul_add'
- \- *theorem* add_smul'
- \- *theorem* mul_smul'
- \- *theorem* one_smul'
- \- *theorem* zero_smul'
- \- *theorem* smul_zero'
- \- *theorem* is_submodule.eq_univ_of_contains_unit
- \- *theorem* is_submodule.univ_of_one_mem
- \+ *def* module.of_core
- \+ *def* comp
- \+ *def* id
- \+ *def* mk'
- \+ *def* ideal
- \+/\- *def* subspace

Modified algebra/order.lean
- \+ *lemma* eq_iff_le_not_lt

Modified algebra/pi_instances.lean
- \+ *lemma* mk_mul_mk
- \+ *lemma* one_eq_mk
- \+ *lemma* inv_mk
- \+ *theorem* smul_fst
- \+ *theorem* smul_snd
- \+ *theorem* smul_mk

Modified analysis/bounded_linear_maps.lean
- \+/\- *lemma* tendsto

Modified analysis/normed_space.lean


Modified analysis/topology/quotient_topological_structures.lean
- \+/\- *lemma* quotient_ring.is_open_map_coe
- \+/\- *lemma* quotient_ring.quotient_map_coe_coe

Modified analysis/topology/topological_structures.lean
- \+ *lemma* ideal.coe_closure
- \+ *def* ideal.closure

Modified data/equiv/basic.lean
- \+ *def* prop_equiv_punit
- \+/\- *def* true_equiv_punit

Modified data/finsupp.lean
- \+ *lemma* map_range_zero
- \+ *lemma* map_range_add
- \+/\- *lemma* sum_single
- \+/\- *lemma* map_domain_id
- \+/\- *lemma* map_domain_zero
- \+ *lemma* filter_single_of_pos
- \+ *lemma* filter_single_of_neg
- \+/\- *lemma* filter_pos_add_filter_neg
- \+ *lemma* filter_add
- \+/\- *lemma* smul_apply'
- \+ *lemma* support_smul
- \+ *lemma* filter_smul
- \+ *lemma* map_domain_smul
- \+ *lemma* smul_single
- \+/\- *def* to_has_scalar'
- \+ *def* to_semimodule
- \+/\- *def* to_module
- \+/\- *def* to_has_scalar

Modified data/fintype.lean
- \+ *theorem* fintype.univ_of_subsingleton
- \+ *theorem* fintype.card_of_subsingleton
- \+ *def* of_subsingleton

Modified data/holor.lean


Modified data/padics/padic_integers.lean
- \+ *lemma* is_unit_iff
- \+ *lemma* norm_lt_one_add
- \+ *lemma* norm_lt_one_mul
- \+ *lemma* mem_nonunits
- \- *lemma* maximal_ideal_add
- \- *lemma* maximal_ideal_mul
- \- *lemma* maximal_ideal_ne_univ
- \- *lemma* maximal_ideal_eq_nonunits
- \- *lemma* maximal_ideal_eq_or_univ_of_subset
- \- *lemma* maximal_ideal_unique
- \- *def* maximal_ideal

Modified data/padics/padic_numbers.lean
- \+/\- *theorem* rat_dense'
- \+/\- *theorem* rat_dense
- \+/\- *def* padic
- \+/\- *def* padic_norm_e

Modified data/polynomial.lean
- \+ *lemma* lcoeff_apply
- \- *lemma* coeff_is_linear
- \+ *def* lcoeff

Modified data/set/basic.lean
- \+ *theorem* coe_nonempty_iff_ne_empty
- \+ *theorem* pairwise_on.mono
- \+ *theorem* pairwise_on.mono'

Modified data/set/lattice.lean
- \+/\- *theorem* disjoint_bot_left
- \+/\- *theorem* disjoint_bot_right

Modified group_theory/free_abelian_group.lean


Modified linear_algebra/basic.lean
- \+ *lemma* classical.some_spec3
- \+/\- *lemma* smul_sum
- \+ *lemma* zero_apply
- \+ *lemma* neg_apply
- \+ *lemma* add_apply
- \+ *lemma* sum_apply
- \+ *lemma* sub_apply
- \+ *lemma* one_app
- \+ *lemma* mul_app
- \+ *lemma* smul_apply
- \+ *lemma* le_def
- \+ *lemma* le_def'
- \+ *lemma* bot_coe
- \+ *lemma* mem_bot
- \+ *lemma* top_coe
- \+ *lemma* mem_top
- \+ *lemma* eq_top_iff'
- \+ *lemma* map_coe
- \+ *lemma* mem_map
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* map_mono
- \+ *lemma* comap_coe
- \+ *lemma* mem_comap
- \+ *lemma* comap_id
- \+ *lemma* comap_comp
- \+ *lemma* comap_mono
- \+ *lemma* comap_top
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* map_comap_le
- \+ *lemma* le_comap_map
- \+ *lemma* map_bot
- \+ *lemma* map_inf_eq_map_inf_comap
- \+ *lemma* map_comap_subtype
- \+ *lemma* mem_span
- \+ *lemma* span_le
- \+/\- *lemma* span_mono
- \+ *lemma* span_eq_of_le
- \+/\- *lemma* span_eq
- \+ *lemma* span_induction
- \+/\- *lemma* span_empty
- \+/\- *lemma* span_union
- \+ *lemma* span_Union
- \+ *lemma* mem_sup
- \+ *lemma* mem_span_singleton
- \+ *lemma* span_singleton_eq_range
- \+/\- *lemma* mem_span_insert
- \+ *lemma* mem_span_insert'
- \+/\- *lemma* span_insert_eq_span
- \+/\- *lemma* span_span
- \+ *lemma* span_eq_bot
- \+ *lemma* span_singleton_eq_bot
- \+ *lemma* span_image
- \+ *lemma* prod_coe
- \+ *lemma* mem_prod
- \+ *lemma* span_prod_le
- \+ *lemma* prod_top
- \+ *lemma* prod_bot
- \+ *lemma* prod_mono
- \+ *lemma* prod_inf_prod
- \+ *lemma* prod_sup_prod
- \+/\- *lemma* finsupp_sum
- \+ *lemma* range_le_iff_comap
- \+ *lemma* le_ker_iff_map
- \+ *lemma* map_comap_eq
- \+ *lemma* map_comap_eq_self
- \+ *lemma* comap_map_eq
- \+ *lemma* comap_map_eq_self
- \+ *lemma* span_inl_union_inr
- \+ *lemma* map_subtype_le
- \+ *lemma* map_subtype_embedding_eq
- \+ *lemma* le_comap_mkq
- \+ *lemma* comap_mkq_embedding_eq
- \- *lemma* is_linear_map_sum
- \- *lemma* linear_inv
- \- *lemma* span_eq_of_is_submodule
- \- *lemma* span_minimal
- \- *lemma* is_submodule_range_smul
- \- *lemma* span_singleton
- \- *lemma* span_insert
- \- *lemma* span_image_of_linear_map
- \- *lemma* linear_eq_on
- \- *lemma* linear_independent_empty
- \- *lemma* linear_independent.mono
- \- *lemma* zero_not_mem_of_linear_independent
- \- *lemma* linear_independent_union
- \- *lemma* linear_independent_Union_of_directed
- \- *lemma* linear_independent_bUnion_of_directed
- \- *lemma* linear_independent.unique
- \- *lemma* repr_not_span
- \- *lemma* repr_spec
- \- *lemma* repr_eq_zero
- \- *lemma* repr_sum_eq
- \- *lemma* repr_eq
- \- *lemma* repr_eq_single
- \- *lemma* repr_zero
- \- *lemma* repr_support
- \- *lemma* repr_add
- \- *lemma* repr_smul
- \- *lemma* repr_neg
- \- *lemma* repr_sub
- \- *lemma* repr_sum
- \- *lemma* repr_finsupp_sum
- \- *lemma* repr_eq_repr_of_subset
- \- *lemma* linear_independent.of_image
- \- *lemma* linear_independent.eq_0_of_span
- \- *lemma* is_basis.map_repr
- \- *lemma* is_basis.map_constr
- \- *lemma* is_basis.eq_linear_map
- \- *lemma* constr_congr
- \- *lemma* constr_basis
- \- *lemma* constr_eq
- \- *lemma* constr_zero
- \- *lemma* constr_add
- \- *lemma* constr_sub
- \- *lemma* constr_neg
- \- *lemma* constr_smul
- \- *lemma* constr_mem_span
- \- *lemma* constr_im_eq_span
- \- *lemma* linear_independent.inj_span_iff_inj
- \- *lemma* linear_independent.image
- \- *lemma* linear_map.linear_independent_image_iff
- \- *lemma* is_basis.linear_equiv
- \- *lemma* mem_span_insert_exchange
- \- *lemma* linear_independent_iff_not_mem_span
- \- *lemma* linear_independent_singleton
- \- *lemma* linear_independent.insert
- \- *lemma* exists_linear_independent
- \- *lemma* exists_subset_is_basis
- \- *lemma* exists_is_basis
- \- *lemma* eq_of_linear_independent_of_span
- \- *lemma* exists_of_linear_independent_of_finite_span
- \- *lemma* exists_finite_card_le_of_finite_of_linear_independent_of_span
- \- *lemma* exists_left_inverse_linear_map_of_injective
- \- *lemma* exists_right_inverse_linear_map_of_surjective
- \+ *theorem* comp_id
- \+ *theorem* id_comp
- \+ *theorem* cod_restrict_apply
- \+ *theorem* smul_right_apply
- \+ *theorem* fst_apply
- \+ *theorem* snd_apply
- \+ *theorem* pair_apply
- \+ *theorem* fst_pair
- \+ *theorem* snd_pair
- \+ *theorem* pair_fst_snd
- \+ *theorem* inl_apply
- \+ *theorem* inr_apply
- \+ *theorem* copair_apply
- \+ *theorem* copair_inl
- \+ *theorem* copair_inr
- \+ *theorem* copair_inl_inr
- \+ *theorem* fst_eq_copair
- \+ *theorem* snd_eq_copair
- \+ *theorem* inl_eq_pair
- \+ *theorem* inr_eq_pair
- \+ *theorem* of_le_apply
- \+ *theorem* inf_coe
- \+ *theorem* mem_inf
- \+ *theorem* Inf_coe
- \+ *theorem* infi_coe
- \+ *theorem* mem_infi
- \+ *theorem* disjoint_def
- \+ *theorem* Union_coe_of_directed
- \+ *theorem* mem_supr_of_directed
- \+ *theorem* mk_eq_mk
- \+ *theorem* mk'_eq_mk
- \+ *theorem* quot_mk_eq_mk
- \+ *theorem* mk_zero
- \+ *theorem* mk_eq_zero
- \+ *theorem* mk_add
- \+ *theorem* mk_neg
- \+ *theorem* mk_smul
- \+ *theorem* map_cod_restrict
- \+ *theorem* comap_cod_restrict
- \+ *theorem* range_coe
- \+ *theorem* mem_range
- \+ *theorem* range_id
- \+ *theorem* range_comp
- \+ *theorem* range_comp_le_range
- \+ *theorem* range_eq_top
- \+ *theorem* mem_ker
- \+ *theorem* ker_id
- \+ *theorem* ker_comp
- \+ *theorem* ker_le_ker_comp
- \+ *theorem* sub_mem_ker_iff
- \+ *theorem* disjoint_ker
- \+ *theorem* disjoint_ker'
- \+ *theorem* inj_of_disjoint_ker
- \+ *theorem* ker_eq_bot
- \+ *theorem* ker_zero
- \+ *theorem* ker_eq_top
- \+ *theorem* map_le_map_iff
- \+ *theorem* map_injective
- \+ *theorem* comap_le_comap_iff
- \+ *theorem* comap_injective
- \+ *theorem* map_copair_prod
- \+ *theorem* comap_pair_prod
- \+ *theorem* prod_eq_inf_comap
- \+ *theorem* prod_eq_sup_map
- \+ *theorem* map_top
- \+ *theorem* comap_bot
- \+ *theorem* ker_subtype
- \+ *theorem* range_subtype
- \+ *theorem* map_inl
- \+ *theorem* map_inr
- \+ *theorem* comap_fst
- \+ *theorem* comap_snd
- \+ *theorem* prod_comap_inl
- \+ *theorem* prod_comap_inr
- \+ *theorem* prod_map_fst
- \+ *theorem* prod_map_snd
- \+ *theorem* ker_inl
- \+ *theorem* ker_inr
- \+ *theorem* range_fst
- \+ *theorem* range_snd
- \+ *theorem* mkq_apply
- \+ *theorem* liftq_apply
- \+ *theorem* liftq_mkq
- \+ *theorem* range_mkq
- \+ *theorem* ker_mkq
- \+ *theorem* mkq_map_self
- \+ *theorem* comap_map_mkq
- \+ *theorem* mapq_apply
- \+ *theorem* mapq_mkq
- \+ *theorem* comap_liftq
- \+ *theorem* ker_liftq
- \+ *theorem* ker_liftq_eq_bot
- \+ *theorem* apply_symm_apply
- \+ *theorem* symm_apply_apply
- \+ *theorem* coe_apply
- \+ *theorem* of_bijective_apply
- \+ *theorem* of_linear_apply
- \+ *theorem* of_linear_symm_apply
- \+ *theorem* of_top_apply
- \+ *theorem* of_top_symm_apply
- \+ *def* cod_restrict
- \+ *def* inverse
- \+ *def* smul_right
- \+ *def* endomorphism_ring
- \+ *def* general_linear_group
- \+ *def* fst
- \+ *def* snd
- \+ *def* pair
- \+ *def* inl
- \+ *def* inr
- \+ *def* copair
- \+ *def* congr_right
- \+ *def* of_le
- \+ *def* map
- \+ *def* comap
- \+/\- *def* span
- \+ *def* prod
- \+ *def* quotient_rel
- \+ *def* quotient
- \+ *def* mk
- \+ *def* range
- \+ *def* ker
- \+ *def* map_subtype.order_iso
- \+ *def* map_subtype.le_order_embedding
- \+ *def* map_subtype.lt_order_embedding
- \+ *def* mkq
- \+ *def* liftq
- \+ *def* mapq
- \+ *def* comap_mkq.order_iso
- \+ *def* comap_mkq.le_order_embedding
- \+ *def* comap_mkq.lt_order_embedding
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* trans
- \+ *def* of_linear
- \+ *def* of_top
- \- *def* lc
- \- *def* linear_independent
- \- *def* linear_independent.repr
- \- *def* is_basis
- \- *def* is_basis.constr
- \- *def* module_equiv_lc
- \- *def* equiv_of_is_basis

Created linear_algebra/basis.lean
- \+ *lemma* linear_independent_empty
- \+ *lemma* linear_independent.mono
- \+ *lemma* linear_independent.unique
- \+ *lemma* zero_not_mem_of_linear_independent
- \+ *lemma* linear_independent_union
- \+ *lemma* linear_independent_of_finite
- \+ *lemma* linear_independent_Union_of_directed
- \+ *lemma* linear_independent_sUnion_of_directed
- \+ *lemma* linear_independent_bUnion_of_directed
- \+ *lemma* linear_independent.total_repr
- \+ *lemma* linear_independent.total_comp_repr
- \+ *lemma* linear_independent.repr_ker
- \+ *lemma* linear_independent.repr_range
- \+ *lemma* linear_independent.repr_eq
- \+ *lemma* linear_independent.repr_eq_single
- \+ *lemma* linear_independent.repr_supported
- \+ *lemma* linear_independent.repr_eq_repr_of_subset
- \+ *lemma* linear_independent_iff_not_smul_mem_span
- \+ *lemma* eq_of_linear_independent_of_span
- \+ *lemma* linear_independent.supported_disjoint_ker
- \+ *lemma* linear_independent.of_image
- \+ *lemma* linear_independent.disjoint_ker
- \+ *lemma* linear_independent.inj_span_iff_inj
- \+ *lemma* linear_independent.image
- \+ *lemma* linear_map.linear_independent_image_iff
- \+ *lemma* linear_independent_inl_union_inr
- \+ *lemma* is_basis.mem_span
- \+ *lemma* is_basis.total_repr
- \+ *lemma* is_basis.total_comp_repr
- \+ *lemma* is_basis.repr_ker
- \+ *lemma* is_basis.repr_range
- \+ *lemma* is_basis.repr_supported
- \+ *lemma* is_basis.repr_eq_single
- \+ *lemma* is_basis.ext
- \+ *lemma* constr_congr
- \+ *lemma* constr_basis
- \+ *lemma* constr_eq
- \+ *lemma* constr_self
- \+ *lemma* constr_zero
- \+ *lemma* constr_add
- \+ *lemma* constr_neg
- \+ *lemma* constr_sub
- \+ *lemma* constr_smul
- \+ *lemma* constr_range
- \+ *lemma* is_basis_inl_union_inr
- \+ *lemma* linear_equiv.is_basis
- \+ *lemma* mem_span_insert_exchange
- \+ *lemma* linear_independent_iff_not_mem_span
- \+ *lemma* linear_independent_singleton
- \+ *lemma* disjoint_span_singleton
- \+ *lemma* linear_independent.insert
- \+ *lemma* exists_linear_independent
- \+ *lemma* exists_subset_is_basis
- \+ *lemma* exists_is_basis
- \+ *lemma* exists_of_linear_independent_of_finite_span
- \+ *lemma* exists_finite_card_le_of_finite_of_linear_independent_of_span
- \+ *lemma* exists_left_inverse_linear_map_of_injective
- \+ *lemma* exists_right_inverse_linear_map_of_surjective
- \+ *theorem* linear_independent_iff
- \+ *theorem* linear_independent_iff_total_on
- \+ *theorem* is_basis.constr_apply
- \+ *theorem* quotient_prod_linear_equiv
- \+ *def* linear_independent
- \+ *def* linear_independent.total_equiv
- \+ *def* linear_independent.repr
- \+ *def* is_basis
- \+ *def* is_basis.repr
- \+ *def* is_basis.constr
- \+ *def* module_equiv_lc
- \+ *def* equiv_of_is_basis

Modified linear_algebra/dimension.lean
- \+ *theorem* is_basis.le_span
- \+/\- *theorem* mk_eq_mk_of_basis
- \+ *theorem* is_basis.mk_eq_dim
- \+ *theorem* linear_equiv.dim_eq
- \+/\- *theorem* dim_quotient
- \+ *theorem* dim_range_add_dim_ker
- \- *theorem* basis_le_span
- \- *theorem* mk_basis
- \- *theorem* dim_eq_of_linear_equiv
- \- *theorem* dim_im_add_dim_ker
- \+ *def* vector_space.dim
- \- *def* dim

Created linear_algebra/lc.lean
- \+ *lemma* linear_eq_on
- \+ *theorem* mem_supported
- \+ *theorem* mem_supported'
- \+ *theorem* single_mem_supported
- \+ *theorem* supported_eq_span_single
- \+ *theorem* restrict_dom_apply
- \+ *theorem* restrict_dom_comp_subtype
- \+ *theorem* range_restrict_dom
- \+ *theorem* supported_mono
- \+ *theorem* supported_empty
- \+ *theorem* supported_univ
- \+ *theorem* supported_Union
- \+ *theorem* supported_union
- \+ *theorem* supported_Inter
- \+ *theorem* apply_apply
- \+ *theorem* lsum_apply
- \+ *theorem* total_apply
- \+ *theorem* total_single
- \+ *theorem* total_range
- \+ *theorem* map_apply
- \+ *theorem* map_id
- \+ *theorem* map_comp
- \+ *theorem* supported_comap_map
- \+ *theorem* map_supported
- \+ *theorem* map_disjoint_ker
- \+ *theorem* map_total
- \+ *theorem* span_eq_map_lc
- \+ *theorem* mem_span_iff_lc
- \+ *theorem* lc.total_on_range
- \+ *def* lc
- \+ *def* supported
- \+ *def* restrict_dom
- \+ *def* apply
- \+ *def* lc.total_on

Deleted linear_algebra/linear_map_module.lean
- \- *lemma* is_linear_map_coe
- \- *lemma* map_add
- \- *lemma* map_smul
- \- *lemma* map_zero
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *lemma* mem_ker
- \- *lemma* mem_im
- \- *lemma* is_submodule.add_left_iff
- \- *lemma* is_submodule.neg_iff
- \- *lemma* add_app
- \- *lemma* zero_app
- \- *lemma* neg_app
- \- *lemma* smul_app
- \- *lemma* one_app
- \- *lemma* mul_app
- \- *theorem* ext
- \- *theorem* ker_of_map_eq_map
- \- *theorem* inj_of_trivial_ker
- \- *theorem* sub_ker
- \- *def* linear_map
- \- *def* ker
- \- *def* im
- \- *def* quot_ker_equiv_im
- \- *def* union_quotient_equiv_quotient_inter
- \- *def* endomorphism_ring
- \- *def* general_linear_group

Modified linear_algebra/multivariate_polynomial.lean


Deleted linear_algebra/prod_module.lean
- \- *lemma* is_linear_map_prod_fst
- \- *lemma* is_linear_map_prod_snd
- \- *lemma* is_linear_map_prod_mk
- \- *lemma* is_linear_map_prod_inl
- \- *lemma* is_linear_map_prod_inr
- \- *lemma* span_prod
- \- *lemma* span_inl_union_inr
- \- *lemma* linear_independent_inl_union_inr
- \- *lemma* is_basis_inl_union_inr

Deleted linear_algebra/quotient_module.lean
- \- *lemma* coe_zero
- \- *lemma* coe_smul
- \- *lemma* coe_add
- \- *lemma* coe_eq_zero
- \- *lemma* is_linear_map_quotient_mk
- \- *lemma* quotient.lift_mk
- \- *lemma* is_linear_map_quotient_lift
- \- *lemma* quotient.injective_lift
- \- *lemma* quotient.exists_rep
- \- *theorem* quotient_prod_linear_equiv
- \- *def* quotient_rel
- \- *def* quotient
- \- *def* mk
- \- *def* quotient.lift

Deleted linear_algebra/submodule.lean
- \- *lemma* span_singleton_subset
- \- *lemma* mem_span_singleton
- \- *lemma* coe_map
- \- *lemma* map_id
- \- *lemma* map_comp
- \- *lemma* injective_map
- \- *lemma* coe_comap
- \- *lemma* comap_id
- \- *lemma* comap_comp
- \- *lemma* injective_comap
- \- *lemma* comap_map_eq
- \- *lemma* map_subtype_subset
- \- *lemma* map_subtype_embedding_eq
- \- *lemma* subset_comap_quotient
- \- *lemma* coe_prod
- \- *theorem* mem_coe
- \- *theorem* ext
- \- *theorem* span_subset_iff
- \- *theorem* sInter_set
- \- *theorem* bot_set
- \- *theorem* span_empty
- \- *theorem* top_set
- \- *theorem* Union_set_of_directed
- \- *theorem* span_union
- \- *def* span
- \- *def* map
- \- *def* comap
- \- *def* map_subtype
- \- *def* map_subtype.order_iso
- \- *def* map_subtype.le_order_embedding
- \- *def* lt_order_embedding
- \- *def* comap_quotient
- \- *def* comap_quotient.order_iso
- \- *def* prod
- \- *def* le_order_embedding

Deleted linear_algebra/subtype_module.lean
- \- *lemma* coe_add
- \- *lemma* coe_zero
- \- *lemma* coe_neg
- \- *lemma* coe_smul
- \- *lemma* sub_val
- \- *lemma* is_linear_map_coe
- \- *lemma* is_linear_map_subtype_val
- \- *lemma* is_linear_map_subtype_mk

Modified linear_algebra/tensor_product.lean
- \+/\- *lemma* add_tmul
- \+/\- *lemma* tmul_add
- \+/\- *lemma* smul_tmul
- \+/\- *lemma* tmul_smul
- \+ *lemma* mk_apply
- \+ *lemma* zero_tmul
- \+ *lemma* tmul_zero
- \+ *lemma* neg_tmul
- \+ *lemma* tmul_neg
- \+ *lemma* lift_aux.add
- \+ *lemma* lift_aux.smul
- \+ *lemma* lift.tmul
- \+ *lemma* lift.tmul'
- \- *lemma* tmul.add_left
- \- *lemma* tmul.add_right
- \- *lemma* tmul.smul
- \- *lemma* smul.is_add_group_hom
- \- *lemma* to_module.add
- \- *lemma* to_module.smul
- \- *lemma* to_module.tmul
- \+ *theorem* mk₂_apply
- \+ *theorem* ext₂
- \+ *theorem* flip_apply
- \+ *theorem* flip_inj
- \+ *theorem* lflip_apply
- \+ *theorem* map_zero₂
- \+ *theorem* map_neg₂
- \+ *theorem* map_add₂
- \+ *theorem* map_smul₂
- \+ *theorem* lcomp_apply
- \+ *theorem* llcomp_apply
- \+ *theorem* compl₂_apply
- \+ *theorem* compr₂_apply
- \+ *theorem* lsmul_apply
- \+ *theorem* lift.unique
- \+ *theorem* lift_mk
- \+ *theorem* lift_compr₂
- \+ *theorem* lift_mk_compr₂
- \+ *theorem* ext
- \+ *theorem* mk_compr₂_inj
- \+ *theorem* uncurry_apply
- \+ *theorem* lcurry_apply
- \+ *theorem* curry_apply
- \+ *theorem* map_tmul
- \- *theorem* zero_left
- \- *theorem* zero_right
- \- *theorem* neg_left
- \- *theorem* neg_right
- \- *theorem* linear_left
- \- *theorem* linear_right
- \- *theorem* comm
- \- *theorem* comp
- \- *theorem* bilinear
- \- *theorem* to_module.unique
- \- *theorem* to_module.ext
- \+ *def* mk₂
- \+ *def* flip
- \+ *def* lflip
- \+ *def* lcomp
- \+ *def* llcomp
- \+ *def* compl₂
- \+ *def* compr₂
- \+ *def* lsmul
- \+/\- *def* smul.aux
- \+ *def* mk
- \+ *def* lift_aux
- \+ *def* lift
- \+ *def* uncurry
- \+ *def* lift.equiv
- \+ *def* lcurry
- \+ *def* curry
- \+ *def* map
- \+ *def* congr
- \- *def* smul
- \- *def* to_module
- \- *def* to_module.linear
- \- *def* to_module.equiv

Modified logic/basic.lean


Modified order/zorn.lean
- \+ *theorem* chain.mono
- \+ *theorem* zorn_subset₀

Modified ring_theory/associated.lean
- \+ *theorem* is_unit_zero_iff
- \+/\- *theorem* not_is_unit_zero
- \+ *theorem* is_unit_iff_exists_inv
- \+ *theorem* is_unit_iff_exists_inv'
- \+ *theorem* is_unit_of_mul_is_unit_left
- \+ *theorem* is_unit_of_mul_is_unit_right
- \+ *theorem* mul_dvd_of_is_unit_left
- \+ *theorem* mul_dvd_of_is_unit_right
- \+ *theorem* nonzero_of_irreducible

Modified ring_theory/ideals.lean
- \+ *lemma* subset_span
- \+ *lemma* span_le
- \+ *lemma* span_mono
- \+ *lemma* span_eq
- \+ *lemma* span_singleton_one
- \+ *lemma* mem_span_insert
- \+ *lemma* mem_span_insert'
- \+ *lemma* mem_span_singleton'
- \+ *lemma* mem_span_singleton
- \+ *lemma* span_singleton_le_span_singleton
- \+ *lemma* span_eq_bot
- \+ *lemma* span_singleton_eq_bot
- \+ *lemma* span_singleton_eq_top
- \+ *lemma* mk_one
- \+ *lemma* mk_zero
- \+ *lemma* mk_add
- \+ *lemma* mk_neg
- \+ *lemma* mk_sub
- \+ *lemma* mk_pow
- \+/\- *lemma* eq_zero_iff_mem
- \+/\- *lemma* exists_inv
- \- *lemma* neg_iff
- \- *lemma* mul_left
- \- *lemma* mul_right
- \- *lemma* mem_trivial
- \- *lemma* is_proper_ideal_iff_one_not_mem
- \- *lemma* coe_zero
- \- *lemma* coe_one
- \- *lemma* coe_add
- \- *lemma* coe_mul
- \- *lemma* coe_neg
- \- *lemma* coe_sub
- \- *lemma* coe_pow
- \+ *theorem* eq_top_of_unit_mem
- \+ *theorem* eq_top_of_is_unit_mem
- \+ *theorem* eq_top_iff_one
- \+ *theorem* ne_top_iff_one
- \+ *theorem* mem_comap
- \+ *theorem* comap_ne_top
- \+ *theorem* is_prime.mem_or_mem
- \+ *theorem* is_prime.mem_or_mem_of_mul_eq_zero
- \+ *theorem* span_singleton_prime
- \+ *theorem* is_maximal_iff
- \+ *theorem* is_maximal.eq_of_le
- \+ *theorem* is_maximal.exists_inv
- \+ *theorem* is_maximal.is_prime
- \+ *theorem* exists_le_maximal
- \+ *theorem* mem_nonunits_iff
- \+ *theorem* mul_mem_nonunits_right
- \+ *theorem* mul_mem_nonunits_left
- \+ *theorem* zero_mem_nonunits
- \+ *theorem* one_not_mem_nonunits
- \+ *theorem* coe_subset_nonunits
- \+ *theorem* mem_nonunits_ideal
- \+ *theorem* local_of_nonunits_ideal
- \+ *theorem* mk_mul
- \+ *theorem* zero_eq_one_iff
- \+ *theorem* zero_ne_one_iff
- \- *theorem* mem_or_mem_of_mul_eq_zero
- \- *theorem* is_maximal_ideal.mk
- \- *theorem* not_unit_of_mem_proper_ideal
- \+ *def* span
- \+ *def* comap
- \+ *def* is_prime
- \+ *def* zero_ne_one_of_proper
- \+ *def* is_maximal
- \+/\- *def* nonunits
- \+ *def* is_local_ring
- \+ *def* is_local_ring.zero_ne_one
- \+ *def* nonunits_ideal
- \+/\- *def* quotient
- \+/\- *def* mk
- \+ *def* map_mk
- \- *def* trivial
- \- *def* local_of_nonunits_ideal
- \- *def* quotient_rel

Modified ring_theory/localization.lean
- \+/\- *lemma* ne_zero_of_mem_non_zero_divisors

Modified ring_theory/matrix.lean


Modified ring_theory/noetherian.lean
- \+/\- *theorem* ring.is_noetherian_of_fintype
- \+/\- *theorem* is_noetherian_of_submodule_of_noetherian
- \+/\- *theorem* is_noetherian_of_quotient_of_noetherian
- \+/\- *def* fg
- \+/\- *def* is_noetherian
- \- *def* is_fg

Modified ring_theory/principal_ideal_domain.lean
- \+ *lemma* span_singleton_generator
- \+/\- *lemma* generator_mem
- \+/\- *lemma* mem_iff_generator_dvd
- \+ *lemma* eq_bot_iff_generator_eq_zero
- \+/\- *lemma* to_maximal_ideal
- \+/\- *lemma* mod_mem_iff
- \+ *lemma* is_maximal_of_irreducible
- \- *lemma* generator_generates
- \- *lemma* eq_trivial_iff_generator_eq_zero
- \- *lemma* is_maximal_ideal_of_irreducible

Modified set_theory/cardinal.lean
- \+ *theorem* mk_emptyc
- \+ *theorem* mk_plift_of_false
- \+ *theorem* mk_plift_of_true
- \+ *theorem* mk_union_of_disjoint
- \- *theorem* mk_empty'
- \- *theorem* mk_plift_false
- \- *theorem* mk_plift_true
- \- *theorem* mk_union_of_disjiont

Modified set_theory/ordinal.lean




## [2018-11-05 10:08:52-05:00](https://github.com/leanprover-community/mathlib/commit/37c0d53)
refactor(field_theory/finite): generalize proofs ([#429](https://github.com/leanprover-community/mathlib/pull/429))
#### Estimated changes
Modified data/equiv/algebra.lean
- \+ *lemma* coe_units_equiv_ne_zero
- \+ *def* units_equiv_ne_zero

Modified data/nat/gcd.lean
- \+ *lemma* gcd_mul_left_left
- \+ *lemma* gcd_mul_left_right
- \+ *lemma* gcd_mul_right_left
- \+ *lemma* gcd_mul_right_right
- \+ *lemma* gcd_gcd_self_right_left
- \+ *lemma* gcd_gcd_self_right_right
- \+ *lemma* gcd_gcd_self_left_right
- \+ *lemma* gcd_gcd_self_left_left

Modified data/zmod/quadratic_reciprocity.lean


Modified field_theory/finite.lean
- \+ *lemma* card_nth_roots_subgroup_units
- \+/\- *lemma* card_units
- \+/\- *lemma* prod_univ_units_id_eq_neg_one
- \- *lemma* order_of_pow
- \- *lemma* coe_units_equiv_ne_zero
- \- *lemma* card_nth_roots_units
- \- *lemma* card_pow_eq_one_eq_order_of
- \- *lemma* card_order_of_eq_totient
- \- *def* units_equiv_ne_zero

Modified group_theory/order_of_element.lean
- \+ *lemma* order_of_pow
- \+ *lemma* pow_gcd_card_eq_one_iff
- \+ *lemma* order_of_eq_card_of_forall_mem_gpowers
- \+ *lemma* is_cyclic.card_pow_eq_one_le
- \+ *lemma* card_pow_eq_one_eq_order_of_aux
- \+ *lemma* card_order_of_eq_totient_aux₂
- \+ *lemma* is_cyclic_of_card_pow_eq_one_le
- \+ *lemma* is_cyclic.card_order_of_eq_totient
- \- *lemma* order_of_eq_card_of_forall_mem_gppowers
- \+ *def* is_cyclic.comm_group



## [2018-11-05 09:56:33-05:00](https://github.com/leanprover-community/mathlib/commit/a64be8d)
feat(category/bifunctor): Bifunctor and bitraversable ([#255](https://github.com/leanprover-community/mathlib/pull/255))
#### Estimated changes
Modified category/applicative.lean


Created category/bifunctor.lean
- \+ *lemma* id_fst
- \+ *lemma* id_snd
- \+ *lemma* comp_fst
- \+ *lemma* fst_snd
- \+ *lemma* snd_fst
- \+ *lemma* comp_snd
- \+ *def* fst
- \+ *def* snd
- \+ *def* bicompl
- \+ *def* bicompr

Created category/bitraversable/basic.lean
- \+ *def* bisequence

Created category/bitraversable/instances.lean
- \+ *def* prod.bitraverse
- \+ *def* sum.bitraverse
- \+ *def* const.bitraverse
- \+ *def* flip.bitraverse
- \+ *def* bicompl.bitraverse
- \+ *def* bicompr.bitraverse

Created category/bitraversable/lemmas.lean
- \+ *lemma* id_tfst
- \+ *lemma* id_tsnd
- \+ *lemma* comp_tfst
- \+ *lemma* tfst_tsnd
- \+ *lemma* tsnd_tfst
- \+ *lemma* comp_tsnd
- \+ *lemma* tfst_eq_fst_id
- \+ *lemma* tsnd_eq_snd_id
- \+ *def* tfst
- \+ *def* tsnd

Modified category/functor.lean
- \+ *def* const
- \+ *def* add_const
- \+ *def* const.mk
- \+ *def* const.run

Modified category/traversable/instances.lean


Modified data/sum.lean
- \- *def* map

Modified tactic/basic.lean




## [2018-11-05 09:50:04-05:00](https://github.com/leanprover-community/mathlib/commit/d556d6a)
refactor(topology/topological_space): rename open_set to opens and unbundle it ([#427](https://github.com/leanprover-community/mathlib/pull/427))
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* ext
- \+ *lemma* Sup_s
- \+ *lemma* is_basis_iff_nbhd
- \+ *lemma* is_basis_iff_cover
- \+ *def* opens
- \+ *def* interior
- \+ *def* gc
- \+ *def* gi
- \+ *def* is_basis

Modified category_theory/examples/topological_spaces.lean
- \+/\- *lemma* map_id_obj
- \+/\- *def* nbhd
- \+/\- *def* map_id
- \+/\- *def* map_iso



## [2018-11-05 09:43:52-05:00](https://github.com/leanprover-community/mathlib/commit/dcd90a3)
feat(order/filter): ultrafilter monad and the Stone-Cech compactification ([#434](https://github.com/leanprover-community/mathlib/pull/434))
* feat(order/filter): simplify theory of ultrafilters slightly
Introduce an alternate characterization of ultrafilters, and use it
to prove ultrafilter_map and ultrafilter_pure.
* chore(*): rename ultrafilter to is_ultrafilter
* feat(order/filter): the ultrafilter monad
* feat(analysis/topology): closure, continuous maps and T2 spaces via ultrafilters
For these, first prove that a filter is the intersection of the ultrafilters
containing it.
* feat(analysis/topology): Normal spaces. Compact Hausdorff spaces are normal.
* feat(analysis/topology/stone_cech): the Stone-Čech compactification
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* continuous_at_iff_ultrafilter
- \+ *lemma* continuous_iff_ultrafilter
- \+ *lemma* compact_of_closed
- \+ *lemma* normal_of_compact_t2

Created analysis/topology/stone_cech.lean
- \+ *lemma* ultrafilter_basis_is_basis
- \+ *lemma* ultrafilter_is_open_basic
- \+ *lemma* ultrafilter_is_closed_basic
- \+ *lemma* ultrafilter_converges_iff
- \+ *lemma* ultrafilter_comap_pure_nhds
- \+ *lemma* ultrafilter_pure_injective
- \+ *lemma* dense_embedding_pure
- \+ *lemma* ultrafilter_extend_extends
- \+ *lemma* continuous_ultrafilter_extend
- \+ *lemma* ultrafilter_extend_eq_iff
- \+ *lemma* stone_cech_unit_dense
- \+ *lemma* stone_cech_extend_extends
- \+ *lemma* continuous_stone_cech_extend
- \+ *lemma* convergent_eqv_pure
- \+ *lemma* continuous_stone_cech_unit
- \+ *def* ultrafilter_basis
- \+ *def* ultrafilter.extend
- \+ *def* stone_cech
- \+ *def* stone_cech_unit
- \+ *def* stone_cech_extend

Modified analysis/topology/topological_space.lean
- \+ *lemma* mem_closure_iff_ultrafilter
- \+ *lemma* t2_iff_nhds
- \+ *lemma* t2_iff_ultrafilter

Modified analysis/topology/uniform_space.lean


Modified order/filter.lean
- \+ *lemma* range_mem_map
- \+/\- *lemma* ultrafilter_unique
- \+/\- *lemma* le_of_ultrafilter
- \+ *lemma* ultrafilter_iff_compl_mem_iff_not_mem
- \+/\- *lemma* mem_or_compl_mem_of_ultrafilter
- \+/\- *lemma* mem_or_mem_of_ultrafilter
- \+/\- *lemma* mem_of_finite_sUnion_ultrafilter
- \+/\- *lemma* ultrafilter_map
- \+/\- *lemma* ultrafilter_pure
- \+ *lemma* ultrafilter_bind
- \+/\- *lemma* exists_ultrafilter
- \+/\- *lemma* ultrafilter_of_spec
- \+/\- *lemma* ultrafilter_ultrafilter_of
- \+/\- *lemma* ultrafilter_of_ultrafilter
- \+ *lemma* sup_of_ultrafilters
- \+ *lemma* tendsto_iff_ultrafilter
- \+ *lemma* ultrafilter.eq_iff_val_le_val
- \+ *lemma* exists_ultrafilter_iff
- \- *lemma* ultrafilter_of_split
- \+ *def* is_ultrafilter
- \+/\- *def* ultrafilter
- \+ *def* ultrafilter.map
- \+ *def* ultrafilter.pure
- \+ *def* ultrafilter.bind



## [2018-11-05 09:39:57-05:00](https://github.com/leanprover-community/mathlib/commit/62538c8)
feat(analysis/metric_spaces): Compact and proper spaces ([#430](https://github.com/leanprover-community/mathlib/pull/430))
#### Estimated changes
Modified analysis/metric_space.lean
- \+ *lemma* second_countable_of_separable_metric_space
- \+ *lemma* finite_cover_balls_of_compact
- \+ *lemma* countable_closure_of_compact
- \+ *theorem* ball_subset_closed_ball
- \+ *theorem* mem_closure_iff'

Modified analysis/topology/continuity.lean
- \+ *lemma* compact_univ
- \- *lemma* locally_compact_of_compact

Modified analysis/topology/uniform_space.lean
- \+ *lemma* complete_of_compact_set

Modified data/real/basic.lean
- \+ *lemma* le_of_forall_epsilon_le



## [2018-11-05 09:03:45-05:00](https://github.com/leanprover-community/mathlib/commit/47a0a22)
fix(algebra/ordered_group): make instances defeq ([#442](https://github.com/leanprover-community/mathlib/pull/442))
#### Estimated changes
Modified algebra/ordered_group.lean




## [2018-11-05 09:03:15-05:00](https://github.com/leanprover-community/mathlib/commit/8ae3fb8)
feat(ring_theory/subring): ring.closure ([#444](https://github.com/leanprover-community/mathlib/pull/444))
#### Estimated changes
Modified group_theory/subgroup.lean
- \+ *theorem* in_closure.rec_on

Modified group_theory/submonoid.lean
- \+ *theorem* in_closure.rec_on

Modified ring_theory/subring.lean
- \+ *theorem* exists_list_of_mem_closure
- \+ *theorem* mem_closure
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* closure_subset_iff
- \+ *def* closure



## [2018-11-05 09:01:57-05:00](https://github.com/leanprover-community/mathlib/commit/849d2a4)
feat(analysis/topology/topological_space): define T0 spaces, T4 spaces, connected and irreducible sets and components ([#448](https://github.com/leanprover-community/mathlib/pull/448))
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+/\- *lemma* is_closed_imp
- \+/\- *lemma* closure_singleton
- \+ *theorem* is_clopen_union
- \+ *theorem* is_clopen_inter
- \+ *theorem* is_clopen_empty
- \+ *theorem* is_clopen_univ
- \+ *theorem* is_clopen_compl
- \+ *theorem* is_clopen_compl_iff
- \+ *theorem* is_clopen_diff
- \+ *theorem* is_irreducible_empty
- \+ *theorem* is_irreducible_singleton
- \+ *theorem* is_irreducible_closure
- \+ *theorem* exists_irreducible
- \+ *theorem* is_irreducible_irreducible_component
- \+ *theorem* mem_irreducible_component
- \+ *theorem* eq_irreducible_component
- \+ *theorem* is_closed_irreducible_component
- \+ *theorem* irreducible_exists_mem_inter
- \+ *theorem* is_connected_of_is_irreducible
- \+ *theorem* is_connected_empty
- \+ *theorem* is_connected_singleton
- \+ *theorem* is_connected_sUnion
- \+ *theorem* is_connected_union
- \+ *theorem* is_connected_closure
- \+ *theorem* is_connected_connected_component
- \+ *theorem* mem_connected_component
- \+ *theorem* subset_connected_component
- \+ *theorem* is_closed_connected_component
- \+ *theorem* irreducible_component_subset_connected_component
- \+ *theorem* exists_mem_inter
- \+ *theorem* is_clopen_iff
- \+ *theorem* is_totally_disconnected_empty
- \+ *theorem* is_totally_disconnected_singleton
- \+ *theorem* is_totally_separated_empty
- \+ *theorem* is_totally_separated_singleton
- \+ *theorem* is_totally_disconnected_of_is_totally_separated
- \+ *theorem* exists_open_singleton_of_fintype
- \+ *theorem* normal_separation
- \+ *def* is_clopen
- \+ *def* is_irreducible
- \+ *def* irreducible_component
- \+ *def* is_connected
- \+ *def* connected_component
- \+ *def* is_totally_disconnected
- \+ *def* is_totally_separated



## [2018-11-05 08:59:28-05:00](https://github.com/leanprover-community/mathlib/commit/8898f0e)
feat(data/real/irrational): add basic irrational facts ([#453](https://github.com/leanprover-community/mathlib/pull/453))
Joint work by Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Kenny Lau, and Chris Hughes
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* int.nat_abs_pow

Created data/int/sqrt.lean
- \+ *theorem* sqrt_eq
- \+ *theorem* exists_mul_self
- \+ *theorem* sqrt_nonneg
- \+ *def* sqrt

Modified data/nat/sqrt.lean
- \+ *theorem* exists_mul_self

Modified data/padics/padic_norm.lean


Modified data/rat.lean
- \+ *theorem* cast_pow
- \+ *theorem* mk_pnat_num
- \+ *theorem* mk_pnat_denom
- \+ *theorem* mul_num
- \+ *theorem* mul_denom
- \+ *theorem* mul_self_num
- \+ *theorem* mul_self_denom
- \+ *theorem* abs_def
- \+ *theorem* sqrt_eq
- \+ *theorem* exists_mul_self
- \+ *theorem* sqrt_nonneg
- \+ *def* sqrt

Modified data/real/irrational.lean
- \+ *theorem* irr_nrt_of_notint_nrt
- \+ *theorem* irr_nrt_of_n_not_dvd_padic_val
- \+ *theorem* irr_sqrt_of_padic_val_odd
- \+ *theorem* irr_sqrt_of_prime
- \+ *theorem* irr_sqrt_two
- \+ *theorem* irr_sqrt_rat_iff
- \+ *theorem* irr_rat_add_of_irr
- \+ *theorem* irr_rat_add_iff_irr
- \+ *theorem* irr_add_rat_iff_irr
- \+ *theorem* irr_mul_rat_iff_irr
- \+ *theorem* irr_of_irr_mul_self
- \+ *theorem* irr_neg
- \- *theorem* sqrt_two_irrational



## [2018-11-05 08:57:04-05:00](https://github.com/leanprover-community/mathlib/commit/94b09d6)
refactor(data/real/basic): make real irreducible ([#454](https://github.com/leanprover-community/mathlib/pull/454))
#### Estimated changes
Modified analysis/complex.lean


Modified analysis/limits.lean
- \+/\- *lemma* tendsto_pow_at_top_at_top_of_gt_1_nat

Modified analysis/real.lean


Modified data/complex/basic.lean
- \+/\- *lemma* of_real_add
- \+/\- *lemma* of_real_bit0
- \+/\- *lemma* of_real_bit1
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* I_mul_I
- \+/\- *lemma* conj_of_real
- \+/\- *lemma* conj_zero
- \+/\- *lemma* conj_one
- \+/\- *lemma* conj_I
- \+/\- *lemma* conj_neg_I
- \+/\- *lemma* norm_sq_zero
- \+/\- *lemma* norm_sq_one
- \+/\- *lemma* norm_sq_I
- \+/\- *lemma* of_real_sub

Modified data/complex/exponential.lean


Modified data/padics/hensel.lean


Modified data/real/basic.lean
- \+ *theorem* mk_eq
- \+ *theorem* quotient_mk_eq_mk
- \+ *theorem* mk_eq_mk
- \+ *def* mk
- \+ *def* comm_ring_aux



## [2018-11-05 08:56:18-05:00](https://github.com/leanprover-community/mathlib/commit/c57a9a6)
fix(category_theory/isomorphism): use `category_theory.inv` in simp lemmas
`category_theory.is_iso.inv` is not the preferred name for this.
#### Estimated changes
Modified category_theory/isomorphism.lean
- \+/\- *def* hom_inv_id
- \+/\- *def* inv_hom_id



## [2018-11-05 08:53:41-05:00](https://github.com/leanprover-community/mathlib/commit/354d59e)
feat(data/nat/basic,algebra/ring): adding two lemmas about division ([#385](https://github.com/leanprover-community/mathlib/pull/385))
#### Estimated changes
Modified algebra/ring.lean


Modified data/nat/basic.lean




## [2018-11-05 13:47:01+01:00](https://github.com/leanprover-community/mathlib/commit/279b9ed)
feat(ring_theory/matrix): add minor, sub_[left|right|up|down], sub_[left|right]_[up][down] ([#389](https://github.com/leanprover-community/mathlib/pull/389))
Also add fin.nat_add.
#### Estimated changes
Modified data/fin.lean
- \+ *def* nat_add

Modified ring_theory/matrix.lean
- \+ *def* minor
- \+ *def* sub_left
- \+ *def* sub_right
- \+ *def* sub_up
- \+ *def* sub_down
- \+ *def* sub_up_right
- \+ *def* sub_down_right
- \+ *def* sub_up_left
- \+ *def* sub_down_left



## [2018-11-05 11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/c56bb3b)
feat(tactic/norm_num): permit `norm_num(1)` inside `conv`
#### Estimated changes
Modified docs/extras/conv.md


Modified docs/tactics.md


Modified tactic/norm_num.lean


Modified tests/tactics.lean




## [2018-11-05 11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/b092755)
doc(docs/conv): document additions
#### Estimated changes
Modified docs/extras/conv.md


Modified docs/tactics.md




## [2018-11-05 11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/fb57843)
feat(tactic/ring(2)): permit `ring` and `ring2` inside `conv`
#### Estimated changes
Modified tactic/converter/interactive.lean


Modified tactic/ring.lean


Modified tactic/ring2.lean


Modified tests/tactics.lean




## [2018-11-05 11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/d560431)
feat(tactic/basic): add `lock_tactic_state`
For state-preserving tactic invocations (extracting the result)
#### Estimated changes
Modified tactic/basic.lean




## [2018-11-05 11:45:33+01:00](https://github.com/leanprover-community/mathlib/commit/350e6e2)
feat(tactic/conv): add `erw`, `conv_lhs`, and `conv_rhs`
#### Estimated changes
Modified docs/extras/conv.md


Modified docs/tactics.md


Modified tactic/converter/interactive.lean


Modified tests/tactics.lean




## [2018-11-05 05:21:48-05:00](https://github.com/leanprover-community/mathlib/commit/aed8194)
feat(docs/extras) add doc about coercions between number types ([#443](https://github.com/leanprover-community/mathlib/pull/443))
#### Estimated changes
Created docs/extras/casts.md
- \+ *def* from_R_to_C



## [2018-11-05 05:20:29-05:00](https://github.com/leanprover-community/mathlib/commit/072a11e)
feat(data/polynomial): polynomial.comp ([#441](https://github.com/leanprover-community/mathlib/pull/441))
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* C_pow
- \+ *lemma* eval₂_sum
- \+/\- *lemma* eval_sum
- \+ *lemma* eval₂_comp
- \+ *lemma* eval_comp
- \+ *lemma* comp_X
- \+ *lemma* X_comp
- \+ *lemma* comp_C
- \+ *lemma* C_comp
- \+ *lemma* comp_zero
- \+ *lemma* zero_comp
- \+ *lemma* comp_one
- \+ *lemma* one_comp
- \+ *lemma* add_comp
- \+ *lemma* mul_comp
- \+/\- *lemma* degree_sum_le
- \+/\- *lemma* degree_pos_of_root
- \+ *def* comp



## [2018-11-05 05:19:00-05:00](https://github.com/leanprover-community/mathlib/commit/1cadd48)
feat(data/list): mfoldl, mfoldr theorems; reverse_foldl
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* reverse_foldl
- \+ *theorem* mfoldl_nil
- \+ *theorem* mfoldr_nil
- \+ *theorem* mfoldl_cons
- \+ *theorem* mfoldr_cons
- \+ *theorem* mfoldl_append
- \+ *theorem* mfoldr_append



## [2018-11-05 05:07:45-05:00](https://github.com/leanprover-community/mathlib/commit/b934956)
feat(data/int/basic): make coe_nat_le, coe_nat_lt, coe_nat_inj' into simp lemmas
#### Estimated changes
Modified data/int/basic.lean
- \+/\- *theorem* coe_nat_le
- \+/\- *theorem* coe_nat_lt
- \+/\- *theorem* coe_nat_inj'



## [2018-11-05 05:07:04-05:00](https://github.com/leanprover-community/mathlib/commit/f5ce71f)
fix(tactic/eval_expr): often crashes when reflecting expressions ([#358](https://github.com/leanprover-community/mathlib/pull/358))
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/replacer.lean




## [2018-11-05 05:03:22-05:00](https://github.com/leanprover-community/mathlib/commit/f00ed77)
feat(data/complex/basic): I_ne_zero and cast_re, cast_im lemmas
#### Estimated changes
Modified data/complex/basic.lean
- \+ *lemma* I_ne_zero
- \+ *lemma* nat_cast_re
- \+ *lemma* nat_cast_im
- \+ *lemma* int_cast_re
- \+ *lemma* int_cast_im
- \+ *lemma* rat_cast_re
- \+ *lemma* rat_cast_im



## [2018-11-03 20:19:22-04:00](https://github.com/leanprover-community/mathlib/commit/3f5ec68)
fix(*): make three `trans_apply`s rfl-lemmas
#### Estimated changes
Modified data/equiv/basic.lean
- \+/\- *theorem* trans_apply

Modified order/order_iso.lean
- \+/\- *theorem* trans_apply

Modified set_theory/ordinal.lean
- \+/\- *theorem* trans_apply

