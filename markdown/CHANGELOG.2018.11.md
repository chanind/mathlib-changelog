## [2018-11-29 22:13:08-05:00](https://github.com/leanprover-community/mathlib/commit/2a86b06)
fix(order/filter): tendsto_at_top only requires preorder not partial_order
#### Estimated changes
Modified order/filter.lean
- \+/\- *lemma* filter.tendsto_at_top



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


Added category_theory/equivalence.lean
- \+ *def* category_theory.category_theory.equivalence.equivalence_of_fully_faithfully_ess_surj
- \+ *def* category_theory.category_theory.equivalence.ess_surj_of_equivalence
- \+ *lemma* category_theory.equivalence.fun_inv_map
- \+ *lemma* category_theory.equivalence.inv_fun_map
- \+ *def* category_theory.equivalence.refl
- \+ *def* category_theory.equivalence.symm
- \+ *def* category_theory.equivalence.trans
- \+ *def* category_theory.functor.as_equivalence
- \+ *def* category_theory.functor.fun_inv_id
- \+ *def* category_theory.functor.fun_obj_preimage_iso
- \+ *def* category_theory.functor.inv
- \+ *def* category_theory.functor.inv_fun_id
- \+ *def* category_theory.functor.obj_preimage
- \+ *lemma* category_theory.is_equivalence.fun_inv_map
- \+ *lemma* category_theory.is_equivalence.inv_fun_map

Modified category_theory/natural_isomorphism.lean
- \+ *lemma* category_theory.nat_iso.hom_app_inv_app_id
- \+ *lemma* category_theory.nat_iso.hom_vcomp_inv
- \+ *lemma* category_theory.nat_iso.inv_app_hom_app_id
- \+ *lemma* category_theory.nat_iso.inv_vcomp_hom

Added tactic/slice.lean




## [2018-11-28 01:31:22-05:00](https://github.com/leanprover-community/mathlib/commit/131b46f)
feat(data/list): separate out list defs into `data.lists.defs`
#### Estimated changes
Modified data/list/basic.lean
- \- *theorem* list.chain_cons
- \- *def* list.choose
- \- *def* list.choose_x
- \- *def* list.concat
- \- *def* list.count
- \- *def* list.countp
- \- *def* list.disjoint
- \- *def* list.erase_dup
- \- *def* list.erasep
- \- *def* list.extractp
- \- *def* list.find
- \- *def* list.find_indexes
- \- *def* list.find_indexes_aux
- \- *def* list.head'
- \- *def* list.indexes_of
- \- *def* list.inits
- \- *def* list.insert_nth
- \- *def* list.inth
- \- *def* list.is_infix
- \- *def* list.is_prefix
- \- *def* list.is_suffix
- \- *def* list.last'
- \- *def* list.lookmap
- \- *def* list.map_head
- \- *def* list.map_last
- \- *def* list.modify_head
- \- *def* list.modify_nth
- \- *def* list.modify_nth_tail
- \- *def* list.nodup
- \- *def* list.of_fn
- \- *def* list.of_fn_aux
- \- *def* list.of_fn_nth_val
- \- *theorem* list.pairwise_cons
- \- *def* list.permutations
- \- *def* list.permutations_aux.rec
- \- *def* list.permutations_aux2
- \- *def* list.permutations_aux
- \- *def* list.prod
- \- *def* list.product
- \- *def* list.pw_filter
- \- *def* list.range'
- \- *def* list.reduce_option
- \- *def* list.revzip
- \- *def* list.scanl
- \- *def* list.scanr
- \- *def* list.scanr_aux
- \- *def* list.sections
- \- *def* list.split_at
- \- *def* list.sublists'
- \- *def* list.sublists'_aux
- \- *def* list.sublists
- \- *def* list.sublists_aux
- \- *def* list.sublists_aux₁
- \- *def* list.tails
- \- *def* list.take'
- \- *def* list.take_while
- \- *def* list.tfae
- \- *def* list.to_array
- \- *def* list.transpose
- \- *def* list.transpose_aux

Added data/list/defs.lean
- \+ *theorem* list.chain_cons
- \+ *def* list.choose
- \+ *def* list.choose_x
- \+ *def* list.concat
- \+ *def* list.count
- \+ *def* list.countp
- \+ *def* list.disjoint
- \+ *def* list.erase_dup
- \+ *def* list.erasep
- \+ *def* list.extractp
- \+ *def* list.find
- \+ *def* list.find_indexes
- \+ *def* list.find_indexes_aux
- \+ *def* list.head'
- \+ *def* list.indexes_of
- \+ *def* list.inits
- \+ *def* list.insert_nth
- \+ *def* list.inth
- \+ *def* list.is_infix
- \+ *def* list.is_prefix
- \+ *def* list.is_suffix
- \+ *def* list.last'
- \+ *def* list.lookmap
- \+ *def* list.map_head
- \+ *def* list.map_last
- \+ *def* list.modify_head
- \+ *def* list.modify_nth
- \+ *def* list.modify_nth_tail
- \+ *def* list.nodup
- \+ *def* list.of_fn
- \+ *def* list.of_fn_aux
- \+ *def* list.of_fn_nth_val
- \+ *theorem* list.pairwise_cons
- \+ *def* list.permutations
- \+ *def* list.permutations_aux.rec
- \+ *def* list.permutations_aux2
- \+ *def* list.permutations_aux
- \+ *def* list.prod
- \+ *def* list.product
- \+ *def* list.pw_filter
- \+ *def* list.range'
- \+ *def* list.reduce_option
- \+ *def* list.revzip
- \+ *def* list.scanl
- \+ *def* list.scanr
- \+ *def* list.scanr_aux
- \+ *def* list.sections
- \+ *def* list.split_at
- \+ *def* list.sublists'
- \+ *def* list.sublists'_aux
- \+ *def* list.sublists
- \+ *def* list.sublists_aux
- \+ *def* list.sublists_aux₁
- \+ *def* list.tails
- \+ *def* list.take'
- \+ *def* list.take_while
- \+ *def* list.tfae
- \+ *def* list.to_array
- \+ *def* list.transpose
- \+ *def* list.transpose_aux



## [2018-11-27 05:19:28-05:00](https://github.com/leanprover-community/mathlib/commit/98eacf8)
feat(tactic/basic,tactic/interactive): generalize use tactic ([#497](https://github.com/leanprover-community/mathlib/pull/497))
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/interactive.lean




## [2018-11-24 03:58:50-05:00](https://github.com/leanprover-community/mathlib/commit/452c9a2)
feat(data/polynomial): nat_degree_comp ([#477](https://github.com/leanprover-community/mathlib/pull/477))
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* add_monoid.smul_le_smul
- \+ *lemma* add_monoid.smul_le_smul_of_le_right
- \+ *lemma* with_bot.coe_smul

Modified algebra/ordered_group.lean
- \+ *lemma* with_bot.coe_zero
- \+/\- *lemma* with_top.coe_add

Modified data/polynomial.lean
- \+ *lemma* polynomial.coeff_comp_degree_mul_degree
- \+ *lemma* polynomial.leading_coeff_comp
- \+ *lemma* polynomial.nat_degree_comp
- \+ *lemma* polynomial.nat_degree_comp_le
- \+ *lemma* polynomial.nat_degree_one
- \+ *lemma* polynomial.nat_degree_pow_eq'
- \+ *lemma* polynomial.nat_degree_pow_eq



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


Added data/finmap.lean
- \+ *def* alist.to_finmap
- \+ *theorem* alist.to_finmap_entries
- \+ *theorem* alist.to_finmap_eq
- \+ *theorem* finmap.empty_to_finmap
- \+ *def* finmap.erase
- \+ *theorem* finmap.erase_to_finmap
- \+ *theorem* finmap.ext
- \+ *def* finmap.extract
- \+ *theorem* finmap.extract_eq_lookup_erase
- \+ *def* finmap.foldl
- \+ *theorem* finmap.induction_on
- \+ *def* finmap.insert
- \+ *theorem* finmap.insert_entries_of_neg
- \+ *theorem* finmap.insert_of_pos
- \+ *theorem* finmap.insert_to_finmap
- \+ *def* finmap.keys
- \+ *theorem* finmap.keys_empty
- \+ *theorem* finmap.keys_erase
- \+ *theorem* finmap.keys_erase_to_finset
- \+ *theorem* finmap.keys_ext
- \+ *theorem* finmap.keys_replace
- \+ *theorem* finmap.keys_singleton
- \+ *theorem* finmap.keys_val
- \+ *def* finmap.lift_on
- \+ *theorem* finmap.lift_on_to_finmap
- \+ *def* finmap.lookup
- \+ *theorem* finmap.lookup_is_some
- \+ *theorem* finmap.lookup_to_finmap
- \+ *theorem* finmap.mem_def
- \+ *theorem* finmap.mem_erase
- \+ *theorem* finmap.mem_insert
- \+ *theorem* finmap.mem_keys
- \+ *theorem* finmap.mem_replace
- \+ *theorem* finmap.mem_to_finmap
- \+ *theorem* finmap.not_mem_empty
- \+ *theorem* finmap.not_mem_empty_entries
- \+ *def* finmap.replace
- \+ *theorem* finmap.replace_to_finmap
- \+ *def* finmap.singleton
- \+ *theorem* multiset.coe_nodupkeys
- \+ *def* multiset.nodupkeys

Added data/list/alist.lean
- \+ *def* alist.erase
- \+ *theorem* alist.ext
- \+ *def* alist.extract
- \+ *theorem* alist.extract_eq_lookup_erase
- \+ *def* alist.foldl
- \+ *def* alist.insert
- \+ *theorem* alist.insert_entries_of_neg
- \+ *theorem* alist.insert_of_pos
- \+ *def* alist.keys
- \+ *theorem* alist.keys_empty
- \+ *theorem* alist.keys_erase
- \+ *theorem* alist.keys_insert
- \+ *theorem* alist.keys_nodup
- \+ *theorem* alist.keys_replace
- \+ *theorem* alist.keys_singleton
- \+ *def* alist.lookup
- \+ *theorem* alist.lookup_is_some
- \+ *theorem* alist.mem_def
- \+ *theorem* alist.mem_erase
- \+ *theorem* alist.mem_insert
- \+ *theorem* alist.mem_keys
- \+ *theorem* alist.mem_of_perm
- \+ *theorem* alist.mem_replace
- \+ *theorem* alist.not_mem_empty
- \+ *theorem* alist.not_mem_empty_entries
- \+ *theorem* alist.perm_erase
- \+ *theorem* alist.perm_insert
- \+ *theorem* alist.perm_lookup
- \+ *theorem* alist.perm_replace
- \+ *def* alist.replace
- \+ *def* alist.singleton

Modified data/list/basic.lean
- \+/\- *theorem* list.erase_append_left
- \+/\- *theorem* list.erase_append_right
- \+ *theorem* list.erase_eq_erasep
- \+/\- *theorem* list.erase_sublist_erase
- \+ *def* list.erasep
- \+ *theorem* list.erasep_append_left
- \+ *theorem* list.erasep_append_right
- \+ *theorem* list.erasep_cons
- \+ *theorem* list.erasep_cons_of_neg
- \+ *theorem* list.erasep_cons_of_pos
- \+ *theorem* list.erasep_map
- \+ *theorem* list.erasep_nil
- \+ *theorem* list.erasep_of_forall_not
- \+ *theorem* list.erasep_sublist
- \+ *theorem* list.erasep_sublist_erasep
- \+ *theorem* list.erasep_subset
- \+ *theorem* list.exists_of_erasep
- \+ *theorem* list.exists_or_eq_self_of_erasep
- \+ *def* list.extractp
- \+ *theorem* list.extractp_eq_find_erasep
- \+ *theorem* list.forall_of_forall_of_pairwise
- \+ *theorem* list.length_erasep_of_mem
- \+ *theorem* list.length_lookmap
- \+ *def* list.lookmap
- \+ *theorem* list.lookmap_congr
- \+ *theorem* list.lookmap_cons_none
- \+ *theorem* list.lookmap_cons_some
- \+ *theorem* list.lookmap_id'
- \+ *theorem* list.lookmap_map_eq
- \+ *theorem* list.lookmap_nil
- \+ *theorem* list.lookmap_none
- \+ *theorem* list.lookmap_of_forall_not
- \+ *theorem* list.lookmap_some
- \+/\- *theorem* list.map_erase
- \+ *theorem* list.mem_erasep_of_neg
- \+ *theorem* list.mem_of_mem_erasep
- \+ *theorem* list.nodup_repeat

Modified data/list/perm.lean
- \+ *theorem* list.perm.swap'
- \+ *theorem* list.perm_erasep
- \+ *theorem* list.perm_lookmap
- \+ *theorem* list.perm_option_to_list

Added data/list/sigma.lean
- \+ *theorem* list.head_lookup_all
- \+ *def* list.kerase
- \+ *theorem* list.kerase_map_fst
- \+ *theorem* list.kerase_nodupkeys
- \+ *theorem* list.kerase_sublist
- \+ *def* list.kextract
- \+ *theorem* list.kextract_eq_lookup_kerase
- \+ *def* list.kreplace
- \+ *theorem* list.kreplace_map_fst
- \+ *theorem* list.kreplace_nodupkeys
- \+ *theorem* list.kreplace_of_forall_not
- \+ *theorem* list.kreplace_self
- \+ *def* list.lookup
- \+ *def* list.lookup_all
- \+ *theorem* list.lookup_all_cons_eq
- \+ *theorem* list.lookup_all_cons_ne
- \+ *theorem* list.lookup_all_eq_lookup
- \+ *theorem* list.lookup_all_eq_nil
- \+ *theorem* list.lookup_all_length_le_one
- \+ *theorem* list.lookup_all_nil
- \+ *theorem* list.lookup_all_nodup
- \+ *theorem* list.lookup_all_sublist
- \+ *theorem* list.lookup_cons_eq
- \+ *theorem* list.lookup_cons_ne
- \+ *theorem* list.lookup_eq_none
- \+ *theorem* list.lookup_is_some
- \+ *theorem* list.lookup_nil
- \+ *theorem* list.map_lookup_eq_find
- \+ *theorem* list.mem_lookup_all
- \+ *theorem* list.mem_lookup_iff
- \+ *theorem* list.nodup_enum_map_fst
- \+ *theorem* list.nodup_of_nodupkeys
- \+ *theorem* list.nodupkeys.eq_of_fst_eq
- \+ *theorem* list.nodupkeys.eq_of_mk_mem
- \+ *def* list.nodupkeys
- \+ *theorem* list.nodupkeys_cons
- \+ *theorem* list.nodupkeys_iff_pairwise
- \+ *theorem* list.nodupkeys_join
- \+ *theorem* list.nodupkeys_nil
- \+ *theorem* list.nodupkeys_of_sublist
- \+ *theorem* list.nodupkeys_singleton
- \+ *theorem* list.of_mem_lookup
- \+ *theorem* list.perm_kerase
- \+ *theorem* list.perm_kreplace
- \+ *theorem* list.perm_lookup
- \+ *theorem* list.perm_lookup_all
- \+ *theorem* list.perm_nodupkeys

Modified data/option.lean
- \+/\- *theorem* option.ext

Modified logic/basic.lean
- \+ *lemma* congr_arg_heq



## [2018-11-24 03:56:32-05:00](https://github.com/leanprover-community/mathlib/commit/e19cd0f)
fix(*): adding a few @[simp] attributes ([#492](https://github.com/leanprover-community/mathlib/pull/492))
* some additional simp lemmas
* nat.add_sub_cancel
#### Estimated changes
Modified data/multiset.lean
- \+/\- *theorem* multiset.add_sub_cancel
- \+/\- *theorem* multiset.add_sub_cancel_left

Modified data/nat/basic.lean


Modified data/rat.lean
- \+/\- *theorem* rat.cast_pow

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
- \+/\- *lemma* category_theory.concrete_category_comp
- \+/\- *lemma* category_theory.concrete_category_id

Added category_theory/comma.lean
- \+ *def* category_theory.comma.fst
- \+ *lemma* category_theory.comma.fst_map
- \+ *lemma* category_theory.comma.fst_obj
- \+ *def* category_theory.comma.map_left
- \+ *def* category_theory.comma.map_right
- \+ *def* category_theory.comma.nat_trans
- \+ *def* category_theory.comma.snd
- \+ *lemma* category_theory.comma.snd_map
- \+ *lemma* category_theory.comma.snd_obj
- \+ *lemma* category_theory.comma_morphism.ext

Modified category_theory/examples/monoids.lean
- \+/\- *def* category_theory.examples.CommMon.forget_to_Mon

Modified category_theory/examples/rings.lean


Modified category_theory/examples/topological_spaces.lean


Modified category_theory/full_subcategory.lean
- \- *def* category_theory.full_subcategory_embedding
- \+ *def* category_theory.full_subcategory_inclusion

Renamed category_theory/embedding.lean to category_theory/fully_faithful.lean
- \+/\- *lemma* category_theory.functor.image_preimage
- \+/\- *def* category_theory.functor.preimage
- \+/\- *lemma* category_theory.preimage_iso_hom
- \+/\- *lemma* category_theory.preimage_iso_inv

Modified category_theory/functor.lean
- \+/\- *def* category_theory.bundled.map

Modified category_theory/functor_category.lean
- \+ *lemma* category_theory.functor.flip_obj_map

Modified category_theory/isomorphism.lean
- \+ *def* category_theory.eq_to_hom
- \+ *lemma* category_theory.eq_to_hom_refl
- \+ *lemma* category_theory.eq_to_hom_trans
- \+ *lemma* category_theory.eq_to_iso.hom
- \+/\- *def* category_theory.eq_to_iso
- \+/\- *lemma* category_theory.eq_to_iso_refl
- \+/\- *lemma* category_theory.eq_to_iso_trans
- \+/\- *lemma* category_theory.functor.eq_to_iso

Modified category_theory/opposites.lean
- \+/\- *lemma* category_theory.functor.hom_pairing_map
- \+ *lemma* category_theory.functor.op_hom.map_app
- \+ *lemma* category_theory.functor.op_hom.obj
- \+ *lemma* category_theory.functor.op_inv.map_app
- \+ *lemma* category_theory.functor.op_inv.obj
- \+ *lemma* category_theory.functor.op_map
- \+ *lemma* category_theory.functor.op_obj
- \- *lemma* category_theory.functor.opposite_map
- \- *lemma* category_theory.functor.opposite_obj
- \+ *lemma* category_theory.functor.unop_map
- \+ *lemma* category_theory.functor.unop_obj
- \+ *def* category_theory.op_op

Added category_theory/pempty.lean
- \+ *def* category_theory.functor.empty

Modified category_theory/products.lean
- \+/\- *def* category_theory.evaluation
- \+ *def* category_theory.evaluation_uncurried
- \+/\- *lemma* category_theory.prod_comp
- \+ *lemma* category_theory.prod_comp_fst
- \+ *lemma* category_theory.prod_comp_snd
- \+ *lemma* category_theory.prod_id_fst
- \+ *lemma* category_theory.prod_id_snd

Added category_theory/punit.lean
- \+ *def* category_theory.functor.of_obj
- \+ *lemma* category_theory.functor.of_obj_obj

Modified category_theory/types.lean


Modified category_theory/yoneda.lean
- \+/\- *lemma* category_theory.yoneda.map_app
- \+/\- *lemma* category_theory.yoneda.naturality
- \+/\- *lemma* category_theory.yoneda.obj_map
- \+/\- *lemma* category_theory.yoneda.obj_map_id
- \+/\- *lemma* category_theory.yoneda.obj_obj
- \+/\- *def* category_theory.yoneda_evaluation
- \+/\- *def* category_theory.yoneda_lemma
- \+/\- *def* category_theory.yoneda_pairing

Modified docs/theories/category_theory.md




## [2018-11-22 23:51:18-05:00](https://github.com/leanprover-community/mathlib/commit/de8985c)
fix(finsupp): remove superfluous typeclass argument ([#490](https://github.com/leanprover-community/mathlib/pull/490))
#### Estimated changes
Modified data/finsupp.lean
- \+/\- *lemma* finsupp.filter_pos_add_filter_neg



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
- \+/\- *theorem* option.is_none_iff_eq_none
- \+ *theorem* option.not_is_some

Modified data/set/disjointed.lean


Modified data/set/lattice.lean


Modified docs/tactics.md


Modified logic/basic.lean
- \+ *lemma* imp_imp_imp

Modified meta/rb_map.lean


Modified order/bounded_lattice.lean
- \+/\- *theorem* with_bot.some_lt_some

Modified tactic/basic.lean


Modified tactic/default.lean


Modified tactic/interactive.lean


Added tactic/monotonicity/basic.lean
- \+ *def* tactic.interactive.last_two
- \+ *def* tactic.interactive.mono_key

Added tactic/monotonicity/default.lean


Added tactic/monotonicity/interactive.lean
- \+ *lemma* tactic.interactive.apply_rel
- \+ *def* tactic.interactive.list.minimum_on

Added tactic/monotonicity/lemmas.lean
- \+ *lemma* gt_of_mul_lt_mul_neg_right
- \+ *lemma* mul_mono_nonneg
- \+ *lemma* mul_mono_nonpos
- \+ *lemma* nat.sub_mono_left_strict
- \+ *lemma* nat.sub_mono_right_strict

Modified tactic/norm_num.lean


Added tests/monotonicity.lean
- \+ *def* P
- \+ *lemma* P_mono
- \+ *def* Q
- \+ *lemma* Q_mono
- \+ *lemma* bar_bar''
- \+ *lemma* bar_bar'
- \+ *lemma* bar_bar
- \+ *def* list.le'
- \+ *lemma* list.le_refl
- \+ *lemma* list.le_trans
- \+ *lemma* list_le_mono_left
- \+ *lemma* list_le_mono_right

Added tests/monotonicity/test_cases.lean




## [2018-11-17 21:37:06-05:00](https://github.com/leanprover-community/mathlib/commit/8c385bc)
feat(category_theory): associator and unitors for functors ([#478](https://github.com/leanprover-community/mathlib/pull/478))
also check pentagon and triangle
#### Estimated changes
Modified category_theory/whiskering.lean
- \+ *def* category_theory.functor.associator
- \+ *def* category_theory.functor.left_unitor
- \+ *lemma* category_theory.functor.pentagon
- \+ *def* category_theory.functor.right_unitor
- \+ *lemma* category_theory.functor.triangle



## [2018-11-16 19:49:32-05:00](https://github.com/leanprover-community/mathlib/commit/1c60f5b)
fix(ring_theory/subring): unnecessary classical ([#482](https://github.com/leanprover-community/mathlib/pull/482))
#### Estimated changes
Modified ring_theory/subring.lean




## [2018-11-15 23:08:53+01:00](https://github.com/leanprover-community/mathlib/commit/47b3477)
feat(category_theory/whiskering): more whiskering lemmas
#### Estimated changes
Modified category_theory/whiskering.lean
- \+ *lemma* category_theory.whisker_left_id
- \+ *lemma* category_theory.whisker_right_id



## [2018-11-15 23:02:43+01:00](https://github.com/leanprover-community/mathlib/commit/c834715)
style(category_theory/natural_transformation): fix hcomp/vcomp notation ([#470](https://github.com/leanprover-community/mathlib/pull/470))
#### Estimated changes
Modified category_theory/natural_transformation.lean
- \+/\- *lemma* category_theory.nat_trans.vcomp_assoc

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
- \+/\- *lemma* lattice.Inf_range
- \+/\- *lemma* lattice.Sup_range
- \+/\- *def* lattice.infi
- \+/\- *def* lattice.supr

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
- \+/\- *def* lattice.infi
- \+/\- *theorem* lattice.infi_congr_Prop
- \+/\- *def* lattice.supr
- \+/\- *theorem* lattice.supr_congr_Prop



## [2018-11-10 18:16:37+01:00](https://github.com/leanprover-community/mathlib/commit/4a013fb)
feat(analysis): sequential completeness
#### Estimated changes
Modified analysis/metric_space.lean
- \+ *theorem* cauchy_seq_metric'
- \+ *theorem* cauchy_seq_metric
- \+ *theorem* continuous_topo_metric
- \+/\- *theorem* exists_delta_of_continuous
- \+ *theorem* tendsto_at_top_metric
- \+ *theorem* tendsto_nhds_topo_metric

Modified analysis/topology/uniform_space.lean
- \+ *def* cauchy_seq
- \+ *theorem* cauchy_seq_tendsto_of_complete

Modified data/real/cau_seq_filter.lean
- \- *lemma* cau_filter_lim_spec
- \+ *lemma* cau_seq_iff_cauchy_seq
- \- *lemma* cau_seq_of_cau_filter_mem_set_seq
- \+/\- *lemma* cauchy_of_filter_cauchy
- \+ *theorem* complete_of_cauchy_seq_tendsto
- \+/\- *lemma* filter_cauchy_of_cauchy
- \- *lemma* is_cau_seq_of_dist_tendsto_0
- \- *lemma* le_nhds_cau_filter_lim
- \- *lemma* mono_of_mono_succ
- \- *lemma* seq_of_cau_filter_is_cauchy'
- \- *lemma* seq_of_cau_filter_is_cauchy
- \- *lemma* seq_of_cau_filter_mem_set_seq
- \+ *lemma* sequentially_complete.cauchy_seq_of_dist_tendsto_0
- \+ *lemma* sequentially_complete.le_nhds_cau_filter_lim
- \+ *lemma* sequentially_complete.mono_of_mono_succ
- \+ *lemma* sequentially_complete.seq_of_cau_filter_is_cauchy'
- \+ *lemma* sequentially_complete.seq_of_cau_filter_is_cauchy
- \+ *lemma* sequentially_complete.seq_of_cau_filter_mem_set_seq
- \+ *def* sequentially_complete.set_seq_of_cau_filter
- \+ *lemma* sequentially_complete.set_seq_of_cau_filter_inhabited
- \+ *lemma* sequentially_complete.set_seq_of_cau_filter_mem_sets
- \+ *lemma* sequentially_complete.set_seq_of_cau_filter_monotone'
- \+ *lemma* sequentially_complete.set_seq_of_cau_filter_monotone
- \+ *lemma* sequentially_complete.set_seq_of_cau_filter_spec
- \+ *lemma* sequentially_complete.tendsto_div
- \- *def* set_seq_of_cau_filter
- \- *lemma* set_seq_of_cau_filter_inhabited
- \- *lemma* set_seq_of_cau_filter_mem_sets
- \- *lemma* set_seq_of_cau_filter_monotone'
- \- *lemma* set_seq_of_cau_filter_monotone
- \- *lemma* set_seq_of_cau_filter_spec
- \- *lemma* tendsto_div
- \+/\- *lemma* tendsto_limit



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
- \+/\- *theorem* zorn.zorn_partial_order₀

Modified ring_theory/ideal_operations.lean


Modified ring_theory/ideals.lean




## [2018-11-09 10:43:01+01:00](https://github.com/leanprover-community/mathlib/commit/4fc67f8)
feat(data/fintype): add choose_unique and construct inverses to bijections ([#421](https://github.com/leanprover-community/mathlib/pull/421))
#### Estimated changes
Modified data/finset.lean
- \+ *def* finset.choose
- \+ *lemma* finset.choose_mem
- \+ *lemma* finset.choose_property
- \+ *lemma* finset.choose_spec
- \+ *def* finset.choose_x

Modified data/fintype.lean
- \+ *def* fintype.bij_inv
- \+ *lemma* fintype.bijective_bij_inv
- \+ *def* fintype.choose
- \+ *lemma* fintype.choose_spec
- \+ *def* fintype.choose_x
- \+ *lemma* fintype.left_inverse_bij_inv
- \+ *lemma* fintype.right_inverse_bij_inv

Modified data/list/basic.lean
- \+ *def* list.choose
- \+ *lemma* list.choose_mem
- \+ *lemma* list.choose_property
- \+ *lemma* list.choose_spec
- \+ *def* list.choose_x

Modified data/multiset.lean
- \+ *def* multiset.choose
- \+ *lemma* multiset.choose_mem
- \+ *lemma* multiset.choose_property
- \+ *lemma* multiset.choose_spec
- \+ *def* multiset.choose_x



## [2018-11-09 10:22:08+01:00](https://github.com/leanprover-community/mathlib/commit/9f5099e)
refactor(analysis): add uniform_embedding_comap
#### Estimated changes
Modified analysis/emetric_space.lean
- \- *theorem* emetric_space.induced_uniform_embedding

Modified analysis/metric_space.lean
- \- *theorem* metric_space.induced_uniform_embedding

Modified analysis/real.lean


Modified analysis/topology/uniform_space.lean
- \+ *lemma* uniform_embedding_comap



## [2018-11-09 10:22:08+01:00](https://github.com/leanprover-community/mathlib/commit/6273837)
feat(analysis): add emetric spaces
#### Estimated changes
Modified algebra/ordered_ring.lean
- \+ *lemma* with_top.coe_nat
- \+ *lemma* with_top.nat_ne_top
- \+ *lemma* with_top.top_ne_nat

Added analysis/emetric_space.lean
- \+ *lemma* emetric_space.cauchy_of_emetric
- \+ *theorem* emetric_space.edist_eq_zero
- \+ *theorem* emetric_space.edist_mem_uniformity
- \+ *theorem* emetric_space.edist_triangle_left
- \+ *theorem* emetric_space.edist_triangle_right
- \+ *theorem* emetric_space.eq_of_forall_edist_le
- \+ *def* emetric_space.induced
- \+ *theorem* emetric_space.induced_uniform_embedding
- \+ *theorem* emetric_space.mem_uniformity_edist
- \+ *def* emetric_space.replace_uniformity
- \+ *theorem* emetric_space.subtype.edist_eq
- \+ *theorem* emetric_space.uniform_continuous_of_emetric
- \+ *theorem* emetric_space.uniform_embedding_of_emetric
- \+ *def* emetric_space.uniform_space_of_edist
- \+ *theorem* emetric_space.uniformity_edist''
- \+ *theorem* emetric_space.uniformity_edist'
- \+ *theorem* emetric_space.zero_eq_edist
- \+ *theorem* uniformity_dist_of_mem_uniformity

Modified analysis/ennreal.lean


Modified analysis/metric_space.lean
- \- *lemma* coe_dist
- \+ *lemma* dist_eq_edist
- \+ *lemma* dist_eq_nndist
- \+ *theorem* edist_dist
- \+ *lemma* edist_eq_dist
- \+ *lemma* edist_eq_nndist
- \+ *lemma* edist_ne_top
- \+ *lemma* mem_uniformity_dist_edist
- \+ *lemma* nndist_eq_dist
- \+ *lemma* nndist_eq_edist
- \- *theorem* uniformity_dist_of_mem_uniformity
- \+ *theorem* uniformity_edist'
- \+ *theorem* uniformity_edist

Modified data/complex/exponential.lean


Modified data/finset.lean
- \+ *lemma* finset.comp_inf_eq_inf_comp
- \+ *lemma* finset.comp_sup_eq_sup_comp
- \+ *lemma* finset.lt_inf
- \+ *lemma* finset.sup_lt

Modified data/nat/cast.lean
- \+/\- *theorem* nat.cast_pos

Modified data/real/basic.lean


Modified data/real/cau_seq_filter.lean


Modified data/real/ennreal.lean
- \+ *lemma* ennreal.add_halves
- \+ *lemma* ennreal.add_lt_add
- \+ *lemma* ennreal.coe_div
- \+/\- *lemma* ennreal.coe_nat
- \+ *lemma* ennreal.div_add_div_same
- \+ *lemma* ennreal.div_pos_iff
- \+ *lemma* ennreal.div_self
- \+ *lemma* ennreal.nat_ne_top
- \+ *lemma* ennreal.to_nnreal_eq_zero_iff
- \+ *lemma* ennreal.top_ne_nat
- \+ *lemma* ennreal.zero_to_nnreal

Modified data/real/nnreal.lean
- \+ *lemma* nnreal.add_halves
- \+ *lemma* nnreal.div_add_div_same
- \+ *lemma* nnreal.of_real_eq_zero

Modified order/bounded_lattice.lean
- \+ *lemma* lattice.bot_lt_iff_ne_bot
- \+ *lemma* lattice.lt_top_iff_ne_top



## [2018-11-09 09:39:52+01:00](https://github.com/leanprover-community/mathlib/commit/ff8bd5b)
fix(data/multiset): remove unused argument from `range_zero` ([#466](https://github.com/leanprover-community/mathlib/pull/466))
#### Estimated changes
Modified data/multiset.lean
- \+/\- *theorem* multiset.range_zero



## [2018-11-08 10:16:03+01:00](https://github.com/leanprover-community/mathlib/commit/b0564b2)
feat(category_theory): propose removing coercions from category_theory/ ([#463](https://github.com/leanprover-community/mathlib/pull/463))
#### Estimated changes
Modified category_theory/embedding.lean
- \+/\- *lemma* category_theory.functor.image_preimage
- \+/\- *def* category_theory.functor.preimage
- \+/\- *def* category_theory.preimage_iso
- \- *lemma* category_theory.preimage_iso_coe
- \+ *lemma* category_theory.preimage_iso_hom
- \+ *lemma* category_theory.preimage_iso_inv
- \- *lemma* category_theory.preimage_iso_symm_coe

Modified category_theory/examples/topological_spaces.lean
- \+/\- *lemma* category_theory.examples.map_id_obj

Modified category_theory/full_subcategory.lean
- \+/\- *def* category_theory.full_subcategory_embedding

Modified category_theory/functor.lean
- \+/\- *lemma* category_theory.functor.comp_obj
- \+/\- *lemma* category_theory.functor.id_obj
- \- *def* category_theory.functor.map
- \- *lemma* category_theory.functor.map_comp
- \- *lemma* category_theory.functor.map_id
- \- *lemma* category_theory.functor.mk_map
- \- *lemma* category_theory.functor.mk_obj
- \- *lemma* category_theory.functor.obj_eq_coe

Modified category_theory/functor_category.lean
- \+/\- *lemma* category_theory.functor.category.comp_app
- \+/\- *lemma* category_theory.functor.category.id_app
- \+/\- *lemma* category_theory.functor.category.nat_trans.app_naturality
- \+/\- *lemma* category_theory.functor.category.nat_trans.naturality_app

Modified category_theory/isomorphism.lean
- \+/\- *def* category_theory.functor.on_iso
- \+/\- *lemma* category_theory.functor.on_iso_hom
- \+/\- *lemma* category_theory.functor.on_iso_inv
- \- *lemma* category_theory.iso.hom_eq_coe
- \- *lemma* category_theory.iso.hom_inv_id
- \- *lemma* category_theory.iso.inv_eq_coe
- \- *lemma* category_theory.iso.inv_hom_id
- \- *lemma* category_theory.iso.refl_coe
- \+ *lemma* category_theory.iso.refl_hom
- \+ *lemma* category_theory.iso.refl_inv
- \+/\- *lemma* category_theory.iso.refl_symm
- \- *lemma* category_theory.iso.refl_symm_coe
- \+ *lemma* category_theory.iso.symm_hom
- \+ *lemma* category_theory.iso.symm_inv
- \- *lemma* category_theory.iso.trans_coe
- \+ *lemma* category_theory.iso.trans_hom
- \+ *lemma* category_theory.iso.trans_inv
- \+/\- *lemma* category_theory.iso.trans_symm
- \- *lemma* category_theory.iso.trans_symm_coe

Modified category_theory/natural_isomorphism.lean
- \+/\- *def* category_theory.functor.assoc
- \+/\- *def* category_theory.functor.comp_id
- \+/\- *def* category_theory.functor.id_comp
- \+/\- *def* category_theory.nat_iso.app
- \+ *lemma* category_theory.nat_iso.app_hom
- \+ *lemma* category_theory.nat_iso.app_inv
- \+/\- *lemma* category_theory.nat_iso.comp_app
- \- *lemma* category_theory.nat_iso.hom_eq_coe
- \- *lemma* category_theory.nat_iso.inv_eq_symm_coe
- \- *lemma* category_theory.nat_iso.mk_app'
- \- *lemma* category_theory.nat_iso.mk_app
- \+/\- *lemma* category_theory.nat_iso.naturality_1
- \+/\- *lemma* category_theory.nat_iso.naturality_2
- \+/\- *def* category_theory.nat_iso.of_components.app
- \+/\- *def* category_theory.nat_iso.of_components.hom_app
- \+/\- *def* category_theory.nat_iso.of_components.inv_app
- \+/\- *def* category_theory.nat_iso.of_components

Modified category_theory/natural_transformation.lean
- \- *lemma* category_theory.nat_trans.app_eq_coe
- \+/\- *lemma* category_theory.nat_trans.exchange
- \+/\- *lemma* category_theory.nat_trans.ext
- \+/\- *lemma* category_theory.nat_trans.hcomp_app
- \+/\- *lemma* category_theory.nat_trans.id_app
- \- *lemma* category_theory.nat_trans.mk_app
- \- *lemma* category_theory.nat_trans.naturality
- \+/\- *lemma* category_theory.nat_trans.vcomp_app

Modified category_theory/opposites.lean
- \+/\- *lemma* category_theory.functor.hom_obj
- \+/\- *lemma* category_theory.functor.opposite_obj

Modified category_theory/products.lean
- \+/\- *def* category_theory.evaluation
- \+/\- *lemma* category_theory.functor.prod_map
- \+/\- *lemma* category_theory.functor.prod_obj
- \+/\- *lemma* category_theory.nat_trans.prod_app

Modified category_theory/types.lean
- \+/\- *def* category_theory.forget
- \+/\- *lemma* category_theory.functor_to_types.hcomp
- \+/\- *lemma* category_theory.functor_to_types.map_comp
- \+/\- *lemma* category_theory.functor_to_types.map_id
- \+/\- *lemma* category_theory.functor_to_types.naturality
- \+/\- *lemma* category_theory.functor_to_types.vcomp
- \- *lemma* category_theory.types.iso_mk_coe

Modified category_theory/whiskering.lean
- \+/\- *lemma* category_theory.whisker_left.app
- \+/\- *lemma* category_theory.whisker_left_vcomp
- \+/\- *def* category_theory.whisker_right
- \+/\- *lemma* category_theory.whisker_right_vcomp
- \+/\- *def* category_theory.whiskering_left

Modified category_theory/yoneda.lean
- \+/\- *lemma* category_theory.yoneda.map_app
- \+/\- *lemma* category_theory.yoneda.naturality
- \+/\- *lemma* category_theory.yoneda.obj_map
- \+/\- *lemma* category_theory.yoneda.obj_map_id
- \+/\- *lemma* category_theory.yoneda.obj_obj
- \+/\- *def* category_theory.yoneda
- \+/\- *def* category_theory.yoneda_evaluation
- \+/\- *def* category_theory.yoneda_lemma
- \+/\- *def* category_theory.yoneda_pairing

Modified docs/theories/category_theory.md




## [2018-11-08 09:29:40+01:00](https://github.com/leanprover-community/mathlib/commit/2f38ed7)
feat(ring_theory/ideal_operations): define ideal operations (multiplication and radical) ([#462](https://github.com/leanprover-community/mathlib/pull/462))
#### Estimated changes
Modified group_theory/free_abelian_group.lean


Modified linear_algebra/basic.lean
- \+ *theorem* submodule.mem_Sup_of_directed
- \+ *theorem* submodule.mem_map_of_mem

Modified linear_algebra/tensor_product.lean


Modified order/order_iso.lean


Modified order/zorn.lean
- \+ *theorem* zorn.zorn_partial_order₀

Added ring_theory/ideal_operations.lean
- \+ *lemma* ideal.add_eq_sup
- \+ *theorem* ideal.bot_mul
- \+ *def* ideal.comap
- \+ *theorem* ideal.comap_inf
- \+ *theorem* ideal.comap_mono
- \+ *theorem* ideal.comap_ne_top
- \+ *theorem* ideal.comap_radical
- \+ *theorem* ideal.comap_top
- \+ *theorem* ideal.is_prime.radical
- \+ *theorem* ideal.is_prime.radical_le_iff
- \+ *theorem* ideal.le_comap_mul
- \+ *theorem* ideal.le_comap_sup
- \+ *theorem* ideal.le_radical
- \+ *def* ideal.map
- \+ *theorem* ideal.map_bot
- \+ *theorem* ideal.map_inf_le
- \+ *theorem* ideal.map_le_iff_le_comap
- \+ *theorem* ideal.map_mono
- \+ *theorem* ideal.map_mul
- \+ *theorem* ideal.map_radical_le
- \+ *theorem* ideal.map_sup
- \+ *theorem* ideal.map_top
- \+ *theorem* ideal.mem_comap
- \+ *theorem* ideal.mem_map_of_mem
- \+ *theorem* ideal.mul_bot
- \+ *theorem* ideal.mul_eq_inf_of_coprime
- \+ *theorem* ideal.mul_le
- \+ *theorem* ideal.mul_le_inf
- \+ *theorem* ideal.mul_mem_mul
- \+ *theorem* ideal.mul_mem_mul_rev
- \+ *theorem* ideal.mul_mono
- \+ *theorem* ideal.mul_mono_left
- \+ *theorem* ideal.mul_mono_right
- \+ *theorem* ideal.mul_sup
- \+ *theorem* ideal.mul_top
- \+ *lemma* ideal.one_eq_top
- \+ *def* ideal.radical
- \+ *theorem* ideal.radical_eq_Inf
- \+ *theorem* ideal.radical_eq_top
- \+ *theorem* ideal.radical_idem
- \+ *theorem* ideal.radical_inf
- \+ *theorem* ideal.radical_mono
- \+ *theorem* ideal.radical_mul
- \+ *theorem* ideal.radical_pow
- \+ *theorem* ideal.radical_sup
- \+ *theorem* ideal.radical_top
- \+ *theorem* ideal.span_mul_span
- \+ *theorem* ideal.sup_mul
- \+ *theorem* ideal.top_mul
- \+ *lemma* ideal.zero_eq_bot
- \+ *lemma* submodule.add_eq_sup
- \+ *def* submodule.annihilator
- \+ *theorem* submodule.annihilator_bot
- \+ *theorem* submodule.annihilator_eq_top_iff
- \+ *theorem* submodule.annihilator_mono
- \+ *theorem* submodule.annihilator_supr
- \+ *theorem* submodule.bot_smul
- \+ *def* submodule.colon
- \+ *theorem* submodule.colon_mono
- \+ *theorem* submodule.infi_colon_supr
- \+ *theorem* submodule.mem_annihilator'
- \+ *theorem* submodule.mem_annihilator
- \+ *theorem* submodule.mem_colon'
- \+ *theorem* submodule.mem_colon
- \+ *theorem* submodule.smul_assoc
- \+ *theorem* submodule.smul_bot
- \+ *theorem* submodule.smul_induction_on
- \+ *theorem* submodule.smul_le
- \+ *theorem* submodule.smul_le_right
- \+ *theorem* submodule.smul_mem_smul
- \+ *theorem* submodule.smul_mono
- \+ *theorem* submodule.smul_mono_left
- \+ *theorem* submodule.smul_mono_right
- \+ *theorem* submodule.smul_sup
- \+ *theorem* submodule.span_smul_span
- \+ *theorem* submodule.sup_smul
- \+ *theorem* submodule.top_smul
- \+ *lemma* submodule.zero_eq_bot

Modified ring_theory/ideals.lean
- \- *def* ideal.comap
- \- *theorem* ideal.comap_ne_top
- \+ *theorem* ideal.is_prime.mem_of_pow_mem
- \- *theorem* ideal.mem_comap



## [2018-11-08 09:28:27+01:00](https://github.com/leanprover-community/mathlib/commit/41e8eb3)
feat(ring_theory/localization): quotient ring of integral domain is discrete field
#### Estimated changes
Modified ring_theory/localization.lean
- \+/\- *def* localization.quotient_ring.field.of_integral_domain



## [2018-11-06 12:40:58+01:00](https://github.com/leanprover-community/mathlib/commit/89431cf)
feat(linear_algebra): direct sum
#### Estimated changes
Added data/dfinsupp.lean
- \+ *def* decidable_zero_symm
- \+ *lemma* dfinsupp.add_apply
- \+ *theorem* dfinsupp.eq_mk_support
- \+ *def* dfinsupp.erase
- \+ *lemma* dfinsupp.erase_add_single
- \+ *lemma* dfinsupp.erase_apply
- \+ *lemma* dfinsupp.erase_def
- \+ *lemma* dfinsupp.erase_ne
- \+ *lemma* dfinsupp.erase_same
- \+ *lemma* dfinsupp.ext
- \+ *def* dfinsupp.filter
- \+ *lemma* dfinsupp.filter_apply
- \+ *lemma* dfinsupp.filter_apply_neg
- \+ *lemma* dfinsupp.filter_apply_pos
- \+ *lemma* dfinsupp.filter_def
- \+ *lemma* dfinsupp.filter_pos_add_filter_neg
- \+ *lemma* dfinsupp.finite_supp
- \+ *lemma* dfinsupp.induction₂
- \+ *def* dfinsupp.lmk
- \+ *lemma* dfinsupp.lmk_apply
- \+ *def* dfinsupp.lsingle
- \+ *lemma* dfinsupp.lsingle_apply
- \+ *def* dfinsupp.map_range
- \+ *lemma* dfinsupp.map_range_apply
- \+ *lemma* dfinsupp.map_range_def
- \+ *lemma* dfinsupp.map_range_single
- \+ *lemma* dfinsupp.mem_support_iff
- \+ *theorem* dfinsupp.mem_support_to_fun
- \+ *def* dfinsupp.mk
- \+ *lemma* dfinsupp.mk_add
- \+ *lemma* dfinsupp.mk_apply
- \+ *theorem* dfinsupp.mk_inj
- \+ *lemma* dfinsupp.mk_neg
- \+ *lemma* dfinsupp.mk_smul
- \+ *lemma* dfinsupp.mk_sub
- \+ *lemma* dfinsupp.mk_zero
- \+ *lemma* dfinsupp.neg_apply
- \+ *def* dfinsupp.prod
- \+ *lemma* dfinsupp.prod_add_index
- \+ *lemma* dfinsupp.prod_finset_sum_index
- \+ *lemma* dfinsupp.prod_map_range_index
- \+ *lemma* dfinsupp.prod_neg_index
- \+ *lemma* dfinsupp.prod_single_index
- \+ *lemma* dfinsupp.prod_subtype_domain_index
- \+ *lemma* dfinsupp.prod_sum_index
- \+ *lemma* dfinsupp.prod_zero_index
- \+ *def* dfinsupp.single
- \+ *lemma* dfinsupp.single_add
- \+ *lemma* dfinsupp.single_add_erase
- \+ *lemma* dfinsupp.single_apply
- \+ *lemma* dfinsupp.single_eq_of_ne
- \+ *lemma* dfinsupp.single_eq_same
- \+ *lemma* dfinsupp.single_smul
- \+ *lemma* dfinsupp.single_zero
- \+ *lemma* dfinsupp.smul_apply
- \+ *lemma* dfinsupp.sub_apply
- \+ *def* dfinsupp.subtype_domain
- \+ *lemma* dfinsupp.subtype_domain_add
- \+ *lemma* dfinsupp.subtype_domain_apply
- \+ *lemma* dfinsupp.subtype_domain_def
- \+ *lemma* dfinsupp.subtype_domain_finsupp_sum
- \+ *lemma* dfinsupp.subtype_domain_neg
- \+ *lemma* dfinsupp.subtype_domain_sub
- \+ *lemma* dfinsupp.subtype_domain_sum
- \+ *lemma* dfinsupp.subtype_domain_zero
- \+ *def* dfinsupp.sum
- \+ *lemma* dfinsupp.sum_add
- \+ *lemma* dfinsupp.sum_apply
- \+ *lemma* dfinsupp.sum_neg
- \+ *lemma* dfinsupp.sum_single
- \+ *lemma* dfinsupp.sum_sub_index
- \+ *lemma* dfinsupp.sum_zero
- \+ *def* dfinsupp.support
- \+ *lemma* dfinsupp.support_add
- \+ *lemma* dfinsupp.support_eq_empty
- \+ *lemma* dfinsupp.support_erase
- \+ *lemma* dfinsupp.support_filter
- \+ *lemma* dfinsupp.support_map_range
- \+ *theorem* dfinsupp.support_mk_subset
- \+ *lemma* dfinsupp.support_neg
- \+ *lemma* dfinsupp.support_single_ne_zero
- \+ *lemma* dfinsupp.support_single_subset
- \+ *lemma* dfinsupp.support_subset_iff
- \+ *lemma* dfinsupp.support_subtype_domain
- \+ *lemma* dfinsupp.support_sum
- \+ *lemma* dfinsupp.support_zero
- \+ *lemma* dfinsupp.support_zip_with
- \+ *def* dfinsupp.to_has_scalar
- \+ *def* dfinsupp.to_module
- \+ *lemma* dfinsupp.zero_apply
- \+ *def* dfinsupp.zip_with
- \+ *lemma* dfinsupp.zip_with_apply
- \+ *lemma* dfinsupp.zip_with_def
- \+ *def* dfinsupp

Modified data/finset.lean
- \+ *lemma* multiset.to_finset_add
- \+ *lemma* multiset.to_finset_zero

Added linear_algebra/direct_sum_module.lean
- \+ *def* direct_sum.mk
- \+ *theorem* direct_sum.mk_inj
- \+ *def* direct_sum.of
- \+ *theorem* direct_sum.of_inj
- \+ *def* direct_sum.set_to_set
- \+ *theorem* direct_sum.to_module.ext
- \+ *lemma* direct_sum.to_module.of
- \+ *theorem* direct_sum.to_module.unique
- \+ *def* direct_sum.to_module
- \+ *lemma* direct_sum.to_module_apply
- \+ *theorem* direct_sum.to_module_aux.add
- \+ *theorem* direct_sum.to_module_aux.smul
- \+ *def* direct_sum.to_module_aux
- \+ *def* direct_sum

Modified linear_algebra/tensor_product.lean
- \+ *def* tensor_product.direct_sum



## [2018-11-05 13:32:36-05:00](https://github.com/leanprover-community/mathlib/commit/0963290)
fix(data/real/irrational): fix build
#### Estimated changes
Modified data/real/irrational.lean




## [2018-11-05 17:58:46+01:00](https://github.com/leanprover-community/mathlib/commit/21d4d1c)
feat(field_theory/perfect_closure): define the perfect closure of a field
#### Estimated changes
Modified data/nat/basic.lean
- \+ *theorem* nat.iterate_cancel
- \+ *theorem* nat.iterate_inj
- \+ *theorem* nat.iterate₀
- \+ *theorem* nat.iterate₁
- \+ *theorem* nat.iterate₂

Added field_theory/perfect_closure.lean
- \+ *theorem* frobenius_pth_root
- \+ *theorem* is_ring_hom.pth_root
- \+ *def* perfect_closure.UMP
- \+ *theorem* perfect_closure.eq_iff'
- \+ *theorem* perfect_closure.eq_iff
- \+ *theorem* perfect_closure.eq_pth_root
- \+ *def* perfect_closure.frobenius_equiv
- \+ *theorem* perfect_closure.frobenius_equiv_apply
- \+ *theorem* perfect_closure.frobenius_mk
- \+ *theorem* perfect_closure.int_cast
- \+ *theorem* perfect_closure.mk_zero
- \+ *theorem* perfect_closure.nat_cast
- \+ *theorem* perfect_closure.nat_cast_eq_iff
- \+ *def* perfect_closure.of
- \+ *theorem* perfect_closure.r.sound
- \+ *def* perfect_closure
- \+ *theorem* pth_root_frobenius



## [2018-11-05 17:58:46+01:00](https://github.com/leanprover-community/mathlib/commit/8eac03c)
feat(algebra/char_p): define the characteristic of a semiring
#### Estimated changes
Added algebra/char_p.lean
- \+ *theorem* add_pow_char
- \+ *theorem* char_p.cast_eq_zero
- \+ *theorem* char_p.eq
- \+ *theorem* char_p.exists
- \+ *theorem* char_p.exists_unique
- \+ *def* frobenius
- \+ *theorem* frobenius_add
- \+ *theorem* frobenius_def
- \+ *theorem* frobenius_inj
- \+ *theorem* frobenius_mul
- \+ *theorem* frobenius_nat_cast
- \+ *theorem* frobenius_neg
- \+ *theorem* frobenius_one
- \+ *theorem* frobenius_sub
- \+ *theorem* frobenius_zero
- \+ *theorem* is_monoid_hom.map_frobenius
- \+ *theorem* ring_char.eq
- \+ *theorem* ring_char.spec

Modified algebra/group_power.lean
- \+ *theorem* pow_eq_zero



## [2018-11-05 17:46:35+01:00](https://github.com/leanprover-community/mathlib/commit/53d4883)
refactor(cau_seq): unify real.lim, complex.lim and cau_seq.lim ([#433](https://github.com/leanprover-community/mathlib/pull/433))
#### Estimated changes
Modified analysis/real.lean


Modified data/complex/basic.lean
- \- *lemma* complex.eq_lim_of_const_equiv
- \- *theorem* complex.equiv_lim
- \+ *theorem* complex.equiv_lim_aux
- \- *lemma* complex.im_const_equiv_of_const_equiv
- \+/\- *lemma* complex.is_cau_seq_conj
- \+/\- *lemma* complex.lim_abs
- \- *lemma* complex.lim_add
- \+/\- *lemma* complex.lim_conj
- \- *lemma* complex.lim_const
- \+ *lemma* complex.lim_eq_lim_im_add_lim_re
- \- *lemma* complex.lim_eq_lim_of_equiv
- \- *lemma* complex.lim_eq_of_equiv_const
- \- *lemma* complex.lim_eq_zero_iff
- \+ *lemma* complex.lim_im
- \- *lemma* complex.lim_inv
- \- *lemma* complex.lim_mul
- \- *lemma* complex.lim_mul_lim
- \- *lemma* complex.lim_neg
- \+ *lemma* complex.lim_re
- \- *lemma* complex.re_const_equiv_of_const_equiv

Modified data/complex/exponential.lean


Modified data/padics/hensel.lean


Modified data/padics/padic_integers.lean


Modified data/padics/padic_numbers.lean


Modified data/real/basic.lean
- \- *lemma* real.eq_lim_of_const_equiv
- \- *theorem* real.equiv_lim
- \- *lemma* real.le_lim
- \- *lemma* real.lim_add
- \- *lemma* real.lim_const
- \- *lemma* real.lim_eq_lim_of_equiv
- \- *lemma* real.lim_eq_of_equiv_const
- \- *lemma* real.lim_eq_zero_iff
- \- *lemma* real.lim_inv
- \- *lemma* real.lim_le
- \- *lemma* real.lim_lt
- \- *lemma* real.lim_mul
- \- *lemma* real.lim_mul_lim
- \- *lemma* real.lim_neg
- \- *lemma* real.lt_lim

Modified data/real/cau_seq.lean
- \+/\- *theorem* cau_seq.const_equiv
- \- *theorem* cau_seq.mul_lim_zero
- \+ *theorem* cau_seq.mul_lim_zero_left
- \+ *theorem* cau_seq.mul_lim_zero_right

Modified data/real/cau_seq_completion.lean
- \+/\- *lemma* cau_seq.complete
- \+ *lemma* cau_seq.eq_lim_of_const_equiv
- \+ *lemma* cau_seq.equiv_lim
- \+ *lemma* cau_seq.le_lim
- \+ *lemma* cau_seq.lim_add
- \+ *lemma* cau_seq.lim_const
- \+ *lemma* cau_seq.lim_eq_lim_of_equiv
- \+ *lemma* cau_seq.lim_eq_of_equiv_const
- \+ *lemma* cau_seq.lim_eq_zero_iff
- \+ *lemma* cau_seq.lim_inv
- \+ *lemma* cau_seq.lim_le
- \+ *lemma* cau_seq.lim_lt
- \+ *lemma* cau_seq.lim_mul
- \+ *lemma* cau_seq.lim_mul_lim
- \+ *lemma* cau_seq.lim_neg
- \- *lemma* cau_seq.lim_spec
- \+ *lemma* cau_seq.lt_lim

Modified data/real/cau_seq_filter.lean




## [2018-11-05 17:44:01+01:00](https://github.com/leanprover-community/mathlib/commit/17da277)
feat(group_theory/eckmann_hilton): add Eckmann-Hilton ([#335](https://github.com/leanprover-community/mathlib/pull/335))
#### Estimated changes
Added group_theory/eckmann_hilton.lean
- \+ *def* eckmann_hilton.comm_group
- \+ *def* eckmann_hilton.comm_monoid
- \+ *lemma* eckmann_hilton.group.is_unital
- \+ *lemma* eckmann_hilton.mul
- \+ *lemma* eckmann_hilton.mul_assoc
- \+ *lemma* eckmann_hilton.mul_comm
- \+ *lemma* eckmann_hilton.one



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
- \- *theorem* add_smul'
- \+/\- *theorem* add_smul
- \+ *lemma* ideal.add_mem_iff_left
- \+ *lemma* ideal.add_mem_iff_right
- \+ *lemma* ideal.mul_mem_left
- \+ *lemma* ideal.mul_mem_right
- \+ *lemma* ideal.neg_mem_iff
- \+ *def* ideal
- \- *lemma* is_linear_map.comp
- \- *lemma* is_linear_map.id
- \- *lemma* is_linear_map.inverse
- \- *lemma* is_linear_map.map_add
- \- *lemma* is_linear_map.map_neg
- \- *lemma* is_linear_map.map_smul_left
- \- *lemma* is_linear_map.map_smul_right
- \- *lemma* is_linear_map.map_sub
- \- *lemma* is_linear_map.map_sum
- \- *lemma* is_linear_map.map_zero
- \+ *def* is_linear_map.mk'
- \+ *theorem* is_linear_map.mk'_apply
- \- *lemma* is_linear_map.neg
- \- *lemma* is_linear_map.sub
- \- *lemma* is_linear_map.sum
- \- *lemma* is_linear_map.zero
- \- *lemma* is_submodule.Inter_submodule
- \- *lemma* is_submodule.add
- \- *theorem* is_submodule.eq_univ_of_contains_unit
- \- *lemma* is_submodule.neg
- \- *lemma* is_submodule.smul_ne_0
- \- *lemma* is_submodule.sub
- \- *lemma* is_submodule.sum
- \- *theorem* is_submodule.univ_of_one_mem
- \- *lemma* is_submodule.zero
- \+ *def* linear_map.comp
- \+ *lemma* linear_map.comp_apply
- \+ *theorem* linear_map.ext
- \+ *theorem* linear_map.ext_iff
- \+ *def* linear_map.id
- \+ *lemma* linear_map.id_apply
- \+ *theorem* linear_map.is_linear
- \+ *lemma* linear_map.map_add
- \+ *lemma* linear_map.map_neg
- \+ *lemma* linear_map.map_smul
- \+ *lemma* linear_map.map_sub
- \+ *lemma* linear_map.map_sum
- \+ *lemma* linear_map.map_zero
- \+ *def* module.of_core
- \- *theorem* mul_smul'
- \+/\- *theorem* mul_smul
- \- *theorem* one_smul'
- \+/\- *theorem* one_smul
- \- *theorem* smul_add'
- \+/\- *theorem* smul_add
- \- *lemma* smul_eq_mul'
- \+/\- *lemma* smul_eq_mul
- \- *lemma* smul_smul'
- \+/\- *lemma* smul_smul
- \- *theorem* smul_zero'
- \+/\- *theorem* smul_zero
- \+ *lemma* submodule.add_mem
- \+ *lemma* submodule.add_mem_iff_left
- \+ *lemma* submodule.add_mem_iff_right
- \+ *lemma* submodule.coe_add
- \+ *lemma* submodule.coe_neg
- \+ *lemma* submodule.coe_smul
- \+ *lemma* submodule.coe_sub
- \+ *lemma* submodule.coe_zero
- \+ *theorem* submodule.ext'
- \+ *theorem* submodule.ext
- \+ *theorem* submodule.mem_coe
- \+ *lemma* submodule.neg_mem
- \+ *lemma* submodule.neg_mem_iff
- \+ *lemma* submodule.smul_mem
- \+ *theorem* submodule.smul_mem_iff
- \+ *lemma* submodule.sub_mem
- \+ *theorem* submodule.subtype_apply
- \+ *lemma* submodule.sum_mem
- \+ *lemma* submodule.zero_mem
- \+/\- *def* subspace
- \- *theorem* zero_smul'
- \+/\- *theorem* zero_smul

Modified algebra/order.lean
- \+ *lemma* eq_iff_le_not_lt

Modified algebra/pi_instances.lean
- \+ *lemma* prod.inv_mk
- \+ *lemma* prod.mk_mul_mk
- \+ *lemma* prod.one_eq_mk
- \+ *theorem* prod.smul_fst
- \+ *theorem* prod.smul_mk
- \+ *theorem* prod.smul_snd

Modified analysis/bounded_linear_maps.lean
- \+/\- *lemma* is_bounded_linear_map.tendsto

Modified analysis/normed_space.lean


Modified analysis/topology/quotient_topological_structures.lean
- \+/\- *lemma* quotient_ring.is_open_map_coe
- \+/\- *lemma* quotient_ring.quotient_map_coe_coe

Modified analysis/topology/topological_structures.lean
- \+ *def* ideal.closure
- \+ *lemma* ideal.coe_closure

Modified data/equiv/basic.lean
- \+ *def* equiv.prop_equiv_punit
- \+/\- *def* equiv.true_equiv_punit

Modified data/finsupp.lean
- \+ *lemma* finsupp.filter_add
- \+/\- *lemma* finsupp.filter_pos_add_filter_neg
- \+ *lemma* finsupp.filter_single_of_neg
- \+ *lemma* finsupp.filter_single_of_pos
- \+ *lemma* finsupp.filter_smul
- \+/\- *lemma* finsupp.map_domain_id
- \+ *lemma* finsupp.map_domain_smul
- \+/\- *lemma* finsupp.map_domain_zero
- \+ *lemma* finsupp.map_range_add
- \+ *lemma* finsupp.map_range_zero
- \+/\- *lemma* finsupp.smul_apply'
- \+ *lemma* finsupp.smul_single
- \+/\- *lemma* finsupp.sum_single
- \+ *lemma* finsupp.support_smul
- \+/\- *def* finsupp.to_has_scalar'
- \+/\- *def* finsupp.to_has_scalar
- \+/\- *def* finsupp.to_module
- \+ *def* finsupp.to_semimodule

Modified data/fintype.lean
- \+ *theorem* fintype.fintype.card_of_subsingleton
- \+ *theorem* fintype.fintype.univ_of_subsingleton
- \+ *def* fintype.of_subsingleton

Modified data/holor.lean


Modified data/padics/padic_integers.lean
- \+ *lemma* padic_int.is_unit_iff
- \- *def* padic_int.maximal_ideal
- \- *lemma* padic_int.maximal_ideal_add
- \- *lemma* padic_int.maximal_ideal_eq_nonunits
- \- *lemma* padic_int.maximal_ideal_eq_or_univ_of_subset
- \- *lemma* padic_int.maximal_ideal_mul
- \- *lemma* padic_int.maximal_ideal_ne_univ
- \- *lemma* padic_int.maximal_ideal_unique
- \+ *lemma* padic_int.mem_nonunits
- \+ *lemma* padic_int.norm_lt_one_add
- \+ *lemma* padic_int.norm_lt_one_mul

Modified data/padics/padic_numbers.lean
- \+/\- *theorem* padic.rat_dense'
- \+/\- *theorem* padic.rat_dense
- \+/\- *def* padic
- \+/\- *def* padic_norm_e

Modified data/polynomial.lean
- \- *lemma* polynomial.coeff_is_linear
- \+ *def* polynomial.lcoeff
- \+ *lemma* polynomial.lcoeff_apply

Modified data/set/basic.lean
- \+ *theorem* set.coe_nonempty_iff_ne_empty
- \+ *theorem* set.pairwise_on.mono'
- \+ *theorem* set.pairwise_on.mono

Modified data/set/lattice.lean
- \+/\- *theorem* disjoint_bot_left
- \+/\- *theorem* disjoint_bot_right

Modified group_theory/free_abelian_group.lean


Modified linear_algebra/basic.lean
- \+ *lemma* classical.some_spec3
- \- *lemma* constr_add
- \- *lemma* constr_basis
- \- *lemma* constr_congr
- \- *lemma* constr_eq
- \- *lemma* constr_im_eq_span
- \- *lemma* constr_mem_span
- \- *lemma* constr_neg
- \- *lemma* constr_smul
- \- *lemma* constr_sub
- \- *lemma* constr_zero
- \- *lemma* eq_of_linear_independent_of_span
- \- *def* equiv_of_is_basis
- \- *lemma* exists_finite_card_le_of_finite_of_linear_independent_of_span
- \- *lemma* exists_is_basis
- \- *lemma* exists_left_inverse_linear_map_of_injective
- \- *lemma* exists_linear_independent
- \- *lemma* exists_of_linear_independent_of_finite_span
- \- *lemma* exists_right_inverse_linear_map_of_surjective
- \- *lemma* exists_subset_is_basis
- \+/\- *lemma* finset.smul_sum
- \+/\- *lemma* finsupp.smul_sum
- \- *def* is_basis.constr
- \- *lemma* is_basis.eq_linear_map
- \- *lemma* is_basis.linear_equiv
- \- *lemma* is_basis.map_constr
- \- *lemma* is_basis.map_repr
- \- *def* is_basis
- \- *lemma* is_linear_map.finsupp_sum
- \- *lemma* is_submodule_range_smul
- \- *lemma* lc.is_linear_map_sum
- \- *def* lc
- \- *lemma* linear_eq_on
- \+ *theorem* linear_equiv.apply_symm_apply
- \+ *theorem* linear_equiv.coe_apply
- \+ *def* linear_equiv.congr_right
- \- *lemma* linear_equiv.linear_inv
- \+ *theorem* linear_equiv.of_bijective_apply
- \+ *def* linear_equiv.of_linear
- \+ *theorem* linear_equiv.of_linear_apply
- \+ *theorem* linear_equiv.of_linear_symm_apply
- \+ *def* linear_equiv.of_top
- \+ *theorem* linear_equiv.of_top_apply
- \+ *theorem* linear_equiv.of_top_symm_apply
- \+/\- *def* linear_equiv.refl
- \+/\- *def* linear_equiv.symm
- \+ *theorem* linear_equiv.symm_apply_apply
- \- *lemma* linear_independent.eq_0_of_span
- \- *lemma* linear_independent.image
- \- *lemma* linear_independent.inj_span_iff_inj
- \- *lemma* linear_independent.insert
- \- *lemma* linear_independent.mono
- \- *lemma* linear_independent.of_image
- \- *def* linear_independent.repr
- \- *lemma* linear_independent.unique
- \- *def* linear_independent
- \- *lemma* linear_independent_Union_of_directed
- \- *lemma* linear_independent_bUnion_of_directed
- \- *lemma* linear_independent_empty
- \- *lemma* linear_independent_iff_not_mem_span
- \- *lemma* linear_independent_singleton
- \- *lemma* linear_independent_union
- \+ *lemma* linear_map.add_apply
- \+ *def* linear_map.cod_restrict
- \+ *theorem* linear_map.cod_restrict_apply
- \+ *theorem* linear_map.comap_cod_restrict
- \+ *theorem* linear_map.comap_injective
- \+ *theorem* linear_map.comap_le_comap_iff
- \+ *lemma* linear_map.comap_map_eq
- \+ *lemma* linear_map.comap_map_eq_self
- \+ *theorem* linear_map.comap_pair_prod
- \+ *theorem* linear_map.comp_id
- \+ *def* linear_map.congr_right
- \+ *def* linear_map.copair
- \+ *theorem* linear_map.copair_apply
- \+ *theorem* linear_map.copair_inl
- \+ *theorem* linear_map.copair_inl_inr
- \+ *theorem* linear_map.copair_inr
- \+ *theorem* linear_map.disjoint_ker'
- \+ *theorem* linear_map.disjoint_ker
- \+ *def* linear_map.endomorphism_ring
- \+ *lemma* linear_map.finsupp_sum
- \+ *def* linear_map.fst
- \+ *theorem* linear_map.fst_apply
- \+ *theorem* linear_map.fst_eq_copair
- \+ *theorem* linear_map.fst_pair
- \+ *def* linear_map.general_linear_group
- \+ *theorem* linear_map.id_comp
- \+ *theorem* linear_map.inj_of_disjoint_ker
- \+ *def* linear_map.inl
- \+ *theorem* linear_map.inl_apply
- \+ *theorem* linear_map.inl_eq_pair
- \+ *def* linear_map.inr
- \+ *theorem* linear_map.inr_apply
- \+ *theorem* linear_map.inr_eq_pair
- \+ *def* linear_map.inverse
- \+ *def* linear_map.ker
- \+ *theorem* linear_map.ker_comp
- \+ *theorem* linear_map.ker_eq_bot
- \+ *theorem* linear_map.ker_eq_top
- \+ *theorem* linear_map.ker_id
- \+ *theorem* linear_map.ker_le_ker_comp
- \+ *theorem* linear_map.ker_zero
- \+ *lemma* linear_map.le_ker_iff_map
- \- *lemma* linear_map.linear_independent_image_iff
- \+ *theorem* linear_map.map_cod_restrict
- \+ *lemma* linear_map.map_comap_eq
- \+ *lemma* linear_map.map_comap_eq_self
- \+ *theorem* linear_map.map_copair_prod
- \+ *theorem* linear_map.map_injective
- \+ *theorem* linear_map.map_le_map_iff
- \+ *theorem* linear_map.mem_ker
- \+ *theorem* linear_map.mem_range
- \+ *lemma* linear_map.mul_app
- \+ *lemma* linear_map.neg_apply
- \+ *lemma* linear_map.one_app
- \+ *def* linear_map.pair
- \+ *theorem* linear_map.pair_apply
- \+ *theorem* linear_map.pair_fst_snd
- \+ *theorem* linear_map.prod_eq_inf_comap
- \+ *theorem* linear_map.prod_eq_sup_map
- \+ *def* linear_map.range
- \+ *theorem* linear_map.range_coe
- \+ *theorem* linear_map.range_comp
- \+ *theorem* linear_map.range_comp_le_range
- \+ *theorem* linear_map.range_eq_top
- \+ *theorem* linear_map.range_id
- \+ *lemma* linear_map.range_le_iff_comap
- \+ *lemma* linear_map.smul_apply
- \+ *def* linear_map.smul_right
- \+ *theorem* linear_map.smul_right_apply
- \+ *def* linear_map.snd
- \+ *theorem* linear_map.snd_apply
- \+ *theorem* linear_map.snd_eq_copair
- \+ *theorem* linear_map.snd_pair
- \+ *lemma* linear_map.span_inl_union_inr
- \+ *lemma* linear_map.sub_apply
- \+ *theorem* linear_map.sub_mem_ker_iff
- \+ *lemma* linear_map.sum_apply
- \+ *lemma* linear_map.zero_apply
- \- *lemma* mem_span_insert
- \- *lemma* mem_span_insert_exchange
- \- *def* module_equiv_lc
- \- *lemma* repr_add
- \- *lemma* repr_eq
- \- *lemma* repr_eq_repr_of_subset
- \- *lemma* repr_eq_single
- \- *lemma* repr_eq_zero
- \- *lemma* repr_finsupp_sum
- \- *lemma* repr_neg
- \- *lemma* repr_not_span
- \- *lemma* repr_smul
- \- *lemma* repr_spec
- \- *lemma* repr_sub
- \- *lemma* repr_sum
- \- *lemma* repr_sum_eq
- \- *lemma* repr_support
- \- *lemma* repr_zero
- \- *def* span
- \- *lemma* span_empty
- \- *lemma* span_eq
- \- *lemma* span_eq_of_is_submodule
- \- *lemma* span_image_of_linear_map
- \- *lemma* span_insert
- \- *lemma* span_insert_eq_span
- \- *lemma* span_minimal
- \- *lemma* span_mono
- \- *lemma* span_singleton
- \- *lemma* span_span
- \- *lemma* span_union
- \+ *theorem* submodule.Inf_coe
- \+ *theorem* submodule.Union_coe_of_directed
- \+ *lemma* submodule.bot_coe
- \+ *def* submodule.comap
- \+ *theorem* submodule.comap_bot
- \+ *lemma* submodule.comap_coe
- \+ *lemma* submodule.comap_comp
- \+ *theorem* submodule.comap_fst
- \+ *lemma* submodule.comap_id
- \+ *theorem* submodule.comap_liftq
- \+ *theorem* submodule.comap_map_mkq
- \+ *def* submodule.comap_mkq.le_order_embedding
- \+ *def* submodule.comap_mkq.lt_order_embedding
- \+ *def* submodule.comap_mkq.order_iso
- \+ *lemma* submodule.comap_mkq_embedding_eq
- \+ *lemma* submodule.comap_mono
- \+ *theorem* submodule.comap_snd
- \+ *lemma* submodule.comap_top
- \+ *theorem* submodule.disjoint_def
- \+ *lemma* submodule.eq_top_iff'
- \+ *theorem* submodule.inf_coe
- \+ *theorem* submodule.infi_coe
- \+ *theorem* submodule.ker_inl
- \+ *theorem* submodule.ker_inr
- \+ *theorem* submodule.ker_liftq
- \+ *theorem* submodule.ker_liftq_eq_bot
- \+ *theorem* submodule.ker_mkq
- \+ *theorem* submodule.ker_subtype
- \+ *lemma* submodule.le_comap_map
- \+ *lemma* submodule.le_comap_mkq
- \+ *lemma* submodule.le_def'
- \+ *lemma* submodule.le_def
- \+ *def* submodule.liftq
- \+ *theorem* submodule.liftq_apply
- \+ *theorem* submodule.liftq_mkq
- \+ *def* submodule.map
- \+ *lemma* submodule.map_bot
- \+ *lemma* submodule.map_coe
- \+ *lemma* submodule.map_comap_le
- \+ *lemma* submodule.map_comap_subtype
- \+ *lemma* submodule.map_comp
- \+ *lemma* submodule.map_id
- \+ *lemma* submodule.map_inf_eq_map_inf_comap
- \+ *theorem* submodule.map_inl
- \+ *theorem* submodule.map_inr
- \+ *lemma* submodule.map_le_iff_le_comap
- \+ *lemma* submodule.map_mono
- \+ *def* submodule.map_subtype.le_order_embedding
- \+ *def* submodule.map_subtype.lt_order_embedding
- \+ *def* submodule.map_subtype.order_iso
- \+ *lemma* submodule.map_subtype_embedding_eq
- \+ *lemma* submodule.map_subtype_le
- \+ *theorem* submodule.map_top
- \+ *def* submodule.mapq
- \+ *theorem* submodule.mapq_apply
- \+ *theorem* submodule.mapq_mkq
- \+ *lemma* submodule.mem_bot
- \+ *lemma* submodule.mem_comap
- \+ *theorem* submodule.mem_inf
- \+ *theorem* submodule.mem_infi
- \+ *lemma* submodule.mem_map
- \+ *lemma* submodule.mem_prod
- \+ *lemma* submodule.mem_span
- \+ *lemma* submodule.mem_span_insert'
- \+ *lemma* submodule.mem_span_insert
- \+ *lemma* submodule.mem_span_singleton
- \+ *lemma* submodule.mem_sup
- \+ *theorem* submodule.mem_supr_of_directed
- \+ *lemma* submodule.mem_top
- \+ *def* submodule.mkq
- \+ *theorem* submodule.mkq_apply
- \+ *theorem* submodule.mkq_map_self
- \+ *def* submodule.of_le
- \+ *theorem* submodule.of_le_apply
- \+ *def* submodule.prod
- \+ *lemma* submodule.prod_bot
- \+ *lemma* submodule.prod_coe
- \+ *theorem* submodule.prod_comap_inl
- \+ *theorem* submodule.prod_comap_inr
- \+ *lemma* submodule.prod_inf_prod
- \+ *theorem* submodule.prod_map_fst
- \+ *theorem* submodule.prod_map_snd
- \+ *lemma* submodule.prod_mono
- \+ *lemma* submodule.prod_sup_prod
- \+ *lemma* submodule.prod_top
- \+ *theorem* submodule.quotient.mk'_eq_mk
- \+ *def* submodule.quotient.mk
- \+ *theorem* submodule.quotient.mk_add
- \+ *theorem* submodule.quotient.mk_eq_mk
- \+ *theorem* submodule.quotient.mk_eq_zero
- \+ *theorem* submodule.quotient.mk_neg
- \+ *theorem* submodule.quotient.mk_smul
- \+ *theorem* submodule.quotient.mk_zero
- \+ *theorem* submodule.quotient.quot_mk_eq_mk
- \+ *def* submodule.quotient
- \+ *def* submodule.quotient_rel
- \+ *theorem* submodule.range_fst
- \+ *theorem* submodule.range_mkq
- \+ *theorem* submodule.range_snd
- \+ *theorem* submodule.range_subtype
- \+ *def* submodule.span
- \+ *lemma* submodule.span_Union
- \+ *lemma* submodule.span_empty
- \+ *lemma* submodule.span_eq
- \+ *lemma* submodule.span_eq_bot
- \+ *lemma* submodule.span_eq_of_le
- \+ *lemma* submodule.span_image
- \+ *lemma* submodule.span_induction
- \+ *lemma* submodule.span_insert_eq_span
- \+ *lemma* submodule.span_le
- \+ *lemma* submodule.span_mono
- \+ *lemma* submodule.span_prod_le
- \+ *lemma* submodule.span_singleton_eq_bot
- \+ *lemma* submodule.span_singleton_eq_range
- \+ *lemma* submodule.span_span
- \+ *lemma* submodule.span_union
- \+ *lemma* submodule.subset_span
- \+ *lemma* submodule.top_coe
- \- *lemma* subset_span
- \- *lemma* zero_not_mem_of_linear_independent

Added linear_algebra/basis.lean
- \+ *lemma* constr_add
- \+ *lemma* constr_basis
- \+ *lemma* constr_congr
- \+ *lemma* constr_eq
- \+ *lemma* constr_neg
- \+ *lemma* constr_range
- \+ *lemma* constr_self
- \+ *lemma* constr_smul
- \+ *lemma* constr_sub
- \+ *lemma* constr_zero
- \+ *lemma* disjoint_span_singleton
- \+ *lemma* eq_of_linear_independent_of_span
- \+ *def* equiv_of_is_basis
- \+ *lemma* exists_finite_card_le_of_finite_of_linear_independent_of_span
- \+ *lemma* exists_is_basis
- \+ *lemma* exists_left_inverse_linear_map_of_injective
- \+ *lemma* exists_linear_independent
- \+ *lemma* exists_of_linear_independent_of_finite_span
- \+ *lemma* exists_right_inverse_linear_map_of_surjective
- \+ *lemma* exists_subset_is_basis
- \+ *def* is_basis.constr
- \+ *theorem* is_basis.constr_apply
- \+ *lemma* is_basis.ext
- \+ *lemma* is_basis.mem_span
- \+ *def* is_basis.repr
- \+ *lemma* is_basis.repr_eq_single
- \+ *lemma* is_basis.repr_ker
- \+ *lemma* is_basis.repr_range
- \+ *lemma* is_basis.repr_supported
- \+ *lemma* is_basis.total_comp_repr
- \+ *lemma* is_basis.total_repr
- \+ *def* is_basis
- \+ *lemma* is_basis_inl_union_inr
- \+ *lemma* linear_equiv.is_basis
- \+ *lemma* linear_independent.disjoint_ker
- \+ *lemma* linear_independent.image
- \+ *lemma* linear_independent.inj_span_iff_inj
- \+ *lemma* linear_independent.insert
- \+ *lemma* linear_independent.mono
- \+ *lemma* linear_independent.of_image
- \+ *def* linear_independent.repr
- \+ *lemma* linear_independent.repr_eq
- \+ *lemma* linear_independent.repr_eq_repr_of_subset
- \+ *lemma* linear_independent.repr_eq_single
- \+ *lemma* linear_independent.repr_ker
- \+ *lemma* linear_independent.repr_range
- \+ *lemma* linear_independent.repr_supported
- \+ *lemma* linear_independent.supported_disjoint_ker
- \+ *lemma* linear_independent.total_comp_repr
- \+ *def* linear_independent.total_equiv
- \+ *lemma* linear_independent.total_repr
- \+ *lemma* linear_independent.unique
- \+ *def* linear_independent
- \+ *lemma* linear_independent_Union_of_directed
- \+ *lemma* linear_independent_bUnion_of_directed
- \+ *lemma* linear_independent_empty
- \+ *theorem* linear_independent_iff
- \+ *lemma* linear_independent_iff_not_mem_span
- \+ *lemma* linear_independent_iff_not_smul_mem_span
- \+ *theorem* linear_independent_iff_total_on
- \+ *lemma* linear_independent_inl_union_inr
- \+ *lemma* linear_independent_of_finite
- \+ *lemma* linear_independent_sUnion_of_directed
- \+ *lemma* linear_independent_singleton
- \+ *lemma* linear_independent_union
- \+ *lemma* linear_map.linear_independent_image_iff
- \+ *lemma* mem_span_insert_exchange
- \+ *def* module_equiv_lc
- \+ *theorem* quotient_prod_linear_equiv
- \+ *lemma* zero_not_mem_of_linear_independent

Modified linear_algebra/dimension.lean
- \+ *theorem* dim_prod
- \+ *theorem* dim_quotient
- \+ *theorem* dim_range_add_dim_ker
- \+ *theorem* is_basis.le_span
- \+ *theorem* is_basis.mk_eq_dim
- \+ *theorem* linear_equiv.dim_eq
- \+ *theorem* mk_eq_mk_of_basis
- \- *theorem* vector_space.basis_le_span
- \+/\- *def* vector_space.dim
- \- *theorem* vector_space.dim_eq_of_linear_equiv
- \- *theorem* vector_space.dim_im_add_dim_ker
- \- *theorem* vector_space.dim_prod
- \- *theorem* vector_space.dim_quotient
- \- *theorem* vector_space.mk_basis
- \- *theorem* vector_space.mk_eq_mk_of_basis

Added linear_algebra/lc.lean
- \+ *def* lc.apply
- \+ *theorem* lc.apply_apply
- \+ *theorem* lc.lsum_apply
- \+ *theorem* lc.map_apply
- \+ *theorem* lc.map_comp
- \+ *theorem* lc.map_disjoint_ker
- \+ *theorem* lc.map_id
- \+ *theorem* lc.map_supported
- \+ *theorem* lc.map_total
- \+ *theorem* lc.mem_supported'
- \+ *theorem* lc.mem_supported
- \+ *theorem* lc.range_restrict_dom
- \+ *def* lc.restrict_dom
- \+ *theorem* lc.restrict_dom_apply
- \+ *theorem* lc.restrict_dom_comp_subtype
- \+ *theorem* lc.single_mem_supported
- \+ *def* lc.supported
- \+ *theorem* lc.supported_Inter
- \+ *theorem* lc.supported_Union
- \+ *theorem* lc.supported_comap_map
- \+ *theorem* lc.supported_empty
- \+ *theorem* lc.supported_eq_span_single
- \+ *theorem* lc.supported_mono
- \+ *theorem* lc.supported_union
- \+ *theorem* lc.supported_univ
- \+ *theorem* lc.total_apply
- \+ *def* lc.total_on
- \+ *theorem* lc.total_on_range
- \+ *theorem* lc.total_range
- \+ *theorem* lc.total_single
- \+ *def* lc
- \+ *lemma* linear_eq_on
- \+ *theorem* mem_span_iff_lc
- \+ *theorem* span_eq_map_lc

Deleted linear_algebra/linear_map_module.lean
- \- *lemma* linear_map.add_app
- \- *theorem* linear_map.ext
- \- *def* linear_map.im
- \- *theorem* linear_map.inj_of_trivial_ker
- \- *lemma* linear_map.is_linear_map_coe
- \- *lemma* linear_map.is_submodule.add_left_iff
- \- *lemma* linear_map.is_submodule.neg_iff
- \- *def* linear_map.ker
- \- *theorem* linear_map.ker_of_map_eq_map
- \- *lemma* linear_map.map_add
- \- *lemma* linear_map.map_neg
- \- *lemma* linear_map.map_smul
- \- *lemma* linear_map.map_sub
- \- *lemma* linear_map.map_zero
- \- *lemma* linear_map.mem_im
- \- *lemma* linear_map.mem_ker
- \- *lemma* linear_map.neg_app
- \- *def* linear_map.quot_ker_equiv_im
- \- *lemma* linear_map.smul_app
- \- *theorem* linear_map.sub_ker
- \- *def* linear_map.union_quotient_equiv_quotient_inter
- \- *lemma* linear_map.zero_app
- \- *def* linear_map
- \- *def* module.endomorphism_ring
- \- *def* module.general_linear_group
- \- *lemma* module.mul_app
- \- *lemma* module.one_app

Modified linear_algebra/multivariate_polynomial.lean


Deleted linear_algebra/prod_module.lean
- \- *lemma* prod.is_basis_inl_union_inr
- \- *lemma* prod.is_linear_map_prod_fst
- \- *lemma* prod.is_linear_map_prod_inl
- \- *lemma* prod.is_linear_map_prod_inr
- \- *lemma* prod.is_linear_map_prod_mk
- \- *lemma* prod.is_linear_map_prod_snd
- \- *lemma* prod.linear_independent_inl_union_inr
- \- *lemma* prod.span_inl_union_inr
- \- *lemma* prod.span_prod

Deleted linear_algebra/quotient_module.lean
- \- *def* is_submodule.quotient_rel
- \- *lemma* quotient_module.coe_add
- \- *lemma* quotient_module.coe_eq_zero
- \- *lemma* quotient_module.coe_smul
- \- *lemma* quotient_module.coe_zero
- \- *lemma* quotient_module.is_linear_map_quotient_lift
- \- *lemma* quotient_module.is_linear_map_quotient_mk
- \- *def* quotient_module.mk
- \- *lemma* quotient_module.quotient.exists_rep
- \- *lemma* quotient_module.quotient.injective_lift
- \- *def* quotient_module.quotient.lift
- \- *lemma* quotient_module.quotient.lift_mk
- \- *def* quotient_module.quotient
- \- *theorem* quotient_module.quotient_prod_linear_equiv

Deleted linear_algebra/submodule.lean
- \- *def* quotient_module.le_order_embedding
- \- *def* quotient_module.lt_order_embedding
- \- *theorem* submodule.Union_set_of_directed
- \- *theorem* submodule.bot_set
- \- *lemma* submodule.coe_comap
- \- *lemma* submodule.coe_map
- \- *lemma* submodule.coe_prod
- \- *def* submodule.comap
- \- *lemma* submodule.comap_comp
- \- *lemma* submodule.comap_id
- \- *lemma* submodule.comap_map_eq
- \- *def* submodule.comap_quotient.order_iso
- \- *def* submodule.comap_quotient
- \- *theorem* submodule.ext
- \- *lemma* submodule.injective_comap
- \- *lemma* submodule.injective_map
- \- *def* submodule.lt_order_embedding
- \- *def* submodule.map
- \- *lemma* submodule.map_comp
- \- *lemma* submodule.map_id
- \- *def* submodule.map_subtype.le_order_embedding
- \- *def* submodule.map_subtype.order_iso
- \- *def* submodule.map_subtype
- \- *lemma* submodule.map_subtype_embedding_eq
- \- *lemma* submodule.map_subtype_subset
- \- *theorem* submodule.mem_coe
- \- *lemma* submodule.mem_span_singleton
- \- *def* submodule.prod
- \- *theorem* submodule.sInter_set
- \- *def* submodule.span
- \- *theorem* submodule.span_empty
- \- *lemma* submodule.span_singleton_subset
- \- *theorem* submodule.span_subset_iff
- \- *theorem* submodule.span_union
- \- *lemma* submodule.subset_comap_quotient
- \- *theorem* submodule.top_set

Deleted linear_algebra/subtype_module.lean
- \- *lemma* is_submodule.coe_add
- \- *lemma* is_submodule.coe_neg
- \- *lemma* is_submodule.coe_smul
- \- *lemma* is_submodule.coe_zero
- \- *lemma* is_submodule.is_linear_map_coe
- \- *lemma* is_submodule.is_linear_map_subtype_mk
- \- *lemma* is_submodule.is_linear_map_subtype_val
- \- *lemma* is_submodule.sub_val

Modified linear_algebra/tensor_product.lean
- \- *theorem* is_bilinear_map.comm
- \- *theorem* is_bilinear_map.comp
- \- *theorem* is_bilinear_map.linear_left
- \- *theorem* is_bilinear_map.linear_right
- \- *theorem* is_bilinear_map.neg_left
- \- *theorem* is_bilinear_map.neg_right
- \- *theorem* is_bilinear_map.zero_left
- \- *theorem* is_bilinear_map.zero_right
- \+ *def* linear_map.compl₂
- \+ *theorem* linear_map.compl₂_apply
- \+ *def* linear_map.compr₂
- \+ *theorem* linear_map.compr₂_apply
- \+ *theorem* linear_map.ext₂
- \+ *def* linear_map.flip
- \+ *theorem* linear_map.flip_apply
- \+ *theorem* linear_map.flip_inj
- \+ *def* linear_map.lcomp
- \+ *theorem* linear_map.lcomp_apply
- \+ *def* linear_map.lflip
- \+ *theorem* linear_map.lflip_apply
- \+ *def* linear_map.llcomp
- \+ *theorem* linear_map.llcomp_apply
- \+ *def* linear_map.lsmul
- \+ *theorem* linear_map.lsmul_apply
- \+ *theorem* linear_map.map_add₂
- \+ *theorem* linear_map.map_neg₂
- \+ *theorem* linear_map.map_smul₂
- \+ *theorem* linear_map.map_zero₂
- \+ *def* linear_map.mk₂
- \+ *theorem* linear_map.mk₂_apply
- \+/\- *lemma* tensor_product.add_tmul
- \- *theorem* tensor_product.bilinear
- \+ *def* tensor_product.congr
- \+ *def* tensor_product.curry
- \+ *theorem* tensor_product.curry_apply
- \+ *theorem* tensor_product.ext
- \+ *def* tensor_product.lcurry
- \+ *theorem* tensor_product.lcurry_apply
- \+ *def* tensor_product.lift.equiv
- \+ *lemma* tensor_product.lift.tmul'
- \+ *lemma* tensor_product.lift.tmul
- \+ *theorem* tensor_product.lift.unique
- \+ *def* tensor_product.lift
- \+ *lemma* tensor_product.lift_aux.add
- \+ *lemma* tensor_product.lift_aux.smul
- \+ *def* tensor_product.lift_aux
- \+ *theorem* tensor_product.lift_compr₂
- \+ *theorem* tensor_product.lift_mk
- \+ *theorem* tensor_product.lift_mk_compr₂
- \+ *def* tensor_product.map
- \+ *theorem* tensor_product.map_tmul
- \+ *def* tensor_product.mk
- \+ *lemma* tensor_product.mk_apply
- \+ *theorem* tensor_product.mk_compr₂_inj
- \+ *lemma* tensor_product.neg_tmul
- \+/\- *def* tensor_product.smul.aux
- \- *lemma* tensor_product.smul.is_add_group_hom
- \- *def* tensor_product.smul
- \+/\- *lemma* tensor_product.smul_tmul
- \- *lemma* tensor_product.tmul.add_left
- \- *lemma* tensor_product.tmul.add_right
- \- *lemma* tensor_product.tmul.smul
- \+/\- *lemma* tensor_product.tmul_add
- \+ *lemma* tensor_product.tmul_neg
- \+ *lemma* tensor_product.tmul_zero
- \- *lemma* tensor_product.to_module.add
- \- *def* tensor_product.to_module.equiv
- \- *theorem* tensor_product.to_module.ext
- \- *def* tensor_product.to_module.linear
- \- *lemma* tensor_product.to_module.smul
- \- *lemma* tensor_product.to_module.tmul
- \- *theorem* tensor_product.to_module.unique
- \- *def* tensor_product.to_module
- \+ *def* tensor_product.uncurry
- \+ *theorem* tensor_product.uncurry_apply
- \+ *lemma* tensor_product.zero_tmul

Modified logic/basic.lean


Modified order/zorn.lean
- \+ *theorem* zorn.chain.mono
- \+ *theorem* zorn.zorn_subset₀

Modified ring_theory/associated.lean
- \+ *theorem* is_unit_iff_exists_inv'
- \+ *theorem* is_unit_iff_exists_inv
- \+ *theorem* is_unit_of_mul_is_unit_left
- \+ *theorem* is_unit_of_mul_is_unit_right
- \+ *theorem* is_unit_zero_iff
- \+ *theorem* mul_dvd_of_is_unit_left
- \+ *theorem* mul_dvd_of_is_unit_right
- \+ *theorem* nonzero_of_irreducible
- \+/\- *theorem* not_is_unit_zero

Modified ring_theory/ideals.lean
- \+ *theorem* coe_subset_nonunits
- \+ *def* ideal.comap
- \+ *theorem* ideal.comap_ne_top
- \+ *theorem* ideal.eq_top_iff_one
- \+ *theorem* ideal.eq_top_of_is_unit_mem
- \+ *theorem* ideal.eq_top_of_unit_mem
- \+ *theorem* ideal.exists_le_maximal
- \+ *theorem* ideal.is_maximal.eq_of_le
- \+ *theorem* ideal.is_maximal.exists_inv
- \+ *theorem* ideal.is_maximal.is_prime
- \+ *def* ideal.is_maximal
- \+ *theorem* ideal.is_maximal_iff
- \+ *theorem* ideal.is_prime.mem_or_mem
- \+ *theorem* ideal.is_prime.mem_or_mem_of_mul_eq_zero
- \+ *def* ideal.is_prime
- \+ *theorem* ideal.mem_comap
- \+ *lemma* ideal.mem_span_insert'
- \+ *lemma* ideal.mem_span_insert
- \+ *lemma* ideal.mem_span_singleton'
- \+ *lemma* ideal.mem_span_singleton
- \+ *theorem* ideal.ne_top_iff_one
- \+ *lemma* ideal.quotient.eq_zero_iff_mem
- \+ *lemma* ideal.quotient.exists_inv
- \+ *def* ideal.quotient.map_mk
- \+ *def* ideal.quotient.mk
- \+ *lemma* ideal.quotient.mk_add
- \+ *theorem* ideal.quotient.mk_mul
- \+ *lemma* ideal.quotient.mk_neg
- \+ *lemma* ideal.quotient.mk_one
- \+ *lemma* ideal.quotient.mk_pow
- \+ *lemma* ideal.quotient.mk_sub
- \+ *lemma* ideal.quotient.mk_zero
- \+ *theorem* ideal.quotient.zero_eq_one_iff
- \+ *theorem* ideal.quotient.zero_ne_one_iff
- \+ *def* ideal.quotient
- \+ *def* ideal.span
- \+ *lemma* ideal.span_eq
- \+ *lemma* ideal.span_eq_bot
- \+ *lemma* ideal.span_le
- \+ *lemma* ideal.span_mono
- \+ *lemma* ideal.span_singleton_eq_bot
- \+ *lemma* ideal.span_singleton_eq_top
- \+ *lemma* ideal.span_singleton_le_span_singleton
- \+ *lemma* ideal.span_singleton_one
- \+ *theorem* ideal.span_singleton_prime
- \+ *lemma* ideal.subset_span
- \+ *def* ideal.zero_ne_one_of_proper
- \- *lemma* is_ideal.mem_trivial
- \- *lemma* is_ideal.mul_left
- \- *lemma* is_ideal.mul_right
- \- *lemma* is_ideal.neg_iff
- \- *def* is_ideal.trivial
- \+ *def* is_local_ring.zero_ne_one
- \+ *def* is_local_ring
- \- *theorem* is_maximal_ideal.mk
- \- *lemma* is_proper_ideal_iff_one_not_mem
- \+ *theorem* local_of_nonunits_ideal
- \- *def* local_of_nonunits_ideal
- \+ *theorem* mem_nonunits_ideal
- \+ *theorem* mem_nonunits_iff
- \- *theorem* mem_or_mem_of_mul_eq_zero
- \+ *theorem* mul_mem_nonunits_left
- \+ *theorem* mul_mem_nonunits_right
- \+/\- *def* nonunits
- \+ *def* nonunits_ideal
- \- *theorem* not_unit_of_mem_proper_ideal
- \+ *theorem* one_not_mem_nonunits
- \- *lemma* quotient_ring.coe_add
- \- *lemma* quotient_ring.coe_mul
- \- *lemma* quotient_ring.coe_neg
- \- *lemma* quotient_ring.coe_one
- \- *lemma* quotient_ring.coe_pow
- \- *lemma* quotient_ring.coe_sub
- \- *lemma* quotient_ring.coe_zero
- \- *lemma* quotient_ring.eq_zero_iff_mem
- \- *lemma* quotient_ring.exists_inv
- \- *def* quotient_ring.mk
- \- *def* quotient_ring.quotient
- \- *def* quotient_ring.quotient_rel
- \+ *theorem* zero_mem_nonunits

Modified ring_theory/localization.lean
- \+/\- *lemma* localization.ne_zero_of_mem_non_zero_divisors

Modified ring_theory/matrix.lean


Modified ring_theory/noetherian.lean
- \- *def* is_fg
- \+/\- *def* is_noetherian
- \+/\- *theorem* is_noetherian_of_quotient_of_noetherian
- \+/\- *theorem* is_noetherian_of_submodule_of_noetherian
- \+/\- *theorem* ring.is_noetherian_of_fintype
- \+/\- *def* submodule.fg

Modified ring_theory/principal_ideal_domain.lean
- \+ *lemma* ideal.is_principal.eq_bot_iff_generator_eq_zero
- \+ *lemma* ideal.is_principal.generator_mem
- \+ *lemma* ideal.is_principal.mem_iff_generator_dvd
- \+ *lemma* ideal.is_principal.span_singleton_generator
- \+ *lemma* is_prime.to_maximal_ideal
- \- *lemma* is_prime_ideal.to_maximal_ideal
- \- *lemma* is_principal_ideal.eq_trivial_iff_generator_eq_zero
- \- *lemma* is_principal_ideal.generator_generates
- \- *lemma* is_principal_ideal.generator_mem
- \- *lemma* is_principal_ideal.mem_iff_generator_dvd
- \+/\- *lemma* mod_mem_iff
- \- *lemma* principal_ideal_domain.is_maximal_ideal_of_irreducible
- \+ *lemma* principal_ideal_domain.is_maximal_of_irreducible

Modified set_theory/cardinal.lean
- \- *theorem* cardinal.mk_empty'
- \+ *theorem* cardinal.mk_emptyc
- \- *theorem* cardinal.mk_plift_false
- \+ *theorem* cardinal.mk_plift_of_false
- \+ *theorem* cardinal.mk_plift_of_true
- \- *theorem* cardinal.mk_plift_true
- \- *theorem* cardinal.mk_union_of_disjiont
- \+ *theorem* cardinal.mk_union_of_disjoint

Modified set_theory/ordinal.lean




## [2018-11-05 10:08:52-05:00](https://github.com/leanprover-community/mathlib/commit/37c0d53)
refactor(field_theory/finite): generalize proofs ([#429](https://github.com/leanprover-community/mathlib/pull/429))
#### Estimated changes
Modified data/equiv/algebra.lean
- \+ *lemma* equiv.coe_units_equiv_ne_zero
- \+ *def* equiv.units_equiv_ne_zero

Modified data/nat/gcd.lean
- \+ *lemma* nat.gcd_gcd_self_left_left
- \+ *lemma* nat.gcd_gcd_self_left_right
- \+ *lemma* nat.gcd_gcd_self_right_left
- \+ *lemma* nat.gcd_gcd_self_right_right
- \+ *lemma* nat.gcd_mul_left_left
- \+ *lemma* nat.gcd_mul_left_right
- \+ *lemma* nat.gcd_mul_right_left
- \+ *lemma* nat.gcd_mul_right_right

Modified data/zmod/quadratic_reciprocity.lean


Modified field_theory/finite.lean
- \+ *lemma* card_nth_roots_subgroup_units
- \- *lemma* coe_units_equiv_ne_zero
- \- *lemma* finite_field.card_nth_roots_units
- \- *lemma* finite_field.card_order_of_eq_totient
- \- *lemma* finite_field.card_pow_eq_one_eq_order_of
- \+/\- *lemma* finite_field.card_units
- \+/\- *lemma* finite_field.prod_univ_units_id_eq_neg_one
- \- *lemma* order_of_pow
- \- *def* units_equiv_ne_zero

Modified group_theory/order_of_element.lean
- \+ *lemma* card_order_of_eq_totient_aux₂
- \+ *lemma* card_pow_eq_one_eq_order_of_aux
- \+ *lemma* is_cyclic.card_order_of_eq_totient
- \+ *lemma* is_cyclic.card_pow_eq_one_le
- \+ *def* is_cyclic.comm_group
- \+ *lemma* is_cyclic_of_card_pow_eq_one_le
- \+ *lemma* order_of_eq_card_of_forall_mem_gpowers
- \- *lemma* order_of_eq_card_of_forall_mem_gppowers
- \+ *lemma* order_of_pow
- \+ *lemma* pow_gcd_card_eq_one_iff



## [2018-11-05 09:56:33-05:00](https://github.com/leanprover-community/mathlib/commit/a64be8d)
feat(category/bifunctor): Bifunctor and bitraversable ([#255](https://github.com/leanprover-community/mathlib/pull/255))
#### Estimated changes
Modified category/applicative.lean


Added category/bifunctor.lean
- \+ *def* bifunctor.bicompl
- \+ *def* bifunctor.bicompr
- \+ *lemma* bifunctor.comp_fst
- \+ *lemma* bifunctor.comp_snd
- \+ *def* bifunctor.fst
- \+ *lemma* bifunctor.fst_snd
- \+ *lemma* bifunctor.id_fst
- \+ *lemma* bifunctor.id_snd
- \+ *def* bifunctor.snd
- \+ *lemma* bifunctor.snd_fst

Added category/bitraversable/basic.lean
- \+ *def* bisequence

Added category/bitraversable/instances.lean
- \+ *def* bicompl.bitraverse
- \+ *def* bicompr.bitraverse
- \+ *def* const.bitraverse
- \+ *def* flip.bitraverse
- \+ *def* prod.bitraverse
- \+ *def* sum.bitraverse

Added category/bitraversable/lemmas.lean
- \+ *lemma* bitraversable.comp_tfst
- \+ *lemma* bitraversable.comp_tsnd
- \+ *lemma* bitraversable.id_tfst
- \+ *lemma* bitraversable.id_tsnd
- \+ *def* bitraversable.tfst
- \+ *lemma* bitraversable.tfst_eq_fst_id
- \+ *lemma* bitraversable.tfst_tsnd
- \+ *def* bitraversable.tsnd
- \+ *lemma* bitraversable.tsnd_eq_snd_id
- \+ *lemma* bitraversable.tsnd_tfst

Modified category/functor.lean
- \+ *def* functor.add_const
- \+ *def* functor.const.mk
- \+ *def* functor.const.run
- \+ *def* functor.const

Modified category/traversable/instances.lean


Modified data/sum.lean
- \- *def* sum.map

Modified tactic/basic.lean




## [2018-11-05 09:50:04-05:00](https://github.com/leanprover-community/mathlib/commit/d556d6a)
refactor(topology/topological_space): rename open_set to opens and unbundle it ([#427](https://github.com/leanprover-community/mathlib/pull/427))
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* topological_space.opens.Sup_s
- \+ *lemma* topological_space.opens.ext
- \+ *def* topological_space.opens.gc
- \+ *def* topological_space.opens.gi
- \+ *def* topological_space.opens.interior
- \+ *def* topological_space.opens.is_basis
- \+ *lemma* topological_space.opens.is_basis_iff_cover
- \+ *lemma* topological_space.opens.is_basis_iff_nbhd
- \+ *def* topological_space.opens

Modified category_theory/examples/topological_spaces.lean
- \+ *def* category_theory.examples.map
- \+ *def* category_theory.examples.map_id
- \+ *lemma* category_theory.examples.map_id_obj
- \+ *def* category_theory.examples.map_iso
- \+ *def* category_theory.examples.map_iso_id
- \+ *def* category_theory.examples.nbhd
- \+ *def* category_theory.examples.nbhds
- \- *def* category_theory.examples.open_set.map
- \- *def* category_theory.examples.open_set.map_id
- \- *lemma* category_theory.examples.open_set.map_id_obj
- \- *def* category_theory.examples.open_set.map_iso
- \- *def* category_theory.examples.open_set.map_iso_id
- \- *def* category_theory.examples.open_set.nbhd
- \- *def* category_theory.examples.open_set.nbhds



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
- \+ *lemma* compact_of_closed
- \+ *lemma* continuous_at_iff_ultrafilter
- \+ *lemma* continuous_iff_ultrafilter
- \+ *lemma* normal_of_compact_t2

Added analysis/topology/stone_cech.lean
- \+ *lemma* continuous_stone_cech_extend
- \+ *lemma* continuous_stone_cech_unit
- \+ *lemma* continuous_ultrafilter_extend
- \+ *lemma* convergent_eqv_pure
- \+ *lemma* dense_embedding_pure
- \+ *def* stone_cech
- \+ *def* stone_cech_extend
- \+ *lemma* stone_cech_extend_extends
- \+ *def* stone_cech_unit
- \+ *lemma* stone_cech_unit_dense
- \+ *def* ultrafilter.extend
- \+ *def* ultrafilter_basis
- \+ *lemma* ultrafilter_basis_is_basis
- \+ *lemma* ultrafilter_comap_pure_nhds
- \+ *lemma* ultrafilter_converges_iff
- \+ *lemma* ultrafilter_extend_eq_iff
- \+ *lemma* ultrafilter_extend_extends
- \+ *lemma* ultrafilter_is_closed_basic
- \+ *lemma* ultrafilter_is_open_basic
- \+ *lemma* ultrafilter_pure_injective

Modified analysis/topology/topological_space.lean
- \+ *lemma* mem_closure_iff_ultrafilter
- \+ *lemma* t2_iff_nhds
- \+ *lemma* t2_iff_ultrafilter

Modified analysis/topology/uniform_space.lean


Modified order/filter.lean
- \+/\- *lemma* filter.exists_ultrafilter
- \+ *lemma* filter.exists_ultrafilter_iff
- \+ *def* filter.is_ultrafilter
- \+/\- *lemma* filter.le_of_ultrafilter
- \+/\- *lemma* filter.mem_of_finite_sUnion_ultrafilter
- \+/\- *lemma* filter.mem_or_compl_mem_of_ultrafilter
- \+/\- *lemma* filter.mem_or_mem_of_ultrafilter
- \+ *lemma* filter.range_mem_map
- \+ *lemma* filter.sup_of_ultrafilters
- \+ *lemma* filter.tendsto_iff_ultrafilter
- \+ *def* filter.ultrafilter.bind
- \+ *lemma* filter.ultrafilter.eq_iff_val_le_val
- \+ *def* filter.ultrafilter.map
- \+ *def* filter.ultrafilter.pure
- \+/\- *def* filter.ultrafilter
- \+ *lemma* filter.ultrafilter_bind
- \+ *lemma* filter.ultrafilter_iff_compl_mem_iff_not_mem
- \+/\- *lemma* filter.ultrafilter_map
- \+/\- *lemma* filter.ultrafilter_of_spec
- \- *lemma* filter.ultrafilter_of_split
- \+/\- *lemma* filter.ultrafilter_of_ultrafilter
- \+/\- *lemma* filter.ultrafilter_pure
- \+/\- *lemma* filter.ultrafilter_ultrafilter_of
- \+/\- *lemma* filter.ultrafilter_unique



## [2018-11-05 09:39:57-05:00](https://github.com/leanprover-community/mathlib/commit/62538c8)
feat(analysis/metric_spaces): Compact and proper spaces ([#430](https://github.com/leanprover-community/mathlib/pull/430))
#### Estimated changes
Modified analysis/metric_space.lean
- \+ *theorem* ball_subset_closed_ball
- \+ *lemma* countable_closure_of_compact
- \+ *lemma* finite_cover_balls_of_compact
- \+ *theorem* mem_closure_iff'
- \+ *lemma* second_countable_of_separable_metric_space

Modified analysis/topology/continuity.lean
- \+ *lemma* compact_univ
- \- *lemma* locally_compact_of_compact

Modified analysis/topology/uniform_space.lean
- \+ *lemma* complete_of_compact_set

Modified data/real/basic.lean
- \+ *lemma* real.le_of_forall_epsilon_le



## [2018-11-05 09:03:45-05:00](https://github.com/leanprover-community/mathlib/commit/47a0a22)
fix(algebra/ordered_group): make instances defeq ([#442](https://github.com/leanprover-community/mathlib/pull/442))
#### Estimated changes
Modified algebra/ordered_group.lean




## [2018-11-05 09:03:15-05:00](https://github.com/leanprover-community/mathlib/commit/8ae3fb8)
feat(ring_theory/subring): ring.closure ([#444](https://github.com/leanprover-community/mathlib/pull/444))
#### Estimated changes
Modified group_theory/subgroup.lean
- \+ *theorem* add_group.in_closure.rec_on

Modified group_theory/submonoid.lean
- \+ *theorem* add_monoid.in_closure.rec_on

Modified ring_theory/subring.lean
- \+ *def* ring.closure
- \+ *theorem* ring.closure_subset
- \+ *theorem* ring.closure_subset_iff
- \+ *theorem* ring.exists_list_of_mem_closure
- \+ *theorem* ring.mem_closure
- \+ *theorem* ring.subset_closure



## [2018-11-05 09:01:57-05:00](https://github.com/leanprover-community/mathlib/commit/849d2a4)
feat(analysis/topology/topological_space): define T0 spaces, T4 spaces, connected and irreducible sets and components ([#448](https://github.com/leanprover-community/mathlib/pull/448))
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+/\- *lemma* closure_singleton
- \+ *def* connected_component
- \+ *theorem* eq_irreducible_component
- \+ *theorem* exists_irreducible
- \+ *theorem* exists_mem_inter
- \+ *theorem* exists_open_singleton_of_fintype
- \+ *def* irreducible_component
- \+ *theorem* irreducible_component_subset_connected_component
- \+ *theorem* irreducible_exists_mem_inter
- \+ *def* is_clopen
- \+ *theorem* is_clopen_compl
- \+ *theorem* is_clopen_compl_iff
- \+ *theorem* is_clopen_diff
- \+ *theorem* is_clopen_empty
- \+ *theorem* is_clopen_iff
- \+ *theorem* is_clopen_inter
- \+ *theorem* is_clopen_union
- \+ *theorem* is_clopen_univ
- \+ *theorem* is_closed_connected_component
- \+/\- *lemma* is_closed_imp
- \+ *theorem* is_closed_irreducible_component
- \+ *def* is_connected
- \+ *theorem* is_connected_closure
- \+ *theorem* is_connected_connected_component
- \+ *theorem* is_connected_empty
- \+ *theorem* is_connected_of_is_irreducible
- \+ *theorem* is_connected_sUnion
- \+ *theorem* is_connected_singleton
- \+ *theorem* is_connected_union
- \+ *def* is_irreducible
- \+ *theorem* is_irreducible_closure
- \+ *theorem* is_irreducible_empty
- \+ *theorem* is_irreducible_irreducible_component
- \+ *theorem* is_irreducible_singleton
- \+ *def* is_totally_disconnected
- \+ *theorem* is_totally_disconnected_empty
- \+ *theorem* is_totally_disconnected_of_is_totally_separated
- \+ *theorem* is_totally_disconnected_singleton
- \+ *def* is_totally_separated
- \+ *theorem* is_totally_separated_empty
- \+ *theorem* is_totally_separated_singleton
- \+ *theorem* mem_connected_component
- \+ *theorem* mem_irreducible_component
- \+ *theorem* normal_separation
- \+ *theorem* subset_connected_component



## [2018-11-05 08:59:28-05:00](https://github.com/leanprover-community/mathlib/commit/8898f0e)
feat(data/real/irrational): add basic irrational facts ([#453](https://github.com/leanprover-community/mathlib/pull/453))
Joint work by Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Kenny Lau, and Chris Hughes
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* int.nat_abs_pow

Added data/int/sqrt.lean
- \+ *theorem* int.exists_mul_self
- \+ *def* int.sqrt
- \+ *theorem* int.sqrt_eq
- \+ *theorem* int.sqrt_nonneg

Modified data/nat/sqrt.lean
- \+ *theorem* nat.exists_mul_self

Modified data/padics/padic_norm.lean


Modified data/rat.lean
- \+ *theorem* rat.abs_def
- \+ *theorem* rat.cast_pow
- \+ *theorem* rat.exists_mul_self
- \+ *theorem* rat.mk_pnat_denom
- \+ *theorem* rat.mk_pnat_num
- \+ *theorem* rat.mul_denom
- \+ *theorem* rat.mul_num
- \+ *theorem* rat.mul_self_denom
- \+ *theorem* rat.mul_self_num
- \+ *def* rat.sqrt
- \+ *theorem* rat.sqrt_eq
- \+ *theorem* rat.sqrt_nonneg

Modified data/real/irrational.lean
- \+ *theorem* irr_add_rat_iff_irr
- \+ *theorem* irr_mul_rat_iff_irr
- \+ *theorem* irr_neg
- \+ *theorem* irr_nrt_of_n_not_dvd_padic_val
- \+ *theorem* irr_nrt_of_notint_nrt
- \+ *theorem* irr_of_irr_mul_self
- \+ *theorem* irr_rat_add_iff_irr
- \+ *theorem* irr_rat_add_of_irr
- \+ *theorem* irr_sqrt_of_padic_val_odd
- \+ *theorem* irr_sqrt_of_prime
- \+ *theorem* irr_sqrt_rat_iff
- \+ *theorem* irr_sqrt_two
- \- *theorem* sqrt_two_irrational



## [2018-11-05 08:57:04-05:00](https://github.com/leanprover-community/mathlib/commit/94b09d6)
refactor(data/real/basic): make real irreducible ([#454](https://github.com/leanprover-community/mathlib/pull/454))
#### Estimated changes
Modified analysis/complex.lean


Modified analysis/limits.lean
- \+/\- *lemma* tendsto_pow_at_top_at_top_of_gt_1_nat

Modified analysis/real.lean


Modified data/complex/basic.lean
- \+/\- *lemma* complex.I_mul_I
- \+/\- *lemma* complex.conj_I
- \+/\- *lemma* complex.conj_neg_I
- \+/\- *lemma* complex.conj_of_real
- \+/\- *lemma* complex.conj_one
- \+/\- *lemma* complex.conj_zero
- \+/\- *lemma* complex.norm_sq_I
- \+/\- *lemma* complex.norm_sq_one
- \+/\- *lemma* complex.norm_sq_zero
- \+/\- *lemma* complex.of_real_add
- \+/\- *lemma* complex.of_real_bit0
- \+/\- *lemma* complex.of_real_bit1
- \+/\- *lemma* complex.of_real_neg
- \+/\- *lemma* complex.of_real_sub

Modified data/complex/exponential.lean


Modified data/padics/hensel.lean


Modified data/real/basic.lean
- \+ *def* real.comm_ring_aux
- \+ *def* real.mk
- \+ *theorem* real.mk_eq
- \+ *theorem* real.mk_eq_mk
- \+ *theorem* real.quotient_mk_eq_mk



## [2018-11-05 08:56:18-05:00](https://github.com/leanprover-community/mathlib/commit/c57a9a6)
fix(category_theory/isomorphism): use `category_theory.inv` in simp lemmas
`category_theory.is_iso.inv` is not the preferred name for this.
#### Estimated changes
Modified category_theory/isomorphism.lean
- \+/\- *def* category_theory.is_iso.hom_inv_id
- \+/\- *def* category_theory.is_iso.inv_hom_id



## [2018-11-05 08:53:41-05:00](https://github.com/leanprover-community/mathlib/commit/354d59e)
feat(data/nat/basic,algebra/ring): adding two lemmas about division ([#385](https://github.com/leanprover-community/mathlib/pull/385))
#### Estimated changes
Modified algebra/ring.lean
- \+ *theorem* dvd_add_left
- \+ *theorem* dvd_add_right

Modified data/nat/basic.lean




## [2018-11-05 13:47:01+01:00](https://github.com/leanprover-community/mathlib/commit/279b9ed)
feat(ring_theory/matrix): add minor, sub_[left|right|up|down], sub_[left|right]_[up][down] ([#389](https://github.com/leanprover-community/mathlib/pull/389))
Also add fin.nat_add.
#### Estimated changes
Modified data/fin.lean
- \+ *def* fin.nat_add

Modified ring_theory/matrix.lean
- \+ *def* matrix.minor
- \+ *def* matrix.sub_down
- \+ *def* matrix.sub_down_left
- \+ *def* matrix.sub_down_right
- \+ *def* matrix.sub_left
- \+ *def* matrix.sub_right
- \+ *def* matrix.sub_up
- \+ *def* matrix.sub_up_left
- \+ *def* matrix.sub_up_right



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
Added docs/extras/casts.md




## [2018-11-05 05:20:29-05:00](https://github.com/leanprover-community/mathlib/commit/072a11e)
feat(data/polynomial): polynomial.comp ([#441](https://github.com/leanprover-community/mathlib/pull/441))
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* polynomial.C_comp
- \+ *lemma* polynomial.C_pow
- \+ *lemma* polynomial.X_comp
- \+ *lemma* polynomial.add_comp
- \+ *def* polynomial.comp
- \+ *lemma* polynomial.comp_C
- \+ *lemma* polynomial.comp_X
- \+ *lemma* polynomial.comp_one
- \+ *lemma* polynomial.comp_zero
- \+/\- *lemma* polynomial.degree_sum_le
- \+ *lemma* polynomial.eval_comp
- \+ *lemma* polynomial.eval₂_comp
- \+ *lemma* polynomial.eval₂_sum
- \+ *lemma* polynomial.mul_comp
- \+ *lemma* polynomial.one_comp
- \+ *lemma* polynomial.zero_comp



## [2018-11-05 05:19:00-05:00](https://github.com/leanprover-community/mathlib/commit/1cadd48)
feat(data/list): mfoldl, mfoldr theorems; reverse_foldl
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.mfoldl_append
- \+ *theorem* list.mfoldl_cons
- \+ *theorem* list.mfoldl_nil
- \+ *theorem* list.mfoldr_append
- \+ *theorem* list.mfoldr_cons
- \+ *theorem* list.mfoldr_nil
- \+ *theorem* list.reverse_foldl



## [2018-11-05 05:07:45-05:00](https://github.com/leanprover-community/mathlib/commit/b934956)
feat(data/int/basic): make coe_nat_le, coe_nat_lt, coe_nat_inj' into simp lemmas
#### Estimated changes
Modified data/int/basic.lean
- \+/\- *theorem* int.coe_nat_inj'
- \+/\- *theorem* int.coe_nat_le
- \+/\- *theorem* int.coe_nat_lt



## [2018-11-05 05:07:04-05:00](https://github.com/leanprover-community/mathlib/commit/f5ce71f)
fix(tactic/eval_expr): often crashes when reflecting expressions ([#358](https://github.com/leanprover-community/mathlib/pull/358))
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/replacer.lean




## [2018-11-05 05:03:22-05:00](https://github.com/leanprover-community/mathlib/commit/f00ed77)
feat(data/complex/basic): I_ne_zero and cast_re, cast_im lemmas
#### Estimated changes
Modified data/complex/basic.lean
- \+ *lemma* complex.I_ne_zero
- \+ *lemma* complex.int_cast_im
- \+ *lemma* complex.int_cast_re
- \+ *lemma* complex.nat_cast_im
- \+ *lemma* complex.nat_cast_re
- \+ *lemma* complex.rat_cast_im
- \+ *lemma* complex.rat_cast_re



## [2018-11-03 20:19:22-04:00](https://github.com/leanprover-community/mathlib/commit/3f5ec68)
fix(*): make three `trans_apply`s rfl-lemmas
#### Estimated changes
Modified data/equiv/basic.lean
- \+/\- *theorem* equiv.trans_apply

Modified order/order_iso.lean
- \+/\- *theorem* order_embedding.trans_apply

Modified set_theory/ordinal.lean
- \+/\- *theorem* initial_seg.trans_apply

