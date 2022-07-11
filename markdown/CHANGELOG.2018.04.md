## [2018-04-29 01:27:12-04:00](https://github.com/leanprover-community/mathlib/commit/a97101d)
fix(docs/naming): use names in use ([#122](https://github.com/leanprover-community/mathlib/pull/122))
#### Estimated changes
Modified docs/naming.md




## [2018-04-26 18:29:10+02:00](https://github.com/leanprover-community/mathlib/commit/48485a2)
refactor(logic/relation,group_theory/free_group): add theory for reflextive/transitive relations & use them for the free group reduction
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* append_eq_has_append
- \+ *lemma* nil_eq_append_iff
- \+ *lemma* append_eq_cons_iff
- \+ *lemma* cons_eq_append_iff
- \+ *lemma* append_eq_append_iff
- \+ *theorem* infix_cons

Modified data/list/perm.lean


Modified group_theory/free_group.lean
- \+ *lemma* red.refl
- \+ *lemma* red.trans
- \+ *lemma* step.bnot_rev
- \+ *lemma* step.cons_bnot
- \+ *lemma* step.cons_bnot_rev
- \+ *lemma* not_step_nil
- \+ *lemma* step.cons_left_iff
- \+ *lemma* not_step_singleton
- \+ *lemma* step.cons_cons_iff
- \+ *lemma* step.append_left_iff
- \+ *lemma* step.to_red
- \+ *lemma* cons_cons
- \+ *lemma* cons_cons_iff
- \+ *lemma* append_append_left_iff
- \+ *lemma* append_append
- \+ *lemma* to_append_iff
- \+ *lemma* one_eq_mk
- \+/\- *lemma* mul_mk
- \+ *lemma* inv_mk
- \- *lemma* list.append_eq_has_append
- \- *lemma* list.infix_cons
- \- *lemma* red.step.bnot_rev
- \- *lemma* red.bnot
- \- *lemma* red.step.cons_bnot
- \- *lemma* red.cons_bnot
- \- *lemma* red.cons_bnot_rev
- \- *lemma* red.cons_iff
- \+ *theorem* step.length
- \+ *theorem* step.append_left
- \+ *theorem* step.cons
- \+ *theorem* step.append_right
- \+ *theorem* step.diamond
- \+/\- *theorem* church_rosser
- \+ *theorem* nil_iff
- \+ *theorem* singleton_iff
- \+ *theorem* cons_nil_iff_singleton
- \+ *theorem* red_iff_irreducible
- \+ *theorem* inv_of_red_of_ne
- \+ *theorem* step.sublist
- \+ *theorem* sublist
- \+ *theorem* sizeof_of_step
- \+ *theorem* length
- \+ *theorem* antisymm
- \+ *theorem* equivalence_join_red
- \+ *theorem* join_red_of_step
- \+ *theorem* eqv_gen_step_iff_join_red
- \+ *theorem* red.exact
- \+/\- *theorem* map.comp
- \+/\- *theorem* to_group_eq_prod_map
- \+/\- *theorem* reduce.not
- \- *theorem* red.trans.aux
- \- *theorem* red.trans
- \- *theorem* red.step.length
- \- *theorem* red.sizeof
- \- *theorem* red.of_step
- \- *theorem* red.step.append_left
- \- *theorem* red.step.append_right
- \- *theorem* red.step.cons
- \- *theorem* red.append
- \- *theorem* red.cons
- \- *theorem* red.of_cons
- \- *theorem* red.length
- \- *theorem* red.antisymm
- \- *theorem* red.step.church_rosser.aux2
- \- *theorem* red.step.church_rosser.aux
- \- *theorem* red.step.church_rosser
- \- *theorem* church_rosser_1
- \- *theorem* red.step.inv
- \- *theorem* red.step.eqv_gen_of_red
- \- *theorem* red.step.exact
- \- *theorem* red.step.sound
- \- *theorem* red.nil.aux
- \- *theorem* red.nil
- \- *theorem* red.singleton.aux
- \- *theorem* red.singleton
- \- *theorem* red.step.sublist
- \- *theorem* red.sublist
- \- *theorem* red.inv_of_red_nil.aux
- \- *theorem* red.inv_of_red_nil
- \- *theorem* red.inv_of_red_of_ne.aux
- \- *theorem* red.inv_of_red_of_ne
- \- *theorem* red.to_group
- \+ *def* red
- \+/\- *def* free_group
- \- *def* inv

Created logic/relation.lean
- \+ *lemma* refl_gen.to_refl_trans_gen
- \+ *lemma* trans
- \+ *lemma* single
- \+ *lemma* head
- \+ *lemma* head_induction_on
- \+ *lemma* trans_induction_on
- \+ *lemma* cases_head
- \+ *lemma* cases_head_iff
- \+ *lemma* cases_tail
- \+ *lemma* cases_tail_iff
- \+ *lemma* refl_trans_gen_iff_eq
- \+ *lemma* refl_trans_gen_lift
- \+ *lemma* refl_trans_gen_mono
- \+ *lemma* refl_trans_gen_refl_trans_gen
- \+ *lemma* reflexive_refl_trans_gen
- \+ *lemma* transitive_refl_trans_gen
- \+ *lemma* church_rosser
- \+ *lemma* join_of_single
- \+ *lemma* symmetric_join
- \+ *lemma* reflexive_join
- \+ *lemma* transitive_join
- \+ *lemma* equivalence_join
- \+ *lemma* equivalence_join_refl_trans_gen
- \+ *lemma* join_of_equivalence
- \+ *lemma* refl_trans_gen_of_transitive_reflexive
- \+ *lemma* refl_trans_gen_of_equivalence
- \+ *lemma* eqv_gen_iff_of_equivalence
- \+ *lemma* eqv_gen_mono
- \+ *def* join



## [2018-04-25 14:35:58+02:00](https://github.com/leanprover-community/mathlib/commit/5df2ee7)
style(group_theory): move free_group from algebra to group_theory
#### Estimated changes
Renamed algebra/free_group.lean to group_theory/free_group.lean
- \+/\- *theorem* red.inv_of_red_of_ne.aux



## [2018-04-25 14:28:21+02:00](https://github.com/leanprover-community/mathlib/commit/716decc)
feat(algebra): add free groups ([#89](https://github.com/leanprover-community/mathlib/pull/89))
#### Estimated changes
Created algebra/free_group.lean
- \+ *lemma* list.append_eq_has_append
- \+ *lemma* list.infix_cons
- \+ *lemma* red.step.bnot_rev
- \+ *lemma* red.bnot
- \+ *lemma* red.step.cons_bnot
- \+ *lemma* red.cons_bnot
- \+ *lemma* red.cons_bnot_rev
- \+ *lemma* red.cons_iff
- \+ *lemma* quot_mk_eq_mk
- \+ *lemma* quot_lift_mk
- \+ *lemma* quot_lift_on_mk
- \+ *lemma* mul_mk
- \+ *lemma* to_group.mk
- \+ *lemma* to_group.of
- \+ *lemma* to_group.mul
- \+ *lemma* to_group.one
- \+ *lemma* to_group.inv
- \+ *lemma* map.mk
- \+ *lemma* map.id
- \+ *lemma* map.id'
- \+ *lemma* map.of
- \+ *lemma* map.mul
- \+ *lemma* map.one
- \+ *lemma* map.inv
- \+ *lemma* prod_mk
- \+ *lemma* prod.of
- \+ *lemma* prod.mul
- \+ *lemma* prod.one
- \+ *lemma* prod.inv
- \+ *lemma* prod.unique
- \+ *lemma* sum_mk
- \+ *lemma* sum.of
- \+ *lemma* sum.sum
- \+ *lemma* sum.one
- \+ *lemma* sum.inv
- \+ *lemma* reduce.cons
- \+ *theorem* red.trans.aux
- \+ *theorem* red.trans
- \+ *theorem* red.step.length
- \+ *theorem* red.sizeof
- \+ *theorem* red.of_step
- \+ *theorem* red.step.append_left
- \+ *theorem* red.step.append_right
- \+ *theorem* red.step.cons
- \+ *theorem* red.append
- \+ *theorem* red.cons
- \+ *theorem* red.of_cons
- \+ *theorem* red.length
- \+ *theorem* red.antisymm
- \+ *theorem* red.step.church_rosser.aux2
- \+ *theorem* red.step.church_rosser.aux
- \+ *theorem* red.step.church_rosser
- \+ *theorem* church_rosser_1
- \+ *theorem* church_rosser
- \+ *theorem* red.step.inv
- \+ *theorem* red.step.eqv_gen_of_red
- \+ *theorem* red.step.exact
- \+ *theorem* red.step.sound
- \+ *theorem* red.nil.aux
- \+ *theorem* red.nil
- \+ *theorem* red.singleton.aux
- \+ *theorem* red.singleton
- \+ *theorem* of.inj
- \+ *theorem* red.step.sublist
- \+ *theorem* red.sublist
- \+ *theorem* red.inv_of_red_nil.aux
- \+ *theorem* red.inv_of_red_nil
- \+ *theorem* red.inv_of_red_of_ne.aux
- \+ *theorem* red.inv_of_red_of_ne
- \+ *theorem* red.step.to_group
- \+ *theorem* red.to_group
- \+ *theorem* to_group.unique
- \+ *theorem* to_group.of_eq
- \+ *theorem* to_group.range_subset
- \+ *theorem* to_group.range_eq_closure
- \+ *theorem* map.comp
- \+ *theorem* map.unique
- \+ *theorem* map_eq_to_group
- \+ *theorem* to_group_eq_prod_map
- \+ *theorem* reduce.red
- \+ *theorem* reduce.not
- \+ *theorem* reduce.min
- \+ *theorem* reduce.idem
- \+ *theorem* reduce.step.eq
- \+ *theorem* reduce.eq_of_red
- \+ *theorem* reduce.sound
- \+ *theorem* reduce.exact
- \+ *theorem* reduce.self
- \+ *theorem* reduce.rev
- \+ *theorem* red.enum.sound
- \+ *theorem* red.enum.complete
- \+ *def* free_group
- \+ *def* mk
- \+ *def* inv
- \+ *def* of
- \+ *def* to_group.aux
- \+ *def* to_group
- \+ *def* map.aux
- \+ *def* map
- \+ *def* free_group_congr
- \+ *def* prod
- \+ *def* sum
- \+ *def* free_group_empty_equiv_unit
- \+ *def* free_group_unit_equiv_int
- \+ *def* reduce
- \+ *def* to_word
- \+ *def* to_word.mk
- \+ *def* to_word.inj
- \+ *def* reduce.church_rosser
- \+ *def* red.enum

Modified group_theory/subgroup.lean




## [2018-04-25 13:44:07+02:00](https://github.com/leanprover-community/mathlib/commit/e6264eb)
feat(order/conditionally_complete_lattice): add instance complete_linear_order -> conditionally_complete_linear_order; add cSup/cInf_interval
#### Estimated changes
Modified order/conditionally_complete_lattice.lean
- \+ *lemma* cInf_interval
- \+ *lemma* cSup_interval



## [2018-04-25 13:06:49+02:00](https://github.com/leanprover-community/mathlib/commit/bf04127)
feat(order): add liminf and limsup over filters (c.f. Sébastien Gouëzel's [#115](https://github.com/leanprover-community/mathlib/pull/115))
#### Estimated changes
Modified analysis/topology/topological_structures.lean
- \+ *lemma* is_bounded_le_nhds
- \+ *lemma* is_bounded_under_le_of_tendsto
- \+ *lemma* is_cobounded_ge_nhds
- \+ *lemma* is_cobounded_under_ge_of_tendsto
- \+ *lemma* is_bounded_ge_nhds
- \+ *lemma* is_bounded_under_ge_of_tendsto
- \+ *lemma* is_cobounded_le_nhds
- \+ *lemma* is_cobounded_under_le_of_tendsto
- \+ *theorem* lt_mem_sets_of_Limsup_lt
- \+ *theorem* gt_mem_sets_of_Liminf_gt
- \+ *theorem* le_nhds_of_Limsup_eq_Liminf
- \+ *theorem* Limsup_nhds
- \+ *theorem* Liminf_nhds
- \+ *theorem* Liminf_eq_of_le_nhds
- \+ *theorem* Limsup_eq_of_le_nhds

Modified logic/basic.lean
- \+ *lemma* exists_true_iff_nonempty

Modified order/conditionally_complete_lattice.lean
- \+ *lemma* cSup_upper_bounds_eq_cInf
- \+ *lemma* cInf_lower_bounds_eq_cSup

Modified order/lattice.lean
- \+ *lemma* forall_le_or_exists_lt_sup
- \+ *lemma* forall_le_or_exists_lt_inf

Created order/liminf_limsup.lean
- \+ *lemma* is_bounded_iff
- \+ *lemma* is_bounded_under_of
- \+ *lemma* is_bounded_bot
- \+ *lemma* is_bounded_top
- \+ *lemma* is_bounded_principal
- \+ *lemma* is_bounded_sup
- \+ *lemma* is_bounded_of_le
- \+ *lemma* is_bounded_under_of_is_bounded
- \+ *lemma* is_cobounded.mk
- \+ *lemma* is_cobounded_of_is_bounded
- \+ *lemma* is_cobounded_bot
- \+ *lemma* is_cobounded_top
- \+ *lemma* is_cobounded_principal
- \+ *lemma* is_cobounded_of_le
- \+ *lemma* is_cobounded_le_of_bot
- \+ *lemma* is_cobounded_ge_of_top
- \+ *lemma* is_bounded_le_of_top
- \+ *lemma* is_bounded_ge_of_bot
- \+ *lemma* is_bounded_under_sup
- \+ *lemma* is_bounded_under_inf
- \+ *lemma* Liminf_le_Liminf
- \+ *lemma* Limsup_le_Limsup
- \+ *lemma* Limsup_le_Limsup_of_le
- \+ *lemma* Liminf_le_Liminf_of_le
- \+ *lemma* limsup_le_limsup
- \+ *lemma* liminf_le_liminf
- \+ *theorem* limsup_eq
- \+ *theorem* liminf_eq
- \+ *theorem* Limsup_le_of_le
- \+ *theorem* le_Liminf_of_le
- \+ *theorem* le_Limsup_of_le
- \+ *theorem* Liminf_le_of_le
- \+ *theorem* Liminf_le_Limsup
- \+ *theorem* Limsup_principal
- \+ *theorem* Liminf_principal
- \+ *theorem* Limsup_bot
- \+ *theorem* Liminf_bot
- \+ *theorem* Limsup_top
- \+ *theorem* Liminf_top
- \+ *theorem* Limsup_eq_infi_Sup
- \+ *theorem* limsup_eq_infi_supr
- \+ *theorem* Liminf_eq_supr_Inf
- \+ *theorem* liminf_eq_supr_infi
- \+ *def* is_bounded
- \+ *def* is_bounded_under
- \+ *def* is_cobounded
- \+ *def* is_cobounded_under
- \+ *def* Limsup
- \+ *def* Liminf
- \+ *def* limsup
- \+ *def* liminf



## [2018-04-24 22:18:49-04:00](https://github.com/leanprover-community/mathlib/commit/78d28c5)
fix(*): update to lean
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* pi_val
- \+/\- *lemma* mem_pi
- \+ *theorem* insert_val_of_not_mem
- \+/\- *def* pi.empty

Modified data/list/basic.lean
- \+/\- *lemma* append_eq_nil

Modified leanpkg.toml


Modified set_theory/zfc.lean
- \+ *theorem* eval_val
- \- *def* eval_val



## [2018-04-24 21:11:29-04:00](https://github.com/leanprover-community/mathlib/commit/44271cf)
feat(tactic/interactive): add `clean` tactic
for removing identity junk and annotations added to terms by common tactics like dsimp
#### Estimated changes
Modified tactic/interactive.lean


Modified tests/tactics.lean




## [2018-04-24 20:17:52-04:00](https://github.com/leanprover-community/mathlib/commit/e4c09d4)
feat(analysis/topology/topological_space): a finite union of compact sets is compact ([#117](https://github.com/leanprover-community/mathlib/pull/117))
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* compact_bUnion_of_compact
- \+ *lemma* compact_of_finite



## [2018-04-24 20:16:10-04:00](https://github.com/leanprover-community/mathlib/commit/e4e4659)
feat(tactic/generalize_hyp): a version of `generalize` that also applies to assumptions ([#110](https://github.com/leanprover-community/mathlib/pull/110))
#### Estimated changes
Modified tactic/interactive.lean
- \+ *lemma* {u}

Modified tests/tactics.lean




## [2018-04-24 17:00:19-04:00](https://github.com/leanprover-community/mathlib/commit/f87135b)
feat(algebra/pi_instances): Adds pi instances for common algebraic structures
#### Estimated changes
Created algebra/pi_instances.lean




## [2018-04-24 15:57:06-04:00](https://github.com/leanprover-community/mathlib/commit/3b73ea1)
feat(tactic/convert): tactic similar to `refine` ([#116](https://github.com/leanprover-community/mathlib/pull/116))
... but which generates equality proof obligations for every discrepancy between the goal and
the type of the rule
#### Estimated changes
Modified tactic/interactive.lean


Renamed tests/wlog.lean to tests/tactics.lean




## [2018-04-24 14:30:20-04:00](https://github.com/leanprover-community/mathlib/commit/7dcd6f5)
feat(tactic/interactive): adding a discharger argument to solve_by_elim ([#108](https://github.com/leanprover-community/mathlib/pull/108))
#### Estimated changes
Modified docs/tactics.md


Modified tactic/interactive.lean




## [2018-04-24 14:26:32-04:00](https://github.com/leanprover-community/mathlib/commit/009968e)
feat(docs/tactic): document congr_n and unfold_coes ([#105](https://github.com/leanprover-community/mathlib/pull/105))
#### Estimated changes
Modified docs/tactics.md




## [2018-04-24 14:25:48-04:00](https://github.com/leanprover-community/mathlib/commit/44391c9)
doc(docs/elan.md): a short setup guide
A short guide on getting started with Lean, mathlib and elan.
Adds a link to docs/elan.md in README.md
#### Estimated changes
Modified README.md


Created docs/elan.md




## [2018-04-24 14:24:59-04:00](https://github.com/leanprover-community/mathlib/commit/23c07fd)
feat(docs/extras/cc) Documents the cc tactic
From explanations and experiments by Simon, Gabriel and Kenny at
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/cc.20is.20so.20powerful
#### Estimated changes
Modified docs/extras.md


Created docs/extras/cc.md




## [2018-04-24 14:22:35-04:00](https://github.com/leanprover-community/mathlib/commit/e2c7421)
feat(tactic/ext): new `ext` tactic and corresponding `extensionality` attribute
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* ext'

Modified data/list/basic.lean


Modified data/multiset.lean
- \+ *theorem* ext'

Modified data/set/basic.lean


Created data/stream/basic.lean


Modified docs/tactics.md


Modified tactic/interactive.lean


Modified tests/examples.lean




## [2018-04-24 14:15:55-04:00](https://github.com/leanprover-community/mathlib/commit/d862939)
fix(tactic/wlog): in the proof of completeness, useful assumptions were not visible
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/interactive.lean


Modified tests/wlog.lean




## [2018-04-19 08:49:27-04:00](https://github.com/leanprover-community/mathlib/commit/c13c5ea)
fix(ordinal): fix looping simp
#### Estimated changes
Modified set_theory/ordinal.lean




## [2018-04-19 07:58:36-04:00](https://github.com/leanprover-community/mathlib/commit/2d935cb)
refactor(lebesgue_measure): clean up proofs
#### Estimated changes
Modified algebra/ordered_group.lean
- \- *lemma* sub_lt_iff
- \- *lemma* lt_sub_iff
- \+ *theorem* lt_sub

Modified algebra/ordered_ring.lean


Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/lebesgue_measure.lean
- \+ *lemma* lebesgue_length_Ico'
- \+/\- *lemma* lebesgue_length_Ico
- \+/\- *lemma* le_lebesgue_length
- \+/\- *lemma* lebesgue_outer_Ico
- \+/\- *lemma* lebesgue_Ico
- \+/\- *lemma* lebesgue_Ioo
- \- *lemma* lebesgue_length_Ico_le_lebesgue_length_Ico

Modified analysis/measure_theory/outer_measure.lean
- \+ *theorem* of_function_le

Modified analysis/topology/topological_structures.lean


Modified data/int/basic.lean


Modified data/set/intervals.lean
- \+ *lemma* Ico_self
- \+ *lemma* Ico_subset_Ico_left
- \+ *lemma* Ico_subset_Ico_right
- \+ *lemma* Ico_subset_Ioo_left
- \+ *lemma* Ioo_subset_Ico_self
- \+ *lemma* Ico_subset_Iio_self
- \+ *lemma* Ioo_self
- \+ *lemma* Ico_sdiff_Ioo_eq_singleton



## [2018-04-19 04:40:28-04:00](https://github.com/leanprover-community/mathlib/commit/7d1ab38)
feat(list/basic,...): minor modifications & additions
based on Zulip conversations and requests
#### Estimated changes
Modified algebra/group.lean


Modified algebra/ring.lean
- \- *def* nonunits

Modified data/list/basic.lean
- \+/\- *theorem* append_inj_left
- \+/\- *theorem* append_inj_right
- \+/\- *theorem* append_inj_left'
- \+/\- *theorem* append_inj_right'
- \+/\- *theorem* append_left_cancel
- \+/\- *theorem* append_right_cancel
- \+ *theorem* append_left_inj
- \+ *theorem* append_right_inj
- \+ *theorem* prefix_append_left_inj
- \+ *theorem* prefix_cons_inj
- \+ *theorem* take_prefix
- \+ *theorem* drop_suffix
- \+ *theorem* prefix_iff_eq_append
- \+ *theorem* suffix_iff_eq_append
- \+ *theorem* prefix_iff_eq_take
- \+ *theorem* suffix_iff_eq_drop

Modified data/set/basic.lean
- \+/\- *theorem* preimage_image_eq
- \+/\- *theorem* image_preimage_eq

Modified logic/basic.lean
- \+ *lemma* not_nonempty_iff_imp_false
- \+/\- *theorem* not_imp_of_and_not
- \+/\- *theorem* not_and_not_right
- \+/\- *theorem* not_and_of_not_or_not
- \+ *theorem* forall_prop_of_true
- \+ *theorem* exists_prop_of_true
- \+ *theorem* forall_prop_of_false
- \+ *theorem* exists_prop_of_false
- \+/\- *def* decidable_of_iff
- \+/\- *def* decidable_of_iff'

Modified ring_theory/ideals.lean
- \+ *def* nonunits



## [2018-04-17 21:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/ed09867)
feat(data/list/basic): prefix_or_prefix
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* nil_prefix
- \+ *theorem* nil_suffix
- \+ *theorem* nil_infix
- \+ *theorem* reverse_suffix
- \+ *theorem* reverse_prefix
- \+ *theorem* prefix_of_prefix_length_le
- \+ *theorem* prefix_or_prefix_of_prefix
- \+ *theorem* suffix_of_suffix_length_le
- \+ *theorem* suffix_or_suffix_of_suffix



## [2018-04-17 01:53:53-04:00](https://github.com/leanprover-community/mathlib/commit/d9daa10)
chore(group_theory): fixups
#### Estimated changes
Modified algebra/group.lean
- \- *theorem* mul
- \- *def* is_group_hom
- \- *def* is_group_anti_hom

Modified group_theory/coset.lean
- \+ *def* left_rel

Modified group_theory/order_of_element.lean


Modified group_theory/subgroup.lean
- \+/\- *lemma* trivial_eq_closure
- \+/\- *lemma* trivial_ker_of_inj
- \+/\- *lemma* inj_iff_trivial_ker

Modified group_theory/submonoid.lean




## [2018-04-16 19:39:05-04:00](https://github.com/leanprover-community/mathlib/commit/4f42fbf)
feat(data/option): more option stuff
#### Estimated changes
Modified algebra/big_operators.lean


Modified algebra/group.lean
- \+/\- *def* is_group_hom

Modified data/list/basic.lean
- \+ *theorem* option.to_list_nodup

Modified data/option.lean
- \- *lemma* mem_def
- \- *lemma* some_inj
- \- *lemma* none_bind
- \- *lemma* some_bind
- \- *lemma* bind_some
- \- *lemma* bind_eq_some
- \- *lemma* map_none
- \- *lemma* map_some
- \- *lemma* map_eq_some
- \- *lemma* map_id'
- \- *lemma* seq_some
- \- *lemma* is_some_iff_exists
- \- *lemma* is_none_iff_eq_none
- \- *lemma* guard_eq_some
- \+ *theorem* mem_def
- \+ *theorem* get_mem
- \+ *theorem* get_of_mem
- \+ *theorem* some_inj
- \+ *theorem* none_bind
- \+ *theorem* some_bind
- \+ *theorem* bind_some
- \+ *theorem* bind_eq_some
- \+ *theorem* map_none
- \+ *theorem* map_some
- \+ *theorem* map_eq_some
- \+ *theorem* map_id'
- \+ *theorem* seq_some
- \+ *theorem* is_some_iff_exists
- \+ *theorem* is_none_iff_eq_none
- \+ *theorem* iget_some
- \+ *theorem* iget_mem
- \+ *theorem* iget_of_mem
- \+ *theorem* guard_eq_some
- \+ *theorem* mem_to_list



## [2018-04-16 19:01:44-04:00](https://github.com/leanprover-community/mathlib/commit/d5c73c0)
chore(*): trailing spaces
#### Estimated changes
Modified algebra/archimedean.lean
- \+/\- *lemma* pow_unbounded_of_gt_one

Modified algebra/euclidean_domain.lean
- \+/\- *lemma* mod_zero
- \+/\- *lemma* mod_one
- \+/\- *theorem* gcd_zero_left
- \+/\- *theorem* gcd_one_left

Modified algebra/ordered_group.lean


Modified algebra/ring.lean


Modified analysis/metric_space.lean


Modified data/int/modeq.lean
- \+/\- *theorem* modeq_neg

Modified data/nat/choose.lean
- \+/\- *lemma* choose_succ_self

Modified data/nat/prime.lean
- \+/\- *lemma* prod_factors
- \+/\- *lemma* mem_list_primes_of_dvd_prod

Modified data/num/basic.lean


Modified data/real/cau_seq.lean


Modified data/seq/wseq.lean


Modified data/set/function.lean


Modified logic/function.lean
- \+/\- *lemma* hfunext

Modified order/galois_connection.lean


Modified order/order_iso.lean


Modified set_theory/cofinality.lean
- \+/\- *theorem* cof_zero
- \+/\- *theorem* cof_eq_zero
- \+/\- *theorem* cof_succ
- \+/\- *theorem* cof_eq_one_iff_is_succ

Modified set_theory/ordinal_notation.lean
- \+/\- *theorem* split_eq_scale_split'

Modified tactic/alias.lean


Modified tactic/norm_num.lean


Modified tactic/ring.lean


Modified tests/examples.lean




## [2018-04-16 19:00:13-04:00](https://github.com/leanprover-community/mathlib/commit/b7db508)
feat(analysis/topology/topological_space): basis elements are open
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* is_open_of_is_topological_basis
- \+ *lemma* mem_basis_subset_of_mem_open



## [2018-04-16 19:00:13-04:00](https://github.com/leanprover-community/mathlib/commit/6dd2bc0)
feat(data/option): more option decidability
#### Estimated changes
Modified data/bool.lean
- \+ *lemma* not_ff

Modified data/option.lean
- \+ *lemma* is_none_iff_eq_none
- \+/\- *def* to_list

Modified logic/basic.lean
- \+ *def* decidable_of_bool



## [2018-04-16 20:29:17+02:00](https://github.com/leanprover-community/mathlib/commit/f2361dc)
fix(group_theory/coset): left_cosets.left_cosets -> left_cosets.eq_class_eq_left_coset is now a theorem
#### Estimated changes
Modified group_theory/coset.lean
- \+ *lemma* eq_class_eq_left_coset
- \- *def* left_cosets.left_coset



## [2018-04-16 20:09:50+02:00](https://github.com/leanprover-community/mathlib/commit/910de7e)
refactor(group_theory/coset): left_cosets is now a quotient ([#103](https://github.com/leanprover-community/mathlib/pull/103))
#### Estimated changes
Modified data/equiv.lean
- \+ *def* equiv_fib

Modified group_theory/coset.lean
- \- *lemma* subgroup_mem_left_cosets
- \- *lemma* left_cosets_disjoint
- \- *lemma* pairwise_left_cosets_disjoint
- \- *lemma* left_cosets_equiv_subgroup
- \- *lemma* Union_left_cosets_eq_univ
- \- *lemma* group_equiv_left_cosets_times_subgroup
- \+/\- *def* left_cosets
- \+ *def* left_cosets.left_coset
- \+ *def* left_coset_equiv_subgroup

Modified group_theory/order_of_element.lean




## [2018-04-15 17:58:13+02:00](https://github.com/leanprover-community/mathlib/commit/479a122)
doc(doc): add topological space doc ([#101](https://github.com/leanprover-community/mathlib/pull/101))
#### Estimated changes
Created docs/theories/topological_spaces.md
- \+ *lemma* is_open_Union
- \+ *lemma* is_open_union
- \+ *lemma* tendsto_nhds_unique
- \+ *def* compact



## [2018-04-15 17:41:57+02:00](https://github.com/leanprover-community/mathlib/commit/c34f202)
Adding some notes on calc
#### Estimated changes
Modified docs/extras.md


Created docs/extras/calc.md
- \+ *lemma* lt_of_lt_of_le
- \+ *lemma* lt_trans
- \+ *theorem* r_trans
- \+ *theorem* T2
- \+ *theorem* rst_trans



## [2018-04-15 17:39:03+02:00](https://github.com/leanprover-community/mathlib/commit/21d5618)
feat(docs/styles): Some more indentation guidelines ([#95](https://github.com/leanprover-community/mathlib/pull/95))
Fixed also a typo pointed out by Scott
#### Estimated changes
Modified docs/style.md
- \+ *lemma* div_self
- \+ *lemma* nhds_supr
- \+ *lemma* mem_nhds_of_is_topological_basis
- \+ *theorem* sub_eq_zero_iff_le



## [2018-04-15 17:36:59+02:00](https://github.com/leanprover-community/mathlib/commit/f1179bd)
feat(algebra/big_operators): update prod_bij_ne_one ([#100](https://github.com/leanprover-community/mathlib/pull/100))
#### Estimated changes
Modified algebra/big_operators.lean


Modified linear_algebra/basic.lean




## [2018-04-13 19:25:49+02:00](https://github.com/leanprover-community/mathlib/commit/5605233)
feat(algebra/big_operators): add prod_sum (equating the product over a sum to the sum of all combinations)
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* prod_sum

Modified data/finset.lean
- \+ *lemma* attach_insert
- \+ *lemma* pi.cons_same
- \+ *lemma* pi.cons_ne
- \+ *lemma* injective_pi_cons
- \+ *lemma* pi_empty
- \+ *lemma* pi_insert
- \+ *theorem* attach_empty
- \+ *def* pi.empty
- \+ *def* pi.cons

Modified data/multiset.lean
- \+ *lemma* map_singleton
- \+ *lemma* prod_bind
- \+ *lemma* pmap_zero
- \+ *lemma* pmap_cons
- \+ *lemma* disjoint_map_map
- \+ *lemma* pairwise_coe_iff_pairwise
- \+ *lemma* pairwise_of_nodup
- \+ *lemma* nodup_bind
- \+ *lemma* attach_ndinsert
- \+ *lemma* injective_pi_cons
- \+ *lemma* nodup_pi
- \+ *theorem* map_id
- \+ *def* pairwise



## [2018-04-11 17:11:19+02:00](https://github.com/leanprover-community/mathlib/commit/f1e46e1)
fix(.travis.yml): fix some elan
#### Estimated changes
Modified .travis.yml




## [2018-04-11 16:41:07+02:00](https://github.com/leanprover-community/mathlib/commit/b13f404)
chore(.travis.yml): show some elan
#### Estimated changes
Modified .travis.yml




## [2018-04-11 15:17:30+02:00](https://github.com/leanprover-community/mathlib/commit/5f360e3)
feat(group_theory): add group.closure, the subgroup generated by a set
#### Estimated changes
Modified group_theory/subgroup.lean
- \+ *lemma* mem_gpowers
- \+ *lemma* mem_closure
- \+ *lemma* trivial_eq_closure
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* gpowers_eq_closure
- \+ *def* closure

Modified group_theory/submonoid.lean




## [2018-04-11 14:49:46+02:00](https://github.com/leanprover-community/mathlib/commit/fea2491)
chore(group_theory): move order_of into its own file; base costes on left_coset
#### Estimated changes
Modified group_theory/coset.lean
- \+/\- *lemma* mem_left_coset
- \+/\- *lemma* mem_right_coset
- \+/\- *lemma* left_coset_equiv_rel
- \+/\- *lemma* left_coset_assoc
- \+/\- *lemma* right_coset_assoc
- \+/\- *lemma* left_coset_right_coset
- \+/\- *lemma* mem_own_left_coset
- \+/\- *lemma* mem_own_right_coset
- \+/\- *lemma* mem_left_coset_left_coset
- \+/\- *lemma* mem_right_coset_right_coset
- \+/\- *lemma* mem_left_coset_iff
- \+/\- *lemma* mem_right_coset_iff
- \+/\- *lemma* left_coset_mem_left_coset
- \+/\- *lemma* right_coset_mem_right_coset
- \+ *lemma* subgroup_mem_left_cosets
- \+ *lemma* left_cosets_disjoint
- \+ *lemma* pairwise_left_cosets_disjoint
- \+ *lemma* left_cosets_equiv_subgroup
- \+ *lemma* Union_left_cosets_eq_univ
- \+ *lemma* group_equiv_left_cosets_times_subgroup
- \+/\- *theorem* normal_of_eq_cosets
- \+/\- *def* left_coset
- \+/\- *def* right_coset
- \+/\- *def* left_coset_equiv
- \+ *def* left_cosets

Created group_theory/order_of_element.lean
- \+ *lemma* mem_range_iff_mem_finset_range_of_mod_eq
- \+ *lemma* exists_gpow_eq_one
- \+ *lemma* exists_pow_eq_one
- \+ *lemma* pow_order_of_eq_one
- \+ *lemma* order_of_ne_zero
- \+ *lemma* pow_injective_of_lt_order_of
- \+ *lemma* order_of_le_card_univ
- \+ *lemma* pow_eq_mod_order_of
- \+ *lemma* gpow_eq_mod_order_of
- \+ *lemma* mem_range_gpow_iff_mem_range_order_of
- \+ *lemma* order_eq_card_range_gpow
- \+ *lemma* order_of_dvd_card_univ
- \+ *def* order_of

Modified group_theory/subgroup.lean
- \+/\- *lemma* injective_mul
- \- *lemma* mem_range_iff_mem_finset_range_of_mod_eq
- \- *lemma* mul_image
- \- *lemma* subgroup_mem_cosets
- \- *lemma* cosets_disjoint
- \- *lemma* pairwise_cosets_disjoint
- \- *lemma* cosets_equiv_subgroup
- \- *lemma* Union_cosets_eq_univ
- \- *lemma* group_equiv_cosets_times_subgroup
- \- *lemma* exists_gpow_eq_one
- \- *lemma* exists_pow_eq_one
- \- *lemma* pow_order_of_eq_one
- \- *lemma* order_of_ne_zero
- \- *lemma* pow_injective_of_lt_order_of
- \- *lemma* order_of_le_card_univ
- \- *lemma* pow_eq_mod_order_of
- \- *lemma* gpow_eq_mod_order_of
- \- *lemma* mem_range_gpow_iff_mem_range_order_of
- \- *lemma* order_eq_card_range_gpow
- \- *lemma* order_of_dvd_card_univ
- \- *def* cosets
- \- *def* order_of



## [2018-04-11 13:50:33+02:00](https://github.com/leanprover-community/mathlib/commit/d2ab199)
chore(group_theory): simplify proofs; generalize some theorems
#### Estimated changes
Modified group_theory/coset.lean
- \+/\- *lemma* left_coset_assoc
- \+/\- *lemma* right_coset_assoc
- \+/\- *lemma* left_coset_right_coset
- \+/\- *lemma* one_left_coset
- \+ *lemma* right_coset_one
- \+ *lemma* mem_left_coset_iff
- \+ *lemma* mem_right_coset_iff
- \+/\- *lemma* left_coset_mem_left_coset
- \+/\- *lemma* right_coset_mem_right_coset
- \- *lemma* one_right_coset
- \- *lemma* mem_mem_left_coset
- \+/\- *theorem* normal_of_eq_cosets
- \+/\- *theorem* eq_cosets_of_normal

Modified group_theory/subgroup.lean
- \+/\- *lemma* mem_norm_comm
- \+ *lemma* mem_norm_comm_iff
- \+ *lemma* mem_trivial
- \+ *lemma* mem_center
- \+ *lemma* mem_ker
- \+/\- *lemma* one_ker_inv
- \+/\- *lemma* inv_iff_ker
- \+ *lemma* inj_of_trivial_ker
- \+ *lemma* trivial_ker_of_inj
- \+ *lemma* inj_iff_trivial_ker
- \- *lemma* eq_one_of_trivial_mem
- \- *lemma* trivial_mem_of_eq_one
- \- *lemma* mem_ker_one
- \- *lemma* ker_inv
- \- *lemma* inv_ker
- \- *lemma* inj_of_trivial_kernel
- \- *lemma* trivial_kernel_of_inj
- \- *lemma* inj_iff_trivial_kernel
- \+ *def* ker
- \- *def* kernel



## [2018-04-11 10:25:21+02:00](https://github.com/leanprover-community/mathlib/commit/ea0fb11)
style(group_theory): try to follow conventions (calc indentation, lowercase names, ...)
#### Estimated changes
Modified group_theory/coset.lean
- \+/\- *lemma* mem_left_coset
- \+/\- *lemma* mem_right_coset
- \+/\- *lemma* left_coset_equiv_rel
- \+/\- *lemma* left_coset_assoc
- \+/\- *lemma* right_coset_assoc
- \+/\- *lemma* left_coset_right_coset
- \+/\- *lemma* left_coset_mem_left_coset
- \+/\- *lemma* right_coset_mem_right_coset
- \+/\- *lemma* one_left_coset
- \+/\- *lemma* one_right_coset
- \+/\- *lemma* mem_own_left_coset
- \+/\- *lemma* mem_own_right_coset
- \+/\- *lemma* mem_left_coset_left_coset
- \+/\- *lemma* mem_right_coset_right_coset
- \+/\- *lemma* mem_mem_left_coset
- \+/\- *theorem* normal_of_eq_cosets
- \+/\- *theorem* eq_cosets_of_normal
- \+/\- *theorem* normal_iff_eq_cosets
- \+/\- *def* left_coset
- \+/\- *def* right_coset
- \+/\- *def* left_coset_equiv

Modified group_theory/subgroup.lean
- \+/\- *lemma* injective_mul
- \+/\- *lemma* mem_norm_comm
- \+/\- *lemma* eq_one_of_trivial_mem
- \+/\- *lemma* trivial_mem_of_eq_one
- \+/\- *lemma* mem_ker_one
- \+/\- *lemma* one_ker_inv
- \+/\- *lemma* inv_ker_one
- \+/\- *lemma* ker_inv
- \+/\- *lemma* inv_ker
- \+/\- *lemma* one_iff_ker_inv
- \+/\- *lemma* inv_iff_ker
- \+/\- *lemma* inj_of_trivial_kernel
- \+/\- *lemma* trivial_kernel_of_inj
- \+/\- *lemma* inj_iff_trivial_kernel
- \+/\- *def* cosets
- \+/\- *def* trivial
- \+/\- *def* center
- \+/\- *def* kernel



## [2018-04-11 10:24:33+02:00](https://github.com/leanprover-community/mathlib/commit/fa86d34)
feat(group_theory): add left/right cosets and normal subgroups
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *theorem* is_group_hom.prod
- \+/\- *theorem* is_group_anti_hom.prod

Modified algebra/group.lean
- \+/\- *theorem* mul
- \+/\- *theorem* inv
- \+/\- *def* is_group_hom

Created group_theory/coset.lean
- \+ *lemma* mem_left_coset
- \+ *lemma* mem_right_coset
- \+ *lemma* left_coset_equiv_rel
- \+ *lemma* left_coset_assoc
- \+ *lemma* right_coset_assoc
- \+ *lemma* left_coset_right_coset
- \+ *lemma* left_coset_mem_left_coset
- \+ *lemma* right_coset_mem_right_coset
- \+ *lemma* one_left_coset
- \+ *lemma* one_right_coset
- \+ *lemma* mem_own_left_coset
- \+ *lemma* mem_own_right_coset
- \+ *lemma* mem_left_coset_left_coset
- \+ *lemma* mem_right_coset_right_coset
- \+ *lemma* mem_mem_left_coset
- \+ *theorem* normal_of_eq_cosets
- \+ *theorem* eq_cosets_of_normal
- \+ *theorem* normal_iff_eq_cosets
- \+ *def* left_coset
- \+ *def* right_coset
- \+ *def* left_coset_equiv

Modified group_theory/subgroup.lean
- \+ *lemma* mem_norm_comm
- \+ *lemma* eq_one_of_trivial_mem
- \+ *lemma* trivial_mem_of_eq_one
- \+ *lemma* mem_ker_one
- \+ *lemma* one_ker_inv
- \+ *lemma* inv_ker_one
- \+ *lemma* ker_inv
- \+ *lemma* inv_ker
- \+ *lemma* one_iff_ker_inv
- \+ *lemma* inv_iff_ker
- \+ *lemma* inj_of_trivial_kernel
- \+ *lemma* trivial_kernel_of_inj
- \+ *lemma* inj_iff_trivial_kernel
- \+ *def* trivial
- \+ *def* center
- \+ *def* kernel



## [2018-04-10 14:38:56+02:00](https://github.com/leanprover-community/mathlib/commit/f85330a)
feat(group_theory/submonoid): relate monoid closure to list product
#### Estimated changes
Modified group_theory/submonoid.lean
- \+/\- *lemma* is_submonoid.pow_mem
- \+ *lemma* is_submonoid.power_subset
- \+ *lemma* is_submonoid.list_prod_mem
- \+ *theorem* exists_list_of_mem_closure



## [2018-04-10 13:58:37+02:00](https://github.com/leanprover-community/mathlib/commit/4a15503)
refactor(ring_theory): unify monoid closure in ring theory with the one in group theory
#### Estimated changes
Modified group_theory/submonoid.lean
- \- *lemma* is_submonoid_closure
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset

Modified ring_theory/localization.lean
- \- *theorem* subset_closure
- \- *def* closure



## [2018-04-10 13:13:52+02:00](https://github.com/leanprover-community/mathlib/commit/ec18563)
feat(group_theory): add subtype instanes for group and monoid; monoid closure
#### Estimated changes
Modified group_theory/subgroup.lean


Modified group_theory/submonoid.lean
- \+ *lemma* is_submonoid_closure
- \+ *def* closure



## [2018-04-10 13:02:43+02:00](https://github.com/leanprover-community/mathlib/commit/88960f0)
refactor(algebra): move is_submonoid to group_theory and base is_subgroup on is_submonoid
#### Estimated changes
Modified algebra/group.lean
- \+/\- *theorem* inv_is_group_anti_hom
- \+/\- *def* is_group_hom
- \+/\- *def* is_group_anti_hom

Modified algebra/group_power.lean
- \- *def* powers

Modified data/list/basic.lean


Modified group_theory/subgroup.lean
- \+ *lemma* is_subgroup.gpow_mem
- \+/\- *lemma* inv_mem_iff
- \+ *lemma* mul_mem_cancel_left
- \+ *lemma* mul_mem_cancel_right
- \+/\- *lemma* mul_image
- \+/\- *lemma* subgroup_mem_cosets
- \+/\- *lemma* cosets_disjoint
- \- *lemma* inv_mem
- \- *lemma* mul_mem
- \- *lemma* is_subgroup_range_gpow
- \+ *theorem* is_subgroup.of_div
- \+ *def* gpowers
- \+/\- *def* cosets

Created group_theory/submonoid.lean
- \+ *lemma* is_submonoid.pow_mem
- \+ *def* powers

Modified ring_theory/localization.lean




## [2018-04-09 14:39:12-04:00](https://github.com/leanprover-community/mathlib/commit/bd0a555)
fix(algebra/group_power): remove has_smul
This was causing notation overload problems with module smul
#### Estimated changes
Modified algebra/archimedean.lean


Modified algebra/group_power.lean
- \+/\- *theorem* add_monoid.mul_smul'
- \+/\- *theorem* add_monoid.smul_add
- \+/\- *theorem* add_monoid.neg_smul
- \+/\- *theorem* add_monoid.smul_neg_comm
- \+/\- *theorem* gpow_coe_nat
- \+/\- *theorem* gsmul_coe_nat
- \+/\- *theorem* gpow_of_nat
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* gpow_neg_succ
- \+/\- *theorem* gsmul_neg_succ
- \+/\- *theorem* gsmul_add_comm
- \+/\- *theorem* gsmul_eq_mul
- \+/\- *theorem* gsmul_eq_mul'
- \+/\- *theorem* mul_gsmul_left
- \+/\- *theorem* mul_gsmul_assoc
- \+/\- *theorem* add_monoid.smul_nonneg

Modified data/multiset.lean




## [2018-04-09 11:32:20+02:00](https://github.com/leanprover-community/mathlib/commit/b02733d)
fix(data/finset): change argument order of finset.induction(_on) so that the induction tactic accepts them
#### Estimated changes
Modified data/finset.lean




## [2018-04-09 10:30:13+02:00](https://github.com/leanprover-community/mathlib/commit/018cfdd)
feat(linear_algebra/multivariate_polynomial): make theory computational
#### Estimated changes
Modified linear_algebra/multivariate_polynomial.lean
- \+/\- *lemma* finset.bind_singleton2
- \+/\- *lemma* finsupp.single_induction_on



## [2018-04-08 01:00:54-04:00](https://github.com/leanprover-community/mathlib/commit/2bd5e21)
feat(data/int/modeq): Modular arithmetic for integers
#### Estimated changes
Created data/int/modeq.lean
- \+ *lemma* coe_nat_modeq_iff
- \+ *theorem* modeq_zero_iff
- \+ *theorem* modeq_iff_dvd
- \+ *theorem* modeq_of_dvd_of_modeq
- \+ *theorem* modeq_mul_left'
- \+ *theorem* modeq_mul_right'
- \+ *theorem* modeq_add
- \+ *theorem* modeq_add_cancel_left
- \+ *theorem* modeq_add_cancel_right
- \+ *theorem* modeq_neg
- \+ *theorem* modeq_sub
- \+ *theorem* modeq_mul_left
- \+ *theorem* modeq_mul_right
- \+ *theorem* modeq_mul
- \+ *def* modeq



## [2018-04-08 00:45:25-04:00](https://github.com/leanprover-community/mathlib/commit/6815830)
chore(measure_theory/measure_space): add coe_fn instance
#### Estimated changes
Modified analysis/measure_theory/lebesgue_measure.lean
- \+/\- *lemma* lebesgue_Ico
- \+/\- *lemma* lebesgue_Ioo
- \+/\- *lemma* lebesgue_singleton

Modified analysis/measure_theory/measure_space.lean
- \+/\- *lemma* measure_space_eq
- \+/\- *lemma* measure_empty
- \+/\- *lemma* measure_mono
- \+/\- *lemma* measure_Union_le_tsum_nat



## [2018-04-08 00:35:55-04:00](https://github.com/leanprover-community/mathlib/commit/03d5bd9)
fix(*): update to lean
#### Estimated changes
Modified .travis.yml


Modified algebra/group_power.lean
- \+/\- *lemma* pow_abs
- \+/\- *lemma* pow_inv
- \+/\- *theorem* mul_pow
- \+/\- *theorem* inv_pow
- \+/\- *theorem* pow_inv_comm
- \+/\- *theorem* inv_gpow
- \+/\- *theorem* one_div_pow
- \+/\- *theorem* division_ring.inv_pow
- \+/\- *theorem* div_pow
- \+/\- *def* powers

Modified analysis/limits.lean


Modified analysis/measure_theory/outer_measure.lean


Modified data/int/basic.lean
- \+/\- *lemma* shiftl_eq_mul_pow
- \+/\- *lemma* shiftr_eq_div_pow

Modified data/nat/sqrt.lean


Modified data/pnat.lean
- \+/\- *theorem* pow_coe

Modified group_theory/subgroup.lean
- \+/\- *lemma* is_subgroup_range_gpow
- \+/\- *lemma* exists_pow_eq_one
- \+/\- *lemma* pow_order_of_eq_one
- \+/\- *lemma* pow_eq_mod_order_of
- \+/\- *lemma* order_eq_card_range_gpow

Modified leanpkg.toml


Modified linear_algebra/multivariate_polynomial.lean


Modified number_theory/pell.lean


Modified set_theory/cardinal.lean
- \+/\- *theorem* nat_cast_pow

Modified set_theory/cofinality.lean


Modified set_theory/ordinal.lean
- \+/\- *theorem* nat_cast_power
- \+/\- *theorem* mul_omega_power_power

Modified set_theory/ordinal_notation.lean
- \+ *theorem* power_def
- \+/\- *theorem* repr_power

Modified tactic/ring.lean
- \+/\- *theorem* pow_add_rev
- \+/\- *theorem* pow_add_rev_right



## [2018-04-07 22:38:50-04:00](https://github.com/leanprover-community/mathlib/commit/e9b9014)
feat(data/erased): VM-erased data type
#### Estimated changes
Created data/erased.lean
- \+ *theorem* out_proof
- \+ *theorem* out_mk
- \+ *theorem* mk_out
- \+ *theorem* nonempty_iff
- \+ *theorem* bind_eq_out
- \+ *theorem* join_eq_out
- \+ *def* erased
- \+ *def* mk
- \+ *def* out_type
- \+ *def* choice
- \+ *def* bind
- \+ *def* join

Modified data/set/basic.lean
- \+/\- *theorem* mem_singleton_iff



## [2018-04-05 01:29:34-04:00](https://github.com/leanprover-community/mathlib/commit/22e671c)
fix(travis.yml): fix travis setup for new nightlies
#### Estimated changes
Modified .travis.yml


Modified leanpkg.toml




## [2018-04-05 01:05:02-04:00](https://github.com/leanprover-community/mathlib/commit/81264ec)
fix(leanpkg.toml): remove lean_version
I will keep marking the nightly version here, but I will leave it commented out until I can figure out how to make travis work with it
#### Estimated changes
Modified leanpkg.toml




## [2018-04-05 00:59:52-04:00](https://github.com/leanprover-community/mathlib/commit/08f19fd)
chore(data/nat/prime): style and minor modifications
#### Estimated changes
Modified data/nat/prime.lean
- \+/\- *lemma* perm_of_prod_eq_prod
- \+ *theorem* factors_lemma



## [2018-04-05 00:35:23-04:00](https://github.com/leanprover-community/mathlib/commit/efa4f92)
feat(data/nat/prime): lemmas about nat.factors
#### Estimated changes
Modified data/nat/prime.lean
- \+ *lemma* mem_factors
- \+ *lemma* prod_factors
- \+ *lemma* mem_list_primes_of_dvd_prod
- \+ *lemma* mem_factors_of_dvd
- \+ *lemma* perm_of_prod_eq_prod
- \+ *lemma* factors_unique



## [2018-04-05 00:22:45-04:00](https://github.com/leanprover-community/mathlib/commit/2d370e9)
feat(algebra/euclidean_domain): euclidean domains / euclidean algorithm
#### Estimated changes
Created algebra/euclidean_domain.lean
- \+ *lemma* gcd_decreasing
- \+ *lemma* mod_zero
- \+ *lemma* dvd_mod_self
- \+ *lemma* mod_lt
- \+ *lemma* neq_zero_lt_mod_lt
- \+ *lemma* dvd_mod
- \+ *lemma* val_lt_one
- \+ *lemma* val_dvd_le
- \+ *lemma* mod_one
- \+ *lemma* zero_mod
- \+ *lemma* zero_div
- \+ *lemma* mod_self
- \+ *lemma* div_self
- \+ *theorem* gcd_zero_left
- \+ *theorem* gcd.induction
- \+ *theorem* gcd_dvd
- \+ *theorem* gcd_dvd_left
- \+ *theorem* gcd_dvd_right
- \+ *theorem* dvd_gcd
- \+ *theorem* gcd_zero_right
- \+ *theorem* gcd_one_left
- \+ *theorem* gcd_next
- \+ *theorem* gcd_self
- \+ *def* gcd



## [2018-04-05 00:16:34-04:00](https://github.com/leanprover-community/mathlib/commit/467f60f)
feat(data/nat/basic): add div_le_div_right
Based on [#91](https://github.com/leanprover-community/mathlib/pull/91) by @MonoidMusician
#### Estimated changes
Modified data/nat/basic.lean




## [2018-04-05 00:13:56-04:00](https://github.com/leanprover-community/mathlib/commit/47f1384)
doc(docs/extras): Adding notes on simp
#### Estimated changes
Created docs/extras/simp.md
- \+ *lemma* my_lemma
- \+ *theorem* cong_refl
- \+ *theorem* ne_zero



## [2018-04-05 00:12:09-04:00](https://github.com/leanprover-community/mathlib/commit/73d481a)
adding explanation of "change"
#### Estimated changes
Modified docs/extras/conv.md




## [2018-04-05 00:07:53-04:00](https://github.com/leanprover-community/mathlib/commit/c87f1e6)
fix(*): finish lean update
#### Estimated changes
Modified data/pnat.lean
- \+ *theorem* pow_coe
- \+/\- *def* pow

Modified leanpkg.toml


Modified set_theory/ordinal_notation.lean


Modified tactic/norm_num.lean


Modified tests/norm_num.lean




## [2018-04-03 21:23:26-04:00](https://github.com/leanprover-community/mathlib/commit/5717986)
fix(*): update to lean
also add mathlib nightly version to leanpkg.toml
#### Estimated changes
Modified algebra/archimedean.lean


Modified algebra/big_operators.lean
- \+/\- *lemma* prod_const_one
- \+ *lemma* sum_const_zero

Modified algebra/group.lean
- \+ *def* additive
- \+ *def* multiplicative

Modified algebra/group_power.lean
- \+/\- *lemma* pow_abs
- \+/\- *theorem* pow_zero
- \+/\- *theorem* add_monoid.zero_smul
- \+ *theorem* succ_smul
- \+/\- *theorem* add_monoid.one_smul
- \+ *theorem* smul_add_comm'
- \+ *theorem* succ_smul'
- \+ *theorem* two_smul
- \+/\- *theorem* add_monoid.add_smul
- \+ *theorem* add_monoid.smul_zero
- \+ *theorem* add_monoid.mul_smul'
- \+ *theorem* pow_mul'
- \+ *theorem* add_monoid.mul_smul
- \+/\- *theorem* add_monoid.smul_one
- \+ *theorem* bit0_smul
- \+ *theorem* bit1_smul
- \+/\- *theorem* pow_mul_comm
- \+ *theorem* smul_add_comm
- \+/\- *theorem* list.sum_repeat
- \+/\- *theorem* nat.pow_eq_pow
- \+ *theorem* add_monoid.smul_add
- \+/\- *theorem* add_monoid.neg_smul
- \+ *theorem* add_monoid.smul_sub
- \+ *theorem* add_monoid.smul_neg_comm
- \+/\- *theorem* gpow_coe_nat
- \+ *theorem* gsmul_coe_nat
- \+ *theorem* gpow_of_nat
- \+ *theorem* gsmul_of_nat
- \+ *theorem* gpow_neg_succ
- \+ *theorem* gsmul_neg_succ
- \+/\- *theorem* gpow_zero
- \+ *theorem* zero_gsmul
- \+/\- *theorem* gpow_one
- \+ *theorem* one_gsmul
- \+/\- *theorem* one_gpow
- \+/\- *theorem* gpow_neg
- \+ *theorem* neg_gsmul
- \+/\- *theorem* gpow_neg_one
- \+ *theorem* neg_one_gsmul
- \+/\- *theorem* inv_gpow
- \+/\- *theorem* gpow_add
- \+ *theorem* add_gsmul
- \+/\- *theorem* gpow_mul_comm
- \+ *theorem* gsmul_add_comm
- \+/\- *theorem* gpow_mul
- \+ *theorem* gsmul_mul'
- \+ *theorem* gpow_mul'
- \+/\- *theorem* gsmul_mul
- \+/\- *theorem* gpow_bit0
- \+ *theorem* bit0_gsmul
- \+/\- *theorem* gpow_bit1
- \+ *theorem* bit1_gsmul
- \+/\- *theorem* add_monoid.smul_eq_mul'
- \+/\- *theorem* add_monoid.smul_eq_mul
- \+ *theorem* add_monoid.mul_smul_left
- \+/\- *theorem* add_monoid.mul_smul_assoc
- \+/\- *theorem* gsmul_eq_mul
- \+/\- *theorem* gsmul_eq_mul'
- \+ *theorem* mul_gsmul_left
- \+/\- *theorem* mul_gsmul_assoc
- \+/\- *theorem* add_monoid.smul_nonneg
- \- *theorem* smul_succ
- \- *theorem* smul_succ'
- \- *theorem* smul_two
- \- *theorem* add_monoid.smul_mul
- \- *theorem* smul_bit1
- \- *theorem* gsmul_one
- \- *theorem* gsmul_neg
- \- *theorem* gsmul_neg_one
- \- *theorem* gsmul_bit1
- \- *theorem* add_monoid.mul_smul_right
- \- *theorem* mul_gsmul_right
- \+ *def* add_monoid.smul
- \+/\- *def* gpow
- \+ *def* gsmul

Modified analysis/limits.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/topological_space.lean


Modified data/int/basic.lean
- \+/\- *lemma* shiftl_eq_mul_pow
- \+/\- *lemma* shiftr_eq_div_pow

Modified data/multiset.lean
- \+ *lemma* sum_map_sum_map
- \+/\- *theorem* prod_repeat
- \+ *theorem* sum_repeat
- \+/\- *theorem* count_smul

Modified data/nat/sqrt.lean


Modified data/real/basic.lean


Modified data/set/lattice.lean
- \- *lemma* subset.antisymm_iff

Modified group_theory/subgroup.lean
- \+/\- *lemma* is_subgroup_range_gpow
- \+/\- *lemma* exists_gpow_eq_one
- \+/\- *lemma* exists_pow_eq_one
- \+/\- *lemma* pow_order_of_eq_one
- \+/\- *lemma* pow_eq_mod_order_of
- \+/\- *lemma* gpow_eq_mod_order_of
- \+/\- *lemma* order_eq_card_range_gpow

Modified leanpkg.toml


Modified linear_algebra/multivariate_polynomial.lean


Modified number_theory/pell.lean


Modified ring_theory/localization.lean


Modified set_theory/cardinal.lean
- \+/\- *theorem* nat_cast_pow

Modified set_theory/ordinal.lean
- \+/\- *theorem* nat_cast_power

Modified tactic/norm_num.lean


Modified tactic/ring.lean


Modified tests/norm_num.lean




## [2018-04-01 22:10:37-04:00](https://github.com/leanprover-community/mathlib/commit/777f6b4)
feat(data/set/basic): add some more set lemmas
#### Estimated changes
Modified data/analysis/filter.lean


Modified data/set/basic.lean
- \+ *theorem* subset.antisymm_iff
- \+/\- *theorem* subset_empty_iff
- \+/\- *theorem* eq_empty_of_subset_empty
- \+/\- *theorem* exists_mem_of_ne_empty
- \+/\- *theorem* mem_univ
- \+ *theorem* univ_subset_iff
- \+/\- *theorem* eq_univ_of_univ_subset
- \+/\- *theorem* union_compl_self
- \+/\- *theorem* compl_union_self
- \+ *theorem* compl_subset_comm
- \+ *theorem* compl_subset_iff_union
- \+ *theorem* subset_compl_comm
- \+ *theorem* subset_compl_iff_disjoint
- \+/\- *theorem* image_empty
- \+/\- *theorem* image_inter
- \+ *theorem* image_univ_of_surjective
- \+ *theorem* mem_compl_image
- \+ *theorem* image_compl_subset
- \+ *theorem* subset_image_compl
- \+ *theorem* image_compl_eq
- \- *theorem* mem_univ_iff
- \- *theorem* mem_univ_eq
- \- *theorem* compl_subset_of_compl_subset
- \- *theorem* mem_image_compl



## [2018-04-01 21:30:17-04:00](https://github.com/leanprover-community/mathlib/commit/d80ca59)
feat(data/fin): add fz/fs recursor for fin
#### Estimated changes
Modified data/fin.lean
- \+ *theorem* fin.succ_rec_on_zero
- \+ *theorem* fin.succ_rec_on_succ
- \+ *def* fin.succ_rec
- \+ *def* fin.succ_rec_on

