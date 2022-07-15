## [2018-04-29 01:27:12-04:00](https://github.com/leanprover-community/mathlib/commit/a97101d)
fix(docs/naming): use names in use ([#122](https://github.com/leanprover-community/mathlib/pull/122))
#### Estimated changes
Modified docs/naming.md




## [2018-04-26 18:29:10+02:00](https://github.com/leanprover-community/mathlib/commit/48485a2)
refactor(logic/relation,group_theory/free_group): add theory for reflextive/transitive relations & use them for the free group reduction
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* list.append_eq_append_iff
- \+ *lemma* list.append_eq_cons_iff
- \+ *lemma* list.append_eq_has_append
- \+ *lemma* list.cons_eq_append_iff
- \+ *theorem* list.infix_cons
- \+ *lemma* list.nil_eq_append_iff

Modified data/list/perm.lean


Modified group_theory/free_group.lean
- \- *theorem* free_group.church_rosser
- \- *theorem* free_group.church_rosser_1
- \+ *theorem* free_group.equivalence_join_red
- \+ *theorem* free_group.eqv_gen_step_iff_join_red
- \- *def* free_group.inv
- \+ *lemma* free_group.inv_mk
- \+ *theorem* free_group.join_red_of_step
- \+/\- *theorem* free_group.map.comp
- \+ *lemma* free_group.one_eq_mk
- \+/\- *theorem* free_group.red.antisymm
- \- *theorem* free_group.red.append
- \+ *lemma* free_group.red.append_append
- \+ *lemma* free_group.red.append_append_left_iff
- \- *lemma* free_group.red.bnot
- \+ *theorem* free_group.red.church_rosser
- \- *theorem* free_group.red.cons
- \- *lemma* free_group.red.cons_bnot
- \- *lemma* free_group.red.cons_bnot_rev
- \+ *lemma* free_group.red.cons_cons
- \+ *lemma* free_group.red.cons_cons_iff
- \- *lemma* free_group.red.cons_iff
- \+ *theorem* free_group.red.cons_nil_iff_singleton
- \+ *theorem* free_group.red.exact
- \- *theorem* free_group.red.inv_of_red_nil.aux
- \- *theorem* free_group.red.inv_of_red_nil
- \- *theorem* free_group.red.inv_of_red_of_ne.aux
- \+/\- *theorem* free_group.red.inv_of_red_of_ne
- \+/\- *theorem* free_group.red.length
- \- *theorem* free_group.red.nil.aux
- \- *theorem* free_group.red.nil
- \+ *theorem* free_group.red.nil_iff
- \+ *lemma* free_group.red.not_step_nil
- \+ *lemma* free_group.red.not_step_singleton
- \- *theorem* free_group.red.of_cons
- \- *theorem* free_group.red.of_step
- \+ *theorem* free_group.red.red_iff_irreducible
- \+ *lemma* free_group.red.refl
- \- *theorem* free_group.red.singleton.aux
- \- *theorem* free_group.red.singleton
- \+ *theorem* free_group.red.singleton_iff
- \- *theorem* free_group.red.sizeof
- \+ *theorem* free_group.red.sizeof_of_step
- \+/\- *theorem* free_group.red.step.append_left
- \+ *lemma* free_group.red.step.append_left_iff
- \+/\- *theorem* free_group.red.step.append_right
- \+/\- *lemma* free_group.red.step.bnot_rev
- \- *theorem* free_group.red.step.church_rosser.aux2
- \- *theorem* free_group.red.step.church_rosser.aux
- \- *theorem* free_group.red.step.church_rosser
- \+/\- *theorem* free_group.red.step.cons
- \+/\- *lemma* free_group.red.step.cons_bnot
- \+ *lemma* free_group.red.step.cons_bnot_rev
- \+ *lemma* free_group.red.step.cons_cons_iff
- \+ *lemma* free_group.red.step.cons_left_iff
- \+ *theorem* free_group.red.step.diamond
- \- *theorem* free_group.red.step.eqv_gen_of_red
- \- *theorem* free_group.red.step.exact
- \- *theorem* free_group.red.step.inv
- \+/\- *theorem* free_group.red.step.length
- \- *theorem* free_group.red.step.sound
- \+/\- *theorem* free_group.red.step.sublist
- \+ *lemma* free_group.red.step.to_red
- \+/\- *theorem* free_group.red.sublist
- \+ *lemma* free_group.red.to_append_iff
- \- *theorem* free_group.red.to_group
- \- *theorem* free_group.red.trans.aux
- \+ *lemma* free_group.red.trans
- \- *theorem* free_group.red.trans
- \+ *def* free_group.red
- \- *inductive* free_group.red
- \+/\- *theorem* free_group.reduce.not
- \+/\- *theorem* free_group.to_group_eq_prod_map
- \+/\- *def* free_group
- \- *lemma* list.append_eq_has_append
- \- *lemma* list.infix_cons

Added logic/relation.lean
- \+ *lemma* relation.church_rosser
- \+ *lemma* relation.equivalence_join
- \+ *lemma* relation.equivalence_join_refl_trans_gen
- \+ *lemma* relation.eqv_gen_iff_of_equivalence
- \+ *lemma* relation.eqv_gen_mono
- \+ *def* relation.join
- \+ *lemma* relation.join_of_equivalence
- \+ *lemma* relation.join_of_single
- \+ *lemma* relation.refl_gen.to_refl_trans_gen
- \+ *inductive* relation.refl_gen
- \+ *lemma* relation.refl_trans_gen.cases_head
- \+ *lemma* relation.refl_trans_gen.cases_head_iff
- \+ *lemma* relation.refl_trans_gen.cases_tail
- \+ *lemma* relation.refl_trans_gen.cases_tail_iff
- \+ *lemma* relation.refl_trans_gen.head
- \+ *lemma* relation.refl_trans_gen.head_induction_on
- \+ *lemma* relation.refl_trans_gen.single
- \+ *lemma* relation.refl_trans_gen.trans
- \+ *lemma* relation.refl_trans_gen.trans_induction_on
- \+ *inductive* relation.refl_trans_gen
- \+ *lemma* relation.refl_trans_gen_iff_eq
- \+ *lemma* relation.refl_trans_gen_lift
- \+ *lemma* relation.refl_trans_gen_mono
- \+ *lemma* relation.refl_trans_gen_of_equivalence
- \+ *lemma* relation.refl_trans_gen_of_transitive_reflexive
- \+ *lemma* relation.refl_trans_gen_refl_trans_gen
- \+ *lemma* relation.reflexive_join
- \+ *lemma* relation.reflexive_refl_trans_gen
- \+ *lemma* relation.symmetric_join
- \+ *lemma* relation.transitive_join
- \+ *lemma* relation.transitive_refl_trans_gen



## [2018-04-25 14:35:58+02:00](https://github.com/leanprover-community/mathlib/commit/5df2ee7)
style(group_theory): move free_group from algebra to group_theory
#### Estimated changes
Renamed algebra/free_group.lean to group_theory/free_group.lean
- \+/\- *theorem* free_group.red.inv_of_red_of_ne.aux



## [2018-04-25 14:28:21+02:00](https://github.com/leanprover-community/mathlib/commit/716decc)
feat(algebra): add free groups ([#89](https://github.com/leanprover-community/mathlib/pull/89))
#### Estimated changes
Added algebra/free_group.lean
- \+ *theorem* free_group.church_rosser
- \+ *theorem* free_group.church_rosser_1
- \+ *def* free_group.free_group_congr
- \+ *def* free_group.free_group_empty_equiv_unit
- \+ *def* free_group.free_group_unit_equiv_int
- \+ *def* free_group.inv
- \+ *def* free_group.map.aux
- \+ *theorem* free_group.map.comp
- \+ *lemma* free_group.map.id'
- \+ *lemma* free_group.map.id
- \+ *lemma* free_group.map.inv
- \+ *lemma* free_group.map.mk
- \+ *lemma* free_group.map.mul
- \+ *lemma* free_group.map.of
- \+ *lemma* free_group.map.one
- \+ *theorem* free_group.map.unique
- \+ *def* free_group.map
- \+ *theorem* free_group.map_eq_to_group
- \+ *def* free_group.mk
- \+ *lemma* free_group.mul_mk
- \+ *theorem* free_group.of.inj
- \+ *def* free_group.of
- \+ *lemma* free_group.prod.inv
- \+ *lemma* free_group.prod.mul
- \+ *lemma* free_group.prod.of
- \+ *lemma* free_group.prod.one
- \+ *lemma* free_group.prod.unique
- \+ *def* free_group.prod
- \+ *lemma* free_group.prod_mk
- \+ *lemma* free_group.quot_lift_mk
- \+ *lemma* free_group.quot_lift_on_mk
- \+ *lemma* free_group.quot_mk_eq_mk
- \+ *theorem* free_group.red.antisymm
- \+ *theorem* free_group.red.append
- \+ *lemma* free_group.red.bnot
- \+ *theorem* free_group.red.cons
- \+ *lemma* free_group.red.cons_bnot
- \+ *lemma* free_group.red.cons_bnot_rev
- \+ *lemma* free_group.red.cons_iff
- \+ *theorem* free_group.red.enum.complete
- \+ *theorem* free_group.red.enum.sound
- \+ *def* free_group.red.enum
- \+ *theorem* free_group.red.inv_of_red_nil.aux
- \+ *theorem* free_group.red.inv_of_red_nil
- \+ *theorem* free_group.red.inv_of_red_of_ne.aux
- \+ *theorem* free_group.red.inv_of_red_of_ne
- \+ *theorem* free_group.red.length
- \+ *theorem* free_group.red.nil.aux
- \+ *theorem* free_group.red.nil
- \+ *theorem* free_group.red.of_cons
- \+ *theorem* free_group.red.of_step
- \+ *theorem* free_group.red.singleton.aux
- \+ *theorem* free_group.red.singleton
- \+ *theorem* free_group.red.sizeof
- \+ *theorem* free_group.red.step.append_left
- \+ *theorem* free_group.red.step.append_right
- \+ *lemma* free_group.red.step.bnot_rev
- \+ *theorem* free_group.red.step.church_rosser.aux2
- \+ *theorem* free_group.red.step.church_rosser.aux
- \+ *theorem* free_group.red.step.church_rosser
- \+ *theorem* free_group.red.step.cons
- \+ *lemma* free_group.red.step.cons_bnot
- \+ *theorem* free_group.red.step.eqv_gen_of_red
- \+ *theorem* free_group.red.step.exact
- \+ *theorem* free_group.red.step.inv
- \+ *theorem* free_group.red.step.length
- \+ *theorem* free_group.red.step.sound
- \+ *theorem* free_group.red.step.sublist
- \+ *theorem* free_group.red.step.to_group
- \+ *inductive* free_group.red.step
- \+ *theorem* free_group.red.sublist
- \+ *theorem* free_group.red.to_group
- \+ *theorem* free_group.red.trans.aux
- \+ *theorem* free_group.red.trans
- \+ *inductive* free_group.red
- \+ *def* free_group.reduce.church_rosser
- \+ *lemma* free_group.reduce.cons
- \+ *theorem* free_group.reduce.eq_of_red
- \+ *theorem* free_group.reduce.exact
- \+ *theorem* free_group.reduce.idem
- \+ *theorem* free_group.reduce.min
- \+ *theorem* free_group.reduce.not
- \+ *theorem* free_group.reduce.red
- \+ *theorem* free_group.reduce.rev
- \+ *theorem* free_group.reduce.self
- \+ *theorem* free_group.reduce.sound
- \+ *theorem* free_group.reduce.step.eq
- \+ *def* free_group.reduce
- \+ *lemma* free_group.sum.inv
- \+ *lemma* free_group.sum.of
- \+ *lemma* free_group.sum.one
- \+ *lemma* free_group.sum.sum
- \+ *def* free_group.sum
- \+ *lemma* free_group.sum_mk
- \+ *def* free_group.to_group.aux
- \+ *lemma* free_group.to_group.inv
- \+ *lemma* free_group.to_group.mk
- \+ *lemma* free_group.to_group.mul
- \+ *lemma* free_group.to_group.of
- \+ *theorem* free_group.to_group.of_eq
- \+ *lemma* free_group.to_group.one
- \+ *theorem* free_group.to_group.range_eq_closure
- \+ *theorem* free_group.to_group.range_subset
- \+ *theorem* free_group.to_group.unique
- \+ *def* free_group.to_group
- \+ *theorem* free_group.to_group_eq_prod_map
- \+ *def* free_group.to_word.inj
- \+ *def* free_group.to_word.mk
- \+ *def* free_group.to_word
- \+ *def* free_group
- \+ *lemma* list.append_eq_has_append
- \+ *lemma* list.infix_cons

Modified group_theory/subgroup.lean




## [2018-04-25 13:44:07+02:00](https://github.com/leanprover-community/mathlib/commit/e6264eb)
feat(order/conditionally_complete_lattice): add instance complete_linear_order -> conditionally_complete_linear_order; add cSup/cInf_interval
#### Estimated changes
Modified order/conditionally_complete_lattice.lean
- \+ *lemma* lattice.cInf_interval
- \+ *lemma* lattice.cSup_interval



## [2018-04-25 13:06:49+02:00](https://github.com/leanprover-community/mathlib/commit/bf04127)
feat(order): add liminf and limsup over filters (c.f. Sébastien Gouëzel's [#115](https://github.com/leanprover-community/mathlib/pull/115))
#### Estimated changes
Modified analysis/topology/topological_structures.lean
- \+ *theorem* Liminf_eq_of_le_nhds
- \+ *theorem* Liminf_nhds
- \+ *theorem* Limsup_eq_of_le_nhds
- \+ *theorem* Limsup_nhds
- \+ *theorem* gt_mem_sets_of_Liminf_gt
- \+ *lemma* is_bounded_ge_nhds
- \+ *lemma* is_bounded_le_nhds
- \+ *lemma* is_bounded_under_ge_of_tendsto
- \+ *lemma* is_bounded_under_le_of_tendsto
- \+ *lemma* is_cobounded_ge_nhds
- \+ *lemma* is_cobounded_le_nhds
- \+ *lemma* is_cobounded_under_ge_of_tendsto
- \+ *lemma* is_cobounded_under_le_of_tendsto
- \+ *theorem* le_nhds_of_Limsup_eq_Liminf
- \+ *theorem* lt_mem_sets_of_Limsup_lt

Modified logic/basic.lean
- \+ *lemma* exists_true_iff_nonempty

Modified order/conditionally_complete_lattice.lean
- \+ *lemma* lattice.cInf_lower_bounds_eq_cSup
- \+ *lemma* lattice.cSup_upper_bounds_eq_cInf

Modified order/lattice.lean
- \+ *lemma* lattice.forall_le_or_exists_lt_inf
- \+ *lemma* lattice.forall_le_or_exists_lt_sup

Added order/liminf_limsup.lean
- \+ *def* filter.Liminf
- \+ *theorem* filter.Liminf_bot
- \+ *theorem* filter.Liminf_eq_supr_Inf
- \+ *lemma* filter.Liminf_le_Liminf
- \+ *lemma* filter.Liminf_le_Liminf_of_le
- \+ *theorem* filter.Liminf_le_Limsup
- \+ *theorem* filter.Liminf_le_of_le
- \+ *theorem* filter.Liminf_principal
- \+ *theorem* filter.Liminf_top
- \+ *def* filter.Limsup
- \+ *theorem* filter.Limsup_bot
- \+ *theorem* filter.Limsup_eq_infi_Sup
- \+ *lemma* filter.Limsup_le_Limsup
- \+ *lemma* filter.Limsup_le_Limsup_of_le
- \+ *theorem* filter.Limsup_le_of_le
- \+ *theorem* filter.Limsup_principal
- \+ *theorem* filter.Limsup_top
- \+ *def* filter.is_bounded
- \+ *lemma* filter.is_bounded_bot
- \+ *lemma* filter.is_bounded_ge_of_bot
- \+ *lemma* filter.is_bounded_iff
- \+ *lemma* filter.is_bounded_le_of_top
- \+ *lemma* filter.is_bounded_of_le
- \+ *lemma* filter.is_bounded_principal
- \+ *lemma* filter.is_bounded_sup
- \+ *lemma* filter.is_bounded_top
- \+ *def* filter.is_bounded_under
- \+ *lemma* filter.is_bounded_under_inf
- \+ *lemma* filter.is_bounded_under_of
- \+ *lemma* filter.is_bounded_under_of_is_bounded
- \+ *lemma* filter.is_bounded_under_sup
- \+ *lemma* filter.is_cobounded.mk
- \+ *def* filter.is_cobounded
- \+ *lemma* filter.is_cobounded_bot
- \+ *lemma* filter.is_cobounded_ge_of_top
- \+ *lemma* filter.is_cobounded_le_of_bot
- \+ *lemma* filter.is_cobounded_of_is_bounded
- \+ *lemma* filter.is_cobounded_of_le
- \+ *lemma* filter.is_cobounded_principal
- \+ *lemma* filter.is_cobounded_top
- \+ *def* filter.is_cobounded_under
- \+ *theorem* filter.le_Liminf_of_le
- \+ *theorem* filter.le_Limsup_of_le
- \+ *def* filter.liminf
- \+ *theorem* filter.liminf_eq
- \+ *theorem* filter.liminf_eq_supr_infi
- \+ *lemma* filter.liminf_le_liminf
- \+ *def* filter.limsup
- \+ *theorem* filter.limsup_eq
- \+ *theorem* filter.limsup_eq_infi_supr
- \+ *lemma* filter.limsup_le_limsup



## [2018-04-24 22:18:49-04:00](https://github.com/leanprover-community/mathlib/commit/78d28c5)
fix(*): update to lean
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* finset.insert_val_of_not_mem
- \+/\- *lemma* finset.mem_pi
- \+/\- *def* finset.pi.empty
- \+ *lemma* finset.pi_val

Modified data/list/basic.lean
- \+/\- *lemma* list.append_eq_nil

Modified leanpkg.toml


Modified set_theory/zfc.lean
- \+ *theorem* pSet.resp.eval_val
- \- *def* pSet.resp.eval_val



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
- \+ *lemma* tactic.interactive.{u}

Modified tests/tactics.lean




## [2018-04-24 17:00:19-04:00](https://github.com/leanprover-community/mathlib/commit/f87135b)
feat(algebra/pi_instances): Adds pi instances for common algebraic structures
#### Estimated changes
Added algebra/pi_instances.lean




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


Added docs/elan.md




## [2018-04-24 14:24:59-04:00](https://github.com/leanprover-community/mathlib/commit/23c07fd)
feat(docs/extras/cc) Documents the cc tactic
From explanations and experiments by Simon, Gabriel and Kenny at
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/cc.20is.20so.20powerful
#### Estimated changes
Modified docs/extras.md


Added docs/extras/cc.md




## [2018-04-24 14:22:35-04:00](https://github.com/leanprover-community/mathlib/commit/e2c7421)
feat(tactic/ext): new `ext` tactic and corresponding `extensionality` attribute
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* finset.ext'

Modified data/list/basic.lean


Modified data/multiset.lean
- \+ *theorem* multiset.ext'

Modified data/set/basic.lean


Added data/stream/basic.lean


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
- \+ *theorem* lt_sub
- \- *lemma* lt_sub_iff
- \- *lemma* sub_lt_iff

Modified algebra/ordered_ring.lean


Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/lebesgue_measure.lean
- \+/\- *lemma* measure_theory.le_lebesgue_length
- \+/\- *lemma* measure_theory.lebesgue_Ico
- \+/\- *lemma* measure_theory.lebesgue_Ioo
- \+ *lemma* measure_theory.lebesgue_length_Ico'
- \+/\- *lemma* measure_theory.lebesgue_length_Ico
- \- *lemma* measure_theory.lebesgue_length_Ico_le_lebesgue_length_Ico
- \+/\- *lemma* measure_theory.lebesgue_outer_Ico

Modified analysis/measure_theory/outer_measure.lean
- \+ *theorem* measure_theory.outer_measure.of_function_le

Modified analysis/topology/topological_structures.lean


Modified data/int/basic.lean


Modified data/set/intervals.lean
- \+ *lemma* set.Ico_sdiff_Ioo_eq_singleton
- \+ *lemma* set.Ico_self
- \+ *lemma* set.Ico_subset_Ico_left
- \+ *lemma* set.Ico_subset_Ico_right
- \+ *lemma* set.Ico_subset_Iio_self
- \+ *lemma* set.Ico_subset_Ioo_left
- \+ *lemma* set.Ioo_self
- \+ *lemma* set.Ioo_subset_Ico_self



## [2018-04-19 04:40:28-04:00](https://github.com/leanprover-community/mathlib/commit/7d1ab38)
feat(list/basic,...): minor modifications & additions
based on Zulip conversations and requests
#### Estimated changes
Modified algebra/group.lean


Modified algebra/ring.lean
- \- *def* nonunits

Modified data/list/basic.lean
- \+/\- *theorem* list.append_inj_left'
- \+/\- *theorem* list.append_inj_left
- \+/\- *theorem* list.append_inj_right'
- \+/\- *theorem* list.append_inj_right
- \+/\- *theorem* list.append_left_cancel
- \+ *theorem* list.append_left_inj
- \+/\- *theorem* list.append_right_cancel
- \+ *theorem* list.append_right_inj
- \+ *theorem* list.drop_suffix
- \+ *theorem* list.prefix_append_left_inj
- \+ *theorem* list.prefix_cons_inj
- \+ *theorem* list.prefix_iff_eq_append
- \+ *theorem* list.prefix_iff_eq_take
- \+ *theorem* list.suffix_iff_eq_append
- \+ *theorem* list.suffix_iff_eq_drop
- \+ *theorem* list.take_prefix

Modified data/set/basic.lean
- \+/\- *theorem* set.image_preimage_eq
- \+/\- *theorem* set.preimage_image_eq

Modified logic/basic.lean
- \+/\- *def* decidable_of_iff'
- \+/\- *def* decidable_of_iff
- \+ *theorem* exists_prop_of_false
- \+ *theorem* exists_prop_of_true
- \+ *theorem* forall_prop_of_false
- \+ *theorem* forall_prop_of_true
- \+/\- *theorem* not_and_not_right
- \+/\- *theorem* not_and_of_not_or_not
- \+/\- *theorem* not_imp_of_and_not
- \+ *lemma* not_nonempty_iff_imp_false

Modified ring_theory/ideals.lean
- \+ *def* nonunits



## [2018-04-17 21:08:42-04:00](https://github.com/leanprover-community/mathlib/commit/ed09867)
feat(data/list/basic): prefix_or_prefix
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.nil_infix
- \+ *theorem* list.nil_prefix
- \+ *theorem* list.nil_suffix
- \+ *theorem* list.prefix_of_prefix_length_le
- \+ *theorem* list.prefix_or_prefix_of_prefix
- \+ *theorem* list.reverse_prefix
- \+ *theorem* list.reverse_suffix
- \+ *theorem* list.suffix_of_suffix_length_le
- \+ *theorem* list.suffix_or_suffix_of_suffix



## [2018-04-17 01:53:53-04:00](https://github.com/leanprover-community/mathlib/commit/d9daa10)
chore(group_theory): fixups
#### Estimated changes
Modified algebra/group.lean
- \- *theorem* is_group_anti_hom.mul
- \- *def* is_group_anti_hom
- \- *theorem* is_group_hom.mul
- \- *def* is_group_hom

Modified group_theory/coset.lean
- \+ *def* left_rel

Modified group_theory/order_of_element.lean


Modified group_theory/subgroup.lean
- \+/\- *lemma* is_group_hom.inj_iff_trivial_ker
- \+/\- *lemma* is_group_hom.trivial_ker_of_inj
- \+/\- *lemma* is_subgroup.trivial_eq_closure

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
- \+ *theorem* option.bind_eq_some
- \- *lemma* option.bind_eq_some
- \+ *theorem* option.bind_some
- \- *lemma* option.bind_some
- \+ *theorem* option.get_mem
- \+ *theorem* option.get_of_mem
- \+ *theorem* option.guard_eq_some
- \- *lemma* option.guard_eq_some
- \+ *theorem* option.iget_mem
- \+ *theorem* option.iget_of_mem
- \+ *theorem* option.iget_some
- \+ *theorem* option.is_none_iff_eq_none
- \- *lemma* option.is_none_iff_eq_none
- \+ *theorem* option.is_some_iff_exists
- \- *lemma* option.is_some_iff_exists
- \+ *theorem* option.map_eq_some
- \- *lemma* option.map_eq_some
- \+ *theorem* option.map_id'
- \- *lemma* option.map_id'
- \+ *theorem* option.map_none
- \- *lemma* option.map_none
- \+ *theorem* option.map_some
- \- *lemma* option.map_some
- \+ *theorem* option.mem_def
- \- *lemma* option.mem_def
- \+ *theorem* option.mem_to_list
- \+ *theorem* option.none_bind
- \- *lemma* option.none_bind
- \+ *theorem* option.seq_some
- \- *lemma* option.seq_some
- \+ *theorem* option.some_bind
- \- *lemma* option.some_bind
- \+ *theorem* option.some_inj
- \- *lemma* option.some_inj



## [2018-04-16 19:01:44-04:00](https://github.com/leanprover-community/mathlib/commit/d5c73c0)
chore(*): trailing spaces
#### Estimated changes
Modified algebra/archimedean.lean
- \+/\- *lemma* pow_unbounded_of_gt_one

Modified algebra/euclidean_domain.lean
- \+/\- *theorem* euclidean_domain.gcd_one_left
- \+/\- *theorem* euclidean_domain.gcd_zero_left
- \+/\- *lemma* euclidean_domain.mod_one
- \+/\- *lemma* euclidean_domain.mod_zero

Modified algebra/ordered_group.lean


Modified algebra/ring.lean


Modified analysis/metric_space.lean


Modified data/int/modeq.lean
- \+/\- *theorem* int.modeq.modeq_neg

Modified data/nat/choose.lean
- \+/\- *lemma* choose_succ_self

Modified data/nat/prime.lean
- \+/\- *lemma* nat.mem_list_primes_of_dvd_prod
- \+/\- *lemma* nat.prod_factors

Modified data/num/basic.lean


Modified data/real/cau_seq.lean


Modified data/seq/wseq.lean


Modified data/set/function.lean


Modified logic/function.lean
- \+/\- *lemma* function.hfunext

Modified order/galois_connection.lean


Modified order/order_iso.lean


Modified set_theory/cofinality.lean
- \+/\- *theorem* ordinal.cof_eq_one_iff_is_succ
- \+/\- *theorem* ordinal.cof_eq_zero
- \+/\- *theorem* ordinal.cof_succ
- \+/\- *theorem* ordinal.cof_zero

Modified set_theory/ordinal_notation.lean
- \+/\- *theorem* onote.split_eq_scale_split'

Modified tactic/alias.lean


Modified tactic/norm_num.lean


Modified tactic/ring.lean


Modified tests/examples.lean




## [2018-04-16 19:00:13-04:00](https://github.com/leanprover-community/mathlib/commit/b7db508)
feat(analysis/topology/topological_space): basis elements are open
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* topological_space.is_open_of_is_topological_basis
- \+ *lemma* topological_space.mem_basis_subset_of_mem_open



## [2018-04-16 19:00:13-04:00](https://github.com/leanprover-community/mathlib/commit/6dd2bc0)
feat(data/option): more option decidability
#### Estimated changes
Modified data/bool.lean
- \+ *lemma* bool.not_ff

Modified data/option.lean
- \+ *lemma* option.is_none_iff_eq_none
- \+/\- *def* option.to_list

Modified logic/basic.lean
- \+ *def* decidable_of_bool



## [2018-04-16 20:29:17+02:00](https://github.com/leanprover-community/mathlib/commit/f2361dc)
fix(group_theory/coset): left_cosets.left_cosets -> left_cosets.eq_class_eq_left_coset is now a theorem
#### Estimated changes
Modified group_theory/coset.lean
- \+ *lemma* left_cosets.eq_class_eq_left_coset
- \- *def* left_cosets.left_coset



## [2018-04-16 20:09:50+02:00](https://github.com/leanprover-community/mathlib/commit/910de7e)
refactor(group_theory/coset): left_cosets is now a quotient ([#103](https://github.com/leanprover-community/mathlib/pull/103))
#### Estimated changes
Modified data/equiv.lean
- \+ *def* equiv.equiv_fib

Modified group_theory/coset.lean
- \- *lemma* is_subgroup.Union_left_cosets_eq_univ
- \- *lemma* is_subgroup.group_equiv_left_cosets_times_subgroup
- \+ *def* is_subgroup.left_coset_equiv_subgroup
- \- *lemma* is_subgroup.left_cosets_disjoint
- \- *lemma* is_subgroup.left_cosets_equiv_subgroup
- \- *lemma* is_subgroup.pairwise_left_cosets_disjoint
- \- *lemma* is_subgroup.subgroup_mem_left_cosets
- \+ *def* left_cosets.left_coset
- \+/\- *def* left_cosets

Modified group_theory/order_of_element.lean




## [2018-04-15 17:58:13+02:00](https://github.com/leanprover-community/mathlib/commit/479a122)
doc(doc): add topological space doc ([#101](https://github.com/leanprover-community/mathlib/pull/101))
#### Estimated changes
Added docs/theories/topological_spaces.md




## [2018-04-15 17:41:57+02:00](https://github.com/leanprover-community/mathlib/commit/c34f202)
Adding some notes on calc
#### Estimated changes
Modified docs/extras.md


Added docs/extras/calc.md




## [2018-04-15 17:39:03+02:00](https://github.com/leanprover-community/mathlib/commit/21d5618)
feat(docs/styles): Some more indentation guidelines ([#95](https://github.com/leanprover-community/mathlib/pull/95))
Fixed also a typo pointed out by Scott
#### Estimated changes
Modified docs/style.md




## [2018-04-15 17:36:59+02:00](https://github.com/leanprover-community/mathlib/commit/f1179bd)
feat(algebra/big_operators): update prod_bij_ne_one ([#100](https://github.com/leanprover-community/mathlib/pull/100))
#### Estimated changes
Modified algebra/big_operators.lean


Modified linear_algebra/basic.lean




## [2018-04-13 19:25:49+02:00](https://github.com/leanprover-community/mathlib/commit/5605233)
feat(algebra/big_operators): add prod_sum (equating the product over a sum to the sum of all combinations)
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.prod_sum

Modified data/finset.lean
- \+ *theorem* finset.attach_empty
- \+ *lemma* finset.attach_insert
- \+ *lemma* finset.injective_pi_cons
- \+ *def* finset.pi.cons
- \+ *lemma* finset.pi.cons_ne
- \+ *lemma* finset.pi.cons_same
- \+ *def* finset.pi.empty
- \+ *lemma* finset.pi_empty
- \+ *lemma* finset.pi_insert

Modified data/multiset.lean
- \+ *lemma* multiset.attach_ndinsert
- \+ *lemma* multiset.disjoint_map_map
- \+ *lemma* multiset.injective_pi_cons
- \+ *theorem* multiset.map_id
- \+ *lemma* multiset.map_singleton
- \+ *lemma* multiset.nodup_bind
- \+ *lemma* multiset.nodup_pi
- \+ *def* multiset.pairwise
- \+ *lemma* multiset.pairwise_coe_iff_pairwise
- \+ *lemma* multiset.pairwise_of_nodup
- \+ *lemma* multiset.pmap_cons
- \+ *lemma* multiset.pmap_zero
- \+ *lemma* multiset.prod_bind



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
- \+ *def* group.closure
- \+ *theorem* group.closure_subset
- \+ *theorem* group.gpowers_eq_closure
- \+ *inductive* group.in_closure
- \+ *lemma* group.mem_closure
- \+ *theorem* group.subset_closure
- \+ *lemma* is_subgroup.trivial_eq_closure
- \+ *lemma* mem_gpowers

Modified group_theory/submonoid.lean




## [2018-04-11 14:49:46+02:00](https://github.com/leanprover-community/mathlib/commit/fea2491)
chore(group_theory): move order_of into its own file; base costes on left_coset
#### Estimated changes
Modified group_theory/coset.lean
- \+ *lemma* is_subgroup.Union_left_cosets_eq_univ
- \+ *lemma* is_subgroup.group_equiv_left_cosets_times_subgroup
- \+ *lemma* is_subgroup.left_cosets_disjoint
- \+ *lemma* is_subgroup.left_cosets_equiv_subgroup
- \+ *lemma* is_subgroup.pairwise_left_cosets_disjoint
- \+ *lemma* is_subgroup.subgroup_mem_left_cosets
- \+/\- *def* left_coset
- \+/\- *lemma* left_coset_assoc
- \+/\- *def* left_coset_equiv
- \+/\- *lemma* left_coset_equiv_rel
- \+/\- *lemma* left_coset_mem_left_coset
- \+/\- *lemma* left_coset_right_coset
- \+ *def* left_cosets
- \+/\- *lemma* mem_left_coset
- \+/\- *lemma* mem_left_coset_iff
- \+/\- *lemma* mem_left_coset_left_coset
- \+/\- *lemma* mem_own_left_coset
- \+/\- *lemma* mem_own_right_coset
- \+/\- *lemma* mem_right_coset
- \+/\- *lemma* mem_right_coset_iff
- \+/\- *lemma* mem_right_coset_right_coset
- \+/\- *theorem* normal_of_eq_cosets
- \+/\- *def* right_coset
- \+/\- *lemma* right_coset_assoc
- \+/\- *lemma* right_coset_mem_right_coset

Added group_theory/order_of_element.lean
- \+ *lemma* exists_gpow_eq_one
- \+ *lemma* exists_pow_eq_one
- \+ *lemma* finset.mem_range_iff_mem_finset_range_of_mod_eq
- \+ *lemma* gpow_eq_mod_order_of
- \+ *lemma* mem_range_gpow_iff_mem_range_order_of
- \+ *lemma* order_eq_card_range_gpow
- \+ *def* order_of
- \+ *lemma* order_of_dvd_card_univ
- \+ *lemma* order_of_le_card_univ
- \+ *lemma* order_of_ne_zero
- \+ *lemma* pow_eq_mod_order_of
- \+ *lemma* pow_injective_of_lt_order_of
- \+ *lemma* pow_order_of_eq_one

Modified group_theory/subgroup.lean
- \- *def* cosets
- \- *lemma* exists_gpow_eq_one
- \- *lemma* exists_pow_eq_one
- \- *lemma* finset.mem_range_iff_mem_finset_range_of_mod_eq
- \- *lemma* gpow_eq_mod_order_of
- \+/\- *lemma* injective_mul
- \- *lemma* is_subgroup.Union_cosets_eq_univ
- \- *lemma* is_subgroup.cosets_disjoint
- \- *lemma* is_subgroup.cosets_equiv_subgroup
- \- *lemma* is_subgroup.group_equiv_cosets_times_subgroup
- \- *lemma* is_subgroup.mul_image
- \- *lemma* is_subgroup.pairwise_cosets_disjoint
- \- *lemma* is_subgroup.subgroup_mem_cosets
- \- *lemma* mem_range_gpow_iff_mem_range_order_of
- \- *lemma* order_eq_card_range_gpow
- \- *def* order_of
- \- *lemma* order_of_dvd_card_univ
- \- *lemma* order_of_le_card_univ
- \- *lemma* order_of_ne_zero
- \- *lemma* pow_eq_mod_order_of
- \- *lemma* pow_injective_of_lt_order_of
- \- *lemma* pow_order_of_eq_one



## [2018-04-11 13:50:33+02:00](https://github.com/leanprover-community/mathlib/commit/d2ab199)
chore(group_theory): simplify proofs; generalize some theorems
#### Estimated changes
Modified group_theory/coset.lean
- \+/\- *theorem* eq_cosets_of_normal
- \+/\- *lemma* left_coset_assoc
- \+/\- *lemma* left_coset_right_coset
- \+ *lemma* mem_left_coset_iff
- \- *lemma* mem_mem_left_coset
- \+ *lemma* mem_right_coset_iff
- \+/\- *theorem* normal_of_eq_cosets
- \+/\- *lemma* one_left_coset
- \- *lemma* one_right_coset
- \+/\- *lemma* right_coset_assoc
- \+ *lemma* right_coset_one

Modified group_theory/subgroup.lean
- \+ *lemma* is_group_hom.inj_iff_trivial_ker
- \- *lemma* is_group_hom.inj_iff_trivial_kernel
- \+ *lemma* is_group_hom.inj_of_trivial_ker
- \- *lemma* is_group_hom.inj_of_trivial_kernel
- \+/\- *lemma* is_group_hom.inv_iff_ker
- \- *lemma* is_group_hom.inv_ker
- \+ *def* is_group_hom.ker
- \- *lemma* is_group_hom.ker_inv
- \- *def* is_group_hom.kernel
- \+ *lemma* is_group_hom.mem_ker
- \- *lemma* is_group_hom.mem_ker_one
- \+/\- *lemma* is_group_hom.one_ker_inv
- \+ *lemma* is_group_hom.trivial_ker_of_inj
- \- *lemma* is_group_hom.trivial_kernel_of_inj
- \- *lemma* is_subgroup.eq_one_of_trivial_mem
- \+ *lemma* is_subgroup.mem_center
- \+/\- *lemma* is_subgroup.mem_norm_comm
- \+ *lemma* is_subgroup.mem_norm_comm_iff
- \+ *lemma* is_subgroup.mem_trivial
- \- *lemma* is_subgroup.trivial_mem_of_eq_one



## [2018-04-11 10:25:21+02:00](https://github.com/leanprover-community/mathlib/commit/ea0fb11)
style(group_theory): try to follow conventions (calc indentation, lowercase names, ...)
#### Estimated changes
Modified group_theory/coset.lean
- \+/\- *theorem* eq_cosets_of_normal
- \+/\- *def* left_coset
- \+/\- *lemma* left_coset_assoc
- \+/\- *def* left_coset_equiv
- \+/\- *lemma* left_coset_equiv_rel
- \+/\- *lemma* left_coset_mem_left_coset
- \+/\- *lemma* left_coset_right_coset
- \+/\- *lemma* mem_left_coset
- \+/\- *lemma* mem_left_coset_left_coset
- \+/\- *lemma* mem_mem_left_coset
- \+/\- *lemma* mem_own_left_coset
- \+/\- *lemma* mem_own_right_coset
- \+/\- *lemma* mem_right_coset
- \+/\- *lemma* mem_right_coset_right_coset
- \+/\- *theorem* normal_iff_eq_cosets
- \+/\- *theorem* normal_of_eq_cosets
- \+/\- *lemma* one_left_coset
- \+/\- *lemma* one_right_coset
- \+/\- *def* right_coset
- \+/\- *lemma* right_coset_assoc
- \+/\- *lemma* right_coset_mem_right_coset

Modified group_theory/subgroup.lean
- \+/\- *def* cosets
- \+/\- *lemma* injective_mul
- \+/\- *lemma* is_group_hom.inj_iff_trivial_kernel
- \+/\- *lemma* is_group_hom.inj_of_trivial_kernel
- \+/\- *lemma* is_group_hom.inv_iff_ker
- \+/\- *lemma* is_group_hom.inv_ker
- \+/\- *lemma* is_group_hom.inv_ker_one
- \+/\- *lemma* is_group_hom.ker_inv
- \+/\- *def* is_group_hom.kernel
- \+/\- *lemma* is_group_hom.mem_ker_one
- \+/\- *lemma* is_group_hom.one_iff_ker_inv
- \+/\- *lemma* is_group_hom.one_ker_inv
- \+/\- *lemma* is_group_hom.trivial_kernel_of_inj
- \+/\- *def* is_subgroup.center
- \+/\- *lemma* is_subgroup.eq_one_of_trivial_mem
- \+/\- *lemma* is_subgroup.mem_norm_comm
- \+/\- *def* is_subgroup.trivial
- \+/\- *lemma* is_subgroup.trivial_mem_of_eq_one



## [2018-04-11 10:24:33+02:00](https://github.com/leanprover-community/mathlib/commit/fa86d34)
feat(group_theory): add left/right cosets and normal subgroups
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *theorem* is_group_anti_hom.prod
- \+/\- *theorem* is_group_hom.prod

Modified algebra/group.lean
- \+/\- *theorem* is_group_anti_hom.inv
- \+/\- *theorem* is_group_anti_hom.mul
- \+/\- *theorem* is_group_hom.inv
- \+/\- *theorem* is_group_hom.mul
- \+/\- *def* is_group_hom

Added group_theory/coset.lean
- \+ *theorem* eq_cosets_of_normal
- \+ *def* left_coset
- \+ *lemma* left_coset_assoc
- \+ *def* left_coset_equiv
- \+ *lemma* left_coset_equiv_rel
- \+ *lemma* left_coset_mem_left_coset
- \+ *lemma* left_coset_right_coset
- \+ *lemma* mem_left_coset
- \+ *lemma* mem_left_coset_left_coset
- \+ *lemma* mem_mem_left_coset
- \+ *lemma* mem_own_left_coset
- \+ *lemma* mem_own_right_coset
- \+ *lemma* mem_right_coset
- \+ *lemma* mem_right_coset_right_coset
- \+ *theorem* normal_iff_eq_cosets
- \+ *theorem* normal_of_eq_cosets
- \+ *lemma* one_left_coset
- \+ *lemma* one_right_coset
- \+ *def* right_coset
- \+ *lemma* right_coset_assoc
- \+ *lemma* right_coset_mem_right_coset

Modified group_theory/subgroup.lean
- \+ *lemma* is_group_hom.inj_iff_trivial_kernel
- \+ *lemma* is_group_hom.inj_of_trivial_kernel
- \+ *lemma* is_group_hom.inv_iff_ker
- \+ *lemma* is_group_hom.inv_ker
- \+ *lemma* is_group_hom.inv_ker_one
- \+ *lemma* is_group_hom.ker_inv
- \+ *def* is_group_hom.kernel
- \+ *lemma* is_group_hom.mem_ker_one
- \+ *lemma* is_group_hom.one_iff_ker_inv
- \+ *lemma* is_group_hom.one_ker_inv
- \+ *lemma* is_group_hom.trivial_kernel_of_inj
- \+ *def* is_subgroup.center
- \+ *lemma* is_subgroup.eq_one_of_trivial_mem
- \+ *lemma* is_subgroup.mem_norm_comm
- \+ *def* is_subgroup.trivial
- \+ *lemma* is_subgroup.trivial_mem_of_eq_one



## [2018-04-10 14:38:56+02:00](https://github.com/leanprover-community/mathlib/commit/f85330a)
feat(group_theory/submonoid): relate monoid closure to list product
#### Estimated changes
Modified group_theory/submonoid.lean
- \+ *lemma* is_submonoid.list_prod_mem
- \+/\- *lemma* is_submonoid.pow_mem
- \+ *lemma* is_submonoid.power_subset
- \+ *theorem* monoid.exists_list_of_mem_closure



## [2018-04-10 13:58:37+02:00](https://github.com/leanprover-community/mathlib/commit/4a15503)
refactor(ring_theory): unify monoid closure in ring theory with the one in group theory
#### Estimated changes
Modified group_theory/submonoid.lean
- \+ *theorem* monoid.closure_subset
- \- *lemma* monoid.is_submonoid_closure
- \+ *theorem* monoid.subset_closure

Modified ring_theory/localization.lean
- \- *def* localization.closure
- \- *inductive* localization.in_closure
- \- *theorem* localization.subset_closure



## [2018-04-10 13:13:52+02:00](https://github.com/leanprover-community/mathlib/commit/ec18563)
feat(group_theory): add subtype instanes for group and monoid; monoid closure
#### Estimated changes
Modified group_theory/subgroup.lean


Modified group_theory/submonoid.lean
- \+ *def* monoid.closure
- \+ *inductive* monoid.in_closure
- \+ *lemma* monoid.is_submonoid_closure



## [2018-04-10 13:02:43+02:00](https://github.com/leanprover-community/mathlib/commit/88960f0)
refactor(algebra): move is_submonoid to group_theory and base is_subgroup on is_submonoid
#### Estimated changes
Modified algebra/group.lean
- \+/\- *theorem* inv_is_group_anti_hom
- \+/\- *def* is_group_anti_hom
- \+/\- *def* is_group_hom

Modified algebra/group_power.lean
- \- *def* powers

Modified data/list/basic.lean


Modified group_theory/subgroup.lean
- \+ *def* gpowers
- \+ *lemma* injective_mul
- \+/\- *lemma* is_subgroup.cosets_disjoint
- \+ *lemma* is_subgroup.gpow_mem
- \- *lemma* is_subgroup.injective_mul
- \- *lemma* is_subgroup.inv_mem
- \+/\- *lemma* is_subgroup.inv_mem_iff
- \+/\- *lemma* is_subgroup.mul_image
- \- *lemma* is_subgroup.mul_mem
- \+ *lemma* is_subgroup.mul_mem_cancel_left
- \+ *lemma* is_subgroup.mul_mem_cancel_right
- \+ *theorem* is_subgroup.of_div
- \+/\- *lemma* is_subgroup.subgroup_mem_cosets
- \- *structure* is_subgroup
- \- *lemma* is_subgroup_range_gpow

Added group_theory/submonoid.lean
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
- \+/\- *theorem* add_monoid.neg_smul
- \+/\- *theorem* add_monoid.smul_add
- \+/\- *theorem* add_monoid.smul_neg_comm
- \+/\- *theorem* add_monoid.smul_nonneg
- \+/\- *theorem* gpow_coe_nat
- \+/\- *theorem* gpow_neg_succ
- \+/\- *theorem* gpow_of_nat
- \+/\- *theorem* gsmul_add_comm
- \+/\- *theorem* gsmul_coe_nat
- \+/\- *theorem* gsmul_eq_mul'
- \+/\- *theorem* gsmul_eq_mul
- \+/\- *theorem* gsmul_neg_succ
- \+/\- *theorem* gsmul_of_nat
- \+/\- *theorem* mul_gsmul_assoc
- \+/\- *theorem* mul_gsmul_left

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
Added data/int/modeq.lean
- \+ *lemma* int.modeq.coe_nat_modeq_iff
- \+ *theorem* int.modeq.modeq_add
- \+ *theorem* int.modeq.modeq_add_cancel_left
- \+ *theorem* int.modeq.modeq_add_cancel_right
- \+ *theorem* int.modeq.modeq_iff_dvd
- \+ *theorem* int.modeq.modeq_mul
- \+ *theorem* int.modeq.modeq_mul_left'
- \+ *theorem* int.modeq.modeq_mul_left
- \+ *theorem* int.modeq.modeq_mul_right'
- \+ *theorem* int.modeq.modeq_mul_right
- \+ *theorem* int.modeq.modeq_neg
- \+ *theorem* int.modeq.modeq_of_dvd_of_modeq
- \+ *theorem* int.modeq.modeq_sub
- \+ *theorem* int.modeq.modeq_zero_iff
- \+ *def* int.modeq



## [2018-04-08 00:45:25-04:00](https://github.com/leanprover-community/mathlib/commit/6815830)
chore(measure_theory/measure_space): add coe_fn instance
#### Estimated changes
Modified analysis/measure_theory/lebesgue_measure.lean
- \+/\- *lemma* measure_theory.lebesgue_Ico
- \+/\- *lemma* measure_theory.lebesgue_Ioo
- \+/\- *lemma* measure_theory.lebesgue_singleton

Modified analysis/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.measure_Union_le_tsum_nat
- \+/\- *lemma* measure_theory.measure_empty
- \+/\- *lemma* measure_theory.measure_mono
- \+/\- *lemma* measure_theory.measure_space_eq



## [2018-04-08 00:35:55-04:00](https://github.com/leanprover-community/mathlib/commit/03d5bd9)
fix(*): update to lean
#### Estimated changes
Modified .travis.yml


Modified algebra/group_power.lean
- \+/\- *theorem* div_pow
- \+/\- *theorem* division_ring.inv_pow
- \+/\- *theorem* inv_gpow
- \+/\- *theorem* inv_pow
- \+/\- *theorem* mul_pow
- \+/\- *theorem* one_div_pow
- \+/\- *lemma* pow_abs
- \+/\- *lemma* pow_inv
- \+/\- *theorem* pow_inv_comm
- \+/\- *def* powers

Modified analysis/limits.lean


Modified analysis/measure_theory/outer_measure.lean


Modified data/int/basic.lean
- \+/\- *lemma* int.shiftl_eq_mul_pow
- \+/\- *lemma* int.shiftr_eq_div_pow

Modified data/nat/sqrt.lean


Modified data/pnat.lean
- \+/\- *theorem* pnat.pow_coe

Modified group_theory/subgroup.lean
- \+/\- *lemma* exists_pow_eq_one
- \+/\- *lemma* is_subgroup_range_gpow
- \+/\- *lemma* order_eq_card_range_gpow
- \+/\- *lemma* pow_eq_mod_order_of
- \+/\- *lemma* pow_order_of_eq_one

Modified leanpkg.toml


Modified linear_algebra/multivariate_polynomial.lean


Modified number_theory/pell.lean


Modified set_theory/cardinal.lean
- \+/\- *theorem* cardinal.nat_cast_pow

Modified set_theory/cofinality.lean


Modified set_theory/ordinal.lean
- \+/\- *theorem* ordinal.mul_omega_power_power
- \+/\- *theorem* ordinal.nat_cast_power

Modified set_theory/ordinal_notation.lean
- \+ *theorem* onote.power_def
- \+/\- *theorem* onote.repr_power

Modified tactic/ring.lean
- \+/\- *theorem* tactic.ring.pow_add_rev
- \+/\- *theorem* tactic.ring.pow_add_rev_right



## [2018-04-07 22:38:50-04:00](https://github.com/leanprover-community/mathlib/commit/e9b9014)
feat(data/erased): VM-erased data type
#### Estimated changes
Added data/erased.lean
- \+ *def* erased.bind
- \+ *theorem* erased.bind_eq_out
- \+ *def* erased.choice
- \+ *def* erased.join
- \+ *theorem* erased.join_eq_out
- \+ *def* erased.mk
- \+ *theorem* erased.mk_out
- \+ *theorem* erased.nonempty_iff
- \+ *theorem* erased.out_mk
- \+ *theorem* erased.out_proof
- \+ *def* erased.out_type
- \+ *def* erased

Modified data/set/basic.lean
- \+/\- *theorem* set.mem_singleton_iff



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
- \+ *theorem* nat.factors_lemma
- \+/\- *lemma* nat.perm_of_prod_eq_prod



## [2018-04-05 00:35:23-04:00](https://github.com/leanprover-community/mathlib/commit/efa4f92)
feat(data/nat/prime): lemmas about nat.factors
#### Estimated changes
Modified data/nat/prime.lean
- \+ *lemma* nat.factors_unique
- \+ *lemma* nat.mem_factors
- \+ *lemma* nat.mem_factors_of_dvd
- \+ *lemma* nat.mem_list_primes_of_dvd_prod
- \+ *lemma* nat.perm_of_prod_eq_prod
- \+ *lemma* nat.prod_factors



## [2018-04-05 00:22:45-04:00](https://github.com/leanprover-community/mathlib/commit/2d370e9)
feat(algebra/euclidean_domain): euclidean domains / euclidean algorithm
#### Estimated changes
Added algebra/euclidean_domain.lean
- \+ *lemma* euclidean_domain.div_self
- \+ *theorem* euclidean_domain.dvd_gcd
- \+ *lemma* euclidean_domain.dvd_mod
- \+ *lemma* euclidean_domain.dvd_mod_self
- \+ *theorem* euclidean_domain.gcd.induction
- \+ *def* euclidean_domain.gcd
- \+ *lemma* euclidean_domain.gcd_decreasing
- \+ *theorem* euclidean_domain.gcd_dvd
- \+ *theorem* euclidean_domain.gcd_dvd_left
- \+ *theorem* euclidean_domain.gcd_dvd_right
- \+ *theorem* euclidean_domain.gcd_next
- \+ *theorem* euclidean_domain.gcd_one_left
- \+ *theorem* euclidean_domain.gcd_self
- \+ *theorem* euclidean_domain.gcd_zero_left
- \+ *theorem* euclidean_domain.gcd_zero_right
- \+ *lemma* euclidean_domain.mod_lt
- \+ *lemma* euclidean_domain.mod_one
- \+ *lemma* euclidean_domain.mod_self
- \+ *lemma* euclidean_domain.mod_zero
- \+ *lemma* euclidean_domain.neq_zero_lt_mod_lt
- \+ *lemma* euclidean_domain.val_dvd_le
- \+ *lemma* euclidean_domain.val_lt_one
- \+ *lemma* euclidean_domain.zero_div
- \+ *lemma* euclidean_domain.zero_mod



## [2018-04-05 00:16:34-04:00](https://github.com/leanprover-community/mathlib/commit/467f60f)
feat(data/nat/basic): add div_le_div_right
Based on [#91](https://github.com/leanprover-community/mathlib/pull/91) by @MonoidMusician
#### Estimated changes
Modified data/nat/basic.lean




## [2018-04-05 00:13:56-04:00](https://github.com/leanprover-community/mathlib/commit/47f1384)
doc(docs/extras): Adding notes on simp
#### Estimated changes
Added docs/extras/simp.md




## [2018-04-05 00:12:09-04:00](https://github.com/leanprover-community/mathlib/commit/73d481a)
adding explanation of "change"
#### Estimated changes
Modified docs/extras/conv.md




## [2018-04-05 00:07:53-04:00](https://github.com/leanprover-community/mathlib/commit/c87f1e6)
fix(*): finish lean update
#### Estimated changes
Modified data/pnat.lean
- \+/\- *def* pnat.pow
- \+ *theorem* pnat.pow_coe

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
- \+/\- *lemma* finset.prod_const_one
- \+ *lemma* finset.sum_const_zero

Modified algebra/group.lean
- \+ *def* additive
- \+ *def* multiplicative

Modified algebra/group_power.lean
- \+ *theorem* add_gsmul
- \+/\- *theorem* add_monoid.add_smul
- \+ *theorem* add_monoid.mul_smul'
- \+ *theorem* add_monoid.mul_smul
- \+/\- *theorem* add_monoid.mul_smul_assoc
- \+ *theorem* add_monoid.mul_smul_left
- \- *theorem* add_monoid.mul_smul_right
- \+/\- *theorem* add_monoid.neg_smul
- \+/\- *theorem* add_monoid.one_smul
- \+ *def* add_monoid.smul
- \+ *theorem* add_monoid.smul_add
- \+/\- *theorem* add_monoid.smul_eq_mul'
- \+/\- *theorem* add_monoid.smul_eq_mul
- \- *theorem* add_monoid.smul_mul
- \+ *theorem* add_monoid.smul_neg_comm
- \+/\- *theorem* add_monoid.smul_nonneg
- \+/\- *theorem* add_monoid.smul_one
- \+ *theorem* add_monoid.smul_sub
- \+ *theorem* add_monoid.smul_zero
- \+/\- *theorem* add_monoid.zero_smul
- \+ *theorem* bit0_gsmul
- \+ *theorem* bit0_smul
- \+ *theorem* bit1_gsmul
- \+ *theorem* bit1_smul
- \+/\- *def* gpow
- \+/\- *theorem* gpow_add
- \+/\- *theorem* gpow_bit0
- \+/\- *theorem* gpow_bit1
- \+/\- *theorem* gpow_coe_nat
- \+ *theorem* gpow_mul'
- \+/\- *theorem* gpow_mul
- \+/\- *theorem* gpow_mul_comm
- \+/\- *theorem* gpow_neg
- \+/\- *theorem* gpow_neg_one
- \+ *theorem* gpow_neg_succ
- \+ *theorem* gpow_of_nat
- \+/\- *theorem* gpow_one
- \+/\- *theorem* gpow_zero
- \+ *def* gsmul
- \+ *theorem* gsmul_add_comm
- \- *theorem* gsmul_bit1
- \+ *theorem* gsmul_coe_nat
- \+/\- *theorem* gsmul_eq_mul'
- \+/\- *theorem* gsmul_eq_mul
- \+ *theorem* gsmul_mul'
- \+/\- *theorem* gsmul_mul
- \- *theorem* gsmul_neg
- \- *theorem* gsmul_neg_one
- \+ *theorem* gsmul_neg_succ
- \+ *theorem* gsmul_of_nat
- \- *theorem* gsmul_one
- \+/\- *theorem* inv_gpow
- \+/\- *theorem* list.sum_repeat
- \+/\- *theorem* mul_gsmul_assoc
- \+ *theorem* mul_gsmul_left
- \- *theorem* mul_gsmul_right
- \+/\- *theorem* nat.pow_eq_pow
- \+ *theorem* neg_gsmul
- \+ *theorem* neg_one_gsmul
- \+/\- *theorem* one_gpow
- \+ *theorem* one_gsmul
- \+/\- *lemma* pow_abs
- \+ *theorem* pow_mul'
- \+/\- *theorem* pow_mul_comm
- \+/\- *theorem* pow_zero
- \+ *theorem* smul_add_comm'
- \+ *theorem* smul_add_comm
- \- *theorem* smul_bit1
- \- *theorem* smul_succ'
- \- *theorem* smul_succ
- \- *theorem* smul_two
- \+ *theorem* succ_smul'
- \+ *theorem* succ_smul
- \+ *theorem* two_smul
- \+ *theorem* zero_gsmul

Modified analysis/limits.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/topological_space.lean


Modified data/int/basic.lean
- \+/\- *lemma* int.shiftl_eq_mul_pow
- \+/\- *lemma* int.shiftr_eq_div_pow

Modified data/multiset.lean
- \+/\- *theorem* multiset.count_smul
- \+/\- *theorem* multiset.prod_repeat
- \+ *lemma* multiset.sum_map_sum_map
- \+ *theorem* multiset.sum_repeat

Modified data/nat/sqrt.lean


Modified data/real/basic.lean


Modified data/set/lattice.lean
- \- *lemma* set.subset.antisymm_iff

Modified group_theory/subgroup.lean
- \+/\- *lemma* exists_gpow_eq_one
- \+/\- *lemma* exists_pow_eq_one
- \+/\- *lemma* gpow_eq_mod_order_of
- \+/\- *lemma* is_subgroup_range_gpow
- \+/\- *lemma* order_eq_card_range_gpow
- \+/\- *lemma* pow_eq_mod_order_of
- \+/\- *lemma* pow_order_of_eq_one

Modified leanpkg.toml


Modified linear_algebra/multivariate_polynomial.lean


Modified number_theory/pell.lean


Modified ring_theory/localization.lean


Modified set_theory/cardinal.lean
- \+/\- *theorem* cardinal.nat_cast_pow

Modified set_theory/ordinal.lean
- \+/\- *theorem* ordinal.nat_cast_power

Modified tactic/norm_num.lean


Modified tactic/ring.lean


Modified tests/norm_num.lean




## [2018-04-01 22:10:37-04:00](https://github.com/leanprover-community/mathlib/commit/777f6b4)
feat(data/set/basic): add some more set lemmas
#### Estimated changes
Modified data/analysis/filter.lean


Modified data/set/basic.lean
- \+ *theorem* set.compl_subset_comm
- \+ *theorem* set.compl_subset_iff_union
- \- *theorem* set.compl_subset_of_compl_subset
- \+/\- *theorem* set.compl_union_self
- \+/\- *theorem* set.eq_empty_of_subset_empty
- \+/\- *theorem* set.eq_univ_of_univ_subset
- \+/\- *theorem* set.exists_mem_of_ne_empty
- \+ *theorem* set.image_compl_eq
- \+ *theorem* set.image_compl_subset
- \+/\- *theorem* set.image_empty
- \+/\- *theorem* set.image_inter
- \+ *theorem* set.image_univ_of_surjective
- \+ *theorem* set.mem_compl_image
- \- *theorem* set.mem_image_compl
- \+/\- *theorem* set.mem_univ
- \- *theorem* set.mem_univ_eq
- \- *theorem* set.mem_univ_iff
- \+ *theorem* set.subset.antisymm_iff
- \+ *theorem* set.subset_compl_comm
- \+ *theorem* set.subset_compl_iff_disjoint
- \+ *theorem* set.subset_image_compl
- \+/\- *theorem* set.union_compl_self
- \+ *theorem* set.univ_subset_iff



## [2018-04-01 21:30:17-04:00](https://github.com/leanprover-community/mathlib/commit/d80ca59)
feat(data/fin): add fz/fs recursor for fin
#### Estimated changes
Modified data/fin.lean
- \+ *def* fin.succ_rec
- \+ *def* fin.succ_rec_on
- \+ *theorem* fin.succ_rec_on_succ
- \+ *theorem* fin.succ_rec_on_zero

