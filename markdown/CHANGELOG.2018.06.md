## [2018-06-30 23:04:40-04:00](https://github.com/leanprover-community/mathlib/commit/7b0c150)
refactor(data/equiv): reorganize data.equiv deps
#### Estimated changes
Modified computability/primrec.lean


Modified data/array/lemmas.lean
- \+ *def* equiv.array_equiv_fin
- \+ *def* equiv.d_array_equiv_fin

Renamed data/equiv.lean to data/equiv/basic.lean
- \- *def* equiv.array_equiv_fin
- \- *def* equiv.bool_prod_nat_equiv_nat
- \- *def* equiv.d_array_equiv_fin
- \- *def* equiv.int_equiv_nat
- \- *def* equiv.nat_prod_nat_equiv_nat
- \- *def* equiv.nat_sum_bool_equiv_nat
- \- *def* equiv.nat_sum_nat_equiv_nat
- \- *def* equiv.prod_equiv_of_equiv_nat
- \- *def* equiv.vector_equiv_array
- \- *def* equiv.vector_equiv_fin
- \- *theorem* function.left_inverse.comp
- \- *theorem* function.left_inverse.f_g_eq_id
- \- *theorem* function.right_inverse.comp
- \- *theorem* function.right_inverse.g_f_eq_id

Added data/equiv/denumerable.lean
- \+ *theorem* denumerable.decode_eq_of_nat
- \+ *theorem* denumerable.decode_is_some
- \+ *theorem* denumerable.encode_of_nat
- \+ *def* denumerable.equiv₂
- \+ *def* denumerable.eqv
- \+ *def* denumerable.mk'
- \+ *def* denumerable.of_equiv
- \+ *theorem* denumerable.of_equiv_of_nat
- \+ *def* denumerable.of_nat
- \+ *theorem* denumerable.of_nat_encode
- \+ *theorem* denumerable.of_nat_nat
- \+ *theorem* denumerable.of_nat_of_decode
- \+ *def* denumerable.pair
- \+ *theorem* denumerable.prod_nat_of_nat
- \+ *theorem* denumerable.prod_of_nat_val
- \+ *theorem* denumerable.sigma_of_nat_val

Renamed data/encodable.lean to data/equiv/encodable.lean
- \- *def* encodable.decode_list
- \- *theorem* encodable.decode_list_succ
- \- *theorem* encodable.decode_list_zero
- \- *def* encodable.decode_multiset
- \- *def* encodable.encodable_of_list
- \- *def* encodable.encode_list
- \- *theorem* encodable.encode_list_cons
- \- *theorem* encodable.encode_list_nil
- \- *def* encodable.encode_multiset
- \- *theorem* encodable.length_le_encode
- \- *def* encodable.trunc_encodable_of_fintype

Renamed data/denumerable.lean to data/equiv/list.lean
- \- *theorem* denumerable.decode_eq_of_nat
- \- *theorem* denumerable.decode_is_some
- \- *theorem* denumerable.encode_of_nat
- \- *def* denumerable.equiv₂
- \- *def* denumerable.eqv
- \- *def* denumerable.mk'
- \- *def* denumerable.of_equiv
- \- *theorem* denumerable.of_equiv_of_nat
- \- *def* denumerable.of_nat
- \- *theorem* denumerable.of_nat_encode
- \- *theorem* denumerable.of_nat_nat
- \- *theorem* denumerable.of_nat_of_decode
- \- *def* denumerable.pair
- \- *theorem* denumerable.prod_nat_of_nat
- \- *theorem* denumerable.prod_of_nat_val
- \- *theorem* denumerable.sigma_of_nat_val
- \+ *def* encodable.decode_list
- \+ *theorem* encodable.decode_list_succ
- \+ *theorem* encodable.decode_list_zero
- \+ *def* encodable.decode_multiset
- \+ *def* encodable.encodable_of_list
- \+ *def* encodable.encode_list
- \+ *theorem* encodable.encode_list_cons
- \+ *theorem* encodable.encode_list_nil
- \+ *def* encodable.encode_multiset
- \+ *theorem* encodable.length_le_encode
- \+ *def* encodable.trunc_encodable_of_fintype

Added data/equiv/nat.lean
- \+ *def* equiv.bool_prod_nat_equiv_nat
- \+ *def* equiv.int_equiv_nat
- \+ *def* equiv.nat_prod_nat_equiv_nat
- \+ *def* equiv.nat_sum_nat_equiv_nat
- \+ *def* equiv.prod_equiv_of_equiv_nat

Modified data/erased.lean


Modified data/fintype.lean


Modified data/rat.lean


Modified data/real/cau_seq.lean


Modified data/set/basic.lean
- \+ *lemma* set.image_congr
- \+ *lemma* set.subtype_val_image
- \+ *lemma* set.subtype_val_range

Modified data/set/countable.lean


Modified data/set/enumerate.lean


Modified data/set/lattice.lean
- \- *lemma* set.image_congr
- \- *lemma* set.subtype_val_image
- \- *lemma* set.subtype_val_range

Modified data/vector2.lean
- \+ *def* equiv.vector_equiv_array
- \+ *def* equiv.vector_equiv_fin

Modified group_theory/coset.lean


Modified group_theory/free_group.lean


Modified logic/embedding.lean


Modified logic/function.lean
- \+ *theorem* function.left_inverse.comp
- \+ *theorem* function.left_inverse.comp_eq_id
- \+ *theorem* function.right_inverse.comp
- \+ *theorem* function.right_inverse.comp_eq_id

Modified order/order_iso.lean




## [2018-06-30 00:43:36-04:00](https://github.com/leanprover-community/mathlib/commit/913f702)
feat(computability/turing_machine): rework proofs, simplify TM lang
#### Estimated changes
Modified algebra/group_power.lean


Modified computability/turing_machine.lean
- \+/\- *def* turing.TM0.eval
- \+ *def* turing.TM0.init
- \+/\- *def* turing.TM1.eval
- \+ *def* turing.TM1.init
- \- *def* turing.TM1.reaches
- \+ *def* turing.TM1.step_aux
- \- *def* turing.TM1to0.tr'
- \+/\- *def* turing.TM1to0.tr
- \+ *def* turing.TM1to0.tr_aux
- \+/\- *def* turing.TM1to0.tr_cfg
- \+ *theorem* turing.TM1to0.tr_eval
- \- *theorem* turing.TM1to0.tr_reaches
- \+ *theorem* turing.TM1to0.tr_respects
- \+/\- *theorem* turing.TM1to0.tr_supports
- \+/\- *def* turing.TM1to0.Λ'
- \+/\- *def* turing.TM2.eval
- \+ *def* turing.TM2.init
- \- *theorem* turing.TM2.move_until_left_reaches₁
- \- *theorem* turing.TM2.move_until_right_reaches₁
- \- *def* turing.TM2.reaches₁
- \- *theorem* turing.TM2.reaches₁_step
- \+ *def* turing.TM2to1.st_run
- \+ *def* turing.TM2to1.st_var
- \+ *def* turing.TM2to1.st_write
- \+ *def* turing.TM2to1.stackel.get
- \+ *def* turing.TM2to1.stackel.is_bottom
- \+ *def* turing.TM2to1.stackel.is_top
- \+ *def* turing.TM2to1.stackel_equiv
- \+ *theorem* turing.TM2to1.step_run
- \+ *theorem* turing.TM2to1.supports_run
- \- *def* turing.TM2to1.tr'
- \- *def* turing.TM2to1.tr_cfg
- \+ *theorem* turing.TM2to1.tr_cfg_init
- \+ *theorem* turing.TM2to1.tr_eval
- \+ *theorem* turing.TM2to1.tr_eval_dom
- \+ *def* turing.TM2to1.tr_init
- \+ *def* turing.TM2to1.tr_normal
- \+ *theorem* turing.TM2to1.tr_normal_run
- \- *theorem* turing.TM2to1.tr_reaches
- \+ *theorem* turing.TM2to1.tr_respects
- \+ *theorem* turing.TM2to1.tr_respects_aux
- \+ *theorem* turing.TM2to1.tr_respects_aux₁
- \+ *theorem* turing.TM2to1.tr_respects_aux₂
- \+ *theorem* turing.TM2to1.tr_respects_aux₃
- \+ *def* turing.TM2to1.tr_st_act
- \+ *def* turing.TM2to1.tr_stk
- \+ *theorem* turing.TM2to1.tr_stmts₁_run
- \+ *theorem* turing.TM2to1.{l}
- \+ *def* turing.TM2to1.Γ'
- \- *def* turing.TM2to1.Λ'
- \+ *def* turing.TM2to1.Λ'_inh
- \- *def* turing.TM3.eval
- \- *def* turing.TM3.reaches
- \- *def* turing.TM3.step
- \- *def* turing.TM3.step_aux
- \- *theorem* turing.TM3.step_supports
- \- *theorem* turing.TM3.stmts_supports_stmt
- \- *theorem* turing.TM3.stmts_trans
- \- *theorem* turing.TM3.stmts₁_self
- \- *theorem* turing.TM3.stmts₁_supports_stmt_mono
- \- *theorem* turing.TM3.stmts₁_trans
- \- *def* turing.TM3.supports
- \- *def* turing.TM3.supports_stmt
- \- *def* turing.TM3to2.at_stack
- \- *def* turing.TM3to2.stackel.get
- \- *def* turing.TM3to2.stackel.is_bottom
- \- *def* turing.TM3to2.stackel.is_top
- \- *def* turing.TM3to2.stackel_equiv
- \- *def* turing.TM3to2.tr
- \- *theorem* turing.TM3to2.tr_reaches
- \- *def* turing.TM3to2.tr_stk
- \- *theorem* turing.TM3to2.tr_supports
- \- *def* turing.TM3to2.Γ'
- \- *def* turing.TM3to2.Λ'
- \- *def* turing.dir.rev
- \+ *theorem* turing.eval_maximal
- \+ *theorem* turing.eval_maximal₁
- \+ *def* turing.frespects
- \+ *theorem* turing.frespects_eq
- \+ *theorem* turing.fun_respects
- \+ *theorem* turing.mem_eval
- \+ *def* turing.reaches
- \+ *theorem* turing.reaches_eval
- \+ *theorem* turing.reaches_total
- \+ *def* turing.reaches₁
- \+ *theorem* turing.reaches₁_eq
- \+ *def* turing.respects
- \+ *theorem* turing.tr_eval'
- \+ *theorem* turing.tr_eval
- \+ *theorem* turing.tr_eval_dom
- \+ *theorem* turing.tr_eval_rev
- \+ *theorem* turing.tr_reaches
- \+ *theorem* turing.tr_reaches_rev
- \+ *theorem* turing.tr_reaches₁

Modified data/fintype.lean
- \+ *def* finset.insert_none
- \+ *theorem* finset.mem_insert_none
- \+ *theorem* finset.some_mem_insert_none

Modified data/list/basic.lean
- \+ *theorem* list.map_repeat
- \+ *theorem* list.map_reverse_core
- \+ *theorem* list.map_tail
- \+/\- *theorem* list.repeat_add
- \+ *theorem* list.repeat_succ
- \+ *theorem* list.reverse_core_eq
- \+ *theorem* list.tail_repeat

Modified data/option.lean
- \+ *theorem* option.eq_none_iff_forall_not_mem
- \+ *theorem* option.mem_unique

Modified data/pfun.lean
- \+/\- *theorem* pfun.fix_induction

Modified logic/relation.lean
- \+ *lemma* relation.refl_trans_gen.total_of_right_unique



## [2018-06-30 00:36:55-04:00](https://github.com/leanprover-community/mathlib/commit/cfb5dfd)
refactor(data/finset): use partial_order to define lattice structure
#### Estimated changes
Modified data/finset.lean




## [2018-06-30 00:36:27-04:00](https://github.com/leanprover-community/mathlib/commit/ddbb813)
feat(data/fintype): finite choices, computably
#### Estimated changes
Modified data/fintype.lean
- \+ *def* quotient.fin_choice
- \+ *def* quotient.fin_choice_aux
- \+ *theorem* quotient.fin_choice_aux_eq
- \+ *theorem* quotient.fin_choice_eq

Modified data/quot.lean
- \+ *theorem* quotient.choice_eq



## [2018-06-25 20:05:43-04:00](https://github.com/leanprover-community/mathlib/commit/a7b749f)
fix(order/boolean_algebra): neg_unique: replace rsimp proof, speed up build
#### Estimated changes
Modified order/boolean_algebra.lean




## [2018-06-25 05:45:48-04:00](https://github.com/leanprover-community/mathlib/commit/97a1d1b)
feat(data/fintype): more fintype instances ([#145](https://github.com/leanprover-community/mathlib/pull/145))
#### Estimated changes
Modified data/fintype.lean


Modified data/set/finite.lean




## [2018-06-25 05:43:26-04:00](https://github.com/leanprover-community/mathlib/commit/90aeb8e)
feat(tactic/solve_by_elim): writing a symm_apply tactic for solve_by_elim ([#164](https://github.com/leanprover-community/mathlib/pull/164))
writing a symm_apply tactic, and have solve_by_elim use it, per discussion with @SimonHudon
#### Estimated changes
Modified tactic/interactive.lean


Modified tests/tactics.lean




## [2018-06-25 05:42:30-04:00](https://github.com/leanprover-community/mathlib/commit/a39c5ca)
correcting comment
#### Estimated changes
Modified algebra/euclidean_domain.lean




## [2018-06-25 05:41:01-04:00](https://github.com/leanprover-community/mathlib/commit/0a13c05)
feat(list/basic): map_subset
from [#166](https://github.com/leanprover-community/mathlib/pull/166)
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.map_subset



## [2018-06-25 05:35:22-04:00](https://github.com/leanprover-community/mathlib/commit/4ec65f5)
fix(data/list/basic): simplify last_append, speed up build
#### Estimated changes
Modified data/list/basic.lean




## [2018-06-25 05:29:11-04:00](https://github.com/leanprover-community/mathlib/commit/516b254)
feat(tactic/ring2): alternative ring tactic
#### Estimated changes
Modified data/num/lemmas.lean
- \+/\- *theorem* num.cast_sub'
- \+ *theorem* num.to_znum_inj
- \+ *theorem* znum.abs_to_znum

Added tactic/ring2.lean
- \+ *theorem* tactic.ring2.correctness
- \+ *def* tactic.ring2.csring_expr.eval
- \+ *def* tactic.ring2.horner_expr.add
- \+ *def* tactic.ring2.horner_expr.add_aux
- \+ *def* tactic.ring2.horner_expr.add_const
- \+ *def* tactic.ring2.horner_expr.atom
- \+ *def* tactic.ring2.horner_expr.cseval
- \+ *theorem* tactic.ring2.horner_expr.cseval_add
- \+ *theorem* tactic.ring2.horner_expr.cseval_add_const
- \+ *theorem* tactic.ring2.horner_expr.cseval_atom
- \+ *theorem* tactic.ring2.horner_expr.cseval_horner'
- \+ *theorem* tactic.ring2.horner_expr.cseval_mul
- \+ *theorem* tactic.ring2.horner_expr.cseval_mul_const
- \+ *theorem* tactic.ring2.horner_expr.cseval_of_csexpr
- \+ *theorem* tactic.ring2.horner_expr.cseval_pow
- \+ *def* tactic.ring2.horner_expr.horner'
- \+ *def* tactic.ring2.horner_expr.inv
- \+ *def* tactic.ring2.horner_expr.is_cs
- \+ *def* tactic.ring2.horner_expr.mul
- \+ *def* tactic.ring2.horner_expr.mul_aux
- \+ *def* tactic.ring2.horner_expr.mul_const
- \+ *def* tactic.ring2.horner_expr.neg
- \+ *def* tactic.ring2.horner_expr.of_csexpr
- \+ *def* tactic.ring2.horner_expr.pow
- \+ *def* tactic.ring2.horner_expr.repr
- \+ *def* tactic.ring2.tree.get
- \+ *def* tactic.ring2.tree.index_of
- \+ *def* tactic.ring2.tree.of_rbnode



## [2018-06-21 08:06:52-04:00](https://github.com/leanprover-community/mathlib/commit/4082136)
feat(tactic/refine_struct): match `{ .. }` in subexpressions ([#162](https://github.com/leanprover-community/mathlib/pull/162))
#### Estimated changes
Modified tactic/interactive.lean


Modified tests/tactics.lean
- \+ *def* my_bar
- \+ *def* my_foo



## [2018-06-21 08:05:27-04:00](https://github.com/leanprover-community/mathlib/commit/aa55cba)
fix(order/lattice): typo
#### Estimated changes
Modified order/lattice.lean




## [2018-06-20 22:42:18-04:00](https://github.com/leanprover-community/mathlib/commit/905345a)
fix(data/array/lemmas,...): fix build
#### Estimated changes
Modified data/array/lemmas.lean


Modified set_theory/cofinality.lean




## [2018-06-20 21:42:57-04:00](https://github.com/leanprover-community/mathlib/commit/a30b7c7)
feat(data/string): fix string_lt, add repr for multiset, pnat
#### Estimated changes
Added data/char.lean


Modified data/finset.lean


Modified data/list/basic.lean
- \+ *theorem* list.lex.append_left
- \+ *theorem* list.lex.append_right
- \+ *theorem* list.lex.cons_iff
- \+/\- *theorem* list.lex.imp
- \+ *theorem* list.lex.ne_iff
- \+ *theorem* list.lex.to_ne
- \- *theorem* list.lex_append_left
- \- *theorem* list.lex_append_right
- \- *theorem* list.lex_ne_iff
- \- *theorem* list.ne_of_lex_ne
- \+ *theorem* list.nil_lt_cons
- \+/\- *theorem* list.reverse_cons'
- \+/\- *theorem* list.reverse_cons

Modified data/list/perm.lean


Modified data/multiset.lean


Modified data/pnat.lean


Added data/string.lean
- \+ *theorem* string.le_iff_to_list_le
- \+ *theorem* string.lt_iff_to_list_lt
- \+ *def* string.ltb
- \+ *theorem* string.to_list_inj

Modified order/basic.lean
- \+/\- *theorem* is_order_connected.neg_trans
- \+/\- *theorem* is_strict_weak_order_of_is_order_connected



## [2018-06-19 14:32:22-04:00](https://github.com/leanprover-community/mathlib/commit/fbe1047)
feat(tactic/refine_struct): add `refine_struct` to use goal tags ([#147](https://github.com/leanprover-community/mathlib/pull/147))
#### Estimated changes
Modified algebra/pi_instances.lean


Modified category/basic.lean
- \+ *def* mmap₂

Added data/dlist/basic.lean
- \+ *def* dlist.join

Modified data/multiset.lean


Modified docs/tactics.md


Modified tactic/basic.lean


Modified tactic/interactive.lean




## [2018-06-19 09:53:45-04:00](https://github.com/leanprover-community/mathlib/commit/2216460)
Merge branch 'master' of github.com:leanprover/mathlib
#### Estimated changes
Modified analysis/topology/continuity.lean


Modified analysis/topology/uniform_space.lean


Modified category/basic.lean
- \+ *theorem* id_map'
- \+ *lemma* is_comm_applicative.commutative_map
- \+ *theorem* map_map
- \+ *theorem* map_seq
- \+ *theorem* pure_id'_seq
- \+ *theorem* seq_map_assoc

Modified computability/partrec.lean
- \+/\- *theorem* partrec.comp



## [2018-06-19 08:25:55-04:00](https://github.com/leanprover-community/mathlib/commit/f22285c)
feat(algebra/pi_instances): add apply lemmas ([#149](https://github.com/leanprover-community/mathlib/pull/149))
#### Estimated changes
Modified algebra/pi_instances.lean
- \+ *lemma* pi.add_apply
- \+ *lemma* pi.inv_apply
- \+ *lemma* pi.mul_apply
- \+ *lemma* pi.neg_apply
- \+ *lemma* pi.one_apply
- \+ *lemma* pi.smul_apply
- \+ *lemma* pi.zero_apply



## [2018-06-19 08:19:49-04:00](https://github.com/leanprover-community/mathlib/commit/0a0e8a5)
feat(tactic/ext): `ext` now applies to `prod`; fix `ext` on function types ([#158](https://github.com/leanprover-community/mathlib/pull/158))
#### Estimated changes
Modified analysis/metric_space.lean


Modified analysis/topology/topological_space.lean


Modified data/prod.lean
- \+/\- *lemma* prod.ext
- \+ *lemma* prod.ext_iff

Modified docs/tactics.md


Modified tactic/basic.lean


Modified tactic/interactive.lean


Modified tests/tactics.lean




## [2018-06-19 08:17:52-04:00](https://github.com/leanprover-community/mathlib/commit/0087c2c)
feat(analysis/topology): quotient spaces and quotient maps ([#155](https://github.com/leanprover-community/mathlib/pull/155))
* style(analysis/topology): simplify induced_mono and induced_sup
* style(analysis/topology/topological_space): reorganize section constructions
* feat(analysis/topology/topological_space): add more galois connection lemmas
* feat(analysis/topology): quotient spaces and quotient maps
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* coinduced_compose
- \+ *lemma* coinduced_id
- \+ *lemma* continuous_quot_lift
- \+ *lemma* continuous_quot_mk
- \+ *lemma* continuous_quotient_lift
- \+ *lemma* continuous_quotient_mk
- \- *lemma* induced_mono
- \- *lemma* induced_sup
- \+ *lemma* quotient_map.continuous_iff
- \+ *def* quotient_map
- \+ *lemma* quotient_map_compose
- \+ *lemma* quotient_map_id
- \+ *lemma* quotient_map_of_quotient_map_compose
- \+ *lemma* quotient_map_quot_mk
- \+ *lemma* quotient_map_quotient_mk

Modified analysis/topology/topological_space.lean
- \+ *lemma* coinduced_inf
- \+ *lemma* coinduced_infi
- \+ *lemma* coinduced_mono
- \+ *lemma* coinduced_top
- \+ *lemma* gc_induced_coinduced
- \+ *lemma* induced_bot
- \+ *lemma* induced_mono
- \+ *lemma* induced_sup
- \+ *lemma* induced_supr



## [2018-06-19 08:13:31-04:00](https://github.com/leanprover-community/mathlib/commit/5e0b137)
feat (group_theory/coset): quotient by normal subgroup is a group
#### Estimated changes
Modified group_theory/coset.lean




## [2018-06-19 08:12:39-04:00](https://github.com/leanprover-community/mathlib/commit/8609a3d)
feat(split_ifs): fail if no progress ([#153](https://github.com/leanprover-community/mathlib/pull/153))
#### Estimated changes
Modified tactic/split_ifs.lean


Modified tests/split_ifs.lean




## [2018-06-19 08:11:25-04:00](https://github.com/leanprover-community/mathlib/commit/f8e3965)
blah
#### Estimated changes
Modified algebra/ring.lean




## [2018-06-19 08:09:27-04:00](https://github.com/leanprover-community/mathlib/commit/4e2aea5)
feat(data/option): is_some and is_none simp theorems
#### Estimated changes
Modified data/hash_map.lean


Modified data/option.lean
- \+ *theorem* option.is_none_none
- \+ *theorem* option.is_none_some
- \+ *theorem* option.is_some_none
- \+ *theorem* option.is_some_some



## [2018-06-19 08:08:36-04:00](https://github.com/leanprover-community/mathlib/commit/e1f795d)
chore(data/list/basic): minor cleanup of find variables ([#137](https://github.com/leanprover-community/mathlib/pull/137))
#### Estimated changes
Modified analysis/topology/continuity.lean


Modified analysis/topology/uniform_space.lean


Modified category/basic.lean
- \- *theorem* id_map'
- \- *lemma* is_comm_applicative.commutative_map
- \- *theorem* map_map
- \- *theorem* map_seq
- \- *theorem* pure_id'_seq
- \- *theorem* seq_map_assoc

Modified computability/partrec.lean
- \+/\- *theorem* partrec.comp

Modified data/list/basic.lean
- \+/\- *def* list.find
- \+/\- *theorem* list.find_cons_of_neg
- \+/\- *theorem* list.find_cons_of_pos
- \+/\- *theorem* list.find_eq_none
- \+/\- *theorem* list.find_mem
- \+/\- *theorem* list.find_nil
- \+/\- *theorem* list.find_some



## [2018-06-17 10:20:07-04:00](https://github.com/leanprover-community/mathlib/commit/896455c)
feat(category): add functor_norm simp_attr, and class is_comm_applicative
#### Estimated changes
Modified analysis/topology/continuity.lean


Modified analysis/topology/uniform_space.lean


Modified category/basic.lean
- \+ *theorem* id_map'
- \+ *lemma* is_comm_applicative.commutative_map
- \+ *theorem* map_map
- \+ *theorem* map_seq
- \+ *theorem* pure_id'_seq
- \+ *theorem* seq_map_assoc

Modified computability/partrec.lean
- \+/\- *theorem* partrec.comp



## [2018-06-16 17:39:03-04:00](https://github.com/leanprover-community/mathlib/commit/85bc56a)
feat(computability/turing_machine): finish stack machine proof
#### Estimated changes
Modified algebra/group_power.lean


Modified computability/turing_machine.lean
- \- *theorem* turing.TM2.move_until_left_reaches
- \+ *theorem* turing.TM2.move_until_left_reaches₁
- \- *theorem* turing.TM2.move_until_right_reaches
- \+ *theorem* turing.TM2.move_until_right_reaches₁
- \+ *def* turing.TM2.reaches₁
- \+ *theorem* turing.TM2.reaches₁_step
- \+/\- *def* turing.TM3.eval
- \+/\- *def* turing.TM3to2.at_stack
- \- *theorem* turing.TM3to2.at_stack_supports
- \- *def* turing.TM3to2.pop
- \- *def* turing.TM3to2.push
- \- *def* turing.TM3to2.stack_val
- \+/\- *def* turing.TM3to2.stackel.get
- \+/\- *def* turing.TM3to2.stackel.is_bottom
- \+/\- *def* turing.TM3to2.stackel.is_top
- \+/\- *def* turing.TM3to2.stackel_equiv
- \+ *theorem* turing.TM3to2.tr_reaches
- \+ *def* turing.TM3to2.tr_stk
- \- *def* turing.TM3to2.tr_tape
- \- *def* turing.TM3to2.Γ'.write_stack
- \+ *def* turing.TM3to2.Γ'
- \- *def* turing.TM3to2.Γ'_equiv
- \+ *def* turing.dwrite
- \+ *theorem* turing.dwrite_eq
- \+ *theorem* turing.dwrite_ne
- \+ *theorem* turing.dwrite_self
- \+/\- *theorem* turing.tape.move_left_nth
- \+/\- *theorem* turing.tape.move_right_nth
- \+ *theorem* turing.tape.nth_zero
- \+/\- *theorem* turing.tape.write_nth

Modified data/list/basic.lean
- \+ *theorem* list.map_eq_append_split
- \+ *theorem* list.repeat_add

Modified group_theory/free_group.lean


Modified logic/relation.lean
- \+ *lemma* relation.refl_trans_gen_iff_eq_or_trans_gen
- \+ *lemma* relation.trans_gen.head'
- \+ *lemma* relation.trans_gen.head'_iff
- \+ *lemma* relation.trans_gen.head
- \+ *lemma* relation.trans_gen.tail'
- \+ *lemma* relation.trans_gen.tail'_iff
- \+ *lemma* relation.trans_gen.to_refl
- \+ *lemma* relation.trans_gen.trans
- \+ *lemma* relation.trans_gen.trans_left
- \+ *lemma* relation.trans_gen.trans_right



## [2018-06-15 05:11:08+07:00](https://github.com/leanprover-community/mathlib/commit/fba4d89)
fix(analysis/topology/continuity): remove unused code
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+/\- *lemma* continuous_apply



## [2018-06-13 01:28:56+07:00](https://github.com/leanprover-community/mathlib/commit/fe590ca)
fix(data/num/lemmas): fix formatting
#### Estimated changes
Modified data/num/lemmas.lean
- \+/\- *theorem* pos_num.cast_one'
- \+/\- *theorem* pos_num.cast_one
- \+ *theorem* pos_num.one_add



## [2018-06-13 00:32:23+07:00](https://github.com/leanprover-community/mathlib/commit/4f32a4b)
feat(data/num/basic): to_nat' function for efficient nat -> num in VM
#### Estimated changes
Modified data/num/basic.lean
- \+ *def* num.of_nat'
- \+ *def* znum.of_int'

Modified data/num/lemmas.lean
- \+ *theorem* num.cast_zero'
- \+ *theorem* num.of_nat'_eq
- \+ *theorem* num.of_nat_cast
- \+ *theorem* pos_num.cast_one'
- \+ *theorem* znum.cast_zero'
- \+ *theorem* znum.of_int'_eq
- \+ *theorem* znum.of_int_cast
- \+ *theorem* znum.of_nat_cast



## [2018-06-12 22:37:08+07:00](https://github.com/leanprover-community/mathlib/commit/99101ea)
feat(data/num/basic): add div,mod,gcd for num,znum
#### Estimated changes
Modified algebra/ordered_ring.lean
- \+ *lemma* mul_lt_mul''

Modified data/int/basic.lean
- \+ *theorem* int.coe_nat_div
- \+ *theorem* int.mem_to_nat'
- \+/\- *theorem* int.neg_succ_of_nat_div
- \+/\- *theorem* int.of_nat_div
- \+ *def* int.to_nat'

Modified data/num/basic.lean
- \+ *def* num.div2
- \+ *def* num.div
- \+ *def* num.gcd
- \+ *def* num.gcd_aux
- \+ *def* num.mod
- \+ *def* num.nat_size
- \+ *def* pos_num.div'
- \+ *def* pos_num.divmod
- \+ *def* pos_num.divmod_aux
- \+ *def* pos_num.mod'
- \+ *def* pos_num.nat_size
- \+ *def* pos_num.sqrt_aux1
- \+ *def* pos_num.sqrt_aux
- \+ *def* znum.abs
- \+ *def* znum.div
- \+ *def* znum.gcd
- \+ *def* znum.mod

Modified data/num/lemmas.lean
- \+ *theorem* num.cast_bit0
- \+ *theorem* num.cast_bit1
- \+ *theorem* num.cast_of_znum
- \+ *theorem* num.cast_pos
- \+ *theorem* num.div_to_nat
- \+ *theorem* num.dvd_iff_mod_eq_zero
- \+ *theorem* num.dvd_to_nat
- \+ *theorem* num.gcd_to_nat
- \+ *theorem* num.gcd_to_nat_aux
- \+ *theorem* num.mem_of_znum'
- \+ *theorem* num.mod_to_nat
- \+ *theorem* num.nat_size_to_nat
- \+/\- *theorem* num.of_nat_to_znum
- \+/\- *theorem* num.of_nat_to_znum_neg
- \+ *theorem* num.of_znum'_to_nat
- \+ *theorem* num.of_znum_to_nat
- \+ *theorem* num.size_eq_nat_size
- \+ *theorem* num.size_to_nat
- \+ *theorem* num.sub_to_nat
- \+ *theorem* num.to_nat_to_int
- \+/\- *theorem* pos_num.cast_inj
- \+ *theorem* pos_num.div'_to_nat
- \+ *theorem* pos_num.divmod_to_nat
- \+ *theorem* pos_num.divmod_to_nat_aux
- \+ *theorem* pos_num.mod'_to_nat
- \+ *theorem* pos_num.nat_size_pos
- \+ *theorem* pos_num.nat_size_to_nat
- \+ *theorem* pos_num.size_eq_nat_size
- \+ *theorem* pos_num.to_int_eq_succ_pred
- \+ *theorem* pos_num.to_nat_eq_succ_pred
- \+ *theorem* pos_num.to_nat_to_int
- \+ *theorem* znum.abs_to_nat
- \+ *theorem* znum.div_to_int
- \+ *theorem* znum.dvd_iff_mod_eq_zero
- \+ *theorem* znum.dvd_to_int
- \+ *theorem* znum.gcd_to_nat
- \+ *theorem* znum.mod_to_int



## [2018-06-12 22:37:08+07:00](https://github.com/leanprover-community/mathlib/commit/3c554a3)
refactor(data/equiv): move subtype.map
#### Estimated changes
Modified data/equiv.lean
- \+/\- *def* equiv.decidable_eq_of_equiv
- \+/\- *def* equiv.inhabited_of_equiv
- \- *def* subtype.map
- \- *theorem* subtype.map_comp
- \- *theorem* subtype.map_id

Modified data/sigma/basic.lean
- \+ *def* subtype.map
- \+ *theorem* subtype.map_comp
- \+ *theorem* subtype.map_id



## [2018-06-12 22:37:08+07:00](https://github.com/leanprover-community/mathlib/commit/0865bce)
fix(tactic/ring): fix normalization bugs
fixes [#84](https://github.com/leanprover-community/mathlib/pull/84)
#### Estimated changes
Modified tactic/ring.lean
- \+/\- *theorem* tactic.ring.horner_add_horner_gt
- \+/\- *theorem* tactic.ring.horner_add_horner_lt



## [2018-06-11 14:05:37+07:00](https://github.com/leanprover-community/mathlib/commit/90fc912)
feat(data/list): add parametricity for perm
#### Estimated changes
Modified data/list/perm.lean
- \+ *lemma* list.forall₂_comp_perm_eq_perm_comp_forall₂
- \+ *lemma* list.perm_comp_forall₂
- \+ *lemma* list.perm_comp_perm
- \+ *lemma* list.rel_perm
- \+ *lemma* list.rel_perm_imp



## [2018-06-11 14:05:37+07:00](https://github.com/leanprover-community/mathlib/commit/9546e62)
feat(data/list): add parametricity rules for list operations
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* list.bi_unique_forall₂
- \+ *theorem* list.filter_map_cons
- \+ *lemma* list.forall₂_cons_left_iff
- \+ *lemma* list.forall₂_cons_right_iff
- \+ *lemma* list.forall₂_eq_eq_eq
- \+ *lemma* list.forall₂_flip
- \+ *lemma* list.forall₂_map_left_iff
- \+ *lemma* list.forall₂_map_right_iff
- \- *theorem* list.forall₂_nil_left
- \+ *lemma* list.forall₂_nil_left_iff
- \- *theorem* list.forall₂_nil_right
- \+ *lemma* list.forall₂_nil_right_iff
- \+ *lemma* list.forall₂_refl
- \+ *lemma* list.forall₂_same
- \+ *lemma* list.left_unique_forall₂
- \+ *lemma* list.rel_append
- \+ *lemma* list.rel_bind
- \+ *lemma* list.rel_filter
- \+ *lemma* list.rel_filter_map
- \+ *lemma* list.rel_foldl
- \+ *lemma* list.rel_foldr
- \+ *lemma* list.rel_join
- \+ *lemma* list.rel_map
- \+ *lemma* list.rel_mem
- \+ *lemma* list.rel_nodup
- \+ *lemma* list.rel_prod
- \+ *lemma* list.rel_sections
- \+ *lemma* list.right_unique_forall₂



## [2018-06-11 14:05:09+07:00](https://github.com/leanprover-community/mathlib/commit/1416ebb)
feat(data/option): add relator option.rel
#### Estimated changes
Modified data/option.lean




## [2018-06-11 14:04:44+07:00](https://github.com/leanprover-community/mathlib/commit/205e3b4)
feat(logic/relation): add relation composition, map, and bi_unique
#### Estimated changes
Modified logic/relation.lean
- \+ *def* relation.comp
- \+ *lemma* relation.comp_assoc
- \+ *lemma* relation.comp_eq
- \+ *lemma* relation.comp_iff
- \+ *lemma* relation.eq_comp
- \+ *lemma* relation.flip_comp
- \+ *lemma* relation.iff_comp

Added logic/relator.lean
- \+ *def* relator.bi_unique
- \+ *lemma* relator.left_unique_flip
- \+ *lemma* relator.rel_and
- \+ *lemma* relator.rel_eq
- \+ *lemma* relator.rel_iff
- \+ *lemma* relator.rel_or



## [2018-06-02 10:36:21-04:00](https://github.com/leanprover-community/mathlib/commit/344192a)
refactor(computability): move out of data directory
#### Estimated changes
Renamed data/computability/halting.lean to computability/halting.lean


Renamed data/computability/partrec.lean to computability/partrec.lean


Renamed data/computability/partrec_code.lean to computability/partrec_code.lean


Renamed data/computability/primrec.lean to computability/primrec.lean


Renamed data/computability/turing_machine.lean to computability/turing_machine.lean




## [2018-06-02 10:36:16-04:00](https://github.com/leanprover-community/mathlib/commit/5603595)
feat(computability/turing_machine): proving the TM reductions
#### Estimated changes
Modified data/computability/turing_machine.lean
- \+ *def* turing.TM0.eval
- \+ *def* turing.TM0.machine
- \+ *def* turing.TM0.reaches
- \+/\- *def* turing.TM0.step
- \+ *def* turing.TM1.eval
- \+ *def* turing.TM1.reaches
- \+/\- *def* turing.TM1.step
- \+/\- *theorem* turing.TM1.step_supports
- \+ *theorem* turing.TM1.stmts_supports_stmt
- \+ *theorem* turing.TM1.stmts_trans
- \+/\- *theorem* turing.TM1.stmts₁_self
- \+ *theorem* turing.TM1.stmts₁_supports_stmt_mono
- \+ *theorem* turing.TM1.stmts₁_trans
- \+/\- *def* turing.TM1.supports
- \+/\- *def* turing.TM1.supports_stmt
- \+ *def* turing.TM1to0.tr'
- \+ *def* turing.TM1to0.tr
- \+ *def* turing.TM1to0.tr_cfg
- \+ *theorem* turing.TM1to0.tr_reaches
- \+ *theorem* turing.TM1to0.tr_supports
- \- *def* turing.TM1to0.trans
- \- *def* turing.TM1to0.translate
- \+ *def* turing.TM1to0.Λ'
- \+ *def* turing.TM2.eval
- \+ *theorem* turing.TM2.move_until_left_reaches
- \+ *theorem* turing.TM2.move_until_right_reaches
- \+ *def* turing.TM2.reaches
- \+/\- *def* turing.TM2.step
- \+/\- *def* turing.TM2.step_aux
- \+ *theorem* turing.TM2.step_supports
- \+ *theorem* turing.TM2.stmts_supports_stmt
- \+ *theorem* turing.TM2.stmts_trans
- \+ *theorem* turing.TM2.stmts₁_self
- \+ *theorem* turing.TM2.stmts₁_supports_stmt_mono
- \+ *theorem* turing.TM2.stmts₁_trans
- \+ *def* turing.TM2.supports
- \+ *def* turing.TM2.supports_stmt
- \+ *def* turing.TM2to1.tr'
- \+ *def* turing.TM2to1.tr
- \+ *def* turing.TM2to1.tr_cfg
- \+ *theorem* turing.TM2to1.tr_reaches
- \+ *theorem* turing.TM2to1.tr_supports
- \- *def* turing.TM2to1.translate'
- \- *def* turing.TM2to1.translate
- \+ *def* turing.TM2to1.Λ'
- \+ *def* turing.TM3.eval
- \+ *def* turing.TM3.reaches
- \+/\- *def* turing.TM3.step
- \+/\- *def* turing.TM3.step_aux
- \+ *theorem* turing.TM3.step_supports
- \+ *theorem* turing.TM3.stmts_supports_stmt
- \+ *theorem* turing.TM3.stmts_trans
- \+ *theorem* turing.TM3.stmts₁_self
- \+ *theorem* turing.TM3.stmts₁_supports_stmt_mono
- \+ *theorem* turing.TM3.stmts₁_trans
- \+ *def* turing.TM3.supports
- \+ *def* turing.TM3.supports_stmt
- \+ *theorem* turing.TM3to2.at_stack_supports
- \+ *def* turing.TM3to2.stack_val
- \+ *def* turing.TM3to2.tr
- \+ *theorem* turing.TM3to2.tr_supports
- \+ *def* turing.TM3to2.tr_tape
- \- *def* turing.TM3to2.translate
- \+ *def* turing.TM3to2.Γ'.write_stack
- \+ *def* turing.TM3to2.Γ'_equiv
- \+ *def* turing.TM3to2.Λ'
- \+ *def* turing.eval
- \- *def* turing.move_tape
- \+ *def* turing.tape.mk
- \+ *def* turing.tape.move
- \+ *theorem* turing.tape.move_left_nth
- \+ *theorem* turing.tape.move_right_nth
- \+ *def* turing.tape.nth
- \+ *def* turing.tape.write
- \+ *theorem* turing.tape.write_nth
- \+ *theorem* turing.tape.write_self
- \+ *def* turing.tape

Modified data/equiv.lean
- \+/\- *def* equiv.d_array_equiv_fin

Modified data/finset.lean
- \+/\- *lemma* finset.pi_insert

Modified data/fintype.lean
- \+ *theorem* fintype.card_option

Modified data/multiset.lean


Modified logic/basic.lean
- \- *theorem* exists_eq'
- \+/\- *theorem* exists_eq
- \+ *theorem* exists_eq_left'
- \+ *theorem* exists_eq_left

Modified logic/relation.lean
- \+ *lemma* relation.refl_trans_gen_closed
- \+ *lemma* relation.refl_trans_gen_eq_self
- \+ *lemma* relation.refl_trans_gen_idem
- \+ *lemma* relation.refl_trans_gen_lift'
- \- *lemma* relation.refl_trans_gen_refl_trans_gen



## [2018-06-01 22:49:29-04:00](https://github.com/leanprover-community/mathlib/commit/dd1c558)
feat(algebra/ordered_group): with_bot as an ordered monoid
#### Estimated changes
Modified algebra/ordered_group.lean




## [2018-06-01 22:48:49-04:00](https://github.com/leanprover-community/mathlib/commit/372bdab)
feat(algebra/archimedean): some more floor thms
#### Estimated changes
Modified algebra/archimedean.lean
- \+ *theorem* floor_one
- \+ *theorem* floor_zero
- \+ *theorem* rat.cast_floor

