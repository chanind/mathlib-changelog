## [2018-06-30 23:04:40-04:00](https://github.com/leanprover-community/mathlib/commit/7b0c150)
refactor(data/equiv): reorganize data.equiv deps
#### Estimated changes
Modified computability/primrec.lean

Modified data/array/lemmas.lean
- \+ *def* d_array_equiv_fin
- \+ *def* array_equiv_fin

Renamed data/equiv.lean to data/equiv/basic.lean
- \- *theorem* left_inverse.f_g_eq_id
- \- *theorem* right_inverse.g_f_eq_id
- \- *theorem* left_inverse.comp
- \- *theorem* right_inverse.comp
- \- *def* nat_prod_nat_equiv_nat
- \- *def* nat_sum_bool_equiv_nat
- \- *def* bool_prod_nat_equiv_nat
- \- *def* nat_sum_nat_equiv_nat
- \- *def* int_equiv_nat
- \- *def* prod_equiv_of_equiv_nat
- \- *def* vector_equiv_fin
- \- *def* d_array_equiv_fin
- \- *def* array_equiv_fin
- \- *def* vector_equiv_array

Created data/equiv/denumerable.lean
- \+ *theorem* decode_is_some
- \+ *theorem* decode_eq_of_nat
- \+ *theorem* of_nat_of_decode
- \+ *theorem* encode_of_nat
- \+ *theorem* of_nat_encode
- \+ *theorem* of_equiv_of_nat
- \+ *theorem* of_nat_nat
- \+ *theorem* sigma_of_nat_val
- \+ *theorem* prod_of_nat_val
- \+ *theorem* prod_nat_of_nat
- \+ *def* of_nat
- \+ *def* eqv
- \+ *def* mk'
- \+ *def* of_equiv
- \+ *def* equiv₂
- \+ *def* pair

Renamed data/encodable.lean to data/equiv/encodable.lean
- \- *theorem* encode_list_nil
- \- *theorem* encode_list_cons
- \- *theorem* decode_list_zero
- \- *theorem* decode_list_succ
- \- *theorem* length_le_encode
- \- *def* encode_list
- \- *def* decode_list
- \- *def* encode_multiset
- \- *def* decode_multiset
- \- *def* encodable_of_list
- \- *def* trunc_encodable_of_fintype

Renamed data/denumerable.lean to data/equiv/list.lean
- \+ *theorem* encode_list_nil
- \+ *theorem* encode_list_cons
- \+ *theorem* decode_list_zero
- \+ *theorem* decode_list_succ
- \+ *theorem* length_le_encode
- \- *theorem* decode_is_some
- \- *theorem* decode_eq_of_nat
- \- *theorem* of_nat_of_decode
- \- *theorem* encode_of_nat
- \- *theorem* of_nat_encode
- \- *theorem* of_equiv_of_nat
- \- *theorem* of_nat_nat
- \- *theorem* sigma_of_nat_val
- \- *theorem* prod_of_nat_val
- \- *theorem* prod_nat_of_nat
- \+ *def* encode_list
- \+ *def* decode_list
- \+ *def* encode_multiset
- \+ *def* decode_multiset
- \+ *def* encodable_of_list
- \+ *def* trunc_encodable_of_fintype
- \- *def* of_nat
- \- *def* eqv
- \- *def* mk'
- \- *def* of_equiv
- \- *def* equiv₂
- \- *def* pair

Created data/equiv/nat.lean
- \+ *def* nat_prod_nat_equiv_nat
- \+ *def* bool_prod_nat_equiv_nat
- \+ *def* nat_sum_nat_equiv_nat
- \+ *def* int_equiv_nat
- \+ *def* prod_equiv_of_equiv_nat

Modified data/erased.lean

Modified data/fintype.lean

Modified data/rat.lean

Modified data/real/cau_seq.lean

Modified data/set/basic.lean
- \+ *lemma* image_congr
- \+ *lemma* subtype_val_image
- \+ *lemma* subtype_val_range

Modified data/set/countable.lean

Modified data/set/enumerate.lean

Modified data/set/lattice.lean
- \- *lemma* image_congr
- \- *lemma* subtype_val_image
- \- *lemma* subtype_val_range

Modified data/vector2.lean
- \+ *def* vector_equiv_fin
- \+ *def* vector_equiv_array

Modified group_theory/coset.lean

Modified group_theory/free_group.lean

Modified logic/embedding.lean

Modified logic/function.lean
- \+ *theorem* left_inverse.comp_eq_id
- \+ *theorem* right_inverse.comp_eq_id
- \+ *theorem* left_inverse.comp
- \+ *theorem* right_inverse.comp

Modified order/order_iso.lean



## [2018-06-30 00:43:36-04:00](https://github.com/leanprover-community/mathlib/commit/913f702)
feat(computability/turing_machine): rework proofs, simplify TM lang
#### Estimated changes
Modified algebra/group_power.lean

Modified computability/turing_machine.lean
- \+ *theorem* reaches₁_eq
- \+ *theorem* reaches_total
- \+ *theorem* mem_eval
- \+ *theorem* eval_maximal₁
- \+ *theorem* eval_maximal
- \+ *theorem* reaches_eval
- \+ *theorem* tr_reaches₁
- \+/\- *theorem* tr_reaches
- \+ *theorem* tr_reaches_rev
- \+ *theorem* tr_eval
- \+ *theorem* tr_eval_rev
- \+ *theorem* tr_eval_dom
- \+ *theorem* frespects_eq
- \+ *theorem* fun_respects
- \+ *theorem* tr_eval'
- \+ *theorem* tr_respects
- \+/\- *theorem* tr_supports
- \+ *theorem* tr_eval
- \+ *theorem* {l}
- \+ *theorem* supports_run
- \+ *theorem* step_run
- \+ *theorem* tr_normal_run
- \+ *theorem* tr_respects_aux₁
- \+ *theorem* tr_respects_aux₂
- \+ *theorem* tr_respects_aux₃
- \+ *theorem* tr_respects_aux
- \+ *theorem* tr_respects
- \+ *theorem* tr_cfg_init
- \+ *theorem* tr_eval_dom
- \+ *theorem* tr_eval
- \+ *theorem* tr_stmts₁_run
- \+/\- *theorem* tr_supports
- \+/\- *theorem* tr_reaches
- \+/\- *theorem* tr_supports
- \- *theorem* reaches₁_step
- \- *theorem* move_until_left_reaches₁
- \- *theorem* move_until_right_reaches₁
- \- *theorem* stmts₁_self
- \- *theorem* stmts₁_trans
- \- *theorem* stmts₁_supports_stmt_mono
- \- *theorem* stmts_trans
- \- *theorem* stmts_supports_stmt
- \- *theorem* step_supports
- \+/\- *theorem* tr_reaches
- \+/\- *theorem* tr_supports
- \+/\- *theorem* tr_reaches
- \+/\- *theorem* tr_supports
- \+/\- *def* reaches
- \+/\- *def* reaches₁
- \+ *def* respects
- \+ *def* frespects
- \+ *def* init
- \+/\- *def* eval
- \+/\- *def* step_aux
- \+ *def* init
- \+/\- *def* eval
- \+/\- *def* Λ'
- \+ *def* tr_aux
- \+/\- *def* tr
- \+/\- *def* tr_cfg
- \+ *def* init
- \+/\- *def* eval
- \+ *def* st_run
- \+ *def* st_var
- \+ *def* st_write
- \+ *def* tr_st_act
- \+ *def* tr_init
- \+ *def* Λ'_inh
- \+ *def* tr_normal
- \+/\- *def* tr
- \- *def* rev
- \+/\- *def* eval
- \+/\- *def* reaches
- \+/\- *def* eval
- \+/\- *def* Λ'
- \- *def* tr'
- \+/\- *def* tr
- \+/\- *def* tr_cfg
- \+/\- *def* step_aux
- \- *def* step
- \+/\- *def* reaches
- \+/\- *def* reaches₁
- \+/\- *def* eval
- \- *def* supports_stmt
- \- *def* supports
- \+/\- *def* Λ'
- \- *def* tr'
- \+/\- *def* tr
- \+/\- *def* tr_cfg
- \+/\- *def* eval
- \+/\- *def* Λ'
- \- *def* at_stack
- \+/\- *def* tr

Modified data/fintype.lean
- \+ *theorem* finset.mem_insert_none
- \+ *theorem* finset.some_mem_insert_none
- \+ *def* finset.insert_none

Modified data/list/basic.lean
- \+/\- *theorem* join_append
- \+ *theorem* repeat_succ
- \+/\- *theorem* repeat_add
- \+ *theorem* map_repeat
- \+ *theorem* tail_repeat
- \+ *theorem* reverse_core_eq
- \+ *theorem* map_reverse_core
- \+ *theorem* map_tail
- \+/\- *theorem* join_append
- \+/\- *theorem* repeat_add

Modified data/option.lean
- \+ *theorem* mem_unique
- \+ *theorem* eq_none_iff_forall_not_mem

Modified data/pfun.lean
- \+/\- *theorem* fix_induction
- \+/\- *theorem* fix_induction

Modified logic/relation.lean
- \+ *lemma* total_of_right_unique



## [2018-06-30 00:36:55-04:00](https://github.com/leanprover-community/mathlib/commit/cfb5dfd)
refactor(data/finset): use partial_order to define lattice structure
#### Estimated changes
Modified data/finset.lean



## [2018-06-30 00:36:27-04:00](https://github.com/leanprover-community/mathlib/commit/ddbb813)
feat(data/fintype): finite choices, computably
#### Estimated changes
Modified data/fintype.lean
- \+ *theorem* quotient.fin_choice_aux_eq
- \+ *theorem* quotient.fin_choice_eq
- \+ *def* quotient.fin_choice_aux
- \+ *def* quotient.fin_choice

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
- \+/\- *lemma* coe_image
- \+/\- *lemma* coe_bind
- \+/\- *lemma* coe_filter
- \+/\- *lemma* coe_to_finset
- \+/\- *lemma* coe_insert
- \+/\- *lemma* coe_erase
- \+/\- *lemma* coe_sdiff
- \+/\- *lemma* coe_singleton
- \+/\- *lemma* coe_union
- \+/\- *lemma* coe_inter
- \+/\- *lemma* coe_insert
- \+/\- *lemma* coe_erase
- \+/\- *lemma* coe_sdiff
- \+/\- *lemma* coe_singleton
- \+/\- *lemma* coe_union
- \+/\- *lemma* coe_inter
- \+/\- *lemma* coe_image
- \+/\- *lemma* coe_bind
- \+/\- *lemma* coe_filter
- \+/\- *lemma* coe_to_finset



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
- \+ *theorem* map_subset



## [2018-06-25 05:35:22-04:00](https://github.com/leanprover-community/mathlib/commit/4ec65f5)
fix(data/list/basic): simplify last_append, speed up build
#### Estimated changes
Modified data/list/basic.lean



## [2018-06-25 05:29:11-04:00](https://github.com/leanprover-community/mathlib/commit/516b254)
feat(tactic/ring2): alternative ring tactic
#### Estimated changes
Modified data/num/lemmas.lean

Created tactic/ring2.lean
- \+ *theorem* cseval_atom
- \+ *theorem* cseval_add_const
- \+ *theorem* cseval_horner'
- \+ *theorem* cseval_add
- \+ *theorem* cseval_mul_const
- \+ *theorem* cseval_mul
- \+ *theorem* cseval_pow
- \+ *theorem* cseval_of_csexpr
- \+ *theorem* correctness
- \+ *def* tree.get
- \+ *def* tree.of_rbnode
- \+ *def* tree.index_of
- \+ *def* eval
- \+ *def* is_cs
- \+ *def* atom
- \+ *def* repr
- \+ *def* horner'
- \+ *def* add_const
- \+ *def* add_aux
- \+ *def* add
- \+ *def* neg
- \+ *def* mul_const
- \+ *def* mul_aux
- \+ *def* mul
- \+ *def* pow
- \+ *def* inv
- \+ *def* of_csexpr
- \+ *def* cseval



## [2018-06-21 08:06:52-04:00](https://github.com/leanprover-community/mathlib/commit/4082136)
feat(tactic/refine_struct): match `{ .. }` in subexpressions ([#162](https://github.com/leanprover-community/mathlib/pull/162))
#### Estimated changes
Modified tactic/interactive.lean

Modified tests/tactics.lean
- \+ *def* my_foo
- \+ *def* my_bar



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
Created data/char.lean

Modified data/finset.lean

Modified data/list/basic.lean
- \+/\- *theorem* reverse_cons
- \+/\- *theorem* reverse_cons'
- \+ *theorem* cons_iff
- \+ *theorem* append_right
- \+ *theorem* append_left
- \+ *theorem* imp
- \+ *theorem* to_ne
- \+ *theorem* ne_iff
- \+ *theorem* nil_lt_cons
- \+/\- *theorem* reverse_cons
- \+/\- *theorem* reverse_cons'
- \- *theorem* lex_append_right
- \- *theorem* lex_append_left
- \- *theorem* lex.imp
- \- *theorem* ne_of_lex_ne
- \- *theorem* lex_ne_iff

Modified data/list/perm.lean

Modified data/multiset.lean

Modified data/pnat.lean

Created data/string.lean
- \+ *theorem* lt_iff_to_list_lt
- \+ *theorem* le_iff_to_list_le
- \+ *theorem* to_list_inj
- \+ *def* ltb

Modified order/basic.lean
- \+/\- *theorem* is_order_connected.neg_trans
- \+/\- *theorem* is_strict_weak_order_of_is_order_connected
- \+/\- *theorem* is_order_connected.neg_trans
- \+/\- *theorem* is_strict_weak_order_of_is_order_connected



## [2018-06-19 14:32:22-04:00](https://github.com/leanprover-community/mathlib/commit/fbe1047)
feat(tactic/refine_struct): add `refine_struct` to use goal tags ([#147](https://github.com/leanprover-community/mathlib/pull/147))
#### Estimated changes
Modified algebra/pi_instances.lean

Modified category/basic.lean
- \+ *def* mmap₂

Created data/dlist/basic.lean
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
- \+ *lemma* is_comm_applicative.commutative_map
- \+ *theorem* map_map
- \+ *theorem* id_map'
- \+ *theorem* pure_id'_seq
- \+ *theorem* seq_map_assoc
- \+ *theorem* map_seq

Modified computability/partrec.lean
- \+/\- *theorem* comp
- \+/\- *theorem* comp



## [2018-06-19 08:25:55-04:00](https://github.com/leanprover-community/mathlib/commit/f22285c)
feat(algebra/pi_instances): add apply lemmas ([#149](https://github.com/leanprover-community/mathlib/pull/149))
#### Estimated changes
Modified algebra/pi_instances.lean
- \+ *lemma* mul_apply
- \+ *lemma* one_apply
- \+ *lemma* inv_apply
- \+ *lemma* add_apply
- \+ *lemma* zero_apply
- \+ *lemma* neg_apply
- \+ *lemma* smul_apply



## [2018-06-19 08:19:49-04:00](https://github.com/leanprover-community/mathlib/commit/0a0e8a5)
feat(tactic/ext): `ext` now applies to `prod`; fix `ext` on function types ([#158](https://github.com/leanprover-community/mathlib/pull/158))
#### Estimated changes
Modified analysis/metric_space.lean

Modified analysis/topology/topological_space.lean

Modified data/prod.lean
- \+ *lemma* ext_iff
- \+/\- *lemma* ext
- \+/\- *lemma* ext

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
- \+ *lemma* coinduced_id
- \+ *lemma* coinduced_compose
- \+ *lemma* quotient_map_id
- \+ *lemma* quotient_map_compose
- \+ *lemma* quotient_map_of_quotient_map_compose
- \+ *lemma* quotient_map.continuous_iff
- \+ *lemma* quotient_map_quot_mk
- \+ *lemma* continuous_quot_mk
- \+ *lemma* continuous_quot_lift
- \+ *lemma* quotient_map_quotient_mk
- \+ *lemma* continuous_quotient_mk
- \+ *lemma* continuous_quotient_lift
- \- *lemma* induced_mono
- \- *lemma* induced_sup
- \+ *def* quotient_map

Modified analysis/topology/topological_space.lean
- \+/\- *lemma* is_closed_induced_iff
- \+ *lemma* gc_induced_coinduced
- \+ *lemma* induced_mono
- \+ *lemma* coinduced_mono
- \+ *lemma* induced_bot
- \+ *lemma* induced_sup
- \+ *lemma* induced_supr
- \+ *lemma* coinduced_top
- \+ *lemma* coinduced_inf
- \+ *lemma* coinduced_infi
- \+/\- *lemma* t2_space_top
- \+/\- *lemma* is_closed_induced_iff
- \+/\- *lemma* t2_space_top
- \+/\- *def* topological_space.induced
- \+/\- *def* topological_space.coinduced
- \+/\- *def* topological_space.induced
- \+/\- *def* topological_space.coinduced



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
- \+ *theorem* is_some_none
- \+ *theorem* is_some_some
- \+ *theorem* is_none_none
- \+ *theorem* is_none_some



## [2018-06-19 08:08:36-04:00](https://github.com/leanprover-community/mathlib/commit/e1f795d)
chore(data/list/basic): minor cleanup of find variables ([#137](https://github.com/leanprover-community/mathlib/pull/137))
#### Estimated changes
Modified analysis/topology/continuity.lean

Modified analysis/topology/uniform_space.lean

Modified category/basic.lean
- \- *lemma* is_comm_applicative.commutative_map
- \- *theorem* map_map
- \- *theorem* id_map'
- \- *theorem* pure_id'_seq
- \- *theorem* seq_map_assoc
- \- *theorem* map_seq

Modified computability/partrec.lean
- \+/\- *theorem* comp
- \+/\- *theorem* comp

Modified data/list/basic.lean
- \+/\- *theorem* find_nil
- \+/\- *theorem* find_cons_of_pos
- \+/\- *theorem* find_cons_of_neg
- \+/\- *theorem* find_eq_none
- \+/\- *theorem* find_some
- \+/\- *theorem* find_mem
- \+/\- *theorem* find_nil
- \+/\- *theorem* find_cons_of_pos
- \+/\- *theorem* find_cons_of_neg
- \+/\- *theorem* find_eq_none
- \+/\- *theorem* find_some
- \+/\- *theorem* find_mem
- \+/\- *def* find
- \+/\- *def* find



## [2018-06-17 10:20:07-04:00](https://github.com/leanprover-community/mathlib/commit/896455c)
feat(category): add functor_norm simp_attr, and class is_comm_applicative
#### Estimated changes
Modified analysis/topology/continuity.lean

Modified analysis/topology/uniform_space.lean

Modified category/basic.lean
- \+ *lemma* is_comm_applicative.commutative_map
- \+ *theorem* map_map
- \+ *theorem* id_map'
- \+ *theorem* pure_id'_seq
- \+ *theorem* seq_map_assoc
- \+ *theorem* map_seq

Modified computability/partrec.lean
- \+/\- *theorem* comp
- \+/\- *theorem* comp



## [2018-06-16 17:39:03-04:00](https://github.com/leanprover-community/mathlib/commit/85bc56a)
feat(computability/turing_machine): finish stack machine proof
#### Estimated changes
Modified algebra/group_power.lean

Modified computability/turing_machine.lean
- \+ *theorem* tape.nth_zero
- \+/\- *theorem* tape.move_left_nth
- \+/\- *theorem* tape.move_right_nth
- \+/\- *theorem* tape.write_nth
- \+ *theorem* dwrite_eq
- \+ *theorem* dwrite_ne
- \+ *theorem* dwrite_self
- \+ *theorem* reaches₁_step
- \+ *theorem* move_until_left_reaches₁
- \+ *theorem* move_until_right_reaches₁
- \+/\- *theorem* tape.move_left_nth
- \+/\- *theorem* tape.move_right_nth
- \+/\- *theorem* tape.write_nth
- \- *theorem* move_until_left_reaches
- \- *theorem* move_until_right_reaches
- \- *theorem* at_stack_supports
- \+ *def* dwrite
- \+ *def* reaches₁
- \+/\- *def* eval
- \+/\- *def* stackel.is_bottom
- \+/\- *def* stackel.is_top
- \+/\- *def* stackel.get
- \+/\- *def* stackel_equiv
- \+ *def* Γ'
- \+/\- *def* at_stack
- \+ *def* tr_stk
- \+/\- *def* eval
- \+/\- *def* stackel.is_bottom
- \+/\- *def* stackel.is_top
- \+/\- *def* stackel.get
- \- *def* stack_val
- \+/\- *def* stackel_equiv
- \- *def* Γ'.write_stack
- \- *def* Γ'_equiv
- \+/\- *def* at_stack
- \- *def* push
- \- *def* pop
- \- *def* tr_tape

Modified data/list/basic.lean
- \+ *theorem* map_eq_append_split
- \+ *theorem* repeat_add

Modified group_theory/free_group.lean

Modified logic/relation.lean
- \+ *lemma* to_refl
- \+ *lemma* trans_left
- \+ *lemma* trans
- \+ *lemma* head'
- \+ *lemma* tail'
- \+ *lemma* trans_right
- \+ *lemma* head
- \+ *lemma* tail'_iff
- \+ *lemma* head'_iff
- \+ *lemma* refl_trans_gen_iff_eq_or_trans_gen



## [2018-06-15 05:11:08+07:00](https://github.com/leanprover-community/mathlib/commit/fba4d89)
fix(analysis/topology/continuity): remove unused code
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+/\- *lemma* continuous_apply
- \+/\- *lemma* continuous_apply



## [2018-06-13 01:28:56+07:00](https://github.com/leanprover-community/mathlib/commit/fe590ca)
fix(data/num/lemmas): fix formatting
#### Estimated changes
Modified data/num/lemmas.lean



## [2018-06-13 00:32:23+07:00](https://github.com/leanprover-community/mathlib/commit/4f32a4b)
feat(data/num/basic): to_nat' function for efficient nat -> num in VM
#### Estimated changes
Modified data/num/basic.lean

Modified data/num/lemmas.lean



## [2018-06-12 22:37:08+07:00](https://github.com/leanprover-community/mathlib/commit/99101ea)
feat(data/num/basic): add div,mod,gcd for num,znum
#### Estimated changes
Modified algebra/ordered_ring.lean
- \+ *lemma* mul_lt_mul''

Modified data/int/basic.lean
- \+/\- *theorem* of_nat_div
- \+ *theorem* coe_nat_div
- \+/\- *theorem* neg_succ_of_nat_div
- \+ *theorem* mem_to_nat'
- \+/\- *theorem* of_nat_div
- \+/\- *theorem* neg_succ_of_nat_div
- \+ *def* to_nat'

Modified data/num/basic.lean
- \+ *def* sqrt_aux
- \+ *def* sqrt

Modified data/num/lemmas.lean



## [2018-06-12 22:37:08+07:00](https://github.com/leanprover-community/mathlib/commit/3c554a3)
refactor(data/equiv): move subtype.map
#### Estimated changes
Modified data/equiv.lean
- \- *theorem* map_comp
- \- *theorem* map_id
- \+/\- *def* decidable_eq_of_equiv
- \+/\- *def* inhabited_of_equiv
- \- *def* map
- \+/\- *def* decidable_eq_of_equiv
- \+/\- *def* inhabited_of_equiv

Modified data/sigma/basic.lean
- \+ *theorem* map_comp
- \+ *theorem* map_id
- \+ *def* map



## [2018-06-12 22:37:08+07:00](https://github.com/leanprover-community/mathlib/commit/0865bce)
fix(tactic/ring): fix normalization bugs
fixes [#84](https://github.com/leanprover-community/mathlib/pull/84)
#### Estimated changes
Modified tactic/ring.lean
- \+/\- *theorem* horner_add_horner_lt
- \+/\- *theorem* horner_add_horner_gt
- \+/\- *theorem* horner_add_horner_lt
- \+/\- *theorem* horner_add_horner_gt



## [2018-06-11 14:05:37+07:00](https://github.com/leanprover-community/mathlib/commit/90fc912)
feat(data/list): add parametricity for perm
#### Estimated changes
Modified data/list/perm.lean
- \+ *lemma* perm_comp_perm
- \+ *lemma* perm_comp_forall₂
- \+ *lemma* forall₂_comp_perm_eq_perm_comp_forall₂
- \+ *lemma* rel_perm_imp
- \+ *lemma* rel_perm



## [2018-06-11 14:05:37+07:00](https://github.com/leanprover-community/mathlib/commit/9546e62)
feat(data/list): add parametricity rules for list operations
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* forall₂_flip
- \+ *lemma* forall₂_same
- \+ *lemma* forall₂_refl
- \+ *lemma* forall₂_eq_eq_eq
- \+ *lemma* forall₂_nil_left_iff
- \+ *lemma* forall₂_nil_right_iff
- \+ *lemma* forall₂_cons_left_iff
- \+ *lemma* forall₂_cons_right_iff
- \+ *lemma* forall₂_map_left_iff
- \+ *lemma* forall₂_map_right_iff
- \+ *lemma* left_unique_forall₂
- \+ *lemma* right_unique_forall₂
- \+ *lemma* bi_unique_forall₂
- \+ *lemma* rel_mem
- \+ *lemma* rel_map
- \+ *lemma* rel_append
- \+ *lemma* rel_join
- \+ *lemma* rel_bind
- \+ *lemma* rel_foldl
- \+ *lemma* rel_foldr
- \+ *lemma* rel_filter
- \+ *lemma* rel_filter_map
- \+ *lemma* rel_prod
- \+ *lemma* rel_sections
- \+ *lemma* rel_nodup
- \+ *theorem* filter_map_cons
- \- *theorem* forall₂_nil_left
- \- *theorem* forall₂_nil_right



## [2018-06-11 14:05:09+07:00](https://github.com/leanprover-community/mathlib/commit/1416ebb)
feat(data/option): add relator option.rel
#### Estimated changes
Modified data/option.lean



## [2018-06-11 14:04:44+07:00](https://github.com/leanprover-community/mathlib/commit/205e3b4)
feat(logic/relation): add relation composition, map, and bi_unique
#### Estimated changes
Modified logic/relation.lean
- \+ *lemma* comp_eq
- \+ *lemma* eq_comp
- \+ *lemma* iff_comp
- \+ *lemma* comp_iff
- \+ *lemma* comp_assoc
- \+ *lemma* flip_comp
- \+ *def* comp

Created logic/relator.lean
- \+ *lemma* left_unique_flip
- \+ *lemma* rel_and
- \+ *lemma* rel_or
- \+ *lemma* rel_iff
- \+ *lemma* rel_eq
- \+ *def* bi_unique



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
- \+ *theorem* tape.move_left_nth
- \+ *theorem* tape.move_right_nth
- \+ *theorem* tape.write_self
- \+ *theorem* tape.write_nth
- \+/\- *theorem* stmts₁_self
- \+ *theorem* stmts₁_trans
- \+ *theorem* stmts₁_supports_stmt_mono
- \+ *theorem* stmts_trans
- \+ *theorem* stmts_supports_stmt
- \+/\- *theorem* step_supports
- \+ *theorem* tr_reaches
- \+ *theorem* tr_supports
- \+ *theorem* move_until_left_reaches
- \+ *theorem* move_until_right_reaches
- \+/\- *theorem* stmts₁_self
- \+ *theorem* stmts₁_trans
- \+ *theorem* stmts₁_supports_stmt_mono
- \+ *theorem* stmts_trans
- \+ *theorem* stmts_supports_stmt
- \+/\- *theorem* step_supports
- \+ *theorem* tr_reaches
- \+ *theorem* tr_supports
- \+/\- *theorem* stmts₁_self
- \+ *theorem* stmts₁_trans
- \+ *theorem* stmts₁_supports_stmt_mono
- \+ *theorem* stmts_trans
- \+ *theorem* stmts_supports_stmt
- \+/\- *theorem* step_supports
- \+ *theorem* tr_reaches
- \+ *theorem* at_stack_supports
- \+ *theorem* tr_supports
- \+/\- *theorem* stmts₁_self
- \+/\- *theorem* step_supports
- \+ *def* tape
- \+ *def* tape.mk
- \+ *def* tape.move
- \+ *def* tape.write
- \+ *def* tape.nth
- \+ *def* eval
- \+ *def* machine
- \+/\- *def* step
- \+ *def* reaches
- \+ *def* eval
- \+/\- *def* step
- \+ *def* reaches
- \+ *def* eval
- \+/\- *def* supports_stmt
- \+/\- *def* supports
- \+ *def* Λ'
- \+ *def* tr'
- \+ *def* tr
- \+ *def* tr_cfg
- \+/\- *def* step_aux
- \+/\- *def* step
- \+ *def* reaches
- \+ *def* eval
- \+/\- *def* supports_stmt
- \+/\- *def* supports
- \+ *def* Λ'
- \+ *def* tr'
- \+ *def* tr
- \+ *def* tr_cfg
- \+/\- *def* step_aux
- \+/\- *def* step
- \+ *def* reaches
- \+ *def* eval
- \+/\- *def* supports_stmt
- \+/\- *def* supports
- \+ *def* stack_val
- \+ *def* Γ'.write_stack
- \+ *def* Γ'_equiv
- \+ *def* Λ'
- \+ *def* tr
- \+ *def* tr_tape
- \- *def* move_tape
- \+/\- *def* step
- \+/\- *def* step
- \+/\- *def* supports_stmt
- \+/\- *def* supports
- \- *def* trans
- \- *def* translate
- \+/\- *def* step_aux
- \+/\- *def* step
- \- *def* translate'
- \- *def* translate
- \+/\- *def* step_aux
- \+/\- *def* step
- \- *def* translate

Modified data/equiv.lean
- \+/\- *def* d_array_equiv_fin
- \+/\- *def* d_array_equiv_fin

Modified data/finset.lean
- \+/\- *lemma* pi_insert
- \+/\- *lemma* pi_insert

Modified data/fintype.lean
- \+ *theorem* fintype.card_option

Modified data/multiset.lean

Modified logic/basic.lean
- \+/\- *theorem* exists_eq
- \+ *theorem* exists_eq_left
- \+ *theorem* exists_eq_left'
- \+/\- *theorem* exists_eq
- \- *theorem* exists_eq'

Modified logic/relation.lean
- \+ *lemma* refl_trans_gen_eq_self
- \+ *lemma* refl_trans_gen_idem
- \+ *lemma* refl_trans_gen_lift'
- \+ *lemma* refl_trans_gen_closed
- \- *lemma* refl_trans_gen_refl_trans_gen



## [2018-06-01 22:49:29-04:00](https://github.com/leanprover-community/mathlib/commit/dd1c558)
feat(algebra/ordered_group): with_bot as an ordered monoid
#### Estimated changes
Modified algebra/ordered_group.lean



## [2018-06-01 22:48:49-04:00](https://github.com/leanprover-community/mathlib/commit/372bdab)
feat(algebra/archimedean): some more floor thms
#### Estimated changes
Modified algebra/archimedean.lean
- \+ *theorem* floor_zero
- \+ *theorem* floor_one
- \+ *theorem* rat.cast_floor

