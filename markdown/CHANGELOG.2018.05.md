## [2018-05-31 03:00:24-04:00](https://github.com/leanprover-community/mathlib/commit/b375264)
feat(computability/turing_machine): add TMs and reductions
#### Estimated changes
Modified data/array/lemmas.lean


Modified data/computability/halting.lean


Added data/computability/turing_machine.lean
- \+ *structure* turing.TM0.machine
- \+ *structure* turing.TM0.state
- \+ *def* turing.TM0.step
- \+ *theorem* turing.TM0.step_supports
- \+ *inductive* turing.TM0.stmt
- \+ *def* turing.TM0.supports
- \+ *structure* turing.TM1.state
- \+ *def* turing.TM1.step
- \+ *theorem* turing.TM1.step_supports
- \+ *inductive* turing.TM1.stmt
- \+ *theorem* turing.TM1.stmts₁_self
- \+ *def* turing.TM1.supports
- \+ *def* turing.TM1.supports_stmt
- \+ *def* turing.TM1to0.trans
- \+ *def* turing.TM1to0.translate
- \+ *structure* turing.TM2.state
- \+ *def* turing.TM2.step
- \+ *def* turing.TM2.step_aux
- \+ *inductive* turing.TM2.stmt
- \+ *def* turing.TM2to1.translate'
- \+ *def* turing.TM2to1.translate
- \+ *structure* turing.TM3.machine
- \+ *structure* turing.TM3.state
- \+ *def* turing.TM3.step
- \+ *def* turing.TM3.step_aux
- \+ *inductive* turing.TM3.stmt
- \+ *structure* turing.TM3to2.alph
- \+ *def* turing.TM3to2.at_stack
- \+ *def* turing.TM3to2.pop
- \+ *def* turing.TM3to2.push
- \+ *def* turing.TM3to2.stackel.get
- \+ *def* turing.TM3to2.stackel.is_bottom
- \+ *def* turing.TM3to2.stackel.is_top
- \+ *inductive* turing.TM3to2.stackel
- \+ *def* turing.TM3to2.stackel_equiv
- \+ *def* turing.TM3to2.translate
- \+ *def* turing.dir.rev
- \+ *inductive* turing.dir
- \+ *def* turing.move_tape

Modified data/fintype.lean


Modified data/real/basic.lean
- \+/\- *def* real

Modified data/sum.lean




## [2018-05-30 15:29:43-04:00](https://github.com/leanprover-community/mathlib/commit/bdd54ac)
feat(data/computablility): reduced partrec
#### Estimated changes
Modified data/computability/halting.lean
- \+ *theorem* nat.partrec'.comp'
- \+ *theorem* nat.partrec'.comp₁
- \+ *theorem* nat.partrec'.head
- \+ *theorem* nat.partrec'.idv
- \+ *theorem* nat.partrec'.of_eq
- \+ *theorem* nat.partrec'.of_part
- \+ *theorem* nat.partrec'.of_prim
- \+ *theorem* nat.partrec'.part_iff
- \+ *theorem* nat.partrec'.part_iff₁
- \+ *theorem* nat.partrec'.part_iff₂
- \+ *theorem* nat.partrec'.rfind_opt
- \+ *theorem* nat.partrec'.tail
- \+ *theorem* nat.partrec'.to_part
- \+ *theorem* nat.partrec'.vec.prim
- \+ *def* nat.partrec'.vec
- \+ *theorem* nat.partrec'.vec_iff
- \+ *inductive* nat.partrec'

Modified data/computability/partrec.lean
- \+ *theorem* computable.fin_app
- \+ *theorem* computable.list_of_fn
- \+ *theorem* computable.vector_cons
- \+ *theorem* computable.vector_head
- \+ *theorem* computable.vector_length
- \+ *theorem* computable.vector_nth'
- \+ *theorem* computable.vector_nth
- \+ *theorem* computable.vector_of_fn'
- \+ *theorem* computable.vector_of_fn
- \+ *theorem* computable.vector_tail
- \+ *theorem* computable.vector_to_list
- \+ *theorem* partrec.vector_m_of_fn
- \+ *theorem* vector.m_of_fn_roption_some

Modified data/computability/partrec_code.lean
- \+ *theorem* nat.partrec.code.eval_eq_rfind_opt

Modified data/computability/primrec.lean
- \+/\- *theorem* nat.primrec'.idv
- \- *def* nat.primrec'.primvec
- \- *theorem* nat.primrec'.primvec_iff
- \+ *def* nat.primrec'.vec
- \+ *theorem* nat.primrec'.vec_iff

Modified data/vector2.lean
- \+ *theorem* vector.m_of_fn_pure
- \+ *theorem* vector.mmap_cons
- \+ *theorem* vector.mmap_nil
- \+ *def* vector.{u}



## [2018-05-29 18:57:49-04:00](https://github.com/leanprover-community/mathlib/commit/00a2eb4)
feat(algebra/group_power): mul_two_nonneg
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* pow_two_nonneg



## [2018-05-29 17:20:24-04:00](https://github.com/leanprover-community/mathlib/commit/40bd947)
feat(computability/primrec): add traditional primrec definition
This shows that the pairing function with its square roots does not give any additional power.
#### Estimated changes
Modified data/computability/primrec.lean
- \+ *theorem* nat.primrec'.add
- \+ *theorem* nat.primrec'.comp'
- \+ *theorem* nat.primrec'.comp₁
- \+ *theorem* nat.primrec'.comp₂
- \+ *theorem* nat.primrec'.const
- \+ *theorem* nat.primrec'.head
- \+ *theorem* nat.primrec'.idv
- \+ *theorem* nat.primrec'.if_lt
- \+ *theorem* nat.primrec'.mkpair
- \+ *theorem* nat.primrec'.mul
- \+ *theorem* nat.primrec'.of_eq
- \+ *theorem* nat.primrec'.of_prim
- \+ *theorem* nat.primrec'.prec'
- \+ *theorem* nat.primrec'.pred
- \+ *theorem* nat.primrec'.prim_iff
- \+ *theorem* nat.primrec'.prim_iff₁
- \+ *theorem* nat.primrec'.prim_iff₂
- \+ *def* nat.primrec'.primvec
- \+ *theorem* nat.primrec'.primvec_iff
- \+ *theorem* nat.primrec'.sqrt
- \+ *theorem* nat.primrec'.sub
- \+ *theorem* nat.primrec'.tail
- \+ *theorem* nat.primrec'.to_prim
- \+ *theorem* nat.primrec'.unpair₁
- \+ *theorem* nat.primrec'.unpair₂
- \+ *inductive* nat.primrec'
- \+ *def* primcodable.subtype
- \+ *theorem* primrec.fin_app
- \+ *theorem* primrec.fin_curry
- \+ *theorem* primrec.fin_curry₁
- \+ *theorem* primrec.fin_succ
- \+ *theorem* primrec.fin_val
- \+ *theorem* primrec.fin_val_iff
- \+ *theorem* primrec.list_head'
- \+ *theorem* primrec.list_head
- \+ *theorem* primrec.list_of_fn
- \+ *theorem* primrec.list_tail
- \+ *theorem* primrec.nat_lt
- \+ *theorem* primrec.nat_sqrt
- \+ *theorem* primrec.of_equiv
- \+ *theorem* primrec.of_equiv_iff
- \+ *theorem* primrec.of_equiv_symm
- \+ *theorem* primrec.of_equiv_symm_iff
- \+ *theorem* primrec.subtype_val
- \+ *theorem* primrec.subtype_val_iff
- \+ *theorem* primrec.vector_cons
- \+ *theorem* primrec.vector_head
- \+ *theorem* primrec.vector_length
- \+ *theorem* primrec.vector_nth'
- \+ *theorem* primrec.vector_nth
- \+ *theorem* primrec.vector_of_fn'
- \+ *theorem* primrec.vector_of_fn
- \+ *theorem* primrec.vector_tail
- \+ *theorem* primrec.vector_to_list
- \+ *theorem* primrec.vector_to_list_iff

Modified data/encodable.lean


Modified data/equiv.lean
- \+ *def* equiv.array_equiv_fin
- \+ *def* equiv.d_array_equiv_fin
- \+ *def* equiv.fin_equiv_subtype
- \+ *def* equiv.vector_equiv_array
- \+ *def* equiv.vector_equiv_fin

Modified data/fin.lean
- \+ *def* fin.cases
- \+ *theorem* fin.cases_succ
- \+ *theorem* fin.cases_zero

Modified data/list/basic.lean
- \+ *theorem* list.array_eq_of_fn
- \+/\- *theorem* list.cons_head_tail
- \+ *def* list.head'
- \+/\- *theorem* list.head_append
- \+/\- *theorem* list.head_cons
- \+ *theorem* list.head_eq_head'
- \+ *theorem* list.length_of_fn
- \+ *theorem* list.length_of_fn_aux
- \+ *theorem* list.nth_le_of_fn
- \+ *theorem* list.nth_of_fn
- \+ *theorem* list.nth_of_fn_aux
- \+ *def* list.of_fn
- \+ *def* list.of_fn_aux
- \+ *theorem* list.of_fn_nth_le
- \+ *def* list.of_fn_nth_val
- \+ *theorem* list.of_fn_succ
- \+ *theorem* list.of_fn_zero

Modified data/nat/sqrt.lean
- \+ *theorem* nat.eq_sqrt
- \+ *theorem* nat.sqrt_succ_le_succ_sqrt

Modified data/set/basic.lean
- \+/\- *theorem* set.image_empty
- \+/\- *theorem* set.image_id

Modified data/sigma/basic.lean
- \+ *lemma* subtype.ext
- \+ *theorem* subtype.val_injective

Added data/vector2.lean
- \+ *theorem* vector.head'_to_list
- \+ *theorem* vector.head_of_fn
- \+ *theorem* vector.mk_to_list
- \+ *theorem* vector.nth_cons_succ
- \+ *theorem* vector.nth_cons_zero
- \+ *theorem* vector.nth_eq_nth_le
- \+ *theorem* vector.nth_of_fn
- \+ *theorem* vector.nth_tail
- \+ *theorem* vector.nth_zero
- \+ *theorem* vector.of_fn_nth
- \+ *theorem* vector.tail_of_fn
- \+ *theorem* vector.to_list_injective
- \+ *theorem* vector.to_list_of_fn

Modified logic/embedding.lean




## [2018-05-29 17:20:24-04:00](https://github.com/leanprover-community/mathlib/commit/5fea16e)
feat(category/basic): $< notation for reversed application
#### Estimated changes
Modified category/basic.lean




## [2018-05-29 15:48:54+02:00](https://github.com/leanprover-community/mathlib/commit/a2d2537)
feat(analysis/probability_mass_function): add bernoulli
#### Estimated changes
Modified analysis/nnreal.lean


Modified analysis/probability_mass_function.lean
- \+ *def* pmf.bernoulli
- \+ *def* pmf.of_fintype



## [2018-05-29 15:08:43+02:00](https://github.com/leanprover-community/mathlib/commit/4f9e951)
feat(analysis): add probability mass functions
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.sum_nat_cast
- \+ *lemma* multiset.to_finset_sum_count_eq

Modified analysis/ennreal.lean
- \+ *lemma* ennreal.coe_eq_coe
- \+ *lemma* ennreal.coe_mul
- \+ *lemma* ennreal.coe_one
- \+ *lemma* ennreal.tendsto_coe_iff
- \+ *lemma* ennreal.tendsto_of_real_iff
- \+ *lemma* has_sum_of_nonneg_of_le
- \+ *lemma* nnreal.has_sum_of_le

Modified analysis/nnreal.lean
- \+ *lemma* nnreal.has_sum_coe
- \+ *lemma* nnreal.is_sum_coe
- \+ *lemma* nnreal.sum_coe
- \+ *lemma* nnreal.tendsto_coe

Added analysis/probability_mass_function.lean
- \+ *def* pmf.bind
- \+ *lemma* pmf.bind_apply
- \+ *lemma* pmf.bind_bind
- \+ *lemma* pmf.bind_comm
- \+ *lemma* pmf.bind_pure
- \+ *lemma* pmf.bind_pure_comp
- \+ *lemma* pmf.coe_bind_apply
- \+ *lemma* pmf.coe_le_one
- \+ *lemma* pmf.has_sum_coe
- \+ *lemma* pmf.is_sum_coe_one
- \+ *def* pmf.map
- \+ *lemma* pmf.map_comp
- \+ *lemma* pmf.map_id
- \+ *def* pmf.of_multiset
- \+ *def* pmf.pure
- \+ *lemma* pmf.pure_apply
- \+ *lemma* pmf.pure_bind
- \+ *lemma* pmf.pure_map
- \+ *def* pmf.seq
- \+ *def* pmf.support
- \+ *lemma* pmf.tsum_coe
- \+ *def* {u}

Modified analysis/topology/infinite_sum.lean
- \+ *lemma* is_sum_iff_of_has_sum
- \+ *lemma* is_sum_ite
- \+ *lemma* tsum_ite

Modified data/finset.lean
- \+ *lemma* multiset.to_finset_cons

Modified data/multiset.lean
- \+/\- *theorem* multiset.count_eq_zero_of_not_mem

Modified order/filter.lean
- \+ *lemma* filter.le_of_map_le_map_inj_iff



## [2018-05-29 04:19:54-04:00](https://github.com/leanprover-community/mathlib/commit/eaa1b93)
feat(data.list.basic): forall_mem_singleton, forall_mem_append
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.forall_mem_append
- \+ *theorem* list.forall_mem_singleton



## [2018-05-29 03:47:46-04:00](https://github.com/leanprover-community/mathlib/commit/a6be523)
feat(data/list/basic): map_erase, map_diff, map_union
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.map_diff
- \+ *theorem* list.map_erase
- \+ *theorem* list.map_foldl_erase

Modified data/multiset.lean
- \+ *theorem* multiset.map_union



## [2018-05-28 15:36:19+02:00](https://github.com/leanprover-community/mathlib/commit/0022068)
fix(tactics/wlog): allow union instead of disjunction; assume disjunction in strict associcated order; fix discharger
#### Estimated changes
Modified data/set/enumerate.lean


Modified tactic/wlog.lean


Modified tests/tactics.lean




## [2018-05-28 14:30:41+02:00](https://github.com/leanprover-community/mathlib/commit/1dbd8c6)
feat(data/equiv): image, preimage under equivalences; simp rules for perm.val  ([#102](https://github.com/leanprover-community/mathlib/pull/102))
#### Estimated changes
Modified data/equiv.lean
- \+ *theorem* equiv.left_inverse_symm
- \+ *theorem* equiv.perm.mul_val
- \+ *theorem* equiv.perm.one_val
- \+ *theorem* equiv.right_inverse_symm
- \+ *lemma* equiv.symm_image_image



## [2018-05-27 22:50:42-04:00](https://github.com/leanprover-community/mathlib/commit/c53f9f1)
refactor(algebra/euclidean_domain): clean up proofs
#### Estimated changes
Modified algebra/euclidean_domain.lean
- \+ *theorem* euclidean_domain.div_add_mod
- \+/\- *lemma* euclidean_domain.div_self
- \- *lemma* euclidean_domain.dvd_mod
- \+ *lemma* euclidean_domain.dvd_mod_iff
- \- *lemma* euclidean_domain.dvd_mod_self
- \+/\- *theorem* euclidean_domain.gcd.induction
- \- *lemma* euclidean_domain.gcd_decreasing
- \+/\- *theorem* euclidean_domain.gcd_dvd
- \+ *theorem* euclidean_domain.gcd_eq_left
- \- *theorem* euclidean_domain.gcd_next
- \+ *theorem* euclidean_domain.gcd_val
- \+ *lemma* euclidean_domain.mod_eq_zero
- \- *lemma* euclidean_domain.mod_lt
- \+/\- *lemma* euclidean_domain.mod_zero
- \+ *lemma* euclidean_domain.mul_div_cancel
- \+ *lemma* euclidean_domain.mul_div_cancel_left
- \- *lemma* euclidean_domain.neq_zero_lt_mod_lt
- \+ *theorem* euclidean_domain.val_le_mul_right
- \+ *theorem* euclidean_domain.val_mod_lt
- \+/\- *lemma* euclidean_domain.zero_div

Modified analysis/topology/infinite_sum.lean


Modified linear_algebra/multivariate_polynomial.lean
- \- *lemma* finsupp.single_induction_on



## [2018-05-27 19:47:56-04:00](https://github.com/leanprover-community/mathlib/commit/9f0d1d8)
fix(analysis/limits): fix ambiguous import (fin)set.range
#### Estimated changes
Modified analysis/limits.lean


Modified analysis/topology/infinite_sum.lean




## [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/ad92a9b)
feat(algebra/group,...): add with_zero, with_one structures
other ways to add an element to an algebraic structure:
* Add a top or bottom to an order (with_top, with_bot)
* add a unit to a semigroup (with_zero, with_one)
* add a zero to a multiplicative semigroup (with_zero)
* add an infinite element to an additive semigroup (with_top)
#### Estimated changes
Modified algebra/group.lean
- \+ *def* with_one

Modified algebra/ordered_group.lean
- \+ *def* with_zero.ordered_comm_monoid

Modified algebra/ring.lean


Modified data/option.lean


Modified order/bounded_lattice.lean
- \- *theorem* lattice.with_bot.some_le
- \- *theorem* lattice.with_bot.some_le_some
- \- *def* lattice.with_bot
- \- *theorem* lattice.with_top.le_some
- \- *theorem* lattice.with_top.some_le_some
- \- *def* lattice.with_top
- \+ *theorem* with_bot.coe_le
- \+ *theorem* with_bot.coe_le_coe
- \+ *theorem* with_bot.some_le_some
- \+ *theorem* with_bot.some_lt_some
- \+ *def* with_bot
- \+ *theorem* with_top.coe_le_coe
- \+ *theorem* with_top.le_coe
- \+ *theorem* with_top.some_le_some
- \+ *theorem* with_top.some_lt_some
- \+ *def* with_top

Modified order/lattice.lean




## [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/431d997)
feat(nat/basic): mod_mod
#### Estimated changes
Modified data/nat/basic.lean
- \+ *theorem* nat.mod_mod

Modified data/nat/modeq.lean
- \+ *theorem* nat.modeq.mod_modeq



## [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/4c1a826)
refactor(data/set/finite): use hypotheses for fintype assumptions
in simp rules
#### Estimated changes
Modified data/set/finite.lean
- \+/\- *theorem* set.card_insert
- \+ *theorem* set.empty_card'
- \+/\- *theorem* set.empty_card

Modified number_theory/pell.lean




## [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/f563ac8)
chore(data/pnat): remove nat -> pnat coercion
#### Estimated changes
Modified analysis/real.lean


Modified data/finset.lean
- \- *theorem* finset.max_eq_inf_with_top
- \+ *theorem* finset.min_eq_inf_with_top

Modified data/pnat.lean
- \- *theorem* pnat.coe_nat_coe
- \+ *theorem* pnat.coe_to_pnat'
- \- *theorem* pnat.nat_coe_coe



## [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/b7012fb)
fix(tactic/norm_num): use norm_num to discharge simp goals
#### Estimated changes
Modified tactic/norm_num.lean




## [2018-05-25 16:15:06+02:00](https://github.com/leanprover-community/mathlib/commit/6811f13)
fix(data/list/perm): remove unused code ([#143](https://github.com/leanprover-community/mathlib/pull/143))
#### Estimated changes
Modified data/list/perm.lean
- \- *theorem* list.xswap



## [2018-05-25 05:57:39-04:00](https://github.com/leanprover-community/mathlib/commit/bcec475)
chore(leanpkg.toml): update version to 3.4.1
#### Estimated changes
Modified leanpkg.toml




## [2018-05-25 05:55:41-04:00](https://github.com/leanprover-community/mathlib/commit/1991869)
feat(order/bounded_lattice): with_bot, with_top structures
#### Estimated changes
Modified data/finset.lean
- \+ *def* finset.inf
- \+ *lemma* finset.inf_empty
- \+ *lemma* finset.inf_insert
- \+ *lemma* finset.inf_le
- \+ *lemma* finset.inf_mono
- \+ *lemma* finset.inf_mono_fun
- \+ *lemma* finset.inf_singleton
- \+ *lemma* finset.inf_union
- \+ *lemma* finset.le_inf
- \+ *lemma* finset.le_sup
- \+ *theorem* finset.max_eq_inf_with_top
- \+ *theorem* finset.max_eq_sup_with_bot
- \+ *lemma* finset.singleton_bind
- \+/\- *theorem* finset.subset_iff
- \+ *def* finset.sup
- \+ *lemma* finset.sup_empty
- \+ *lemma* finset.sup_insert
- \+ *lemma* finset.sup_le
- \+ *lemma* finset.sup_mono
- \+ *lemma* finset.sup_mono_fun
- \+ *lemma* finset.sup_singleton
- \+ *lemma* finset.sup_union

Modified data/finsupp.lean
- \+ *lemma* finsupp.erase_add_single
- \+ *lemma* finsupp.induction₂
- \+/\- *lemma* finsupp.single_add_erase

Modified data/option.lean
- \+ *theorem* option.ext

Modified linear_algebra/multivariate_polynomial.lean
- \- *lemma* finset.bind_singleton2
- \- *lemma* finset.le_sup
- \- *def* finset.sup
- \- *lemma* finset.sup_empty
- \- *lemma* finset.sup_insert
- \- *lemma* finset.sup_le
- \- *lemma* finset.sup_mono
- \- *lemma* finset.sup_mono_fun
- \- *lemma* finset.sup_singleton
- \- *lemma* finset.sup_union

Modified order/bounded_lattice.lean
- \+ *theorem* lattice.with_bot.some_le
- \+ *theorem* lattice.with_bot.some_le_some
- \+ *def* lattice.with_bot
- \+ *theorem* lattice.with_top.le_some
- \+ *theorem* lattice.with_top.some_le_some
- \+ *def* lattice.with_top

Modified order/lattice.lean




## [2018-05-25 01:14:13-04:00](https://github.com/leanprover-community/mathlib/commit/94dc067)
refactor(order/lattice): move top/bot to bounded_lattice
#### Estimated changes
Modified order/bounded_lattice.lean
- \+ *theorem* lattice.bot_inf_eq
- \+ *theorem* lattice.bot_le
- \+ *theorem* lattice.bot_sup_eq
- \+ *theorem* lattice.bot_unique
- \+ *theorem* lattice.eq_bot_iff
- \+ *theorem* lattice.eq_top_iff
- \+ *theorem* lattice.inf_bot_eq
- \+ *theorem* lattice.inf_eq_top_iff
- \+ *theorem* lattice.inf_top_eq
- \+ *theorem* lattice.le_bot_iff
- \+ *theorem* lattice.le_top
- \+ *theorem* lattice.neq_bot_of_le_neq_bot
- \+ *theorem* lattice.not_lt_bot
- \+ *theorem* lattice.not_top_lt
- \+ *theorem* lattice.sup_bot_eq
- \+ *theorem* lattice.sup_eq_bot_iff
- \+ *theorem* lattice.sup_top_eq
- \+ *theorem* lattice.top_inf_eq
- \+ *theorem* lattice.top_le_iff
- \+ *theorem* lattice.top_sup_eq
- \+ *theorem* lattice.top_unique

Modified order/lattice.lean
- \- *theorem* lattice.bot_inf_eq
- \- *theorem* lattice.bot_le
- \- *theorem* lattice.bot_sup_eq
- \- *theorem* lattice.bot_unique
- \- *theorem* lattice.eq_bot_iff
- \- *theorem* lattice.eq_top_iff
- \- *theorem* lattice.inf_bot_eq
- \- *theorem* lattice.inf_eq_top_iff
- \- *theorem* lattice.inf_top_eq
- \- *theorem* lattice.le_bot_iff
- \- *theorem* lattice.le_top
- \- *theorem* lattice.neq_bot_of_le_neq_bot
- \- *theorem* lattice.not_lt_bot
- \- *theorem* lattice.not_top_lt
- \- *theorem* lattice.sup_bot_eq
- \- *theorem* lattice.sup_eq_bot_iff
- \- *theorem* lattice.sup_top_eq
- \- *theorem* lattice.top_inf_eq
- \- *theorem* lattice.top_le_iff
- \- *theorem* lattice.top_sup_eq
- \- *theorem* lattice.top_unique



## [2018-05-25 01:14:13-04:00](https://github.com/leanprover-community/mathlib/commit/4117ff4)
refactor(algebra/order_functions): reorganize new lemmas
#### Estimated changes
Modified algebra/order_functions.lean
- \+ *theorem* max_choice
- \+ *theorem* min_choice

Modified logic/basic.lean
- \- *theorem* if_choice
- \- *theorem* max_choice
- \- *theorem* min_choice

Modified order/lattice.lean




## [2018-05-24 15:55:26+02:00](https://github.com/leanprover-community/mathlib/commit/9303bc0)
feat(analysis/ennreal): add further type class instances for nonnegative reals
#### Estimated changes
Modified algebra/ordered_group.lean
- \+ *lemma* le_zero_iff_eq

Modified analysis/nnreal.lean
- \- *lemma* nnreal.add_val
- \- *lemma* nnreal.le_zero_iff_eq
- \- *lemma* nnreal.mul_val
- \- *lemma* nnreal.val_one
- \- *lemma* nnreal.val_zero

Modified set_theory/cofinality.lean




## [2018-05-24 15:55:26+02:00](https://github.com/leanprover-community/mathlib/commit/02f8f48)
feat(analysis/nnreal): define the nonnegative reals
NB: This file has a lot in common with `ennreal.lean`, the extended nonnegative reals.
#### Estimated changes
Added analysis/nnreal.lean
- \+ *lemma* nnreal.add_val
- \+ *lemma* nnreal.le_zero_iff_eq
- \+ *lemma* nnreal.mul_val
- \+ *lemma* nnreal.val_one
- \+ *lemma* nnreal.val_zero



## [2018-05-24 09:39:41+02:00](https://github.com/leanprover-community/mathlib/commit/2c94668)
fix(data/fin): rename raise_fin -> fin.raise; simp lemmas for fin ([#138](https://github.com/leanprover-community/mathlib/pull/138))
#### Estimated changes
Modified data/fin.lean
- \+ *lemma* fin.pred_val
- \+ *def* fin.raise
- \+ *lemma* fin.succ_val
- \- *def* raise_fin



## [2018-05-23 19:20:55+02:00](https://github.com/leanprover-community/mathlib/commit/d91a267)
fix(data/list/basic): protected list.sigma ([#140](https://github.com/leanprover-community/mathlib/pull/140))
#### Estimated changes
Modified data/list/basic.lean
- \- *def* list.sigma



## [2018-05-23 19:20:25+02:00](https://github.com/leanprover-community/mathlib/commit/94a4b07)
doc(docs/extras): some notes on well founded recursion ([#127](https://github.com/leanprover-community/mathlib/pull/127))
#### Estimated changes
Added docs/extras/well_founded_recursion.md




## [2018-05-23 19:16:42+02:00](https://github.com/leanprover-community/mathlib/commit/23bd3f2)
doc(docs/extra/simp): adding reference to simpa ([#106](https://github.com/leanprover-community/mathlib/pull/106))
#### Estimated changes
Modified docs/extras/simp.md




## [2018-05-23 18:54:35+02:00](https://github.com/leanprover-community/mathlib/commit/add172d)
chore(tactic/default): move split_ifs import to tactic.interactive
#### Estimated changes
Modified tactic/default.lean


Modified tactic/interactive.lean




## [2018-05-23 18:54:35+02:00](https://github.com/leanprover-community/mathlib/commit/d442907)
fix(tactic/split_if): clarify behavior
#### Estimated changes
Modified tactic/split_ifs.lean




## [2018-05-23 18:54:35+02:00](https://github.com/leanprover-community/mathlib/commit/509934f)
feat(tactic/split_ifs): add if-splitter
#### Estimated changes
Modified algebra/euclidean_domain.lean


Modified data/equiv.lean


Modified data/list/basic.lean


Modified tactic/default.lean


Added tactic/split_ifs.lean


Added tests/split_ifs.lean




## [2018-05-23 17:29:32+02:00](https://github.com/leanprover-community/mathlib/commit/f458eef)
feat(analysis/topology): add tendsto and continuity rules for big operators
#### Estimated changes
Modified analysis/measure_theory/borel_space.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* continuous_add'
- \+/\- *lemma* continuous_add
- \+ *lemma* continuous_finset_prod
- \+ *lemma* continuous_finset_sum
- \+ *lemma* continuous_list_prod
- \+ *lemma* continuous_list_sum
- \+ *lemma* continuous_mul'
- \+/\- *lemma* continuous_mul
- \+ *lemma* continuous_multiset_prod
- \+ *lemma* continuous_multiset_sum
- \+/\- *lemma* tendsto_add'
- \+/\- *lemma* tendsto_add
- \+ *lemma* tendsto_finset_prod
- \+ *lemma* tendsto_finset_sum
- \+ *lemma* tendsto_list_prod
- \+ *lemma* tendsto_list_sum
- \+ *lemma* tendsto_mul'
- \+/\- *lemma* tendsto_mul
- \+ *lemma* tendsto_multiset_prod
- \+ *lemma* tendsto_multiset_sum
- \- *lemma* tendsto_sum



## [2018-05-23 17:17:56+02:00](https://github.com/leanprover-community/mathlib/commit/a54be05)
feat(analysis/topology): add continuity rules for supr, Sup, and pi spaces
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+/\- *lemma* compact_pi_infinite
- \+/\- *lemma* continuous_Inf_rng
- \+ *lemma* continuous_Sup_dom
- \+ *lemma* continuous_Sup_rng
- \+ *lemma* continuous_apply
- \+/\- *lemma* continuous_infi_rng
- \+ *lemma* continuous_pi
- \+/\- *lemma* continuous_subtype_nhds_cover
- \+ *lemma* continuous_supr_dom
- \+ *lemma* continuous_supr_rng
- \+/\- *lemma* nhds_pi



## [2018-05-23 15:22:09+02:00](https://github.com/leanprover-community/mathlib/commit/cff886b)
feat(data/finset): max and min
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* finset.le_max_of_mem
- \+ *theorem* finset.le_min_of_mem
- \+ *theorem* finset.max_empty
- \+ *theorem* finset.max_insert
- \+ *theorem* finset.max_of_mem
- \+ *theorem* finset.max_singleton
- \+ *theorem* finset.mem_of_max
- \+ *theorem* finset.mem_of_min
- \+ *theorem* finset.min_empty
- \+ *theorem* finset.min_insert
- \+ *theorem* finset.min_of_mem
- \+ *theorem* finset.min_singleton

Modified data/option.lean
- \+ *theorem* option.lift_or_get_choice
- \- *theorem* option.lift_or_get_is_some_left
- \- *theorem* option.lift_or_get_is_some_right

Modified logic/basic.lean
- \+ *theorem* if_choice
- \+ *theorem* max_choice
- \+ *theorem* min_choice

Modified order/lattice.lean




## [2018-05-23 15:22:09+02:00](https://github.com/leanprover-community/mathlib/commit/d1ea272)
feat(data/option): lift_or_get
#### Estimated changes
Modified data/option.lean
- \+ *def* option.lift_or_get
- \+ *theorem* option.lift_or_get_is_some_left
- \+ *theorem* option.lift_or_get_is_some_right



## [2018-05-22 05:26:41-04:00](https://github.com/leanprover-community/mathlib/commit/d62bf56)
feat(computability/halting): halting problem
#### Estimated changes
Added data/computability/halting.lean
- \+ *theorem* computable_pred.halting_problem
- \+ *theorem* computable_pred.of_eq
- \+ *theorem* computable_pred.rice
- \+ *theorem* computable_pred.rice₂
- \+ *def* computable_pred
- \+ *theorem* nat.partrec.merge'
- \+ *theorem* partrec.cond
- \+ *theorem* partrec.merge'
- \+ *theorem* partrec.merge
- \+ *theorem* partrec.sum_cases
- \+ *def* re_pred

Modified data/computability/partrec.lean
- \+ *def* nat.rfind_opt
- \+ *theorem* nat.rfind_opt_dom
- \+ *theorem* nat.rfind_opt_mono
- \+ *theorem* nat.rfind_opt_spec
- \+ *theorem* partrec.bind_decode2_iff
- \+ *theorem* partrec.map_encode_iff
- \+ *theorem* partrec.rfind_opt
- \+ *theorem* primrec₂.to_comp

Modified data/computability/partrec_code.lean
- \+ *theorem* nat.partrec.code.const_prim
- \+ *def* nat.partrec.code.curry
- \+ *theorem* nat.partrec.code.curry_prim
- \+ *theorem* nat.partrec.code.eval_const
- \+ *theorem* nat.partrec.code.eval_curry
- \+ *theorem* nat.partrec.code.eval_id
- \+ *theorem* nat.partrec.code.fixed_point
- \+ *theorem* nat.partrec.code.fixed_point₂

Modified data/computability/primrec.lean
- \+ *theorem* primrec.option_guard
- \+/\- *theorem* primrec.option_is_some
- \+ *theorem* primrec.option_orelse

Modified data/encodable.lean
- \+ *def* encodable.decode2
- \+ *theorem* encodable.decode2_inj
- \+ *theorem* encodable.encodek2
- \+ *theorem* encodable.mem_decode2

Modified data/option.lean
- \+ *theorem* option.orelse_none'
- \+ *theorem* option.orelse_none
- \+ *theorem* option.orelse_some'
- \+ *theorem* option.orelse_some

Modified data/pfun.lean
- \+ *theorem* roption.bind_some_right
- \+ *theorem* roption.eq_none_iff'
- \+ *theorem* roption.get_eq_of_mem
- \+ *theorem* roption.get_mem



## [2018-05-21 11:44:37-04:00](https://github.com/leanprover-community/mathlib/commit/f0bcba5)
feat(computability/partrec_code): Kleene normal form theorem
among other things
#### Estimated changes
Modified category/basic.lean
- \+ *theorem* guard_false
- \+ *theorem* guard_true

Modified data/computability/partrec.lean
- \+ *theorem* computable.bind_decode_iff
- \+ *theorem* computable.cond
- \+ *theorem* computable.encode_iff
- \+ *theorem* computable.list_append
- \+ *theorem* computable.list_concat
- \+ *theorem* computable.list_cons
- \+ *theorem* computable.list_length
- \+ *theorem* computable.list_nth
- \+ *theorem* computable.list_reverse
- \+ *theorem* computable.map_decode_iff
- \+ *theorem* computable.nat_bodd
- \+ *theorem* computable.nat_cases
- \+ *theorem* computable.nat_div2
- \+ *theorem* computable.nat_strong_rec
- \+ *theorem* computable.option_bind
- \+ *theorem* computable.option_cases
- \+ *theorem* computable.option_map
- \+ *theorem* computable.option_some
- \+ *theorem* computable.option_some_iff
- \+ *theorem* computable.pred
- \+ *theorem* computable.succ
- \+ *theorem* computable.sum_cases
- \+ *theorem* computable.sum_inl
- \+ *theorem* computable.sum_inr
- \+ *theorem* computable.unpair
- \- *theorem* nat.partrec.code.comp_prim
- \- *def* nat.partrec.code.encode_code
- \- *def* nat.partrec.code.eval
- \- *def* nat.partrec.code.evaln
- \- *theorem* nat.partrec.code.exists_code
- \- *def* nat.partrec.code.of_nat_code
- \- *theorem* nat.partrec.code.pair_prim
- \- *theorem* nat.partrec.code.prec_prim
- \- *theorem* nat.partrec.code.rec_prim
- \- *theorem* nat.partrec.code.rfind_prim
- \- *inductive* nat.partrec.code
- \- *theorem* nat.partrec.rfind'
- \+ *theorem* partrec.fix
- \+ *theorem* partrec.nat_cases_right
- \+ *theorem* partrec.option_cases_right
- \+ *theorem* partrec.option_some_iff
- \+ *theorem* partrec.sum_cases_left
- \+ *theorem* partrec.sum_cases_right

Added data/computability/partrec_code.lean
- \+ *theorem* nat.partrec.code.comp_prim
- \+ *def* nat.partrec.code.encode_code
- \+ *theorem* nat.partrec.code.encode_code_eq
- \+ *theorem* nat.partrec.code.encode_lt_comp
- \+ *theorem* nat.partrec.code.encode_lt_pair
- \+ *theorem* nat.partrec.code.encode_lt_prec
- \+ *theorem* nat.partrec.code.encode_lt_rfind'
- \+ *def* nat.partrec.code.eval
- \+ *theorem* nat.partrec.code.eval_part
- \+ *def* nat.partrec.code.evaln
- \+ *theorem* nat.partrec.code.evaln_bound
- \+ *theorem* nat.partrec.code.evaln_complete
- \+ *theorem* nat.partrec.code.evaln_mono
- \+ *theorem* nat.partrec.code.evaln_prim
- \+ *theorem* nat.partrec.code.evaln_sound
- \+ *theorem* nat.partrec.code.exists_code
- \+ *def* nat.partrec.code.of_nat_code
- \+ *theorem* nat.partrec.code.of_nat_code_eq
- \+ *theorem* nat.partrec.code.pair_prim
- \+ *theorem* nat.partrec.code.prec_prim
- \+ *theorem* nat.partrec.code.rec_computable
- \+ *theorem* nat.partrec.code.rec_prim'
- \+ *theorem* nat.partrec.code.rec_prim
- \+ *theorem* nat.partrec.code.rfind_prim
- \+ *inductive* nat.partrec.code
- \+ *theorem* nat.partrec.rfind'

Modified data/computability/primrec.lean
- \+ *theorem* primrec.list_range
- \+ *theorem* primrec.nat_max
- \+ *theorem* primrec.nat_min
- \+ *theorem* primrec.option_is_some

Modified data/nat/pairing.lean
- \+ *theorem* nat.mkpair_lt_mkpair_left
- \+ *theorem* nat.mkpair_lt_mkpair_right

Modified data/option.lean
- \+ *theorem* option.bind_eq_some'
- \+ *theorem* option.guard_eq_some'
- \+ *theorem* option.map_eq_some'
- \+ *theorem* option.none_bind'
- \+ *theorem* option.some_bind'

Modified data/pfun.lean
- \+ *theorem* pfun.fix_induction
- \+/\- *theorem* pfun.mem_fix_iff
- \+ *theorem* roption.bind_dom
- \+ *theorem* roption.mem_coe



## [2018-05-21 11:41:40-04:00](https://github.com/leanprover-community/mathlib/commit/fe5c86c)
fix(tactic/interactive): fix congr bug, rename congr_n to congr'
#### Estimated changes
Modified data/list/basic.lean


Modified data/real/basic.lean


Modified docs/tactics.md


Modified logic/basic.lean
- \+ *theorem* proof_irrel_heq

Modified set_theory/ordinal.lean


Modified set_theory/ordinal_notation.lean


Modified tactic/interactive.lean




## [2018-05-20 06:37:12-04:00](https://github.com/leanprover-community/mathlib/commit/741469a)
fix(tactic/interactive): make rcases handle nested constructors correctly
The line changed by this commit was wrong because `k` might contain
further constructors, which also need to be "inverted".
Fixes [#56](https://github.com/leanprover-community/mathlib/pull/56).
* doc(tactic): Internal documentation for rcases
* style(tactic/rcases): eliminate an unused recursive parameter
* style(*): use rcases more
#### Estimated changes
Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_structures.lean


Modified data/list/basic.lean


Modified data/real/basic.lean


Modified data/seq/computation.lean


Modified data/seq/parallel.lean


Modified data/seq/seq.lean


Modified data/seq/wseq.lean


Modified group_theory/free_group.lean


Modified order/filter.lean


Modified ring_theory/localization.lean


Modified set_theory/cofinality.lean


Modified set_theory/ordinal.lean


Modified tactic/interactive.lean
- \+ *def* tactic.interactive.rcases_patt_inverted

Modified tactic/rcases.lean
- \+ *def* tactic.list_Pi
- \+ *def* tactic.list_Sigma

Modified tests/tactics.lean




## [2018-05-19 21:28:26-04:00](https://github.com/leanprover-community/mathlib/commit/fc20442)
feat(computability/partrec): partial recursion, Godel numbering
#### Estimated changes
Modified data/bool.lean
- \+ *lemma* bool.ff_eq_to_bool_iff
- \+ *lemma* bool.tt_eq_to_bool_iff

Modified data/computability/partrec.lean
- \+ *theorem* computable.comp
- \+ *theorem* computable.comp₂
- \+ *theorem* computable.const
- \+ *theorem* computable.fst
- \+ *theorem* computable.nat_elim
- \+ *theorem* computable.of_eq
- \+ *theorem* computable.of_option
- \+ *theorem* computable.pair
- \+ *theorem* computable.part
- \+ *theorem* computable.snd
- \+ *theorem* computable.to₂
- \+ *def* computable
- \+ *theorem* computable₂.comp
- \+ *theorem* computable₂.comp₂
- \+ *theorem* computable₂.part
- \+ *def* computable₂
- \+ *theorem* nat.mem_rfind
- \+ *theorem* nat.partrec.code.comp_prim
- \+ *def* nat.partrec.code.encode_code
- \+ *def* nat.partrec.code.eval
- \+ *def* nat.partrec.code.evaln
- \+ *theorem* nat.partrec.code.exists_code
- \+ *def* nat.partrec.code.of_nat_code
- \+ *theorem* nat.partrec.code.pair_prim
- \+ *theorem* nat.partrec.code.prec_prim
- \+ *theorem* nat.partrec.code.rec_prim
- \+ *theorem* nat.partrec.code.rfind_prim
- \+ *inductive* nat.partrec.code
- \+ *theorem* nat.partrec.none
- \+/\- *theorem* nat.partrec.of_eq
- \+ *theorem* nat.partrec.of_eq_tot
- \+ *theorem* nat.partrec.of_primrec
- \+ *theorem* nat.partrec.ppred
- \+ *theorem* nat.partrec.prec'
- \- *theorem* nat.partrec.prim
- \+ *theorem* nat.partrec.rfind'
- \+ *def* nat.rfind
- \+ *theorem* nat.rfind_dom'
- \+ *theorem* nat.rfind_dom
- \+ *theorem* nat.rfind_min'
- \+ *theorem* nat.rfind_min
- \+ *theorem* nat.rfind_spec
- \+ *def* nat.rfind_x
- \+ *theorem* nat.rfind_zero_none
- \+ *theorem* partrec.comp
- \+ *theorem* partrec.const'
- \+ *theorem* partrec.map
- \+ *theorem* partrec.nat_elim
- \+ *theorem* partrec.nat_iff
- \+ *theorem* partrec.none
- \+ *theorem* partrec.of_eq
- \+ *theorem* partrec.of_eq_tot
- \+ *theorem* partrec.rfind
- \+ *theorem* partrec.to₂
- \+ *def* partrec
- \+ *theorem* partrec₂.comp
- \+ *theorem* partrec₂.comp₂
- \+ *theorem* partrec₂.unpaired'
- \+ *theorem* partrec₂.unpaired
- \+ *def* partrec₂
- \+ *theorem* primrec.to_comp

Modified data/computability/primrec.lean
- \+/\- *theorem* nat.primrec.of_eq
- \+/\- *theorem* primrec.comp
- \+ *theorem* primrec.list_concat
- \+ *theorem* primrec.nat_strong_rec
- \+/\- *theorem* primrec.of_eq
- \+/\- *theorem* primrec₂.of_eq

Modified data/denumerable.lean
- \+ *def* equiv.list_equiv_self_of_equiv_nat
- \+ *def* equiv.list_nat_equiv_nat

Modified data/encodable.lean
- \+ *theorem* encodable.decode_nat
- \+ *theorem* encodable.encode_nat

Modified data/equiv.lean
- \- *def* equiv.list_equiv_self_of_equiv_nat
- \- *def* equiv.list_nat_equiv_nat

Modified data/nat/basic.lean
- \+ *lemma* nat.bodd_bit0
- \+ *lemma* nat.bodd_bit1
- \+ *lemma* nat.div2_bit0
- \+ *lemma* nat.div2_bit1

Modified data/nat/pairing.lean
- \+ *theorem* nat.le_mkpair_right
- \- *theorem* nat.unpair_le
- \+ *theorem* nat.unpair_le_left
- \+ *theorem* nat.unpair_le_right

Modified data/pfun.lean
- \+/\- *theorem* pfun.bind_defined
- \+ *theorem* pfun.dom_of_mem_fix
- \+ *def* pfun.fix
- \+ *theorem* pfun.mem_fix_iff
- \+/\- *def* pfun
- \- *def* roption.bind
- \+ *theorem* roption.bind_map
- \+ *theorem* roption.bind_none
- \+/\- *theorem* roption.bind_some_eq_map
- \+ *theorem* roption.coe_none
- \+ *theorem* roption.coe_some
- \+/\- *theorem* roption.dom_iff_mem
- \+ *theorem* roption.eq_none_iff
- \+ *theorem* roption.eq_some_iff
- \- *theorem* roption.eq_some_of_mem
- \+ *theorem* roption.map_bind
- \+ *theorem* roption.map_id'
- \+ *theorem* roption.map_map
- \+ *theorem* roption.map_none
- \+ *theorem* roption.mem_assert
- \+ *theorem* roption.mem_assert_iff
- \+ *theorem* roption.not_mem_none
- \- *structure* roption
- \+ *structure* {u}



## [2018-05-18 05:14:19-04:00](https://github.com/leanprover-community/mathlib/commit/38d5536)
feat(computability/partrec): starting work on partial recursive funcs
#### Estimated changes
Added data/computability/partrec.lean
- \+ *theorem* nat.partrec.of_eq
- \+ *theorem* nat.partrec.prim
- \+ *inductive* nat.partrec

Modified data/computability/primrec.lean
- \+/\- *def* nat.unpaired

Modified data/pfun.lean
- \+ *def* pfun.bind
- \+ *theorem* pfun.coe_val
- \+ *def* pfun.ext'
- \+ *def* pfun.ext
- \+ *theorem* pfun.lift_eq_coe
- \+ *def* pfun.map
- \+ *def* roption.bind
- \+ *theorem* roption.bind_eq_bind
- \+ *theorem* roption.bind_some
- \- *theorem* roption.eq_ret_of_mem
- \+ *theorem* roption.eq_some_of_mem
- \- *theorem* roption.exists_of_mem_bind
- \+ *def* roption.ext'
- \+ *def* roption.ext
- \+ *def* roption.map
- \+ *theorem* roption.map_eq_map
- \+ *theorem* roption.map_some
- \+ *theorem* roption.mem_bind_iff
- \+ *theorem* roption.mem_map
- \+ *theorem* roption.mem_map_iff
- \+ *theorem* roption.mem_of_option
- \- *theorem* roption.mem_ret
- \- *theorem* roption.mem_ret_iff
- \+/\- *theorem* roption.mem_some
- \+ *theorem* roption.mem_some_iff
- \+ *theorem* roption.mem_to_option
- \+ *def* roption.none
- \+/\- *theorem* roption.of_to_option
- \+ *theorem* roption.ret_eq_some
- \+ *def* roption.some
- \- *theorem* roption.some_bind
- \+/\- *theorem* roption.to_of_option



## [2018-05-18 05:10:04-04:00](https://github.com/leanprover-community/mathlib/commit/92feaf9)
feat(computability/primrec): list definitions are primrec
#### Estimated changes
Modified data/computability/primrec.lean
- \+ *theorem* primrec.list_append
- \+ *theorem* primrec.list_cases
- \+ *theorem* primrec.list_cons
- \+/\- *theorem* primrec.list_find_index
- \+ *theorem* primrec.list_find_index₁
- \+ *theorem* primrec.list_foldl
- \+ *theorem* primrec.list_foldr
- \+/\- *theorem* primrec.list_index_of
- \+ *theorem* primrec.list_index_of₁
- \+/\- *theorem* primrec.list_inth
- \+ *theorem* primrec.list_join
- \+ *theorem* primrec.list_length
- \+ *theorem* primrec.list_map
- \+/\- *theorem* primrec.list_nth
- \+ *theorem* primrec.list_nth₁
- \+ *theorem* primrec.list_rec
- \+ *theorem* primrec.list_reverse
- \- *theorem* primrec.nat_cases1
- \+ *theorem* primrec.nat_cases₁
- \- *theorem* primrec.nat_elim1
- \+ *theorem* primrec.nat_elim₁
- \+ *theorem* primrec.nat_iterate
- \- *theorem* primrec.option_bind1
- \+ *theorem* primrec.option_bind₁
- \- *theorem* primrec.option_map1
- \+ *theorem* primrec.option_map₁
- \+ *theorem* primrec.sum_cases
- \+ *theorem* primrec.sum_inl
- \+ *theorem* primrec.sum_inr
- \+ *theorem* primrec.to₂

Modified data/denumerable.lean
- \+ *theorem* denumerable.list_of_nat_succ
- \+ *theorem* denumerable.list_of_nat_zero

Modified data/encodable.lean
- \+ *theorem* encodable.decode_list_succ
- \+ *theorem* encodable.decode_list_zero
- \+ *theorem* encodable.decode_sum_val
- \+ *theorem* encodable.encode_inl
- \+ *theorem* encodable.encode_inr
- \+ *theorem* encodable.encode_list_cons
- \+ *theorem* encodable.encode_list_nil
- \+ *theorem* encodable.length_le_encode

Modified data/list/basic.lean
- \+ *theorem* list.drop_nil

Modified data/nat/basic.lean
- \- *def* nat.foldl
- \- *def* nat.foldr
- \+ *theorem* nat.iterate_add
- \+ *theorem* nat.iterate_succ'
- \+ *theorem* nat.iterate_succ
- \+ *theorem* nat.iterate_zero

Modified data/nat/pairing.lean
- \+ *theorem* nat.le_mkpair_left
- \+/\- *def* nat.mkpair
- \+/\- *theorem* nat.mkpair_unpair
- \+/\- *def* nat.unpair
- \+/\- *theorem* nat.unpair_le
- \+/\- *theorem* nat.unpair_lt
- \+/\- *theorem* nat.unpair_mkpair

Modified order/order_iso.lean


Modified set_theory/ordinal.lean
- \- *theorem* ordinal.foldr_le_nfp
- \+ *theorem* ordinal.iterate_le_nfp



## [2018-05-17 04:23:08-04:00](https://github.com/leanprover-community/mathlib/commit/e017f0f)
feat(data/computability): primrec, denumerable
#### Estimated changes
Modified analysis/limits.lean


Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean
- \+ *lemma* topological_space.Union_basis_of_is_open
- \+ *lemma* topological_space.sUnion_basis_of_is_open

Modified data/bool.lean
- \+/\- *theorem* bool.cond_ff
- \+ *theorem* bool.cond_to_bool
- \+/\- *theorem* bool.cond_tt
- \+ *theorem* bool.to_bool_and
- \+ *theorem* bool.to_bool_not
- \+ *theorem* bool.to_bool_or

Added data/computability/primrec.lean
- \+ *def* nat.cases
- \+ *theorem* nat.cases_succ
- \+ *theorem* nat.cases_zero
- \+ *def* nat.elim
- \+ *theorem* nat.elim_succ
- \+ *theorem* nat.elim_zero
- \+ *theorem* nat.primrec.add
- \+ *theorem* nat.primrec.cases1
- \+ *theorem* nat.primrec.cases
- \+ *theorem* nat.primrec.const
- \+ *theorem* nat.primrec.mul
- \+ *theorem* nat.primrec.of_eq
- \+ *theorem* nat.primrec.pow
- \+ *theorem* nat.primrec.prec1
- \+ *theorem* nat.primrec.pred
- \+ *theorem* nat.primrec.sub
- \+ *theorem* nat.primrec.swap'
- \+ *inductive* nat.primrec
- \+ *def* nat.unpaired
- \+ *def* primcodable.of_equiv
- \+ *theorem* primrec.bind_decode_iff
- \+ *theorem* primrec.comp
- \+ *theorem* primrec.comp₂
- \+ *theorem* primrec.cond
- \+ *theorem* primrec.const
- \+ *theorem* primrec.dom_bool
- \+ *theorem* primrec.dom_bool₂
- \+ *theorem* primrec.dom_denumerable
- \+ *theorem* primrec.dom_fintype
- \+ *theorem* primrec.encdec
- \+ *theorem* primrec.encode_iff
- \+ *theorem* primrec.fst
- \+ *theorem* primrec.ite
- \+ *theorem* primrec.list_find_index
- \+ *theorem* primrec.list_index_of
- \+ *theorem* primrec.list_inth
- \+ *theorem* primrec.list_nth
- \+ *theorem* primrec.map_decode_iff
- \+ *theorem* primrec.nat_add
- \+ *theorem* primrec.nat_bit0
- \+ *theorem* primrec.nat_bit1
- \+ *theorem* primrec.nat_bit
- \+ *theorem* primrec.nat_bodd
- \+ *theorem* primrec.nat_bodd_div2
- \+ *theorem* primrec.nat_cases'
- \+ *theorem* primrec.nat_cases1
- \+ *theorem* primrec.nat_cases
- \+ *theorem* primrec.nat_div2
- \+ *theorem* primrec.nat_div
- \+ *theorem* primrec.nat_div_mod
- \+ *theorem* primrec.nat_elim'
- \+ *theorem* primrec.nat_elim1
- \+ *theorem* primrec.nat_elim
- \+ *theorem* primrec.nat_iff
- \+ *theorem* primrec.nat_le
- \+ *theorem* primrec.nat_mod
- \+ *theorem* primrec.nat_mul
- \+ *theorem* primrec.nat_sub
- \+ *theorem* primrec.of_eq
- \+ *theorem* primrec.of_nat_iff
- \+ *theorem* primrec.option_bind1
- \+ *theorem* primrec.option_bind
- \+ *theorem* primrec.option_cases
- \+ *theorem* primrec.option_iget
- \+ *theorem* primrec.option_map1
- \+ *theorem* primrec.option_map
- \+ *theorem* primrec.option_some
- \+ *theorem* primrec.option_some_iff
- \+ *theorem* primrec.pair
- \+ *theorem* primrec.pred
- \+ *theorem* primrec.snd
- \+ *theorem* primrec.succ
- \+ *theorem* primrec.unpair
- \+ *def* primrec
- \+ *theorem* primrec_pred.comp
- \+ *theorem* primrec_pred.of_eq
- \+ *def* primrec_pred
- \+ *theorem* primrec_rel.comp
- \+ *theorem* primrec_rel.comp₂
- \+ *theorem* primrec_rel.of_eq
- \+ *def* primrec_rel
- \+ *theorem* primrec₂.comp
- \+ *theorem* primrec₂.comp₂
- \+ *theorem* primrec₂.const
- \+ *theorem* primrec₂.curry
- \+ *theorem* primrec₂.encode_iff
- \+ *theorem* primrec₂.left
- \+ *theorem* primrec₂.mkpair
- \+ *theorem* primrec₂.nat_iff'
- \+ *theorem* primrec₂.nat_iff
- \+ *theorem* primrec₂.of_eq
- \+ *theorem* primrec₂.of_nat_iff
- \+ *theorem* primrec₂.option_some_iff
- \+ *theorem* primrec₂.right
- \+ *theorem* primrec₂.swap
- \+ *theorem* primrec₂.uncurry
- \+ *theorem* primrec₂.unpaired'
- \+ *theorem* primrec₂.unpaired
- \+ *def* primrec₂

Added data/denumerable.lean
- \+ *theorem* denumerable.decode_eq_of_nat
- \+ *theorem* denumerable.decode_is_some
- \+ *theorem* denumerable.denumerable_list_aux
- \+ *theorem* denumerable.encode_of_nat
- \+ *def* denumerable.equiv₂
- \+ *def* denumerable.eqv
- \+ *def* denumerable.lower'
- \+ *def* denumerable.lower
- \+ *lemma* denumerable.lower_raise'
- \+ *lemma* denumerable.lower_raise
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
- \+ *def* denumerable.raise'
- \+ *lemma* denumerable.raise'_chain
- \+ *def* denumerable.raise'_finset
- \+ *lemma* denumerable.raise'_sorted
- \+ *def* denumerable.raise
- \+ *lemma* denumerable.raise_chain
- \+ *lemma* denumerable.raise_lower'
- \+ *lemma* denumerable.raise_lower
- \+ *lemma* denumerable.raise_sorted
- \+ *theorem* denumerable.sigma_of_nat_val

Modified data/encodable.lean
- \+ *def* encodable.decidable_eq_of_encodable
- \+ *theorem* encodable.decode_ge_two
- \+ *def* encodable.decode_list
- \+ *def* encodable.decode_multiset
- \+ *theorem* encodable.decode_of_equiv
- \+ *theorem* encodable.decode_one
- \+ *theorem* encodable.decode_option_succ
- \+ *theorem* encodable.decode_option_zero
- \+ *theorem* encodable.decode_prod_val
- \+ *def* encodable.decode_sigma
- \+ *theorem* encodable.decode_sigma_val
- \+ *def* encodable.decode_subtype
- \+ *def* encodable.decode_sum
- \+ *theorem* encodable.decode_unit_succ
- \+ *theorem* encodable.decode_unit_zero
- \+ *theorem* encodable.decode_zero
- \+ *def* encodable.encodable_of_list
- \+ *theorem* encodable.encode_ff
- \+ *theorem* encodable.encode_injective
- \+ *def* encodable.encode_list
- \+ *def* encodable.encode_multiset
- \+ *theorem* encodable.encode_none
- \+ *theorem* encodable.encode_of_equiv
- \+ *theorem* encodable.encode_prod_val
- \+ *def* encodable.encode_sigma
- \+ *theorem* encodable.encode_sigma_val
- \+ *theorem* encodable.encode_some
- \+ *theorem* encodable.encode_star
- \+ *def* encodable.encode_subtype
- \+ *def* encodable.encode_sum
- \+ *theorem* encodable.encode_tt
- \+ *def* encodable.of_equiv
- \+ *def* encodable.of_left_injection
- \+ *def* encodable.of_left_inverse
- \+ *def* encodable.trunc_encodable_of_fintype
- \- *def* encodable_of_equiv
- \- *def* encodable_of_left_injection
- \- *def* encodable_of_list
- \- *theorem* encode_injective
- \- *def* trunc_encodable_of_fintype

Modified data/equiv.lean
- \+ *theorem* equiv.symm_symm

Modified data/finset.lean
- \+ *lemma* finset.attach_map_val
- \+ *def* finset.map
- \+ *theorem* finset.map_empty
- \+ *theorem* finset.map_eq_empty
- \+ *theorem* finset.map_eq_image
- \+ *theorem* finset.map_filter
- \+ *theorem* finset.map_insert
- \+ *theorem* finset.map_inter
- \+ *theorem* finset.map_map
- \+ *theorem* finset.map_refl
- \+ *theorem* finset.map_singleton
- \+ *theorem* finset.map_subset_map
- \+ *theorem* finset.map_to_finset
- \+ *theorem* finset.map_union
- \+ *theorem* finset.map_val
- \+ *theorem* finset.mem_map
- \+ *theorem* finset.mem_map_of_mem
- \+ *theorem* finset.sort_sorted_lt

Modified data/fintype.lean
- \+ *theorem* fintype.exists_univ_list

Modified data/list/basic.lean
- \+ *lemma* list.filter_congr
- \+ *lemma* list.foldl_ext
- \+ *lemma* list.foldr_ext
- \+ *theorem* list.map_add_range'
- \+ *theorem* list.nth_le_map'
- \+ *theorem* list.nth_le_map
- \+ *theorem* list.nth_map
- \+ *theorem* list.pairwise.and
- \+ *theorem* list.pairwise.imp₂
- \+ *theorem* list.range'_eq_map_range
- \+ *theorem* list.range_succ_eq_map
- \+ *theorem* list.reverse_range'

Modified data/list/sort.lean
- \+/\- *theorem* list.eq_of_sorted_of_perm
- \+ *theorem* list.merge_sort_eq_self

Modified data/multiset.lean


Modified data/nat/basic.lean


Modified data/nat/pairing.lean
- \+/\- *theorem* nat.mkpair_unpair
- \+/\- *theorem* nat.unpair_mkpair

Modified data/option.lean
- \+ *theorem* option.map_none'
- \+ *theorem* option.map_some'

Modified data/rat.lean


Modified data/semiquot.lean
- \+ *theorem* semiquot.is_pure.min
- \+ *theorem* semiquot.is_pure.mono
- \+ *theorem* semiquot.is_pure_iff
- \+ *theorem* semiquot.pure_inj

Modified data/seq/parallel.lean


Modified data/seq/seq.lean


Modified data/seq/wseq.lean


Modified data/set/countable.lean


Modified logic/basic.lean
- \+ *lemma* and.right_comm
- \+ *lemma* and.rotate

Modified logic/embedding.lean
- \+ *def* function.embedding.subtype

Modified order/basic.lean




## [2018-05-16 10:16:22+02:00](https://github.com/leanprover-community/mathlib/commit/fe7d573)
refactor(data/set/enumerate): proof enumeration_inj using wlog
#### Estimated changes
Modified data/set/enumerate.lean
- \+/\- *lemma* set.enumerate_inj



## [2018-05-16 10:16:22+02:00](https://github.com/leanprover-community/mathlib/commit/d8c33e8)
feat(tactic): generalize wlog to support multiple variables and cases, allow to provide case rule
#### Estimated changes
Modified tactic/default.lean


Modified tactic/interactive.lean


Added tactic/wlog.lean


Modified tests/tactics.lean




## [2018-05-10 15:29:47+02:00](https://github.com/leanprover-community/mathlib/commit/2cd640a)
feat(data/multiset): add sections
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* list.bind_map

Modified data/multiset.lean
- \+ *theorem* multiset.bind_add
- \+ *lemma* multiset.bind_assoc
- \+/\- *lemma* multiset.bind_bind
- \+ *theorem* multiset.bind_cons
- \+ *lemma* multiset.bind_map
- \+ *lemma* multiset.bind_map_comm
- \+ *theorem* multiset.bind_zero
- \+ *lemma* multiset.card_sections
- \+ *lemma* multiset.coe_sections
- \+/\- *lemma* multiset.map_bind
- \+ *lemma* multiset.map_id'
- \+ *lemma* multiset.mem_sections
- \+ *lemma* multiset.prod_map_one
- \+ *lemma* multiset.prod_map_sum
- \+ *lemma* multiset.rel_bind
- \+ *def* multiset.sections
- \+ *lemma* multiset.sections_add
- \+ *lemma* multiset.sections_cons
- \+ *lemma* multiset.sections_zero
- \+ *lemma* multiset.sum_map_mul_left
- \+ *lemma* multiset.sum_map_mul_right
- \+ *lemma* multiset.sum_map_zero



## [2018-05-10 15:29:29+02:00](https://github.com/leanprover-community/mathlib/commit/62833ca)
feat(data/multiset): add relator
#### Estimated changes
Modified data/multiset.lean
- \+ *lemma* multiset.card_eq_card_of_rel
- \+ *lemma* multiset.cons_eq_cons
- \+ *lemma* multiset.cons_ne_zero
- \+ *lemma* multiset.rel.add
- \+ *lemma* multiset.rel.mono
- \+ *inductive* multiset.rel
- \+ *lemma* multiset.rel_add_left
- \+ *lemma* multiset.rel_add_right
- \+ *lemma* multiset.rel_cons_left
- \+ *lemma* multiset.rel_cons_right
- \+ *lemma* multiset.rel_eq
- \+ *lemma* multiset.rel_eq_refl
- \+ *lemma* multiset.rel_flip
- \+ *lemma* multiset.rel_flip_eq
- \+ *lemma* multiset.rel_join
- \+ *lemma* multiset.rel_map
- \+ *lemma* multiset.rel_map_left
- \+ *lemma* multiset.rel_map_right
- \+ *lemma* multiset.rel_zero_left
- \+ *lemma* multiset.rel_zero_right
- \+ *lemma* multiset.zero_ne_cons

Modified tests/mk_iff_of_inductive.lean
- \- *inductive* multiset.rel



## [2018-05-10 12:12:25+02:00](https://github.com/leanprover-community/mathlib/commit/d10c3bb)
fix(order/complete_boolean_algebra): replace finish proof by simp (finish was very slow)
#### Estimated changes
Modified order/complete_boolean_algebra.lean




## [2018-05-09 06:19:46-04:00](https://github.com/leanprover-community/mathlib/commit/fc6f57a)
feat(data/list/basic): list.forall2, list.sections
#### Estimated changes
Modified data/list/basic.lean
- \+ *inductive* list.forall₂
- \+ *theorem* list.forall₂_cons
- \+ *theorem* list.forall₂_iff_zip
- \+ *theorem* list.forall₂_length_eq
- \+ *theorem* list.forall₂_nil_left
- \+ *theorem* list.forall₂_nil_right
- \+ *theorem* list.forall₂_zip
- \+ *theorem* list.mem_sections
- \+ *theorem* list.mem_sections_length
- \+ *def* list.sections



## [2018-05-09 06:04:38-04:00](https://github.com/leanprover-community/mathlib/commit/42f5ea0)
feat(data/semiquot): semiquotient types
#### Estimated changes
Modified data/fp/basic.lean
- \- *def* fp.float.default_nan
- \- *structure* fp.nan_pl
- \- *def* fp.shift2
- \+ *def* int.shift2

Modified data/quot.lean
- \+ *theorem* true_equivalence
- \+ *def* trunc.bind
- \+ *def* trunc.map

Modified data/rat.lean
- \+ *theorem* rat.num_nonneg_iff_zero_le
- \+ *theorem* rat.num_pos_iff_pos

Added data/semiquot.lean
- \+ *def* semiquot.bind
- \+ *def* semiquot.blur'
- \+ *def* semiquot.blur
- \+ *theorem* semiquot.blur_eq_blur'
- \+ *theorem* semiquot.eq_mk_of_mem
- \+ *theorem* semiquot.eq_pure
- \+ *theorem* semiquot.exists_mem
- \+ *theorem* semiquot.ext
- \+ *theorem* semiquot.ext_s
- \+ *def* semiquot.get
- \+ *theorem* semiquot.get_mem
- \+ *def* semiquot.is_pure
- \+ *theorem* semiquot.is_pure_of_subsingleton
- \+ *theorem* semiquot.is_pure_univ
- \+ *def* semiquot.lift_on
- \+ *theorem* semiquot.lift_on_of_mem
- \+ *def* semiquot.map
- \+ *theorem* semiquot.mem_bind
- \+ *theorem* semiquot.mem_blur'
- \+ *theorem* semiquot.mem_map
- \+ *theorem* semiquot.mem_pure'
- \+ *theorem* semiquot.mem_pure
- \+ *theorem* semiquot.mem_pure_self
- \+ *theorem* semiquot.mem_univ
- \+ *def* semiquot.mk
- \+ *theorem* semiquot.ne_empty
- \+ *def* semiquot.of_trunc
- \+ *theorem* semiquot.pure_is_pure
- \+ *theorem* semiquot.pure_le
- \+ *def* semiquot.to_trunc
- \+ *def* semiquot.univ
- \+ *theorem* semiquot.univ_unique
- \+ *structure* {u}

Modified data/set/lattice.lean
- \+ *theorem* set.mem_bInter_iff
- \+ *theorem* set.mem_bUnion_iff

Modified logic/basic.lean
- \+ *theorem* eq_equivalence



## [2018-05-09 06:04:38-04:00](https://github.com/leanprover-community/mathlib/commit/b31c30d)
refactor(logic/function): constructive proof of cantor_injective
#### Estimated changes
Modified logic/function.lean
- \+/\- *theorem* function.cantor_injective



## [2018-05-09 11:41:31+02:00](https://github.com/leanprover-community/mathlib/commit/54df4d9)
feat(linear_algebra/multivariate_polynomial): change order of eval arguments; show that eval is ring homomorphism
(closes https://github.com/leanprover/mathlib/pull/134)
#### Estimated changes
Modified linear_algebra/multivariate_polynomial.lean
- \+/\- *def* mv_polynomial.eval



## [2018-05-09 10:46:03+02:00](https://github.com/leanprover-community/mathlib/commit/b5eddd8)
fix(data/set/basic): mark subset.refl as @[refl]
#### Estimated changes
Modified analysis/measure_theory/outer_measure.lean


Modified data/set/basic.lean
- \+/\- *theorem* set.subset.refl



## [2018-05-04 16:10:27+02:00](https://github.com/leanprover-community/mathlib/commit/e4c64fd)
feat(tactic/mk_iff_of_inductive_prop): add tactic to represent inductives using logical connectives
#### Estimated changes
Modified data/list/basic.lean


Modified logic/relation.lean
- \+/\- *lemma* relation.refl_gen.to_refl_trans_gen
- \+/\- *lemma* relation.refl_trans_gen.cases_tail
- \- *lemma* relation.refl_trans_gen.cases_tail_iff

Modified tactic/default.lean


Added tactic/mk_iff_of_inductive_prop.lean


Added tests/mk_iff_of_inductive.lean
- \+ *inductive* multiset.rel
- \+ *inductive* test.is_true



## [2018-05-03 13:46:52-04:00](https://github.com/leanprover-community/mathlib/commit/fa7a180)
feat(tactic/solve_by_elim): make solve_by_elim easier to use correctly ([#131](https://github.com/leanprover-community/mathlib/pull/131))
#### Estimated changes
Modified tactic/interactive.lean




## [2018-05-03 14:41:35+02:00](https://github.com/leanprover-community/mathlib/commit/ef43edf)
feat(data/finset): add list.to_finset theorems
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* list.to_finset_card_of_nodup
- \+ *theorem* list.to_finset_cons
- \+ *theorem* list.to_finset_nil

Modified data/list/basic.lean
- \+ *theorem* list.erase_dup_idempotent
- \+ *theorem* list.pw_filter_idempotent



## [2018-05-03 11:23:10+02:00](https://github.com/leanprover-community/mathlib/commit/02c2b56)
feat(analysis/topology/topological_space): t2 instances for constructions of limit type
#### Estimated changes
Modified analysis/topology/topological_space.lean


