## [2018-05-31 03:00:24-04:00](https://github.com/leanprover-community/mathlib/commit/b375264)
feat(computability/turing_machine): add TMs and reductions
#### Estimated changes
Modified data/array/lemmas.lean

Modified data/computability/halting.lean

Created data/computability/turing_machine.lean
- \+ *theorem* step_supports
- \+ *theorem* stmts₁_self
- \+ *theorem* step_supports
- \+ *def* rev
- \+ *def* move_tape
- \+ *def* step
- \+ *def* supports
- \+ *def* step
- \+ *def* supports_stmt
- \+ *def* supports
- \+ *def* trans
- \+ *def* translate
- \+ *def* step_aux
- \+ *def* step
- \+ *def* translate'
- \+ *def* translate
- \+ *def* step_aux
- \+ *def* step
- \+ *def* stackel.is_bottom
- \+ *def* stackel.is_top
- \+ *def* stackel.get
- \+ *def* stackel_equiv
- \+ *def* at_stack
- \+ *def* push
- \+ *def* pop
- \+ *def* translate

Modified data/fintype.lean

Modified data/real/basic.lean
- \+/\- *def* real
- \+/\- *def* real

Modified data/sum.lean



## [2018-05-30 15:29:43-04:00](https://github.com/leanprover-community/mathlib/commit/bdd54ac)
feat(data/computablility): reduced partrec
#### Estimated changes
Modified data/computability/halting.lean
- \+ *theorem* to_part
- \+ *theorem* of_eq
- \+ *theorem* of_prim
- \+ *theorem* head
- \+ *theorem* tail
- \+ *theorem* vec.prim
- \+ *theorem* idv
- \+ *theorem* comp'
- \+ *theorem* comp₁
- \+ *theorem* rfind_opt
- \+ *theorem* of_part
- \+ *theorem* part_iff
- \+ *theorem* part_iff₁
- \+ *theorem* part_iff₂
- \+ *theorem* vec_iff
- \+ *def* vec

Modified data/computability/partrec.lean
- \+ *theorem* vector_cons
- \+ *theorem* vector_to_list
- \+ *theorem* vector_length
- \+ *theorem* vector_head
- \+ *theorem* vector_tail
- \+ *theorem* vector_nth
- \+ *theorem* vector_nth'
- \+ *theorem* vector_of_fn'
- \+ *theorem* fin_app
- \+ *theorem* vector_m_of_fn
- \+ *theorem* vector.m_of_fn_roption_some
- \+ *theorem* list_of_fn
- \+ *theorem* vector_of_fn

Modified data/computability/partrec_code.lean
- \+ *theorem* eval_eq_rfind_opt

Modified data/computability/primrec.lean
- \+/\- *theorem* idv
- \+ *theorem* vec_iff
- \+/\- *theorem* idv
- \- *theorem* primvec_iff
- \+ *def* vec
- \- *def* primvec

Modified data/vector2.lean
- \+ *theorem* m_of_fn_pure
- \+ *theorem* mmap_nil
- \+ *theorem* mmap_cons
- \+ *def* {u}
- \+ *def* {u}



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
- \+ *theorem* of_equiv
- \+ *theorem* of_equiv_symm
- \+ *theorem* of_equiv_iff
- \+ *theorem* of_equiv_symm_iff
- \+ *theorem* nat_lt
- \+ *theorem* list_head'
- \+ *theorem* list_head
- \+ *theorem* list_tail
- \+ *theorem* subtype_val
- \+ *theorem* subtype_val_iff
- \+ *theorem* fin_val_iff
- \+ *theorem* fin_val
- \+ *theorem* fin_succ
- \+ *theorem* vector_to_list
- \+ *theorem* vector_to_list_iff
- \+ *theorem* vector_cons
- \+ *theorem* vector_length
- \+ *theorem* vector_head
- \+ *theorem* vector_tail
- \+ *theorem* vector_nth
- \+ *theorem* list_of_fn
- \+ *theorem* vector_of_fn
- \+ *theorem* vector_nth'
- \+ *theorem* vector_of_fn'
- \+ *theorem* fin_app
- \+ *theorem* fin_curry₁
- \+ *theorem* fin_curry
- \+ *theorem* to_prim
- \+ *theorem* of_eq
- \+ *theorem* const
- \+ *theorem* head
- \+ *theorem* tail
- \+ *theorem* idv
- \+ *theorem* comp'
- \+ *theorem* comp₁
- \+ *theorem* comp₂
- \+ *theorem* prec'
- \+ *theorem* pred
- \+ *theorem* add
- \+ *theorem* sub
- \+ *theorem* mul
- \+ *theorem* if_lt
- \+ *theorem* mkpair
- \+ *theorem* sqrt
- \+ *theorem* unpair₁
- \+ *theorem* unpair₂
- \+ *theorem* of_prim
- \+ *theorem* prim_iff
- \+ *theorem* prim_iff₁
- \+ *theorem* prim_iff₂
- \+ *theorem* primvec_iff
- \+ *theorem* primrec.nat_sqrt
- \+ *def* subtype
- \+ *def* primvec

Modified data/encodable.lean

Modified data/equiv.lean
- \+ *def* fin_equiv_subtype
- \+ *def* vector_equiv_fin
- \+ *def* d_array_equiv_fin
- \+ *def* array_equiv_fin
- \+ *def* vector_equiv_array

Modified data/fin.lean
- \+ *theorem* fin.cases_zero
- \+ *theorem* fin.cases_succ
- \+ *def* fin.cases

Modified data/list/basic.lean
- \+ *theorem* head_eq_head'
- \+/\- *theorem* head_cons
- \+/\- *theorem* head_append
- \+/\- *theorem* cons_head_tail
- \+ *theorem* length_of_fn_aux
- \+ *theorem* length_of_fn
- \+ *theorem* nth_of_fn_aux
- \+ *theorem* nth_of_fn
- \+ *theorem* nth_le_of_fn
- \+ *theorem* array_eq_of_fn
- \+ *theorem* of_fn_zero
- \+ *theorem* of_fn_succ
- \+ *theorem* of_fn_nth_le
- \+/\- *theorem* head_cons
- \+/\- *theorem* head_append
- \+/\- *theorem* cons_head_tail
- \+ *def* head'
- \+ *def* of_fn_aux
- \+ *def* of_fn
- \+ *def* of_fn_nth_val

Modified data/nat/sqrt.lean
- \+ *theorem* eq_sqrt
- \+ *theorem* sqrt_succ_le_succ_sqrt

Modified data/set/basic.lean
- \+/\- *theorem* image_empty
- \+/\- *theorem* image_id
- \+/\- *theorem* image_empty
- \+/\- *theorem* image_id

Modified data/sigma/basic.lean
- \+ *lemma* subtype.ext
- \+ *theorem* subtype.val_injective

Created data/vector2.lean
- \+ *theorem* to_list_injective
- \+ *theorem* to_list_of_fn
- \+ *theorem* mk_to_list
- \+ *theorem* nth_eq_nth_le
- \+ *theorem* nth_of_fn
- \+ *theorem* of_fn_nth
- \+ *theorem* nth_tail
- \+ *theorem* tail_of_fn
- \+ *theorem* head'_to_list
- \+ *theorem* nth_zero
- \+ *theorem* head_of_fn
- \+ *theorem* nth_cons_zero
- \+ *theorem* nth_cons_succ

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
- \+ *def* of_fintype
- \+ *def* bernoulli



## [2018-05-29 15:08:43+02:00](https://github.com/leanprover-community/mathlib/commit/4f9e951)
feat(analysis): add probability mass functions
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* sum_nat_cast
- \+ *lemma* to_finset_sum_count_eq

Modified analysis/ennreal.lean
- \+ *lemma* tendsto_of_real_iff
- \+ *lemma* tendsto_coe_iff
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_eq_coe
- \+ *lemma* has_sum_of_nonneg_of_le
- \+ *lemma* nnreal.has_sum_of_le

Modified analysis/nnreal.lean
- \+ *lemma* tendsto_coe
- \+ *lemma* sum_coe
- \+ *lemma* is_sum_coe
- \+ *lemma* has_sum_coe

Created analysis/probability_mass_function.lean
- \+ *lemma* is_sum_coe_one
- \+ *lemma* has_sum_coe
- \+ *lemma* tsum_coe
- \+ *lemma* pure_apply
- \+ *lemma* coe_le_one
- \+ *lemma* bind_apply
- \+ *lemma* coe_bind_apply
- \+ *lemma* pure_bind
- \+ *lemma* bind_pure
- \+ *lemma* bind_bind
- \+ *lemma* bind_comm
- \+ *lemma* bind_pure_comp
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* pure_map
- \+ *def* {u}
- \+ *def* support
- \+ *def* pure
- \+ *def* bind
- \+ *def* map
- \+ *def* seq
- \+ *def* of_multiset

Modified analysis/topology/infinite_sum.lean
- \+ *lemma* is_sum_ite
- \+ *lemma* is_sum_iff_of_has_sum
- \+ *lemma* tsum_ite

Modified data/finset.lean
- \+ *lemma* to_finset_cons

Modified data/multiset.lean
- \+/\- *theorem* count_eq_zero_of_not_mem
- \+/\- *theorem* count_eq_zero_of_not_mem

Modified order/filter.lean
- \+ *lemma* le_of_map_le_map_inj_iff



## [2018-05-29 04:19:54-04:00](https://github.com/leanprover-community/mathlib/commit/eaa1b93)
feat(data.list.basic): forall_mem_singleton, forall_mem_append
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* forall_mem_singleton
- \+ *theorem* forall_mem_append



## [2018-05-29 03:47:46-04:00](https://github.com/leanprover-community/mathlib/commit/a6be523)
feat(data/list/basic): map_erase, map_diff, map_union
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* map_erase
- \+ *theorem* map_foldl_erase
- \+ *theorem* map_diff

Modified data/multiset.lean
- \+ *theorem* map_union



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
- \+ *lemma* symm_image_image
- \+ *theorem* left_inverse_symm
- \+ *theorem* right_inverse_symm
- \+ *theorem* perm.mul_val
- \+ *theorem* perm.one_val



## [2018-05-27 22:50:42-04:00](https://github.com/leanprover-community/mathlib/commit/c53f9f1)
refactor(algebra/euclidean_domain): clean up proofs
#### Estimated changes
Modified algebra/euclidean_domain.lean
- \+ *lemma* mul_div_cancel_left
- \+ *lemma* mul_div_cancel
- \+/\- *lemma* mod_zero
- \+ *lemma* mod_eq_zero
- \+/\- *lemma* mod_self
- \+ *lemma* dvd_mod_iff
- \+/\- *lemma* zero_div
- \+/\- *lemma* div_self
- \- *lemma* gcd_decreasing
- \+/\- *lemma* mod_zero
- \- *lemma* dvd_mod_self
- \- *lemma* mod_lt
- \- *lemma* neq_zero_lt_mod_lt
- \- *lemma* dvd_mod
- \+/\- *lemma* zero_div
- \+/\- *lemma* mod_self
- \+/\- *lemma* div_self
- \+ *theorem* div_add_mod
- \+ *theorem* val_mod_lt
- \+ *theorem* val_le_mul_right
- \+/\- *theorem* gcd_zero_right
- \+ *theorem* gcd_val
- \+/\- *theorem* gcd.induction
- \+/\- *theorem* gcd_dvd
- \+ *theorem* gcd_eq_left
- \+/\- *theorem* gcd.induction
- \+/\- *theorem* gcd_dvd
- \+/\- *theorem* gcd_zero_right
- \- *theorem* gcd_next
- \+/\- *def* gcd
- \+/\- *def* gcd

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
- \+/\- *lemma* bit0_pos
- \+/\- *lemma* bit0_pos
- \+ *def* ordered_comm_monoid

Modified algebra/ring.lean

Modified data/option.lean

Modified order/bounded_lattice.lean
- \+ *theorem* coe_le_coe
- \+/\- *theorem* some_le_some
- \+ *theorem* coe_le
- \+ *theorem* some_lt_some
- \+ *theorem* coe_le_coe
- \+/\- *theorem* some_le_some
- \+ *theorem* le_coe
- \+ *theorem* some_lt_some
- \+/\- *theorem* some_le_some
- \- *theorem* some_le
- \+/\- *theorem* some_le_some
- \- *theorem* le_some

Modified order/lattice.lean



## [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/431d997)
feat(nat/basic): mod_mod
#### Estimated changes
Modified data/nat/basic.lean
- \+ *theorem* mod_mod

Modified data/nat/modeq.lean
- \+ *theorem* mod_modeq



## [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/4c1a826)
refactor(data/set/finite): use hypotheses for fintype assumptions
in simp rules
#### Estimated changes
Modified data/set/finite.lean
- \+/\- *theorem* empty_card
- \+ *theorem* empty_card'
- \+/\- *theorem* card_insert
- \+/\- *theorem* empty_card
- \+/\- *theorem* card_insert

Modified number_theory/pell.lean



## [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/f563ac8)
chore(data/pnat): remove nat -> pnat coercion
#### Estimated changes
Modified analysis/real.lean

Modified data/finset.lean
- \+ *theorem* min_eq_inf_with_top
- \- *theorem* max_eq_inf_with_top

Modified data/pnat.lean
- \+ *theorem* coe_to_pnat'
- \- *theorem* nat_coe_coe
- \- *theorem* coe_nat_coe



## [2018-05-27 18:15:30-04:00](https://github.com/leanprover-community/mathlib/commit/b7012fb)
fix(tactic/norm_num): use norm_num to discharge simp goals
#### Estimated changes
Modified tactic/norm_num.lean



## [2018-05-25 16:15:06+02:00](https://github.com/leanprover-community/mathlib/commit/6811f13)
fix(data/list/perm): remove unused code ([#143](https://github.com/leanprover-community/mathlib/pull/143))
#### Estimated changes
Modified data/list/perm.lean
- \- *theorem* xswap



## [2018-05-25 05:57:39-04:00](https://github.com/leanprover-community/mathlib/commit/bcec475)
chore(leanpkg.toml): update version to 3.4.1
#### Estimated changes
Modified leanpkg.toml



## [2018-05-25 05:55:41-04:00](https://github.com/leanprover-community/mathlib/commit/1991869)
feat(order/bounded_lattice): with_bot, with_top structures
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* singleton_bind
- \+ *lemma* sup_empty
- \+ *lemma* sup_insert
- \+ *lemma* sup_singleton
- \+ *lemma* sup_union
- \+ *lemma* sup_mono_fun
- \+ *lemma* le_sup
- \+ *lemma* sup_le
- \+ *lemma* sup_mono
- \+ *lemma* inf_empty
- \+ *lemma* inf_insert
- \+ *lemma* inf_singleton
- \+ *lemma* inf_union
- \+ *lemma* inf_mono_fun
- \+ *lemma* inf_le
- \+ *lemma* le_inf
- \+ *lemma* inf_mono
- \+/\- *theorem* subset_iff
- \+ *theorem* max_eq_sup_with_bot
- \+ *theorem* max_eq_inf_with_top
- \+/\- *theorem* subset_iff
- \+ *def* sup
- \+ *def* inf

Modified data/finsupp.lean
- \+/\- *lemma* single_add_erase
- \+ *lemma* erase_add_single
- \+ *lemma* induction₂
- \+/\- *lemma* single_add_erase

Modified data/option.lean
- \+ *theorem* ext

Modified linear_algebra/multivariate_polynomial.lean
- \- *lemma* sup_empty
- \- *lemma* sup_insert
- \- *lemma* sup_singleton
- \- *lemma* sup_union
- \- *lemma* sup_mono_fun
- \- *lemma* le_sup
- \- *lemma* sup_le
- \- *lemma* sup_mono
- \- *lemma* finset.bind_singleton2
- \- *def* sup

Modified order/bounded_lattice.lean
- \+ *theorem* some_le_some
- \+ *theorem* some_le
- \+ *theorem* some_le_some
- \+ *theorem* le_some
- \+ *def* with_bot
- \+ *def* with_top

Modified order/lattice.lean



## [2018-05-25 01:14:13-04:00](https://github.com/leanprover-community/mathlib/commit/94dc067)
refactor(order/lattice): move top/bot to bounded_lattice
#### Estimated changes
Modified order/bounded_lattice.lean
- \+ *theorem* le_top
- \+ *theorem* top_unique
- \+ *theorem* eq_top_iff
- \+ *theorem* top_le_iff
- \+ *theorem* not_top_lt
- \+ *theorem* bot_le
- \+ *theorem* bot_unique
- \+ *theorem* eq_bot_iff
- \+ *theorem* le_bot_iff
- \+ *theorem* not_lt_bot
- \+ *theorem* neq_bot_of_le_neq_bot
- \+ *theorem* top_sup_eq
- \+ *theorem* sup_top_eq
- \+ *theorem* bot_sup_eq
- \+ *theorem* sup_bot_eq
- \+ *theorem* sup_eq_bot_iff
- \+ *theorem* top_inf_eq
- \+ *theorem* inf_top_eq
- \+ *theorem* inf_eq_top_iff
- \+ *theorem* bot_inf_eq
- \+ *theorem* inf_bot_eq

Modified order/lattice.lean
- \- *theorem* le_top
- \- *theorem* top_unique
- \- *theorem* eq_top_iff
- \- *theorem* top_le_iff
- \- *theorem* not_top_lt
- \- *theorem* bot_le
- \- *theorem* bot_unique
- \- *theorem* eq_bot_iff
- \- *theorem* le_bot_iff
- \- *theorem* not_lt_bot
- \- *theorem* neq_bot_of_le_neq_bot
- \- *theorem* top_sup_eq
- \- *theorem* sup_top_eq
- \- *theorem* bot_sup_eq
- \- *theorem* sup_bot_eq
- \- *theorem* sup_eq_bot_iff
- \- *theorem* top_inf_eq
- \- *theorem* inf_top_eq
- \- *theorem* inf_eq_top_iff
- \- *theorem* bot_inf_eq
- \- *theorem* inf_bot_eq



## [2018-05-25 01:14:13-04:00](https://github.com/leanprover-community/mathlib/commit/4117ff4)
refactor(algebra/order_functions): reorganize new lemmas
#### Estimated changes
Modified algebra/order_functions.lean
- \+ *theorem* min_choice
- \+ *theorem* max_choice

Modified logic/basic.lean
- \- *theorem* if_choice
- \- *theorem* min_choice
- \- *theorem* max_choice

Modified order/lattice.lean



## [2018-05-24 15:55:26+02:00](https://github.com/leanprover-community/mathlib/commit/9303bc0)
feat(analysis/ennreal): add further type class instances for nonnegative reals
#### Estimated changes
Modified algebra/ordered_group.lean
- \+ *lemma* le_zero_iff_eq

Modified analysis/nnreal.lean
- \- *lemma* val_zero
- \- *lemma* val_one
- \- *lemma* add_val
- \- *lemma* mul_val
- \- *lemma* le_zero_iff_eq

Modified set_theory/cofinality.lean



## [2018-05-24 15:55:26+02:00](https://github.com/leanprover-community/mathlib/commit/02f8f48)
feat(analysis/nnreal): define the nonnegative reals
NB: This file has a lot in common with `ennreal.lean`, the extended nonnegative reals.
#### Estimated changes
Created analysis/nnreal.lean
- \+ *lemma* val_zero
- \+ *lemma* val_one
- \+ *lemma* add_val
- \+ *lemma* mul_val
- \+ *lemma* le_zero_iff_eq



## [2018-05-24 09:39:41+02:00](https://github.com/leanprover-community/mathlib/commit/2c94668)
fix(data/fin): rename raise_fin -> fin.raise; simp lemmas for fin ([#138](https://github.com/leanprover-community/mathlib/pull/138))
#### Estimated changes
Modified data/fin.lean
- \+ *lemma* succ_val
- \+ *lemma* pred_val
- \+ *def* raise
- \- *def* raise_fin



## [2018-05-23 19:20:55+02:00](https://github.com/leanprover-community/mathlib/commit/d91a267)
fix(data/list/basic): protected list.sigma ([#140](https://github.com/leanprover-community/mathlib/pull/140))
#### Estimated changes
Modified data/list/basic.lean
- \- *def* sigma



## [2018-05-23 19:20:25+02:00](https://github.com/leanprover-community/mathlib/commit/94a4b07)
doc(docs/extras): some notes on well founded recursion ([#127](https://github.com/leanprover-community/mathlib/pull/127))
#### Estimated changes
Created docs/extras/well_founded_recursion.md
- \+ *lemma* prod_factors
- \+ *lemma* prod_factors
- \+ *lemma* strong_induction_on
- \+ *def* gcd
- \+ *def* gcd
- \+ *def* gcd
- \+ *def* gcd
- \+ *def* gcd
- \+ *def* gcd



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

Created tactic/split_ifs.lean

Created tests/split_ifs.lean



## [2018-05-23 17:29:32+02:00](https://github.com/leanprover-community/mathlib/commit/f458eef)
feat(analysis/topology): add tendsto and continuity rules for big operators
#### Estimated changes
Modified analysis/measure_theory/borel_space.lean

Modified analysis/topology/infinite_sum.lean

Modified analysis/topology/topological_structures.lean
- \+ *lemma* continuous_mul'
- \+/\- *lemma* continuous_mul
- \+ *lemma* tendsto_mul'
- \+/\- *lemma* tendsto_mul
- \+ *lemma* tendsto_list_prod
- \+ *lemma* continuous_list_prod
- \+ *lemma* tendsto_multiset_prod
- \+ *lemma* tendsto_finset_prod
- \+ *lemma* continuous_multiset_prod
- \+ *lemma* continuous_finset_prod
- \+/\- *lemma* continuous_add'
- \+/\- *lemma* continuous_add
- \+/\- *lemma* tendsto_add'
- \+/\- *lemma* tendsto_add
- \+ *lemma* tendsto_list_sum
- \+ *lemma* continuous_list_sum
- \+ *lemma* tendsto_multiset_sum
- \+ *lemma* tendsto_finset_sum
- \+ *lemma* continuous_multiset_sum
- \+ *lemma* continuous_finset_sum
- \+/\- *lemma* continuous_add'
- \+/\- *lemma* continuous_add
- \+/\- *lemma* tendsto_add'
- \+/\- *lemma* tendsto_add
- \- *lemma* tendsto_sum
- \+/\- *lemma* continuous_mul
- \+/\- *lemma* tendsto_mul



## [2018-05-23 17:17:56+02:00](https://github.com/leanprover-community/mathlib/commit/a54be05)
feat(analysis/topology): add continuity rules for supr, Sup, and pi spaces
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+/\- *lemma* continuous_Inf_rng
- \+/\- *lemma* continuous_infi_rng
- \+ *lemma* continuous_Sup_dom
- \+ *lemma* continuous_Sup_rng
- \+ *lemma* continuous_supr_dom
- \+ *lemma* continuous_supr_rng
- \+/\- *lemma* continuous_top
- \+/\- *lemma* continuous_bot
- \+/\- *lemma* continuous_subtype_nhds_cover
- \+ *lemma* continuous_pi
- \+ *lemma* continuous_apply
- \+/\- *lemma* nhds_pi
- \+/\- *lemma* compact_pi_infinite
- \+/\- *lemma* continuous_Inf_rng
- \+/\- *lemma* continuous_infi_rng
- \+/\- *lemma* continuous_top
- \+/\- *lemma* continuous_bot
- \+/\- *lemma* continuous_subtype_nhds_cover
- \+/\- *lemma* nhds_pi
- \+/\- *lemma* compact_pi_infinite



## [2018-05-23 15:22:09+02:00](https://github.com/leanprover-community/mathlib/commit/cff886b)
feat(data/finset): max and min
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* max_empty
- \+ *theorem* max_insert
- \+ *theorem* max_singleton
- \+ *theorem* max_of_mem
- \+ *theorem* mem_of_max
- \+ *theorem* le_max_of_mem
- \+ *theorem* min_empty
- \+ *theorem* min_insert
- \+ *theorem* min_singleton
- \+ *theorem* min_of_mem
- \+ *theorem* mem_of_min
- \+ *theorem* le_min_of_mem

Modified data/option.lean
- \+ *theorem* lift_or_get_choice
- \- *theorem* lift_or_get_is_some_left
- \- *theorem* lift_or_get_is_some_right

Modified logic/basic.lean
- \+ *theorem* if_choice
- \+ *theorem* min_choice
- \+ *theorem* max_choice

Modified order/lattice.lean



## [2018-05-23 15:22:09+02:00](https://github.com/leanprover-community/mathlib/commit/d1ea272)
feat(data/option): lift_or_get
#### Estimated changes
Modified data/option.lean
- \+ *theorem* lift_or_get_is_some_left
- \+ *theorem* lift_or_get_is_some_right
- \+ *def* lift_or_get



## [2018-05-22 05:26:41-04:00](https://github.com/leanprover-community/mathlib/commit/d62bf56)
feat(computability/halting): halting problem
#### Estimated changes
Created data/computability/halting.lean
- \+ *theorem* merge'
- \+ *theorem* merge'
- \+ *theorem* merge
- \+ *theorem* cond
- \+ *theorem* sum_cases
- \+ *theorem* computable_pred.of_eq
- \+ *theorem* rice
- \+ *theorem* rice₂
- \+ *theorem* halting_problem
- \+ *def* computable_pred
- \+ *def* re_pred

Modified data/computability/partrec.lean
- \+ *theorem* rfind_opt_spec
- \+ *theorem* rfind_opt_dom
- \+ *theorem* rfind_opt_mono
- \+ *theorem* primrec₂.to_comp
- \+/\- *theorem* encode_iff
- \+/\- *theorem* option_some
- \+ *theorem* map_encode_iff
- \+ *theorem* rfind_opt
- \+ *theorem* bind_decode2_iff
- \- *theorem* cond
- \- *theorem* sum_cases
- \- *theorem* fix
- \+/\- *theorem* encode_iff
- \+/\- *theorem* option_some
- \+ *def* rfind_opt

Modified data/computability/partrec_code.lean
- \+ *theorem* eval_const
- \+ *theorem* eval_id
- \+ *theorem* eval_curry
- \+ *theorem* const_prim
- \+ *theorem* curry_prim
- \+ *theorem* fixed_point
- \+ *theorem* fixed_point₂
- \+ *def* curry
- \- *def* evaln

Modified data/computability/primrec.lean
- \+/\- *theorem* option_is_some
- \+ *theorem* option_guard
- \+ *theorem* option_orelse
- \+/\- *theorem* option_is_some

Modified data/encodable.lean
- \+ *theorem* mem_decode2
- \+ *theorem* decode2_inj
- \+ *theorem* encodek2
- \+ *def* decode2

Modified data/option.lean
- \+ *theorem* orelse_some'
- \+ *theorem* orelse_some
- \+ *theorem* orelse_none'
- \+ *theorem* orelse_none

Modified data/pfun.lean
- \+ *theorem* get_mem
- \+ *theorem* get_eq_of_mem
- \+ *theorem* eq_none_iff'
- \+ *theorem* bind_some_right



## [2018-05-21 11:44:37-04:00](https://github.com/leanprover-community/mathlib/commit/f0bcba5)
feat(computability/partrec_code): Kleene normal form theorem
among other things
#### Estimated changes
Modified category/basic.lean
- \+ *theorem* guard_true
- \+ *theorem* guard_false

Modified data/computability/partrec.lean
- \+ *theorem* unpair
- \+ *theorem* succ
- \+ *theorem* pred
- \+ *theorem* nat_bodd
- \+ *theorem* nat_div2
- \+ *theorem* sum_inl
- \+ *theorem* sum_inr
- \+ *theorem* list_cons
- \+ *theorem* list_reverse
- \+ *theorem* list_nth
- \+ *theorem* list_append
- \+ *theorem* list_concat
- \+ *theorem* list_length
- \+ *theorem* nat_cases_right
- \+ *theorem* encode_iff
- \+ *theorem* option_some
- \+ *theorem* option_some_iff
- \+ *theorem* bind_decode_iff
- \+ *theorem* map_decode_iff
- \+/\- *theorem* nat_elim
- \+/\- *theorem* nat_cases
- \+ *theorem* cond
- \+ *theorem* option_cases
- \+ *theorem* option_bind
- \+ *theorem* option_map
- \+ *theorem* sum_cases
- \+ *theorem* nat_strong_rec
- \+ *theorem* option_some_iff
- \+ *theorem* option_cases_right
- \+ *theorem* sum_cases_right
- \+ *theorem* sum_cases_left
- \+ *theorem* fix
- \+/\- *theorem* nat_elim
- \+/\- *theorem* nat_cases
- \- *theorem* rfind'
- \- *theorem* exists_code
- \- *theorem* pair_prim
- \- *theorem* comp_prim
- \- *theorem* prec_prim
- \- *theorem* rfind_prim
- \- *theorem* rec_prim
- \- *theorem* rec_part
- \- *def* encode_code
- \- *def* of_nat_code
- \- *def* eval
- \- *def* evaln

Created data/computability/partrec_code.lean
- \+ *theorem* rfind'
- \+ *theorem* encode_code_eq
- \+ *theorem* of_nat_code_eq
- \+ *theorem* encode_lt_pair
- \+ *theorem* encode_lt_comp
- \+ *theorem* encode_lt_prec
- \+ *theorem* encode_lt_rfind'
- \+ *theorem* pair_prim
- \+ *theorem* comp_prim
- \+ *theorem* prec_prim
- \+ *theorem* rfind_prim
- \+ *theorem* rec_prim'
- \+ *theorem* rec_prim
- \+ *theorem* rec_computable
- \+ *theorem* exists_code
- \+ *theorem* evaln_bound
- \+ *theorem* evaln_mono
- \+ *theorem* evaln_sound
- \+ *theorem* evaln_complete
- \+ *theorem* evaln_prim
- \+ *theorem* eval_part
- \+ *def* encode_code
- \+ *def* of_nat_code
- \+ *def* eval
- \+ *def* evaln
- \+ *def* evaln

Modified data/computability/primrec.lean
- \+ *theorem* option_is_some
- \+ *theorem* nat_min
- \+ *theorem* nat_max
- \+ *theorem* list_range

Modified data/nat/pairing.lean
- \+ *theorem* mkpair_lt_mkpair_left
- \+ *theorem* mkpair_lt_mkpair_right

Modified data/option.lean
- \+ *theorem* none_bind'
- \+ *theorem* some_bind'
- \+ *theorem* bind_eq_some'
- \+ *theorem* map_eq_some'
- \+ *theorem* guard_eq_some'

Modified data/pfun.lean
- \+ *theorem* mem_coe
- \+ *theorem* bind_dom
- \+/\- *theorem* mem_fix_iff
- \+ *theorem* fix_induction
- \+/\- *theorem* mem_fix_iff



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
- \+ *def* rcases_patt_inverted

Modified tactic/rcases.lean
- \+ *def* list_Sigma
- \+ *def* list_Pi

Modified tests/tactics.lean



## [2018-05-19 21:28:26-04:00](https://github.com/leanprover-community/mathlib/commit/fc20442)
feat(computability/partrec): partial recursion, Godel numbering
#### Estimated changes
Modified data/bool.lean
- \+ *lemma* tt_eq_to_bool_iff
- \+ *lemma* ff_eq_to_bool_iff

Modified data/computability/partrec.lean
- \+ *theorem* rfind_spec
- \+ *theorem* rfind_min
- \+ *theorem* rfind_dom
- \+ *theorem* rfind_dom'
- \+ *theorem* mem_rfind
- \+ *theorem* rfind_min'
- \+ *theorem* rfind_zero_none
- \+/\- *theorem* of_eq
- \+ *theorem* of_eq_tot
- \+ *theorem* of_primrec
- \+ *theorem* none
- \+ *theorem* prec'
- \+ *theorem* ppred
- \+ *theorem* primrec.to_comp
- \+ *theorem* computable.part
- \+ *theorem* computable₂.part
- \+/\- *theorem* of_eq
- \+ *theorem* const
- \+ *theorem* of_option
- \+ *theorem* to₂
- \+ *theorem* fst
- \+ *theorem* snd
- \+ *theorem* pair
- \+/\- *theorem* of_eq
- \+ *theorem* of_eq_tot
- \+ *theorem* none
- \+ *theorem* const'
- \+ *theorem* map
- \+ *theorem* to₂
- \+ *theorem* nat_elim
- \+ *theorem* comp
- \+ *theorem* nat_iff
- \+ *theorem* unpaired
- \+ *theorem* unpaired'
- \+ *theorem* comp
- \+ *theorem* comp₂
- \+ *theorem* comp
- \+ *theorem* comp₂
- \+ *theorem* nat_elim
- \+ *theorem* nat_cases
- \+ *theorem* comp
- \+ *theorem* comp₂
- \+ *theorem* rfind
- \+ *theorem* cond
- \+ *theorem* sum_cases
- \+ *theorem* fix
- \+ *theorem* rfind'
- \+ *theorem* exists_code
- \+ *theorem* pair_prim
- \+ *theorem* comp_prim
- \+ *theorem* prec_prim
- \+ *theorem* rfind_prim
- \+ *theorem* rec_prim
- \+ *theorem* rec_part
- \+/\- *theorem* of_eq
- \- *theorem* prim
- \+ *def* rfind_x
- \+ *def* rfind
- \+ *def* partrec
- \+ *def* partrec₂
- \+ *def* computable
- \+ *def* computable₂
- \+ *def* encode_code
- \+ *def* of_nat_code
- \+ *def* eval
- \+ *def* evaln

Modified data/computability/primrec.lean
- \+/\- *theorem* of_eq
- \+/\- *theorem* of_eq
- \+/\- *theorem* comp
- \+/\- *theorem* of_eq
- \+ *theorem* list_concat
- \+ *theorem* nat_strong_rec
- \+/\- *theorem* of_eq
- \+/\- *theorem* of_eq
- \+/\- *theorem* comp
- \+/\- *theorem* of_eq

Modified data/denumerable.lean
- \+ *def* list_nat_equiv_nat
- \+ *def* list_equiv_self_of_equiv_nat

Modified data/encodable.lean
- \+ *theorem* encode_nat
- \+ *theorem* decode_nat

Modified data/equiv.lean
- \- *def* list_nat_equiv_nat
- \- *def* list_equiv_self_of_equiv_nat

Modified data/nat/basic.lean
- \+ *lemma* bodd_bit0
- \+ *lemma* bodd_bit1
- \+ *lemma* div2_bit0
- \+ *lemma* div2_bit1

Modified data/nat/pairing.lean
- \+ *theorem* unpair_le_left
- \+ *theorem* le_mkpair_right
- \+ *theorem* unpair_le_right
- \- *theorem* unpair_le

Modified data/pfun.lean
- \+/\- *theorem* dom_iff_mem
- \+ *theorem* not_mem_none
- \+ *theorem* eq_some_iff
- \+ *theorem* eq_none_iff
- \+ *theorem* coe_none
- \+ *theorem* coe_some
- \+ *theorem* map_none
- \+ *theorem* mem_assert
- \+ *theorem* mem_assert_iff
- \+ *theorem* bind_none
- \+/\- *theorem* bind_some_eq_map
- \+ *theorem* bind_map
- \+ *theorem* map_bind
- \+ *theorem* map_map
- \+ *theorem* map_id'
- \+/\- *theorem* bind_defined
- \+ *theorem* dom_of_mem_fix
- \+ *theorem* mem_fix_iff
- \+/\- *theorem* dom_iff_mem
- \- *theorem* eq_some_of_mem
- \+/\- *theorem* bind_some_eq_map
- \+/\- *theorem* bind_defined
- \+/\- *def* pfun
- \+ *def* fix
- \- *def* bind
- \+/\- *def* pfun



## [2018-05-18 05:14:19-04:00](https://github.com/leanprover-community/mathlib/commit/38d5536)
feat(computability/partrec): starting work on partial recursive funcs
#### Estimated changes
Created data/computability/partrec.lean
- \+ *theorem* of_eq
- \+ *theorem* prim

Modified data/computability/primrec.lean
- \+/\- *def* unpaired
- \+/\- *def* unpaired

Modified data/pfun.lean
- \+/\- *theorem* dom_iff_mem
- \+/\- *theorem* mem_unique
- \+/\- *theorem* mem_some
- \+ *theorem* mem_some_iff
- \+ *theorem* eq_some_of_mem
- \+ *theorem* mem_to_option
- \+ *theorem* mem_of_option
- \+/\- *theorem* to_of_option
- \+/\- *theorem* of_to_option
- \+ *theorem* mem_map
- \+ *theorem* mem_map_iff
- \+ *theorem* map_some
- \+/\- *theorem* mem_bind
- \+ *theorem* mem_bind_iff
- \+ *theorem* bind_some
- \+/\- *theorem* bind_some_eq_map
- \+ *theorem* ret_eq_some
- \+ *theorem* map_eq_map
- \+ *theorem* bind_eq_bind
- \+ *theorem* lift_eq_coe
- \+ *theorem* coe_val
- \+/\- *theorem* to_of_option
- \+/\- *theorem* of_to_option
- \+/\- *theorem* dom_iff_mem
- \+/\- *theorem* bind_some_eq_map
- \- *theorem* some_bind
- \+/\- *theorem* mem_unique
- \+/\- *theorem* mem_some
- \- *theorem* mem_ret
- \- *theorem* mem_ret_iff
- \- *theorem* eq_ret_of_mem
- \+/\- *theorem* mem_bind
- \- *theorem* exists_of_mem_bind
- \+ *def* ext'
- \+ *def* ext
- \+ *def* none
- \+ *def* some
- \+/\- *def* of_option
- \+ *def* bind
- \+ *def* map
- \+ *def* ext'
- \+ *def* ext
- \+ *def* bind
- \+ *def* map
- \+/\- *def* of_option



## [2018-05-18 05:10:04-04:00](https://github.com/leanprover-community/mathlib/commit/92feaf9)
feat(computability/primrec): list definitions are primrec
#### Estimated changes
Modified data/computability/primrec.lean
- \+ *theorem* list_nth₁
- \+ *theorem* to₂
- \+ *theorem* nat_elim₁
- \+ *theorem* nat_cases₁
- \+ *theorem* nat_iterate
- \+ *theorem* option_bind₁
- \+ *theorem* option_map₁
- \+ *theorem* list_find_index₁
- \+ *theorem* list_index_of₁
- \+ *theorem* sum_inl
- \+ *theorem* sum_inr
- \+ *theorem* sum_cases
- \+ *theorem* list_cons
- \+ *theorem* list_cases
- \+ *theorem* list_foldl
- \+ *theorem* list_reverse
- \+ *theorem* list_foldr
- \+ *theorem* list_rec
- \+/\- *theorem* list_nth
- \+/\- *theorem* list_inth
- \+ *theorem* list_append
- \+ *theorem* list_map
- \+ *theorem* list_join
- \+ *theorem* list_length
- \+/\- *theorem* list_find_index
- \+/\- *theorem* list_index_of
- \+/\- *theorem* list_nth
- \- *theorem* nat_elim1
- \- *theorem* nat_cases1
- \- *theorem* option_bind1
- \- *theorem* option_map1
- \+/\- *theorem* list_inth
- \+/\- *theorem* list_find_index
- \+/\- *theorem* list_index_of

Modified data/denumerable.lean
- \+ *theorem* list_of_nat_zero
- \+ *theorem* list_of_nat_succ

Modified data/encodable.lean
- \+ *theorem* encode_inl
- \+ *theorem* encode_inr
- \+ *theorem* decode_sum_val
- \+ *theorem* encode_list_nil
- \+ *theorem* encode_list_cons
- \+ *theorem* decode_list_zero
- \+ *theorem* decode_list_succ
- \+ *theorem* length_le_encode

Modified data/list/basic.lean
- \+ *theorem* drop_nil

Modified data/nat/basic.lean
- \+ *theorem* iterate_zero
- \+ *theorem* iterate_succ
- \+ *theorem* iterate_add
- \+ *theorem* iterate_succ'
- \- *def* foldl
- \- *def* foldr

Modified data/nat/pairing.lean
- \+/\- *theorem* mkpair_unpair
- \+/\- *theorem* unpair_mkpair
- \+/\- *theorem* unpair_lt
- \+/\- *theorem* unpair_le
- \+ *theorem* le_mkpair_left
- \+/\- *theorem* mkpair_unpair
- \+/\- *theorem* unpair_mkpair
- \+/\- *theorem* unpair_lt
- \+/\- *theorem* unpair_le
- \+/\- *def* mkpair
- \+/\- *def* unpair
- \+/\- *def* mkpair
- \+/\- *def* unpair

Modified order/order_iso.lean

Modified set_theory/ordinal.lean
- \+ *theorem* iterate_le_nfp
- \- *theorem* foldr_le_nfp



## [2018-05-17 04:23:08-04:00](https://github.com/leanprover-community/mathlib/commit/e017f0f)
feat(data/computability): primrec, denumerable
#### Estimated changes
Modified analysis/limits.lean

Modified analysis/topology/infinite_sum.lean

Modified analysis/topology/topological_space.lean
- \+ *lemma* sUnion_basis_of_is_open
- \+ *lemma* Union_basis_of_is_open

Modified data/bool.lean
- \+ *theorem* to_bool_not
- \+ *theorem* to_bool_and
- \+ *theorem* to_bool_or
- \+/\- *theorem* cond_ff
- \+/\- *theorem* cond_tt
- \+ *theorem* cond_to_bool
- \+/\- *theorem* cond_ff
- \+/\- *theorem* cond_tt

Created data/computability/primrec.lean
- \+ *theorem* elim_zero
- \+ *theorem* elim_succ
- \+ *theorem* cases_zero
- \+ *theorem* cases_succ
- \+ *theorem* of_eq
- \+ *theorem* const
- \+ *theorem* prec1
- \+ *theorem* cases1
- \+ *theorem* cases
- \+ *theorem* swap'
- \+ *theorem* pred
- \+ *theorem* add
- \+ *theorem* sub
- \+ *theorem* mul
- \+ *theorem* pow
- \+ *theorem* dom_denumerable
- \+ *theorem* nat_iff
- \+ *theorem* encdec
- \+ *theorem* option_some
- \+ *theorem* of_eq
- \+ *theorem* const
- \+ *theorem* comp
- \+ *theorem* succ
- \+ *theorem* pred
- \+ *theorem* encode_iff
- \+ *theorem* of_nat_iff
- \+ *theorem* option_some_iff
- \+ *theorem* fst
- \+ *theorem* snd
- \+ *theorem* pair
- \+ *theorem* unpair
- \+ *theorem* list_nth
- \+ *theorem* of_eq
- \+ *theorem* const
- \+ *theorem* left
- \+ *theorem* right
- \+ *theorem* mkpair
- \+ *theorem* unpaired
- \+ *theorem* unpaired'
- \+ *theorem* encode_iff
- \+ *theorem* option_some_iff
- \+ *theorem* of_nat_iff
- \+ *theorem* uncurry
- \+ *theorem* curry
- \+ *theorem* primrec.comp₂
- \+ *theorem* primrec₂.comp
- \+ *theorem* primrec₂.comp₂
- \+ *theorem* primrec_pred.comp
- \+ *theorem* primrec_rel.comp
- \+ *theorem* primrec_rel.comp₂
- \+ *theorem* primrec_pred.of_eq
- \+ *theorem* primrec_rel.of_eq
- \+ *theorem* swap
- \+ *theorem* nat_iff
- \+ *theorem* nat_iff'
- \+ *theorem* nat_elim
- \+ *theorem* nat_elim'
- \+ *theorem* nat_elim1
- \+ *theorem* nat_cases'
- \+ *theorem* nat_cases
- \+ *theorem* nat_cases1
- \+ *theorem* option_cases
- \+ *theorem* option_bind
- \+ *theorem* option_bind1
- \+ *theorem* option_map
- \+ *theorem* option_map1
- \+ *theorem* option_iget
- \+ *theorem* bind_decode_iff
- \+ *theorem* map_decode_iff
- \+ *theorem* nat_add
- \+ *theorem* nat_sub
- \+ *theorem* nat_mul
- \+ *theorem* cond
- \+ *theorem* ite
- \+ *theorem* list_inth
- \+ *theorem* nat_le
- \+ *theorem* dom_bool
- \+ *theorem* dom_bool₂
- \+ *theorem* list_find_index
- \+ *theorem* list_index_of
- \+ *theorem* dom_fintype
- \+ *theorem* nat_bodd_div2
- \+ *theorem* nat_bodd
- \+ *theorem* nat_div2
- \+ *theorem* nat_bit0
- \+ *theorem* nat_bit1
- \+ *theorem* nat_bit
- \+ *theorem* nat_div_mod
- \+ *theorem* nat_div
- \+ *theorem* nat_mod
- \+ *def* elim
- \+ *def* cases
- \+ *def* unpaired
- \+ *def* of_equiv
- \+ *def* primrec
- \+ *def* primrec₂
- \+ *def* primrec_pred
- \+ *def* primrec_rel

Created data/denumerable.lean
- \+ *lemma* lower_raise
- \+ *lemma* raise_lower
- \+ *lemma* raise_chain
- \+ *lemma* raise_sorted
- \+ *lemma* lower_raise'
- \+ *lemma* raise_lower'
- \+ *lemma* raise'_chain
- \+ *lemma* raise'_sorted
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
- \+ *theorem* denumerable_list_aux
- \+ *def* of_nat
- \+ *def* eqv
- \+ *def* mk'
- \+ *def* of_equiv
- \+ *def* equiv₂
- \+ *def* lower
- \+ *def* raise
- \+ *def* lower'
- \+ *def* raise'
- \+ *def* raise'_finset
- \+ *def* pair

Modified data/encodable.lean
- \+/\- *theorem* encode_injective
- \+ *theorem* encode_of_equiv
- \+ *theorem* decode_of_equiv
- \+ *theorem* encode_star
- \+ *theorem* decode_unit_zero
- \+ *theorem* decode_unit_succ
- \+ *theorem* encode_none
- \+ *theorem* encode_some
- \+ *theorem* decode_option_zero
- \+ *theorem* decode_option_succ
- \+ *theorem* encode_tt
- \+ *theorem* encode_ff
- \+ *theorem* decode_zero
- \+ *theorem* decode_one
- \+ *theorem* decode_ge_two
- \+ *theorem* decode_sigma_val
- \+ *theorem* encode_sigma_val
- \+ *theorem* decode_prod_val
- \+ *theorem* encode_prod_val
- \+/\- *theorem* encode_injective
- \+ *def* decidable_eq_of_encodable
- \+ *def* of_left_injection
- \+ *def* of_left_inverse
- \+ *def* of_equiv
- \+ *def* encode_sum
- \+ *def* decode_sum
- \+ *def* encode_sigma
- \+ *def* decode_sigma
- \+ *def* encode_list
- \+ *def* decode_list
- \+ *def* encode_multiset
- \+ *def* decode_multiset
- \+ *def* encode_subtype
- \+ *def* decode_subtype
- \- *def* encodable_of_left_injection
- \- *def* encodable_of_equiv

Modified data/equiv.lean
- \+ *theorem* symm_symm

Modified data/finset.lean
- \+ *lemma* attach_map_val
- \+ *theorem* map_val
- \+ *theorem* map_empty
- \+ *theorem* mem_map
- \+ *theorem* mem_map_of_mem
- \+ *theorem* map_to_finset
- \+ *theorem* map_refl
- \+ *theorem* map_map
- \+ *theorem* map_subset_map
- \+ *theorem* map_filter
- \+ *theorem* map_union
- \+ *theorem* map_inter
- \+ *theorem* map_singleton
- \+ *theorem* map_insert
- \+ *theorem* map_eq_empty
- \+ *theorem* map_eq_image
- \+ *theorem* sort_sorted_lt
- \+ *def* map

Modified data/fintype.lean
- \+ *theorem* exists_univ_list

Modified data/list/basic.lean
- \+ *lemma* foldl_ext
- \+ *lemma* foldr_ext
- \+ *lemma* filter_congr
- \+ *theorem* nth_map
- \+ *theorem* nth_le_map
- \+ *theorem* nth_le_map'
- \+ *theorem* pairwise.and
- \+ *theorem* pairwise.imp₂
- \+ *theorem* map_add_range'
- \+ *theorem* range_succ_eq_map
- \+ *theorem* range'_eq_map_range
- \+ *theorem* reverse_range'

Modified data/list/sort.lean
- \+/\- *theorem* eq_of_sorted_of_perm
- \+ *theorem* merge_sort_eq_self
- \+/\- *theorem* eq_of_sorted_of_perm

Modified data/multiset.lean

Modified data/nat/basic.lean

Modified data/nat/pairing.lean
- \+/\- *theorem* mkpair_unpair
- \+/\- *theorem* unpair_mkpair
- \+/\- *theorem* mkpair_unpair
- \+/\- *theorem* unpair_mkpair

Modified data/option.lean
- \+ *theorem* map_none'
- \+ *theorem* map_some'

Modified data/rat.lean

Modified data/semiquot.lean
- \+ *theorem* pure_inj
- \+ *theorem* is_pure_iff
- \+ *theorem* is_pure.mono
- \+ *theorem* is_pure.min

Modified data/seq/parallel.lean

Modified data/seq/seq.lean

Modified data/seq/wseq.lean

Modified data/set/countable.lean

Modified logic/basic.lean
- \+ *lemma* and.right_comm
- \+ *lemma* and.rotate

Modified logic/embedding.lean
- \+ *def* subtype

Modified order/basic.lean



## [2018-05-16 10:16:22+02:00](https://github.com/leanprover-community/mathlib/commit/fe7d573)
refactor(data/set/enumerate): proof enumeration_inj using wlog
#### Estimated changes
Modified data/set/enumerate.lean
- \+/\- *lemma* enumerate_inj
- \+/\- *lemma* enumerate_inj



## [2018-05-16 10:16:22+02:00](https://github.com/leanprover-community/mathlib/commit/d8c33e8)
feat(tactic): generalize wlog to support multiple variables and cases, allow to provide case rule
#### Estimated changes
Modified tactic/default.lean

Modified tactic/interactive.lean

Created tactic/wlog.lean

Modified tests/tactics.lean



## [2018-05-10 15:29:47+02:00](https://github.com/leanprover-community/mathlib/commit/2cd640a)
feat(data/multiset): add sections
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* bind_map

Modified data/multiset.lean
- \+ *lemma* map_id'
- \+ *lemma* prod_map_one
- \+ *lemma* sum_map_zero
- \+ *lemma* sum_map_mul_left
- \+ *lemma* sum_map_mul_right
- \+/\- *lemma* map_bind
- \+ *lemma* bind_map
- \+ *lemma* bind_assoc
- \+/\- *lemma* bind_bind
- \+ *lemma* bind_map_comm
- \+ *lemma* rel_bind
- \+ *lemma* sections_zero
- \+ *lemma* sections_cons
- \+ *lemma* coe_sections
- \+ *lemma* sections_add
- \+ *lemma* mem_sections
- \+ *lemma* card_sections
- \+ *lemma* prod_map_sum
- \+/\- *lemma* map_bind
- \+/\- *lemma* bind_bind
- \+ *theorem* bind_zero
- \+ *theorem* bind_add
- \+ *theorem* bind_cons
- \+ *def* sections



## [2018-05-10 15:29:29+02:00](https://github.com/leanprover-community/mathlib/commit/62833ca)
feat(data/multiset): add relator
#### Estimated changes
Modified data/multiset.lean
- \+ *lemma* zero_ne_cons
- \+ *lemma* cons_ne_zero
- \+ *lemma* cons_eq_cons
- \+ *lemma* rel_flip
- \+ *lemma* rel_eq_refl
- \+ *lemma* rel_eq
- \+ *lemma* rel.mono
- \+ *lemma* rel.add
- \+ *lemma* rel_flip_eq
- \+ *lemma* rel_zero_left
- \+ *lemma* rel_zero_right
- \+ *lemma* rel_cons_left
- \+ *lemma* rel_cons_right
- \+ *lemma* rel_add_left
- \+ *lemma* rel_add_right
- \+ *lemma* rel_map_left
- \+ *lemma* rel_map_right
- \+ *lemma* rel_join
- \+ *lemma* rel_map
- \+ *lemma* card_eq_card_of_rel

Modified tests/mk_iff_of_inductive.lean



## [2018-05-10 12:12:25+02:00](https://github.com/leanprover-community/mathlib/commit/d10c3bb)
fix(order/complete_boolean_algebra): replace finish proof by simp (finish was very slow)
#### Estimated changes
Modified order/complete_boolean_algebra.lean



## [2018-05-09 06:19:46-04:00](https://github.com/leanprover-community/mathlib/commit/fc6f57a)
feat(data/list/basic): list.forall2, list.sections
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* forall₂_cons
- \+ *theorem* forall₂_nil_left
- \+ *theorem* forall₂_nil_right
- \+ *theorem* forall₂_length_eq
- \+ *theorem* forall₂_zip
- \+ *theorem* forall₂_iff_zip
- \+ *theorem* mem_sections
- \+ *theorem* mem_sections_length
- \+ *def* sections



## [2018-05-09 06:04:38-04:00](https://github.com/leanprover-community/mathlib/commit/42f5ea0)
feat(data/semiquot): semiquotient types
#### Estimated changes
Modified data/fp/basic.lean
- \+ *def* int.shift2
- \- *def* shift2
- \- *def* default_nan

Modified data/quot.lean
- \+ *theorem* true_equivalence
- \+ *def* bind
- \+ *def* map

Modified data/rat.lean
- \+ *theorem* num_nonneg_iff_zero_le
- \+ *theorem* num_pos_iff_pos

Created data/semiquot.lean
- \+ *theorem* ext_s
- \+ *theorem* ext
- \+ *theorem* exists_mem
- \+ *theorem* eq_mk_of_mem
- \+ *theorem* ne_empty
- \+ *theorem* mem_pure'
- \+ *theorem* blur_eq_blur'
- \+ *theorem* mem_blur'
- \+ *theorem* lift_on_of_mem
- \+ *theorem* mem_map
- \+ *theorem* mem_bind
- \+ *theorem* mem_pure
- \+ *theorem* mem_pure_self
- \+ *theorem* pure_le
- \+ *theorem* get_mem
- \+ *theorem* eq_pure
- \+ *theorem* pure_is_pure
- \+ *theorem* is_pure_of_subsingleton
- \+ *theorem* mem_univ
- \+ *theorem* univ_unique
- \+ *theorem* is_pure_univ
- \+ *def* mk
- \+ *def* blur'
- \+ *def* blur
- \+ *def* of_trunc
- \+ *def* to_trunc
- \+ *def* lift_on
- \+ *def* map
- \+ *def* bind
- \+ *def* is_pure
- \+ *def* get
- \+ *def* univ

Modified data/set/lattice.lean
- \+ *theorem* mem_bUnion_iff
- \+ *theorem* mem_bInter_iff

Modified logic/basic.lean
- \+ *theorem* eq_equivalence



## [2018-05-09 06:04:38-04:00](https://github.com/leanprover-community/mathlib/commit/b31c30d)
refactor(logic/function): constructive proof of cantor_injective
#### Estimated changes
Modified logic/function.lean
- \+/\- *theorem* cantor_injective
- \+/\- *theorem* cantor_injective



## [2018-05-09 11:41:31+02:00](https://github.com/leanprover-community/mathlib/commit/54df4d9)
feat(linear_algebra/multivariate_polynomial): change order of eval arguments; show that eval is ring homomorphism
(closes https://github.com/leanprover/mathlib/pull/134)
#### Estimated changes
Modified linear_algebra/multivariate_polynomial.lean
- \+/\- *def* eval
- \+/\- *def* eval



## [2018-05-09 10:46:03+02:00](https://github.com/leanprover-community/mathlib/commit/b5eddd8)
fix(data/set/basic): mark subset.refl as @[refl]
#### Estimated changes
Modified analysis/measure_theory/outer_measure.lean

Modified data/set/basic.lean
- \+/\- *theorem* subset.refl
- \+/\- *theorem* subset.refl



## [2018-05-04 16:10:27+02:00](https://github.com/leanprover-community/mathlib/commit/e4c64fd)
feat(tactic/mk_iff_of_inductive_prop): add tactic to represent inductives using logical connectives
#### Estimated changes
Modified data/list/basic.lean

Modified logic/relation.lean
- \+/\- *lemma* refl_gen.to_refl_trans_gen
- \+/\- *lemma* cases_tail
- \+/\- *lemma* refl_gen.to_refl_trans_gen
- \+/\- *lemma* cases_tail
- \- *lemma* cases_tail_iff

Modified tactic/default.lean

Created tactic/mk_iff_of_inductive_prop.lean

Created tests/mk_iff_of_inductive.lean



## [2018-05-03 13:46:52-04:00](https://github.com/leanprover-community/mathlib/commit/fa7a180)
feat(tactic/solve_by_elim): make solve_by_elim easier to use correctly ([#131](https://github.com/leanprover-community/mathlib/pull/131))
#### Estimated changes
Modified tactic/interactive.lean



## [2018-05-03 14:41:35+02:00](https://github.com/leanprover-community/mathlib/commit/ef43edf)
feat(data/finset): add list.to_finset theorems
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* to_finset_nil
- \+ *theorem* to_finset_cons
- \+ *theorem* to_finset_card_of_nodup

Modified data/list/basic.lean
- \+ *theorem* pw_filter_idempotent
- \+ *theorem* erase_dup_idempotent



## [2018-05-03 11:23:10+02:00](https://github.com/leanprover-community/mathlib/commit/02c2b56)
feat(analysis/topology/topological_space): t2 instances for constructions of limit type
#### Estimated changes
Modified analysis/topology/topological_space.lean

