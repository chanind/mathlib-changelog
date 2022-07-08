## [2018-02-26 19:33:33-05:00](https://github.com/leanprover-community/mathlib/commit/f98626c)
chore(.travis.yml): add notification hook
#### Estimated changes
modified .travis.yml



## [2018-02-25 08:41:54-05:00](https://github.com/leanprover-community/mathlib/commit/8f680d0)
fix(docs/tactics): update instance cache tactics doc ([#70](https://github.com/leanprover-community/mathlib/pull/70))
#### Estimated changes
modified docs/tactics.md



## [2018-02-25 05:09:48-05:00](https://github.com/leanprover-community/mathlib/commit/14e10bb)
fix(*): update to lean
#### Estimated changes
modified analysis/topology/topological_space.lean
- \+/\- *lemma* topological_space_eq
- \+/\- *lemma* topological_space_eq

modified data/list/basic.lean

modified data/nat/basic.lean

modified data/seq/computation.lean

modified data/set/countable.lean

modified data/set/finite.lean

modified order/order_iso.lean

modified set_theory/cardinal.lean

modified set_theory/cofinality.lean

modified set_theory/ordinal.lean

modified set_theory/ordinal_notation.lean

modified tactic/basic.lean

modified tactic/finish.lean

modified tactic/interactive.lean



## [2018-02-25 00:08:30-05:00](https://github.com/leanprover-community/mathlib/commit/c88a9e6)
doc(docs/tactics): Document the find command ([#67](https://github.com/leanprover-community/mathlib/pull/67))
#### Estimated changes
modified docs/tactics.md



## [2018-02-22 19:42:03-05:00](https://github.com/leanprover-community/mathlib/commit/1630725)
feat(data/finset): insert_union_distrib ([#66](https://github.com/leanprover-community/mathlib/pull/66))
* chore(data/finset): match style guide
* feat(data/finset): insert_union_distrib
#### Estimated changes
modified data/finset.lean
- \+/\- *theorem* insert_union
- \+/\- *theorem* union_insert
- \+ *theorem* insert_union_distrib
- \+/\- *theorem* insert_union
- \+/\- *theorem* union_insert



## [2018-02-22 15:14:26-05:00](https://github.com/leanprover-community/mathlib/commit/49b196c)
feat(data/multiset): erase_lt
#### Estimated changes
modified data/multiset.lean
- \+ *theorem* erase_lt



## [2018-02-22 14:08:57-05:00](https://github.com/leanprover-community/mathlib/commit/d68c8ae)
feat(set_theory/cardinal): some missing power theorems
#### Estimated changes
modified set_theory/cardinal.lean
- \+ *theorem* power_one
- \+ *theorem* power_add
- \+ *theorem* nat_cast_pow
- \+ *theorem* power_lt_omega
- \- *theorem* power_sum



## [2018-02-21 20:14:45-05:00](https://github.com/leanprover-community/mathlib/commit/22a52c3)
fix(tactic/find): update to lean
#### Estimated changes
modified tactic/basic.lean

modified tactic/find.lean



## [2018-02-21 04:29:29-05:00](https://github.com/leanprover-community/mathlib/commit/8ae1cef)
feat(tactic/find): add @Kha's #find command
#### Estimated changes
created tactic/find.lean



## [2018-02-20 22:14:23-05:00](https://github.com/leanprover-community/mathlib/commit/e2a562a)
refactor(analysis/topology): simplify is_topological_basis_of_open_of_nhds
#### Estimated changes
modified algebra/big_operators.lean
- \+/\- *lemma* prod_attach
- \+/\- *lemma* prod_bij
- \+/\- *lemma* prod_bij_ne_one
- \+/\- *lemma* prod_attach
- \+/\- *lemma* prod_bij
- \+/\- *lemma* prod_bij_ne_one

modified analysis/measure_theory/borel_space.lean

modified analysis/topology/topological_space.lean

modified data/encodable.lean

modified data/fintype.lean
- \+ *def* set_fintype



## [2018-02-20 22:12:18-05:00](https://github.com/leanprover-community/mathlib/commit/ebcbb6b)
doc(.): MD documentation ([#58](https://github.com/leanprover-community/mathlib/pull/58))
#### Estimated changes
modified README.md

created docs/naming.md

renamed style.md to docs/style.md

created docs/tactics.md

created docs/theories.md

created docs/theories/functions.md

created docs/theories/groups.md

created docs/theories/integers.md

created docs/theories/naturals.md

created docs/theories/orders.md

created docs/theories/quotients.md

created docs/theories/relations.md

created docs/theories/rings_fields.md

created docs/theories/sets.md

created docs/wip.md



## [2018-02-20 15:36:49+01:00](https://github.com/leanprover-community/mathlib/commit/140c672)
feat(algebra/order_functions): add abs_le_max_abs_abs; and relations between mul and max / min (suggested by @PatrickMassot)
#### Estimated changes
modified algebra/order_functions.lean
- \+ *lemma* abs_le_max_abs_abs
- \+ *lemma* monotone_mul_of_nonneg
- \+ *lemma* mul_max_of_nonneg
- \+ *lemma* mul_min_of_nonneg
- \+ *lemma* max_mul_mul_le_max_mul_max



## [2018-02-20 15:22:36+01:00](https://github.com/leanprover-community/mathlib/commit/3e683f4)
chore(algebra,order): cleanup min / max using the lattice theory
#### Estimated changes
modified algebra/default.lean

renamed algebra/functions.lean to algebra/order_functions.lean
- \+/\- *lemma* le_min_iff
- \+/\- *lemma* max_le_iff
- \+ *lemma* max_le_max
- \+ *lemma* min_le_min
- \+ *lemma* le_max_left_of_le
- \+ *lemma* le_max_right_of_le
- \+ *lemma* min_le_left_of_le
- \+ *lemma* min_le_right_of_le
- \+/\- *lemma* max_min_distrib_left
- \+/\- *lemma* max_min_distrib_right
- \+/\- *lemma* min_max_distrib_left
- \+/\- *lemma* min_max_distrib_right
- \+ *lemma* min_le_iff
- \+ *lemma* le_max_iff
- \+ *lemma* min_lt_iff
- \+ *lemma* max_distrib_of_monotone
- \+ *lemma* min_distrib_of_monotone
- \+/\- *lemma* le_min_iff
- \+/\- *lemma* max_le_iff
- \+/\- *lemma* max_min_distrib_left
- \+/\- *lemma* max_min_distrib_right
- \+/\- *lemma* min_max_distrib_left
- \+/\- *lemma* min_max_distrib_right
- \- *theorem* le_max_left_iff_true
- \- *theorem* le_max_right_iff_true

modified data/finset.lean

modified data/int/basic.lean

modified data/multiset.lean

modified data/set/intervals.lean

modified order/boolean_algebra.lean
- \- *lemma* eq_of_sup_eq_inf_eq
- \- *lemma* inf_eq_bot_iff_le_compl
- \- *theorem* le_sup_inf
- \- *theorem* sup_inf_left
- \- *theorem* sup_inf_right
- \- *theorem* inf_sup_left
- \- *theorem* inf_sup_right

modified order/bounded_lattice.lean
- \+ *lemma* inf_eq_bot_iff_le_compl

modified order/lattice.lean
- \+ *lemma* eq_of_sup_eq_inf_eq
- \+ *theorem* le_sup_inf
- \+ *theorem* sup_inf_left
- \+ *theorem* sup_inf_right
- \+ *theorem* inf_sup_left
- \+ *theorem* inf_sup_right



## [2018-02-20 10:43:29+01:00](https://github.com/leanprover-community/mathlib/commit/504a2dc)
Create choose.lean ([#48](https://github.com/leanprover-community/mathlib/pull/48))
deat(data/nat): add choose function to compute the binomial coefficients
#### Estimated changes
created data/nat/choose.lean
- \+ *lemma* choose_zero_right
- \+ *lemma* choose_zero_succ
- \+ *lemma* choose_succ_succ
- \+ *lemma* choose_eq_zero_of_lt
- \+ *lemma* choose_self
- \+ *lemma* choose_succ_self
- \+ *lemma* choose_one_right
- \+ *lemma* choose_pos
- \+ *lemma* succ_mul_choose_eq
- \+ *lemma* choose_mul_fact_mul_fact
- \+ *theorem* choose_eq_fact_div_fact
- \+ *theorem* fact_mul_fact_dvd_fact
- \+ *def* choose



## [2018-02-19 11:00:25+01:00](https://github.com/leanprover-community/mathlib/commit/3c25d94)
feat(algebra/archimedean): pow_unbounded_of_gt_one ([#50](https://github.com/leanprover-community/mathlib/pull/50))
#### Estimated changes
modified algebra/archimedean.lean
- \+ *lemma* pow_unbounded_of_gt_one



## [2018-02-19 10:55:46+01:00](https://github.com/leanprover-community/mathlib/commit/500dcc9)
feat(analysis/metric_space): add tendsto_iff_dist_tendsto_zero
#### Estimated changes
modified analysis/metric_space.lean
- \+ *lemma* nhds_vmap_dist
- \+ *lemma* tendsto_iff_dist_tendsto_zero
- \+ *theorem* real.dist_0_eq_abs
- \+ *theorem* abs_dist

modified analysis/topology/continuity.lean

modified analysis/topology/topological_structures.lean

modified analysis/topology/uniform_space.lean

modified order/filter.lean
- \+ *lemma* map_le_iff_le_vmap
- \+ *lemma* tendsto_vmap_iff
- \- *lemma* map_le_iff_vmap_le
- \- *lemma* le_vmap_iff_map_le
- \- *lemma* tendsto_vmap'



## [2018-02-19 10:38:12+01:00](https://github.com/leanprover-community/mathlib/commit/3ef7c7d)
fix(analysis/metric_space): remove unnecessary topological_space assumption from tendsto_dist
#### Estimated changes
modified analysis/metric_space.lean
- \+/\- *theorem* tendsto_dist
- \+/\- *theorem* tendsto_dist



## [2018-02-18 00:16:10-05:00](https://github.com/leanprover-community/mathlib/commit/9b306b2)
feat(option.to_list)
#### Estimated changes
modified data/option.lean
- \+ *def* to_list



## [2018-02-15 11:21:33+01:00](https://github.com/leanprover-community/mathlib/commit/ff4af0d)
feat(data/list): add append_eq_nil and update_nth_eq_nil
#### Estimated changes
modified data/list/basic.lean
- \+ *lemma* append_eq_nil
- \+ *lemma* update_nth_eq_nil



## [2018-02-15 10:43:12+01:00](https://github.com/leanprover-community/mathlib/commit/c0153c1)
feat(data/multiset): add smielattie_sup_bot instance; add disjoint_union_left/_right
#### Estimated changes
modified data/multiset.lean
- \+ *theorem* disjoint_union_left
- \+ *theorem* disjoint_union_right



## [2018-02-15 09:34:21+01:00](https://github.com/leanprover-community/mathlib/commit/8741b64)
feat(algebra/group_power): add pow_inv and pow_abs
#### Estimated changes
modified algebra/group_power.lean
- \+ *lemma* pow_abs
- \+ *lemma* pow_inv



## [2018-02-14 13:33:17+01:00](https://github.com/leanprover-community/mathlib/commit/eb32bfb)
feat(data/multiset): disjoint_ndinsert theorems
#### Estimated changes
modified data/multiset.lean
- \+ *theorem* disjoint_ndinsert_left
- \+ *theorem* disjoint_ndinsert_right



## [2018-02-12 07:11:07-05:00](https://github.com/leanprover-community/mathlib/commit/6ff5f3e)
feat(data/equiv): generalize list_equiv_of_equiv over universes ([#52](https://github.com/leanprover-community/mathlib/pull/52))
#### Estimated changes
modified data/equiv.lean
- \+/\- *def* list_equiv_of_equiv
- \+/\- *def* list_equiv_of_equiv



## [2018-02-08 22:50:08-05:00](https://github.com/leanprover-community/mathlib/commit/5dd3419)
feat(order/conditionally_complete_lattice): Conditionally complete lattices
#### Estimated changes
modified data/real/basic.lean
- \+/\- *theorem* mk_add
- \+/\- *theorem* mk_neg
- \+/\- *theorem* mk_mul
- \+/\- *theorem* exists_floor
- \+/\- *theorem* mk_add
- \+/\- *theorem* mk_neg
- \+/\- *theorem* mk_mul
- \+/\- *theorem* exists_floor

modified data/set/basic.lean
- \+/\- *theorem* subset_union_left
- \+/\- *theorem* subset_union_right
- \+/\- *theorem* union_subset_iff
- \+ *theorem* union_empty_iff
- \+/\- *theorem* inter_univ
- \+/\- *theorem* univ_inter
- \+/\- *theorem* subset_union_left
- \+/\- *theorem* subset_union_right
- \+/\- *theorem* union_subset_iff
- \+/\- *theorem* inter_univ
- \+/\- *theorem* univ_inter

created order/conditionally_complete_lattice.lean
- \+ *lemma* bdd_above.mk
- \+ *lemma* bdd_below.mk
- \+ *lemma* bdd_above_empty
- \+ *lemma* bdd_below_empty
- \+ *lemma* bdd_above_singleton
- \+ *lemma* bdd_below_singleton
- \+ *lemma* bdd_above_subset
- \+ *lemma* bdd_below_subset
- \+ *lemma* bdd_above_Int1
- \+ *lemma* bdd_above_Int2
- \+ *lemma* bdd_below_Int1
- \+ *lemma* bdd_below_Int2
- \+ *lemma* bdd_above_top
- \+ *lemma* bdd_above_bot
- \+ *lemma* bdd_above_union
- \+ *lemma* bdd_above_insert
- \+ *lemma* bdd_above_finite
- \+ *lemma* bdd_above_finite_union
- \+ *lemma* bdd_below_union
- \+ *lemma* bdd_below_insert
- \+ *lemma* bdd_below_finite
- \+ *lemma* bdd_below_finite_union
- \+ *lemma* lt_cSup_of_lt
- \+ *lemma* cInf_lt_of_lt
- \+ *lemma* exists_lt_of_lt_cSup
- \+ *lemma* exists_lt_of_cInf_lt
- \+ *theorem* le_cSup
- \+ *theorem* cSup_le
- \+ *theorem* cInf_le
- \+ *theorem* le_cInf
- \+ *theorem* le_cSup_of_le
- \+ *theorem* cInf_le_of_le
- \+ *theorem* cSup_le_cSup
- \+ *theorem* cInf_le_cInf
- \+ *theorem* cSup_le_iff
- \+ *theorem* le_cInf_iff
- \+ *theorem* cSup_intro
- \+ *theorem* cInf_intro
- \+ *theorem* cSup_of_in_of_le
- \+ *theorem* cInf_of_in_of_le
- \+ *theorem* cSup_singleton
- \+ *theorem* cInf_singleton
- \+ *theorem* cInf_le_cSup
- \+ *theorem* cSup_union
- \+ *theorem* cInf_union
- \+ *theorem* cSup_inter_le
- \+ *theorem* le_cInf_inter
- \+ *theorem* cSup_insert
- \+ *theorem* cInf_insert
- \+ *def* bdd_above
- \+ *def* bdd_below

modified order/lattice.lean
- \+/\- *theorem* le_sup_left
- \+/\- *theorem* le_sup_right
- \+/\- *theorem* inf_le_left
- \+/\- *theorem* inf_le_right
- \+/\- *theorem* le_sup_left
- \+/\- *theorem* le_sup_right
- \+/\- *theorem* inf_le_left
- \+/\- *theorem* inf_le_right



## [2018-02-08 22:39:23-05:00](https://github.com/leanprover-community/mathlib/commit/6ef721e)
feat(data/finset): not_mem theorems
Adapted from [#44](https://github.com/leanprover-community/mathlib/pull/44)
#### Estimated changes
modified data/finset.lean
- \+ *theorem* not_mem_singleton
- \+ *theorem* not_mem_union

modified logic/basic.lean
- \+ *theorem* ne_of_mem_of_not_mem



## [2018-02-06 17:03:30-05:00](https://github.com/leanprover-community/mathlib/commit/14a19bf)
fix(*): update to lean
Adding typeclasses to the context must now be done with `haveI`, `introsI`, etc.
#### Estimated changes
modified algebra/archimedean.lean

modified algebra/big_operators.lean

modified algebra/field.lean

modified algebra/linear_algebra/linear_map_module.lean

modified algebra/linear_algebra/subtype_module.lean

modified algebra/module.lean
- \+/\- *theorem* one_smul
- \+/\- *theorem* one_smul

modified analysis/metric_space.lean

modified analysis/real.lean

modified analysis/topology/continuity.lean

modified analysis/topology/topological_structures.lean

modified analysis/topology/uniform_space.lean
- \+ *def* uniform_space.mk'

modified data/analysis/filter.lean

modified data/analysis/topology.lean

modified data/finset.lean

modified data/fintype.lean

modified data/list/basic.lean

modified data/list/perm.lean

modified data/nat/basic.lean

modified data/num/lemmas.lean

modified data/real/cau_seq.lean

modified data/seq/computation.lean

modified data/seq/parallel.lean

modified data/set/countable.lean

modified data/set/finite.lean

modified data/sum.lean

modified logic/basic.lean

modified logic/embedding.lean

modified order/basic.lean

modified order/order_iso.lean

modified set_theory/cardinal.lean

modified set_theory/cofinality.lean

modified set_theory/ordinal.lean

modified set_theory/ordinal_notation.lean

modified set_theory/zfc.lean

modified tactic/basic.lean

modified tactic/interactive.lean

modified tactic/rcases.lean



## [2018-02-05 01:47:42-05:00](https://github.com/leanprover-community/mathlib/commit/5da3eb0)
Fix universe parameter in permutation group
#### Estimated changes
modified data/equiv.lean



## [2018-02-05 01:47:42-05:00](https://github.com/leanprover-community/mathlib/commit/cb4449f)
Permutation group instance for any type
#### Estimated changes
modified data/equiv.lean
- \+ *lemma* ext



## [2018-02-01 22:14:26-05:00](https://github.com/leanprover-community/mathlib/commit/03fefd4)
Create localization.lean
#### Estimated changes
created algebra/localization.lean
- \+ *def* loc
- \+ *def* add_aux
- \+ *def* add
- \+ *def* neg_aux
- \+ *def* neg
- \+ *def* mul_aux
- \+ *def* mul



## [2018-02-01 19:43:27-05:00](https://github.com/leanprover-community/mathlib/commit/e0539dd)
fix(data/hash_map,...): update to lean
#### Estimated changes
modified data/hash_map.lean

modified set_theory/cardinal.lean

modified set_theory/cofinality.lean

