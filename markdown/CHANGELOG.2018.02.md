## [2018-02-26 19:33:33-05:00](https://github.com/leanprover-community/mathlib/commit/f98626c)
chore(.travis.yml): add notification hook
#### Estimated changes
Modified .travis.yml




## [2018-02-25 08:41:54-05:00](https://github.com/leanprover-community/mathlib/commit/8f680d0)
fix(docs/tactics): update instance cache tactics doc ([#70](https://github.com/leanprover-community/mathlib/pull/70))
#### Estimated changes
Modified docs/tactics.md




## [2018-02-25 05:09:48-05:00](https://github.com/leanprover-community/mathlib/commit/14e10bb)
fix(*): update to lean
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+/\- *lemma* topological_space_eq

Modified data/list/basic.lean


Modified data/nat/basic.lean


Modified data/seq/computation.lean


Modified data/set/countable.lean


Modified data/set/finite.lean


Modified order/order_iso.lean


Modified set_theory/cardinal.lean


Modified set_theory/cofinality.lean


Modified set_theory/ordinal.lean


Modified set_theory/ordinal_notation.lean


Modified tactic/basic.lean


Modified tactic/finish.lean


Modified tactic/interactive.lean




## [2018-02-25 00:08:30-05:00](https://github.com/leanprover-community/mathlib/commit/c88a9e6)
doc(docs/tactics): Document the find command ([#67](https://github.com/leanprover-community/mathlib/pull/67))
#### Estimated changes
Modified docs/tactics.md




## [2018-02-22 19:42:03-05:00](https://github.com/leanprover-community/mathlib/commit/1630725)
feat(data/finset): insert_union_distrib ([#66](https://github.com/leanprover-community/mathlib/pull/66))
* chore(data/finset): match style guide
* feat(data/finset): insert_union_distrib
#### Estimated changes
Modified data/finset.lean
- \+/\- *theorem* finset.insert_union
- \+ *theorem* finset.insert_union_distrib
- \+/\- *theorem* finset.union_insert



## [2018-02-22 15:14:26-05:00](https://github.com/leanprover-community/mathlib/commit/49b196c)
feat(data/multiset): erase_lt
#### Estimated changes
Modified data/multiset.lean
- \+ *theorem* multiset.erase_lt



## [2018-02-22 14:08:57-05:00](https://github.com/leanprover-community/mathlib/commit/d68c8ae)
feat(set_theory/cardinal): some missing power theorems
#### Estimated changes
Modified set_theory/cardinal.lean
- \+ *theorem* cardinal.nat_cast_pow
- \+ *theorem* cardinal.power_add
- \+ *theorem* cardinal.power_lt_omega
- \+ *theorem* cardinal.power_one
- \- *theorem* cardinal.power_sum



## [2018-02-21 20:14:45-05:00](https://github.com/leanprover-community/mathlib/commit/22a52c3)
fix(tactic/find): update to lean
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/find.lean




## [2018-02-21 04:29:29-05:00](https://github.com/leanprover-community/mathlib/commit/8ae1cef)
feat(tactic/find): add @Kha's #find command
#### Estimated changes
Added tactic/find.lean




## [2018-02-20 22:14:23-05:00](https://github.com/leanprover-community/mathlib/commit/e2a562a)
refactor(analysis/topology): simplify is_topological_basis_of_open_of_nhds
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* finset.prod_attach
- \+/\- *lemma* finset.prod_bij
- \+/\- *lemma* finset.prod_bij_ne_one

Modified analysis/measure_theory/borel_space.lean


Modified analysis/topology/topological_space.lean


Modified data/encodable.lean


Modified data/fintype.lean
- \+ *def* set_fintype



## [2018-02-20 22:12:18-05:00](https://github.com/leanprover-community/mathlib/commit/ebcbb6b)
doc(.): MD documentation ([#58](https://github.com/leanprover-community/mathlib/pull/58))
#### Estimated changes
Modified README.md


Added docs/naming.md


Renamed style.md to docs/style.md


Added docs/tactics.md


Added docs/theories.md


Added docs/theories/functions.md


Added docs/theories/groups.md


Added docs/theories/integers.md


Added docs/theories/naturals.md


Added docs/theories/orders.md


Added docs/theories/quotients.md


Added docs/theories/relations.md


Added docs/theories/rings_fields.md


Added docs/theories/sets.md


Added docs/wip.md




## [2018-02-20 15:36:49+01:00](https://github.com/leanprover-community/mathlib/commit/140c672)
feat(algebra/order_functions): add abs_le_max_abs_abs; and relations between mul and max / min (suggested by @PatrickMassot)
#### Estimated changes
Modified algebra/order_functions.lean
- \+ *lemma* abs_le_max_abs_abs
- \+ *lemma* max_mul_mul_le_max_mul_max
- \+ *lemma* monotone_mul_of_nonneg
- \+ *lemma* mul_max_of_nonneg
- \+ *lemma* mul_min_of_nonneg



## [2018-02-20 15:22:36+01:00](https://github.com/leanprover-community/mathlib/commit/3e683f4)
chore(algebra,order): cleanup min / max using the lattice theory
#### Estimated changes
Modified algebra/default.lean


Renamed algebra/functions.lean to algebra/order_functions.lean
- \+ *lemma* le_max_iff
- \- *theorem* le_max_left_iff_true
- \+ *lemma* le_max_left_of_le
- \- *theorem* le_max_right_iff_true
- \+ *lemma* le_max_right_of_le
- \+/\- *lemma* le_min_iff
- \+ *lemma* max_distrib_of_monotone
- \+/\- *lemma* max_le_iff
- \+ *lemma* max_le_max
- \+/\- *lemma* max_min_distrib_left
- \+/\- *lemma* max_min_distrib_right
- \+ *lemma* min_distrib_of_monotone
- \+ *lemma* min_le_iff
- \+ *lemma* min_le_left_of_le
- \+ *lemma* min_le_min
- \+ *lemma* min_le_right_of_le
- \+ *lemma* min_lt_iff
- \+/\- *lemma* min_max_distrib_left
- \+/\- *lemma* min_max_distrib_right

Modified data/finset.lean


Modified data/int/basic.lean


Modified data/multiset.lean


Modified data/set/intervals.lean


Modified order/boolean_algebra.lean
- \- *lemma* lattice.eq_of_sup_eq_inf_eq
- \- *lemma* lattice.inf_eq_bot_iff_le_compl
- \- *theorem* lattice.inf_sup_left
- \- *theorem* lattice.inf_sup_right
- \- *theorem* lattice.le_sup_inf
- \- *theorem* lattice.sup_inf_left
- \- *theorem* lattice.sup_inf_right

Modified order/bounded_lattice.lean
- \+ *lemma* lattice.inf_eq_bot_iff_le_compl

Modified order/lattice.lean
- \+ *lemma* lattice.eq_of_sup_eq_inf_eq
- \+ *theorem* lattice.inf_sup_left
- \+ *theorem* lattice.inf_sup_right
- \+ *theorem* lattice.le_sup_inf
- \+ *theorem* lattice.sup_inf_left
- \+ *theorem* lattice.sup_inf_right



## [2018-02-20 10:43:29+01:00](https://github.com/leanprover-community/mathlib/commit/504a2dc)
Create choose.lean ([#48](https://github.com/leanprover-community/mathlib/pull/48))
deat(data/nat): add choose function to compute the binomial coefficients
#### Estimated changes
Added data/nat/choose.lean
- \+ *def* choose
- \+ *theorem* choose_eq_fact_div_fact
- \+ *lemma* choose_eq_zero_of_lt
- \+ *lemma* choose_mul_fact_mul_fact
- \+ *lemma* choose_one_right
- \+ *lemma* choose_pos
- \+ *lemma* choose_self
- \+ *lemma* choose_succ_self
- \+ *lemma* choose_succ_succ
- \+ *lemma* choose_zero_right
- \+ *lemma* choose_zero_succ
- \+ *theorem* fact_mul_fact_dvd_fact
- \+ *lemma* succ_mul_choose_eq



## [2018-02-19 11:00:25+01:00](https://github.com/leanprover-community/mathlib/commit/3c25d94)
feat(algebra/archimedean): pow_unbounded_of_gt_one ([#50](https://github.com/leanprover-community/mathlib/pull/50))
#### Estimated changes
Modified algebra/archimedean.lean
- \+ *lemma* pow_unbounded_of_gt_one



## [2018-02-19 10:55:46+01:00](https://github.com/leanprover-community/mathlib/commit/500dcc9)
feat(analysis/metric_space): add tendsto_iff_dist_tendsto_zero
#### Estimated changes
Modified analysis/metric_space.lean
- \+ *theorem* abs_dist
- \+ *lemma* nhds_vmap_dist
- \+ *theorem* real.dist_0_eq_abs
- \+ *lemma* tendsto_iff_dist_tendsto_zero

Modified analysis/topology/continuity.lean


Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean


Modified order/filter.lean
- \- *lemma* filter.le_vmap_iff_map_le
- \+ *lemma* filter.map_le_iff_le_vmap
- \- *lemma* filter.map_le_iff_vmap_le
- \- *lemma* filter.tendsto_vmap'
- \+ *lemma* filter.tendsto_vmap_iff



## [2018-02-19 10:38:12+01:00](https://github.com/leanprover-community/mathlib/commit/3ef7c7d)
fix(analysis/metric_space): remove unnecessary topological_space assumption from tendsto_dist
#### Estimated changes
Modified analysis/metric_space.lean
- \+/\- *theorem* tendsto_dist



## [2018-02-18 00:16:10-05:00](https://github.com/leanprover-community/mathlib/commit/9b306b2)
feat(option.to_list)
#### Estimated changes
Modified data/option.lean
- \+ *def* option.to_list



## [2018-02-15 11:21:33+01:00](https://github.com/leanprover-community/mathlib/commit/ff4af0d)
feat(data/list): add append_eq_nil and update_nth_eq_nil
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* list.append_eq_nil
- \+ *lemma* list.update_nth_eq_nil



## [2018-02-15 10:43:12+01:00](https://github.com/leanprover-community/mathlib/commit/c0153c1)
feat(data/multiset): add smielattie_sup_bot instance; add disjoint_union_left/_right
#### Estimated changes
Modified data/multiset.lean
- \+ *theorem* multiset.disjoint_union_left
- \+ *theorem* multiset.disjoint_union_right



## [2018-02-15 09:34:21+01:00](https://github.com/leanprover-community/mathlib/commit/8741b64)
feat(algebra/group_power): add pow_inv and pow_abs
#### Estimated changes
Modified algebra/group_power.lean
- \+ *lemma* pow_abs
- \+ *lemma* pow_inv



## [2018-02-14 13:33:17+01:00](https://github.com/leanprover-community/mathlib/commit/eb32bfb)
feat(data/multiset): disjoint_ndinsert theorems
#### Estimated changes
Modified data/multiset.lean
- \+ *theorem* multiset.disjoint_ndinsert_left
- \+ *theorem* multiset.disjoint_ndinsert_right



## [2018-02-12 07:11:07-05:00](https://github.com/leanprover-community/mathlib/commit/6ff5f3e)
feat(data/equiv): generalize list_equiv_of_equiv over universes ([#52](https://github.com/leanprover-community/mathlib/pull/52))
#### Estimated changes
Modified data/equiv.lean
- \+/\- *def* equiv.list_equiv_of_equiv



## [2018-02-08 22:50:08-05:00](https://github.com/leanprover-community/mathlib/commit/5dd3419)
feat(order/conditionally_complete_lattice): Conditionally complete lattices
#### Estimated changes
Modified data/real/basic.lean
- \+/\- *theorem* real.exists_floor
- \+/\- *theorem* real.mk_add
- \+/\- *theorem* real.mk_mul
- \+/\- *theorem* real.mk_neg

Modified data/set/basic.lean
- \+/\- *theorem* set.inter_univ
- \+/\- *theorem* set.subset_union_left
- \+/\- *theorem* set.subset_union_right
- \+ *theorem* set.union_empty_iff
- \+/\- *theorem* set.union_subset_iff
- \+/\- *theorem* set.univ_inter

Added order/conditionally_complete_lattice.lean
- \+ *lemma* bdd_above.mk
- \+ *def* bdd_above
- \+ *lemma* bdd_above_Int1
- \+ *lemma* bdd_above_Int2
- \+ *lemma* bdd_above_bot
- \+ *lemma* bdd_above_empty
- \+ *lemma* bdd_above_finite
- \+ *lemma* bdd_above_finite_union
- \+ *lemma* bdd_above_insert
- \+ *lemma* bdd_above_singleton
- \+ *lemma* bdd_above_subset
- \+ *lemma* bdd_above_top
- \+ *lemma* bdd_above_union
- \+ *lemma* bdd_below.mk
- \+ *def* bdd_below
- \+ *lemma* bdd_below_Int1
- \+ *lemma* bdd_below_Int2
- \+ *lemma* bdd_below_empty
- \+ *lemma* bdd_below_finite
- \+ *lemma* bdd_below_finite_union
- \+ *lemma* bdd_below_insert
- \+ *lemma* bdd_below_singleton
- \+ *lemma* bdd_below_subset
- \+ *lemma* bdd_below_union
- \+ *theorem* lattice.cInf_insert
- \+ *theorem* lattice.cInf_intro
- \+ *theorem* lattice.cInf_le
- \+ *theorem* lattice.cInf_le_cInf
- \+ *theorem* lattice.cInf_le_cSup
- \+ *theorem* lattice.cInf_le_of_le
- \+ *lemma* lattice.cInf_lt_of_lt
- \+ *theorem* lattice.cInf_of_in_of_le
- \+ *theorem* lattice.cInf_singleton
- \+ *theorem* lattice.cInf_union
- \+ *theorem* lattice.cSup_insert
- \+ *theorem* lattice.cSup_inter_le
- \+ *theorem* lattice.cSup_intro
- \+ *theorem* lattice.cSup_le
- \+ *theorem* lattice.cSup_le_cSup
- \+ *theorem* lattice.cSup_le_iff
- \+ *theorem* lattice.cSup_of_in_of_le
- \+ *theorem* lattice.cSup_singleton
- \+ *theorem* lattice.cSup_union
- \+ *lemma* lattice.exists_lt_of_cInf_lt
- \+ *lemma* lattice.exists_lt_of_lt_cSup
- \+ *theorem* lattice.le_cInf
- \+ *theorem* lattice.le_cInf_iff
- \+ *theorem* lattice.le_cInf_inter
- \+ *theorem* lattice.le_cSup
- \+ *theorem* lattice.le_cSup_of_le
- \+ *lemma* lattice.lt_cSup_of_lt

Modified order/lattice.lean
- \+/\- *theorem* lattice.inf_le_left
- \+/\- *theorem* lattice.inf_le_right
- \+/\- *theorem* lattice.le_sup_left
- \+/\- *theorem* lattice.le_sup_right



## [2018-02-08 22:39:23-05:00](https://github.com/leanprover-community/mathlib/commit/6ef721e)
feat(data/finset): not_mem theorems
Adapted from [#44](https://github.com/leanprover-community/mathlib/pull/44)
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* finset.not_mem_singleton
- \+ *theorem* finset.not_mem_union

Modified logic/basic.lean
- \+ *theorem* ne_of_mem_of_not_mem



## [2018-02-06 17:03:30-05:00](https://github.com/leanprover-community/mathlib/commit/14a19bf)
fix(*): update to lean
Adding typeclasses to the context must now be done with `haveI`, `introsI`, etc.
#### Estimated changes
Modified algebra/archimedean.lean


Modified algebra/big_operators.lean


Modified algebra/field.lean


Modified algebra/linear_algebra/linear_map_module.lean


Modified algebra/linear_algebra/subtype_module.lean


Modified algebra/module.lean
- \+/\- *theorem* one_smul

Modified analysis/metric_space.lean


Modified analysis/real.lean


Modified analysis/topology/continuity.lean


Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean
- \+ *def* uniform_space.mk'

Modified data/analysis/filter.lean


Modified data/analysis/topology.lean


Modified data/finset.lean


Modified data/fintype.lean


Modified data/list/basic.lean


Modified data/list/perm.lean


Modified data/nat/basic.lean


Modified data/num/lemmas.lean


Modified data/real/cau_seq.lean


Modified data/seq/computation.lean


Modified data/seq/parallel.lean


Modified data/set/countable.lean


Modified data/set/finite.lean


Modified data/sum.lean


Modified logic/basic.lean


Modified logic/embedding.lean


Modified order/basic.lean


Modified order/order_iso.lean


Modified set_theory/cardinal.lean


Modified set_theory/cofinality.lean


Modified set_theory/ordinal.lean


Modified set_theory/ordinal_notation.lean


Modified set_theory/zfc.lean


Modified tactic/basic.lean


Modified tactic/interactive.lean


Modified tactic/rcases.lean




## [2018-02-05 01:47:42-05:00](https://github.com/leanprover-community/mathlib/commit/5da3eb0)
Fix universe parameter in permutation group
#### Estimated changes
Modified data/equiv.lean




## [2018-02-05 01:47:42-05:00](https://github.com/leanprover-community/mathlib/commit/cb4449f)
Permutation group instance for any type
#### Estimated changes
Modified data/equiv.lean
- \+ *lemma* equiv.ext



## [2018-02-01 22:14:26-05:00](https://github.com/leanprover-community/mathlib/commit/03fefd4)
Create localization.lean
#### Estimated changes
Added algebra/localization.lean
- \+ *def* loc.add
- \+ *def* loc.add_aux
- \+ *def* loc.loc
- \+ *def* loc.mul
- \+ *def* loc.mul_aux
- \+ *def* loc.neg
- \+ *def* loc.neg_aux



## [2018-02-01 19:43:27-05:00](https://github.com/leanprover-community/mathlib/commit/e0539dd)
fix(data/hash_map,...): update to lean
#### Estimated changes
Modified data/hash_map.lean


Modified set_theory/cardinal.lean


Modified set_theory/cofinality.lean


