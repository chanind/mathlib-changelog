## [2018-03-30 14:05:43+02:00](https://github.com/leanprover-community/mathlib/commit/162edc3)
feat(order): add complete lattice of fixed points (Knaster-Tarski) by Kenny Lau https://github.com/leanprover/mathlib/pull/88
#### Estimated changes
Modified order/basic.lean
- \+ *theorem* ge_of_eq

Modified order/fixed_points.lean
- \- *theorem* ge_of_eq
- \+ *theorem* lattice.fixed_points.Sup_le_f_of_fixed_points
- \+ *theorem* lattice.fixed_points.f_le_Inf_of_fixed_points
- \+ *theorem* lattice.fixed_points.f_le_inf_of_fixed_points
- \+ *def* lattice.fixed_points.next
- \+ *lemma* lattice.fixed_points.next_eq
- \+ *def* lattice.fixed_points.next_fixed
- \+ *theorem* lattice.fixed_points.next_le
- \+ *def* lattice.fixed_points.prev
- \+ *lemma* lattice.fixed_points.prev_eq
- \+ *def* lattice.fixed_points.prev_fixed
- \+ *theorem* lattice.fixed_points.prev_le
- \+ *theorem* lattice.fixed_points.sup_le_f_of_fixed_points
- \+ *def* lattice.fixed_points



## [2018-03-29 17:23:46+02:00](https://github.com/leanprover-community/mathlib/commit/c54d431)
fix(.): unit is now an abbreviation: unit := punit.{1}
#### Estimated changes
Modified data/encodable.lean


Modified data/equiv.lean
- \+/\- *def* equiv.arrow_empty_unit
- \+/\- *def* equiv.arrow_unit_equiv_unit
- \+/\- *def* equiv.bool_equiv_unit_sum_unit
- \+/\- *def* equiv.empty_arrow_equiv_unit
- \+/\- *def* equiv.false_arrow_equiv_unit
- \+/\- *def* equiv.nat_equiv_nat_sum_unit
- \+/\- *def* equiv.nat_sum_unit_equiv_nat
- \+/\- *def* equiv.option_equiv_sum_unit
- \+/\- *def* equiv.prod_unit
- \+/\- *theorem* equiv.prod_unit_apply
- \+ *def* equiv.punit_equiv_punit
- \+/\- *def* equiv.unit_arrow_equiv
- \+/\- *def* equiv.unit_prod
- \+/\- *theorem* equiv.unit_prod_apply

Modified set_theory/ordinal.lean
- \+/\- *theorem* ordinal.is_normal.limit_le



## [2018-03-25 19:59:40-04:00](https://github.com/leanprover-community/mathlib/commit/d84af03)
fix(data/option): revert to lean commit 28f414
#### Estimated changes
Modified data/option.lean




## [2018-03-22 14:08:02+01:00](https://github.com/leanprover-community/mathlib/commit/e5c1c5e)
fix(number_theory/dipoh): has_map.map -> functor.map
#### Estimated changes
Modified number_theory/dioph.lean




## [2018-03-22 11:27:24+01:00](https://github.com/leanprover-community/mathlib/commit/a357b79)
feat(analysis): measurable_if
#### Estimated changes
Modified analysis/measure_theory/measurable_space.lean
- \+ *lemma* measurable_if



## [2018-03-21 19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/868bbc6)
fix(*): update to lean
#### Estimated changes
Modified category/basic.lean
- \- *lemma* bind_assoc
- \- *lemma* pure_seq_eq_map

Modified data/list/basic.lean


Modified data/nat/basic.lean


Modified data/option.lean
- \+ *lemma* option.map_id'

Modified data/pfun.lean


Modified data/seq/computation.lean


Modified data/seq/parallel.lean


Modified data/seq/seq.lean


Modified data/seq/wseq.lean


Modified data/set/lattice.lean


Modified order/filter.lean


Modified tactic/converter/binders.lean


Modified tactic/converter/old_conv.lean




## [2018-03-21 19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/638265c)
fix(set_theory/zfc): improve pSet.equiv.eq
I claimed in the comment that this converse was not provable, but it is (because equiv is embedded in the definition of mem). Thanks to Vinoth Kumar Raman for bringing this to my attention.
#### Estimated changes
Modified set_theory/zfc.lean
- \+/\- *theorem* pSet.equiv.eq
- \+ *theorem* pSet.equiv_iff_mem



## [2018-03-21 19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/f3660df)
chore(logic/basic): protect classical logic theorems
You can't use these theorems with `open classical` anyway, because of disambiguation with the `_root_` theorems of the same name.
#### Estimated changes
Modified logic/basic.lean
- \- *theorem* classical.forall_or_distrib_left
- \- *theorem* classical.not_forall
- \- *theorem* classical.or_iff_not_imp_left
- \- *theorem* classical.or_iff_not_imp_right



## [2018-03-21 18:56:23-04:00](https://github.com/leanprover-community/mathlib/commit/486e4ed)
fix(test suite): remove `sorry` warning in test suite
#### Estimated changes
Modified tests/wlog.lean




## [2018-03-15 00:57:20-04:00](https://github.com/leanprover-community/mathlib/commit/f7977ff)
feat(data/finset): add finset.powerset
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* finset.card_powerset
- \+ *theorem* finset.empty_mem_powerset
- \+ *theorem* finset.mem_powerset
- \+ *theorem* finset.mem_powerset_self
- \+ *def* finset.powerset
- \+ *theorem* finset.powerset_mono

Modified data/list/basic.lean
- \+ *theorem* list.length_sublists'
- \+/\- *theorem* list.length_sublists
- \+ *theorem* list.map_sublists'_aux
- \+ *theorem* list.mem_sublists'
- \+/\- *theorem* list.nodup_map
- \+ *theorem* list.nodup_map_iff
- \+ *theorem* list.nodup_sublists'
- \+ *theorem* list.pairwise_sublists'
- \+/\- *theorem* list.pairwise_sublists
- \+ *theorem* list.reverse_injective
- \+ *def* list.sublists'
- \+ *def* list.sublists'_aux
- \+ *theorem* list.sublists'_aux_append
- \+ *theorem* list.sublists'_aux_eq_sublists'
- \+ *theorem* list.sublists'_cons
- \+ *theorem* list.sublists'_eq_sublists
- \+ *theorem* list.sublists'_nil
- \+ *theorem* list.sublists'_reverse
- \+ *theorem* list.sublists'_singleton
- \+ *theorem* list.sublists_eq_sublists'
- \+ *theorem* list.sublists_reverse

Modified data/list/perm.lean
- \+ *theorem* list.perm_ext_sublist_nodup
- \+ *theorem* list.sublists_cons_perm_append
- \+ *theorem* list.sublists_perm_sublists'

Modified data/multiset.lean
- \+ *theorem* multiset.card_powerset
- \+ *theorem* multiset.map_single_le_powerset
- \+ *theorem* multiset.mem_powerset
- \+ *theorem* multiset.nodup_powerset
- \+/\- *def* multiset.pmap
- \+ *def* multiset.powerset
- \+ *def* multiset.powerset_aux'
- \+ *theorem* multiset.powerset_aux'_cons
- \+ *theorem* multiset.powerset_aux'_nil
- \+ *theorem* multiset.powerset_aux'_perm
- \+ *def* multiset.powerset_aux
- \+ *theorem* multiset.powerset_aux_eq_map_coe
- \+ *theorem* multiset.powerset_aux_perm
- \+ *theorem* multiset.powerset_aux_perm_powerset_aux'
- \+ *theorem* multiset.powerset_coe'
- \+ *theorem* multiset.powerset_coe



## [2018-03-13 05:57:49-04:00](https://github.com/leanprover-community/mathlib/commit/4ceb545)
feat(data/list/basic): stuff about `list.sublists`
#### Estimated changes
Modified analysis/topology/topological_space.lean


Modified data/list/basic.lean
- \+ *theorem* list.bind_eq_bind
- \+ *theorem* list.bind_ret_eq_map
- \+ *theorem* list.cons_subset
- \+/\- *theorem* list.cons_subset_of_subset_of_mem
- \+ *theorem* list.length_eq_zero
- \+ *theorem* list.length_sublists
- \+ *theorem* list.lex.imp
- \+ *inductive* list.lex
- \+ *theorem* list.lex_append_left
- \+ *theorem* list.lex_append_right
- \+ *theorem* list.lex_ne_iff
- \+ *theorem* list.map_eq_map
- \+ *theorem* list.map_ret_sublist_sublists
- \+/\- *theorem* list.mem_sublists
- \+ *theorem* list.ne_of_lex_ne
- \+ *theorem* list.nodup_sublists
- \+ *theorem* list.pairwise_sublists
- \+ *theorem* list.reverse_eq_nil
- \+ *theorem* list.reverse_inj
- \+/\- *theorem* list.reverse_nil
- \+ *theorem* list.reverse_rec_on
- \+/\- *theorem* list.reverse_singleton
- \+ *theorem* list.sublists_append
- \+ *theorem* list.sublists_aux_cons_append
- \+ *theorem* list.sublists_aux_cons_eq_sublists_aux₁
- \- *theorem* list.sublists_aux_eq_foldl
- \+ *theorem* list.sublists_aux_eq_foldr.aux
- \+ *theorem* list.sublists_aux_eq_foldr
- \+ *theorem* list.sublists_aux_ne_nil
- \+ *def* list.sublists_aux₁
- \+ *theorem* list.sublists_aux₁_append
- \+ *theorem* list.sublists_aux₁_bind
- \+ *theorem* list.sublists_aux₁_concat
- \+ *theorem* list.sublists_aux₁_eq_sublists_aux
- \+ *theorem* list.sublists_concat
- \+ *theorem* list.sublists_nil
- \+ *theorem* list.sublists_singleton
- \+ *theorem* list.subset_def



## [2018-03-12 20:45:43+01:00](https://github.com/leanprover-community/mathlib/commit/5f8c26c)
feat(analysis/measure_theory): measures are embedded in outer measures; add map, dirac, and sum measures
#### Estimated changes
Modified analysis/ennreal.lean
- \+ *lemma* ennreal.tsum_supr_eq

Modified analysis/measure_theory/measure_space.lean
- \- *def* measure_theory.count
- \+ *lemma* measure_theory.le_to_outer_measure_caratheodory
- \+ *def* measure_theory.measure_space.count
- \+ *def* measure_theory.measure_space.dirac
- \+ *def* measure_theory.measure_space.map
- \+ *lemma* measure_theory.measure_space.map_comp
- \+ *lemma* measure_theory.measure_space.map_id
- \+ *lemma* measure_theory.measure_space.map_measure
- \+ *def* measure_theory.measure_space.sum
- \+ *lemma* measure_theory.to_outer_measure_to_measure



## [2018-03-12 17:09:31+01:00](https://github.com/leanprover-community/mathlib/commit/36a061b)
feat(analysis/measure_theory): outer_measures form a complete lattice
#### Estimated changes
Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean
- \+ *lemma* measure_theory.outer_measure.outer_measure_eq
- \+/\- *lemma* measure_theory.outer_measure.subadditive



## [2018-03-11 14:26:05+01:00](https://github.com/leanprover-community/mathlib/commit/64a8d56)
chore(order/filter): simplify definition of filter.prod; cleanup
#### Estimated changes
Modified analysis/ennreal.lean


Modified analysis/real.lean


Modified analysis/topology/continuity.lean


Modified analysis/topology/topological_space.lean
- \+ *lemma* nhds_sup

Modified analysis/topology/uniform_space.lean
- \+/\- *lemma* uniformity_le_symm

Modified data/analysis/filter.lean


Modified order/filter.lean
- \+ *lemma* filter.le_lift
- \+ *lemma* filter.lift_const
- \+ *lemma* filter.lift_inf
- \+ *lemma* filter.lift_principal2
- \+/\- *lemma* filter.map_lift_eq
- \+ *lemma* filter.map_swap_eq_vmap_swap
- \- *lemma* filter.map_swap_vmap_swap_eq
- \+ *lemma* filter.mem_prod_iff
- \- *lemma* filter.mem_prod_sets
- \+ *lemma* filter.prod_bot1
- \+ *lemma* filter.prod_bot2
- \+ *lemma* filter.prod_comm'
- \+/\- *lemma* filter.prod_def
- \+/\- *lemma* filter.prod_mem_prod
- \+/\- *lemma* filter.prod_neq_bot
- \+/\- *lemma* filter.prod_principal_principal
- \+/\- *lemma* filter.vmap_lift_eq



## [2018-03-10 20:37:53+01:00](https://github.com/leanprover-community/mathlib/commit/b154092)
feat(data/finsupp): make finsupp computable; add induction rule; removed comap_domain
#### Estimated changes
Modified data/finsupp.lean
- \+ *lemma* finset.mem_subtype
- \+/\- *lemma* finsupp.add_apply
- \- *def* finsupp.comap_domain
- \- *lemma* finsupp.comap_domain_add
- \- *lemma* finsupp.comap_domain_apply
- \- *lemma* finsupp.comap_domain_finsupp_sum
- \- *lemma* finsupp.comap_domain_neg
- \- *lemma* finsupp.comap_domain_sub
- \- *lemma* finsupp.comap_domain_sum
- \- *lemma* finsupp.comap_domain_zero
- \+ *def* finsupp.erase
- \+ *lemma* finsupp.erase_ne
- \+ *lemma* finsupp.erase_same
- \+/\- *def* finsupp.filter
- \+/\- *lemma* finsupp.filter_pos_add_filter_neg
- \+/\- *lemma* finsupp.finite_supp
- \+/\- *lemma* finsupp.map_domain_finset_sum
- \+/\- *def* finsupp.map_range
- \+/\- *lemma* finsupp.map_range_apply
- \+/\- *lemma* finsupp.mem_support_iff
- \+ *def* finsupp.on_finset
- \+ *lemma* finsupp.on_finset_apply
- \- *lemma* finsupp.prod_comap_domain_index
- \+/\- *lemma* finsupp.prod_finset_sum_index
- \+/\- *lemma* finsupp.prod_map_range_index
- \+/\- *lemma* finsupp.prod_neg_index
- \+/\- *lemma* finsupp.prod_single
- \+/\- *lemma* finsupp.prod_single_index
- \+/\- *lemma* finsupp.prod_sum_index
- \+/\- *lemma* finsupp.single_add
- \+ *lemma* finsupp.single_add_erase
- \+/\- *lemma* finsupp.single_apply
- \+/\- *lemma* finsupp.single_eq_of_ne
- \+/\- *lemma* finsupp.single_eq_same
- \+/\- *lemma* finsupp.single_zero
- \+/\- *def* finsupp.subtype_domain
- \+/\- *lemma* finsupp.subtype_domain_zero
- \+/\- *lemma* finsupp.sum_apply
- \- *def* finsupp.support
- \+/\- *lemma* finsupp.support_add
- \+ *lemma* finsupp.support_eq_empty
- \+ *lemma* finsupp.support_erase
- \+/\- *lemma* finsupp.support_map_range
- \+ *lemma* finsupp.support_on_finset_subset
- \+/\- *lemma* finsupp.support_single_ne_zero
- \+/\- *lemma* finsupp.support_single_subset
- \+/\- *lemma* finsupp.support_subset_iff
- \+ *lemma* finsupp.support_subtype_domain
- \+/\- *lemma* finsupp.support_sum
- \+/\- *lemma* finsupp.support_zero
- \+/\- *lemma* finsupp.support_zip_with
- \+/\- *def* finsupp.zip_with
- \+/\- *lemma* finsupp.zip_with_apply
- \+ *structure* finsupp
- \- *def* finsupp

Modified linear_algebra/basic.lean




## [2018-03-10 13:38:59+01:00](https://github.com/leanprover-community/mathlib/commit/b97b7c3)
feat(group_theory): add a little bit of group theory; prove of Lagrange's theorem
#### Estimated changes
Modified data/equiv.lean
- \+ *def* equiv.subtype_subtype_equiv_subtype

Modified data/finset.lean
- \+ *theorem* finset.card_attach
- \+ *lemma* finset.card_eq_of_bijective
- \+ *lemma* finset.card_le_card_of_inj_on
- \+ *lemma* finset.card_le_of_inj_on

Modified data/fintype.lean
- \+ *def* fintype.fintype_prod_left
- \+ *def* fintype.fintype_prod_right

Modified data/int/basic.lean


Modified data/multiset.lean
- \+ *theorem* multiset.card_attach

Modified data/set/finite.lean
- \+ *lemma* set.infinite_univ_nat
- \+ *lemma* set.not_injective_int_fintype
- \+ *lemma* set.not_injective_nat_fintype

Added group_theory/subgroup.lean
- \+ *def* cosets
- \+ *lemma* exists_gpow_eq_one
- \+ *lemma* exists_pow_eq_one
- \+ *lemma* finset.mem_range_iff_mem_finset_range_of_mod_eq
- \+ *lemma* gpow_eq_mod_order_of
- \+ *lemma* is_subgroup.Union_cosets_eq_univ
- \+ *lemma* is_subgroup.cosets_disjoint
- \+ *lemma* is_subgroup.cosets_equiv_subgroup
- \+ *lemma* is_subgroup.group_equiv_cosets_times_subgroup
- \+ *lemma* is_subgroup.injective_mul
- \+ *lemma* is_subgroup.inv_mem
- \+ *lemma* is_subgroup.inv_mem_iff
- \+ *lemma* is_subgroup.mul_image
- \+ *lemma* is_subgroup.mul_mem
- \+ *lemma* is_subgroup.pairwise_cosets_disjoint
- \+ *lemma* is_subgroup.subgroup_mem_cosets
- \+ *structure* is_subgroup
- \+ *lemma* is_subgroup_range_gpow
- \+ *lemma* mem_range_gpow_iff_mem_range_order_of
- \+ *lemma* order_eq_card_range_gpow
- \+ *def* order_of
- \+ *lemma* order_of_dvd_card_univ
- \+ *lemma* order_of_le_card_univ
- \+ *lemma* order_of_ne_zero
- \+ *lemma* pow_eq_mod_order_of
- \+ *lemma* pow_injective_of_lt_order_of
- \+ *lemma* pow_order_of_eq_one

Modified set_theory/cardinal.lean




## [2018-03-10 12:39:38+01:00](https://github.com/leanprover-community/mathlib/commit/d010717)
chore(linear_algebra): flatten hierarchy, move algebra/linear_algebra to linear_algebra
#### Estimated changes
Deleted algebra/linear_algebra/default.lean


Renamed algebra/linear_algebra/basic.lean to linear_algebra/basic.lean


Added linear_algebra/default.lean


Renamed algebra/linear_algebra/dimension.lean to linear_algebra/dimension.lean


Renamed algebra/linear_algebra/linear_map_module.lean to linear_algebra/linear_map_module.lean


Renamed algebra/linear_algebra/multivariate_polynomial.lean to linear_algebra/multivariate_polynomial.lean


Renamed algebra/linear_algebra/prod_module.lean to linear_algebra/prod_module.lean


Renamed algebra/linear_algebra/quotient_module.lean to linear_algebra/quotient_module.lean


Renamed algebra/linear_algebra/subtype_module.lean to linear_algebra/subtype_module.lean




## [2018-03-09 15:55:09+01:00](https://github.com/leanprover-community/mathlib/commit/d78c8ea)
chore(ring_theory): cleaned up ideals
#### Estimated changes
Modified analysis/topology/topological_structures.lean


Modified data/set/basic.lean
- \+ *lemma* set.exists_of_ssubset

Modified logic/basic.lean
- \+ *theorem* classical.or_iff_not_imp_left
- \+ *theorem* classical.or_iff_not_imp_right

Modified order/filter.lean


Modified order/zorn.lean


Modified ring_theory/ideals.lean
- \+/\- *theorem* is_maximal_ideal.mk
- \+/\- *def* local_of_nonunits_ideal
- \+/\- *theorem* not_unit_of_mem_maximal_ideal

Modified ring_theory/localization.lean




## [2018-03-09 14:39:42+01:00](https://github.com/leanprover-community/mathlib/commit/06c54b3)
chore(ring_theory): introduce r_of_eq for localization
#### Estimated changes
Modified ring_theory/localization.lean
- \+/\- *def* localization.of_comm_ring
- \+ *theorem* localization.r_of_eq
- \+/\- *theorem* localization.refl



## [2018-03-09 14:39:42+01:00](https://github.com/leanprover-community/mathlib/commit/e658d36)
chore(ring_theory): fix indentation
#### Estimated changes
Modified ring_theory/localization.lean




## [2018-03-08 16:21:02+01:00](https://github.com/leanprover-community/mathlib/commit/a6960f5)
chore(ring_theory): add copyright headers
#### Estimated changes
Modified ring_theory/ideals.lean


Modified ring_theory/localization.lean




## [2018-03-08 13:57:16+01:00](https://github.com/leanprover-community/mathlib/commit/fe0f2a3)
fix(analysis/topology/topological_structures): remove unnecessary hypothesis
#### Estimated changes
Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* tendsto_of_tendsto_of_tendsto_of_le_of_le



## [2018-03-08 11:45:04+01:00](https://github.com/leanprover-community/mathlib/commit/a7d8c5f)
feat(tactic): add `wlog` (without loss of generality), `tauto`, `auto` and `xassumption`
* `tauto`: for simple tautologies;
* `auto`: discharging the goals that follow directly from a few assumption applications;
* `xassumption`: similar to `assumption` but matches against the head of assumptions instead of the whole thing
#### Estimated changes
Modified meta/expr.lean


Modified tactic/basic.lean


Modified tactic/interactive.lean


Added tests/wlog.lean




## [2018-03-08 11:25:28+01:00](https://github.com/leanprover-community/mathlib/commit/c852939)
feat(ring_theory): move localization
#### Estimated changes
Modified algebra/group.lean


Modified algebra/group_power.lean
- \+ *def* powers

Deleted algebra/localization.lean
- \- *def* loc.add
- \- *def* loc.add_aux
- \- *def* loc.loc
- \- *def* loc.mul
- \- *def* loc.mul_aux
- \- *def* loc.neg
- \- *def* loc.neg_aux

Modified algebra/module.lean
- \+ *theorem* is_submodule.eq_univ_of_contains_unit
- \+ *theorem* is_submodule.univ_of_one_mem

Modified algebra/ring.lean
- \+ *lemma* is_ring_hom.map_neg
- \+ *lemma* is_ring_hom.map_sub
- \+ *lemma* is_ring_hom.map_zero
- \+ *def* nonunits

Modified data/quot.lean
- \+ *lemma* quotient.lift_beta
- \+ *lemma* quotient.lift_on_beta

Added ring_theory/ideals.lean
- \+ *theorem* is_maximal_ideal.mk
- \+ *def* local_of_nonunits_ideal
- \+ *theorem* mem_or_mem_of_mul_eq_zero
- \+ *theorem* not_unit_of_mem_maximal_ideal

Added ring_theory/localization.lean
- \+ *def* localization.at_prime
- \+ *def* localization.away
- \+ *def* localization.closure
- \+ *lemma* localization.eq_zero_of_ne_zero_of_mul_eq_zero
- \+ *inductive* localization.in_closure
- \+ *def* localization.loc
- \+ *lemma* localization.mem_non_zero_divisors_of_ne_zero
- \+ *lemma* localization.ne_zero_of_mem_non_zero_divisors
- \+ *def* localization.non_zero_divisors
- \+ *def* localization.of_comm_ring
- \+ *def* localization.quotient_ring.field.of_integral_domain
- \+ *def* localization.quotient_ring
- \+ *def* localization.r
- \+ *theorem* localization.refl
- \+ *theorem* localization.subset_closure
- \+ *theorem* localization.symm
- \+ *theorem* localization.trans



## [2018-03-08 10:42:28+01:00](https://github.com/leanprover-community/mathlib/commit/0b81b24)
feat(analysis/topological_structures): add tendsto_of_tendsto_of_tendsto_of_le_of_le
#### Estimated changes
Modified analysis/ennreal.lean


Modified analysis/topology/topological_structures.lean
- \+ *lemma* tendsto_of_tendsto_of_tendsto_of_le_of_le
- \+/\- *lemma* tendsto_orderable



## [2018-03-08 09:55:42+01:00](https://github.com/leanprover-community/mathlib/commit/353c494)
fix(docs): more converter -> conversion
#### Estimated changes
Modified docs/extras.md


Modified docs/extras/conv.md




## [2018-03-08 09:51:03+01:00](https://github.com/leanprover-community/mathlib/commit/fa25539)
feat(docs/extras/conv): Documents conv mode ([#73](https://github.com/leanprover-community/mathlib/pull/73))
#### Estimated changes
Modified README.md


Added docs/extras.md


Added docs/extras/conv.md




## [2018-03-07 13:47:04+01:00](https://github.com/leanprover-community/mathlib/commit/22237f4)
feat(data/fintype): pi is closed under fintype & decidable_eq
#### Estimated changes
Modified data/fintype.lean




## [2018-03-07 13:47:00+01:00](https://github.com/leanprover-community/mathlib/commit/e6afbf5)
feat(data/finset): add Cartesian product over dependent functions
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* finset.mem_pi
- \+ *def* finset.pi



## [2018-03-07 13:46:54+01:00](https://github.com/leanprover-community/mathlib/commit/10cf239)
feat(data/multiset): add Cartesian product over dependent functions
#### Estimated changes
Modified data/multiset.lean
- \+/\- *lemma* multiset.bind_bind
- \+/\- *lemma* multiset.bind_hcongr
- \+ *lemma* multiset.card_pi
- \+/\- *lemma* multiset.map_hcongr
- \+ *lemma* multiset.mem_pi
- \+ *def* multiset.pi.cons
- \+ *lemma* multiset.pi.cons_ne
- \+ *lemma* multiset.pi.cons_same
- \+ *lemma* multiset.pi.cons_swap
- \+ *def* multiset.pi.empty
- \+ *def* multiset.pi
- \+ *lemma* multiset.pi_cons
- \+ *lemma* multiset.pi_zero



## [2018-03-07 13:46:54+01:00](https://github.com/leanprover-community/mathlib/commit/be4a35f)
feat(data/multiset): add dependent recursor for multisets
#### Estimated changes
Modified data/list/basic.lean


Modified data/list/perm.lean
- \+ *lemma* list.rec_heq_of_perm

Modified data/multiset.lean
- \+ *lemma* multiset.rec_on_0
- \+ *lemma* multiset.rec_on_cons



## [2018-03-07 13:46:39+01:00](https://github.com/leanprover-community/mathlib/commit/eef3a4d)
feat(data/multiset): add map_hcongr, bind_hcongr, bind_bind, attach_zero, and attach_cons
#### Estimated changes
Modified data/multiset.lean
- \+ *lemma* multiset.attach_cons
- \+ *lemma* multiset.attach_zero
- \+ *lemma* multiset.bind_bind
- \+ *lemma* multiset.bind_congr
- \+ *lemma* multiset.bind_hcongr
- \+ *theorem* multiset.card_singleton
- \+ *lemma* multiset.count_bind
- \+ *lemma* multiset.map_bind
- \+ *lemma* multiset.map_hcongr
- \+ *lemma* multiset.mem_cons_of_mem
- \+ *lemma* multiset.prod_map_mul
- \+ *lemma* multiset.prod_map_prod_map



## [2018-03-07 13:46:39+01:00](https://github.com/leanprover-community/mathlib/commit/bbd0203)
feat(data/multiset): decidable equality for functions whose domain is bounded by multisets
#### Estimated changes
Modified data/multiset.lean




## [2018-03-07 13:46:32+01:00](https://github.com/leanprover-community/mathlib/commit/dc8c35f)
feat(logic/function): add hfunext and funext_iff
#### Estimated changes
Modified logic/function.lean
- \+ *lemma* function.funext_iff
- \+ *lemma* function.hfunext



## [2018-03-06 16:12:46-05:00](https://github.com/leanprover-community/mathlib/commit/33be7dc)
doc(docs/theories): Description of other set-like types
From [#75](https://github.com/leanprover-community/mathlib/pull/75)
#### Estimated changes
Modified docs/theories.md


Modified docs/theories/sets.md




## [2018-03-05 21:58:36+01:00](https://github.com/leanprover-community/mathlib/commit/65cab91)
doc(order/filter): add documentation for `filter_upward`
#### Estimated changes
Modified order/filter.lean
- \+/\- *lemma* filter.tendsto_vmap_iff



## [2018-03-05 18:18:38+01:00](https://github.com/leanprover-community/mathlib/commit/5193194)
feat(order/filter): reorder filter theory; add filter_upwards tactic
#### Estimated changes
Modified analysis/topology/topological_space.lean


Modified analysis/topology/uniform_space.lean


Modified order/filter.lean
- \+/\- *lemma* filter.Inter_mem_sets
- \+/\- *lemma* filter.exists_sets_subset_iff
- \+/\- *lemma* filter.filter.ext
- \+/\- *lemma* filter.filter_eq_iff
- \+/\- *lemma* filter.inter_mem_sets
- \+/\- *lemma* filter.mem_inf_sets_of_left
- \+/\- *lemma* filter.mem_inf_sets_of_right
- \+ *lemma* filter.mp_sets
- \+ *lemma* filter.tendsto_inf_left
- \+ *lemma* filter.tendsto_inf_right
- \+/\- *lemma* filter.univ_mem_sets'
- \+/\- *lemma* filter.univ_mem_sets



## [2018-03-05 17:55:59+01:00](https://github.com/leanprover-community/mathlib/commit/0487a32)
chore(*): cleanup
#### Estimated changes
Modified analysis/topology/topological_space.lean


Modified logic/function.lean
- \+ *lemma* function.comp_apply
- \+ *def* function.update
- \+ *lemma* function.update_noteq
- \+ *lemma* function.update_same

Modified order/filter.lean
- \+/\- *lemma* filter.binfi_sup_eq
- \+/\- *lemma* filter.infi_sup_eq
- \+ *lemma* lattice.inf_left_comm
- \+ *lemma* lattice.infi_empty_finset
- \+ *lemma* lattice.infi_insert_finset



## [2018-03-05 16:11:22+01:00](https://github.com/leanprover-community/mathlib/commit/ec9dac3)
chore(*): update to Lean d6d44a19
#### Estimated changes
Modified data/encodable.lean


Modified data/equiv.lean


Modified data/list/basic.lean
- \+/\- *theorem* list.exists_of_mem_bind
- \+/\- *theorem* list.length_bind
- \+/\- *theorem* list.mem_bind
- \+/\- *theorem* list.mem_bind_of_mem

Modified data/option.lean
- \+ *lemma* option.seq_some

Modified data/prod.lean
- \- *lemma* prod.mk.eta

Modified tactic/converter/old_conv.lean


