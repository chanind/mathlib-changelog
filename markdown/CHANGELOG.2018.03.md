## [2018-03-30 14:05:43+02:00](https://github.com/leanprover-community/mathlib/commit/162edc3)
feat(order): add complete lattice of fixed points (Knaster-Tarski) by Kenny Lau https://github.com/leanprover/mathlib/pull/88
#### Estimated changes
modified order/basic.lean
- \+ *theorem* ge_of_eq

modified order/fixed_points.lean
- \+ *lemma* prev_eq
- \+ *lemma* next_eq
- \+ *theorem* prev_le
- \+ *theorem* next_le
- \+ *theorem* sup_le_f_of_fixed_points
- \+ *theorem* f_le_inf_of_fixed_points
- \+ *theorem* Sup_le_f_of_fixed_points
- \+ *theorem* f_le_Inf_of_fixed_points
- \- *theorem* ge_of_eq
- \+ *def* fixed_points
- \+ *def* prev
- \+ *def* next
- \+ *def* prev_fixed
- \+ *def* next_fixed



## [2018-03-29 17:23:46+02:00](https://github.com/leanprover-community/mathlib/commit/c54d431)
fix(.): unit is now an abbreviation: unit := punit.{1}
#### Estimated changes
modified data/encodable.lean

modified data/equiv.lean
- \+/\- *theorem* prod_unit_apply
- \+/\- *theorem* unit_prod_apply
- \+/\- *theorem* prod_unit_apply
- \+/\- *theorem* unit_prod_apply
- \+ *def* punit_equiv_punit
- \+/\- *def* arrow_unit_equiv_unit
- \+/\- *def* unit_arrow_equiv
- \+/\- *def* empty_arrow_equiv_unit
- \+/\- *def* false_arrow_equiv_unit
- \+/\- *def* arrow_empty_unit
- \+/\- *def* prod_unit
- \+/\- *def* unit_prod
- \+/\- *def* bool_equiv_unit_sum_unit
- \+/\- *def* option_equiv_sum_unit
- \+/\- *def* nat_equiv_nat_sum_unit
- \+/\- *def* nat_sum_unit_equiv_nat
- \+/\- *def* arrow_unit_equiv_unit
- \+/\- *def* unit_arrow_equiv
- \+/\- *def* empty_arrow_equiv_unit
- \+/\- *def* false_arrow_equiv_unit
- \+/\- *def* arrow_empty_unit
- \+/\- *def* prod_unit
- \+/\- *def* unit_prod
- \+/\- *def* bool_equiv_unit_sum_unit
- \+/\- *def* option_equiv_sum_unit
- \+/\- *def* nat_equiv_nat_sum_unit
- \+/\- *def* nat_sum_unit_equiv_nat

modified set_theory/ordinal.lean
- \+/\- *theorem* is_normal.limit_le
- \+/\- *theorem* is_normal.limit_le



## [2018-03-25 19:59:40-04:00](https://github.com/leanprover-community/mathlib/commit/d84af03)
fix(data/option): revert to lean commit 28f414
#### Estimated changes
modified data/option.lean



## [2018-03-22 14:08:02+01:00](https://github.com/leanprover-community/mathlib/commit/e5c1c5e)
fix(number_theory/dipoh): has_map.map -> functor.map
#### Estimated changes
modified number_theory/dioph.lean



## [2018-03-22 11:27:24+01:00](https://github.com/leanprover-community/mathlib/commit/a357b79)
feat(analysis): measurable_if
#### Estimated changes
modified analysis/measure_theory/measurable_space.lean
- \+ *lemma* measurable_if



## [2018-03-21 19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/868bbc6)
fix(*): update to lean
#### Estimated changes
modified category/basic.lean
- \- *lemma* pure_seq_eq_map
- \- *lemma* bind_assoc

modified data/list/basic.lean

modified data/nat/basic.lean

modified data/option.lean
- \+ *lemma* map_id'

modified data/pfun.lean

modified data/seq/computation.lean

modified data/seq/parallel.lean

modified data/seq/seq.lean

modified data/seq/wseq.lean

modified data/set/lattice.lean

modified order/filter.lean

modified tactic/converter/binders.lean

modified tactic/converter/old_conv.lean



## [2018-03-21 19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/638265c)
fix(set_theory/zfc): improve pSet.equiv.eq
I claimed in the comment that this converse was not provable, but it is (because equiv is embedded in the definition of mem). Thanks to Vinoth Kumar Raman for bringing this to my attention.
#### Estimated changes
modified set_theory/zfc.lean
- \+ *theorem* equiv_iff_mem
- \+/\- *theorem* equiv.eq
- \+/\- *theorem* equiv.eq



## [2018-03-21 19:31:04-04:00](https://github.com/leanprover-community/mathlib/commit/f3660df)
chore(logic/basic): protect classical logic theorems
You can't use these theorems with `open classical` anyway, because of disambiguation with the `_root_` theorems of the same name.
#### Estimated changes
modified logic/basic.lean
- \- *theorem* not_forall
- \- *theorem* forall_or_distrib_left
- \- *theorem* or_iff_not_imp_left
- \- *theorem* or_iff_not_imp_right



## [2018-03-21 18:56:23-04:00](https://github.com/leanprover-community/mathlib/commit/486e4ed)
fix(test suite): remove `sorry` warning in test suite
#### Estimated changes
modified tests/wlog.lean



## [2018-03-15 00:57:20-04:00](https://github.com/leanprover-community/mathlib/commit/f7977ff)
feat(data/finset): add finset.powerset
#### Estimated changes
modified data/finset.lean
- \+ *theorem* mem_powerset
- \+ *theorem* empty_mem_powerset
- \+ *theorem* mem_powerset_self
- \+ *theorem* powerset_mono
- \+ *theorem* card_powerset
- \+ *def* powerset

modified data/list/basic.lean
- \+ *theorem* reverse_injective
- \+ *theorem* sublists'_nil
- \+ *theorem* sublists'_singleton
- \+ *theorem* map_sublists'_aux
- \+ *theorem* sublists'_aux_append
- \+ *theorem* sublists'_aux_eq_sublists'
- \+ *theorem* sublists'_cons
- \+ *theorem* mem_sublists'
- \+ *theorem* length_sublists'
- \+ *theorem* sublists_reverse
- \+ *theorem* sublists_eq_sublists'
- \+ *theorem* sublists'_reverse
- \+ *theorem* sublists'_eq_sublists
- \+/\- *theorem* length_sublists
- \+ *theorem* pairwise_sublists'
- \+/\- *theorem* pairwise_sublists
- \+/\- *theorem* nodup_map
- \+ *theorem* nodup_map_iff
- \+ *theorem* nodup_sublists'
- \+/\- *theorem* length_sublists
- \+/\- *theorem* pairwise_sublists
- \+/\- *theorem* nodup_map
- \+ *def* sublists'_aux
- \+ *def* sublists'

modified data/list/perm.lean
- \+ *theorem* perm_ext_sublist_nodup
- \+ *theorem* sublists_cons_perm_append
- \+ *theorem* sublists_perm_sublists'

modified data/multiset.lean
- \+ *theorem* powerset_aux_eq_map_coe
- \+ *theorem* powerset_aux_perm_powerset_aux'
- \+ *theorem* powerset_aux'_nil
- \+ *theorem* powerset_aux'_cons
- \+ *theorem* powerset_aux'_perm
- \+ *theorem* powerset_aux_perm
- \+ *theorem* powerset_coe
- \+ *theorem* powerset_coe'
- \+ *theorem* mem_powerset
- \+ *theorem* map_single_le_powerset
- \+ *theorem* card_powerset
- \+ *theorem* nodup_powerset
- \+/\- *def* pmap
- \+ *def* powerset_aux
- \+ *def* powerset_aux'
- \+ *def* powerset
- \+/\- *def* pmap



## [2018-03-13 05:57:49-04:00](https://github.com/leanprover-community/mathlib/commit/4ceb545)
feat(data/list/basic): stuff about `list.sublists`
#### Estimated changes
modified analysis/topology/topological_space.lean

modified data/list/basic.lean
- \+ *theorem* length_eq_zero
- \+ *theorem* subset_def
- \+ *theorem* cons_subset
- \+/\- *theorem* cons_subset_of_subset_of_mem
- \+ *theorem* bind_eq_bind
- \+/\- *theorem* reverse_nil
- \+/\- *theorem* reverse_singleton
- \+ *theorem* reverse_inj
- \+ *theorem* reverse_eq_nil
- \+ *theorem* reverse_rec_on
- \+ *theorem* bind_ret_eq_map
- \+ *theorem* map_eq_map
- \+ *theorem* sublists_nil
- \+ *theorem* sublists_singleton
- \+ *theorem* sublists_aux₁_eq_sublists_aux
- \+ *theorem* sublists_aux_cons_eq_sublists_aux₁
- \+ *theorem* sublists_aux_eq_foldr.aux
- \+ *theorem* sublists_aux_eq_foldr
- \+ *theorem* sublists_aux₁_append
- \+ *theorem* sublists_aux₁_concat
- \+ *theorem* sublists_aux₁_bind
- \+ *theorem* sublists_aux_cons_append
- \+ *theorem* sublists_append
- \+ *theorem* sublists_concat
- \+ *theorem* sublists_aux_ne_nil
- \+/\- *theorem* mem_sublists
- \+ *theorem* length_sublists
- \+ *theorem* map_ret_sublist_sublists
- \+ *theorem* lex_append_right
- \+ *theorem* lex_append_left
- \+ *theorem* lex.imp
- \+ *theorem* ne_of_lex_ne
- \+ *theorem* lex_ne_iff
- \+ *theorem* pairwise_sublists
- \+ *theorem* nodup_sublists
- \+/\- *theorem* cons_subset_of_subset_of_mem
- \+/\- *theorem* reverse_nil
- \+/\- *theorem* reverse_singleton
- \- *theorem* sublists_aux_eq_foldl
- \+/\- *theorem* mem_sublists
- \+ *def* sublists_aux₁



## [2018-03-12 20:45:43+01:00](https://github.com/leanprover-community/mathlib/commit/5f8c26c)
feat(analysis/measure_theory): measures are embedded in outer measures; add map, dirac, and sum measures
#### Estimated changes
modified analysis/ennreal.lean
- \+ *lemma* tsum_supr_eq

modified analysis/measure_theory/measure_space.lean
- \+ *lemma* le_to_outer_measure_caratheodory
- \+ *lemma* to_outer_measure_to_measure
- \+ *lemma* map_measure
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *def* map
- \+ *def* dirac
- \+ *def* sum
- \+/\- *def* count
- \+/\- *def* count



## [2018-03-12 17:09:31+01:00](https://github.com/leanprover-community/mathlib/commit/36a061b)
feat(analysis/measure_theory): outer_measures form a complete lattice
#### Estimated changes
modified analysis/measure_theory/measure_space.lean

modified analysis/measure_theory/outer_measure.lean
- \+/\- *lemma* subadditive
- \+ *lemma* outer_measure_eq
- \+/\- *lemma* subadditive



## [2018-03-11 14:26:05+01:00](https://github.com/leanprover-community/mathlib/commit/64a8d56)
chore(order/filter): simplify definition of filter.prod; cleanup
#### Estimated changes
modified analysis/ennreal.lean

modified analysis/real.lean

modified analysis/topology/continuity.lean
- \+/\- *lemma* nhds_prod_eq
- \+/\- *lemma* nhds_prod_eq

modified analysis/topology/topological_space.lean
- \+ *lemma* nhds_sup

modified analysis/topology/uniform_space.lean
- \+/\- *lemma* uniformity_le_symm
- \+/\- *lemma* uniformity_le_symm

modified data/analysis/filter.lean

modified order/filter.lean
- \+/\- *lemma* map_eq_vmap_of_inverse
- \+ *lemma* map_swap_eq_vmap_swap
- \+/\- *lemma* mem_infi_sets
- \+/\- *lemma* infi_sets_induct
- \+ *lemma* le_lift
- \+/\- *lemma* map_lift_eq
- \+/\- *lemma* vmap_lift_eq
- \+ *lemma* lift_const
- \+ *lemma* lift_inf
- \+ *lemma* lift_principal2
- \+/\- *lemma* lift_infi
- \+/\- *lemma* lift_infi'
- \+/\- *lemma* lift'_infi
- \+/\- *lemma* prod_vmap_vmap_eq
- \+ *lemma* prod_comm'
- \+/\- *lemma* prod_map_map_eq
- \+/\- *lemma* prod_inf_prod
- \+ *lemma* prod_bot1
- \+ *lemma* prod_bot2
- \+/\- *lemma* prod_principal_principal
- \+/\- *lemma* prod_def
- \+/\- *lemma* prod_same_eq
- \+/\- *lemma* mem_prod_same_iff
- \+/\- *lemma* prod_neq_bot
- \+/\- *lemma* map_lift_eq
- \+/\- *lemma* vmap_lift_eq
- \- *lemma* prod_mem_prod
- \+/\- *lemma* prod_same_eq
- \- *lemma* mem_prod_sets
- \+/\- *lemma* prod_def
- \+/\- *lemma* mem_prod_same_iff
- \+/\- *lemma* prod_map_map_eq
- \+/\- *lemma* prod_vmap_vmap_eq
- \+/\- *lemma* prod_inf_prod
- \+/\- *lemma* prod_neq_bot
- \+/\- *lemma* prod_principal_principal
- \+/\- *lemma* mem_infi_sets
- \+/\- *lemma* infi_sets_induct
- \+/\- *lemma* lift_infi
- \+/\- *lemma* lift_infi'
- \+/\- *lemma* lift'_infi
- \+/\- *lemma* map_eq_vmap_of_inverse
- \- *lemma* map_swap_vmap_swap_eq



## [2018-03-10 20:37:53+01:00](https://github.com/leanprover-community/mathlib/commit/b154092)
feat(data/finsupp): make finsupp computable; add induction rule; removed comap_domain
#### Estimated changes
modified data/finsupp.lean
- \+ *lemma* mem_subtype
- \+/\- *lemma* support_zero
- \+/\- *lemma* mem_support_iff
- \+ *lemma* support_eq_empty
- \+/\- *lemma* finite_supp
- \+/\- *lemma* support_subset_iff
- \+/\- *lemma* single_apply
- \+/\- *lemma* single_eq_same
- \+/\- *lemma* single_eq_of_ne
- \+/\- *lemma* single_zero
- \+/\- *lemma* support_single_ne_zero
- \+/\- *lemma* support_single_subset
- \+ *lemma* on_finset_apply
- \+ *lemma* support_on_finset_subset
- \+/\- *lemma* map_range_apply
- \+/\- *lemma* support_map_range
- \+/\- *lemma* zip_with_apply
- \+/\- *lemma* support_zip_with
- \+ *lemma* support_erase
- \+ *lemma* erase_same
- \+ *lemma* erase_ne
- \+/\- *lemma* prod_map_range_index
- \+/\- *lemma* prod_single_index
- \+/\- *lemma* add_apply
- \+/\- *lemma* support_add
- \+/\- *lemma* single_add
- \+ *lemma* single_add_erase
- \+/\- *lemma* prod_neg_index
- \+/\- *lemma* sum_apply
- \+/\- *lemma* support_sum
- \+/\- *lemma* prod_finset_sum_index
- \+/\- *lemma* prod_sum_index
- \+/\- *lemma* map_domain_finset_sum
- \+/\- *lemma* filter_apply_pos
- \+/\- *lemma* filter_apply_neg
- \+/\- *lemma* support_filter
- \+/\- *lemma* filter_pos_add_filter_neg
- \+ *lemma* support_subtype_domain
- \+/\- *lemma* subtype_domain_apply
- \+/\- *lemma* subtype_domain_zero
- \+/\- *lemma* prod_single
- \+/\- *lemma* finite_supp
- \+/\- *lemma* mem_support_iff
- \+/\- *lemma* support_subset_iff
- \+/\- *lemma* support_zero
- \+/\- *lemma* single_apply
- \+/\- *lemma* single_eq_same
- \+/\- *lemma* single_eq_of_ne
- \+/\- *lemma* single_zero
- \+/\- *lemma* support_single_subset
- \+/\- *lemma* support_single_ne_zero
- \+/\- *lemma* map_range_apply
- \+/\- *lemma* support_map_range
- \+/\- *lemma* zip_with_apply
- \+/\- *lemma* support_zip_with
- \+/\- *lemma* filter_apply_pos
- \+/\- *lemma* filter_apply_neg
- \+/\- *lemma* support_filter
- \+/\- *lemma* prod_map_range_index
- \+/\- *lemma* prod_single_index
- \+/\- *lemma* add_apply
- \+/\- *lemma* support_add
- \+/\- *lemma* single_add
- \+/\- *lemma* filter_pos_add_filter_neg
- \+/\- *lemma* prod_neg_index
- \+/\- *lemma* sum_apply
- \+/\- *lemma* support_sum
- \+/\- *lemma* prod_finset_sum_index
- \+/\- *lemma* prod_sum_index
- \+/\- *lemma* map_domain_finset_sum
- \- *lemma* comap_domain_apply
- \- *lemma* comap_domain_zero
- \- *lemma* prod_comap_domain_index
- \+/\- *lemma* subtype_domain_apply
- \+/\- *lemma* subtype_domain_zero
- \- *lemma* comap_domain_add
- \- *lemma* comap_domain_sum
- \- *lemma* comap_domain_finsupp_sum
- \- *lemma* comap_domain_neg
- \- *lemma* comap_domain_sub
- \+/\- *lemma* prod_single
- \+ *def* on_finset
- \+/\- *def* map_range
- \+/\- *def* zip_with
- \+ *def* erase
- \+/\- *def* filter
- \+/\- *def* subtype_domain
- \- *def* finsupp
- \- *def* support
- \+/\- *def* map_range
- \+/\- *def* zip_with
- \+/\- *def* filter
- \- *def* comap_domain
- \+/\- *def* subtype_domain

modified linear_algebra/basic.lean



## [2018-03-10 13:38:59+01:00](https://github.com/leanprover-community/mathlib/commit/b97b7c3)
feat(group_theory): add a little bit of group theory; prove of Lagrange's theorem
#### Estimated changes
modified data/equiv.lean
- \+ *def* subtype_subtype_equiv_subtype

modified data/finset.lean
- \+ *lemma* card_eq_of_bijective
- \+ *lemma* card_le_card_of_inj_on
- \+ *lemma* card_le_of_inj_on
- \+ *theorem* card_attach

modified data/fintype.lean
- \+ *def* fintype.fintype_prod_left
- \+ *def* fintype.fintype_prod_right

modified data/int/basic.lean

modified data/multiset.lean
- \+ *theorem* card_attach

modified data/set/finite.lean
- \+ *lemma* infinite_univ_nat
- \+ *lemma* not_injective_nat_fintype
- \+ *lemma* not_injective_int_fintype

created group_theory/subgroup.lean
- \+ *lemma* mem_range_iff_mem_finset_range_of_mod_eq
- \+ *lemma* inv_mem
- \+ *lemma* inv_mem_iff
- \+ *lemma* mul_mem
- \+ *lemma* mul_image
- \+ *lemma* injective_mul
- \+ *lemma* subgroup_mem_cosets
- \+ *lemma* cosets_disjoint
- \+ *lemma* pairwise_cosets_disjoint
- \+ *lemma* cosets_equiv_subgroup
- \+ *lemma* Union_cosets_eq_univ
- \+ *lemma* group_equiv_cosets_times_subgroup
- \+ *lemma* is_subgroup_range_gpow
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
- \+ *def* cosets
- \+ *def* order_of

modified set_theory/cardinal.lean



## [2018-03-10 12:39:38+01:00](https://github.com/leanprover-community/mathlib/commit/d010717)
chore(linear_algebra): flatten hierarchy, move algebra/linear_algebra to linear_algebra
#### Estimated changes
deleted algebra/linear_algebra/default.lean

renamed algebra/linear_algebra/basic.lean to linear_algebra/basic.lean

created linear_algebra/default.lean

renamed algebra/linear_algebra/dimension.lean to linear_algebra/dimension.lean

renamed algebra/linear_algebra/linear_map_module.lean to linear_algebra/linear_map_module.lean

renamed algebra/linear_algebra/multivariate_polynomial.lean to linear_algebra/multivariate_polynomial.lean

renamed algebra/linear_algebra/prod_module.lean to linear_algebra/prod_module.lean

renamed algebra/linear_algebra/quotient_module.lean to linear_algebra/quotient_module.lean

renamed algebra/linear_algebra/subtype_module.lean to linear_algebra/subtype_module.lean



## [2018-03-09 15:55:09+01:00](https://github.com/leanprover-community/mathlib/commit/d78c8ea)
chore(ring_theory): cleaned up ideals
#### Estimated changes
modified analysis/topology/topological_structures.lean

modified data/set/basic.lean
- \+ *lemma* exists_of_ssubset

modified logic/basic.lean
- \+ *theorem* or_iff_not_imp_left
- \+ *theorem* or_iff_not_imp_right

modified order/filter.lean

modified order/zorn.lean

modified ring_theory/ideals.lean
- \+/\- *theorem* is_maximal_ideal.mk
- \+/\- *theorem* not_unit_of_mem_maximal_ideal
- \+/\- *theorem* is_maximal_ideal.mk
- \+/\- *theorem* not_unit_of_mem_maximal_ideal
- \+/\- *def* local_of_nonunits_ideal
- \+/\- *def* local_of_nonunits_ideal

modified ring_theory/localization.lean



## [2018-03-09 14:39:42+01:00](https://github.com/leanprover-community/mathlib/commit/06c54b3)
chore(ring_theory): introduce r_of_eq for localization
#### Estimated changes
modified ring_theory/localization.lean
- \+ *theorem* r_of_eq
- \+/\- *theorem* refl
- \+/\- *theorem* refl
- \+/\- *def* of_comm_ring
- \+/\- *def* of_comm_ring



## [2018-03-09 14:39:42+01:00](https://github.com/leanprover-community/mathlib/commit/e658d36)
chore(ring_theory): fix indentation
#### Estimated changes
modified ring_theory/localization.lean



## [2018-03-08 16:21:02+01:00](https://github.com/leanprover-community/mathlib/commit/a6960f5)
chore(ring_theory): add copyright headers
#### Estimated changes
modified ring_theory/ideals.lean

modified ring_theory/localization.lean



## [2018-03-08 13:57:16+01:00](https://github.com/leanprover-community/mathlib/commit/fe0f2a3)
fix(analysis/topology/topological_structures): remove unnecessary hypothesis
#### Estimated changes
modified analysis/topology/topological_structures.lean
- \+/\- *lemma* tendsto_of_tendsto_of_tendsto_of_le_of_le
- \+/\- *lemma* tendsto_of_tendsto_of_tendsto_of_le_of_le



## [2018-03-08 11:45:04+01:00](https://github.com/leanprover-community/mathlib/commit/a7d8c5f)
feat(tactic): add `wlog` (without loss of generality), `tauto`, `auto` and `xassumption`
* `tauto`: for simple tautologies;
* `auto`: discharging the goals that follow directly from a few assumption applications;
* `xassumption`: similar to `assumption` but matches against the head of assumptions instead of the whole thing
#### Estimated changes
modified meta/expr.lean

modified tactic/basic.lean

modified tactic/interactive.lean

created tests/wlog.lean



## [2018-03-08 11:25:28+01:00](https://github.com/leanprover-community/mathlib/commit/c852939)
feat(ring_theory): move localization
#### Estimated changes
modified algebra/group.lean

modified algebra/group_power.lean
- \+ *def* powers

deleted algebra/localization.lean
- \- *def* loc
- \- *def* add_aux
- \- *def* add
- \- *def* neg_aux
- \- *def* neg
- \- *def* mul_aux
- \- *def* mul

modified algebra/module.lean
- \+ *theorem* is_submodule.eq_univ_of_contains_unit
- \+ *theorem* is_submodule.univ_of_one_mem

modified algebra/ring.lean
- \+ *lemma* map_zero
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *def* nonunits

modified data/quot.lean
- \+ *lemma* quotient.lift_beta
- \+ *lemma* quotient.lift_on_beta

created ring_theory/ideals.lean
- \+ *theorem* mem_or_mem_of_mul_eq_zero
- \+ *theorem* is_maximal_ideal.mk
- \+ *theorem* not_unit_of_mem_maximal_ideal
- \+ *def* local_of_nonunits_ideal

created ring_theory/localization.lean
- \+ *lemma* ne_zero_of_mem_non_zero_divisors
- \+ *lemma* eq_zero_of_ne_zero_of_mul_eq_zero
- \+ *lemma* mem_non_zero_divisors_of_ne_zero
- \+ *theorem* refl
- \+ *theorem* symm
- \+ *theorem* trans
- \+ *theorem* subset_closure
- \+ *def* r
- \+ *def* loc
- \+ *def* of_comm_ring
- \+ *def* away
- \+ *def* at_prime
- \+ *def* closure
- \+ *def* non_zero_divisors
- \+ *def* quotient_ring
- \+ *def* quotient_ring.field.of_integral_domain



## [2018-03-08 10:42:28+01:00](https://github.com/leanprover-community/mathlib/commit/0b81b24)
feat(analysis/topological_structures): add tendsto_of_tendsto_of_tendsto_of_le_of_le
#### Estimated changes
modified analysis/ennreal.lean

modified analysis/topology/topological_structures.lean
- \+/\- *lemma* tendsto_orderable
- \+ *lemma* tendsto_of_tendsto_of_tendsto_of_le_of_le
- \+/\- *lemma* tendsto_orderable



## [2018-03-08 09:55:42+01:00](https://github.com/leanprover-community/mathlib/commit/353c494)
fix(docs): more converter -> conversion
#### Estimated changes
modified docs/extras.md

modified docs/extras/conv.md



## [2018-03-08 09:51:03+01:00](https://github.com/leanprover-community/mathlib/commit/fa25539)
feat(docs/extras/conv): Documents conv mode ([#73](https://github.com/leanprover-community/mathlib/pull/73))
#### Estimated changes
modified README.md

created docs/extras.md

created docs/extras/conv.md



## [2018-03-07 13:47:04+01:00](https://github.com/leanprover-community/mathlib/commit/22237f4)
feat(data/fintype): pi is closed under fintype & decidable_eq
#### Estimated changes
modified data/fintype.lean



## [2018-03-07 13:47:00+01:00](https://github.com/leanprover-community/mathlib/commit/e6afbf5)
feat(data/finset): add Cartesian product over dependent functions
#### Estimated changes
modified data/finset.lean
- \+ *lemma* mem_pi
- \+ *def* pi



## [2018-03-07 13:46:54+01:00](https://github.com/leanprover-community/mathlib/commit/10cf239)
feat(data/multiset): add Cartesian product over dependent functions
#### Estimated changes
modified data/multiset.lean
- \+/\- *lemma* map_hcongr
- \+/\- *lemma* bind_hcongr
- \+/\- *lemma* bind_bind
- \+ *lemma* pi.cons_same
- \+ *lemma* pi.cons_ne
- \+ *lemma* pi.cons_swap
- \+ *lemma* pi_zero
- \+ *lemma* pi_cons
- \+ *lemma* card_pi
- \+ *lemma* mem_pi
- \+/\- *lemma* map_hcongr
- \+/\- *lemma* bind_hcongr
- \+/\- *lemma* bind_bind
- \+ *def* pi.cons
- \+ *def* pi.empty
- \+ *def* pi



## [2018-03-07 13:46:54+01:00](https://github.com/leanprover-community/mathlib/commit/be4a35f)
feat(data/multiset): add dependent recursor for multisets
#### Estimated changes
modified data/list/basic.lean

modified data/list/perm.lean
- \+ *lemma* rec_heq_of_perm

modified data/multiset.lean
- \+ *lemma* rec_on_0
- \+ *lemma* rec_on_cons



## [2018-03-07 13:46:39+01:00](https://github.com/leanprover-community/mathlib/commit/eef3a4d)
feat(data/multiset): add map_hcongr, bind_hcongr, bind_bind, attach_zero, and attach_cons
#### Estimated changes
modified data/multiset.lean
- \+ *lemma* mem_cons_of_mem
- \+ *lemma* map_hcongr
- \+ *lemma* prod_map_mul
- \+ *lemma* prod_map_prod_map
- \+ *lemma* bind_congr
- \+ *lemma* bind_hcongr
- \+ *lemma* map_bind
- \+ *lemma* attach_zero
- \+ *lemma* attach_cons
- \+ *lemma* count_bind
- \+ *lemma* bind_bind
- \+ *theorem* card_singleton



## [2018-03-07 13:46:39+01:00](https://github.com/leanprover-community/mathlib/commit/bbd0203)
feat(data/multiset): decidable equality for functions whose domain is bounded by multisets
#### Estimated changes
modified data/multiset.lean



## [2018-03-07 13:46:32+01:00](https://github.com/leanprover-community/mathlib/commit/dc8c35f)
feat(logic/function): add hfunext and funext_iff
#### Estimated changes
modified logic/function.lean
- \+ *lemma* hfunext
- \+ *lemma* funext_iff



## [2018-03-06 16:12:46-05:00](https://github.com/leanprover-community/mathlib/commit/33be7dc)
doc(docs/theories): Description of other set-like types
From [#75](https://github.com/leanprover-community/mathlib/pull/75)
#### Estimated changes
modified docs/theories.md

modified docs/theories/sets.md
- \+ *def* x
- \+ *def* S
- \+ *def* finite



## [2018-03-05 21:58:36+01:00](https://github.com/leanprover-community/mathlib/commit/65cab91)
doc(order/filter): add documentation for `filter_upward`
#### Estimated changes
modified order/filter.lean
- \+/\- *lemma* tendsto_vmap_iff
- \+/\- *lemma* tendsto_vmap_iff



## [2018-03-05 18:18:38+01:00](https://github.com/leanprover-community/mathlib/commit/5193194)
feat(order/filter): reorder filter theory; add filter_upwards tactic
#### Estimated changes
modified analysis/topology/topological_space.lean

modified analysis/topology/uniform_space.lean

modified order/filter.lean
- \+/\- *lemma* filter_eq_iff
- \+/\- *lemma* filter.ext
- \+/\- *lemma* univ_mem_sets'
- \+/\- *lemma* univ_mem_sets
- \+/\- *lemma* inter_mem_sets
- \+ *lemma* mp_sets
- \+/\- *lemma* Inter_mem_sets
- \+/\- *lemma* exists_sets_subset_iff
- \+/\- *lemma* mem_principal_sets
- \+/\- *lemma* mem_principal_self
- \+/\- *lemma* mem_join_sets
- \+/\- *lemma* le_principal_iff
- \+/\- *lemma* principal_mono
- \+/\- *lemma* monotone_principal
- \+/\- *lemma* principal_eq_iff_eq
- \+/\- *lemma* mem_sup_sets
- \+/\- *lemma* mem_inf_sets
- \+/\- *lemma* mem_inf_sets_of_left
- \+/\- *lemma* mem_inf_sets_of_right
- \+/\- *lemma* inter_mem_inf_sets
- \+/\- *lemma* mem_top_sets_iff
- \+/\- *lemma* mem_bot_sets
- \+/\- *lemma* mem_Sup_sets
- \+/\- *lemma* join_principal_eq_Sup
- \+/\- *lemma* map_principal
- \+/\- *lemma* pure_def
- \+/\- *lemma* mem_pure
- \+/\- *lemma* map_def
- \+/\- *lemma* bind_def
- \+ *lemma* tendsto_inf_left
- \+ *lemma* tendsto_inf_right
- \+/\- *lemma* tendsto_fst
- \+/\- *lemma* tendsto_snd
- \+/\- *lemma* tendsto.prod_mk
- \+/\- *lemma* filter_eq_iff
- \+/\- *lemma* filter.ext
- \+/\- *lemma* univ_mem_sets'
- \+/\- *lemma* univ_mem_sets
- \+/\- *lemma* inter_mem_sets
- \+/\- *lemma* Inter_mem_sets
- \+/\- *lemma* exists_sets_subset_iff
- \+/\- *lemma* mem_join_sets
- \+/\- *lemma* mem_principal_sets
- \+/\- *lemma* mem_principal_self
- \+/\- *lemma* le_principal_iff
- \+/\- *lemma* principal_mono
- \+/\- *lemma* monotone_principal
- \+/\- *lemma* principal_eq_iff_eq
- \+/\- *lemma* mem_Sup_sets
- \+/\- *lemma* map_principal
- \+/\- *lemma* mem_top_sets_iff
- \+/\- *lemma* join_principal_eq_Sup
- \+/\- *lemma* pure_def
- \+/\- *lemma* map_def
- \+/\- *lemma* bind_def
- \+/\- *lemma* mem_inf_sets_of_left
- \+/\- *lemma* mem_inf_sets_of_right
- \+/\- *lemma* mem_bot_sets
- \+/\- *lemma* mem_sup_sets
- \+/\- *lemma* mem_inf_sets
- \+/\- *lemma* inter_mem_inf_sets
- \+/\- *lemma* mem_pure
- \+/\- *lemma* tendsto_fst
- \+/\- *lemma* tendsto_snd
- \+/\- *lemma* tendsto.prod_mk
- \+/\- *theorem* le_def
- \+/\- *theorem* le_def
- \+/\- *def* map
- \+/\- *def* vmap
- \+/\- *def* cofinite
- \+/\- *def* bind
- \+/\- *def* map
- \+/\- *def* vmap
- \+/\- *def* cofinite
- \+/\- *def* bind



## [2018-03-05 17:55:59+01:00](https://github.com/leanprover-community/mathlib/commit/0487a32)
chore(*): cleanup
#### Estimated changes
modified analysis/topology/topological_space.lean

modified logic/function.lean
- \+ *lemma* comp_apply
- \+ *lemma* update_same
- \+ *lemma* update_noteq
- \+ *def* update

modified order/filter.lean
- \+ *lemma* infi_insert_finset
- \+ *lemma* infi_empty_finset
- \+ *lemma* inf_left_comm
- \+/\- *lemma* binfi_sup_eq
- \+/\- *lemma* infi_sup_eq
- \+/\- *lemma* binfi_sup_eq
- \+/\- *lemma* infi_sup_eq



## [2018-03-05 16:11:22+01:00](https://github.com/leanprover-community/mathlib/commit/ec9dac3)
chore(*): update to Lean d6d44a19
#### Estimated changes
modified data/encodable.lean

modified data/equiv.lean

modified data/list/basic.lean
- \+/\- *theorem* mem_bind
- \+/\- *theorem* exists_of_mem_bind
- \+/\- *theorem* mem_bind_of_mem
- \+/\- *theorem* length_bind
- \+/\- *theorem* mem_bind
- \+/\- *theorem* exists_of_mem_bind
- \+/\- *theorem* mem_bind_of_mem
- \+/\- *theorem* length_bind

modified data/option.lean
- \+ *lemma* seq_some

modified data/prod.lean
- \- *lemma* mk.eta

modified tactic/converter/old_conv.lean

