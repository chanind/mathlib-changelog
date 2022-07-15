## [2018-08-31 17:48:25+02:00](https://github.com/leanprover-community/mathlib/commit/20b4143)
feat(algebra): add normalization and GCD domain; setup for int
#### Estimated changes
Added algebra/gcd_domain.lean
- \+ *theorem* associated_of_dvd_of_dvd
- \+ *theorem* dvd_antisymm_of_norm
- \+ *theorem* dvd_gcd_iff
- \+ *lemma* dvd_lcm_left
- \+ *lemma* dvd_lcm_right
- \+ *theorem* gcd_assoc
- \+ *theorem* gcd_comm
- \+ *theorem* gcd_dvd_gcd
- \+ *theorem* gcd_dvd_gcd_mul_left
- \+ *theorem* gcd_dvd_gcd_mul_left_right
- \+ *theorem* gcd_dvd_gcd_mul_right
- \+ *theorem* gcd_dvd_gcd_mul_right_right
- \+ *theorem* gcd_eq_left_iff
- \+ *theorem* gcd_eq_mul_norm_unit
- \+ *theorem* gcd_eq_right_iff
- \+ *theorem* gcd_eq_zero_iff
- \+ *theorem* gcd_mul_lcm
- \+ *theorem* gcd_mul_left
- \+ *theorem* gcd_mul_right
- \+ *theorem* gcd_one_left
- \+ *theorem* gcd_one_right
- \+ *theorem* gcd_same
- \+ *theorem* gcd_zero_left
- \+ *theorem* gcd_zero_right
- \+ *theorem* lcm_assoc
- \+ *theorem* lcm_comm
- \+ *lemma* lcm_dvd
- \+ *lemma* lcm_dvd_iff
- \+ *theorem* lcm_dvd_lcm
- \+ *theorem* lcm_dvd_lcm_mul_left
- \+ *theorem* lcm_dvd_lcm_mul_left_right
- \+ *theorem* lcm_dvd_lcm_mul_right
- \+ *theorem* lcm_dvd_lcm_mul_right_right
- \+ *theorem* lcm_eq_left_iff
- \+ *lemma* lcm_eq_mul_norm_unit
- \+ *theorem* lcm_eq_one_iff
- \+ *theorem* lcm_eq_right_iff
- \+ *theorem* lcm_eq_zero_iff
- \+ *theorem* lcm_mul_left
- \+ *theorem* lcm_mul_right
- \+ *theorem* lcm_one_left
- \+ *theorem* lcm_one_right
- \+ *theorem* lcm_same
- \+ *theorem* lcm_units_coe_left
- \+ *theorem* lcm_units_coe_right
- \+ *theorem* mul_norm_unit_eq_mul_norm_unit
- \+ *theorem* norm_unit_gcd
- \+ *lemma* norm_unit_lcm
- \+ *theorem* norm_unit_mul_norm_unit
- \+ *theorem* norm_unit_one

Modified data/int/gcd.lean
- \+ *lemma* int.coe_gcd
- \+ *lemma* int.coe_lcm
- \+ *theorem* int.coe_nat_abs_eq_mul_norm_unit
- \+/\- *theorem* int.dvd_gcd
- \- *theorem* int.eq_zero_of_gcd_eq_zero_left
- \- *theorem* int.eq_zero_of_gcd_eq_zero_right
- \+/\- *theorem* int.gcd_assoc
- \+/\- *theorem* int.gcd_comm
- \- *theorem* int.gcd_dvd
- \+ *theorem* int.gcd_eq_zero_iff
- \+/\- *theorem* int.gcd_one_right
- \+/\- *theorem* int.gcd_self
- \+/\- *theorem* int.gcd_zero_right
- \+/\- *def* int.lcm
- \+/\- *theorem* int.lcm_def
- \+/\- *theorem* int.lcm_dvd
- \+/\- *theorem* int.lcm_one_left
- \+/\- *theorem* int.lcm_one_right
- \+/\- *theorem* int.lcm_self
- \+/\- *theorem* int.lcm_zero_left
- \+/\- *theorem* int.lcm_zero_right
- \+ *lemma* int.nat_abs_gcd
- \+ *lemma* int.nat_abs_lcm
- \+ *lemma* int.norm_unit_nat_coe
- \+ *lemma* int.norm_unit_of_neg
- \+ *lemma* int.norm_unit_of_nonneg



## [2018-08-31 17:48:25+02:00](https://github.com/leanprover-community/mathlib/commit/5df7cac)
refactor(data/int/gcd): move int gcd proofs to the GCD theory
#### Estimated changes
Modified data/int/basic.lean
- \- *theorem* int.nat_abs_div
- \- *theorem* int.nat_abs_dvd_abs_iff
- \- *lemma* int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \- *def* nat.gcd_a
- \- *def* nat.gcd_b
- \- *theorem* nat.gcd_eq_gcd_ab
- \- *def* nat.xgcd
- \- *def* nat.xgcd_aux
- \- *theorem* nat.xgcd_aux_P
- \- *theorem* nat.xgcd_aux_fst
- \- *theorem* nat.xgcd_aux_rec
- \- *theorem* nat.xgcd_aux_val
- \- *theorem* nat.xgcd_val
- \- *theorem* nat.xgcd_zero_left

Modified data/int/gcd.lean
- \+/\- *theorem* int.gcd_comm
- \+/\- *theorem* int.gcd_dvd
- \+/\- *theorem* int.gcd_dvd_left
- \+/\- *theorem* int.gcd_mul_right
- \+/\- *theorem* int.lcm_one_right
- \+ *theorem* int.nat_abs_div
- \+ *theorem* int.nat_abs_dvd_abs_iff
- \+ *lemma* int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+ *def* nat.gcd_a
- \+ *def* nat.gcd_b
- \+ *theorem* nat.gcd_eq_gcd_ab
- \+ *def* nat.xgcd
- \+ *def* nat.xgcd_aux
- \+ *theorem* nat.xgcd_aux_P
- \+ *theorem* nat.xgcd_aux_fst
- \+ *theorem* nat.xgcd_aux_rec
- \+ *theorem* nat.xgcd_aux_val
- \+ *theorem* nat.xgcd_val
- \+ *theorem* nat.xgcd_zero_left

Modified data/nat/modeq.lean


Modified data/padics/padic_norm.lean


Modified data/zmod.lean




## [2018-08-31 17:48:25+02:00](https://github.com/leanprover-community/mathlib/commit/a89f28e)
feat(data/int/gcd): extended gcd to integers ([#218](https://github.com/leanprover-community/mathlib/pull/218))
Resurrected by @johoelzl. The original commit was not available anymore.
#### Estimated changes
Modified data/int/basic.lean
- \+ *theorem* int.nat_abs_div
- \+ *theorem* int.nat_abs_dvd_abs_iff
- \+/\- *theorem* int.nat_abs_neg_of_nat

Added data/int/gcd.lean
- \+ *theorem* int.dvd_gcd
- \+ *theorem* int.dvd_lcm_left
- \+ *theorem* int.dvd_lcm_right
- \+ *theorem* int.dvd_of_mul_dvd_mul_left
- \+ *theorem* int.dvd_of_mul_dvd_mul_right
- \+ *theorem* int.eq_zero_of_gcd_eq_zero_left
- \+ *theorem* int.eq_zero_of_gcd_eq_zero_right
- \+ *theorem* int.gcd_assoc
- \+ *theorem* int.gcd_comm
- \+ *theorem* int.gcd_div
- \+ *theorem* int.gcd_dvd
- \+ *theorem* int.gcd_dvd_gcd_mul_left
- \+ *theorem* int.gcd_dvd_gcd_mul_left_right
- \+ *theorem* int.gcd_dvd_gcd_mul_right
- \+ *theorem* int.gcd_dvd_gcd_mul_right_right
- \+ *theorem* int.gcd_dvd_gcd_of_dvd_left
- \+ *theorem* int.gcd_dvd_gcd_of_dvd_right
- \+ *theorem* int.gcd_dvd_left
- \+ *theorem* int.gcd_dvd_right
- \+ *theorem* int.gcd_eq_left
- \+ *theorem* int.gcd_eq_right
- \+ *theorem* int.gcd_mul_lcm
- \+ *theorem* int.gcd_mul_left
- \+ *theorem* int.gcd_mul_right
- \+ *theorem* int.gcd_one_left
- \+ *theorem* int.gcd_one_right
- \+ *theorem* int.gcd_pos_of_non_zero_left
- \+ *theorem* int.gcd_pos_of_non_zero_right
- \+ *theorem* int.gcd_self
- \+ *theorem* int.gcd_zero_left
- \+ *theorem* int.gcd_zero_right
- \+ *def* int.lcm
- \+ *theorem* int.lcm_assoc
- \+ *theorem* int.lcm_comm
- \+ *theorem* int.lcm_def
- \+ *theorem* int.lcm_dvd
- \+ *theorem* int.lcm_one_left
- \+ *theorem* int.lcm_one_right
- \+ *theorem* int.lcm_self
- \+ *theorem* int.lcm_zero_left
- \+ *theorem* int.lcm_zero_right



## [2018-08-31 14:44:58+02:00](https://github.com/leanprover-community/mathlib/commit/ee9bf5c)
feat(data/equiv): equiv_congr and perm_congr
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *def* equiv.equiv_congr
- \+ *def* equiv.perm_congr
- \+ *lemma* equiv.trans_assoc



## [2018-08-31 09:14:34+02:00](https://github.com/leanprover-community/mathlib/commit/4068d00)
feat(data/nat): simp rules for find_greatest
#### Estimated changes
Modified data/nat/basic.lean
- \+ *lemma* nat.find_greatest_eq
- \+ *lemma* nat.find_greatest_of_not
- \+ *lemma* nat.find_greatest_zero



## [2018-08-31 01:45:14+02:00](https://github.com/leanprover-community/mathlib/commit/2946088)
feat(tactic/explode): line by line proof display for proof terms
#### Estimated changes
Modified tactic/basic.lean


Added tactic/explode.lean
- \+ *def* tactic.explode.head'



## [2018-08-30 18:39:48+02:00](https://github.com/leanprover-community/mathlib/commit/86c955e)
feat(data/nat): find_greatest is always bounded
#### Estimated changes
Modified data/nat/basic.lean
- \+ *lemma* nat.find_greatest_le



## [2018-08-30 17:30:19+02:00](https://github.com/leanprover-community/mathlib/commit/c238aad)
refactor(data/nat): simplify find_greatest; fix namespace nat.nat.find_greatest -> nat.find_greatest
#### Estimated changes
Modified data/nat/basic.lean
- \+ *lemma* nat.find_greatest_is_greatest
- \+ *lemma* nat.find_greatest_spec
- \+ *lemma* nat.find_greatest_spec_and_le
- \+ *lemma* nat.le_find_greatest
- \+/\- *theorem* nat.mul_pow
- \+/\- *lemma* nat.nat.div_mul_div
- \- *lemma* nat.nat.find_greatest_is_greatest
- \- *lemma* nat.nat.find_greatest_spec



## [2018-08-30 15:34:45+02:00](https://github.com/leanprover-community/mathlib/commit/83edcc0)
refactor(data/nat,int): separate int from nat, i.e. do not import any int theory in nat
#### Estimated changes
Modified data/int/basic.lean
- \+ *theorem* int.coe_nat_dvd_left
- \+ *theorem* int.coe_nat_dvd_right
- \+/\- *lemma* int.dvd_nat_abs_of_of_nat_dvd
- \+/\- *lemma* int.pow_div_of_le_of_pow_div_int
- \+ *lemma* int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+ *def* nat.gcd_a
- \+ *def* nat.gcd_b
- \+ *theorem* nat.gcd_eq_gcd_ab
- \+ *def* nat.xgcd
- \+ *def* nat.xgcd_aux
- \+ *theorem* nat.xgcd_aux_P
- \+ *theorem* nat.xgcd_aux_fst
- \+ *theorem* nat.xgcd_aux_rec
- \+ *theorem* nat.xgcd_aux_val
- \+ *theorem* nat.xgcd_val
- \+ *theorem* nat.xgcd_zero_left

Modified data/nat/gcd.lean
- \- *def* nat.gcd_a
- \- *def* nat.gcd_b
- \- *theorem* nat.gcd_eq_gcd_ab
- \- *def* nat.xgcd
- \- *def* nat.xgcd_aux
- \- *theorem* nat.xgcd_aux_P
- \- *theorem* nat.xgcd_aux_fst
- \- *theorem* nat.xgcd_aux_rec
- \- *theorem* nat.xgcd_aux_val
- \- *theorem* nat.xgcd_val
- \- *theorem* nat.xgcd_zero_left

Modified data/nat/prime.lean
- \- *lemma* nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul_int

Modified data/padics/padic_norm.lean


Modified data/zmod.lean




## [2018-08-30 14:55:56+02:00](https://github.com/leanprover-community/mathlib/commit/d245165)
refactor(algebra): add more facts about units
#### Estimated changes
Modified algebra/field.lean
- \- *theorem* units.ne_zero

Modified algebra/group.lean
- \+ *def* units.mk_of_mul_eq_one

Modified algebra/ring.lean
- \+ *lemma* units.coe_dvd
- \+ *lemma* units.coe_mul_dvd
- \+ *lemma* units.dvd_coe
- \+ *lemma* units.dvd_coe_mul
- \+ *theorem* units.ne_zero
- \+ *lemma* zero_dvd_iff_eq_zero



## [2018-08-30 13:27:07+02:00](https://github.com/leanprover-community/mathlib/commit/b4b05dd)
feat(logic/basic): introduce pempty
#### Estimated changes
Modified data/equiv/basic.lean
- \- *def* equiv.arrow_empty_unit
- \+ *def* equiv.equiv_pempty
- \+ *def* equiv.false_equiv_pempty
- \+ *def* equiv.pempty_arrow_equiv_unit
- \+ *def* equiv.pempty_equiv_pempty
- \+ *def* equiv.pempty_prod
- \+ *def* equiv.pempty_sum
- \+ *def* equiv.prod_pempty
- \+ *def* equiv.sum_pempty

Modified data/fintype.lean
- \+ *theorem* fintype.card_pempty
- \+ *theorem* fintype.univ_pempty

Modified logic/basic.lean
- \+ *def* pempty.elim

Modified set_theory/cardinal.lean


Modified tactic/auto_cases.lean




## [2018-08-29 15:07:11+02:00](https://github.com/leanprover-community/mathlib/commit/afd1c06)
feat(algebra/group): is_add_group_hom
#### Estimated changes
Modified algebra/group.lean
- \+ *lemma* is_add_group_hom.sub



## [2018-08-29 14:48:07+02:00](https://github.com/leanprover-community/mathlib/commit/b0aadaa)
cleanup(analysis/bounded_linear_maps): some reorganization
#### Estimated changes
Added analysis/bounded_linear_maps.lean
- \+ *lemma* bounded_continuous_linear_map
- \+ *lemma* is_bounded_linear_map.add
- \+ *lemma* is_bounded_linear_map.comp
- \+ *lemma* is_bounded_linear_map.continuous
- \+ *lemma* is_bounded_linear_map.id
- \+ *lemma* is_bounded_linear_map.lim_zero_bounded_linear_map
- \+ *lemma* is_bounded_linear_map.neg
- \+ *lemma* is_bounded_linear_map.smul
- \+ *lemma* is_bounded_linear_map.sub
- \+ *lemma* is_bounded_linear_map.tendsto
- \+ *lemma* is_bounded_linear_map.zero
- \+ *lemma* is_linear_map.with_bound
- \+ *lemma* mul_inv_eq'

Deleted analysis/continuous_linear_maps.lean
- \- *lemma* bounded_continuous_linear_map
- \- *lemma* is_bounded_linear_map.add
- \- *lemma* is_bounded_linear_map.comp
- \- *lemma* is_bounded_linear_map.continuous
- \- *lemma* is_bounded_linear_map.id
- \- *lemma* is_bounded_linear_map.lim_zero_bounded_linear_map
- \- *lemma* is_bounded_linear_map.neg
- \- *lemma* is_bounded_linear_map.smul
- \- *lemma* is_bounded_linear_map.sub
- \- *lemma* is_bounded_linear_map.zero
- \- *def* is_bounded_linear_map

Modified analysis/metric_space.lean
- \+ *theorem* exists_delta_of_continuous

Modified analysis/normed_space.lean
- \+ *lemma* real.norm_eq_abs



## [2018-08-29 14:48:07+02:00](https://github.com/leanprover-community/mathlib/commit/21a9355)
feat(analysis/continuous_linear_maps)
#### Estimated changes
Added analysis/continuous_linear_maps.lean
- \+ *lemma* bounded_continuous_linear_map
- \+ *lemma* is_bounded_linear_map.add
- \+ *lemma* is_bounded_linear_map.comp
- \+ *lemma* is_bounded_linear_map.continuous
- \+ *lemma* is_bounded_linear_map.id
- \+ *lemma* is_bounded_linear_map.lim_zero_bounded_linear_map
- \+ *lemma* is_bounded_linear_map.neg
- \+ *lemma* is_bounded_linear_map.smul
- \+ *lemma* is_bounded_linear_map.sub
- \+ *lemma* is_bounded_linear_map.zero
- \+ *def* is_bounded_linear_map



## [2018-08-29 14:38:32+02:00](https://github.com/leanprover-community/mathlib/commit/49f700c)
feat(analysis/topology/uniform_space): prepare for completions ([#297](https://github.com/leanprover-community/mathlib/pull/297))
#### Estimated changes
Modified analysis/topology/uniform_space.lean
- \+ *lemma* eq_of_separated_of_uniform_continuous
- \+ *lemma* separated_of_uniform_continuous
- \+ *lemma* separation_prod
- \+/\- *lemma* uniform_continuous.prod_mk
- \+ *lemma* uniform_continuous.prod_mk_left
- \+ *lemma* uniform_continuous.prod_mk_right
- \+ *lemma* uniform_continuous_quotient
- \+ *lemma* uniform_continuous_quotient_lift
- \+ *lemma* uniform_continuous_quotient_lift₂
- \+ *lemma* uniformity_quotient



## [2018-08-29 02:55:13+02:00](https://github.com/leanprover-community/mathlib/commit/0c11112)
feat(logic/function): adds uncurry_def ([#293](https://github.com/leanprover-community/mathlib/pull/293))
#### Estimated changes
Modified logic/function.lean
- \+ *lemma* function.uncurry_def



## [2018-08-29 02:53:42+02:00](https://github.com/leanprover-community/mathlib/commit/b82ba3c)
feat(data/multiset): multisets are traversable using commutative, applicative functors ([#220](https://github.com/leanprover-community/mathlib/pull/220))
#### Estimated changes
Modified category/applicative.lean


Modified category/traversable/instances.lean
- \- *lemma* list.comp_traverse
- \- *lemma* list.id_traverse
- \- *lemma* list.naturality
- \- *lemma* list.traverse_eq_map_id
- \+ *lemma* traverse_append

Modified category/traversable/lemmas.lean
- \+ *lemma* traversable.map_traverse'

Modified data/multiset.lean
- \+ *lemma* multiset.coe_append_eq_add_coe
- \+ *lemma* multiset.coe_list_cons_eq_cons_coe
- \+ *lemma* multiset.coe_traverse_cons
- \+ *lemma* multiset.coe_traverse_cons_swap
- \+ *lemma* multiset.comp_traverse
- \+ *lemma* multiset.id_traverse
- \+ *lemma* multiset.lift_beta
- \+ *lemma* multiset.map_comp_coe
- \+ *lemma* multiset.map_traverse
- \+ *lemma* multiset.naturality
- \+ *def* multiset.traverse
- \+ *lemma* multiset.traverse_map



## [2018-08-29 02:46:53+02:00](https://github.com/leanprover-community/mathlib/commit/3e38b73)
feat(analysis/topology): density and continuity lemmas ([#292](https://github.com/leanprover-community/mathlib/pull/292))
Still from the perfectoid project
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* dense_embedding.closure_image_nhds_of_nhds
- \+ *lemma* dense_embedding.self_sub_closure_image_preimage_of_open
- \+ *lemma* dense_embedding.tendsto_vmap_nhds_nhds

Modified analysis/topology/topological_space.lean
- \+ *lemma* dense_iff_inter_open
- \+ *lemma* quotient_dense_of_dense



## [2018-08-29 02:45:15+02:00](https://github.com/leanprover-community/mathlib/commit/4eca29f)
doc(docs/howto-contribute.md): How to contribute to mathlib ([#291](https://github.com/leanprover-community/mathlib/pull/291))
#### Estimated changes
Modified README.md


Added docs/howto-contribute.md




## [2018-08-29 02:42:39+02:00](https://github.com/leanprover-community/mathlib/commit/79bb95c)
feat(analysis/topology, data/set): some zerology ([#295](https://github.com/leanprover-community/mathlib/pull/295))
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* closure_empty_iff

Modified data/set/basic.lean
- \+ *lemma* set.nonempty_iff_univ_ne_empty
- \+ *lemma* set.nonempty_of_nonempty_range



## [2018-08-29 02:26:04+02:00](https://github.com/leanprover-community/mathlib/commit/49fb2db)
fix(docs/style): precise a style rule and fixes a github markdown issue ([#290](https://github.com/leanprover-community/mathlib/pull/290))
#### Estimated changes
Modified docs/style.md




## [2018-08-29 00:28:03+02:00](https://github.com/leanprover-community/mathlib/commit/bab3813)
feat(ring_theory/PID): PIDs and xgcd for ED ([#298](https://github.com/leanprover-community/mathlib/pull/298))
#### Estimated changes
Modified algebra/euclidean_domain.lean
- \+ *def* euclidean_domain.gcd_a
- \+ *def* euclidean_domain.gcd_b
- \+ *theorem* euclidean_domain.gcd_eq_gcd_ab
- \+ *lemma* euclidean_domain.mod_eq_sub_mul_div
- \+ *def* euclidean_domain.xgcd
- \+ *def* euclidean_domain.xgcd_aux
- \+ *theorem* euclidean_domain.xgcd_aux_P
- \+ *theorem* euclidean_domain.xgcd_aux_fst
- \+ *theorem* euclidean_domain.xgcd_aux_rec
- \+ *theorem* euclidean_domain.xgcd_aux_val
- \+ *theorem* euclidean_domain.xgcd_val
- \+ *theorem* euclidean_domain.xgcd_zero_left

Modified algebra/ring.lean
- \+ *lemma* zero_dvd_iff

Added ring_theory/PID.lean
- \+ *lemma* is_prime_ideal.to_maximal_ideal
- \+ *lemma* is_principal_ideal.eq_trivial_iff_generator_eq_zero
- \+ *lemma* is_principal_ideal.generator_generates
- \+ *lemma* is_principal_ideal.generator_mem
- \+ *lemma* is_principal_ideal.mem_iff_generator_dvd
- \+ *lemma* mod_mem_iff

Modified ring_theory/ideals.lean
- \+ *lemma* is_ideal.mem_trivial
- \+/\- *theorem* is_maximal_ideal.mk
- \+/\- *lemma* is_proper_ideal_iff_one_not_mem
- \+/\- *lemma* quotient_ring.eq_zero_iff_mem



## [2018-08-28 20:10:13+02:00](https://github.com/leanprover-community/mathlib/commit/cd73115)
refactor(data/set/basic): clean up [#288](https://github.com/leanprover-community/mathlib/pull/288) and [#289](https://github.com/leanprover-community/mathlib/pull/289)
#### Estimated changes
Modified data/set/basic.lean
- \- *lemma* set.mem_prod'
- \+ *lemma* set.mk_mem_prod
- \+/\- *theorem* set.univ_prod_univ

Modified order/filter.lean
- \- *lemma* filter.inter_vmap_sets
- \+ *lemma* filter.sInter_vmap_sets
- \+/\- *lemma* filter.vmap_eq_of_inverse



## [2018-08-28 20:09:53+02:00](https://github.com/leanprover-community/mathlib/commit/8d3bd80)
feat(tactic/tidy): add tidy tactic ([#285](https://github.com/leanprover-community/mathlib/pull/285))
#### Estimated changes
Modified docs/tactics.md


Added tactic/auto_cases.lean


Modified tactic/basic.lean


Added tactic/chain.lean


Modified tactic/interactive.lean


Added tactic/tidy.lean


Modified tests/tactics.lean


Added tests/tidy.lean
- \+ *def* tidy.test.d
- \+ *def* tidy.test.f
- \+ *def* tidy.test.tidy_test_0
- \+ *def* tidy.test.tidy_test_1



## [2018-08-28 19:40:10+02:00](https://github.com/leanprover-community/mathlib/commit/9ad32e7)
feat(order/filter): More lemmas from perfectoid project ([#289](https://github.com/leanprover-community/mathlib/pull/289))
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* set.prod_sub_preimage_iff
- \- *lemma* set.sub_preimage_iff

Modified order/filter.lean
- \+ *lemma* filter.inter_vmap_sets
- \+ *lemma* filter.tendsto_prod_iff
- \+ *lemma* filter.tendsto_prod_self_iff
- \+ *lemma* filter.vmap_eq_of_inverse



## [2018-08-28 19:38:58+02:00](https://github.com/leanprover-community/mathlib/commit/3f65a93)
fix(tactic/restate_axiom): change default naming in restate_axiom ([#286](https://github.com/leanprover-community/mathlib/pull/286))
* beginning renaming
* modifying names in restate_axiom
* removing ematch attributes from category_theory
* improving behaviour of `restate_axiom`, documenting and testing
* oops
#### Estimated changes
Modified category_theory/category.lean


Modified category_theory/functor.lean
- \+ *lemma* category_theory.functor.map_comp
- \- *lemma* category_theory.functor.map_comp_lemma
- \+ *lemma* category_theory.functor.map_id
- \- *lemma* category_theory.functor.map_id_lemma

Modified category_theory/functor_category.lean
- \+/\- *lemma* category_theory.functor.category.comp_app
- \+/\- *lemma* category_theory.functor.category.id_app
- \+/\- *lemma* category_theory.functor.category.nat_trans.app_naturality
- \+/\- *lemma* category_theory.functor.category.nat_trans.naturality_app

Modified category_theory/natural_transformation.lean
- \+/\- *lemma* category_theory.nat_trans.exchange
- \+ *lemma* category_theory.nat_trans.naturality
- \- *lemma* category_theory.nat_trans.naturality_lemma
- \+/\- *lemma* category_theory.nat_trans.vcomp_assoc

Modified category_theory/opposites.lean


Modified category_theory/products.lean
- \+/\- *lemma* category_theory.functor.prod_map
- \+/\- *lemma* category_theory.functor.prod_obj
- \+/\- *lemma* category_theory.nat_trans.prod_app
- \+/\- *lemma* category_theory.prod_comp
- \+/\- *lemma* category_theory.prod_id

Modified category_theory/types.lean
- \+/\- *lemma* category_theory.functor_to_types.map_comp
- \+/\- *lemma* category_theory.functor_to_types.map_id
- \+/\- *lemma* category_theory.functor_to_types.naturality

Modified docs/tactics.md


Modified tactic/restate_axiom.lean


Added tests/restate_axiom.lean




## [2018-08-28 17:33:14+02:00](https://github.com/leanprover-community/mathlib/commit/ed5a338)
feat(data/set/basic): some more basic set lemmas ([#288](https://github.com/leanprover-community/mathlib/pull/288))
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* set.inter_singleton_ne_empty
- \+ *lemma* set.mem_prod'
- \+ *lemma* set.preimage_subset_iff
- \+ *lemma* set.sub_preimage_iff



## [2018-08-28 15:08:37+02:00](https://github.com/leanprover-community/mathlib/commit/39ffeab)
feat(analysis): add normed spaces
#### Estimated changes
Added analysis/normed_space.lean
- \+ *lemma* abs_norm_sub_norm_le
- \+ *lemma* coe_nnnorm
- \+ *lemma* continuous_norm
- \+ *lemma* dist_eq_norm
- \+ *lemma* dist_norm_norm_le
- \+ *lemma* dist_zero_right
- \+ *lemma* lim_norm
- \+ *lemma* lim_norm_zero
- \+ *lemma* nndist_eq_nnnorm
- \+ *lemma* nndist_nnnorm_nnnorm_le
- \+ *def* nnnorm
- \+ *lemma* nnnorm_eq_zero
- \+ *lemma* nnnorm_neg
- \+ *lemma* nnnorm_smul
- \+ *lemma* nnnorm_triangle
- \+ *lemma* nnnorm_zero
- \+ *lemma* norm_eq_zero
- \+ *lemma* norm_fst_le
- \+ *lemma* norm_le_zero_iff
- \+ *lemma* norm_mul
- \+ *lemma* norm_neg
- \+ *lemma* norm_nonneg
- \+ *lemma* norm_pos_iff
- \+ *lemma* norm_smul
- \+ *lemma* norm_snd_le
- \+ *lemma* norm_triangle
- \+ *lemma* norm_zero
- \+ *lemma* squeeze_zero
- \+ *lemma* tendsto_iff_norm_tendsto_zero
- \+ *lemma* tendsto_smul



## [2018-08-28 15:05:42+02:00](https://github.com/leanprover-community/mathlib/commit/2b9c9a8)
refactor(analysis): add nndist; add finite product of metric spaces; prepare for normed spaces
#### Estimated changes
Modified analysis/complex.lean


Modified analysis/ennreal.lean
- \- *lemma* topological_space.nhds_swap
- \- *lemma* topological_space.prod_mem_nhds_sets
- \- *lemma* topological_space.tendsto_nhds_generate_from
- \- *lemma* topological_space.tendsto_prod_mk_nhds

Modified analysis/metric_space.lean
- \+ *lemma* coe_dist
- \- *def* dist
- \+ *lemma* dist_pi_def
- \+ *theorem* eq_of_nndist_eq_zero
- \+ *def* nndist
- \+ *theorem* nndist_comm
- \+ *theorem* nndist_eq_zero
- \+ *lemma* nndist_self
- \+ *theorem* nndist_triangle
- \+ *theorem* nndist_triangle_left
- \+ *theorem* nndist_triangle_right
- \+ *theorem* zero_eq_nndist

Modified analysis/nnreal.lean


Modified analysis/topology/continuity.lean
- \+ *lemma* embedding.map_nhds_eq
- \+ *lemma* nhds_swap
- \+ *lemma* prod_mem_nhds_sets
- \+ *lemma* tendsto_prod_mk_nhds

Modified analysis/topology/topological_space.lean
- \+ *lemma* topological_space.tendsto_nhds_generate_from

Modified data/finset.lean
- \+ *lemma* finset.image_const
- \+/\- *lemma* finset.inf_insert
- \+/\- *lemma* finset.inf_singleton
- \+/\- *lemma* finset.inf_union
- \+ *lemma* finset.le_inf_iff
- \+ *theorem* finset.max_singleton'
- \+/\- *lemma* finset.sup_insert
- \+ *lemma* finset.sup_le_iff
- \+/\- *lemma* finset.sup_singleton
- \+/\- *lemma* finset.sup_union

Modified data/real/nnreal.lean
- \+ *lemma* nnreal.bot_eq_zero
- \+ *lemma* nnreal.mul_finset_sup
- \+ *lemma* nnreal.mul_sup



## [2018-08-28 15:05:42+02:00](https://github.com/leanprover-community/mathlib/commit/41f5674)
fix(algebra/pi_modules): pi instance for module shouldn't search for the ring structure
#### Estimated changes
Modified algebra/pi_instances.lean




## [2018-08-28 14:39:03+02:00](https://github.com/leanprover-community/mathlib/commit/5c221a3)
feat(order/conditionally_complete_lattic): nat is a conditionally complete linear order with bottom
#### Estimated changes
Modified algebra/ordered_ring.lean


Modified data/equiv/list.lean


Modified order/conditionally_complete_lattice.lean
- \+ *lemma* lattice.Inf_nat_def
- \+ *lemma* lattice.Sup_nat_def



## [2018-08-28 10:22:25+02:00](https://github.com/leanprover-community/mathlib/commit/de67f54)
feat(data/real): cauchy sequence limit lemmas ([#61](https://github.com/leanprover-community/mathlib/pull/61))
#### Estimated changes
Modified data/real/basic.lean
- \+ *lemma* real.eq_lim_of_const_equiv
- \+ *lemma* real.lim_add
- \+ *lemma* real.lim_const
- \+ *lemma* real.lim_eq_lim_of_equiv
- \+ *lemma* real.lim_eq_of_equiv_const
- \+ *lemma* real.lim_eq_zero_iff
- \+ *lemma* real.lim_inv
- \+ *lemma* real.lim_mul
- \+ *lemma* real.lim_mul_lim
- \+ *lemma* real.lim_neg

Modified data/real/cau_seq.lean
- \+ *theorem* cau_seq.const_inv



## [2018-08-28 00:08:50+02:00](https://github.com/leanprover-community/mathlib/commit/c420885)
fix(tactic/interactive): try reflexivity after substs ([#275](https://github.com/leanprover-community/mathlib/pull/275))
This brings `substs` closer to being equivalent to a sequence of `subst`.
#### Estimated changes
Modified tactic/interactive.lean




## [2018-08-28 00:06:47+02:00](https://github.com/leanprover-community/mathlib/commit/bca8d49)
chore(data/array, data/buffer): Array and buffer cleanup ([#277](https://github.com/leanprover-community/mathlib/pull/277))
#### Estimated changes
Modified data/array/lemmas.lean
- \+/\- *theorem* array.mem.def
- \+/\- *theorem* array.mem_rev_list
- \+ *theorem* array.mem_rev_list_aux
- \- *theorem* array.mem_rev_list_core
- \+/\- *theorem* array.mem_to_list
- \+/\- *theorem* array.mem_to_list_enum
- \+/\- *theorem* array.push_back_rev_list
- \+ *lemma* array.push_back_rev_list_aux
- \- *lemma* array.push_back_rev_list_core
- \+/\- *theorem* array.push_back_to_list
- \+/\- *theorem* array.read_foreach
- \+/\- *theorem* array.read_foreach_aux
- \+/\- *theorem* array.read_map
- \+/\- *theorem* array.read_map₂
- \+/\- *theorem* array.rev_list_foldr
- \+/\- *theorem* array.rev_list_foldr_aux
- \+/\- *theorem* array.rev_list_length_aux
- \+/\- *theorem* array.rev_list_reverse
- \+ *theorem* array.rev_list_reverse_aux
- \- *theorem* array.rev_list_reverse_core
- \+/\- *theorem* array.to_list_foldl
- \+/\- *theorem* array.to_list_nth
- \+/\- *theorem* array.to_list_nth_le'
- \+/\- *theorem* array.to_list_nth_le
- \+ *theorem* array.to_list_nth_le_aux
- \- *theorem* array.to_list_nth_le_core
- \+/\- *theorem* array.to_list_of_heq
- \+/\- *theorem* array.to_list_reverse
- \+/\- *theorem* array.write_to_list
- \+/\- *def* equiv.d_array_equiv_fin

Modified data/buffer/basic.lean
- \+/\- *lemma* buffer.ext
- \+/\- *lemma* buffer.to_list_append_list

Modified data/hash_map.lean




## [2018-08-27 23:02:59+02:00](https://github.com/leanprover-community/mathlib/commit/c52b317)
refactor(data/finsupp): generalise finsupp.to_module ([#284](https://github.com/leanprover-community/mathlib/pull/284))
#### Estimated changes
Modified data/finsupp.lean
- \+ *lemma* finsupp.smul_apply'
- \+/\- *lemma* finsupp.smul_apply
- \+ *def* finsupp.to_has_scalar'
- \+/\- *def* finsupp.to_has_scalar
- \+/\- *def* finsupp.to_module

Modified data/polynomial.lean


Modified linear_algebra/basic.lean


Modified linear_algebra/multivariate_polynomial.lean




## [2018-08-27 16:48:59+02:00](https://github.com/leanprover-community/mathlib/commit/9aa2bb0)
feat(data/fin): last ([#273](https://github.com/leanprover-community/mathlib/pull/273))
#### Estimated changes
Modified data/fin.lean
- \+ *def* fin.last
- \+ *theorem* fin.le_last



## [2018-08-27 16:48:29+02:00](https://github.com/leanprover-community/mathlib/commit/a3a9e24)
bug(tactic/interactive): make `solve_by_elim` fail on no goals ([#279](https://github.com/leanprover-community/mathlib/pull/279))
#### Estimated changes
Modified tactic/basic.lean


Modified tests/tactics.lean




## [2018-08-27 16:46:13+02:00](https://github.com/leanprover-community/mathlib/commit/c13a771)
feat(data/list): join_eq_nil, join_repeat_nil ([#274](https://github.com/leanprover-community/mathlib/pull/274))
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.join_eq_nil
- \+ *theorem* list.join_repeat_nil



## [2018-08-27 14:37:37+02:00](https://github.com/leanprover-community/mathlib/commit/92e9d64)
feat(category_theory): restating functor.map and nat_trans.app ([#268](https://github.com/leanprover-community/mathlib/pull/268))
#### Estimated changes
Modified category_theory/functor.lean
- \- *lemma* category_theory.functor.coe_def
- \+/\- *lemma* category_theory.functor.comp_map
- \+ *def* category_theory.functor.map
- \+ *lemma* category_theory.functor.map_comp_lemma
- \+ *lemma* category_theory.functor.map_id_lemma
- \+ *lemma* category_theory.functor.mk_map
- \+ *lemma* category_theory.functor.mk_obj

Modified category_theory/functor_category.lean
- \+/\- *lemma* category_theory.functor.category.comp_app
- \+/\- *lemma* category_theory.functor.category.nat_trans.app_naturality
- \+/\- *lemma* category_theory.functor.category.nat_trans.naturality_app

Modified category_theory/natural_transformation.lean
- \- *lemma* category_theory.nat_trans.coe_def
- \+/\- *lemma* category_theory.nat_trans.exchange
- \+/\- *lemma* category_theory.nat_trans.hcomp_app
- \+ *lemma* category_theory.nat_trans.mk_app
- \+ *lemma* category_theory.nat_trans.naturality_lemma
- \+/\- *lemma* category_theory.nat_trans.vcomp_assoc

Modified category_theory/opposites.lean


Modified category_theory/products.lean


Modified category_theory/types.lean




## [2018-08-27 14:18:50+02:00](https://github.com/leanprover-community/mathlib/commit/e955897)
fix(travis.yml): adding a third stage to the travis build ([#281](https://github.com/leanprover-community/mathlib/pull/281))
#### Estimated changes
Modified .travis.yml




## [2018-08-22 19:50:16+02:00](https://github.com/leanprover-community/mathlib/commit/58cfe9f)
bug(ext): failure on ext lemmas with no hypotheses ([#269](https://github.com/leanprover-community/mathlib/pull/269))
#### Estimated changes
Modified tactic/basic.lean


Modified tests/tactics.lean
- \+ *lemma* unit.ext



## [2018-08-22 19:48:06+02:00](https://github.com/leanprover-community/mathlib/commit/d18a3a8)
doc(docs/tactics): add information on congr' ([#270](https://github.com/leanprover-community/mathlib/pull/270)) [ci-skip]
#### Estimated changes
Modified docs/tactics.md




## [2018-08-22 19:46:57+02:00](https://github.com/leanprover-community/mathlib/commit/0934d7d)
refactor(data/nat/prime): mem_factors_iff_dvd ([#272](https://github.com/leanprover-community/mathlib/pull/272))
#### Estimated changes
Modified data/list/basic.lean
- \+ *lemma* list.dvd_prod

Modified data/nat/prime.lean
- \+ *lemma* nat.mem_factors_iff_dvd
- \- *lemma* nat.mem_factors_of_dvd



## [2018-08-22 19:37:12+02:00](https://github.com/leanprover-community/mathlib/commit/974987c)
refactor(data/nat/prime): cleanup exists_infinite_primes ([#271](https://github.com/leanprover-community/mathlib/pull/271))
* removing unnecessary initial step
* giving names to ambiguous copies of `this`
#### Estimated changes
Modified data/nat/prime.lean
- \+/\- *theorem* nat.exists_infinite_primes
- \+/\- *lemma* nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+/\- *lemma* nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul_int



## [2018-08-21 22:05:08+02:00](https://github.com/leanprover-community/mathlib/commit/b3fc801)
refactor(data/real/nnreal): derive order structure for ennreal from with_top nnreal
#### Estimated changes
Modified algebra/ordered_group.lean
- \+ *lemma* le_add_left
- \+ *lemma* le_add_right
- \- *lemma* with_bot.bot_lt_some
- \- *lemma* with_bot.coe_lt_coe
- \+ *lemma* with_top.add_eq_top
- \+ *lemma* with_top.add_lt_add_iff_left
- \- *theorem* with_top.coe_ne_top
- \- *theorem* with_top.top_ne_coe
- \+ *lemma* with_top.zero_lt_coe
- \+ *lemma* with_top.zero_lt_top

Modified algebra/ordered_ring.lean
- \+/\- *lemma* mul_le_one
- \- *lemma* option.bind_comm
- \+ *lemma* with_top.coe_mul
- \- *lemma* with_top.coe_mul_coe
- \- *lemma* with_top.none_eq_top
- \- *lemma* with_top.some_eq_coe
- \+ *lemma* with_top.top_mul_top

Modified analysis/ennreal.lean
- \- *lemma* ennreal.Inf_add
- \- *lemma* ennreal.add_infi
- \- *lemma* ennreal.coe_eq_coe
- \+ *lemma* ennreal.coe_image_univ_mem_nhds
- \- *lemma* ennreal.coe_mul
- \+ *lemma* ennreal.coe_nat
- \- *lemma* ennreal.coe_one
- \+ *lemma* ennreal.continuous_coe
- \- *lemma* ennreal.continuous_of_real
- \+ *lemma* ennreal.embedding_coe
- \- *theorem* ennreal.exists_pos_sum_of_encodable
- \- *lemma* ennreal.infi_add
- \- *lemma* ennreal.infi_add_infi
- \- *lemma* ennreal.infi_of_real
- \- *lemma* ennreal.infi_sum
- \+ *lemma* ennreal.is_open_ne_top
- \+ *lemma* ennreal.nhds_coe
- \+ *lemma* ennreal.nhds_coe_coe
- \- *lemma* ennreal.nhds_of_real_eq_map_of_real_nhds
- \- *lemma* ennreal.nhds_of_real_eq_map_of_real_nhds_nonneg
- \- *lemma* ennreal.sub_infi
- \+/\- *lemma* ennreal.sub_supr
- \- *lemma* ennreal.supr_of_real
- \+ *lemma* ennreal.tendsto_coe
- \- *lemma* ennreal.tendsto_coe_iff
- \+ *lemma* ennreal.tendsto_nhds_top
- \- *lemma* ennreal.tendsto_of_ennreal
- \- *lemma* ennreal.tendsto_of_real
- \- *lemma* ennreal.tendsto_of_real_iff
- \+ *lemma* ennreal.tendsto_to_nnreal
- \+/\- *lemma* has_sum_of_nonneg_of_le
- \+ *lemma* nnreal.exists_le_is_sum_of_le
- \+/\- *lemma* nnreal.has_sum_of_le
- \+ *lemma* topological_space.nhds_swap
- \+ *lemma* topological_space.prod_mem_nhds_sets
- \+ *lemma* topological_space.tendsto_nhds_generate_from
- \+ *lemma* topological_space.tendsto_prod_mk_nhds

Modified analysis/limits.lean
- \+ *theorem* ennreal.exists_pos_sum_of_encodable
- \+ *theorem* nnreal.exists_pos_sum_of_encodable

Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/nnreal.lean
- \+ *lemma* nnreal.continuous_coe
- \+ *lemma* nnreal.continuous_of_real
- \+ *lemma* nnreal.tendsto_of_real
- \+ *lemma* nnreal.tendsto_sub
- \+ *lemma* nnreal.tsum_coe

Modified analysis/probability_mass_function.lean


Modified analysis/topology/continuity.lean
- \+/\- *lemma* embedding.tendsto_nhds_iff

Modified data/option.lean
- \+ *lemma* option.bind_comm

Modified data/real/basic.lean
- \+ *theorem* real.Inf_empty
- \+ *theorem* real.Inf_of_not_bdd_below
- \+ *theorem* real.Sup_empty
- \+ *theorem* real.Sup_of_not_bdd_above
- \+/\- *def* real.of_rat

Modified data/real/ennreal.lean
- \+ *lemma* ennreal.Inf_add
- \+ *lemma* ennreal.add_eq_top
- \+ *lemma* ennreal.add_infi
- \- *lemma* ennreal.add_infty
- \+ *lemma* ennreal.add_lt_add_iff_left
- \+/\- *lemma* ennreal.add_sub_self
- \+ *lemma* ennreal.add_top
- \+ *lemma* ennreal.bot_eq_zero
- \+ *lemma* ennreal.coe_Inf
- \+ *lemma* ennreal.coe_Sup
- \+ *lemma* ennreal.coe_add
- \+ *lemma* ennreal.coe_eq_coe
- \+ *lemma* ennreal.coe_eq_one
- \+ *lemma* ennreal.coe_eq_zero
- \+ *lemma* ennreal.coe_finset_prod
- \+ *lemma* ennreal.coe_finset_sum
- \+ *lemma* ennreal.coe_le_coe
- \+ *lemma* ennreal.coe_le_iff
- \+ *lemma* ennreal.coe_le_one_iff
- \+ *lemma* ennreal.coe_lt_coe
- \+ *lemma* ennreal.coe_lt_one_iff
- \+ *lemma* ennreal.coe_lt_top
- \+ *lemma* ennreal.coe_mem_upper_bounds
- \+ *lemma* ennreal.coe_mul
- \+ *lemma* ennreal.coe_ne_top
- \+ *lemma* ennreal.coe_one
- \+ *lemma* ennreal.coe_sub
- \+ *lemma* ennreal.coe_to_nnreal
- \+ *lemma* ennreal.coe_zero
- \+ *lemma* ennreal.div_def
- \+ *lemma* ennreal.div_le_iff_le_mul
- \+/\- *lemma* ennreal.forall_ennreal
- \+ *lemma* ennreal.infi_add
- \+ *lemma* ennreal.infi_add_infi
- \+ *lemma* ennreal.infi_sum
- \- *lemma* ennreal.infty_add
- \- *lemma* ennreal.infty_le_iff
- \- *lemma* ennreal.infty_mem_upper_bounds
- \- *lemma* ennreal.infty_mul
- \- *lemma* ennreal.infty_mul_of_real
- \- *lemma* ennreal.infty_ne_of_real
- \- *lemma* ennreal.infty_ne_zero
- \- *lemma* ennreal.infty_sub_of_real
- \+ *lemma* ennreal.inv_coe
- \+ *lemma* ennreal.inv_eq_top
- \+ *lemma* ennreal.inv_eq_zero
- \- *lemma* ennreal.inv_infty
- \+/\- *lemma* ennreal.inv_inv
- \+ *lemma* ennreal.inv_le_iff_le_mul
- \+ *lemma* ennreal.inv_ne_top
- \+ *lemma* ennreal.inv_ne_zero
- \- *lemma* ennreal.inv_of_real
- \+ *lemma* ennreal.inv_top
- \- *lemma* ennreal.is_lub_of_real
- \- *lemma* ennreal.le_add_left
- \- *lemma* ennreal.le_add_right
- \+ *lemma* ennreal.le_coe_iff
- \- *theorem* ennreal.le_def
- \+ *lemma* ennreal.le_div_iff_mul_le
- \- *lemma* ennreal.le_infty
- \+ *lemma* ennreal.le_inv_iff_mul_le
- \+/\- *lemma* ennreal.le_of_forall_epsilon_le
- \- *lemma* ennreal.le_of_real_iff
- \- *lemma* ennreal.le_zero_iff_eq
- \+/\- *lemma* ennreal.lt_add_right
- \+ *lemma* ennreal.lt_iff_exists_coe
- \- *lemma* ennreal.lt_iff_exists_of_real
- \+ *lemma* ennreal.mul_eq_mul_left
- \- *lemma* ennreal.mul_infty
- \- *lemma* ennreal.mul_le_mul
- \+ *lemma* ennreal.mul_le_mul_left
- \+ *lemma* ennreal.mul_top
- \+ *lemma* ennreal.none_eq_top
- \- *lemma* ennreal.not_infty_lt
- \+/\- *lemma* ennreal.not_lt_zero
- \+ *lemma* ennreal.not_top_le_coe
- \- *def* ennreal.of_ennreal
- \- *lemma* ennreal.of_ennreal_of_real
- \- *lemma* ennreal.of_nonneg_real_eq_of_real
- \- *def* ennreal.of_real
- \- *lemma* ennreal.of_real_add
- \- *lemma* ennreal.of_real_add_le
- \- *lemma* ennreal.of_real_eq_of_real_of
- \- *lemma* ennreal.of_real_eq_one_iff
- \- *lemma* ennreal.of_real_eq_zero_iff
- \- *lemma* ennreal.of_real_le_of_real
- \- *lemma* ennreal.of_real_le_of_real_iff
- \- *lemma* ennreal.of_real_lt_infty
- \- *lemma* ennreal.of_real_lt_of_real_iff
- \- *lemma* ennreal.of_real_lt_of_real_iff_cases
- \- *lemma* ennreal.of_real_mem_upper_bounds
- \- *lemma* ennreal.of_real_mul_infty
- \- *lemma* ennreal.of_real_mul_of_real
- \- *lemma* ennreal.of_real_ne_infty
- \- *lemma* ennreal.of_real_ne_of_real_of
- \- *lemma* ennreal.of_real_of_ennreal
- \- *lemma* ennreal.of_real_of_nonpos
- \- *lemma* ennreal.of_real_of_not_nonneg
- \- *lemma* ennreal.of_real_one
- \- *lemma* ennreal.of_real_sub_of_real
- \- *lemma* ennreal.of_real_zero
- \+ *lemma* ennreal.one_eq_coe
- \- *lemma* ennreal.one_eq_of_real_iff
- \+ *lemma* ennreal.one_le_coe_iff
- \- *lemma* ennreal.one_le_of_real_iff
- \+ *lemma* ennreal.one_lt_zero_iff
- \+ *lemma* ennreal.one_ne_top
- \+ *lemma* ennreal.some_eq_coe
- \+/\- *lemma* ennreal.sub_add_cancel_of_le
- \+ *lemma* ennreal.sub_infi
- \- *lemma* ennreal.sum_of_real
- \+ *lemma* ennreal.supr_sub
- \+ *lemma* ennreal.to_nnreal_coe
- \+ *lemma* ennreal.top_add
- \+ *lemma* ennreal.top_mem_upper_bounds
- \+ *lemma* ennreal.top_mul
- \+ *lemma* ennreal.top_mul_top
- \+ *lemma* ennreal.top_ne_coe
- \+ *lemma* ennreal.top_ne_one
- \+ *lemma* ennreal.top_ne_zero
- \+ *lemma* ennreal.top_sub_coe
- \+ *lemma* ennreal.top_to_nnreal
- \+ *lemma* ennreal.zero_eq_coe
- \- *lemma* ennreal.zero_eq_of_real_iff
- \- *lemma* ennreal.zero_le_of_ennreal
- \+ *lemma* ennreal.zero_lt_coe_iff
- \- *lemma* ennreal.zero_lt_of_real_iff
- \- *lemma* ennreal.zero_ne_infty
- \+ *lemma* ennreal.zero_ne_top

Modified data/real/nnreal.lean
- \+ *lemma* inv_eq_zero
- \+ *lemma* nnreal.add_sub_cancel'
- \+ *lemma* nnreal.add_sub_cancel
- \+ *lemma* nnreal.bdd_above_coe
- \+ *lemma* nnreal.bdd_below_coe
- \+ *lemma* nnreal.coe_Inf
- \+ *lemma* nnreal.coe_Sup
- \+ *lemma* nnreal.coe_of_real
- \+ *lemma* nnreal.div_def
- \+ *lemma* nnreal.inv_eq_zero
- \+ *lemma* nnreal.inv_inv
- \+ *lemma* nnreal.inv_le
- \+ *lemma* nnreal.inv_le_of_le_mul
- \+ *lemma* nnreal.inv_mul_cancel
- \+ *lemma* nnreal.inv_pos
- \+ *lemma* nnreal.inv_zero
- \+ *lemma* nnreal.le_inv_iff_mul_le
- \+ *lemma* nnreal.le_of_forall_epsilon_le
- \+ *lemma* nnreal.lt_iff_exists_rat_btwn
- \+ *lemma* nnreal.mul_eq_mul_left
- \+ *lemma* nnreal.mul_inv_cancel
- \+ *lemma* nnreal.of_real_add_le
- \+ *lemma* nnreal.of_real_add_of_real
- \+ *lemma* nnreal.of_real_coe
- \+ *lemma* nnreal.of_real_le_of_real
- \+ *lemma* nnreal.of_real_le_of_real_iff
- \+ *lemma* nnreal.of_real_of_nonpos
- \+ *lemma* nnreal.of_real_zero
- \+ *lemma* nnreal.prod_coe
- \+ *lemma* nnreal.smul_coe
- \+ *lemma* nnreal.sub_add_cancel_of_le
- \+ *lemma* nnreal.sub_eq_zero
- \+ *lemma* nnreal.sub_le_iff_le_add
- \+/\- *lemma* nnreal.sum_coe
- \+ *lemma* nnreal.zero_le_coe
- \+ *lemma* nnreal.zero_lt_of_real
- \+ *lemma* set.image_eq_empty

Modified order/bounded_lattice.lean
- \+ *lemma* with_bot.bot_lt_coe
- \+ *lemma* with_bot.bot_lt_some
- \+ *theorem* with_bot.coe_eq_coe
- \+ *lemma* with_bot.coe_lt_coe
- \+ *lemma* with_bot.none_eq_bot
- \+ *lemma* with_bot.some_eq_coe
- \+ *theorem* with_top.coe_eq_coe
- \+ *theorem* with_top.coe_le_iff
- \+ *lemma* with_top.coe_lt_coe
- \+ *lemma* with_top.coe_lt_top
- \+ *theorem* with_top.coe_ne_top
- \+ *theorem* with_top.le_coe_iff
- \+ *theorem* with_top.lt_iff_exists_coe
- \+ *lemma* with_top.none_eq_top
- \+ *lemma* with_top.not_top_le_coe
- \+ *lemma* with_top.some_eq_coe
- \+ *theorem* with_top.top_ne_coe

Modified order/conditionally_complete_lattice.lean
- \- *lemma* bdd_above_bot
- \+ *lemma* bdd_below_bot
- \+ *lemma* lattice.cSup_empty
- \+ *lemma* with_top.coe_Inf
- \+ *lemma* with_top.coe_Sup
- \+ *lemma* with_top.has_glb
- \+ *lemma* with_top.has_lub
- \+ *lemma* with_top.is_glb_Inf
- \+ *lemma* with_top.is_lub_Sup

Modified order/filter.lean
- \+ *lemma* filter.tendsto_map'_iff

Modified order/galois_connection.lean




## [2018-08-21 21:22:03+02:00](https://github.com/leanprover-community/mathlib/commit/82512ee)
refactor(analysis/ennreal): use canonically_ordered_comm_semiring (with_top α)
#### Estimated changes
Modified algebra/ordered_group.lean
- \+ *lemma* with_top.add_top
- \+ *lemma* with_top.coe_add
- \+ *theorem* with_top.coe_ne_top
- \+ *lemma* with_top.top_add
- \+ *theorem* with_top.top_ne_coe

Modified algebra/ordered_ring.lean
- \+ *lemma* canonically_ordered_semiring.mul_le_mul
- \+ *lemma* option.bind_comm
- \+ *theorem* with_top.coe_eq_zero
- \+ *lemma* with_top.coe_mul_coe
- \+ *theorem* with_top.coe_zero
- \+ *lemma* with_top.mul_coe
- \+ *lemma* with_top.mul_def
- \+ *lemma* with_top.mul_top
- \+ *lemma* with_top.none_eq_top
- \+ *lemma* with_top.some_eq_coe
- \+ *lemma* with_top.top_mul
- \+ *theorem* with_top.top_ne_zero
- \+ *theorem* with_top.zero_eq_coe
- \+ *theorem* with_top.zero_ne_top

Modified data/real/ennreal.lean
- \+/\- *lemma* ennreal.infty_ne_of_real
- \+/\- *lemma* ennreal.infty_ne_zero
- \+/\- *lemma* ennreal.of_real_ne_infty
- \+/\- *lemma* ennreal.zero_ne_infty
- \+ *def* ennreal

Modified data/real/nnreal.lean




## [2018-08-21 21:22:03+02:00](https://github.com/leanprover-community/mathlib/commit/6f31637)
refactor(analysis/nnreal): split up into data.real and analysis part
#### Estimated changes
Modified analysis/nnreal.lean
- \- *lemma* nnreal.sum_coe
- \- *def* nnreal

Added data/real/nnreal.lean
- \+ *lemma* nnreal.sum_coe
- \+ *def* nnreal



## [2018-08-21 21:22:03+02:00](https://github.com/leanprover-community/mathlib/commit/ca1b2d1)
refactor(analysis/measure_theory/measurable_space): derive complete lattice structure from Galois insertion
#### Estimated changes
Modified analysis/measure_theory/measurable_space.lean
- \+ *lemma* measurable_space.generate_from_le_iff
- \+ *def* measurable_space.gi_generate_from
- \+ *lemma* measurable_space.is_measurable_bot_iff
- \+ *theorem* measurable_space.is_measurable_top
- \+ *lemma* measurable_space.mk_of_closure_sets

Modified analysis/measure_theory/measure_space.lean


Modified analysis/topology/continuity.lean




## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/29ad1c8)
feat(order/complete_lattice): add rewrite rules for Inf/Sup/infi/supr for pi and Prop
#### Estimated changes
Modified order/complete_lattice.lean
- \+ *lemma* lattice.Inf_Prop_eq
- \+ *lemma* lattice.Inf_apply
- \+ *lemma* lattice.Sup_Prop_eq
- \+ *lemma* lattice.Sup_apply
- \+ *lemma* lattice.infi_Prop_eq
- \+ *lemma* lattice.infi_apply
- \+ *lemma* lattice.supr_Prop_eq
- \+ *lemma* lattice.supr_apply



## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/202ac15)
refactor(analysis/topology/topological_space): simplify proof of nhds_supr using Galois connection
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* gc_nhds
- \+ *lemma* nhds_Sup
- \+ *lemma* nhds_bot
- \+/\- *lemma* nhds_mono
- \+/\- *lemma* nhds_supr
- \+ *lemma* pure_le_nhds
- \- *lemma* return_le_nhds
- \- *lemma* sup_eq_generate_from
- \- *lemma* supr_eq_generate_from

Modified analysis/topology/uniform_space.lean




## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/6cab92e)
refactor(analysis/topology/topological_space): derive complete lattice structure from Galois insertion
#### Estimated changes
Modified analysis/topology/continuity.lean
- \- *lemma* coinduced_compose
- \- *lemma* coinduced_id
- \- *lemma* induced_compose
- \- *lemma* induced_id

Modified analysis/topology/topological_space.lean
- \+ *lemma* coinduced_compose
- \+ *lemma* coinduced_id
- \+ *lemma* generate_from_le_iff_subset_is_open
- \+ *def* gi_generate_from
- \+ *lemma* induced_compose
- \+ *lemma* induced_id
- \+ *lemma* is_open_fold
- \+ *lemma* is_open_top
- \+ *lemma* mk_of_closure_sets

Modified analysis/topology/uniform_space.lean


Modified order/galois_connection.lean
- \+ *lemma* galois_insertion.l_u_eq



## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/f9434fa)
refactor(order/filter): derive complete lattice structure from Galois insertion
#### Estimated changes
Modified analysis/topology/uniform_space.lean


Modified order/filter.lean
- \+ *lemma* filter.Sup_sets_eq
- \+ *lemma* filter.bot_sets_eq
- \+ *def* filter.generate
- \+ *lemma* filter.generate_Union
- \+ *lemma* filter.generate_empty
- \+ *lemma* filter.generate_union
- \+ *lemma* filter.generate_univ
- \+ *def* filter.gi_generate
- \+/\- *lemma* filter.mem_Sup_sets
- \+/\- *lemma* filter.mem_supr_sets
- \+ *lemma* filter.mem_top_sets
- \- *lemma* filter.mem_top_sets_iff
- \+ *lemma* filter.mem_top_sets_iff_forall
- \+ *lemma* filter.mk_of_closure_sets
- \+/\- *lemma* filter.principal_empty
- \+/\- *lemma* filter.principal_univ
- \+ *lemma* filter.sets_iff_generate
- \+ *lemma* filter.sup_sets_eq
- \+ *def* lattice.complete_lattice.copy



## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/a423cc7)
refactor(order/filter): simplify filter structure
#### Estimated changes
Modified analysis/ennreal.lean


Modified analysis/real.lean


Modified analysis/topology/continuity.lean


Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean


Modified data/analysis/filter.lean


Modified order/filter.lean
- \- *lemma* filter.filter.ext
- \+/\- *lemma* filter.inter_mem_sets
- \+ *lemma* filter.mem_sets_of_superset

Modified order/liminf_limsup.lean




## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/849ed4f)
feat(order/galois_connection): add Galois insertion and lattice lifts along a Galois insertion
#### Estimated changes
Modified analysis/measure_theory/measurable_space.lean
- \+/\- *lemma* measurable_space.comap_map_le
- \+/\- *lemma* measurable_space.le_map_comap

Modified order/filter.lean
- \+/\- *lemma* filter.le_vmap_map
- \+/\- *lemma* filter.map_vmap_le

Modified order/galois_connection.lean
- \- *lemma* galois_connection.decreasing_l_u
- \- *lemma* galois_connection.increasing_u_l
- \+ *lemma* galois_connection.l_Sup
- \+ *lemma* galois_connection.l_u_le
- \+ *lemma* galois_connection.le_u_l
- \+ *def* galois_connection.lift_order_bot
- \+ *lemma* galois_connection.u_Inf
- \+ *def* galois_insertion.lift_bounded_lattice
- \+ *def* galois_insertion.lift_complete_lattice
- \+ *def* galois_insertion.lift_lattice
- \+ *def* galois_insertion.lift_order_top
- \+ *def* galois_insertion.lift_semilattice_inf
- \+ *def* galois_insertion.lift_semilattice_sup



## [2018-08-18 01:02:27-04:00](https://github.com/leanprover-community/mathlib/commit/0ff11df)
refactor(group_theory/order_of_element): use gpowers instead of range ([#265](https://github.com/leanprover-community/mathlib/pull/265))
#### Estimated changes
Modified group_theory/order_of_element.lean
- \+/\- *lemma* exists_pow_eq_one
- \+ *lemma* mem_gpowers_iff_mem_range_order_of
- \- *lemma* mem_range_gpow_iff_mem_range_order_of
- \+ *lemma* order_eq_card_gpowers
- \- *lemma* order_eq_card_range_gpow
- \- *lemma* order_of_ne_zero
- \+ *lemma* order_of_pos



## [2018-08-18 01:00:59-04:00](https://github.com/leanprover-community/mathlib/commit/29508f2)
doc(tactic/solve_by_elim): update doc ([#266](https://github.com/leanprover-community/mathlib/pull/266)) [ci-skip]
#### Estimated changes
Modified docs/tactics.md


Modified tactic/interactive.lean




## [2018-08-18 01:00:24-04:00](https://github.com/leanprover-community/mathlib/commit/157004c)
feat(data/list/basic): some more theorems about sublist ([#264](https://github.com/leanprover-community/mathlib/pull/264))
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.erase_diff_erase_sublist_of_sublist

Modified data/list/perm.lean
- \+ *theorem* list.erase_subperm
- \+ *theorem* list.erase_subperm_erase



## [2018-08-18 00:57:52-04:00](https://github.com/leanprover-community/mathlib/commit/dfc9f8e)
chore(build): prune deleted .lean files and their .olean files
#### Estimated changes
Modified .travis.yml




## [2018-08-18 00:55:17-04:00](https://github.com/leanprover-community/mathlib/commit/cfb27cb)
feat(category_theory): opposites, and the category of types ([#249](https://github.com/leanprover-community/mathlib/pull/249))
#### Estimated changes
Modified category_theory/category.lean


Modified category_theory/functor.lean


Modified category_theory/functor_category.lean


Modified category_theory/natural_transformation.lean


Added category_theory/opposites.lean
- \+ *lemma* category_theory.functor.hom_obj
- \+ *lemma* category_theory.functor.hom_pairing_map
- \+ *lemma* category_theory.functor.opposite_map
- \+ *lemma* category_theory.functor.opposite_obj
- \+ *def* category_theory.op

Modified category_theory/products.lean
- \+/\- *lemma* category_theory.functor.prod_map
- \+/\- *lemma* category_theory.functor.prod_obj
- \+/\- *lemma* category_theory.nat_trans.prod_app

Added category_theory/types.lean
- \+ *lemma* category_theory.functor_to_types.hcomp
- \+ *lemma* category_theory.functor_to_types.map_comp
- \+ *lemma* category_theory.functor_to_types.map_id
- \+ *lemma* category_theory.functor_to_types.naturality
- \+ *lemma* category_theory.functor_to_types.vcomp
- \+ *lemma* category_theory.types_comp
- \+ *lemma* category_theory.types_hom
- \+ *lemma* category_theory.types_id

Modified tactic/ext.lean
- \+ *lemma* ulift.ext



## [2018-08-16 11:32:39-04:00](https://github.com/leanprover-community/mathlib/commit/12d103c)
fix(padics/padic_norm): remove spurious import
#### Estimated changes
Modified data/padics/padic_norm.lean
- \+/\- *lemma* padic_norm.add_eq_max_of_ne
- \+/\- *lemma* padic_val.is_greatest
- \+/\- *lemma* padic_val.le_padic_val_of_pow_div
- \+/\- *lemma* padic_val.min_le_padic_val_add
- \+/\- *lemma* padic_val.spec
- \+/\- *lemma* padic_val.unique
- \+/\- *def* padic_val



## [2018-08-16 11:31:57-04:00](https://github.com/leanprover-community/mathlib/commit/1bca59b)
refactor(tactic/basic): simplify definition
#### Estimated changes
Modified tactic/basic.lean




## [2018-08-16 11:23:04-04:00](https://github.com/leanprover-community/mathlib/commit/93817f1)
feat(data/padics): p-adic numbers ([#262](https://github.com/leanprover-community/mathlib/pull/262))
#### Estimated changes
Modified algebra/archimedean.lean
- \+ *lemma* ceil_nonneg
- \+ *lemma* ceil_pos

Added algebra/field_power.lean
- \+ *def* fpow
- \+ *lemma* fpow_add
- \+ *lemma* fpow_eq_gpow
- \+ *lemma* fpow_inv
- \+ *lemma* fpow_le_of_le
- \+ *lemma* fpow_ne_zero_of_ne_zero
- \+ *lemma* fpow_nonneg_of_nonneg
- \+ *lemma* fpow_zero
- \+ *lemma* pow_le_max_of_min_le
- \+ *lemma* unit_pow
- \+ *lemma* zero_fpow
- \+ *lemma* zero_gpow

Modified algebra/order_functions.lean
- \+ *lemma* le_of_max_le_left
- \+ *lemma* le_of_max_le_right
- \+ *lemma* max_le_add_of_nonneg
- \+ *lemma* min_add
- \+ *lemma* min_le_add_of_nonneg_left
- \+ *lemma* min_le_add_of_nonneg_right
- \+ *lemma* min_sub

Modified algebra/ordered_field.lean
- \+ *lemma* inv_le_one

Modified algebra/ordered_ring.lean
- \+ *lemma* mul_le_one

Modified data/int/basic.lean
- \+ *lemma* int.dvd_nat_abs_of_of_nat_dvd
- \+ *theorem* int.eq_mul_div_of_mul_eq_mul_of_dvd_left
- \+ *lemma* int.nat_abs_ne_zero_of_ne_zero
- \+ *lemma* int.of_nat_dvd_of_dvd_nat_abs
- \+ *lemma* int.pow_div_of_le_of_pow_div_int

Modified data/nat/basic.lean
- \+ *lemma* nat.dvd_div_of_mul_dvd
- \+ *lemma* nat.lt_pow_self
- \+ *lemma* nat.mul_dvd_of_dvd_div
- \+ *lemma* nat.nat.div_mul_div
- \+ *lemma* nat.nat.find_greatest_is_greatest
- \+ *lemma* nat.nat.find_greatest_spec
- \+ *lemma* nat.not_pos_pow_dvd
- \+ *lemma* nat.one_pow
- \+ *lemma* nat.pow_div_of_le_of_pow_div
- \+ *lemma* nat.pow_eq_mul_pow_sub
- \+ *lemma* nat.pow_lt_pow_succ
- \+ *theorem* nat.pow_pos

Modified data/nat/prime.lean
- \+ *lemma* nat.prime.ne_zero
- \+ *lemma* nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+ *lemma* nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul_int

Added data/padics/padic_integers.lean
- \+ *def* padic_int.add
- \+ *def* padic_int.mul
- \+ *def* padic_int.neg
- \+ *def* padic_int

Added data/padics/padic_norm.lean
- \+ *lemma* padic_norm.add_eq_max_of_ne
- \+ *theorem* padic_norm.triangle_ineq
- \+ *lemma* padic_norm.zero_of_padic_norm_eq_zero
- \+ *def* padic_norm
- \+ *lemma* padic_val.is_greatest
- \+ *lemma* padic_val.le_padic_val_of_pow_div
- \+ *lemma* padic_val.min_le_padic_val_add
- \+ *lemma* padic_val.padic_val_self
- \+ *lemma* padic_val.spec
- \+ *lemma* padic_val.unique
- \+ *def* padic_val
- \+ *theorem* padic_val_rat.min_le_padic_val_rat_add
- \+ *lemma* padic_val_rat.padic_val_rat_self
- \+ *def* padic_val_rat

Added data/padics/padic_rationals.lean
- \+ *lemma* padic.cast_eq_of_rat
- \+ *lemma* padic.cast_eq_of_rat_of_int
- \+ *lemma* padic.cast_eq_of_rat_of_nat
- \+ *theorem* padic.complete
- \+ *lemma* padic.const_equiv
- \+ *lemma* padic.exi_rat_seq_conv
- \+ *lemma* padic.exi_rat_seq_conv_cauchy
- \+ *def* padic.lim_seq
- \+ *def* padic.mk
- \+ *lemma* padic.mk_eq
- \+ *def* padic.of_rat
- \+ *lemma* padic.of_rat_add
- \+ *lemma* padic.of_rat_div
- \+ *lemma* padic.of_rat_eq
- \+ *lemma* padic.of_rat_mul
- \+ *lemma* padic.of_rat_neg
- \+ *lemma* padic.of_rat_one
- \+ *lemma* padic.of_rat_sub
- \+ *lemma* padic.of_rat_zero
- \+ *theorem* padic.rat_dense
- \+ *def* padic
- \+ *lemma* padic_norm_e.defn
- \+ *lemma* padic_norm_e.eq_padic_norm
- \+ *theorem* padic_norm_e.nonarchimedean
- \+ *lemma* padic_norm_e.sub_rev
- \+ *lemma* padic_norm_e.zero_def
- \+ *lemma* padic_norm_e.zero_iff
- \+ *def* padic_norm_e
- \+ *lemma* padic_seq.eq_zero_iff_equiv_zero
- \+ *lemma* padic_seq.equiv_zero_of_val_eq_of_equiv_zero
- \+ *lemma* padic_seq.ne_zero_iff_nequiv_zero
- \+ *def* padic_seq.norm
- \+ *lemma* padic_seq.norm_const
- \+ *lemma* padic_seq.norm_eq
- \+ *lemma* padic_seq.norm_eq_norm_app_of_nonzero
- \+ *theorem* padic_seq.norm_equiv
- \+ *lemma* padic_seq.norm_image
- \+ *lemma* padic_seq.norm_mul
- \+ *lemma* padic_seq.norm_neg
- \+ *theorem* padic_seq.norm_nonarchimedean
- \+ *lemma* padic_seq.norm_nonneg
- \+ *lemma* padic_seq.norm_nonzero_of_not_equiv_zero
- \+ *lemma* padic_seq.norm_one
- \+ *lemma* padic_seq.norm_zero_iff
- \+ *lemma* padic_seq.not_equiv_zero_const_of_nonzero
- \+ *lemma* padic_seq.not_lim_zero_const_of_nonzero
- \+ *lemma* padic_seq.stationary
- \+ *def* padic_seq.stationary_point
- \+ *lemma* padic_seq.stationary_point_spec
- \+ *def* padic_seq

Modified data/rat.lean
- \+ *lemma* rat.denom_ne_zero
- \+ *lemma* rat.denom_neg_eq_denom
- \+ *lemma* rat.mk_denom_ne_zero_of_ne_zero
- \+ *lemma* rat.mk_ne_zero_of_ne_zero
- \+ *lemma* rat.mk_num_ne_zero_of_ne_zero
- \+ *lemma* rat.mul_num_denom
- \+ *lemma* rat.num_denom_mk
- \+/\- *theorem* rat.num_dvd
- \+ *lemma* rat.num_ne_zero_of_ne_zero
- \+ *lemma* rat.num_neg_eq_neg_num
- \+ *lemma* rat.num_zero
- \+ *lemma* rat.zero_of_num_zero

Modified data/real/basic.lean
- \- *theorem* real.inv_mk
- \- *theorem* real.inv_zero
- \- *def* real.mk
- \- *theorem* real.mk_add
- \- *theorem* real.mk_eq
- \- *theorem* real.mk_eq_mk
- \- *theorem* real.mk_eq_zero
- \- *theorem* real.mk_mul
- \- *theorem* real.mk_neg
- \+/\- *def* real.of_rat
- \- *theorem* real.of_rat_add
- \- *theorem* real.of_rat_mul
- \- *theorem* real.of_rat_neg
- \- *theorem* real.of_rat_one
- \- *theorem* real.of_rat_zero
- \+/\- *def* real

Modified data/real/cau_seq.lean
- \+ *lemma* cau_seq.mul_equiv_zero'
- \+ *lemma* cau_seq.mul_equiv_zero
- \+ *lemma* cau_seq.mul_not_equiv_zero
- \+ *lemma* cau_seq.not_lim_zero_of_not_congr_zero
- \+ *lemma* cau_seq.one_not_equiv_zero

Added data/real/cau_seq_completion.lean
- \+ *def* cau_seq.completion.Cauchy
- \+ *lemma* cau_seq.completion.cau_seq_zero_ne_one
- \+ *theorem* cau_seq.completion.inv_mk
- \+ *theorem* cau_seq.completion.inv_zero
- \+ *def* cau_seq.completion.mk
- \+ *theorem* cau_seq.completion.mk_add
- \+ *theorem* cau_seq.completion.mk_eq
- \+ *theorem* cau_seq.completion.mk_eq_mk
- \+ *theorem* cau_seq.completion.mk_eq_zero
- \+ *theorem* cau_seq.completion.mk_mul
- \+ *theorem* cau_seq.completion.mk_neg
- \+ *def* cau_seq.completion.of_rat
- \+ *theorem* cau_seq.completion.of_rat_add
- \+ *theorem* cau_seq.completion.of_rat_div
- \+ *theorem* cau_seq.completion.of_rat_inv
- \+ *theorem* cau_seq.completion.of_rat_mul
- \+ *theorem* cau_seq.completion.of_rat_neg
- \+ *theorem* cau_seq.completion.of_rat_one
- \+ *theorem* cau_seq.completion.of_rat_sub
- \+ *theorem* cau_seq.completion.of_rat_zero
- \+ *lemma* cau_seq.completion.zero_ne_one



## [2018-08-16 07:09:33-04:00](https://github.com/leanprover-community/mathlib/commit/47a377d)
refactor(group_theory/quotient_group): remove duplicate definition ([#259](https://github.com/leanprover-community/mathlib/pull/259))
#### Estimated changes
Modified group_theory/coset.lean
- \- *lemma* left_cosets.coe_gpow
- \- *lemma* left_cosets.coe_inv
- \- *lemma* left_cosets.coe_mul
- \- *lemma* left_cosets.coe_one
- \- *lemma* left_cosets.coe_pow
- \- *lemma* left_cosets.eq_class_eq_left_coset
- \- *def* left_cosets.mk
- \- *def* left_cosets
- \- *def* left_rel
- \+ *lemma* quotient_group.eq_class_eq_left_coset
- \+ *def* quotient_group.left_rel
- \+ *def* quotient_group.mk
- \+ *def* quotient_group.quotient

Modified group_theory/group_action.lean
- \+/\- *lemma* is_group_action.orbit_eq_iff

Modified group_theory/order_of_element.lean


Modified group_theory/quotient_group.lean
- \- *lemma* group.quotient.injective_ker_lift
- \- *def* group.quotient.lift
- \- *lemma* group.quotient.lift_mk'
- \- *lemma* group.quotient.lift_mk
- \- *def* group.quotient.mk
- \+ *lemma* quotient_group.coe_gpow
- \+ *lemma* quotient_group.coe_inv
- \+ *lemma* quotient_group.coe_mul
- \+ *lemma* quotient_group.coe_one
- \+ *lemma* quotient_group.coe_pow
- \+ *lemma* quotient_group.injective_ker_lift
- \+ *def* quotient_group.lift
- \+ *lemma* quotient_group.lift_mk'
- \+ *lemma* quotient_group.lift_mk

Modified group_theory/subgroup.lean
- \+ *lemma* normal_subgroup_of_comm_group



## [2018-08-16 06:58:15-04:00](https://github.com/leanprover-community/mathlib/commit/032e21d)
feat(topological_structures): frontier_lt_subset_eq
Based on a suggestion by Luca Gerolla
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* frontier_compl

Modified analysis/topology/topological_structures.lean
- \+ *lemma* frontier_lt_subset_eq



## [2018-08-15 20:54:08-04:00](https://github.com/leanprover-community/mathlib/commit/d468921)
fix(tactic/basic): fix build
#### Estimated changes
Modified tactic/basic.lean




## [2018-08-15 20:47:08-04:00](https://github.com/leanprover-community/mathlib/commit/bde2132)
feat(category/traversable): derive traversable instances
Authors: Simon Hudon, Mario Carneiro
#### Estimated changes
Modified category/applicative.lean
- \+ *theorem* applicative.ext
- \+/\- *lemma* applicative.map_seq_map
- \+/\- *lemma* applicative.pure_seq_eq_map'
- \+ *theorem* comp.applicative_comp_id
- \+ *theorem* comp.applicative_id_comp
- \+/\- *lemma* comp.map_pure
- \+/\- *lemma* comp.pure_seq_eq_map
- \+/\- *lemma* comp.seq_assoc
- \+/\- *lemma* comp.seq_pure

Modified category/basic.lean
- \+ *def* list.mpartition
- \+/\- *theorem* map_seq
- \+/\- *def* mtry
- \+/\- *def* mzip_with'
- \+/\- *theorem* pure_id'_seq
- \+/\- *theorem* seq_map_assoc
- \+/\- *def* succeeds

Modified category/functor.lean
- \+ *theorem* functor.comp.functor_comp_id
- \+ *theorem* functor.comp.functor_id_comp
- \+/\- *lemma* functor.comp.map_mk
- \+ *def* functor.comp.mk
- \+ *def* functor.comp.run
- \+ *def* functor.comp
- \+ *theorem* functor.ext

Modified category/traversable/basic.lean
- \+/\- *lemma* applicative_transformation.preserves_map
- \+/\- *lemma* applicative_transformation.preserves_pure
- \+/\- *def* sequence

Added category/traversable/derive.lean


Modified category/traversable/equiv.lean


Modified category/traversable/instances.lean
- \- *lemma* id.comp_traverse
- \- *lemma* id.id_traverse
- \- *lemma* id.map_traverse
- \- *lemma* id.naturality
- \- *lemma* id.traverse_map
- \+/\- *lemma* list.comp_traverse
- \+/\- *lemma* list.id_traverse
- \- *lemma* list.map_traverse
- \+/\- *lemma* list.naturality
- \+ *lemma* list.traverse_eq_map_id
- \- *lemma* list.traverse_map
- \+/\- *lemma* option.comp_traverse
- \+/\- *lemma* option.id_traverse
- \- *lemma* option.map_traverse
- \+/\- *lemma* option.naturality
- \+ *lemma* option.traverse_eq_map_id
- \- *lemma* option.traverse_map

Modified category/traversable/lemmas.lean
- \+/\- *lemma* traversable.comp_sequence
- \+ *lemma* traversable.map_eq_traverse_id
- \+ *theorem* traversable.map_traverse
- \+/\- *lemma* traversable.naturality'
- \+ *lemma* traversable.naturality_pf
- \+/\- *def* traversable.pure_transformation
- \+ *theorem* traversable.pure_transformation_apply
- \+ *lemma* traversable.pure_traverse
- \- *lemma* traversable.purity
- \+ *lemma* traversable.traverse_comp
- \+ *lemma* traversable.traverse_eq_map_id'
- \- *lemma* traversable.traverse_eq_map_ident
- \+ *lemma* traversable.traverse_id
- \+ *lemma* traversable.traverse_map'
- \+ *theorem* traversable.traverse_map

Modified data/vector2.lean
- \+ *def* vector.to_array

Modified tactic/basic.lean


Modified tactic/wlog.lean


Modified tests/examples.lean


Modified tests/tactics.lean




## [2018-08-15 20:29:33-04:00](https://github.com/leanprover-community/mathlib/commit/d288f07)
feat(docs/*): Docs theories ([#251](https://github.com/leanprover-community/mathlib/pull/251))
Authors: Patrick Massot, Kevin Buzzard, Chris Hughes, Scott Morrison
#### Estimated changes
Modified README.md


Modified docs/extras.md


Added docs/mathlib-overview.md


Modified docs/theories.md


Added docs/theories/linear_algebra.md


Added docs/theories/measure.md


Added docs/theories/number_theory.md


Added docs/theories/polynomials.md


Deleted docs/theories/quotients.md


Modified docs/theories/relations.md


Modified docs/wip.md




## [2018-08-15 20:25:34-04:00](https://github.com/leanprover-community/mathlib/commit/5d791c6)
feat(data/polynomial): nth_roots ([#260](https://github.com/leanprover-community/mathlib/pull/260))
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* polynomial.C_add
- \+ *lemma* polynomial.C_mul
- \- *lemma* polynomial.C_mul_C
- \+ *lemma* polynomial.X_pow_sub_C_ne_zero
- \+ *lemma* polynomial.card_nth_roots
- \+ *lemma* polynomial.card_roots_X_pow_sub_C
- \+ *lemma* polynomial.degree_X_pow
- \+ *lemma* polynomial.degree_X_pow_sub_C
- \+ *lemma* polynomial.eval_pow
- \+ *lemma* polynomial.leading_coeff_X_pow
- \+ *lemma* polynomial.mem_nth_roots



## [2018-08-15 20:22:47-04:00](https://github.com/leanprover-community/mathlib/commit/6e21c48)
feat(data/multiset): count_filter
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.count_filter
- \+ *theorem* list.countp_filter
- \+/\- *theorem* list.filter_filter

Modified data/multiset.lean
- \+ *theorem* multiset.count_filter
- \+ *theorem* multiset.countp_filter



## [2018-08-15 18:43:52-04:00](https://github.com/leanprover-community/mathlib/commit/46229d2)
feat(data/multiset): filter_congr, filter_filter
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* finset.filter_congr

Modified data/list/basic.lean
- \+ *theorem* list.filter_filter

Modified data/multiset.lean
- \+ *theorem* multiset.filter_add_filter
- \+ *theorem* multiset.filter_add_not
- \+ *lemma* multiset.filter_congr
- \+ *theorem* multiset.filter_filter



## [2018-08-15 18:17:20-04:00](https://github.com/leanprover-community/mathlib/commit/4c843f2)
refactor(category/basic): move {list,option}.traverse to category.basic
#### Estimated changes
Modified category/basic.lean


Modified category/traversable/instances.lean


Modified tactic/basic.lean




## [2018-08-15 18:16:17-04:00](https://github.com/leanprover-community/mathlib/commit/1aae37c)
refactor(tactic/basic): move meta.expr to tactic.basic, cleanup
#### Estimated changes
Deleted meta/expr.lean


Modified tactic/basic.lean


Modified tactic/interactive.lean


Modified tactic/rewrite.lean




## [2018-08-15 18:14:01-04:00](https://github.com/leanprover-community/mathlib/commit/0738d4e)
feat(tactic/basic): environment.is_structure
#### Estimated changes
Modified tactic/basic.lean




## [2018-08-15 15:47:27-04:00](https://github.com/leanprover-community/mathlib/commit/4a7103d)
refactor(topology/uniform_space): proof simplification / extension
#### Estimated changes
Modified analysis/metric_space.lean
- \- *lemma* lebesgue_number_lemma
- \+ *lemma* lebesgue_number_lemma_of_metric
- \+ *lemma* lebesgue_number_lemma_of_metric_sUnion

Modified analysis/topology/uniform_space.lean
- \- *lemma* assoc_comp_rel
- \+ *lemma* comp_rel_assoc
- \- *lemma* lebesgue_entourage_lemma
- \+ *lemma* lebesgue_number_lemma
- \+ *lemma* lebesgue_number_lemma_sUnion



## [2018-08-15 10:16:37-04:00](https://github.com/leanprover-community/mathlib/commit/b4dc0a5)
feat(analysis/metric_space): Lebesgue number lemma for uniform spaces and metric spaces ([#237](https://github.com/leanprover-community/mathlib/pull/237))
#### Estimated changes
Modified analysis/metric_space.lean
- \+ *lemma* lebesgue_number_lemma

Modified analysis/topology/uniform_space.lean
- \+ *lemma* assoc_comp_rel
- \+ *lemma* lebesgue_entourage_lemma



## [2018-08-14 13:14:13-04:00](https://github.com/leanprover-community/mathlib/commit/7c1d3b4)
refactor(data/equiv/basic): simplify definition of `equiv.of_bijective`
#### Estimated changes
Modified data/equiv/basic.lean
- \+/\- *theorem* equiv.of_bijective_to_fun



## [2018-08-14 16:11:37+02:00](https://github.com/leanprover-community/mathlib/commit/add16e9)
feat(order): add order_dual (similar to with_top/with_bot) and dual order instances
#### Estimated changes
Modified order/basic.lean
- \- *theorem* le_dual_eq_le
- \+ *def* order_dual
- \- *def* partial_order.dual
- \- *def* preorder.dual

Modified order/bounded_lattice.lean


Modified order/complete_lattice.lean
- \+ *theorem* lattice.Inf_eq_top
- \+ *theorem* lattice.Sup_eq_bot
- \+/\- *theorem* lattice.infi_const
- \+ *lemma* lattice.infi_eq_bot
- \+ *lemma* lattice.infi_eq_top
- \+/\- *lemma* lattice.infi_top
- \+ *def* lattice.ord_continuous
- \+ *lemma* lattice.ord_continuous_mono
- \+ *lemma* lattice.ord_continuous_sup
- \+/\- *lemma* lattice.supr_bot
- \+/\- *theorem* lattice.supr_const
- \- *def* ord_continuous
- \- *lemma* ord_continuous_mono
- \- *lemma* ord_continuous_sup

Modified order/galois_connection.lean


Modified order/lattice.lean




## [2018-08-14 05:14:40-04:00](https://github.com/leanprover-community/mathlib/commit/f81c764)
doc(data/rat): todo [ci-skip]
#### Estimated changes
Modified data/rat.lean




## [2018-08-14 05:07:05-04:00](https://github.com/leanprover-community/mathlib/commit/6359010)
feat(data/list/perm): subperm_cons_diff and subset_cons_diff ([#256](https://github.com/leanprover-community/mathlib/pull/256))
#### Estimated changes
Modified data/list/perm.lean
- \+ *theorem* list.subperm_cons_diff
- \+ *theorem* list.subset_cons_diff



## [2018-08-14 04:59:55-04:00](https://github.com/leanprover-community/mathlib/commit/e53c2bb)
perf(data/rat): add more extra typeclass instances
#### Estimated changes
Modified data/rat.lean


Modified data/real/basic.lean


Modified data/real/cau_seq.lean


Modified tactic/basic.lean




## [2018-08-14 01:44:16-04:00](https://github.com/leanprover-community/mathlib/commit/638b7fd)
feat(set_theory/cardinal): finite lower bound on cardinality
#### Estimated changes
Modified data/fintype.lean
- \+ *lemma* fintype.card_coe

Modified data/set/finite.lean
- \+ *theorem* set.finite.exists_finset

Modified set_theory/cardinal.lean
- \+ *theorem* cardinal.card_le_of_finset



## [2018-08-14 01:42:29-04:00](https://github.com/leanprover-community/mathlib/commit/9699f8d)
feat(data/multiset): some more theorems about diagonal
#### Estimated changes
Modified data/multiset.lean
- \+ *theorem* multiset.diagonal_coe'
- \+/\- *theorem* multiset.diagonal_coe
- \+ *theorem* multiset.diagonal_cons
- \+ *theorem* multiset.diagonal_zero
- \+ *theorem* multiset.revzip_powerset_aux'
- \+/\- *theorem* multiset.revzip_powerset_aux
- \- *theorem* multiset.revzip_powerset_aux_eq_map
- \+ *theorem* multiset.revzip_powerset_aux_lemma
- \+ *theorem* multiset.revzip_powerset_aux_perm_aux'

Modified data/pfun.lean




## [2018-08-14 01:41:49-04:00](https://github.com/leanprover-community/mathlib/commit/d016186)
fix(tactic/norm_num): make norm_num only apply to current goal
#### Estimated changes
Modified tactic/norm_num.lean




## [2018-08-13 07:53:08-04:00](https://github.com/leanprover-community/mathlib/commit/8692959)
feat(data/list/basic): diff_sublist_of_sublist
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.diff_sublist_of_sublist



## [2018-08-13 11:25:34+02:00](https://github.com/leanprover-community/mathlib/commit/4bc2287)
fix(.): fix up ext usages (c.f. 7cfc299fcdcae715dc0ac33cba0cd1aefa9777cd)
#### Estimated changes
Modified data/buffer/basic.lean


Modified data/polynomial.lean


Modified tests/tactics.lean




## [2018-08-13 03:50:00-04:00](https://github.com/leanprover-community/mathlib/commit/89d71ad)
fix(tactic/basic): make `try_intros` not fail given too few names
#### Estimated changes
Modified tactic/basic.lean




## [2018-08-13 03:05:01-04:00](https://github.com/leanprover-community/mathlib/commit/9ea9324)
fix(category/basic): change "try" to "mtry"
#### Estimated changes
Modified category/applicative.lean


Modified category/basic.lean
- \+ *def* mtry
- \- *def* try

Modified tactic/converter/old_conv.lean




## [2018-08-13 02:53:31-04:00](https://github.com/leanprover-community/mathlib/commit/7714632)
fix(category/basic): fix build
#### Estimated changes
Modified category/basic.lean
- \+/\- *def* try



## [2018-08-13 02:46:45-04:00](https://github.com/leanprover-community/mathlib/commit/7cfc299)
refactor(tactic/interactive): minor cleanup, change `ext` notation
#### Estimated changes
Modified category/basic.lean
- \+ *def* succeeds
- \+ *def* try

Modified data/real/basic.lean


Modified docs/tactics.md


Modified tactic/basic.lean


Modified tactic/converter/old_conv.lean


Modified tactic/ext.lean


Modified tactic/replacer.lean




## [2018-08-12 08:52:56-04:00](https://github.com/leanprover-community/mathlib/commit/522d3ea)
refactor(data/list/basic): simplify proof
#### Estimated changes
Modified data/list/basic.lean
- \+/\- *theorem* list.mem_diff_of_mem



## [2018-08-12 17:09:22+10:00](https://github.com/leanprover-community/mathlib/commit/26ef0a0)
feat(data/list/basic): diff_subset and mem_diff_of_mem
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.diff_subset
- \+ *theorem* list.mem_diff_of_mem



## [2018-08-11 03:59:51-04:00](https://github.com/leanprover-community/mathlib/commit/6bf879d)
fix(category_theory): consistent use of coercions, consistent naming ([#248](https://github.com/leanprover-community/mathlib/pull/248))
#### Estimated changes
Modified category_theory/functor.lean
- \+/\- *lemma* category_theory.functor.comp_obj

Modified category_theory/products.lean
- \- *lemma* category_theory.prod.category.comp
- \- *def* category_theory.prod.category.fst
- \- *lemma* category_theory.prod.category.id
- \- *def* category_theory.prod.category.inl
- \- *def* category_theory.prod.category.inr
- \- *def* category_theory.prod.category.snd
- \+ *def* category_theory.prod.fst
- \+ *def* category_theory.prod.inl
- \+ *def* category_theory.prod.inr
- \+ *def* category_theory.prod.snd
- \+ *lemma* category_theory.prod_comp
- \+ *lemma* category_theory.prod_id



## [2018-08-10 14:02:33-04:00](https://github.com/leanprover-community/mathlib/commit/e34fec8)
fix(tests/examples): fix test
#### Estimated changes
Modified tests/examples.lean




## [2018-08-10 12:44:38-04:00](https://github.com/leanprover-community/mathlib/commit/57194fa)
fix(tactic/wlog): fix issue causing segfault
#### Estimated changes
Modified algebra/ring.lean


Modified data/stream/basic.lean


Modified logic/relation.lean


Modified tactic/wlog.lean




## [2018-08-10 12:44:38-04:00](https://github.com/leanprover-community/mathlib/commit/a679c98)
refactor(data/multiset): shorten proof
#### Estimated changes
Modified data/multiset.lean




## [2018-08-10 10:05:03-04:00](https://github.com/leanprover-community/mathlib/commit/24aeeaf)
feat(data/zmod): integers mod n ([#159](https://github.com/leanprover-community/mathlib/pull/159))
#### Estimated changes
Modified data/int/basic.lean
- \+ *lemma* int.coe_nat_ne_zero_iff_pos
- \+ *lemma* int.coe_nat_nonneg
- \+ *lemma* int.mod_mod

Modified data/int/modeq.lean
- \+/\- *lemma* int.modeq.coe_nat_modeq_iff

Added data/zmod.lean
- \+ *lemma* zmod.add_val
- \+ *lemma* zmod.card_zmod
- \+ *lemma* zmod.cast_mod_int
- \+ *lemma* zmod.cast_mod_nat
- \+ *lemma* zmod.cast_self_eq_zero
- \+ *lemma* zmod.cast_val
- \+ *lemma* zmod.eq_iff_modeq_int
- \+ *lemma* zmod.eq_iff_modeq_nat
- \+ *lemma* zmod.mk_eq_cast
- \+ *lemma* zmod.mul_val
- \+ *lemma* zmod.one_val
- \+ *lemma* zmod.val_cast_int
- \+ *lemma* zmod.val_cast_nat
- \+ *lemma* zmod.val_cast_of_lt
- \+ *lemma* zmod.zero_val
- \+ *def* zmod
- \+ *lemma* zmodp.add_val
- \+ *lemma* zmodp.cast_mod_int
- \+ *lemma* zmodp.cast_mod_nat
- \+ *lemma* zmodp.cast_self_eq_zero:
- \+ *lemma* zmodp.cast_val
- \+ *lemma* zmodp.eq_iff_modeq_int
- \+ *lemma* zmodp.eq_iff_modeq_nat
- \+ *lemma* zmodp.gcd_a_modeq
- \+ *lemma* zmodp.mk_eq_cast
- \+ *lemma* zmodp.mul_inv_eq_gcd
- \+ *lemma* zmodp.mul_val
- \+ *lemma* zmodp.one_val
- \+ *lemma* zmodp.val_cast_int
- \+ *lemma* zmodp.val_cast_nat
- \+ *lemma* zmodp.val_cast_of_lt
- \+ *lemma* zmodp.zero_val
- \+ *def* zmodp



## [2018-08-10 09:44:20-04:00](https://github.com/leanprover-community/mathlib/commit/e1312b4)
feat(group_theory/perm): signatures of permutations ([#231](https://github.com/leanprover-community/mathlib/pull/231))
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *theorem* is_group_anti_hom.prod
- \+/\- *theorem* is_group_hom.prod

Modified algebra/group.lean
- \+ *def* is_conj
- \+ *lemma* is_conj_iff_eq
- \+ *lemma* is_conj_refl
- \+ *lemma* is_conj_symm
- \+ *lemma* is_conj_trans

Modified data/equiv/basic.lean
- \+/\- *lemma* equiv.inverse_trans_apply
- \+ *theorem* equiv.refl_trans
- \+ *lemma* equiv.swap_inv
- \+ *theorem* equiv.symm_trans
- \+ *lemma* equiv.symm_trans_swap_trans
- \+ *theorem* equiv.trans_refl
- \+ *theorem* equiv.trans_symm

Modified data/fin.lean


Modified data/finset.lean
- \+ *def* finset.attach_fin
- \+ *lemma* finset.card_attach_fin
- \+ *lemma* finset.eq_empty_iff_forall_not_mem
- \+ *lemma* finset.mem_attach_fin
- \+ *theorem* finset.mem_sort

Modified data/fintype.lean
- \+ *theorem* fintype.card_units_int

Modified data/multiset.lean
- \+ *theorem* multiset.mem_sort

Added group_theory/perm.lean
- \+ *lemma* equiv.perm.eq_sign_of_surjective_hom
- \+ *def* equiv.perm.fin_pairs_lt
- \+ *lemma* equiv.perm.is_conj_swap
- \+ *def* equiv.perm.is_swap
- \+ *lemma* equiv.perm.mem_fin_pairs_lt
- \+ *def* equiv.perm.sign
- \+ *def* equiv.perm.sign_aux2
- \+ *def* equiv.perm.sign_aux3
- \+ *lemma* equiv.perm.sign_aux3_mul_and_swap
- \+ *def* equiv.perm.sign_aux
- \+ *lemma* equiv.perm.sign_aux_eq_sign_aux2
- \+ *lemma* equiv.perm.sign_aux_inv
- \+ *lemma* equiv.perm.sign_aux_mul
- \+ *lemma* equiv.perm.sign_aux_one
- \+ *lemma* equiv.perm.sign_aux_swap
- \+ *def* equiv.perm.sign_bij_aux
- \+ *lemma* equiv.perm.sign_bij_aux_inj
- \+ *lemma* equiv.perm.sign_bij_aux_mem
- \+ *lemma* equiv.perm.sign_bij_aux_surj
- \+ *lemma* equiv.perm.sign_eq_of_is_swap
- \+ *lemma* equiv.perm.sign_swap
- \+ *lemma* equiv.perm.support_swap_mul
- \+ *def* equiv.perm.swap_factors
- \+ *def* equiv.perm.swap_factors_aux
- \+ *lemma* equiv.perm.swap_mul_swap_mul_swap
- \+ *def* equiv.perm.trunc_swap_factors



## [2018-08-10 09:14:19-04:00](https://github.com/leanprover-community/mathlib/commit/251a8c3)
feat(tactic/assoc_rewrite): new tactic for implicitly applying associativity before rewriting ([#228](https://github.com/leanprover-community/mathlib/pull/228))
#### Estimated changes
Modified docs/tactics.md


Added tactic/rewrite.lean


Modified tests/tactics.lean




## [2018-08-10 09:07:20-04:00](https://github.com/leanprover-community/mathlib/commit/ff25083)
feat(data/list/basic): nil_diff and diff_sublist ([#235](https://github.com/leanprover-community/mathlib/pull/235))
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.diff_sublist
- \+ *theorem* list.nil_diff
- \+ *def* list.reverse_rec_on
- \- *theorem* list.reverse_rec_on



## [2018-08-10 09:06:41-04:00](https://github.com/leanprover-community/mathlib/commit/26ef419)
feat(data/fintype): fintype and decidable_eq for partial functions ([#236](https://github.com/leanprover-community/mathlib/pull/236))
#### Estimated changes
Modified data/fintype.lean


Modified logic/function.lean




## [2018-08-10 09:04:15-04:00](https://github.com/leanprover-community/mathlib/commit/e2521c3)
feat(data/set/finite): card_image_of_injective and other minor lemmas ([#245](https://github.com/leanprover-community/mathlib/pull/245))
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* finset.coe_ssubset

Modified data/set/basic.lean
- \+ *lemma* set.ssubset_iff_subset_not_subset

Modified data/set/finite.lean
- \+ *lemma* finset.coe_to_finset'
- \+ *lemma* set.card_image_of_inj_on
- \+ *lemma* set.card_image_of_injective
- \+ *lemma* set.card_lt_card



## [2018-08-10 08:52:34-04:00](https://github.com/leanprover-community/mathlib/commit/d400510)
feat(data/nat/binomial): the binomial theorem ([#214](https://github.com/leanprover-community/mathlib/pull/214))
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.prod_range_succ'
- \+ *lemma* finset.prod_range_succ
- \+ *lemma* finset.sum_range_succ'

Added data/nat/binomial.lean
- \+ *theorem* add_pow



## [2018-08-10 08:50:52-04:00](https://github.com/leanprover-community/mathlib/commit/54ce15b)
refactor(ring_theory/ideals): avoid using type class inference for setoids in quotient rings and groups ([#212](https://github.com/leanprover-community/mathlib/pull/212))
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* is_group_hom.gpow
- \+ *theorem* is_group_hom.pow

Modified data/quot.lean
- \+ *lemma* quotient.exact'
- \+ *theorem* quotient.mk_out'
- \+ *theorem* quotient.out_eq'
- \+ *lemma* quotient.sound'

Modified group_theory/coset.lean
- \+ *lemma* left_cosets.coe_gpow
- \+ *lemma* left_cosets.coe_inv
- \+ *lemma* left_cosets.coe_mul
- \+ *lemma* left_cosets.coe_one
- \+ *lemma* left_cosets.coe_pow
- \+/\- *lemma* left_cosets.eq_class_eq_left_coset
- \+ *def* left_cosets.mk

Modified ring_theory/ideals.lean
- \- *lemma* is_ideal.exists_inv
- \- *def* is_ideal.quotient
- \- *lemma* is_ideal.quotient_eq_zero_iff_mem
- \- *def* is_ideal.quotient_rel
- \+ *def* is_ideal.trivial
- \+ *lemma* quotient_ring.coe_add
- \+ *lemma* quotient_ring.coe_mul
- \+ *lemma* quotient_ring.coe_neg
- \+ *lemma* quotient_ring.coe_one
- \+ *lemma* quotient_ring.coe_pow
- \+ *lemma* quotient_ring.coe_sub
- \+ *lemma* quotient_ring.coe_zero
- \+ *lemma* quotient_ring.eq_zero_iff_mem
- \+ *lemma* quotient_ring.exists_inv
- \+ *def* quotient_ring.mk
- \+ *def* quotient_ring.quotient
- \+ *def* quotient_ring.quotient_rel



## [2018-08-10 07:12:29-04:00](https://github.com/leanprover-community/mathlib/commit/5b9914b)
style(group_theory/quotient_group): code style
#### Estimated changes
Modified group_theory/quotient_group.lean
- \+/\- *def* group.quotient.lift
- \+/\- *lemma* group.quotient.lift_mk'
- \+/\- *lemma* group.quotient.lift_mk



## [2018-08-10 07:05:33-04:00](https://github.com/leanprover-community/mathlib/commit/d279ddb)
feat(group_theory): adding basic theory of quotient groups
#### Estimated changes
Added group_theory/quotient_group.lean
- \+ *lemma* group.quotient.injective_ker_lift
- \+ *def* group.quotient.lift
- \+ *lemma* group.quotient.lift_mk'
- \+ *lemma* group.quotient.lift_mk
- \+ *def* group.quotient.mk



## [2018-08-10 07:04:00-04:00](https://github.com/leanprover-community/mathlib/commit/0f42b27)
feat(group_theory/submonoid,subgroup): merge with add_* versions
#### Estimated changes
Modified algebra/group.lean


Deleted group_theory/add_subgroup.lean
- \- *def* add_group.closure
- \- *theorem* add_group.closure_subset
- \- *theorem* add_group.gmultiples_eq_closure
- \- *lemma* add_group.mem_closure
- \- *theorem* add_group.subset_closure
- \- *def* gmultiples
- \- *lemma* injective_add
- \- *lemma* is_add_subgroup.add_mem_cancel_left
- \- *lemma* is_add_subgroup.add_mem_cancel_right
- \- *def* is_add_subgroup.center
- \- *lemma* is_add_subgroup.gsmul_mem
- \- *lemma* is_add_subgroup.mem_center
- \- *lemma* is_add_subgroup.mem_norm_comm
- \- *lemma* is_add_subgroup.mem_norm_comm_iff
- \- *lemma* is_add_subgroup.mem_trivial
- \- *lemma* is_add_subgroup.neg_mem_iff
- \- *theorem* is_add_subgroup.of_sub
- \- *def* is_add_subgroup.trivial
- \- *lemma* is_add_subgroup.trivial_eq_closure
- \- *lemma* mem_gmultiples

Deleted group_theory/add_submonoid.lean
- \- *def* add_monoid.closure
- \- *theorem* add_monoid.closure_subset
- \- *theorem* add_monoid.exists_list_of_mem_closure
- \- *theorem* add_monoid.subset_closure
- \- *lemma* is_add_submonoid.list_sum_mem
- \- *lemma* is_add_submonoid.multiple_subset
- \- *lemma* is_add_submonoid.smul_mem
- \- *def* multiples

Modified group_theory/subgroup.lean
- \+ *def* add_group.closure
- \+ *theorem* add_group.closure_subset
- \+ *theorem* add_group.gmultiples_eq_closure
- \+ *lemma* add_group.mem_closure
- \+ *theorem* additive.is_add_subgroup_iff
- \+ *theorem* additive.normal_add_subgroup_iff
- \+ *def* gmultiples
- \+/\- *theorem* group.subset_closure
- \+ *def* is_add_subgroup.center
- \+ *lemma* is_add_subgroup.gsmul_mem
- \+ *theorem* is_add_subgroup.of_sub
- \+ *def* is_add_subgroup.trivial
- \+/\- *lemma* is_subgroup.mem_center
- \+/\- *lemma* is_subgroup.mem_norm_comm
- \+/\- *lemma* is_subgroup.mem_norm_comm_iff
- \+/\- *theorem* is_subgroup.of_div
- \+ *lemma* mem_gmultiples
- \+/\- *lemma* mem_gpowers
- \+ *theorem* multiplicative.is_subgroup_iff
- \+ *theorem* multiplicative.normal_subgroup_iff

Modified group_theory/submonoid.lean
- \+ *def* add_monoid.closure
- \+ *theorem* add_monoid.closure_subset
- \+ *theorem* add_monoid.exists_list_of_mem_closure
- \+ *theorem* add_monoid.subset_closure
- \+ *theorem* additive.is_add_submonoid_iff
- \+ *lemma* is_add_submonoid.multiple_subset
- \+ *lemma* is_add_submonoid.smul_mem
- \+/\- *lemma* is_submonoid.pow_mem
- \+ *def* multiples
- \+ *theorem* multiplicative.is_submonoid_iff



## [2018-08-10 07:04:00-04:00](https://github.com/leanprover-community/mathlib/commit/1d5dd0d)
feat(group_theory): adding add_subgroup and add_submonoid
#### Estimated changes
Added group_theory/add_subgroup.lean
- \+ *def* add_group.closure
- \+ *theorem* add_group.closure_subset
- \+ *theorem* add_group.gmultiples_eq_closure
- \+ *lemma* add_group.mem_closure
- \+ *theorem* add_group.subset_closure
- \+ *def* gmultiples
- \+ *lemma* injective_add
- \+ *lemma* is_add_subgroup.add_mem_cancel_left
- \+ *lemma* is_add_subgroup.add_mem_cancel_right
- \+ *def* is_add_subgroup.center
- \+ *lemma* is_add_subgroup.gsmul_mem
- \+ *lemma* is_add_subgroup.mem_center
- \+ *lemma* is_add_subgroup.mem_norm_comm
- \+ *lemma* is_add_subgroup.mem_norm_comm_iff
- \+ *lemma* is_add_subgroup.mem_trivial
- \+ *lemma* is_add_subgroup.neg_mem_iff
- \+ *theorem* is_add_subgroup.of_sub
- \+ *def* is_add_subgroup.trivial
- \+ *lemma* is_add_subgroup.trivial_eq_closure
- \+ *lemma* mem_gmultiples

Added group_theory/add_submonoid.lean
- \+ *def* add_monoid.closure
- \+ *theorem* add_monoid.closure_subset
- \+ *theorem* add_monoid.exists_list_of_mem_closure
- \+ *theorem* add_monoid.subset_closure
- \+ *lemma* is_add_submonoid.list_sum_mem
- \+ *lemma* is_add_submonoid.multiple_subset
- \+ *lemma* is_add_submonoid.smul_mem
- \+ *def* multiples



## [2018-08-10 05:37:13-04:00](https://github.com/leanprover-community/mathlib/commit/e1d92c2)
fix(tactic/replacer): fix tests
#### Estimated changes
Modified tactic/replacer.lean


Modified tests/replacer.lean




## [2018-08-09 12:09:07-04:00](https://github.com/leanprover-community/mathlib/commit/bf3dde1)
refactor(set_theory/cardinal): remove noncomputable theory
#### Estimated changes
Modified set_theory/cardinal.lean
- \- *def* cardinal.min
- \- *def* cardinal.succ
- \- *def* cardinal.sup



## [2018-08-09 12:09:07-04:00](https://github.com/leanprover-community/mathlib/commit/a995a3a)
perf(tactic/replacer): use if instead of match
#### Estimated changes
Modified tactic/replacer.lean




## [2018-08-09 12:06:27-04:00](https://github.com/leanprover-community/mathlib/commit/55c2cfd)
fix(docs/theories/integers): typo pointed out by Bryan Gin-ge Chen ([#244](https://github.com/leanprover-community/mathlib/pull/244))
#### Estimated changes
Modified docs/theories/integers.md




## [2018-08-09 02:41:57-04:00](https://github.com/leanprover-community/mathlib/commit/a52c240)
doc(replacer): documentation and test ([#243](https://github.com/leanprover-community/mathlib/pull/243))
#### Estimated changes
Modified category_theory/category.lean


Modified docs/tactics.md


Added tests/replacer.lean




## [2018-08-08 14:39:58-04:00](https://github.com/leanprover-community/mathlib/commit/a917810)
refactor(tactic/interactive): merge rcases_hint -> rcases?
#### Estimated changes
Modified docs/tactics.md


Modified tactic/interactive.lean




## [2018-08-08 10:51:30-04:00](https://github.com/leanprover-community/mathlib/commit/8a19a98)
feat(tactic/replacer): replaceable tactics
#### Estimated changes
Modified tactic/interactive.lean


Added tactic/replacer.lean




## [2018-08-08 06:57:37-04:00](https://github.com/leanprover-community/mathlib/commit/732ec0e)
feat(tactic/rcases): rcases_hint, rintro_hint
#### Estimated changes
Modified docs/tactics.md


Modified tactic/basic.lean


Modified tactic/interactive.lean
- \- *def* tactic.interactive.rcases_patt_inverted

Modified tactic/rcases.lean
- \+ *def* tactic.merge_list
- \- *def* tactic.rcases_patt.name



## [2018-08-08 00:44:37-04:00](https://github.com/leanprover-community/mathlib/commit/fe7cd33)
refactor(category_theory/products): tweak PR after merge
#### Estimated changes
Modified analysis/nnreal.lean
- \+ *def* nnreal

Modified category_theory/functor.lean
- \+ *def* category_theory.functor.comp

Modified category_theory/functor_category.lean
- \+ *lemma* category_theory.functor.category.comp_app
- \+ *lemma* category_theory.functor.category.id_app
- \+ *lemma* category_theory.functor.category.nat_trans.app_naturality
- \+ *lemma* category_theory.functor.category.nat_trans.naturality_app
- \- *lemma* category_theory.functor_category.comp_app
- \- *lemma* category_theory.functor_category.id_app
- \- *lemma* category_theory.functor_category.nat_trans.app_naturality
- \- *lemma* category_theory.functor_category.nat_trans.naturality_app

Modified category_theory/natural_transformation.lean
- \+/\- *lemma* category_theory.nat_trans.exchange
- \+ *def* category_theory.nat_trans.hcomp
- \+ *def* category_theory.nat_trans.vcomp

Modified category_theory/products.lean
- \+ *def* category_theory.functor.prod
- \+ *lemma* category_theory.functor.prod_map
- \+ *lemma* category_theory.functor.prod_obj
- \- *lemma* category_theory.functor.product_map
- \- *lemma* category_theory.functor.product_obj
- \+ *def* category_theory.nat_trans.prod
- \+ *lemma* category_theory.nat_trans.prod_app
- \- *lemma* category_theory.nat_trans.product_app
- \+ *lemma* category_theory.prod.category.comp
- \+ *def* category_theory.prod.category.fst
- \+ *lemma* category_theory.prod.category.id
- \+ *def* category_theory.prod.category.inl
- \+ *def* category_theory.prod.category.inr
- \+ *def* category_theory.prod.category.snd
- \- *lemma* category_theory.product_category.comp
- \- *lemma* category_theory.product_category.id

Modified order/bounds.lean
- \+ *def* is_glb
- \+ *def* is_greatest
- \+ *def* is_least
- \+ *def* is_lub
- \+ *def* lower_bounds
- \+ *def* upper_bounds

Modified tactic/basic.lean




## [2018-08-08 00:32:10-04:00](https://github.com/leanprover-community/mathlib/commit/02cf7a6)
feat(category_theory): product categories and functor categories ([#239](https://github.com/leanprover-community/mathlib/pull/239))
#### Estimated changes
Added category_theory/functor_category.lean
- \+ *lemma* category_theory.functor_category.comp_app
- \+ *lemma* category_theory.functor_category.id_app
- \+ *lemma* category_theory.functor_category.nat_trans.app_naturality
- \+ *lemma* category_theory.functor_category.nat_trans.naturality_app

Added category_theory/products.lean
- \+ *lemma* category_theory.functor.product_map
- \+ *lemma* category_theory.functor.product_obj
- \+ *lemma* category_theory.nat_trans.product_app
- \+ *lemma* category_theory.product_category.comp
- \+ *lemma* category_theory.product_category.id



## [2018-08-08 00:29:39-04:00](https://github.com/leanprover-community/mathlib/commit/47a6a6f)
fix(tactic/interactive): try_for should fail if the tactic fails
#### Estimated changes
Modified tactic/interactive.lean




## [2018-08-08 00:29:39-04:00](https://github.com/leanprover-community/mathlib/commit/417f29a)
fix(linear_algebra/multivariate_polynomial): remove some @[simp]
#### Estimated changes
Modified linear_algebra/multivariate_polynomial.lean
- \+/\- *lemma* mv_polynomial.C_mul_monomial
- \+/\- *lemma* mv_polynomial.eval_monomial
- \+/\- *lemma* mv_polynomial.eval₂_mul_monomial



## [2018-08-07 20:28:50-04:00](https://github.com/leanprover-community/mathlib/commit/bd7f1b0)
feat(data/fintype): injective_iff_surjective ([#240](https://github.com/leanprover-community/mathlib/pull/240))
#### Estimated changes
Modified data/fintype.lean
- \+/\- *lemma* fintype.card_le_of_injective
- \+ *lemma* fintype.injective_iff_surjective
- \+ *lemma* fintype.injective_iff_surjective_of_equiv



## [2018-08-07 06:43:17-04:00](https://github.com/leanprover-community/mathlib/commit/9b1be73)
feat(category_theory): basic definitions ([#152](https://github.com/leanprover-community/mathlib/pull/152))
* feat(category_theory): basic definitions
* fixing formatting in documentation
* corrections from review
* removing second ematch attribute on associativity_lemma
* being slightly more careful about variables
(I don't think there were any actual errors,
but I was sometimes using an argument
when there was a variable of the same
name available.)
* fix(notation): transformation components
Using `@>` per @rwbarton's suggestion.
* fix(notation): more conventional notation for composition
* adjusting namespaces, capitalisation, and headers
* move functor/default.lean to functor.lean
(Later PRs will add more files to the functor/ directory, but that can wait.)
* oops
* fixing indentation
* namespace for instances
* removing unnecessary `@>` notation for natural transformations
* renaming, namespacing, and removing a spurious attribute
* better naming, namespaces, and coercions
* updating documentation
* renaming id
* reordering definitions
* rfl lemmas for has_one
* formatting
* formatting
* renaming: snake_case
* renaming coe rfl lemmas
* functoriality -> map_comp
* rfl lemmas for identity C and identity F (reducing both to `1`)
* renaming ext lemma to `ext`
* rename `natural_transformation` to `nat_trans`
* rename `make_lemma` to `restate_axiom`
* renaming nat_trans.components to nat_trans.app
* oops, fix import
* adding doc_comments, and `protected`
* formatting
* removing `has_one` instances, per zulip chat, and adding a `vcomp.assoc` lemma
* removing the attribute that `restate_axiom` used to add
(it was causing a problem on travis, but not locally? anyway it's useless)
* fixing names
#### Estimated changes
Added category_theory/category.lean


Added category_theory/functor.lean
- \+ *lemma* category_theory.functor.coe_def
- \+ *lemma* category_theory.functor.comp_map
- \+ *lemma* category_theory.functor.comp_obj
- \+ *lemma* category_theory.functor.id_map
- \+ *lemma* category_theory.functor.id_obj

Added category_theory/natural_transformation.lean
- \+ *lemma* category_theory.nat_trans.coe_def
- \+ *lemma* category_theory.nat_trans.exchange
- \+ *lemma* category_theory.nat_trans.ext
- \+ *lemma* category_theory.nat_trans.hcomp_app
- \+ *lemma* category_theory.nat_trans.id_app
- \+ *lemma* category_theory.nat_trans.vcomp_app
- \+ *lemma* category_theory.nat_trans.vcomp_assoc

Added docs/theories/categories.md


Added tactic/restate_axiom.lean




## [2018-08-07 05:51:20-04:00](https://github.com/leanprover-community/mathlib/commit/235129a)
feat(linear_algebra/multivariate_polynomial): Add `_sub` and `_neg` lemmas, and make them simp. ([#238](https://github.com/leanprover-community/mathlib/pull/238))
#### Estimated changes
Modified linear_algebra/multivariate_polynomial.lean
- \+/\- *lemma* mv_polynomial.C_add
- \+/\- *lemma* mv_polynomial.C_mul
- \+ *lemma* mv_polynomial.C_neg
- \+ *lemma* mv_polynomial.C_sub
- \+/\- *lemma* mv_polynomial.eval_add
- \+/\- *lemma* mv_polynomial.eval_monomial
- \+/\- *lemma* mv_polynomial.eval_mul
- \+ *lemma* mv_polynomial.eval_neg
- \+ *lemma* mv_polynomial.eval_sub
- \+/\- *lemma* mv_polynomial.eval₂_add
- \+/\- *lemma* mv_polynomial.eval₂_monomial
- \+/\- *lemma* mv_polynomial.eval₂_mul_monomial
- \+ *lemma* mv_polynomial.eval₂_neg
- \+ *lemma* mv_polynomial.eval₂_sub
- \+ *lemma* mv_polynomial.map_neg
- \+ *lemma* mv_polynomial.map_sub



## [2018-08-06 20:05:15-04:00](https://github.com/leanprover-community/mathlib/commit/8dc0393)
feat(data/multiset): adding two lemmas about singletons ([#234](https://github.com/leanprover-community/mathlib/pull/234))
#### Estimated changes
Modified data/multiset.lean
- \+ *theorem* multiset.erase_dup_singleton
- \+ *theorem* multiset.powerset_cons
- \+ *theorem* multiset.powerset_zero
- \+ *lemma* multiset.repeat_one
- \+ *lemma* multiset.repeat_succ
- \+ *lemma* multiset.repeat_zero



## [2018-08-06 11:05:42-04:00](https://github.com/leanprover-community/mathlib/commit/18bd614)
feat(algebra/group_power): adding various cast power lemmas for nat and int ([#230](https://github.com/leanprover-community/mathlib/pull/230))
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* int.cast_pow
- \+ *theorem* int.coe_nat_pow
- \+ *theorem* nat.cast_pow

Modified data/nat/basic.lean
- \+ *theorem* nat.pow_two



## [2018-08-06 06:43:02-04:00](https://github.com/leanprover-community/mathlib/commit/cf0bf2a)
fix(data/seq/wseq): fix build
#### Estimated changes
Modified data/seq/wseq.lean




## [2018-08-06 05:08:26-04:00](https://github.com/leanprover-community/mathlib/commit/8d13bb9)
feat(list/basic,multiset): list.revzip, multiset.diagonal
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.forall₂.imp
- \+ *theorem* list.length_revzip
- \+ *theorem* list.length_zip
- \+ *theorem* list.mem_zip
- \+ *theorem* list.reverse_revzip
- \+ *def* list.revzip
- \+ *theorem* list.revzip_map_fst
- \+ *theorem* list.revzip_map_snd
- \+ *theorem* list.revzip_swap
- \+ *theorem* list.unzip_eq_map
- \+ *theorem* list.unzip_left
- \+ *theorem* list.unzip_revzip
- \+ *theorem* list.unzip_right
- \+ *theorem* list.unzip_swap
- \+ *theorem* list.unzip_zip
- \+ *theorem* list.unzip_zip_left
- \+ *theorem* list.unzip_zip_right
- \+ *theorem* list.zip_append
- \+ *theorem* list.zip_map'
- \+ *theorem* list.zip_map
- \+ *theorem* list.zip_map_left
- \+ *theorem* list.zip_map_right
- \+ *theorem* list.zip_swap

Modified data/list/perm.lean
- \+ *theorem* list.revzip_sublists'
- \+ *theorem* list.revzip_sublists

Modified data/multiset.lean
- \+ *theorem* multiset.card_diagonal
- \+/\- *theorem* multiset.coe_eq_coe
- \+ *def* multiset.diagonal
- \+ *theorem* multiset.diagonal_coe
- \+ *theorem* multiset.diagonal_map_fst
- \+ *theorem* multiset.diagonal_map_snd
- \+ *theorem* multiset.mem_diagonal
- \+ *theorem* multiset.mem_powerset_aux
- \+ *theorem* multiset.revzip_powerset_aux
- \+ *theorem* multiset.revzip_powerset_aux_eq_map
- \+ *theorem* multiset.revzip_powerset_aux_perm

Modified data/prod.lean




## [2018-08-05 22:52:53-04:00](https://github.com/leanprover-community/mathlib/commit/e4b652f)
refactor(data/real/basic): rename for consistency
#### Estimated changes
Modified analysis/real.lean
- \- *lemma* exists_supremum_real

Modified data/real/basic.lean
- \- *lemma* real.Sup_is_lub

Modified data/real/ennreal.lean




## [2018-08-05 22:50:26-04:00](https://github.com/leanprover-community/mathlib/commit/e7f1103)
fix(topology/topological_structures): remove decidability assumption
#### Estimated changes
Modified analysis/topology/topological_structures.lean


Modified order/basic.lean




## [2018-08-05 22:48:47-04:00](https://github.com/leanprover-community/mathlib/commit/599df28)
feat(linear_algebra/mv_polynomial): composition lemmas
#### Estimated changes
Modified linear_algebra/multivariate_polynomial.lean
- \+/\- *def* mv_polynomial.eval
- \+/\- *lemma* mv_polynomial.eval_C
- \+/\- *lemma* mv_polynomial.eval_X
- \+/\- *lemma* mv_polynomial.eval_add
- \+ *theorem* mv_polynomial.eval_assoc
- \+/\- *lemma* mv_polynomial.eval_mul
- \+/\- *lemma* mv_polynomial.eval_zero
- \+ *def* mv_polynomial.eval₂
- \+ *lemma* mv_polynomial.eval₂_C
- \+ *lemma* mv_polynomial.eval₂_X
- \+ *lemma* mv_polynomial.eval₂_add
- \+ *lemma* mv_polynomial.eval₂_comp_left
- \+ *theorem* mv_polynomial.eval₂_eq_eval_map
- \+ *lemma* mv_polynomial.eval₂_eta
- \+ *lemma* mv_polynomial.eval₂_monomial
- \+ *lemma* mv_polynomial.eval₂_mul
- \+ *lemma* mv_polynomial.eval₂_mul_monomial
- \+ *lemma* mv_polynomial.eval₂_one
- \+ *lemma* mv_polynomial.eval₂_zero
- \+/\- *def* mv_polynomial.map
- \+/\- *theorem* mv_polynomial.map_C
- \+/\- *theorem* mv_polynomial.map_X
- \+ *theorem* mv_polynomial.map_id
- \+ *theorem* mv_polynomial.map_map
- \+/\- *theorem* mv_polynomial.map_one
- \- *def* mv_polynomial.map₂
- \- *lemma* mv_polynomial.map₂_C
- \- *lemma* mv_polynomial.map₂_X
- \- *lemma* mv_polynomial.map₂_add
- \- *lemma* mv_polynomial.map₂_monomial
- \- *lemma* mv_polynomial.map₂_mul
- \- *lemma* mv_polynomial.map₂_mul_monomial
- \- *lemma* mv_polynomial.map₂_one
- \- *lemma* mv_polynomial.map₂_zero



## [2018-08-04 19:53:15-04:00](https://github.com/leanprover-community/mathlib/commit/2d0eb8c)
feat(linear_algebra/mv_polynomial): map function, map2
#### Estimated changes
Modified data/finsupp.lean
- \+ *lemma* finsupp.map_range_single

Modified linear_algebra/multivariate_polynomial.lean
- \+ *lemma* mv_polynomial.C_add
- \+ *lemma* mv_polynomial.C_mul
- \+/\- *def* mv_polynomial.eval
- \+/\- *lemma* mv_polynomial.eval_C
- \+/\- *lemma* mv_polynomial.eval_X
- \+/\- *lemma* mv_polynomial.eval_add
- \+/\- *lemma* mv_polynomial.eval_mul
- \- *lemma* mv_polynomial.eval_mul_monomial
- \+/\- *lemma* mv_polynomial.eval_zero
- \+ *def* mv_polynomial.map
- \+ *theorem* mv_polynomial.map_C
- \+ *theorem* mv_polynomial.map_X
- \+ *theorem* mv_polynomial.map_add
- \+ *theorem* mv_polynomial.map_monomial
- \+ *theorem* mv_polynomial.map_mul
- \+ *theorem* mv_polynomial.map_one
- \+ *def* mv_polynomial.map₂
- \+ *lemma* mv_polynomial.map₂_C
- \+ *lemma* mv_polynomial.map₂_X
- \+ *lemma* mv_polynomial.map₂_add
- \+ *lemma* mv_polynomial.map₂_monomial
- \+ *lemma* mv_polynomial.map₂_mul
- \+ *lemma* mv_polynomial.map₂_mul_monomial
- \+ *lemma* mv_polynomial.map₂_one
- \+ *lemma* mv_polynomial.map₂_zero



## [2018-08-04 18:47:15-04:00](https://github.com/leanprover-community/mathlib/commit/1b93719)
feat(algebra/ring): units.neg and associated matter
#### Estimated changes
Modified algebra/group.lean
- \+ *theorem* nat.units_eq_one
- \+/\- *theorem* units.ext
- \+ *theorem* units.ext_iff
- \+/\- *lemma* units.inv_coe
- \+/\- *lemma* units.inv_mul
- \+/\- *lemma* units.inv_mul_cancel_left
- \+/\- *lemma* units.inv_mul_cancel_right
- \+/\- *lemma* units.mul_coe
- \+/\- *lemma* units.mul_inv
- \+/\- *lemma* units.mul_inv_cancel_left
- \+/\- *lemma* units.mul_inv_cancel_right
- \+/\- *theorem* units.mul_left_inj
- \+/\- *theorem* units.mul_right_inj
- \+/\- *lemma* units.one_coe
- \+/\- *lemma* units.val_coe

Modified algebra/ordered_group.lean
- \+ *theorem* units.coe_le_coe
- \+ *theorem* units.coe_lt_coe
- \+ *theorem* units.max_coe
- \+ *theorem* units.min_coe

Modified algebra/ring.lean
- \+/\- *theorem* bit0_eq_two_mul
- \+/\- *theorem* mul_two

Modified data/int/basic.lean
- \+ *theorem* int.units_eq_one_or
- \+ *theorem* int.units_nat_abs

Modified ring_theory/localization.lean
- \+ *def* localization.inv_aux



## [2018-08-04 18:43:51-04:00](https://github.com/leanprover-community/mathlib/commit/e40bee5)
feat(algebra/ring): semiring homs
#### Estimated changes
Modified algebra/ring.lean
- \+ *def* is_ring_hom.of_semiring



## [2018-08-04 18:40:37-04:00](https://github.com/leanprover-community/mathlib/commit/7ec5e87)
feat(set_theory/lists): finite ZFA
#### Estimated changes
Added set_theory/lists.lean
- \+ *def* finsets
- \+ *def* lists'.cons
- \+ *theorem* lists'.cons_subset
- \+ *theorem* lists'.mem_cons
- \+ *theorem* lists'.mem_def
- \+ *theorem* lists'.mem_equiv_left
- \+ *theorem* lists'.mem_of_subset'
- \+ *theorem* lists'.mem_of_subset
- \+ *def* lists'.of_list
- \+ *theorem* lists'.of_list_subset
- \+ *theorem* lists'.of_to_list
- \+ *theorem* lists'.subset.refl
- \+ *theorem* lists'.subset.trans
- \+ *theorem* lists'.subset_def
- \+ *theorem* lists'.subset_nil
- \+ *def* lists'.to_list
- \+ *theorem* lists'.to_list_cons
- \+ *theorem* lists'.to_of_list
- \+ *def* lists.atom
- \+ *theorem* lists.equiv.antisymm_iff
- \+ *def* lists.equiv.decidable_meas
- \+ *theorem* lists.equiv.symm
- \+ *theorem* lists.equiv.trans
- \+ *theorem* lists.equiv_atom
- \+ *def* lists.induction_mut
- \+ *def* lists.is_list
- \+ *theorem* lists.is_list_of_mem
- \+ *theorem* lists.is_list_to_list
- \+ *theorem* lists.lt_sizeof_cons'
- \+ *def* lists.mem
- \+ *def* lists.of'
- \+ *def* lists.of_list
- \+ *theorem* lists.of_to_list
- \+ *theorem* lists.sizeof_pos
- \+ *def* lists.to_list
- \+ *theorem* lists.to_of_list
- \+ *def* lists

Modified set_theory/zfc.lean




## [2018-08-03 05:53:29-04:00](https://github.com/leanprover-community/mathlib/commit/8731789)
feat(data/vector2): vector.ext ([#232](https://github.com/leanprover-community/mathlib/pull/232))
#### Estimated changes
Modified data/vector2.lean
- \+ *theorem* vector.ext

