## [2018-08-31 17:48:25+02:00](https://github.com/leanprover-community/mathlib/commit/20b4143)
feat(algebra): add normalization and GCD domain; setup for int
#### Estimated changes
Created algebra/gcd_domain.lean
- \+ *lemma* lcm_dvd_iff
- \+ *lemma* dvd_lcm_left
- \+ *lemma* dvd_lcm_right
- \+ *lemma* lcm_dvd
- \+ *lemma* norm_unit_lcm
- \+ *lemma* lcm_eq_mul_norm_unit
- \+ *theorem* norm_unit_one
- \+ *theorem* norm_unit_mul_norm_unit
- \+ *theorem* associated_of_dvd_of_dvd
- \+ *theorem* mul_norm_unit_eq_mul_norm_unit
- \+ *theorem* dvd_antisymm_of_norm
- \+ *theorem* norm_unit_gcd
- \+ *theorem* gcd_mul_lcm
- \+ *theorem* dvd_gcd_iff
- \+ *theorem* gcd_comm
- \+ *theorem* gcd_assoc
- \+ *theorem* gcd_eq_mul_norm_unit
- \+ *theorem* gcd_zero_left
- \+ *theorem* gcd_zero_right
- \+ *theorem* gcd_eq_zero_iff
- \+ *theorem* gcd_one_left
- \+ *theorem* gcd_one_right
- \+ *theorem* gcd_dvd_gcd
- \+ *theorem* gcd_same
- \+ *theorem* gcd_mul_left
- \+ *theorem* gcd_mul_right
- \+ *theorem* gcd_eq_left_iff
- \+ *theorem* gcd_eq_right_iff
- \+ *theorem* gcd_dvd_gcd_mul_left
- \+ *theorem* gcd_dvd_gcd_mul_right
- \+ *theorem* gcd_dvd_gcd_mul_left_right
- \+ *theorem* gcd_dvd_gcd_mul_right_right
- \+ *theorem* lcm_eq_zero_iff
- \+ *theorem* lcm_comm
- \+ *theorem* lcm_assoc
- \+ *theorem* lcm_dvd_lcm
- \+ *theorem* lcm_units_coe_left
- \+ *theorem* lcm_units_coe_right
- \+ *theorem* lcm_one_left
- \+ *theorem* lcm_one_right
- \+ *theorem* lcm_same
- \+ *theorem* lcm_eq_one_iff
- \+ *theorem* lcm_mul_left
- \+ *theorem* lcm_mul_right
- \+ *theorem* lcm_eq_left_iff
- \+ *theorem* lcm_eq_right_iff
- \+ *theorem* lcm_dvd_lcm_mul_left
- \+ *theorem* lcm_dvd_lcm_mul_right
- \+ *theorem* lcm_dvd_lcm_mul_left_right
- \+ *theorem* lcm_dvd_lcm_mul_right_right

Modified data/int/gcd.lean
- \+ *lemma* norm_unit_of_nonneg
- \+ *lemma* norm_unit_of_neg
- \+ *lemma* norm_unit_nat_coe
- \+ *lemma* coe_gcd
- \+ *lemma* coe_lcm
- \+ *lemma* nat_abs_gcd
- \+ *lemma* nat_abs_lcm
- \+ *theorem* coe_nat_abs_eq_mul_norm_unit
- \+/\- *theorem* lcm_def
- \+/\- *theorem* dvd_gcd
- \+/\- *theorem* gcd_mul_lcm
- \+/\- *theorem* gcd_comm
- \+/\- *theorem* gcd_assoc
- \+/\- *theorem* gcd_self
- \+/\- *theorem* gcd_zero_left
- \+/\- *theorem* gcd_zero_right
- \+/\- *theorem* gcd_one_right
- \+ *theorem* gcd_eq_zero_iff
- \+/\- *theorem* lcm_assoc
- \+/\- *theorem* lcm_zero_left
- \+/\- *theorem* lcm_zero_right
- \+/\- *theorem* lcm_one_left
- \+/\- *theorem* lcm_one_right
- \+/\- *theorem* lcm_self
- \+/\- *theorem* lcm_dvd
- \+/\- *theorem* gcd_self
- \+/\- *theorem* gcd_zero_left
- \+/\- *theorem* gcd_zero_right
- \- *theorem* gcd_dvd
- \+/\- *theorem* dvd_gcd
- \+/\- *theorem* gcd_comm
- \+/\- *theorem* gcd_assoc
- \+/\- *theorem* gcd_one_right
- \- *theorem* eq_zero_of_gcd_eq_zero_left
- \- *theorem* eq_zero_of_gcd_eq_zero_right
- \+/\- *theorem* lcm_def
- \+/\- *theorem* lcm_zero_left
- \+/\- *theorem* lcm_zero_right
- \+/\- *theorem* lcm_one_left
- \+/\- *theorem* lcm_one_right
- \+/\- *theorem* lcm_self
- \+/\- *theorem* gcd_mul_lcm
- \+/\- *theorem* lcm_dvd
- \+/\- *theorem* lcm_assoc
- \+/\- *def* lcm
- \+/\- *def* lcm



## [2018-08-31 17:48:25+02:00](https://github.com/leanprover-community/mathlib/commit/5df7cac)
refactor(data/int/gcd): move int gcd proofs to the GCD theory
#### Estimated changes
Modified data/int/basic.lean
- \- *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \- *theorem* nat_abs_div
- \- *theorem* nat_abs_dvd_abs_iff
- \- *theorem* xgcd_zero_left
- \- *theorem* xgcd_aux_rec
- \- *theorem* xgcd_aux_fst
- \- *theorem* xgcd_aux_val
- \- *theorem* xgcd_val
- \- *theorem* xgcd_aux_P
- \- *theorem* gcd_eq_gcd_ab
- \- *def* xgcd_aux
- \- *def* xgcd
- \- *def* gcd_a
- \- *def* gcd_b

Modified data/int/gcd.lean
- \+ *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+ *theorem* xgcd_zero_left
- \+ *theorem* xgcd_aux_rec
- \+ *theorem* xgcd_aux_fst
- \+ *theorem* xgcd_aux_val
- \+ *theorem* xgcd_val
- \+ *theorem* xgcd_aux_P
- \+ *theorem* gcd_eq_gcd_ab
- \+ *theorem* nat_abs_div
- \+ *theorem* nat_abs_dvd_abs_iff
- \+/\- *theorem* dvd_of_mul_dvd_mul_left
- \+/\- *theorem* dvd_of_mul_dvd_mul_right
- \+/\- *theorem* gcd_dvd_left
- \+/\- *theorem* gcd_dvd
- \+/\- *theorem* gcd_comm
- \+/\- *theorem* gcd_mul_right
- \+/\- *theorem* lcm_one_right
- \+/\- *theorem* gcd_dvd_left
- \+/\- *theorem* gcd_dvd
- \+/\- *theorem* gcd_comm
- \+/\- *theorem* gcd_mul_right
- \+/\- *theorem* lcm_one_right
- \+/\- *theorem* dvd_of_mul_dvd_mul_left
- \+/\- *theorem* dvd_of_mul_dvd_mul_right
- \+ *def* xgcd_aux
- \+ *def* xgcd
- \+ *def* gcd_a
- \+ *def* gcd_b

Modified data/nat/modeq.lean

Modified data/padics/padic_norm.lean

Modified data/zmod.lean



## [2018-08-31 17:48:25+02:00](https://github.com/leanprover-community/mathlib/commit/a89f28e)
feat(data/int/gcd): extended gcd to integers ([#218](https://github.com/leanprover-community/mathlib/pull/218))
Resurrected by @johoelzl. The original commit was not available anymore.
#### Estimated changes
Modified data/int/basic.lean
- \+/\- *theorem* nat_abs_neg_of_nat
- \+ *theorem* nat_abs_div
- \+ *theorem* nat_abs_dvd_abs_iff
- \+/\- *theorem* nat_abs_neg_of_nat

Created data/int/gcd.lean
- \+ *theorem* gcd_self
- \+ *theorem* gcd_zero_left
- \+ *theorem* gcd_zero_right
- \+ *theorem* gcd_dvd_left
- \+ *theorem* gcd_dvd_right
- \+ *theorem* gcd_dvd
- \+ *theorem* dvd_gcd
- \+ *theorem* gcd_comm
- \+ *theorem* gcd_assoc
- \+ *theorem* gcd_one_left
- \+ *theorem* gcd_one_right
- \+ *theorem* gcd_mul_left
- \+ *theorem* gcd_mul_right
- \+ *theorem* gcd_pos_of_non_zero_left
- \+ *theorem* gcd_pos_of_non_zero_right
- \+ *theorem* eq_zero_of_gcd_eq_zero_left
- \+ *theorem* eq_zero_of_gcd_eq_zero_right
- \+ *theorem* gcd_div
- \+ *theorem* gcd_dvd_gcd_of_dvd_left
- \+ *theorem* gcd_dvd_gcd_of_dvd_right
- \+ *theorem* gcd_dvd_gcd_mul_left
- \+ *theorem* gcd_dvd_gcd_mul_right
- \+ *theorem* gcd_dvd_gcd_mul_left_right
- \+ *theorem* gcd_dvd_gcd_mul_right_right
- \+ *theorem* gcd_eq_left
- \+ *theorem* gcd_eq_right
- \+ *theorem* lcm_def
- \+ *theorem* lcm_comm
- \+ *theorem* lcm_zero_left
- \+ *theorem* lcm_zero_right
- \+ *theorem* lcm_one_left
- \+ *theorem* lcm_one_right
- \+ *theorem* lcm_self
- \+ *theorem* dvd_lcm_left
- \+ *theorem* dvd_lcm_right
- \+ *theorem* gcd_mul_lcm
- \+ *theorem* lcm_dvd
- \+ *theorem* lcm_assoc
- \+ *theorem* dvd_of_mul_dvd_mul_left
- \+ *theorem* dvd_of_mul_dvd_mul_right
- \+ *def* lcm



## [2018-08-31 14:44:58+02:00](https://github.com/leanprover-community/mathlib/commit/ee9bf5c)
feat(data/equiv): equiv_congr and perm_congr
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *lemma* trans_assoc
- \+ *def* equiv_congr
- \+ *def* perm_congr



## [2018-08-31 09:14:34+02:00](https://github.com/leanprover-community/mathlib/commit/4068d00)
feat(data/nat): simp rules for find_greatest
#### Estimated changes
Modified data/nat/basic.lean
- \+ *lemma* find_greatest_zero
- \+ *lemma* find_greatest_eq
- \+ *lemma* find_greatest_of_not



## [2018-08-31 01:45:14+02:00](https://github.com/leanprover-community/mathlib/commit/2946088)
feat(tactic/explode): line by line proof display for proof terms
#### Estimated changes
Modified tactic/basic.lean

Created tactic/explode.lean
- \+ *def* head'



## [2018-08-30 18:39:48+02:00](https://github.com/leanprover-community/mathlib/commit/86c955e)
feat(data/nat): find_greatest is always bounded
#### Estimated changes
Modified data/nat/basic.lean
- \+ *lemma* find_greatest_le



## [2018-08-30 17:30:19+02:00](https://github.com/leanprover-community/mathlib/commit/c238aad)
refactor(data/nat): simplify find_greatest; fix namespace nat.nat.find_greatest -> nat.find_greatest
#### Estimated changes
Modified data/nat/basic.lean
- \+ *lemma* find_greatest_spec_and_le
- \+ *lemma* find_greatest_spec
- \+ *lemma* le_find_greatest
- \+ *lemma* find_greatest_is_greatest
- \+/\- *lemma* nat.div_mul_div
- \- *lemma* nat.find_greatest_spec
- \- *lemma* nat.find_greatest_is_greatest
- \+/\- *lemma* nat.div_mul_div
- \+/\- *theorem* mul_pow
- \+/\- *theorem* mul_pow



## [2018-08-30 15:34:45+02:00](https://github.com/leanprover-community/mathlib/commit/83edcc0)
refactor(data/nat,int): separate int from nat, i.e. do not import any int theory in nat
#### Estimated changes
Modified data/int/basic.lean
- \+/\- *lemma* nat_abs_ne_zero_of_ne_zero
- \+/\- *lemma* dvd_nat_abs_of_of_nat_dvd
- \+/\- *lemma* pow_div_of_le_of_pow_div_int
- \+ *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+/\- *lemma* dvd_nat_abs_of_of_nat_dvd
- \+/\- *lemma* pow_div_of_le_of_pow_div_int
- \+/\- *lemma* nat_abs_ne_zero_of_ne_zero
- \+/\- *theorem* nat_abs_add_le
- \+/\- *theorem* nat_abs_neg_of_nat
- \+/\- *theorem* nat_abs_mul
- \+/\- *theorem* neg_succ_of_nat_eq'
- \+ *theorem* coe_nat_dvd_left
- \+ *theorem* coe_nat_dvd_right
- \+ *theorem* xgcd_zero_left
- \+ *theorem* xgcd_aux_rec
- \+ *theorem* xgcd_aux_fst
- \+ *theorem* xgcd_aux_val
- \+ *theorem* xgcd_val
- \+ *theorem* xgcd_aux_P
- \+ *theorem* gcd_eq_gcd_ab
- \+/\- *theorem* nat_abs_add_le
- \+/\- *theorem* nat_abs_neg_of_nat
- \+/\- *theorem* nat_abs_mul
- \+/\- *theorem* neg_succ_of_nat_eq'
- \+ *def* xgcd_aux
- \+ *def* xgcd
- \+ *def* gcd_a
- \+ *def* gcd_b

Modified data/nat/gcd.lean
- \- *theorem* xgcd_zero_left
- \- *theorem* xgcd_aux_rec
- \- *theorem* xgcd_aux_fst
- \- *theorem* xgcd_aux_val
- \- *theorem* xgcd_val
- \- *theorem* xgcd_aux_P
- \- *theorem* gcd_eq_gcd_ab
- \- *def* xgcd_aux
- \- *def* xgcd
- \- *def* gcd_a
- \- *def* gcd_b

Modified data/nat/prime.lean
- \- *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul_int

Modified data/padics/padic_norm.lean

Modified data/zmod.lean



## [2018-08-30 14:55:56+02:00](https://github.com/leanprover-community/mathlib/commit/d245165)
refactor(algebra): add more facts about units
#### Estimated changes
Modified algebra/field.lean
- \- *theorem* ne_zero

Modified algebra/group.lean
- \+ *def* units.mk_of_mul_eq_one

Modified algebra/ring.lean
- \+ *lemma* zero_dvd_iff_eq_zero
- \+ *lemma* coe_dvd
- \+ *lemma* dvd_coe_mul
- \+ *lemma* dvd_coe
- \+ *lemma* coe_mul_dvd
- \+ *theorem* ne_zero



## [2018-08-30 13:27:07+02:00](https://github.com/leanprover-community/mathlib/commit/b4b05dd)
feat(logic/basic): introduce pempty
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *def* equiv_pempty
- \+ *def* false_equiv_pempty
- \+ *def* pempty_equiv_pempty
- \+ *def* pempty_arrow_equiv_unit
- \+ *def* prod_pempty
- \+ *def* pempty_prod
- \+ *def* sum_pempty
- \+ *def* pempty_sum
- \- *def* arrow_empty_unit

Modified data/fintype.lean
- \+ *theorem* fintype.univ_pempty
- \+ *theorem* fintype.card_pempty

Modified logic/basic.lean
- \+ *def* pempty.elim

Modified set_theory/cardinal.lean

Modified tactic/auto_cases.lean



## [2018-08-29 15:07:11+02:00](https://github.com/leanprover-community/mathlib/commit/afd1c06)
feat(algebra/group): is_add_group_hom
#### Estimated changes
Modified algebra/group.lean
- \+ *lemma* sub



## [2018-08-29 14:48:07+02:00](https://github.com/leanprover-community/mathlib/commit/b0aadaa)
cleanup(analysis/bounded_linear_maps): some reorganization
#### Estimated changes
Created analysis/bounded_linear_maps.lean
- \+ *lemma* mul_inv_eq'
- \+ *lemma* is_linear_map.with_bound
- \+ *lemma* zero
- \+ *lemma* id
- \+ *lemma* smul
- \+ *lemma* neg
- \+ *lemma* add
- \+ *lemma* sub
- \+ *lemma* comp
- \+ *lemma* tendsto
- \+ *lemma* continuous
- \+ *lemma* lim_zero_bounded_linear_map
- \+ *lemma* bounded_continuous_linear_map

Deleted analysis/continuous_linear_maps.lean
- \- *lemma* zero
- \- *lemma* id
- \- *lemma* smul
- \- *lemma* neg
- \- *lemma* add
- \- *lemma* sub
- \- *lemma* comp
- \- *lemma* continuous
- \- *lemma* lim_zero_bounded_linear_map
- \- *lemma* bounded_continuous_linear_map
- \- *def* is_bounded_linear_map

Modified analysis/metric_space.lean
- \+ *theorem* exists_delta_of_continuous

Modified analysis/normed_space.lean
- \+ *lemma* real.norm_eq_abs



## [2018-08-29 14:48:07+02:00](https://github.com/leanprover-community/mathlib/commit/21a9355)
feat(analysis/continuous_linear_maps)
#### Estimated changes
Created analysis/continuous_linear_maps.lean
- \+ *lemma* zero
- \+ *lemma* id
- \+ *lemma* smul
- \+ *lemma* neg
- \+ *lemma* add
- \+ *lemma* sub
- \+ *lemma* comp
- \+ *lemma* continuous
- \+ *lemma* lim_zero_bounded_linear_map
- \+ *lemma* bounded_continuous_linear_map
- \+ *def* is_bounded_linear_map



## [2018-08-29 14:38:32+02:00](https://github.com/leanprover-community/mathlib/commit/49f700c)
feat(analysis/topology/uniform_space): prepare for completions ([#297](https://github.com/leanprover-community/mathlib/pull/297))
#### Estimated changes
Modified analysis/topology/uniform_space.lean
- \+ *lemma* uniform_continuous_quotient
- \+ *lemma* uniform_continuous_quotient_lift
- \+ *lemma* uniformity_quotient
- \+ *lemma* separated_of_uniform_continuous
- \+ *lemma* eq_of_separated_of_uniform_continuous
- \+/\- *lemma* uniform_continuous.prod_mk
- \+ *lemma* uniform_continuous.prod_mk_left
- \+ *lemma* uniform_continuous.prod_mk_right
- \+ *lemma* uniform_continuous_quotient_lift₂
- \+ *lemma* separation_prod
- \+/\- *lemma* uniform_continuous.prod_mk



## [2018-08-29 02:55:13+02:00](https://github.com/leanprover-community/mathlib/commit/0c11112)
feat(logic/function): adds uncurry_def ([#293](https://github.com/leanprover-community/mathlib/pull/293))
#### Estimated changes
Modified logic/function.lean
- \+ *lemma* uncurry_def



## [2018-08-29 02:53:42+02:00](https://github.com/leanprover-community/mathlib/commit/b82ba3c)
feat(data/multiset): multisets are traversable using commutative, applicative functors ([#220](https://github.com/leanprover-community/mathlib/pull/220))
#### Estimated changes
Modified category/applicative.lean

Modified category/traversable/instances.lean
- \+ *lemma* traverse_append
- \- *lemma* list.id_traverse
- \- *lemma* list.comp_traverse
- \- *lemma* list.traverse_eq_map_id
- \- *lemma* list.naturality

Modified category/traversable/lemmas.lean
- \+ *lemma* map_traverse'

Modified data/multiset.lean
- \+ *lemma* coe_append_eq_add_coe
- \+ *lemma* coe_list_cons_eq_cons_coe
- \+ *lemma* coe_traverse_cons
- \+ *lemma* coe_traverse_cons_swap
- \+ *lemma* lift_beta
- \+ *lemma* map_comp_coe
- \+ *lemma* id_traverse
- \+ *lemma* comp_traverse
- \+ *lemma* map_traverse
- \+ *lemma* traverse_map
- \+ *lemma* naturality
- \+ *def* traverse



## [2018-08-29 02:46:53+02:00](https://github.com/leanprover-community/mathlib/commit/3e38b73)
feat(analysis/topology): density and continuity lemmas ([#292](https://github.com/leanprover-community/mathlib/pull/292))
Still from the perfectoid project
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* self_sub_closure_image_preimage_of_open
- \+ *lemma* closure_image_nhds_of_nhds
- \+ *lemma* tendsto_vmap_nhds_nhds

Modified analysis/topology/topological_space.lean
- \+ *lemma* dense_iff_inter_open
- \+ *lemma* quotient_dense_of_dense



## [2018-08-29 02:45:15+02:00](https://github.com/leanprover-community/mathlib/commit/4eca29f)
doc(docs/howto-contribute.md): How to contribute to mathlib ([#291](https://github.com/leanprover-community/mathlib/pull/291))
#### Estimated changes
Modified README.md

Created docs/howto-contribute.md



## [2018-08-29 02:42:39+02:00](https://github.com/leanprover-community/mathlib/commit/79bb95c)
feat(analysis/topology, data/set): some zerology ([#295](https://github.com/leanprover-community/mathlib/pull/295))
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* closure_empty_iff

Modified data/set/basic.lean
- \+ *lemma* nonempty_iff_univ_ne_empty
- \+ *lemma* nonempty_of_nonempty_range



## [2018-08-29 02:26:04+02:00](https://github.com/leanprover-community/mathlib/commit/49fb2db)
fix(docs/style): precise a style rule and fixes a github markdown issue ([#290](https://github.com/leanprover-community/mathlib/pull/290))
#### Estimated changes
Modified docs/style.md



## [2018-08-29 00:28:03+02:00](https://github.com/leanprover-community/mathlib/commit/bab3813)
feat(ring_theory/PID): PIDs and xgcd for ED ([#298](https://github.com/leanprover-community/mathlib/pull/298))
#### Estimated changes
Modified algebra/euclidean_domain.lean
- \+ *lemma* mod_eq_sub_mul_div
- \+ *theorem* xgcd_zero_left
- \+ *theorem* xgcd_aux_rec
- \+ *theorem* xgcd_aux_fst
- \+ *theorem* xgcd_aux_val
- \+ *theorem* xgcd_val
- \+ *theorem* xgcd_aux_P
- \+ *theorem* gcd_eq_gcd_ab
- \+ *def* xgcd_aux
- \+ *def* xgcd
- \+ *def* gcd_a
- \+ *def* gcd_b

Modified algebra/ring.lean
- \+ *lemma* zero_dvd_iff

Created ring_theory/PID.lean
- \+ *lemma* generator_generates
- \+ *lemma* generator_mem
- \+ *lemma* mem_iff_generator_dvd
- \+ *lemma* eq_trivial_iff_generator_eq_zero
- \+ *lemma* mod_mem_iff
- \+ *lemma* is_prime_ideal.to_maximal_ideal

Modified ring_theory/ideals.lean
- \+ *lemma* mem_trivial
- \+/\- *lemma* is_proper_ideal_iff_one_not_mem
- \+/\- *lemma* eq_zero_iff_mem
- \+/\- *lemma* is_proper_ideal_iff_one_not_mem
- \+/\- *lemma* eq_zero_iff_mem
- \+/\- *theorem* is_maximal_ideal.mk
- \+/\- *theorem* is_maximal_ideal.mk



## [2018-08-28 20:10:13+02:00](https://github.com/leanprover-community/mathlib/commit/cd73115)
refactor(data/set/basic): clean up [#288](https://github.com/leanprover-community/mathlib/pull/288) and [#289](https://github.com/leanprover-community/mathlib/pull/289)
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* mk_mem_prod
- \- *lemma* mem_prod'
- \+/\- *theorem* univ_prod_univ
- \+/\- *theorem* univ_prod_univ

Modified order/filter.lean
- \+ *lemma* sInter_vmap_sets
- \+/\- *lemma* vmap_eq_of_inverse
- \- *lemma* inter_vmap_sets
- \+/\- *lemma* vmap_eq_of_inverse



## [2018-08-28 20:09:53+02:00](https://github.com/leanprover-community/mathlib/commit/8d3bd80)
feat(tactic/tidy): add tidy tactic ([#285](https://github.com/leanprover-community/mathlib/pull/285))
#### Estimated changes
Modified docs/tactics.md

Created tactic/auto_cases.lean

Modified tactic/basic.lean

Created tactic/chain.lean

Modified tactic/interactive.lean

Created tactic/tidy.lean

Modified tests/tactics.lean

Created tests/tidy.lean
- \+ *def* tidy_test_0
- \+ *def* tidy_test_1
- \+ *def* d
- \+ *def* f



## [2018-08-28 19:40:10+02:00](https://github.com/leanprover-community/mathlib/commit/9ad32e7)
feat(order/filter): More lemmas from perfectoid project ([#289](https://github.com/leanprover-community/mathlib/pull/289))
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* prod_sub_preimage_iff
- \- *lemma* sub_preimage_iff

Modified order/filter.lean
- \+ *lemma* inter_vmap_sets
- \+ *lemma* vmap_eq_of_inverse
- \+ *lemma* tendsto_prod_iff
- \+ *lemma* tendsto_prod_self_iff



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
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \- *lemma* map_id_lemma
- \- *lemma* map_comp_lemma

Modified category_theory/functor_category.lean
- \+/\- *lemma* id_app
- \+/\- *lemma* comp_app
- \+/\- *lemma* app_naturality
- \+/\- *lemma* naturality_app
- \+/\- *lemma* id_app
- \+/\- *lemma* comp_app
- \+/\- *lemma* app_naturality
- \+/\- *lemma* naturality_app

Modified category_theory/natural_transformation.lean
- \+ *lemma* naturality
- \+/\- *lemma* vcomp_assoc
- \+/\- *lemma* exchange
- \- *lemma* naturality_lemma
- \+/\- *lemma* vcomp_assoc
- \+/\- *lemma* exchange

Modified category_theory/opposites.lean

Modified category_theory/products.lean
- \+/\- *lemma* prod_id
- \+/\- *lemma* prod_comp
- \+/\- *lemma* prod_obj
- \+/\- *lemma* prod_map
- \+/\- *lemma* prod_app
- \+/\- *lemma* prod_id
- \+/\- *lemma* prod_comp
- \+/\- *lemma* prod_obj
- \+/\- *lemma* prod_map
- \+/\- *lemma* prod_app

Modified category_theory/types.lean
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_id
- \+/\- *lemma* naturality
- \+/\- *lemma* map_comp
- \+/\- *lemma* map_id
- \+/\- *lemma* naturality

Modified docs/tactics.md

Modified tactic/restate_axiom.lean

Created tests/restate_axiom.lean



## [2018-08-28 17:33:14+02:00](https://github.com/leanprover-community/mathlib/commit/ed5a338)
feat(data/set/basic): some more basic set lemmas ([#288](https://github.com/leanprover-community/mathlib/pull/288))
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* inter_singleton_ne_empty
- \+ *lemma* preimage_subset_iff
- \+ *lemma* mem_prod'
- \+ *lemma* sub_preimage_iff



## [2018-08-28 15:08:37+02:00](https://github.com/leanprover-community/mathlib/commit/39ffeab)
feat(analysis): add normed spaces
#### Estimated changes
Created analysis/normed_space.lean
- \+ *lemma* squeeze_zero
- \+ *lemma* dist_eq_norm
- \+ *lemma* dist_zero_right
- \+ *lemma* norm_triangle
- \+ *lemma* norm_nonneg
- \+ *lemma* norm_eq_zero
- \+ *lemma* norm_zero
- \+ *lemma* norm_pos_iff
- \+ *lemma* norm_le_zero_iff
- \+ *lemma* norm_neg
- \+ *lemma* abs_norm_sub_norm_le
- \+ *lemma* dist_norm_norm_le
- \+ *lemma* coe_nnnorm
- \+ *lemma* nndist_eq_nnnorm
- \+ *lemma* nnnorm_eq_zero
- \+ *lemma* nnnorm_zero
- \+ *lemma* nnnorm_triangle
- \+ *lemma* nnnorm_neg
- \+ *lemma* nndist_nnnorm_nnnorm_le
- \+ *lemma* norm_fst_le
- \+ *lemma* norm_snd_le
- \+ *lemma* tendsto_iff_norm_tendsto_zero
- \+ *lemma* lim_norm
- \+ *lemma* lim_norm_zero
- \+ *lemma* continuous_norm
- \+ *lemma* norm_mul
- \+ *lemma* norm_smul
- \+ *lemma* nnnorm_smul
- \+ *lemma* tendsto_smul
- \+ *def* nnnorm



## [2018-08-28 15:05:42+02:00](https://github.com/leanprover-community/mathlib/commit/2b9c9a8)
refactor(analysis): add nndist; add finite product of metric spaces; prepare for normed spaces
#### Estimated changes
Modified analysis/complex.lean

Modified analysis/ennreal.lean
- \- *lemma* tendsto_nhds_generate_from
- \- *lemma* prod_mem_nhds_sets
- \- *lemma* nhds_swap
- \- *lemma* tendsto_prod_mk_nhds

Modified analysis/metric_space.lean
- \+ *lemma* nndist_self
- \+ *lemma* coe_dist
- \+ *lemma* dist_pi_def
- \+ *theorem* eq_of_nndist_eq_zero
- \+ *theorem* nndist_comm
- \+ *theorem* nndist_eq_zero
- \+ *theorem* zero_eq_nndist
- \+ *theorem* nndist_triangle
- \+ *theorem* nndist_triangle_left
- \+ *theorem* nndist_triangle_right
- \+ *def* nndist
- \- *def* dist

Modified analysis/nnreal.lean

Modified analysis/topology/continuity.lean
- \+ *lemma* embedding.map_nhds_eq
- \+ *lemma* prod_mem_nhds_sets
- \+ *lemma* nhds_swap
- \+ *lemma* tendsto_prod_mk_nhds

Modified analysis/topology/topological_space.lean
- \+ *lemma* tendsto_nhds_generate_from

Modified data/finset.lean
- \+ *lemma* image_const
- \+/\- *lemma* sup_insert
- \+/\- *lemma* sup_singleton
- \+/\- *lemma* sup_union
- \+ *lemma* sup_le_iff
- \+/\- *lemma* inf_insert
- \+/\- *lemma* inf_singleton
- \+/\- *lemma* inf_union
- \+ *lemma* le_inf_iff
- \+/\- *lemma* sup_insert
- \+/\- *lemma* sup_singleton
- \+/\- *lemma* sup_union
- \+/\- *lemma* inf_insert
- \+/\- *lemma* inf_singleton
- \+/\- *lemma* inf_union
- \+ *theorem* max_singleton'

Modified data/real/nnreal.lean
- \+ *lemma* bot_eq_zero
- \+ *lemma* mul_sup
- \+ *lemma* mul_finset_sup



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
- \+ *lemma* Inf_nat_def
- \+ *lemma* Sup_nat_def



## [2018-08-28 10:22:25+02:00](https://github.com/leanprover-community/mathlib/commit/de67f54)
feat(data/real): cauchy sequence limit lemmas ([#61](https://github.com/leanprover-community/mathlib/pull/61))
#### Estimated changes
Modified data/real/basic.lean
- \+ *lemma* eq_lim_of_const_equiv
- \+ *lemma* lim_eq_of_equiv_const
- \+ *lemma* lim_eq_lim_of_equiv
- \+ *lemma* lim_const
- \+ *lemma* lim_add
- \+ *lemma* lim_mul_lim
- \+ *lemma* lim_mul
- \+ *lemma* lim_neg
- \+ *lemma* lim_eq_zero_iff
- \+ *lemma* lim_inv

Modified data/real/cau_seq.lean
- \+ *theorem* const_inv



## [2018-08-28 00:08:50+02:00](https://github.com/leanprover-community/mathlib/commit/c420885)
fix(tactic/interactive): try reflexivity after substs ([#275](https://github.com/leanprover-community/mathlib/pull/275))
This brings `substs` closer to being equivalent to a sequence of `subst`.
#### Estimated changes
Modified tactic/interactive.lean



## [2018-08-28 00:06:47+02:00](https://github.com/leanprover-community/mathlib/commit/bca8d49)
chore(data/array, data/buffer): Array and buffer cleanup ([#277](https://github.com/leanprover-community/mathlib/pull/277))
#### Estimated changes
Modified data/array/lemmas.lean
- \+ *lemma* push_back_rev_list_aux
- \- *lemma* push_back_rev_list_core
- \+/\- *theorem* to_list_of_heq
- \+ *theorem* rev_list_reverse_aux
- \+/\- *theorem* rev_list_reverse
- \+/\- *theorem* to_list_reverse
- \+/\- *theorem* mem.def
- \+ *theorem* mem_rev_list_aux
- \+/\- *theorem* mem_rev_list
- \+/\- *theorem* mem_to_list
- \+/\- *theorem* rev_list_foldr_aux
- \+/\- *theorem* rev_list_foldr
- \+/\- *theorem* to_list_foldl
- \+/\- *theorem* rev_list_length_aux
- \+ *theorem* to_list_nth_le_aux
- \+/\- *theorem* to_list_nth_le
- \+/\- *theorem* to_list_nth_le'
- \+/\- *theorem* to_list_nth
- \+/\- *theorem* write_to_list
- \+/\- *theorem* mem_to_list_enum
- \+/\- *theorem* push_back_rev_list
- \+/\- *theorem* push_back_to_list
- \+/\- *theorem* read_foreach_aux
- \+/\- *theorem* read_foreach
- \+/\- *theorem* read_map
- \+/\- *theorem* read_map₂
- \+/\- *theorem* rev_list_foldr_aux
- \+/\- *theorem* rev_list_foldr
- \+/\- *theorem* mem.def
- \- *theorem* rev_list_reverse_core
- \+/\- *theorem* rev_list_reverse
- \+/\- *theorem* to_list_reverse
- \+/\- *theorem* rev_list_length_aux
- \- *theorem* to_list_nth_le_core
- \+/\- *theorem* to_list_nth_le
- \+/\- *theorem* to_list_nth_le'
- \+/\- *theorem* to_list_nth
- \+/\- *theorem* to_list_foldl
- \+/\- *theorem* write_to_list
- \- *theorem* mem_rev_list_core
- \+/\- *theorem* mem_rev_list
- \+/\- *theorem* mem_to_list
- \+/\- *theorem* mem_to_list_enum
- \+/\- *theorem* to_list_of_heq
- \+/\- *theorem* push_back_rev_list
- \+/\- *theorem* push_back_to_list
- \+/\- *theorem* read_foreach_aux
- \+/\- *theorem* read_foreach
- \+/\- *theorem* read_map
- \+/\- *theorem* read_map₂
- \+/\- *def* d_array_equiv_fin
- \+/\- *def* d_array_equiv_fin

Modified data/buffer/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* to_list_append_list
- \+/\- *lemma* ext
- \+/\- *lemma* to_list_append_list

Modified data/hash_map.lean



## [2018-08-27 23:02:59+02:00](https://github.com/leanprover-community/mathlib/commit/c52b317)
refactor(data/finsupp): generalise finsupp.to_module ([#284](https://github.com/leanprover-community/mathlib/pull/284))
#### Estimated changes
Modified data/finsupp.lean
- \+ *lemma* smul_apply'
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_apply
- \+ *def* to_has_scalar'
- \+/\- *def* to_module
- \+/\- *def* to_has_scalar
- \+/\- *def* to_has_scalar
- \+/\- *def* to_module

Modified data/polynomial.lean

Modified linear_algebra/basic.lean

Modified linear_algebra/multivariate_polynomial.lean



## [2018-08-27 16:48:59+02:00](https://github.com/leanprover-community/mathlib/commit/9aa2bb0)
feat(data/fin): last ([#273](https://github.com/leanprover-community/mathlib/pull/273))
#### Estimated changes
Modified data/fin.lean
- \+ *theorem* le_last
- \+ *def* last



## [2018-08-27 16:48:29+02:00](https://github.com/leanprover-community/mathlib/commit/a3a9e24)
bug(tactic/interactive): make `solve_by_elim` fail on no goals ([#279](https://github.com/leanprover-community/mathlib/pull/279))
#### Estimated changes
Modified tactic/basic.lean

Modified tests/tactics.lean



## [2018-08-27 16:46:13+02:00](https://github.com/leanprover-community/mathlib/commit/c13a771)
feat(data/list): join_eq_nil, join_repeat_nil ([#274](https://github.com/leanprover-community/mathlib/pull/274))
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* join_eq_nil
- \+ *theorem* join_repeat_nil



## [2018-08-27 14:37:37+02:00](https://github.com/leanprover-community/mathlib/commit/92e9d64)
feat(category_theory): restating functor.map and nat_trans.app ([#268](https://github.com/leanprover-community/mathlib/pull/268))
#### Estimated changes
Modified category_theory/functor.lean
- \+ *lemma* map_id_lemma
- \+ *lemma* map_comp_lemma
- \+ *lemma* mk_obj
- \+ *lemma* mk_map
- \+/\- *lemma* comp_map
- \- *lemma* coe_def
- \+/\- *lemma* comp_map
- \+ *def* map

Modified category_theory/functor_category.lean
- \+/\- *lemma* comp_app
- \+/\- *lemma* app_naturality
- \+/\- *lemma* naturality_app
- \+/\- *lemma* comp_app
- \+/\- *lemma* app_naturality
- \+/\- *lemma* naturality_app

Modified category_theory/natural_transformation.lean
- \+ *lemma* mk_app
- \+ *lemma* naturality_lemma
- \+/\- *lemma* vcomp_assoc
- \+/\- *lemma* hcomp_app
- \+/\- *lemma* exchange
- \- *lemma* coe_def
- \+/\- *lemma* vcomp_assoc
- \+/\- *lemma* hcomp_app
- \+/\- *lemma* exchange

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
- \+ *lemma* dvd_prod

Modified data/nat/prime.lean
- \+ *lemma* mem_factors_iff_dvd
- \- *lemma* mem_factors_of_dvd



## [2018-08-22 19:37:12+02:00](https://github.com/leanprover-community/mathlib/commit/974987c)
refactor(data/nat/prime): cleanup exists_infinite_primes ([#271](https://github.com/leanprover-community/mathlib/pull/271))
* removing unnecessary initial step
* giving names to ambiguous copies of `this`
#### Estimated changes
Modified data/nat/prime.lean
- \+/\- *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+/\- *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul_int
- \+/\- *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+/\- *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul_int
- \+/\- *theorem* exists_infinite_primes
- \+/\- *theorem* exists_infinite_primes



## [2018-08-21 22:05:08+02:00](https://github.com/leanprover-community/mathlib/commit/b3fc801)
refactor(data/real/nnreal): derive order structure for ennreal from with_top nnreal
#### Estimated changes
Modified algebra/ordered_group.lean
- \+ *lemma* zero_lt_top
- \+ *lemma* zero_lt_coe
- \+ *lemma* add_eq_top
- \+ *lemma* le_add_left
- \+ *lemma* le_add_right
- \+ *lemma* with_top.add_lt_add_iff_left
- \- *lemma* coe_lt_coe
- \- *lemma* bot_lt_some
- \- *theorem* top_ne_coe
- \- *theorem* coe_ne_top

Modified algebra/ordered_ring.lean
- \+/\- *lemma* mul_le_one
- \+ *lemma* top_mul_top
- \+ *lemma* coe_mul
- \+/\- *lemma* mul_le_one
- \- *lemma* bind_comm
- \- *lemma* none_eq_top
- \- *lemma* some_eq_coe
- \- *lemma* coe_mul_coe

Modified analysis/ennreal.lean
- \+ *lemma* tendsto_nhds_generate_from
- \+ *lemma* prod_mem_nhds_sets
- \+ *lemma* nhds_swap
- \+ *lemma* tendsto_prod_mk_nhds
- \+ *lemma* embedding_coe
- \+ *lemma* is_open_ne_top
- \+ *lemma* coe_image_univ_mem_nhds
- \+ *lemma* tendsto_coe
- \+ *lemma* continuous_coe
- \+ *lemma* nhds_coe
- \+ *lemma* nhds_coe_coe
- \+ *lemma* tendsto_to_nnreal
- \+ *lemma* coe_nat
- \+ *lemma* tendsto_nhds_top
- \+ *lemma* nhds_top
- \+/\- *lemma* nhds_of_real_eq_map_of_real_nhds_nonneg
- \+/\- *lemma* sub_supr
- \+ *lemma* exists_le_is_sum_of_le
- \+ *lemma* has_sum_of_le
- \+/\- *lemma* has_sum_of_nonneg_of_le
- \- *lemma* continuous_of_real
- \- *lemma* tendsto_of_real
- \- *lemma* tendsto_of_ennreal
- \- *lemma* nhds_of_real_eq_map_of_real_nhds
- \+/\- *lemma* nhds_of_real_eq_map_of_real_nhds_nonneg
- \- *lemma* supr_of_real
- \- *lemma* infi_of_real
- \- *lemma* Inf_add
- \- *lemma* infi_add
- \- *lemma* add_infi
- \- *lemma* infi_add_infi
- \- *lemma* infi_sum
- \+/\- *lemma* sub_supr
- \- *lemma* sub_infi
- \- *lemma* tendsto_of_real_iff
- \- *lemma* tendsto_coe_iff
- \- *lemma* coe_mul
- \- *lemma* coe_one
- \- *lemma* coe_eq_coe
- \+/\- *lemma* has_sum_of_nonneg_of_le
- \- *lemma* nnreal.has_sum_of_le
- \- *theorem* exists_pos_sum_of_encodable

Modified analysis/limits.lean
- \+ *theorem* exists_pos_sum_of_encodable
- \+ *theorem* exists_pos_sum_of_encodable

Modified analysis/measure_theory/lebesgue_measure.lean

Modified analysis/measure_theory/measure_space.lean

Modified analysis/measure_theory/outer_measure.lean

Modified analysis/nnreal.lean
- \+ *lemma* continuous_of_real
- \+ *lemma* continuous_coe
- \+ *lemma* tendsto_of_real
- \+ *lemma* tendsto_sub
- \+ *lemma* tsum_coe

Modified analysis/probability_mass_function.lean

Modified analysis/topology/continuity.lean
- \+/\- *lemma* embedding.tendsto_nhds_iff
- \+/\- *lemma* embedding.tendsto_nhds_iff

Modified data/option.lean
- \+ *lemma* bind_comm

Modified data/real/basic.lean
- \+ *theorem* Sup_empty
- \+ *theorem* Sup_of_not_bdd_above
- \+ *theorem* Inf_empty
- \+ *theorem* Inf_of_not_bdd_below
- \+/\- *def* of_rat
- \+/\- *def* of_rat

Modified data/real/ennreal.lean
- \+ *lemma* none_eq_top
- \+ *lemma* some_eq_coe
- \+ *lemma* to_nnreal_coe
- \+ *lemma* coe_to_nnreal
- \+ *lemma* top_to_nnreal
- \+/\- *lemma* forall_ennreal
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* coe_ne_top
- \+ *lemma* top_ne_coe
- \+ *lemma* zero_ne_top
- \+ *lemma* top_ne_zero
- \+ *lemma* one_ne_top
- \+ *lemma* top_ne_one
- \+ *lemma* coe_eq_coe
- \+ *lemma* coe_le_coe
- \+ *lemma* coe_lt_coe
- \+ *lemma* coe_eq_zero
- \+ *lemma* zero_eq_coe
- \+ *lemma* coe_eq_one
- \+ *lemma* one_eq_coe
- \+ *lemma* coe_add
- \+ *lemma* coe_mul
- \+ *lemma* add_top
- \+ *lemma* top_add
- \+ *lemma* add_eq_top
- \+ *lemma* mul_top
- \+ *lemma* top_mul
- \+ *lemma* top_mul_top
- \+ *lemma* coe_finset_sum
- \+ *lemma* coe_finset_prod
- \+ *lemma* bot_eq_zero
- \+ *lemma* coe_lt_top
- \+ *lemma* not_top_le_coe
- \+ *lemma* zero_lt_coe_iff
- \+ *lemma* one_le_coe_iff
- \+ *lemma* coe_le_one_iff
- \+ *lemma* coe_lt_one_iff
- \+ *lemma* one_lt_zero_iff
- \+ *lemma* le_coe_iff
- \+ *lemma* coe_le_iff
- \+ *lemma* lt_iff_exists_coe
- \+/\- *lemma* not_lt_zero
- \+ *lemma* add_lt_add_iff_left
- \+/\- *lemma* lt_add_right
- \+/\- *lemma* le_of_forall_epsilon_le
- \+ *lemma* coe_Sup
- \+ *lemma* coe_Inf
- \+ *lemma* top_mem_upper_bounds
- \+ *lemma* coe_mem_upper_bounds
- \+ *lemma* mul_eq_mul_left
- \+ *lemma* mul_le_mul_left
- \+ *lemma* coe_sub
- \+ *lemma* top_sub_coe
- \+/\- *lemma* zero_sub
- \+/\- *lemma* sub_infty
- \+/\- *lemma* add_sub_self
- \+/\- *lemma* sub_add_cancel_of_le
- \+ *lemma* div_def
- \+ *lemma* inv_top
- \+ *lemma* inv_coe
- \+ *lemma* inv_eq_top
- \+ *lemma* inv_ne_top
- \+ *lemma* inv_eq_zero
- \+ *lemma* inv_ne_zero
- \+/\- *lemma* inv_inv
- \+ *lemma* le_div_iff_mul_le
- \+ *lemma* div_le_iff_le_mul
- \+ *lemma* inv_le_iff_le_mul
- \+ *lemma* le_inv_iff_mul_le
- \+ *lemma* infi_add
- \+ *lemma* supr_sub
- \+ *lemma* sub_infi
- \+ *lemma* Inf_add
- \+ *lemma* add_infi
- \+ *lemma* infi_add_infi
- \+ *lemma* infi_sum
- \- *lemma* of_ennreal_of_real
- \- *lemma* zero_le_of_ennreal
- \- *lemma* of_real_of_ennreal
- \+/\- *lemma* forall_ennreal
- \- *lemma* of_real_zero
- \- *lemma* of_real_one
- \- *lemma* zero_ne_infty
- \- *lemma* infty_ne_zero
- \- *lemma* of_real_ne_infty
- \- *lemma* infty_ne_of_real
- \- *lemma* of_real_eq_of_real_of
- \- *lemma* of_real_ne_of_real_of
- \- *lemma* of_real_of_nonpos
- \- *lemma* of_real_of_not_nonneg
- \- *lemma* of_real_eq_zero_iff
- \- *lemma* zero_eq_of_real_iff
- \- *lemma* of_real_eq_one_iff
- \- *lemma* one_eq_of_real_iff
- \- *lemma* of_nonneg_real_eq_of_real
- \- *lemma* of_real_add
- \- *lemma* add_infty
- \- *lemma* infty_add
- \- *lemma* of_real_mul_of_real
- \- *lemma* of_real_mul_infty
- \- *lemma* infty_mul_of_real
- \- *lemma* mul_infty
- \- *lemma* infty_mul
- \- *lemma* sum_of_real
- \- *lemma* infty_le_iff
- \- *lemma* le_infty
- \- *lemma* of_real_le_of_real_iff
- \- *lemma* one_le_of_real_iff
- \- *lemma* not_infty_lt
- \- *lemma* of_real_lt_infty
- \- *lemma* le_of_real_iff
- \- *lemma* of_real_lt_of_real_iff
- \- *lemma* lt_iff_exists_of_real
- \- *lemma* le_zero_iff_eq
- \- *lemma* zero_lt_of_real_iff
- \+/\- *lemma* not_lt_zero
- \- *lemma* of_real_le_of_real
- \- *lemma* of_real_lt_of_real_iff_cases
- \- *lemma* le_add_left
- \- *lemma* le_add_right
- \+/\- *lemma* lt_add_right
- \- *lemma* of_real_add_le
- \- *lemma* mul_le_mul
- \+/\- *lemma* le_of_forall_epsilon_le
- \- *lemma* infty_mem_upper_bounds
- \- *lemma* of_real_mem_upper_bounds
- \- *lemma* is_lub_of_real
- \+/\- *lemma* zero_sub
- \+/\- *lemma* sub_infty
- \- *lemma* infty_sub_of_real
- \- *lemma* of_real_sub_of_real
- \+/\- *lemma* add_sub_self
- \+/\- *lemma* sub_add_cancel_of_le
- \- *lemma* inv_infty
- \- *lemma* inv_of_real
- \+/\- *lemma* inv_inv
- \- *theorem* le_def
- \- *def* of_real
- \- *def* of_real
- \- *def* of_ennreal

Modified data/real/nnreal.lean
- \+ *lemma* inv_eq_zero
- \+ *lemma* image_eq_empty
- \+ *lemma* coe_of_real
- \+/\- *lemma* sum_coe
- \+ *lemma* prod_coe
- \+ *lemma* smul_coe
- \+ *lemma* bdd_above_coe
- \+ *lemma* bdd_below_coe
- \+ *lemma* coe_Sup
- \+ *lemma* coe_Inf
- \+ *lemma* le_of_forall_epsilon_le
- \+ *lemma* lt_iff_exists_rat_btwn
- \+ *lemma* zero_le_coe
- \+ *lemma* of_real_zero
- \+ *lemma* zero_lt_of_real
- \+ *lemma* of_real_coe
- \+ *lemma* of_real_le_of_real_iff
- \+ *lemma* of_real_add_of_real
- \+ *lemma* of_real_of_nonpos
- \+ *lemma* of_real_le_of_real
- \+ *lemma* of_real_add_le
- \+ *lemma* mul_eq_mul_left
- \+ *lemma* sub_eq_zero
- \+ *lemma* sub_le_iff_le_add
- \+ *lemma* add_sub_cancel
- \+ *lemma* add_sub_cancel'
- \+ *lemma* sub_add_cancel_of_le
- \+ *lemma* div_def
- \+ *lemma* inv_zero
- \+ *lemma* inv_eq_zero
- \+ *lemma* inv_pos
- \+ *lemma* inv_mul_cancel
- \+ *lemma* mul_inv_cancel
- \+ *lemma* inv_inv
- \+ *lemma* inv_le
- \+ *lemma* inv_le_of_le_mul
- \+ *lemma* le_inv_iff_mul_le
- \+/\- *lemma* sum_coe

Modified order/bounded_lattice.lean
- \+ *lemma* none_eq_bot
- \+ *lemma* some_eq_coe
- \+ *lemma* coe_lt_coe
- \+ *lemma* bot_lt_some
- \+ *lemma* bot_lt_coe
- \+ *lemma* none_eq_top
- \+ *lemma* some_eq_coe
- \+ *lemma* coe_lt_coe
- \+ *lemma* coe_lt_top
- \+ *lemma* not_top_le_coe
- \+ *theorem* coe_eq_coe
- \+ *theorem* coe_eq_coe
- \+ *theorem* top_ne_coe
- \+ *theorem* coe_ne_top
- \+ *theorem* le_coe_iff
- \+ *theorem* coe_le_iff
- \+ *theorem* lt_iff_exists_coe

Modified order/conditionally_complete_lattice.lean
- \+ *lemma* bdd_below_bot
- \+ *lemma* cSup_empty
- \+ *lemma* has_lub
- \+ *lemma* has_glb
- \+ *lemma* is_lub_Sup
- \+ *lemma* is_glb_Inf
- \+ *lemma* coe_Sup
- \+ *lemma* coe_Inf
- \- *lemma* bdd_above_bot

Modified order/filter.lean
- \+ *lemma* tendsto_map'_iff

Modified order/galois_connection.lean



## [2018-08-21 21:22:03+02:00](https://github.com/leanprover-community/mathlib/commit/82512ee)
refactor(analysis/ennreal): use canonically_ordered_comm_semiring (with_top α)
#### Estimated changes
Modified algebra/ordered_group.lean
- \+ *lemma* coe_add
- \+ *lemma* add_top
- \+ *lemma* top_add
- \+ *theorem* top_ne_coe
- \+ *theorem* coe_ne_top

Modified algebra/ordered_ring.lean
- \+ *lemma* mul_le_mul
- \+ *lemma* bind_comm
- \+ *lemma* mul_def
- \+ *lemma* none_eq_top
- \+ *lemma* some_eq_coe
- \+ *lemma* mul_top
- \+ *lemma* top_mul
- \+ *lemma* coe_mul_coe
- \+ *lemma* mul_coe
- \+ *theorem* top_ne_zero
- \+ *theorem* zero_ne_top
- \+ *theorem* coe_eq_zero
- \+ *theorem* zero_eq_coe
- \+ *theorem* coe_zero

Modified data/real/ennreal.lean
- \+/\- *lemma* zero_ne_infty
- \+/\- *lemma* infty_ne_zero
- \+/\- *lemma* of_real_ne_infty
- \+/\- *lemma* infty_ne_of_real
- \+/\- *lemma* zero_ne_infty
- \+/\- *lemma* infty_ne_zero
- \+/\- *lemma* of_real_ne_infty
- \+/\- *lemma* infty_ne_of_real
- \+ *def* ennreal
- \+ *def* of_real

Modified data/real/nnreal.lean



## [2018-08-21 21:22:03+02:00](https://github.com/leanprover-community/mathlib/commit/6f31637)
refactor(analysis/nnreal): split up into data.real and analysis part
#### Estimated changes
Modified analysis/nnreal.lean
- \- *lemma* sum_coe
- \- *def* nnreal

Created data/real/nnreal.lean
- \+ *lemma* sum_coe
- \+ *def* nnreal



## [2018-08-21 21:22:03+02:00](https://github.com/leanprover-community/mathlib/commit/ca1b2d1)
refactor(analysis/measure_theory/measurable_space): derive complete lattice structure from Galois insertion
#### Estimated changes
Modified analysis/measure_theory/measurable_space.lean
- \+ *lemma* generate_from_le_iff
- \+ *lemma* mk_of_closure_sets
- \+ *lemma* is_measurable_bot_iff
- \+ *theorem* is_measurable_top
- \+/\- *theorem* is_measurable_inf
- \+/\- *theorem* is_measurable_inf
- \+ *def* gi_generate_from

Modified analysis/measure_theory/measure_space.lean

Modified analysis/topology/continuity.lean
- \+/\- *lemma* continuous_iff_induced_le
- \+/\- *lemma* continuous_iff_induced_le



## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/29ad1c8)
feat(order/complete_lattice): add rewrite rules for Inf/Sup/infi/supr for pi and Prop
#### Estimated changes
Modified order/complete_lattice.lean
- \+ *lemma* Inf_Prop_eq
- \+ *lemma* Sup_Prop_eq
- \+ *lemma* infi_Prop_eq
- \+ *lemma* supr_Prop_eq
- \+ *lemma* Inf_apply
- \+ *lemma* infi_apply
- \+ *lemma* Sup_apply
- \+ *lemma* supr_apply



## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/202ac15)
refactor(analysis/topology/topological_space): simplify proof of nhds_supr using Galois connection
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+ *lemma* pure_le_nhds
- \+ *lemma* gc_nhds
- \+/\- *lemma* nhds_mono
- \+/\- *lemma* nhds_supr
- \+ *lemma* nhds_Sup
- \+ *lemma* nhds_bot
- \- *lemma* return_le_nhds
- \- *lemma* supr_eq_generate_from
- \- *lemma* sup_eq_generate_from
- \+/\- *lemma* nhds_mono
- \+/\- *lemma* nhds_supr

Modified analysis/topology/uniform_space.lean



## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/6cab92e)
refactor(analysis/topology/topological_space): derive complete lattice structure from Galois insertion
#### Estimated changes
Modified analysis/topology/continuity.lean
- \- *lemma* induced_id
- \- *lemma* induced_compose
- \- *lemma* coinduced_id
- \- *lemma* coinduced_compose

Modified analysis/topology/topological_space.lean
- \+ *lemma* is_open_fold
- \+ *lemma* generate_from_le_iff_subset_is_open
- \+ *lemma* mk_of_closure_sets
- \+ *lemma* is_open_top
- \+ *lemma* induced_id
- \+ *lemma* induced_compose
- \+ *lemma* coinduced_id
- \+ *lemma* coinduced_compose
- \+ *def* gi_generate_from

Modified analysis/topology/uniform_space.lean

Modified order/galois_connection.lean
- \+ *lemma* l_u_eq



## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/f9434fa)
refactor(order/filter): derive complete lattice structure from Galois insertion
#### Estimated changes
Modified analysis/topology/uniform_space.lean

Modified order/filter.lean
- \+ *lemma* sets_iff_generate
- \+ *lemma* mk_of_closure_sets
- \+ *lemma* mem_top_sets_iff_forall
- \+ *lemma* mem_top_sets
- \+ *lemma* bot_sets_eq
- \+ *lemma* sup_sets_eq
- \+ *lemma* Sup_sets_eq
- \+/\- *lemma* supr_sets_eq
- \+ *lemma* generate_empty
- \+ *lemma* generate_univ
- \+ *lemma* generate_union
- \+ *lemma* generate_Union
- \+/\- *lemma* mem_sup_sets
- \+/\- *lemma* mem_Sup_sets
- \+/\- *lemma* mem_supr_sets
- \+/\- *lemma* le_principal_iff
- \+/\- *lemma* principal_mono
- \+/\- *lemma* monotone_principal
- \+/\- *lemma* principal_eq_iff_eq
- \+/\- *lemma* join_principal_eq_Sup
- \+/\- *lemma* principal_univ
- \+/\- *lemma* principal_empty
- \+/\- *lemma* le_principal_iff
- \+/\- *lemma* principal_mono
- \+/\- *lemma* monotone_principal
- \+/\- *lemma* principal_eq_iff_eq
- \+/\- *lemma* mem_sup_sets
- \- *lemma* mem_top_sets_iff
- \+/\- *lemma* mem_Sup_sets
- \+/\- *lemma* join_principal_eq_Sup
- \+/\- *lemma* supr_sets_eq
- \+/\- *lemma* mem_supr_sets
- \+/\- *lemma* principal_univ
- \+/\- *lemma* principal_empty
- \+ *def* complete_lattice.copy
- \+ *def* generate
- \+ *def* gi_generate



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
- \+ *lemma* mem_sets_of_superset
- \+/\- *lemma* inter_mem_sets
- \+/\- *lemma* univ_mem_sets'
- \- *lemma* filter.ext
- \+/\- *lemma* univ_mem_sets'
- \+/\- *lemma* inter_mem_sets

Modified order/liminf_limsup.lean



## [2018-08-18 12:55:12+02:00](https://github.com/leanprover-community/mathlib/commit/849ed4f)
feat(order/galois_connection): add Galois insertion and lattice lifts along a Galois insertion
#### Estimated changes
Modified analysis/measure_theory/measurable_space.lean
- \+/\- *lemma* comap_map_le
- \+/\- *lemma* le_map_comap
- \+/\- *lemma* comap_map_le
- \+/\- *lemma* le_map_comap

Modified order/filter.lean
- \+/\- *lemma* map_vmap_le
- \+/\- *lemma* le_vmap_map
- \+/\- *lemma* map_vmap_le
- \+/\- *lemma* le_vmap_map

Modified order/galois_connection.lean
- \+ *lemma* le_u_l
- \+ *lemma* l_u_le
- \+ *lemma* l_Sup
- \+ *lemma* u_Inf
- \- *lemma* increasing_u_l
- \- *lemma* decreasing_l_u
- \+ *def* galois_connection.lift_order_bot
- \+ *def* lift_semilattice_sup
- \+ *def* lift_semilattice_inf
- \+ *def* lift_lattice
- \+ *def* lift_order_top
- \+ *def* lift_bounded_lattice
- \+ *def* lift_complete_lattice



## [2018-08-18 01:02:27-04:00](https://github.com/leanprover-community/mathlib/commit/0ff11df)
refactor(group_theory/order_of_element): use gpowers instead of range ([#265](https://github.com/leanprover-community/mathlib/pull/265))
#### Estimated changes
Modified group_theory/order_of_element.lean
- \+/\- *lemma* exists_pow_eq_one
- \+ *lemma* order_of_pos
- \+ *lemma* mem_gpowers_iff_mem_range_order_of
- \+ *lemma* order_eq_card_gpowers
- \+/\- *lemma* exists_pow_eq_one
- \- *lemma* order_of_ne_zero
- \- *lemma* mem_range_gpow_iff_mem_range_order_of
- \- *lemma* order_eq_card_range_gpow



## [2018-08-18 01:00:59-04:00](https://github.com/leanprover-community/mathlib/commit/29508f2)
doc(tactic/solve_by_elim): update doc ([#266](https://github.com/leanprover-community/mathlib/pull/266)) [ci-skip]
#### Estimated changes
Modified docs/tactics.md

Modified tactic/interactive.lean



## [2018-08-18 01:00:24-04:00](https://github.com/leanprover-community/mathlib/commit/157004c)
feat(data/list/basic): some more theorems about sublist ([#264](https://github.com/leanprover-community/mathlib/pull/264))
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* erase_diff_erase_sublist_of_sublist

Modified data/list/perm.lean
- \+ *theorem* erase_subperm
- \+ *theorem* erase_subperm_erase



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

Created category_theory/opposites.lean
- \+ *lemma* opposite_obj
- \+ *lemma* opposite_map
- \+ *lemma* hom_obj
- \+ *lemma* hom_pairing_map
- \+ *def* op

Modified category_theory/products.lean
- \+/\- *lemma* prod_obj
- \+/\- *lemma* prod_map
- \+/\- *lemma* prod_app
- \+/\- *lemma* prod_obj
- \+/\- *lemma* prod_map
- \+/\- *lemma* prod_app

Created category_theory/types.lean
- \+ *lemma* types_hom
- \+ *lemma* types_id
- \+ *lemma* types_comp
- \+ *lemma* map_comp
- \+ *lemma* map_id
- \+ *lemma* naturality
- \+ *lemma* vcomp
- \+ *lemma* hcomp

Modified tactic/ext.lean
- \+ *lemma* ext



## [2018-08-16 11:32:39-04:00](https://github.com/leanprover-community/mathlib/commit/12d103c)
fix(padics/padic_norm): remove spurious import
#### Estimated changes
Modified data/padics/padic_norm.lean
- \+/\- *lemma* spec
- \+/\- *lemma* is_greatest
- \+/\- *lemma* unique
- \+/\- *lemma* le_padic_val_of_pow_div
- \+/\- *lemma* min_le_padic_val_add
- \+/\- *lemma* add_eq_max_of_ne
- \+/\- *lemma* spec
- \+/\- *lemma* is_greatest
- \+/\- *lemma* unique
- \+/\- *lemma* le_padic_val_of_pow_div
- \+/\- *lemma* min_le_padic_val_add
- \+/\- *lemma* add_eq_max_of_ne
- \+/\- *def* padic_val
- \+/\- *def* padic_val



## [2018-08-16 11:31:57-04:00](https://github.com/leanprover-community/mathlib/commit/1bca59b)
refactor(tactic/basic): simplify definition
#### Estimated changes
Modified tactic/basic.lean



## [2018-08-16 11:23:04-04:00](https://github.com/leanprover-community/mathlib/commit/93817f1)
feat(data/padics): p-adic numbers ([#262](https://github.com/leanprover-community/mathlib/pull/262))
#### Estimated changes
Modified algebra/archimedean.lean
- \+ *lemma* ceil_pos
- \+ *lemma* ceil_nonneg

Created algebra/field_power.lean
- \+ *lemma* zero_gpow
- \+ *lemma* unit_pow
- \+ *lemma* fpow_eq_gpow
- \+ *lemma* fpow_inv
- \+ *lemma* fpow_ne_zero_of_ne_zero
- \+ *lemma* fpow_zero
- \+ *lemma* fpow_add
- \+ *lemma* zero_fpow
- \+ *lemma* fpow_nonneg_of_nonneg
- \+ *lemma* fpow_le_of_le
- \+ *lemma* pow_le_max_of_min_le
- \+ *def* fpow

Modified algebra/order_functions.lean
- \+ *lemma* le_of_max_le_left
- \+ *lemma* le_of_max_le_right
- \+ *lemma* min_add
- \+ *lemma* min_sub
- \+ *lemma* min_le_add_of_nonneg_right
- \+ *lemma* min_le_add_of_nonneg_left
- \+ *lemma* max_le_add_of_nonneg

Modified algebra/ordered_field.lean
- \+ *lemma* inv_le_one

Modified algebra/ordered_ring.lean
- \+ *lemma* mul_le_one

Modified data/int/basic.lean
- \+ *lemma* of_nat_dvd_of_dvd_nat_abs
- \+ *lemma* dvd_nat_abs_of_of_nat_dvd
- \+ *lemma* pow_div_of_le_of_pow_div_int
- \+ *lemma* nat_abs_ne_zero_of_ne_zero
- \+ *theorem* eq_mul_div_of_mul_eq_mul_of_dvd_left

Modified data/nat/basic.lean
- \+ *lemma* one_pow
- \+ *lemma* pow_eq_mul_pow_sub
- \+ *lemma* pow_lt_pow_succ
- \+ *lemma* lt_pow_self
- \+ *lemma* not_pos_pow_dvd
- \+ *lemma* nat.find_greatest_spec
- \+ *lemma* nat.find_greatest_is_greatest
- \+ *lemma* dvd_div_of_mul_dvd
- \+ *lemma* mul_dvd_of_dvd_div
- \+ *lemma* nat.div_mul_div
- \+ *lemma* pow_div_of_le_of_pow_div
- \+ *theorem* pow_pos

Modified data/nat/prime.lean
- \+ *lemma* prime.ne_zero
- \+ *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
- \+ *lemma* succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul_int

Created data/padics/padic_integers.lean
- \+ *def* padic_int
- \+ *def* add
- \+ *def* mul
- \+ *def* neg

Created data/padics/padic_norm.lean
- \+ *lemma* spec
- \+ *lemma* is_greatest
- \+ *lemma* unique
- \+ *lemma* le_padic_val_of_pow_div
- \+ *lemma* padic_val_self
- \+ *lemma* min_le_padic_val_add
- \+ *lemma* padic_val_rat_self
- \+ *lemma* zero_of_padic_norm_eq_zero
- \+ *lemma* add_eq_max_of_ne
- \+ *theorem* min_le_padic_val_rat_add
- \+ *theorem* triangle_ineq
- \+ *def* padic_val
- \+ *def* padic_val_rat
- \+ *def* padic_norm

Created data/padics/padic_rationals.lean
- \+ *lemma* stationary
- \+ *lemma* stationary_point_spec
- \+ *lemma* norm_zero_iff
- \+ *lemma* equiv_zero_of_val_eq_of_equiv_zero
- \+ *lemma* norm_nonzero_of_not_equiv_zero
- \+ *lemma* norm_eq_norm_app_of_nonzero
- \+ *lemma* not_lim_zero_const_of_nonzero
- \+ *lemma* not_equiv_zero_const_of_nonzero
- \+ *lemma* norm_nonneg
- \+ *lemma* norm_mul
- \+ *lemma* eq_zero_iff_equiv_zero
- \+ *lemma* ne_zero_iff_nequiv_zero
- \+ *lemma* norm_const
- \+ *lemma* norm_image
- \+ *lemma* norm_one
- \+ *lemma* norm_eq
- \+ *lemma* norm_neg
- \+ *lemma* mk_eq
- \+ *lemma* of_rat_add
- \+ *lemma* of_rat_neg
- \+ *lemma* of_rat_mul
- \+ *lemma* of_rat_sub
- \+ *lemma* of_rat_div
- \+ *lemma* of_rat_one
- \+ *lemma* of_rat_zero
- \+ *lemma* cast_eq_of_rat_of_nat
- \+ *lemma* cast_eq_of_rat_of_int
- \+ *lemma* cast_eq_of_rat
- \+ *lemma* const_equiv
- \+ *lemma* of_rat_eq
- \+ *lemma* defn
- \+ *lemma* zero_def
- \+ *lemma* zero_iff
- \+ *lemma* eq_padic_norm
- \+ *lemma* sub_rev
- \+ *lemma* exi_rat_seq_conv
- \+ *lemma* exi_rat_seq_conv_cauchy
- \+ *theorem* norm_equiv
- \+ *theorem* norm_nonarchimedean
- \+ *theorem* nonarchimedean
- \+ *theorem* rat_dense
- \+ *theorem* complete
- \+ *def* padic_seq
- \+ *def* stationary_point
- \+ *def* norm
- \+ *def* padic
- \+ *def* mk
- \+ *def* of_rat
- \+ *def* padic_norm_e
- \+ *def* lim_seq

Modified data/rat.lean
- \+ *lemma* denom_neg_eq_denom
- \+ *lemma* num_neg_eq_neg_num
- \+ *lemma* num_zero
- \+ *lemma* zero_of_num_zero
- \+ *lemma* num_ne_zero_of_ne_zero
- \+ *lemma* denom_ne_zero
- \+ *lemma* mk_num_ne_zero_of_ne_zero
- \+ *lemma* mk_denom_ne_zero_of_ne_zero
- \+ *lemma* mk_ne_zero_of_ne_zero
- \+ *lemma* mul_num_denom
- \+ *lemma* num_denom_mk
- \+/\- *theorem* num_dvd
- \+/\- *theorem* num_dvd

Modified data/real/basic.lean
- \- *theorem* mk_eq_mk
- \- *theorem* mk_eq
- \- *theorem* of_rat_zero
- \- *theorem* of_rat_one
- \- *theorem* mk_eq_zero
- \- *theorem* mk_add
- \- *theorem* mk_neg
- \- *theorem* mk_mul
- \- *theorem* of_rat_add
- \- *theorem* of_rat_neg
- \- *theorem* of_rat_mul
- \- *theorem* inv_zero
- \- *theorem* inv_mk
- \+/\- *def* real
- \+/\- *def* of_rat
- \+/\- *def* real
- \- *def* mk
- \+/\- *def* of_rat

Modified data/real/cau_seq.lean
- \+ *lemma* not_lim_zero_of_not_congr_zero
- \+ *lemma* mul_equiv_zero
- \+ *lemma* mul_not_equiv_zero
- \+ *lemma* mul_equiv_zero'
- \+ *lemma* one_not_equiv_zero

Created data/real/cau_seq_completion.lean
- \+ *lemma* cau_seq_zero_ne_one
- \+ *lemma* zero_ne_one
- \+ *theorem* mk_eq_mk
- \+ *theorem* mk_eq
- \+ *theorem* of_rat_zero
- \+ *theorem* of_rat_one
- \+ *theorem* mk_eq_zero
- \+ *theorem* mk_add
- \+ *theorem* mk_neg
- \+ *theorem* mk_mul
- \+ *theorem* of_rat_add
- \+ *theorem* of_rat_neg
- \+ *theorem* of_rat_mul
- \+ *theorem* of_rat_sub
- \+ *theorem* inv_zero
- \+ *theorem* inv_mk
- \+ *theorem* of_rat_inv
- \+ *theorem* of_rat_div
- \+ *def* Cauchy
- \+ *def* mk
- \+ *def* of_rat



## [2018-08-16 07:09:33-04:00](https://github.com/leanprover-community/mathlib/commit/47a377d)
refactor(group_theory/quotient_group): remove duplicate definition ([#259](https://github.com/leanprover-community/mathlib/pull/259))
#### Estimated changes
Modified group_theory/coset.lean
- \+/\- *lemma* eq_class_eq_left_coset
- \+/\- *lemma* eq_class_eq_left_coset
- \- *lemma* coe_one
- \- *lemma* coe_mul
- \- *lemma* coe_inv
- \- *lemma* coe_pow
- \- *lemma* coe_gpow
- \+ *def* quotient
- \+/\- *def* mk
- \- *def* left_cosets
- \+/\- *def* mk

Modified group_theory/group_action.lean
- \+/\- *lemma* orbit_eq_iff
- \+/\- *lemma* orbit_eq_iff

Modified group_theory/order_of_element.lean

Modified group_theory/quotient_group.lean
- \+ *lemma* coe_one
- \+ *lemma* coe_mul
- \+ *lemma* coe_inv
- \+ *lemma* coe_pow
- \+ *lemma* coe_gpow
- \- *def* mk

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
- \+/\- *lemma* applicative.map_seq_map
- \+/\- *lemma* applicative.pure_seq_eq_map'
- \+/\- *lemma* map_pure
- \+/\- *lemma* seq_pure
- \+/\- *lemma* seq_assoc
- \+/\- *lemma* pure_seq_eq_map
- \+/\- *lemma* applicative.map_seq_map
- \+/\- *lemma* applicative.pure_seq_eq_map'
- \+/\- *lemma* map_pure
- \+/\- *lemma* seq_pure
- \+/\- *lemma* seq_assoc
- \+/\- *lemma* pure_seq_eq_map
- \+ *theorem* applicative.ext
- \+ *theorem* applicative_id_comp
- \+ *theorem* applicative_comp_id

Modified category/basic.lean
- \+/\- *theorem* pure_id'_seq
- \+/\- *theorem* seq_map_assoc
- \+/\- *theorem* map_seq
- \+/\- *theorem* pure_id'_seq
- \+/\- *theorem* seq_map_assoc
- \+/\- *theorem* map_seq
- \+/\- *def* mzip_with'
- \+ *def* list.mpartition
- \+/\- *def* succeeds
- \+/\- *def* mtry
- \+/\- *def* mzip_with'
- \+/\- *def* succeeds
- \+/\- *def* mtry

Modified category/functor.lean
- \+ *lemma* map_mk
- \- *lemma* comp.map_mk
- \+ *theorem* functor.ext
- \+ *theorem* functor_comp_id
- \+ *theorem* functor_id_comp
- \+ *def* comp
- \+ *def* comp.mk
- \+ *def* comp.run

Modified category/traversable/basic.lean
- \+/\- *lemma* preserves_pure
- \+/\- *lemma* preserves_map
- \+/\- *lemma* preserves_pure
- \+/\- *lemma* preserves_map
- \+/\- *def* sequence
- \+/\- *def* sequence

Created category/traversable/derive.lean

Modified category/traversable/equiv.lean

Modified category/traversable/instances.lean
- \+/\- *lemma* option.id_traverse
- \+/\- *lemma* option.comp_traverse
- \+ *lemma* option.traverse_eq_map_id
- \+/\- *lemma* option.naturality
- \+/\- *lemma* list.id_traverse
- \+/\- *lemma* list.comp_traverse
- \+ *lemma* list.traverse_eq_map_id
- \+/\- *lemma* list.naturality
- \- *lemma* id.id_traverse
- \- *lemma* id.comp_traverse
- \- *lemma* id.map_traverse
- \- *lemma* id.traverse_map
- \- *lemma* id.naturality
- \+/\- *lemma* option.id_traverse
- \+/\- *lemma* option.comp_traverse
- \- *lemma* option.map_traverse
- \- *lemma* option.traverse_map
- \+/\- *lemma* option.naturality
- \+/\- *lemma* list.id_traverse
- \+/\- *lemma* list.comp_traverse
- \- *lemma* list.map_traverse
- \- *lemma* list.traverse_map
- \+/\- *lemma* list.naturality

Modified category/traversable/lemmas.lean
- \+ *lemma* map_eq_traverse_id
- \+ *lemma* pure_traverse
- \+/\- *lemma* comp_sequence
- \+/\- *lemma* naturality'
- \+ *lemma* traverse_id
- \+ *lemma* traverse_comp
- \+ *lemma* traverse_eq_map_id'
- \+ *lemma* traverse_map'
- \+ *lemma* naturality_pf
- \- *lemma* traverse_eq_map_ident
- \- *lemma* purity
- \+/\- *lemma* comp_sequence
- \+/\- *lemma* naturality'
- \+ *theorem* pure_transformation_apply
- \+ *theorem* map_traverse
- \+ *theorem* traverse_map
- \+/\- *def* pure_transformation
- \+/\- *def* pure_transformation

Modified data/vector2.lean
- \+ *def* to_array

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

Created docs/mathlib-overview.md

Modified docs/theories.md

Created docs/theories/linear_algebra.md

Created docs/theories/measure.md

Created docs/theories/number_theory.md

Created docs/theories/polynomials.md

Deleted docs/theories/quotients.md

Modified docs/theories/relations.md

Modified docs/wip.md



## [2018-08-15 20:25:34-04:00](https://github.com/leanprover-community/mathlib/commit/5d791c6)
feat(data/polynomial): nth_roots ([#260](https://github.com/leanprover-community/mathlib/pull/260))
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* C_mul
- \+ *lemma* C_add
- \+ *lemma* eval_pow
- \+ *lemma* leading_coeff_X_pow
- \+ *lemma* degree_X_pow
- \+ *lemma* degree_X_pow_sub_C
- \+ *lemma* X_pow_sub_C_ne_zero
- \+ *lemma* card_roots_X_pow_sub_C
- \+ *lemma* mem_nth_roots
- \+ *lemma* card_nth_roots
- \- *lemma* C_mul_C



## [2018-08-15 20:22:47-04:00](https://github.com/leanprover-community/mathlib/commit/6e21c48)
feat(data/multiset): count_filter
#### Estimated changes
Modified data/list/basic.lean
- \+/\- *theorem* filter_filter
- \+ *theorem* countp_filter
- \+ *theorem* count_filter
- \+/\- *theorem* filter_filter

Modified data/multiset.lean
- \+ *theorem* countp_filter
- \+ *theorem* count_filter



## [2018-08-15 18:43:52-04:00](https://github.com/leanprover-community/mathlib/commit/46229d2)
feat(data/multiset): filter_congr, filter_filter
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* filter_congr

Modified data/list/basic.lean
- \+ *theorem* filter_filter

Modified data/multiset.lean
- \+ *lemma* filter_congr
- \+ *theorem* filter_filter
- \+ *theorem* filter_add_filter
- \+ *theorem* filter_add_not



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
- \+ *lemma* lebesgue_number_lemma_of_metric
- \+ *lemma* lebesgue_number_lemma_of_metric_sUnion
- \- *lemma* lebesgue_number_lemma

Modified analysis/topology/uniform_space.lean
- \+ *lemma* comp_rel_assoc
- \+ *lemma* lebesgue_number_lemma
- \+ *lemma* lebesgue_number_lemma_sUnion
- \- *lemma* assoc_comp_rel
- \- *lemma* lebesgue_entourage_lemma



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
- \+/\- *theorem* of_bijective_to_fun
- \+/\- *theorem* of_bijective_to_fun



## [2018-08-14 16:11:37+02:00](https://github.com/leanprover-community/mathlib/commit/add16e9)
feat(order): add order_dual (similar to with_top/with_bot) and dual order instances
#### Estimated changes
Modified order/basic.lean
- \- *theorem* le_dual_eq_le
- \+ *def* order_dual
- \- *def* preorder.dual
- \- *def* partial_order.dual

Modified order/bounded_lattice.lean

Modified order/complete_lattice.lean
- \+/\- *lemma* infi_top
- \+/\- *lemma* supr_bot
- \+ *lemma* infi_eq_top
- \+ *lemma* infi_eq_bot
- \+/\- *lemma* infi_top
- \+/\- *lemma* supr_bot
- \+/\- *theorem* Inf_eq_top
- \+/\- *theorem* Sup_eq_bot
- \+/\- *theorem* infi_const
- \+/\- *theorem* supr_const
- \+/\- *theorem* infi_const
- \+/\- *theorem* supr_const
- \+/\- *theorem* Inf_eq_top
- \- *theorem* infi_eq_top
- \+/\- *theorem* Sup_eq_bot
- \- *theorem* supr_eq_top

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
- \+ *theorem* subperm_cons_diff
- \+ *theorem* subset_cons_diff



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
- \+ *theorem* finite.exists_finset

Modified set_theory/cardinal.lean
- \+ *theorem* card_le_of_finset



## [2018-08-14 01:42:29-04:00](https://github.com/leanprover-community/mathlib/commit/9699f8d)
feat(data/multiset): some more theorems about diagonal
#### Estimated changes
Modified data/multiset.lean
- \+/\- *theorem* revzip_powerset_aux
- \+ *theorem* revzip_powerset_aux'
- \+ *theorem* revzip_powerset_aux_lemma
- \+ *theorem* revzip_powerset_aux_perm_aux'
- \+/\- *theorem* diagonal_coe
- \+ *theorem* diagonal_coe'
- \+ *theorem* diagonal_zero
- \+ *theorem* diagonal_cons
- \+/\- *theorem* revzip_powerset_aux
- \- *theorem* revzip_powerset_aux_eq_map
- \+/\- *theorem* diagonal_coe

Modified data/pfun.lean



## [2018-08-14 01:41:49-04:00](https://github.com/leanprover-community/mathlib/commit/d016186)
fix(tactic/norm_num): make norm_num only apply to current goal
#### Estimated changes
Modified tactic/norm_num.lean



## [2018-08-13 07:53:08-04:00](https://github.com/leanprover-community/mathlib/commit/8692959)
feat(data/list/basic): diff_sublist_of_sublist
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* diff_sublist_of_sublist



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
- \+/\- *theorem* mem_diff_of_mem
- \+/\- *theorem* mem_diff_of_mem



## [2018-08-12 17:09:22+10:00](https://github.com/leanprover-community/mathlib/commit/26ef0a0)
feat(data/list/basic): diff_subset and mem_diff_of_mem
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* diff_subset
- \+ *theorem* mem_diff_of_mem



## [2018-08-11 03:59:51-04:00](https://github.com/leanprover-community/mathlib/commit/6bf879d)
fix(category_theory): consistent use of coercions, consistent naming ([#248](https://github.com/leanprover-community/mathlib/pull/248))
#### Estimated changes
Modified category_theory/functor.lean
- \+/\- *lemma* comp_obj
- \+/\- *lemma* comp_obj

Modified category_theory/products.lean
- \+ *lemma* prod_id
- \+ *lemma* prod_comp
- \- *lemma* id
- \- *lemma* comp



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
- \+ *lemma* coe_nat_nonneg
- \+ *lemma* coe_nat_ne_zero_iff_pos
- \+ *lemma* mod_mod

Modified data/int/modeq.lean
- \+/\- *lemma* coe_nat_modeq_iff
- \+/\- *lemma* coe_nat_modeq_iff

Created data/zmod.lean
- \+ *lemma* add_val
- \+ *lemma* mul_val
- \+ *lemma* one_val
- \+ *lemma* zero_val
- \+ *lemma* val_cast_nat
- \+ *lemma* mk_eq_cast
- \+ *lemma* cast_self_eq_zero
- \+ *lemma* val_cast_of_lt
- \+ *lemma* cast_mod_nat
- \+ *lemma* cast_val
- \+ *lemma* cast_mod_int
- \+ *lemma* val_cast_int
- \+ *lemma* eq_iff_modeq_nat
- \+ *lemma* eq_iff_modeq_int
- \+ *lemma* card_zmod
- \+ *lemma* add_val
- \+ *lemma* mul_val
- \+ *lemma* one_val
- \+ *lemma* zero_val
- \+ *lemma* val_cast_nat
- \+ *lemma* mk_eq_cast
- \+ *lemma* cast_self_eq_zero:
- \+ *lemma* val_cast_of_lt
- \+ *lemma* cast_mod_nat
- \+ *lemma* cast_val
- \+ *lemma* cast_mod_int
- \+ *lemma* val_cast_int
- \+ *lemma* eq_iff_modeq_nat
- \+ *lemma* eq_iff_modeq_int
- \+ *lemma* gcd_a_modeq
- \+ *lemma* mul_inv_eq_gcd
- \+ *def* zmod
- \+ *def* zmodp



## [2018-08-10 09:44:20-04:00](https://github.com/leanprover-community/mathlib/commit/e1312b4)
feat(group_theory/perm): signatures of permutations ([#231](https://github.com/leanprover-community/mathlib/pull/231))
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *theorem* is_group_hom.prod
- \+/\- *theorem* is_group_anti_hom.prod
- \+/\- *theorem* is_group_hom.prod
- \+/\- *theorem* is_group_anti_hom.prod

Modified algebra/group.lean
- \+ *lemma* is_conj_refl
- \+ *lemma* is_conj_symm
- \+ *lemma* is_conj_trans
- \+ *lemma* is_conj_iff_eq
- \+ *def* is_conj

Modified data/equiv/basic.lean
- \+/\- *lemma* inverse_trans_apply
- \+ *lemma* swap_inv
- \+ *lemma* symm_trans_swap_trans
- \+/\- *lemma* inverse_trans_apply
- \+ *theorem* trans_refl
- \+ *theorem* refl_trans
- \+ *theorem* symm_trans
- \+ *theorem* trans_symm

Modified data/fin.lean

Modified data/finset.lean
- \+ *lemma* eq_empty_iff_forall_not_mem
- \+ *lemma* mem_attach_fin
- \+ *lemma* card_attach_fin
- \+ *theorem* mem_sort
- \+ *def* attach_fin

Modified data/fintype.lean
- \+ *theorem* fintype.card_units_int

Modified data/multiset.lean
- \+ *theorem* mem_sort

Created group_theory/perm.lean
- \+ *lemma* support_swap_mul
- \+ *lemma* swap_mul_swap_mul_swap
- \+ *lemma* is_conj_swap
- \+ *lemma* mem_fin_pairs_lt
- \+ *lemma* sign_aux_one
- \+ *lemma* sign_bij_aux_inj
- \+ *lemma* sign_bij_aux_surj
- \+ *lemma* sign_bij_aux_mem
- \+ *lemma* sign_aux_inv
- \+ *lemma* sign_aux_mul
- \+ *lemma* sign_aux_swap
- \+ *lemma* sign_aux_eq_sign_aux2
- \+ *lemma* sign_aux3_mul_and_swap
- \+ *lemma* sign_swap
- \+ *lemma* sign_eq_of_is_swap
- \+ *lemma* eq_sign_of_surjective_hom
- \+ *def* is_swap
- \+ *def* swap_factors_aux
- \+ *def* swap_factors
- \+ *def* trunc_swap_factors
- \+ *def* fin_pairs_lt
- \+ *def* sign_aux
- \+ *def* sign_bij_aux
- \+ *def* sign_aux2
- \+ *def* sign_aux3
- \+ *def* sign



## [2018-08-10 09:14:19-04:00](https://github.com/leanprover-community/mathlib/commit/251a8c3)
feat(tactic/assoc_rewrite): new tactic for implicitly applying associativity before rewriting ([#228](https://github.com/leanprover-community/mathlib/pull/228))
#### Estimated changes
Modified docs/tactics.md

Created tactic/rewrite.lean

Modified tests/tactics.lean



## [2018-08-10 09:07:20-04:00](https://github.com/leanprover-community/mathlib/commit/ff25083)
feat(data/list/basic): nil_diff and diff_sublist ([#235](https://github.com/leanprover-community/mathlib/pull/235))
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* nil_diff
- \+ *theorem* diff_sublist
- \- *theorem* reverse_rec_on
- \+ *def* reverse_rec_on



## [2018-08-10 09:06:41-04:00](https://github.com/leanprover-community/mathlib/commit/26ef419)
feat(data/fintype): fintype and decidable_eq for partial functions ([#236](https://github.com/leanprover-community/mathlib/pull/236))
#### Estimated changes
Modified data/fintype.lean

Modified logic/function.lean



## [2018-08-10 09:04:15-04:00](https://github.com/leanprover-community/mathlib/commit/e2521c3)
feat(data/set/finite): card_image_of_injective and other minor lemmas ([#245](https://github.com/leanprover-community/mathlib/pull/245))
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* coe_ssubset

Modified data/set/basic.lean
- \+ *lemma* ssubset_iff_subset_not_subset

Modified data/set/finite.lean
- \+ *lemma* card_image_of_inj_on
- \+ *lemma* card_image_of_injective
- \+ *lemma* coe_to_finset'
- \+ *lemma* card_lt_card



## [2018-08-10 08:52:34-04:00](https://github.com/leanprover-community/mathlib/commit/d400510)
feat(data/nat/binomial): the binomial theorem ([#214](https://github.com/leanprover-community/mathlib/pull/214))
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* prod_range_succ
- \+ *lemma* prod_range_succ'
- \+ *lemma* sum_range_succ'

Created data/nat/binomial.lean
- \+ *theorem* add_pow



## [2018-08-10 08:50:52-04:00](https://github.com/leanprover-community/mathlib/commit/54ce15b)
refactor(ring_theory/ideals): avoid using type class inference for setoids in quotient rings and groups ([#212](https://github.com/leanprover-community/mathlib/pull/212))
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* pow
- \+ *theorem* gpow

Modified data/quot.lean
- \+ *lemma* exact'
- \+ *lemma* sound'
- \+ *theorem* out_eq'
- \+ *theorem* mk_out'

Modified group_theory/coset.lean
- \+/\- *lemma* eq_class_eq_left_coset
- \+ *lemma* coe_one
- \+ *lemma* coe_mul
- \+ *lemma* coe_inv
- \+ *lemma* coe_pow
- \+ *lemma* coe_gpow
- \+/\- *lemma* eq_class_eq_left_coset
- \+ *def* mk

Modified ring_theory/ideals.lean
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* coe_add
- \+ *lemma* coe_mul
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *lemma* coe_pow
- \+ *lemma* eq_zero_iff_mem
- \- *lemma* quotient_eq_zero_iff_mem
- \+ *def* trivial
- \+/\- *def* quotient_rel
- \+ *def* mk
- \+/\- *def* quotient_rel



## [2018-08-10 07:12:29-04:00](https://github.com/leanprover-community/mathlib/commit/5b9914b)
style(group_theory/quotient_group): code style
#### Estimated changes
Modified group_theory/quotient_group.lean
- \+/\- *lemma* lift_mk
- \+/\- *lemma* lift_mk'
- \+/\- *lemma* lift_mk
- \+/\- *lemma* lift_mk'
- \+/\- *def* lift
- \+/\- *def* lift



## [2018-08-10 07:05:33-04:00](https://github.com/leanprover-community/mathlib/commit/d279ddb)
feat(group_theory): adding basic theory of quotient groups
#### Estimated changes
Created group_theory/quotient_group.lean
- \+ *lemma* lift_mk
- \+ *lemma* lift_mk'
- \+ *lemma* injective_ker_lift
- \+ *def* mk
- \+ *def* lift



## [2018-08-10 07:04:00-04:00](https://github.com/leanprover-community/mathlib/commit/0f42b27)
feat(group_theory/submonoid,subgroup): merge with add_* versions
#### Estimated changes
Modified algebra/group.lean

Deleted group_theory/add_subgroup.lean
- \- *lemma* injective_add
- \- *lemma* is_add_subgroup.gsmul_mem
- \- *lemma* mem_gmultiples
- \- *lemma* neg_mem_iff
- \- *lemma* add_mem_cancel_left
- \- *lemma* add_mem_cancel_right
- \- *lemma* mem_closure
- \- *lemma* mem_norm_comm
- \- *lemma* mem_norm_comm_iff
- \- *lemma* mem_trivial
- \- *lemma* trivial_eq_closure
- \- *lemma* mem_center
- \- *theorem* is_add_subgroup.of_sub
- \- *theorem* subset_closure
- \- *theorem* closure_subset
- \- *theorem* gmultiples_eq_closure
- \- *def* gmultiples
- \- *def* closure
- \- *def* trivial
- \- *def* center

Deleted group_theory/add_submonoid.lean
- \- *lemma* is_add_submonoid.smul_mem
- \- *lemma* is_add_submonoid.multiple_subset
- \- *lemma* is_add_submonoid.list_sum_mem
- \- *theorem* subset_closure
- \- *theorem* closure_subset
- \- *theorem* exists_list_of_mem_closure
- \- *def* multiples
- \- *def* closure

Modified group_theory/subgroup.lean
- \+ *lemma* is_add_subgroup.gsmul_mem
- \+/\- *lemma* mem_gpowers
- \+ *lemma* mem_gmultiples
- \+ *lemma* mem_closure
- \+/\- *lemma* mem_norm_comm
- \+/\- *lemma* mem_norm_comm_iff
- \+/\- *lemma* mem_center
- \+/\- *lemma* mem_gpowers
- \+/\- *lemma* mem_norm_comm
- \+/\- *lemma* mem_norm_comm_iff
- \+/\- *lemma* mem_center
- \+ *theorem* additive.is_add_subgroup_iff
- \+ *theorem* multiplicative.is_subgroup_iff
- \+/\- *theorem* is_subgroup.of_div
- \+ *theorem* is_add_subgroup.of_sub
- \+/\- *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* gmultiples_eq_closure
- \+ *theorem* additive.normal_add_subgroup_iff
- \+ *theorem* multiplicative.normal_subgroup_iff
- \+/\- *theorem* is_subgroup.of_div
- \+/\- *theorem* subset_closure
- \+ *def* gmultiples
- \+ *def* closure
- \+ *def* trivial
- \+ *def* center

Modified group_theory/submonoid.lean
- \+/\- *lemma* is_submonoid.pow_mem
- \+ *lemma* is_add_submonoid.smul_mem
- \+ *lemma* is_add_submonoid.multiple_subset
- \+/\- *lemma* is_submonoid.pow_mem
- \+ *theorem* additive.is_add_submonoid_iff
- \+ *theorem* multiplicative.is_submonoid_iff
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* exists_list_of_mem_closure
- \+ *def* multiples
- \+ *def* closure



## [2018-08-10 07:04:00-04:00](https://github.com/leanprover-community/mathlib/commit/1d5dd0d)
feat(group_theory): adding add_subgroup and add_submonoid
#### Estimated changes
Created group_theory/add_subgroup.lean
- \+ *lemma* injective_add
- \+ *lemma* is_add_subgroup.gsmul_mem
- \+ *lemma* mem_gmultiples
- \+ *lemma* neg_mem_iff
- \+ *lemma* add_mem_cancel_left
- \+ *lemma* add_mem_cancel_right
- \+ *lemma* mem_closure
- \+ *lemma* mem_norm_comm
- \+ *lemma* mem_norm_comm_iff
- \+ *lemma* mem_trivial
- \+ *lemma* trivial_eq_closure
- \+ *lemma* mem_center
- \+ *theorem* is_add_subgroup.of_sub
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* gmultiples_eq_closure
- \+ *def* gmultiples
- \+ *def* closure
- \+ *def* trivial
- \+ *def* center

Created group_theory/add_submonoid.lean
- \+ *lemma* is_add_submonoid.smul_mem
- \+ *lemma* is_add_submonoid.multiple_subset
- \+ *lemma* is_add_submonoid.list_sum_mem
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* exists_list_of_mem_closure
- \+ *def* multiples
- \+ *def* closure



## [2018-08-10 05:37:13-04:00](https://github.com/leanprover-community/mathlib/commit/e1d92c2)
fix(tactic/replacer): fix tests
#### Estimated changes
Modified tactic/replacer.lean

Modified tests/replacer.lean



## [2018-08-09 12:09:07-04:00](https://github.com/leanprover-community/mathlib/commit/bf3dde1)
refactor(set_theory/cardinal): remove noncomputable theory
#### Estimated changes
Modified set_theory/cardinal.lean
- \- *def* min
- \- *def* succ
- \- *def* sup



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

Created tests/replacer.lean



## [2018-08-08 14:39:58-04:00](https://github.com/leanprover-community/mathlib/commit/a917810)
refactor(tactic/interactive): merge rcases_hint -> rcases?
#### Estimated changes
Modified docs/tactics.md

Modified tactic/interactive.lean



## [2018-08-08 10:51:30-04:00](https://github.com/leanprover-community/mathlib/commit/8a19a98)
feat(tactic/replacer): replaceable tactics
#### Estimated changes
Modified tactic/interactive.lean

Created tactic/replacer.lean



## [2018-08-08 06:57:37-04:00](https://github.com/leanprover-community/mathlib/commit/732ec0e)
feat(tactic/rcases): rcases_hint, rintro_hint
#### Estimated changes
Modified docs/tactics.md

Modified tactic/basic.lean

Modified tactic/interactive.lean
- \- *def* rcases_patt_inverted

Modified tactic/rcases.lean
- \+ *def* merge_list
- \- *def* rcases_patt.name



## [2018-08-08 00:44:37-04:00](https://github.com/leanprover-community/mathlib/commit/fe7cd33)
refactor(category_theory/products): tweak PR after merge
#### Estimated changes
Modified analysis/nnreal.lean
- \+ *def* nnreal

Modified category_theory/functor.lean
- \+ *def* comp

Modified category_theory/functor_category.lean
- \+/\- *lemma* id_app
- \+/\- *lemma* comp_app
- \+/\- *lemma* id_app
- \+/\- *lemma* comp_app

Modified category_theory/natural_transformation.lean
- \+/\- *lemma* exchange
- \+/\- *lemma* exchange
- \+ *def* vcomp
- \+ *def* hcomp

Modified category_theory/products.lean
- \+/\- *lemma* id
- \+/\- *lemma* comp
- \+ *lemma* prod_obj
- \+ *lemma* prod_map
- \+ *lemma* prod_app
- \+/\- *lemma* id
- \+/\- *lemma* comp
- \- *lemma* product_obj
- \- *lemma* product_map
- \- *lemma* product_app
- \+ *def* inl
- \+ *def* inr
- \+ *def* fst
- \+ *def* snd
- \+ *def* prod
- \+ *def* prod

Modified order/bounds.lean
- \+ *def* upper_bounds
- \+ *def* lower_bounds
- \+ *def* is_least
- \+ *def* is_greatest
- \+ *def* is_lub
- \+ *def* is_glb

Modified tactic/basic.lean



## [2018-08-08 00:32:10-04:00](https://github.com/leanprover-community/mathlib/commit/02cf7a6)
feat(category_theory): product categories and functor categories ([#239](https://github.com/leanprover-community/mathlib/pull/239))
#### Estimated changes
Created category_theory/functor_category.lean
- \+ *lemma* id_app
- \+ *lemma* comp_app
- \+ *lemma* app_naturality
- \+ *lemma* naturality_app

Created category_theory/products.lean
- \+ *lemma* id
- \+ *lemma* comp
- \+ *lemma* product_obj
- \+ *lemma* product_map
- \+ *lemma* product_app



## [2018-08-08 00:29:39-04:00](https://github.com/leanprover-community/mathlib/commit/47a6a6f)
fix(tactic/interactive): try_for should fail if the tactic fails
#### Estimated changes
Modified tactic/interactive.lean



## [2018-08-08 00:29:39-04:00](https://github.com/leanprover-community/mathlib/commit/417f29a)
fix(linear_algebra/multivariate_polynomial): remove some @[simp]
#### Estimated changes
Modified linear_algebra/multivariate_polynomial.lean
- \+/\- *lemma* C_mul_monomial
- \+/\- *lemma* eval₂_mul_monomial
- \+/\- *lemma* eval_monomial
- \+/\- *lemma* C_mul_monomial
- \+/\- *lemma* eval₂_mul_monomial
- \+/\- *lemma* eval_monomial



## [2018-08-07 20:28:50-04:00](https://github.com/leanprover-community/mathlib/commit/bd7f1b0)
feat(data/fintype): injective_iff_surjective ([#240](https://github.com/leanprover-community/mathlib/pull/240))
#### Estimated changes
Modified data/fintype.lean
- \+/\- *lemma* fintype.card_le_of_injective
- \+ *lemma* fintype.injective_iff_surjective
- \+ *lemma* fintype.injective_iff_surjective_of_equiv
- \+/\- *lemma* fintype.card_le_of_injective



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
Created category_theory/category.lean

Created category_theory/functor.lean
- \+ *lemma* coe_def
- \+ *lemma* id_obj
- \+ *lemma* id_map
- \+ *lemma* comp_obj
- \+ *lemma* comp_map

Created category_theory/natural_transformation.lean
- \+ *lemma* coe_def
- \+ *lemma* id_app
- \+ *lemma* ext
- \+ *lemma* vcomp_app
- \+ *lemma* vcomp_assoc
- \+ *lemma* hcomp_app
- \+ *lemma* exchange

Created docs/theories/categories.md

Created tactic/restate_axiom.lean



## [2018-08-07 05:51:20-04:00](https://github.com/leanprover-community/mathlib/commit/235129a)
feat(linear_algebra/multivariate_polynomial): Add `_sub` and `_neg` lemmas, and make them simp. ([#238](https://github.com/leanprover-community/mathlib/pull/238))
#### Estimated changes
Modified linear_algebra/multivariate_polynomial.lean
- \+/\- *lemma* C_add
- \+/\- *lemma* C_mul
- \+/\- *lemma* eval₂_add
- \+/\- *lemma* eval₂_monomial
- \+/\- *lemma* eval₂_mul_monomial
- \+/\- *lemma* eval_add
- \+/\- *lemma* eval_monomial
- \+/\- *lemma* eval_mul
- \+ *lemma* C_sub
- \+ *lemma* C_neg
- \+ *lemma* eval₂_sub
- \+ *lemma* eval₂_neg
- \+ *lemma* eval_sub
- \+ *lemma* eval_neg
- \+ *lemma* map_sub
- \+ *lemma* map_neg
- \+/\- *lemma* C_add
- \+/\- *lemma* C_mul
- \+/\- *lemma* eval₂_add
- \+/\- *lemma* eval₂_monomial
- \+/\- *lemma* eval₂_mul_monomial
- \+/\- *lemma* eval_add
- \+/\- *lemma* eval_monomial
- \+/\- *lemma* eval_mul



## [2018-08-06 20:05:15-04:00](https://github.com/leanprover-community/mathlib/commit/8dc0393)
feat(data/multiset): adding two lemmas about singletons ([#234](https://github.com/leanprover-community/mathlib/pull/234))
#### Estimated changes
Modified data/multiset.lean
- \+ *lemma* repeat_zero
- \+ *lemma* repeat_succ
- \+ *lemma* repeat_one
- \+ *theorem* powerset_zero
- \+ *theorem* powerset_cons
- \+ *theorem* erase_dup_singleton



## [2018-08-06 11:05:42-04:00](https://github.com/leanprover-community/mathlib/commit/18bd614)
feat(algebra/group_power): adding various cast power lemmas for nat and int ([#230](https://github.com/leanprover-community/mathlib/pull/230))
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* nat.cast_pow
- \+ *theorem* int.coe_nat_pow
- \+ *theorem* int.cast_pow

Modified data/nat/basic.lean
- \+ *theorem* pow_two



## [2018-08-06 06:43:02-04:00](https://github.com/leanprover-community/mathlib/commit/cf0bf2a)
fix(data/seq/wseq): fix build
#### Estimated changes
Modified data/seq/wseq.lean



## [2018-08-06 05:08:26-04:00](https://github.com/leanprover-community/mathlib/commit/8d13bb9)
feat(list/basic,multiset): list.revzip, multiset.diagonal
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* forall₂.imp
- \+ *theorem* zip_swap
- \+ *theorem* length_zip
- \+ *theorem* zip_append
- \+ *theorem* zip_map
- \+ *theorem* zip_map_left
- \+ *theorem* zip_map_right
- \+ *theorem* zip_map'
- \+ *theorem* mem_zip
- \+ *theorem* unzip_eq_map
- \+ *theorem* unzip_left
- \+ *theorem* unzip_right
- \+ *theorem* unzip_swap
- \+ *theorem* unzip_zip_left
- \+ *theorem* unzip_zip_right
- \+ *theorem* unzip_zip
- \+ *theorem* length_revzip
- \+ *theorem* unzip_revzip
- \+ *theorem* revzip_map_fst
- \+ *theorem* revzip_map_snd
- \+ *theorem* reverse_revzip
- \+ *theorem* revzip_swap
- \+ *def* revzip

Modified data/list/perm.lean
- \+ *theorem* revzip_sublists
- \+ *theorem* revzip_sublists'

Modified data/multiset.lean
- \+/\- *theorem* coe_eq_coe
- \+ *theorem* mem_powerset_aux
- \+ *theorem* revzip_powerset_aux
- \+ *theorem* revzip_powerset_aux_eq_map
- \+ *theorem* revzip_powerset_aux_perm
- \+ *theorem* diagonal_coe
- \+ *theorem* mem_diagonal
- \+ *theorem* diagonal_map_fst
- \+ *theorem* diagonal_map_snd
- \+ *theorem* card_diagonal
- \+/\- *theorem* coe_eq_coe
- \+ *def* diagonal

Modified data/prod.lean



## [2018-08-05 22:52:53-04:00](https://github.com/leanprover-community/mathlib/commit/e4b652f)
refactor(data/real/basic): rename for consistency
#### Estimated changes
Modified analysis/real.lean
- \- *lemma* exists_supremum_real

Modified data/real/basic.lean
- \- *lemma* Sup_is_lub

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
- \+ *lemma* eval₂_zero
- \+ *lemma* eval₂_add
- \+ *lemma* eval₂_monomial
- \+ *lemma* eval₂_C
- \+ *lemma* eval₂_one
- \+ *lemma* eval₂_X
- \+ *lemma* eval₂_mul_monomial
- \+ *lemma* eval₂_mul
- \+ *lemma* eval₂_comp_left
- \+ *lemma* eval₂_eta
- \+/\- *lemma* eval_zero
- \+/\- *lemma* eval_add
- \+/\- *lemma* eval_C
- \+/\- *lemma* eval_X
- \+/\- *lemma* eval_mul
- \- *lemma* map₂_zero
- \- *lemma* map₂_add
- \- *lemma* map₂_monomial
- \- *lemma* map₂_C
- \- *lemma* map₂_one
- \- *lemma* map₂_X
- \- *lemma* map₂_mul_monomial
- \- *lemma* map₂_mul
- \+/\- *lemma* eval_zero
- \+/\- *lemma* eval_add
- \+/\- *lemma* eval_C
- \+/\- *lemma* eval_X
- \+/\- *lemma* eval_mul
- \+ *theorem* eval_assoc
- \+/\- *theorem* map_C
- \+/\- *theorem* map_X
- \+/\- *theorem* map_one
- \+ *theorem* map_id
- \+ *theorem* map_map
- \+ *theorem* eval₂_eq_eval_map
- \+/\- *theorem* map_C
- \+/\- *theorem* map_X
- \+/\- *theorem* map_one
- \+ *def* eval₂
- \+/\- *def* eval
- \+/\- *def* map
- \- *def* map₂
- \+/\- *def* eval
- \+/\- *def* map



## [2018-08-04 19:53:15-04:00](https://github.com/leanprover-community/mathlib/commit/2d0eb8c)
feat(linear_algebra/mv_polynomial): map function, map2
#### Estimated changes
Modified data/finsupp.lean
- \+ *lemma* map_range_single

Modified linear_algebra/multivariate_polynomial.lean
- \+ *lemma* C_add
- \+ *lemma* C_mul
- \+ *lemma* map₂_zero
- \+ *lemma* map₂_add
- \+ *lemma* map₂_monomial
- \+ *lemma* map₂_C
- \+ *lemma* map₂_one
- \+ *lemma* map₂_X
- \+ *lemma* map₂_mul_monomial
- \+ *lemma* map₂_mul
- \+/\- *lemma* eval_zero
- \+/\- *lemma* eval_add
- \+/\- *lemma* eval_monomial
- \+/\- *lemma* eval_C
- \+/\- *lemma* eval_X
- \+/\- *lemma* eval_mul
- \+/\- *lemma* eval_zero
- \+/\- *lemma* eval_add
- \+/\- *lemma* eval_monomial
- \+/\- *lemma* eval_C
- \+/\- *lemma* eval_X
- \- *lemma* eval_mul_monomial
- \+/\- *lemma* eval_mul
- \+ *theorem* map_monomial
- \+ *theorem* map_C
- \+ *theorem* map_X
- \+ *theorem* map_one
- \+ *theorem* map_add
- \+ *theorem* map_mul
- \+ *def* map₂
- \+/\- *def* eval
- \+ *def* map
- \+/\- *def* eval



## [2018-08-04 18:47:15-04:00](https://github.com/leanprover-community/mathlib/commit/1b93719)
feat(algebra/ring): units.neg and associated matter
#### Estimated changes
Modified algebra/group.lean
- \+ *lemma* mul_coe
- \+ *lemma* one_coe
- \+ *lemma* val_coe
- \+ *lemma* inv_coe
- \+ *lemma* inv_mul
- \+ *lemma* mul_inv
- \+ *lemma* mul_inv_cancel_left
- \+ *lemma* inv_mul_cancel_left
- \+ *lemma* mul_inv_cancel_right
- \+ *lemma* inv_mul_cancel_right
- \+ *theorem* ext
- \+ *theorem* ext_iff
- \+ *theorem* mul_left_inj
- \+ *theorem* mul_right_inj
- \+ *theorem* nat.units_eq_one

Modified algebra/ordered_group.lean
- \+ *theorem* coe_le_coe
- \+ *theorem* coe_lt_coe
- \+ *theorem* max_coe
- \+ *theorem* min_coe

Modified algebra/ring.lean
- \+ *theorem* mul_two
- \+ *theorem* bit0_eq_two_mul

Modified data/int/basic.lean
- \+ *theorem* units_nat_abs
- \+ *theorem* units_eq_one_or

Modified ring_theory/localization.lean
- \+ *def* inv_aux



## [2018-08-04 18:43:51-04:00](https://github.com/leanprover-community/mathlib/commit/e40bee5)
feat(algebra/ring): semiring homs
#### Estimated changes
Modified algebra/ring.lean
- \+ *def* of_semiring



## [2018-08-04 18:40:37-04:00](https://github.com/leanprover-community/mathlib/commit/7ec5e87)
feat(set_theory/lists): finite ZFA
#### Estimated changes
Created set_theory/lists.lean
- \+ *theorem* to_list_cons
- \+ *theorem* to_of_list
- \+ *theorem* of_to_list
- \+ *theorem* mem_def
- \+ *theorem* mem_cons
- \+ *theorem* cons_subset
- \+ *theorem* of_list_subset
- \+ *theorem* subset.refl
- \+ *theorem* subset_nil
- \+ *theorem* mem_of_subset'
- \+ *theorem* subset_def
- \+ *theorem* is_list_to_list
- \+ *theorem* to_of_list
- \+ *theorem* of_to_list
- \+ *theorem* is_list_of_mem
- \+ *theorem* equiv.antisymm_iff
- \+ *theorem* equiv_atom
- \+ *theorem* equiv.symm
- \+ *theorem* equiv.trans
- \+ *theorem* sizeof_pos
- \+ *theorem* lt_sizeof_cons'
- \+ *theorem* mem_equiv_left
- \+ *theorem* mem_of_subset
- \+ *theorem* subset.trans
- \+ *def* lists
- \+ *def* cons
- \+ *def* to_list
- \+ *def* of_list
- \+ *def* atom
- \+ *def* of'
- \+ *def* to_list
- \+ *def* is_list
- \+ *def* of_list
- \+ *def* induction_mut
- \+ *def* mem
- \+ *def* equiv.decidable_meas
- \+ *def* finsets

Modified set_theory/zfc.lean



## [2018-08-03 05:53:29-04:00](https://github.com/leanprover-community/mathlib/commit/8731789)
feat(data/vector2): vector.ext ([#232](https://github.com/leanprover-community/mathlib/pull/232))
#### Estimated changes
Modified data/vector2.lean
- \+ *theorem* ext

