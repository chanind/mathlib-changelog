## [2018-07-30 20:35:12+02:00](https://github.com/leanprover-community/mathlib/commit/cecbf2b)
doc(tactics/pi_instance): add description in `tactics.md` ([#229](https://github.com/leanprover-community/mathlib/pull/229))
#### Estimated changes
Modified docs/tactics.md

Modified tactic/interactive.lean

Modified tactic/pi_instances.lean



## [2018-07-30 12:01:49+02:00](https://github.com/leanprover-community/mathlib/commit/fed6c58)
feat(algebra/euclidean_domain): change definition of ED and instance for polynomials ([#211](https://github.com/leanprover-community/mathlib/pull/211))
#### Estimated changes
Modified algebra/euclidean_domain.lean
- \+ *lemma* lt_one
- \+/\- *lemma* val_dvd_le
- \- *lemma* val_lt_one
- \+/\- *lemma* val_dvd_le
- \+ *theorem* mod_lt
- \+ *theorem* mul_right_not_lt
- \- *theorem* val_mod_lt
- \- *theorem* val_le_mul_right

Modified data/polynomial.lean
- \+ *lemma* degree_le_mul_left
- \+ *lemma* div_def
- \+ *lemma* mod_def
- \+ *lemma* mod_eq_self_iff
- \+ *lemma* div_eq_zero_iff
- \+/\- *lemma* degree_add_div
- \+/\- *lemma* degree_add_div



## [2018-07-30 11:48:54+02:00](https://github.com/leanprover-community/mathlib/commit/08e0e1d)
feat(category/traversable): instances for various collections ([#217](https://github.com/leanprover-community/mathlib/pull/217))
#### Estimated changes
Created category/traversable/equiv.lean

Modified data/array/lemmas.lean
- \+ *theorem* to_list_of_heq
- \+ *def* vector_equiv_fin
- \+ *def* vector_equiv_array

Created data/buffer/basic.lean
- \+ *lemma* ext
- \+ *lemma* to_list_append_list
- \+ *lemma* append_list_mk_buffer
- \+ *def* list_equiv_buffer

Created data/dlist/instances.lean
- \+ *def* list_equiv_dlist

Modified data/equiv/basic.lean

Created data/lazy_list2.lean
- \+ *def* list_equiv_lazy_list
- \+ *def* thunk.mk

Modified data/multiset.lean

Modified data/vector2.lean
- \- *def* vector_equiv_fin
- \- *def* vector_equiv_array

Modified logic/basic.lean
- \+ *lemma* heq_of_eq_mp

Modified tactic/interactive.lean



## [2018-07-30 11:27:47+02:00](https://github.com/leanprover-community/mathlib/commit/7dc1f5d)
feat(algebra/pi_instances): more automation ([#222](https://github.com/leanprover-community/mathlib/pull/222))
#### Estimated changes
Modified algebra/pi_instances.lean

Modified group_theory/coset.lean

Modified meta/expr.lean

Modified order/bounded_lattice.lean

Modified order/complete_lattice.lean

Modified tactic/interactive.lean

Created tactic/pi_instances.lean



## [2018-07-30 11:06:42+02:00](https://github.com/leanprover-community/mathlib/commit/fc88dd4)
fix(tactic/split_ifs): do not process the same condition twice ([#224](https://github.com/leanprover-community/mathlib/pull/224))
#### Estimated changes
Modified tactic/split_ifs.lean



## [2018-07-30 11:01:09+02:00](https://github.com/leanprover-community/mathlib/commit/22d811d)
chore(doc/style): mention how to handle ';'
#### Estimated changes
Modified docs/style.md



## [2018-07-30 10:56:07+02:00](https://github.com/leanprover-community/mathlib/commit/0371f6e)
feat(data/equiv/basic): basic equiv lemmas and decidable_eq ([#225](https://github.com/leanprover-community/mathlib/pull/225))
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *lemma* inverse_trans_apply
- \+ *lemma* inv_apply_self
- \+ *lemma* apply_inv_self
- \+ *lemma* one_def
- \+ *lemma* mul_def
- \+ *lemma* inv_def
- \+ *theorem* mul_apply
- \+ *theorem* one_apply
- \- *theorem* perm.mul_val
- \- *theorem* perm.one_val

Modified data/fintype.lean



## [2018-07-30 10:41:45+02:00](https://github.com/leanprover-community/mathlib/commit/e67f2ad)
chore(analysis/topology/uniform_space): remove redundant prod_uniformity (redundant to uniformity_prod)
#### Estimated changes
Modified analysis/metric_space.lean

Modified analysis/topology/uniform_space.lean
- \- *lemma* uniformity_prod
- \+ *theorem* uniformity_prod
- \- *theorem* prod_uniformity



## [2018-07-30 10:25:10+02:00](https://github.com/leanprover-community/mathlib/commit/8d4f582)
chore(data/list): add prod.erase; cleanup
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* eq_or_ne_mem_of_mem
- \+/\- *theorem* take'_eq_take
- \+ *theorem* prod_erase
- \+/\- *theorem* take'_eq_take



## [2018-07-27 23:51:05-04:00](https://github.com/leanprover-community/mathlib/commit/460df5e)
feat(tactic/norm_num): add support for primality proving
#### Estimated changes
Modified data/nat/gcd.lean
- \+ *theorem* exists_coprime'
- \+/\- *theorem* exists_eq_prod_and_dvd_and_dvd
- \+/\- *theorem* exists_eq_prod_and_dvd_and_dvd

Modified data/nat/prime.lean
- \+ *theorem* not_prime_mul

Modified tactic/norm_num.lean
- \+ *lemma* not_prime_helper
- \+ *lemma* is_prime_helper
- \+ *lemma* min_fac_bit0
- \+ *lemma* min_fac_ne_bit0
- \+ *lemma* min_fac_helper_0
- \+ *lemma* min_fac_helper_1
- \+ *lemma* min_fac_helper_2
- \+ *lemma* min_fac_helper_3
- \+ *lemma* min_fac_helper_4
- \+ *lemma* min_fac_helper_5
- \+ *theorem* min_fac_helper.n_pos
- \+ *def* min_fac_helper

Modified tactic/ring.lean



## [2018-07-27 13:21:15-04:00](https://github.com/leanprover-community/mathlib/commit/4d8ce7e)
feat(data/fin): linear order and eta ([#223](https://github.com/leanprover-community/mathlib/pull/223))
#### Estimated changes
Modified data/fin.lean



## [2018-07-25 19:05:48+02:00](https://github.com/leanprover-community/mathlib/commit/85bc75a)
fix(data/list/basic): typo in pariwise_iff
#### Estimated changes
Modified data/list/basic.lean



## [2018-07-24 16:33:28+02:00](https://github.com/leanprover-community/mathlib/commit/f9cf9d3)
feat(category/traversable): basic classes for traversable collections
#### Estimated changes
Created category/traversable/basic.lean
- \+ *lemma* preserves_pure
- \+ *lemma* preserves_seq
- \+ *lemma* preserves_map
- \+ *def* sequence

Created category/traversable/default.lean

Created category/traversable/instances.lean
- \+ *lemma* id.id_traverse
- \+ *lemma* id.comp_traverse
- \+ *lemma* id.map_traverse
- \+ *lemma* id.traverse_map
- \+ *lemma* id.naturality
- \+ *lemma* option.id_traverse
- \+ *lemma* option.comp_traverse
- \+ *lemma* option.map_traverse
- \+ *lemma* option.traverse_map
- \+ *lemma* option.naturality
- \+ *lemma* list.id_traverse
- \+ *lemma* list.comp_traverse
- \+ *lemma* list.map_traverse
- \+ *lemma* list.traverse_map
- \+ *lemma* list.naturality

Created category/traversable/lemmas.lean
- \+ *lemma* traverse_eq_map_ident
- \+ *lemma* purity
- \+ *lemma* id_sequence
- \+ *lemma* comp_sequence
- \+ *lemma* naturality'
- \+ *def* pure_transformation



## [2018-07-24 05:15:31-04:00](https://github.com/leanprover-community/mathlib/commit/8270475)
doc(wip): finite map ([#215](https://github.com/leanprover-community/mathlib/pull/215)) [ci-skip]
#### Estimated changes
Modified docs/wip.md



## [2018-07-23 20:06:20-04:00](https://github.com/leanprover-community/mathlib/commit/6abb0d4)
feat(algebra/pi_instances): more pi instances
#### Estimated changes
Modified algebra/pi_instances.lean
- \+/\- *lemma* zero_apply
- \+/\- *lemma* mul_apply
- \+/\- *lemma* inv_apply
- \+/\- *lemma* smul_apply
- \+/\- *lemma* mul_apply
- \+/\- *lemma* inv_apply
- \+/\- *lemma* zero_apply
- \+/\- *lemma* smul_apply

Modified order/basic.lean

Modified order/bounded_lattice.lean

Modified order/complete_lattice.lean



## [2018-07-22 15:03:49-04:00](https://github.com/leanprover-community/mathlib/commit/e74ff76)
refactor(data/nat/gcd): simplify proof of pow_dvd_pow_iff
#### Estimated changes
Modified algebra/ring.lean

Modified data/nat/basic.lean
- \+ *theorem* pow_dvd_pow_of_dvd

Modified data/nat/gcd.lean
- \- *lemma* dvd_of_pow_dvd_pow
- \+ *theorem* pow_dvd_pow_iff



## [2018-07-22 14:37:11-04:00](https://github.com/leanprover-community/mathlib/commit/ffb7229)
feat(data/nat/gcd): dvd_of_pow_dvd_pow
#### Estimated changes
Modified data/nat/basic.lean
- \+ *theorem* mul_pow

Modified data/nat/gcd.lean
- \+ *lemma* dvd_of_pow_dvd_pow



## [2018-07-21 14:23:10-04:00](https://github.com/leanprover-community/mathlib/commit/e429aac)
fix(computability/turing_machine): missed a spot
#### Estimated changes
Modified computability/turing_machine.lean



## [2018-07-21 14:02:13-04:00](https://github.com/leanprover-community/mathlib/commit/8bf72b2)
chore(tactic/interactive): change swap so it does what it says
it is supposed to move the nth goal to the front, not rotate all the goals
#### Estimated changes
Modified tactic/interactive.lean



## [2018-07-21 13:58:02-04:00](https://github.com/leanprover-community/mathlib/commit/682025f)
fix(*): fix build, use rw consistently
#### Estimated changes
Modified algebra/ring.lean

Modified computability/primrec.lean

Modified data/int/order.lean

Modified data/seq/wseq.lean

Modified data/set/basic.lean

Modified order/galois_connection.lean



## [2018-07-21 12:10:36-04:00](https://github.com/leanprover-community/mathlib/commit/e7321bb)
fix(data/option): fix universe levels in option.map_some etc.
#### Estimated changes
Modified computability/partrec.lean

Modified computability/partrec_code.lean

Modified computability/primrec.lean

Modified computability/turing_machine.lean

Modified data/equiv/denumerable.lean

Modified data/equiv/encodable.lean

Modified data/list/basic.lean

Modified data/option.lean
- \+/\- *theorem* none_bind
- \+/\- *theorem* some_bind
- \+/\- *theorem* bind_eq_some
- \+/\- *theorem* map_none
- \+/\- *theorem* map_some
- \+/\- *theorem* map_eq_some
- \+/\- *theorem* seq_some
- \+/\- *theorem* none_bind
- \+/\- *theorem* some_bind
- \+/\- *theorem* bind_eq_some
- \+/\- *theorem* map_none
- \+/\- *theorem* map_some
- \+/\- *theorem* map_eq_some
- \+/\- *theorem* seq_some

Modified data/seq/seq.lean

Modified data/seq/wseq.lean



## [2018-07-21 02:09:53-04:00](https://github.com/leanprover-community/mathlib/commit/fb952fe)
refactor(analysis/ennreal): split and move to data.real
#### Estimated changes
Modified analysis/ennreal.lean
- \- *lemma* of_ennreal_of_real
- \- *lemma* zero_le_of_ennreal
- \- *lemma* of_real_of_ennreal
- \- *lemma* forall_ennreal
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
- \- *lemma* not_lt_zero
- \- *lemma* of_real_le_of_real
- \- *lemma* of_real_lt_of_real_iff_cases
- \- *lemma* le_add_left
- \- *lemma* le_add_right
- \- *lemma* lt_add_right
- \- *lemma* of_real_add_le
- \- *lemma* mul_le_mul
- \- *lemma* le_of_forall_epsilon_le
- \- *lemma* infty_mem_upper_bounds
- \- *lemma* of_real_mem_upper_bounds
- \- *lemma* is_lub_of_real
- \- *lemma* sub_eq_zero_of_le
- \- *lemma* sub_add_cancel_of_le
- \- *lemma* add_sub_cancel_of_le
- \- *lemma* sub_add_self_eq_max
- \- *lemma* sub_le_sub
- \- *lemma* sub_le_self
- \- *lemma* zero_sub
- \- *lemma* sub_infty
- \- *lemma* sub_zero
- \- *lemma* infty_sub_of_real
- \- *lemma* of_real_sub_of_real
- \- *lemma* add_sub_self
- \- *lemma* add_sub_self'
- \- *lemma* add_left_inj
- \- *lemma* add_right_inj
- \- *lemma* sub_sub_cancel
- \- *lemma* inv_zero
- \- *lemma* inv_infty
- \- *lemma* inv_of_real
- \- *lemma* inv_inv
- \- *theorem* le_def
- \- *def* of_real
- \- *def* of_ennreal

Modified data/real/basic.lean
- \+ *lemma* Sup_is_lub

Created data/real/ennreal.lean
- \+ *lemma* of_ennreal_of_real
- \+ *lemma* zero_le_of_ennreal
- \+ *lemma* of_real_of_ennreal
- \+ *lemma* forall_ennreal
- \+ *lemma* of_real_zero
- \+ *lemma* of_real_one
- \+ *lemma* zero_ne_infty
- \+ *lemma* infty_ne_zero
- \+ *lemma* of_real_ne_infty
- \+ *lemma* infty_ne_of_real
- \+ *lemma* of_real_eq_of_real_of
- \+ *lemma* of_real_ne_of_real_of
- \+ *lemma* of_real_of_nonpos
- \+ *lemma* of_real_of_not_nonneg
- \+ *lemma* of_real_eq_zero_iff
- \+ *lemma* zero_eq_of_real_iff
- \+ *lemma* of_real_eq_one_iff
- \+ *lemma* one_eq_of_real_iff
- \+ *lemma* of_nonneg_real_eq_of_real
- \+ *lemma* of_real_add
- \+ *lemma* add_infty
- \+ *lemma* infty_add
- \+ *lemma* of_real_mul_of_real
- \+ *lemma* of_real_mul_infty
- \+ *lemma* infty_mul_of_real
- \+ *lemma* mul_infty
- \+ *lemma* infty_mul
- \+ *lemma* sum_of_real
- \+ *lemma* infty_le_iff
- \+ *lemma* le_infty
- \+ *lemma* of_real_le_of_real_iff
- \+ *lemma* one_le_of_real_iff
- \+ *lemma* not_infty_lt
- \+ *lemma* of_real_lt_infty
- \+ *lemma* le_of_real_iff
- \+ *lemma* of_real_lt_of_real_iff
- \+ *lemma* lt_iff_exists_of_real
- \+ *lemma* le_zero_iff_eq
- \+ *lemma* zero_lt_of_real_iff
- \+ *lemma* not_lt_zero
- \+ *lemma* of_real_le_of_real
- \+ *lemma* of_real_lt_of_real_iff_cases
- \+ *lemma* le_add_left
- \+ *lemma* le_add_right
- \+ *lemma* lt_add_right
- \+ *lemma* of_real_add_le
- \+ *lemma* mul_le_mul
- \+ *lemma* le_of_forall_epsilon_le
- \+ *lemma* infty_mem_upper_bounds
- \+ *lemma* of_real_mem_upper_bounds
- \+ *lemma* is_lub_of_real
- \+ *lemma* sub_eq_zero_of_le
- \+ *lemma* sub_le_sub
- \+ *lemma* zero_sub
- \+ *lemma* sub_infty
- \+ *lemma* infty_sub_of_real
- \+ *lemma* of_real_sub_of_real
- \+ *lemma* add_sub_self
- \+ *lemma* add_sub_self'
- \+ *lemma* add_left_inj
- \+ *lemma* add_right_inj
- \+ *lemma* sub_add_cancel_of_le
- \+ *lemma* add_sub_cancel_of_le
- \+ *lemma* sub_add_self_eq_max
- \+ *lemma* sub_le_self
- \+ *lemma* sub_zero
- \+ *lemma* sub_sub_cancel
- \+ *lemma* inv_zero
- \+ *lemma* inv_infty
- \+ *lemma* inv_of_real
- \+ *lemma* inv_inv
- \+ *theorem* le_def
- \+ *def* of_real
- \+ *def* of_ennreal

Modified data/set/lattice.lean
- \+ *def* kern_image

Modified order/bounds.lean

Modified order/galois_connection.lean
- \- *def* kern_image



## [2018-07-20 01:17:21-04:00](https://github.com/leanprover-community/mathlib/commit/23a5591)
feat(tactic/h_generalize): remove `cast` expressions from goal ([#198](https://github.com/leanprover-community/mathlib/pull/198))
#### Estimated changes
Modified docs/tactics.md

Modified tactic/interactive.lean

Modified tests/tactics.lean



## [2018-07-19 15:34:44-04:00](https://github.com/leanprover-community/mathlib/commit/29639b3)
feat(analysis/measure_theory): optimize proofs; trim, is_complete
#### Estimated changes
Modified algebra/ordered_field.lean
- \+ *lemma* one_half_pos
- \+ *lemma* one_half_lt_one

Modified analysis/ennreal.lean
- \+ *lemma* of_real_add_le
- \+ *lemma* add_supr
- \+ *lemma* supr_add_supr
- \+ *lemma* sub_le_self
- \+ *lemma* add_sub_self'
- \+ *lemma* add_left_inj
- \+ *lemma* add_right_inj
- \+ *lemma* sub_sub_cancel
- \+/\- *lemma* sub_supr
- \+ *lemma* sub_infi
- \+/\- *lemma* sub_supr
- \+ *theorem* exists_pos_sum_of_encodable

Modified analysis/limits.lean
- \+ *lemma* is_sum_geometric_two
- \+ *def* pos_sum_of_encodable

Modified analysis/measure_theory/borel_space.lean
- \+ *lemma* borel_prod_le
- \- *lemma* is_topological_basis_Ioo_rat
- \+ *def* borel

Modified analysis/measure_theory/lebesgue_measure.lean
- \+/\- *lemma* lebesgue_length_empty
- \+/\- *lemma* lebesgue_length_Ico
- \+ *lemma* lebesgue_length_mono
- \+ *lemma* lebesgue_length_eq_infi_Ioo
- \+ *lemma* lebesgue_length_Ioo
- \+ *lemma* lebesgue_length_eq_infi_Icc
- \+ *lemma* lebesgue_length_Icc
- \+ *lemma* lebesgue_outer_le_length
- \+/\- *lemma* lebesgue_length_subadditive
- \+ *lemma* lebesgue_outer_Icc
- \+ *lemma* lebesgue_outer_singleton
- \+/\- *lemma* lebesgue_outer_Ico
- \+ *lemma* lebesgue_outer_Ioo
- \+ *lemma* is_lebesgue_measurable_Iio
- \+ *lemma* lebesgue_Icc
- \+/\- *lemma* lebesgue_singleton
- \- *lemma* lebesgue_length_Ico'
- \+/\- *lemma* lebesgue_length_empty
- \+/\- *lemma* lebesgue_length_Ico
- \- *lemma* le_lebesgue_length
- \+/\- *lemma* lebesgue_length_subadditive
- \+/\- *lemma* lebesgue_outer_Ico
- \- *lemma* lebesgue_outer_is_measurable_Iio
- \- *lemma* tendsto_of_nat_at_top_at_top
- \+/\- *lemma* lebesgue_singleton
- \+ *theorem* lebesgue_outer_trim
- \+ *theorem* lebesgue_to_outer_measure
- \+ *theorem* lebesgue_val
- \+/\- *def* lebesgue_length
- \+/\- *def* lebesgue
- \+/\- *def* lebesgue_length
- \+/\- *def* lebesgue

Modified analysis/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable.empty
- \+ *lemma* is_measurable.compl
- \+ *lemma* is_measurable.compl_iff
- \+ *lemma* encodable.Union_decode2
- \+ *lemma* encodable.Union_decode2_cases
- \+ *lemma* is_measurable.Union
- \+ *lemma* is_measurable.bUnion
- \+ *lemma* is_measurable.sUnion
- \+ *lemma* is_measurable.Inter
- \+ *lemma* is_measurable.bInter
- \+ *lemma* is_measurable.sInter
- \+ *lemma* is_measurable.union
- \+ *lemma* is_measurable.inter
- \+ *lemma* is_measurable.diff
- \+ *lemma* is_measurable.sub
- \+ *lemma* is_measurable.disjointed
- \+ *lemma* measurable_space.ext
- \+ *lemma* measurable.preimage
- \+ *lemma* measurable.comp
- \+ *lemma* measurable.if
- \+ *lemma* measurable.prod
- \+ *lemma* ext
- \+ *lemma* has_compl_iff
- \+/\- *lemma* has_univ
- \+ *lemma* has_diff
- \+/\- *lemma* generate_le
- \- *lemma* is_measurable_empty
- \- *lemma* is_measurable_compl
- \- *lemma* is_measurable_Union_nat
- \- *lemma* is_measurable_sUnion
- \- *lemma* is_measurable_bUnion
- \- *lemma* is_measurable_Union
- \- *lemma* is_measurable_sInter
- \- *lemma* is_measurable_bInter
- \- *lemma* is_measurable_Inter
- \- *lemma* is_measurable_union
- \- *lemma* is_measurable_inter
- \- *lemma* is_measurable_sdiff
- \- *lemma* is_measurable_sub
- \- *lemma* is_measurable_disjointed
- \- *lemma* measurable_space_eq
- \- *lemma* measurable_comp
- \- *lemma* measurable_if
- \- *lemma* measurable_prod
- \- *lemma* dynkin_system_eq
- \+/\- *lemma* has_univ
- \- *lemma* has_union
- \- *lemma* has_sdiff
- \+/\- *lemma* generate_le
- \+ *theorem* is_measurable_Inf
- \+ *theorem* is_measurable_infi
- \+ *theorem* is_measurable_inf
- \+ *theorem* Union_decode2_disjoint_on
- \+ *theorem* has_Union
- \+ *theorem* has_union
- \+/\- *def* is_measurable
- \+/\- *def* restrict_on
- \+/\- *def* is_measurable
- \+/\- *def* restrict_on

Modified analysis/measure_theory/measure_space.lean
- \+ *lemma* measure'_eq
- \+ *lemma* measure'_empty
- \+ *lemma* measure'_Union_nat
- \+ *lemma* measure'_Union_le_tsum_nat'
- \+ *lemma* measure'_Union
- \+ *lemma* measure'_union
- \+ *lemma* measure'_mono
- \+ *lemma* measure'_Union_le_tsum_nat
- \+ *lemma* outer_measure'_eq
- \+ *lemma* outer_measure'_eq_measure'
- \+ *lemma* ext
- \+ *lemma* to_outer_measure_apply
- \+ *lemma* measure_eq_trim
- \+ *lemma* measure_eq_infi
- \+ *lemma* measure_eq_outer_measure'
- \+ *lemma* to_outer_measure_eq_outer_measure'
- \+ *lemma* measure_eq_measure'
- \+/\- *lemma* measure_empty
- \+/\- *lemma* measure_mono
- \+ *lemma* measure_mono_null
- \+ *lemma* measure_Union_null
- \+ *lemma* measure_union_null
- \+ *lemma* measure_Union
- \+/\- *lemma* measure_union
- \+/\- *lemma* measure_bUnion
- \+/\- *lemma* measure_sUnion
- \+ *lemma* measure_diff
- \+/\- *lemma* le_to_outer_measure_caratheodory
- \+ *lemma* to_measure_to_outer_measure
- \+ *lemma* to_measure_apply
- \+/\- *lemma* to_outer_measure_to_measure
- \+/\- *lemma* map_id
- \+ *lemma* map_map
- \+ *lemma* dirac_apply
- \- *lemma* measure_space_eq_of
- \- *lemma* measure_space_eq
- \+/\- *lemma* measure_empty
- \+/\- *lemma* measure_mono
- \- *lemma* measure_Union_le_tsum_nat
- \+/\- *lemma* measure_union
- \- *lemma* measure_Union_nat
- \+/\- *lemma* measure_bUnion
- \+/\- *lemma* measure_sUnion
- \- *lemma* measure_sdiff
- \+/\- *lemma* le_to_outer_measure_caratheodory
- \+/\- *lemma* to_outer_measure_to_measure
- \- *lemma* map_measure
- \+/\- *lemma* map_id
- \- *lemma* map_comp
- \+ *theorem* trim_ge
- \+ *theorem* trim_eq
- \+ *theorem* trim_congr
- \+ *theorem* trim_le_trim
- \+ *theorem* le_trim_iff
- \+ *theorem* trim_eq_infi
- \+ *theorem* trim_eq_infi'
- \+ *theorem* trim_trim
- \+ *theorem* trim_zero
- \+ *theorem* trim_add
- \+ *theorem* trim_sum_ge
- \+ *theorem* measure_Union_le
- \+ *theorem* measure_union_le
- \+ *theorem* zero_to_outer_measure
- \+ *theorem* zero_apply
- \+ *theorem* add_to_outer_measure
- \+ *theorem* add_apply
- \+ *theorem* le_iff
- \+ *theorem* to_outer_measure_le
- \+ *theorem* le_iff'
- \+ *theorem* map_apply
- \+ *theorem* is_null_measurable_iff
- \+ *theorem* is_null_measurable_measure_eq
- \+ *theorem* is_measurable.is_null_measurable
- \+ *theorem* is_null_measurable_of_complete
- \+ *theorem* is_null_measurable.union_null
- \+ *theorem* null_is_null_measurable
- \+ *theorem* is_null_measurable.Union_nat
- \+ *theorem* is_measurable.diff_null
- \+ *theorem* is_null_measurable.diff_null
- \+ *theorem* is_null_measurable.compl
- \+ *def* measure'
- \+ *def* outer_measure'
- \+ *def* trim
- \+ *def* of_measurable
- \+/\- *def* outer_measure.to_measure
- \+/\- *def* map
- \+/\- *def* dirac
- \+/\- *def* sum
- \+/\- *def* count
- \+ *def* is_complete
- \+ *def* is_null_measurable
- \+ *def* null_measurable
- \+ *def* completion
- \+/\- *def* outer_measure.to_measure
- \+/\- *def* map
- \+/\- *def* dirac
- \+/\- *def* sum
- \+/\- *def* count

Modified analysis/measure_theory/outer_measure.lean
- \+ *lemma* Union_null
- \+ *lemma* union_null
- \+ *lemma* ext
- \+ *lemma* is_caratheodory
- \+ *lemma* is_caratheodory_le
- \- *lemma* subadditive
- \- *lemma* outer_measure_eq
- \- *lemma* caratheodory_is_measurable_eq
- \+ *theorem* empty'
- \+ *theorem* mono'
- \+ *theorem* Union_aux
- \+ *theorem* zero_apply
- \+ *theorem* add_apply
- \+ *theorem* Sup_apply
- \+ *theorem* supr_apply
- \+ *theorem* sup_apply
- \+ *theorem* map_apply
- \+ *theorem* map_id
- \+ *theorem* map_map
- \+ *theorem* dirac_apply
- \+ *theorem* sum_apply
- \+ *theorem* smul_apply
- \+ *theorem* smul_add
- \+ *theorem* add_smul
- \+ *theorem* mul_smul
- \+ *theorem* one_smul
- \+ *theorem* zero_smul
- \+ *theorem* smul_zero
- \+ *theorem* smul_dirac_apply
- \+ *theorem* top_apply
- \+ *theorem* le_of_function
- \+ *theorem* zero_caratheodory
- \+ *theorem* le_add_caratheodory
- \+ *theorem* le_sum_caratheodory
- \+ *theorem* le_smul_caratheodory
- \+ *theorem* dirac_caratheodory
- \+ *def* map
- \+ *def* dirac
- \+ *def* sum
- \+ *def* smul

Modified analysis/real.lean
- \+ *lemma* real.is_topological_basis_Ioo_rat
- \+/\- *lemma* real.totally_bounded_Icc
- \+/\- *lemma* rat.totally_bounded_Icc
- \+ *lemma* tendsto_of_nat_at_top_at_top
- \+ *lemma* compact_Icc
- \+/\- *lemma* real.totally_bounded_Icc
- \+/\- *lemma* rat.totally_bounded_Icc
- \- *lemma* compact_ivl

Modified analysis/topology/infinite_sum.lean
- \+ *lemma* tsum_fintype
- \+ *lemma* tsum_equiv
- \+/\- *lemma* is_sum_mul_left
- \+/\- *lemma* is_sum_mul_right
- \+/\- *lemma* has_sum_mul_left
- \+/\- *lemma* has_sum_mul_right
- \+/\- *lemma* tsum_mul_left
- \+/\- *lemma* tsum_mul_right
- \+/\- *lemma* is_sum_mul_left
- \+/\- *lemma* is_sum_mul_right
- \+/\- *lemma* has_sum_mul_left
- \+/\- *lemma* has_sum_mul_right
- \+/\- *lemma* tsum_mul_left
- \+/\- *lemma* tsum_mul_right

Modified analysis/topology/topological_space.lean
- \+ *lemma* is_open_sUnion_countable

Modified analysis/topology/topological_structures.lean
- \+ *lemma* is_closed_Icc
- \+/\- *lemma* closure_le_eq
- \+/\- *lemma* closure_le_eq

Modified data/set/basic.lean
- \+/\- *theorem* mem_diff
- \+ *theorem* mem_diff_of_mem
- \+ *theorem* union_diff_distrib
- \+/\- *theorem* mem_diff
- \- *theorem* mem_diff_iff
- \- *theorem* mem_diff_eq

Modified data/set/countable.lean

Modified data/set/disjointed.lean
- \+ *lemma* Union_lt_succ
- \+ *lemma* Inter_lt_succ
- \+ *lemma* Union_disjointed
- \+ *lemma* Union_disjointed_of_mono
- \- *lemma* disjointed_Union
- \+ *theorem* pairwise_on_bool
- \+ *theorem* pairwise_disjoint_on_bool

Modified data/set/intervals.lean
- \+ *lemma* mem_Ioo
- \+ *lemma* mem_Ico
- \+ *lemma* mem_Icc
- \+ *lemma* mem_Iio
- \+ *lemma* Ioo_eq_empty
- \+/\- *lemma* Ico_eq_empty
- \+ *lemma* Icc_eq_empty
- \+/\- *lemma* Ioo_self
- \+/\- *lemma* Ico_self
- \+ *lemma* Iio_ne_empty
- \+ *lemma* Ioo_subset_Ioo
- \+ *lemma* Ioo_subset_Ioo_left
- \+ *lemma* Ioo_subset_Ioo_right
- \+ *lemma* Ico_subset_Ico
- \+/\- *lemma* Ico_subset_Ico_left
- \+/\- *lemma* Ico_subset_Ico_right
- \+ *lemma* Icc_subset_Icc
- \+ *lemma* Icc_subset_Icc_left
- \+ *lemma* Icc_subset_Icc_right
- \+ *lemma* Icc_subset_Ico_right
- \+/\- *lemma* Ioo_subset_Ico_self
- \+ *lemma* Ico_subset_Icc_self
- \+ *lemma* Ioo_subset_Icc_self
- \+/\- *lemma* Ico_subset_Iio_self
- \+ *lemma* Icc_self
- \+ *lemma* Ico_diff_Ioo_eq_singleton
- \+ *lemma* Icc_diff_Ico_eq_singleton
- \+ *lemma* Ioo_eq_empty_iff
- \+/\- *lemma* Ico_eq_empty_iff
- \+ *lemma* Icc_eq_empty_iff
- \+/\- *lemma* Ico_subset_Ico_iff
- \+ *lemma* Ioo_subset_Ioo_iff
- \+/\- *lemma* Ico_eq_Ico_iff
- \+ *lemma* Ico_diff_Iio
- \+ *lemma* Ico_inter_Iio
- \- *lemma* Ioo_eq_empty_of_ge
- \+/\- *lemma* Ico_eq_empty_iff
- \+/\- *lemma* Ico_eq_empty
- \+/\- *lemma* Ico_self
- \+/\- *lemma* Ico_subset_Ico_iff
- \+/\- *lemma* Ico_subset_Ico_left
- \+/\- *lemma* Ico_subset_Ico_right
- \+/\- *lemma* Ioo_subset_Ico_self
- \+/\- *lemma* Ico_subset_Iio_self
- \+/\- *lemma* Ioo_self
- \- *lemma* Ico_sdiff_Ioo_eq_singleton
- \+/\- *lemma* Ico_eq_Ico_iff
- \- *lemma* Ico_sdiff_Iio_eq
- \- *lemma* Ico_inter_Iio_eq
- \+ *def* Icc

Modified order/complete_lattice.lean
- \+/\- *theorem* infi_and
- \+/\- *theorem* supr_and
- \+/\- *theorem* infi_subtype
- \+/\- *theorem* supr_subtype
- \+/\- *theorem* infi_sigma
- \+/\- *theorem* supr_sigma
- \+/\- *theorem* infi_prod
- \+/\- *theorem* supr_prod
- \+/\- *theorem* infi_and
- \+/\- *theorem* supr_and
- \+/\- *theorem* infi_subtype
- \+/\- *theorem* supr_subtype
- \+/\- *theorem* infi_sigma
- \+/\- *theorem* supr_sigma
- \+/\- *theorem* infi_prod
- \+/\- *theorem* supr_prod



## [2018-07-19 10:10:59-04:00](https://github.com/leanprover-community/mathlib/commit/bd90a93)
fix(group_theory/group_action): move is_group_action out of namespace
#### Estimated changes
Modified group_theory/group_action.lean



## [2018-07-19 09:29:24-04:00](https://github.com/leanprover-community/mathlib/commit/2b9780a)
feat(data/finset): disjoint_val ([#206](https://github.com/leanprover-community/mathlib/pull/206))
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* disjoint_val



## [2018-07-19 09:29:24-04:00](https://github.com/leanprover-community/mathlib/commit/1e0c38b)
feat(data/multiset): sup and inf for multisets
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* sup_val
- \+ *lemma* inf_val

Modified data/multiset.lean
- \+ *lemma* sup_zero
- \+ *lemma* sup_cons
- \+ *lemma* sup_singleton
- \+ *lemma* sup_add
- \+ *lemma* sup_erase_dup
- \+ *lemma* sup_ndunion
- \+ *lemma* sup_union
- \+ *lemma* sup_ndinsert
- \+ *lemma* sup_le
- \+ *lemma* le_sup
- \+ *lemma* sup_mono
- \+ *lemma* inf_zero
- \+ *lemma* inf_cons
- \+ *lemma* inf_singleton
- \+ *lemma* inf_add
- \+ *lemma* inf_erase_dup
- \+ *lemma* inf_ndunion
- \+ *lemma* inf_union
- \+ *lemma* inf_ndinsert
- \+ *lemma* le_inf
- \+ *lemma* inf_le
- \+ *lemma* inf_mono
- \+ *theorem* prod_singleton
- \+ *def* sup
- \+ *def* inf



## [2018-07-19 06:54:38-04:00](https://github.com/leanprover-community/mathlib/commit/50f18e6)
feat(group_theory/group_action): group actions and orbit stabilizer ([#204](https://github.com/leanprover-community/mathlib/pull/204))
#### Estimated changes
Created group_theory/group_action.lean
- \+ *lemma* mem_orbit_iff
- \+ *lemma* mem_orbit
- \+ *lemma* mem_orbit_self
- \+ *lemma* mem_stabilizer_iff
- \+ *lemma* mem_fixed_points
- \+ *lemma* mem_fixed_points'
- \+ *lemma* bijective
- \+ *lemma* orbit_eq_iff
- \+ *def* orbit
- \+ *def* stabilizer
- \+ *def* fixed_points
- \+ *def* to_perm



## [2018-07-19 03:56:30-04:00](https://github.com/leanprover-community/mathlib/commit/9f79309)
fix(data/multiset): fix build, cleanup mem_pi
#### Estimated changes
Modified data/multiset.lean
- \+/\- *lemma* pi_zero
- \+/\- *lemma* pi_zero
- \+ *theorem* singleton_eq_singleton
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton



## [2018-07-19 03:18:09-04:00](https://github.com/leanprover-community/mathlib/commit/37f3e32)
fix(algebra/big_operators): fix build
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* card_pi
- \+/\- *lemma* card_pi

Modified data/finset.lean
- \+/\- *lemma* pi_empty
- \+/\- *lemma* pi_empty
- \+/\- *theorem* singleton_eq_singleton
- \+/\- *theorem* insert_empty_eq_singleton
- \+ *theorem* card_singleton
- \+/\- *theorem* singleton_eq_singleton
- \+/\- *theorem* insert_empty_eq_singleton

Modified data/multiset.lean
- \+/\- *lemma* pi_zero
- \+/\- *lemma* pi_zero
- \+/\- *theorem* card_singleton
- \+/\- *theorem* card_singleton



## [2018-07-19 02:36:49-04:00](https://github.com/leanprover-community/mathlib/commit/aedbc12)
feat(data/fintype): card lemmas ([#168](https://github.com/leanprover-community/mathlib/pull/168))
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* prod_const
- \+ *lemma* sum_const
- \+ *lemma* card_pi

Modified data/fintype.lean
- \+ *lemma* fintype.card_le_of_injective
- \+ *lemma* fintype.card_eq_one_iff
- \+ *lemma* fintype.card_eq_zero_iff
- \+ *lemma* fintype.card_pos_iff
- \+ *lemma* fintype.card_le_one_iff
- \+ *lemma* fintype.card_pi
- \+ *lemma* fintype.card_fun



## [2018-07-19 00:25:14-04:00](https://github.com/leanprover-community/mathlib/commit/c2f54ad)
fix(tactic/refine_struct): fix support for source structures
#### Estimated changes
Modified tactic/interactive.lean

Modified tests/examples.lean



## [2018-07-18 14:10:50+02:00](https://github.com/leanprover-community/mathlib/commit/9a30235)
chore(data/polynomial): move auxiliary definitions/theorems to appropriate places
#### Estimated changes
Modified algebra/ordered_group.lean
- \+ *lemma* coe_add
- \+ *lemma* bot_add
- \+ *lemma* add_bot
- \+ *lemma* coe_lt_coe
- \+ *lemma* bot_lt_some

Modified algebra/ring.lean

Modified data/finsupp.lean
- \+ *lemma* sum_mul
- \+ *lemma* mul_sum

Modified data/polynomial.lean
- \- *lemma* sum_mul
- \- *lemma* mul_sum
- \- *lemma* with_bot.coe_add
- \- *lemma* with_bot.bot_add
- \- *lemma* with_bot.add_bot
- \- *lemma* with_bot.coe_lt_coe
- \- *lemma* with_bot.bot_lt_some



## [2018-07-18 14:10:50+02:00](https://github.com/leanprover-community/mathlib/commit/d9daeff)
refactor(data/polynomial): move polynomials to data; replace monomial by `C a * X^n`
#### Estimated changes
Modified algebra/big_operators.lean

Modified data/finsupp.lean

Renamed linear_algebra/univariate_polynomial.lean to data/polynomial.lean
- \+ *lemma* sum_mul
- \+ *lemma* mul_sum
- \+/\- *lemma* with_bot.coe_add
- \+/\- *lemma* support_zero
- \+ *lemma* single_eq_C_mul_X
- \+/\- *lemma* zero_apply
- \+/\- *lemma* one_apply_zero
- \+/\- *lemma* add_apply
- \+ *lemma* X_apply_one
- \+/\- *lemma* C_0
- \+/\- *lemma* C_1
- \+/\- *lemma* C_mul_C
- \+ *lemma* X_pow_apply
- \+/\- *lemma* eval_C
- \+/\- *lemma* eval_X
- \+ *lemma* eval_one
- \+/\- *lemma* degree_C
- \+ *lemma* degree_C_le
- \+ *lemma* degree_one_le
- \+/\- *lemma* degree_monomial
- \+/\- *lemma* degree_monomial_le
- \+/\- *lemma* leading_coeff_monomial
- \+/\- *lemma* leading_coeff_X
- \+/\- *lemma* leading_coeff_one
- \+/\- *lemma* ne_zero_of_ne_zero_of_monic
- \+/\- *lemma* degree_mod_by_monic_lt
- \+/\- *lemma* subsingleton_of_monic_zero
- \+/\- *lemma* mod_by_monic_add_div
- \+/\- *lemma* degree_add_div_by_monic
- \+/\- *lemma* degree_div_by_monic_lt
- \+/\- *lemma* degree_X
- \+/\- *lemma* not_monic_zero
- \+/\- *lemma* ne_zero_of_monic
- \+/\- *lemma* root_X_sub_C
- \+/\- *lemma* mul_div_by_monic_eq_iff_is_root
- \+/\- *lemma* degree_pow_eq
- \+/\- *lemma* leading_coeff_mul
- \+/\- *lemma* monic_mul_leading_coeff_inv
- \+/\- *lemma* with_bot.coe_add
- \+/\- *lemma* C_0
- \+/\- *lemma* C_1
- \- *lemma* C_mul_monomial
- \+/\- *lemma* C_mul_C
- \- *lemma* monomial_mul_monomial
- \- *lemma* monomial_zero_right
- \- *lemma* X_pow_eq_monomial
- \- *lemma* monomial_add_right
- \- *lemma* monomial_add_left
- \- *lemma* monomial_eq
- \+/\- *lemma* support_zero
- \- *lemma* induction_on
- \- *lemma* monomial_apply
- \- *lemma* monomial_apply_self
- \+/\- *lemma* zero_apply
- \+/\- *lemma* one_apply_zero
- \+/\- *lemma* add_apply
- \- *lemma* monomial_induction_on
- \- *lemma* eval_monomial
- \+/\- *lemma* eval_C
- \+/\- *lemma* eval_X
- \- *lemma* eval_mul_monomial
- \+/\- *lemma* degree_C
- \+/\- *lemma* degree_monomial_le
- \+/\- *lemma* degree_monomial
- \+/\- *lemma* leading_coeff_monomial
- \+/\- *lemma* leading_coeff_X
- \+/\- *lemma* leading_coeff_one
- \+/\- *lemma* ne_zero_of_ne_zero_of_monic
- \+/\- *lemma* degree_mod_by_monic_lt
- \+/\- *lemma* subsingleton_of_monic_zero
- \+/\- *lemma* mod_by_monic_add_div
- \+/\- *lemma* degree_add_div_by_monic
- \+/\- *lemma* degree_div_by_monic_lt
- \+/\- *lemma* not_monic_zero
- \+/\- *lemma* ne_zero_of_monic
- \+/\- *lemma* degree_X
- \+/\- *lemma* root_X_sub_C
- \+/\- *lemma* mul_div_by_monic_eq_iff_is_root
- \+/\- *lemma* degree_pow_eq
- \+/\- *lemma* leading_coeff_mul
- \+/\- *lemma* monic_mul_leading_coeff_inv
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* degree
- \+/\- *def* degree_lt_wf
- \+/\- *def* nat_degree
- \+/\- *def* div_mod_by_monic_aux
- \+/\- *def* div
- \- *def* monomial
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* degree
- \+/\- *def* nat_degree
- \+/\- *def* degree_lt_wf
- \+/\- *def* div_mod_by_monic_aux
- \+/\- *def* div



## [2018-07-18 14:10:50+02:00](https://github.com/leanprover-community/mathlib/commit/ce990c5)
feat(linear_algebra/univariate_polynomial): univariate polynomials
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* max_eq_none
- \+ *theorem* min_eq_none

Created linear_algebra/univariate_polynomial.lean
- \+ *lemma* with_bot.coe_add
- \+ *lemma* with_bot.bot_add
- \+ *lemma* with_bot.add_bot
- \+ *lemma* with_bot.coe_lt_coe
- \+ *lemma* with_bot.bot_lt_some
- \+ *lemma* C_0
- \+ *lemma* C_1
- \+ *lemma* C_mul_monomial
- \+ *lemma* C_mul_C
- \+ *lemma* monomial_mul_monomial
- \+ *lemma* monomial_zero_right
- \+ *lemma* X_pow_eq_monomial
- \+ *lemma* monomial_add_right
- \+ *lemma* monomial_add_left
- \+ *lemma* monomial_eq
- \+ *lemma* support_zero
- \+ *lemma* induction_on
- \+ *lemma* monomial_apply
- \+ *lemma* monomial_apply_self
- \+ *lemma* C_apply
- \+ *lemma* C_apply_zero
- \+ *lemma* zero_apply
- \+ *lemma* one_apply_zero
- \+ *lemma* add_apply
- \+ *lemma* C_mul_apply
- \+ *lemma* monomial_induction_on
- \+ *lemma* eval_zero
- \+ *lemma* eval_add
- \+ *lemma* eval_monomial
- \+ *lemma* eval_C
- \+ *lemma* eval_X
- \+ *lemma* eval_mul_monomial
- \+ *lemma* eval_mul
- \+ *lemma* is_root.def
- \+ *lemma* root_mul_left_of_is_root
- \+ *lemma* root_mul_right_of_is_root
- \+ *lemma* monic.def
- \+ *lemma* degree_zero
- \+ *lemma* degree_C
- \+ *lemma* degree_eq_bot
- \+ *lemma* degree_eq_nat_degree
- \+ *lemma* nat_degree_eq_of_degree_eq
- \+ *lemma* nat_degree_C
- \+ *lemma* degree_monomial_le
- \+ *lemma* degree_monomial
- \+ *lemma* le_degree_of_ne_zero
- \+ *lemma* eq_zero_of_degree_lt
- \+ *lemma* ne_zero_of_degree_gt
- \+ *lemma* eq_C_of_degree_le_zero
- \+ *lemma* degree_add_le
- \+ *lemma* leading_coeff_zero
- \+ *lemma* leading_coeff_eq_zero
- \+ *lemma* degree_add_eq_of_degree_lt
- \+ *lemma* degree_add_eq_of_leading_coeff_add_ne_zero
- \+ *lemma* degree_erase_le
- \+ *lemma* degree_erase_lt
- \+ *lemma* degree_sum_le
- \+ *lemma* degree_mul_le
- \+ *lemma* degree_pow_le
- \+ *lemma* leading_coeff_monomial
- \+ *lemma* leading_coeff_C
- \+ *lemma* leading_coeff_X
- \+ *lemma* leading_coeff_one
- \+ *lemma* monic_one
- \+ *lemma* leading_coeff_add_of_degree_lt
- \+ *lemma* leading_coeff_add_of_degree_eq
- \+ *lemma* mul_apply_degree_add_degree
- \+ *lemma* degree_mul_eq'
- \+ *lemma* nat_degree_mul_eq'
- \+ *lemma* leading_coeff_mul'
- \+ *lemma* leading_coeff_pow'
- \+ *lemma* degree_pow_eq'
- \+ *lemma* degree_neg
- \+ *lemma* neg_apply
- \+ *lemma* eval_neg
- \+ *lemma* eval_sub
- \+ *lemma* degree_sub_lt
- \+ *lemma* ne_zero_of_ne_zero_of_monic
- \+ *lemma* div_wf_lemma
- \+ *lemma* degree_mod_by_monic_lt
- \+ *lemma* mod_by_monic_eq_sub_mul_div
- \+ *lemma* subsingleton_of_monic_zero
- \+ *lemma* mod_by_monic_add_div
- \+ *lemma* zero_mod_by_monic
- \+ *lemma* zero_div_by_monic
- \+ *lemma* mod_by_monic_zero
- \+ *lemma* div_by_monic_zero
- \+ *lemma* div_by_monic_eq_of_not_monic
- \+ *lemma* mod_by_monic_eq_of_not_monic
- \+ *lemma* mod_by_monic_eq_self_iff
- \+ *lemma* div_by_monic_eq_zero_iff
- \+ *lemma* degree_add_div_by_monic
- \+ *lemma* degree_div_by_monic_le
- \+ *lemma* degree_div_by_monic_lt
- \+ *lemma* dvd_iff_mod_by_monic_eq_zero
- \+ *lemma* degree_one
- \+ *lemma* not_monic_zero
- \+ *lemma* ne_zero_of_monic
- \+ *lemma* degree_X
- \+ *lemma* degree_X_sub_C
- \+ *lemma* monic_X_sub_C
- \+ *lemma* root_X_sub_C
- \+ *lemma* mod_by_monic_X_sub_C_eq_C_eval
- \+ *lemma* mul_div_by_monic_eq_iff_is_root
- \+ *lemma* degree_mul_eq
- \+ *lemma* degree_pow_eq
- \+ *lemma* leading_coeff_mul
- \+ *lemma* leading_coeff_pow
- \+ *lemma* root_or_root_of_root_mul
- \+ *lemma* degree_pos_of_root
- \+ *lemma* exists_finset_roots
- \+ *lemma* card_roots
- \+ *lemma* mem_roots
- \+ *lemma* monic_mul_leading_coeff_inv
- \+ *lemma* degree_mul_leading_coeff_inv
- \+ *lemma* mod_by_monic_eq_mod
- \+ *lemma* div_by_monic_eq_div
- \+ *lemma* mod_X_sub_C_eq_C_eval
- \+ *lemma* mul_div_eq_iff_is_root
- \+ *lemma* degree_add_div
- \+ *def* polynomial
- \+ *def* monomial
- \+ *def* C
- \+ *def* X
- \+ *def* eval
- \+ *def* is_root
- \+ *def* degree
- \+ *def* nat_degree
- \+ *def* leading_coeff
- \+ *def* monic
- \+ *def* degree_lt_wf
- \+ *def* div_mod_by_monic_aux
- \+ *def* div_by_monic
- \+ *def* mod_by_monic
- \+ *def* div
- \+ *def* mod

Modified order/bounded_lattice.lean
- \+ *lemma* well_founded_lt
- \+ *lemma* well_founded_lt



## [2018-07-17 22:43:01-04:00](https://github.com/leanprover-community/mathlib/commit/a0dd286)
fix(*): fix build
#### Estimated changes
Modified analysis/ennreal.lean

Modified ring_theory/ideals.lean



## [2018-07-17 18:00:59-04:00](https://github.com/leanprover-community/mathlib/commit/7f8b088)
feat(tactic/basic): fix environment.in_current_file
#### Estimated changes
Modified tactic/basic.lean



## [2018-07-17 17:16:55-04:00](https://github.com/leanprover-community/mathlib/commit/980a01e)
feat(ring_theory/ideals): quotient rings ([#196](https://github.com/leanprover-community/mathlib/pull/196))
#### Estimated changes
Modified ring_theory/ideals.lean
- \+ *lemma* neg_iff
- \+ *lemma* mul_left
- \+ *lemma* mul_right
- \+ *lemma* is_proper_ideal_iff_one_not_mem
- \+ *lemma* quotient_eq_zero_iff_mem
- \+ *lemma* exists_inv
- \+ *theorem* not_unit_of_mem_proper_ideal
- \- *theorem* not_unit_of_mem_maximal_ideal
- \+ *def* quotient_rel
- \+ *def* quotient



## [2018-07-17 01:32:25-04:00](https://github.com/leanprover-community/mathlib/commit/421a1cd)
fix(measure_theory/measure_space): fix build
#### Estimated changes
Modified analysis/measure_theory/measure_space.lean



## [2018-07-17 00:35:02-04:00](https://github.com/leanprover-community/mathlib/commit/f92d239)
chore(travis.yml): checkout old files in both stages
#### Estimated changes
Modified .travis.yml



## [2018-07-17 00:30:54-04:00](https://github.com/leanprover-community/mathlib/commit/b267edc)
refactor(data/set/countable): define countable in terms of encodable
#### Estimated changes
Modified analysis/ennreal.lean

Modified analysis/measure_theory/borel_space.lean

Modified analysis/measure_theory/measurable_space.lean

Modified analysis/measure_theory/measure_space.lean

Modified analysis/topology/topological_space.lean

Modified computability/halting.lean

Modified data/equiv/encodable.lean
- \+ *theorem* mem_decode2'
- \+/\- *theorem* mem_decode2
- \+ *theorem* decode2_is_partial_inv
- \+/\- *theorem* mem_decode2

Modified data/set/countable.lean
- \+ *lemma* countable_iff_exists_injective
- \+ *lemma* countable_iff_exists_inj_on
- \+/\- *lemma* countable_encodable'
- \+/\- *lemma* countable_encodable
- \+/\- *lemma* countable_singleton
- \+/\- *lemma* countable_image
- \+ *lemma* countable_range
- \+/\- *lemma* countable_Union
- \+/\- *lemma* countable_sUnion
- \+/\- *lemma* countable_set_of_finite_subset
- \- *lemma* countable.to_encodable
- \+/\- *lemma* countable_encodable'
- \+/\- *lemma* countable_encodable
- \+/\- *lemma* countable_singleton
- \+/\- *lemma* countable_image
- \+/\- *lemma* countable_sUnion
- \+/\- *lemma* countable_Union
- \+/\- *lemma* countable_set_of_finite_subset
- \+/\- *def* countable
- \+ *def* countable.to_encodable
- \+/\- *def* countable

Modified data/set/function.lean
- \+ *lemma* inj_on_iff_injective
- \+ *lemma* surj_on_iff_surjective

Modified logic/function.lean
- \+ *theorem* is_partial_inv_left
- \+ *theorem* partial_inv_left



## [2018-07-16 23:17:06-04:00](https://github.com/leanprover-community/mathlib/commit/ee4ff47)
chore(travis.yml): update lean files before pre-build
#### Estimated changes
Modified .travis.yml



## [2018-07-16 22:13:58-04:00](https://github.com/leanprover-community/mathlib/commit/95a3c47)
fix(.): fix build
#### Estimated changes
Modified analysis/measure_theory/measurable_space.lean

Modified analysis/measure_theory/measure_space.lean

Modified analysis/measure_theory/outer_measure.lean

Modified analysis/topology/topological_space.lean

Modified data/finset.lean
- \+ *theorem* sup_eq_union
- \+ *theorem* inf_eq_inter
- \+/\- *theorem* disjoint_iff_inter_eq_empty
- \+/\- *theorem* disjoint_empty_left
- \+/\- *theorem* disjoint_empty_right
- \+/\- *theorem* disjoint_iff_inter_eq_empty
- \+/\- *theorem* disjoint_empty_left
- \+/\- *theorem* disjoint_empty_right

Modified data/set/disjointed.lean



## [2018-07-16 20:46:11-04:00](https://github.com/leanprover-community/mathlib/commit/bdc90f6)
feat(data/set/basic): more set theorems, normalize naming
#### Estimated changes
Modified algebra/module.lean
- \- *lemma* set.sInter_eq_Inter

Modified analysis/topology/topological_space.lean
- \+/\- *lemma* is_open_diff
- \+/\- *lemma* is_open_diff

Modified analysis/topology/uniform_space.lean

Modified data/analysis/topology.lean

Modified data/set/basic.lean
- \+ *lemma* compl_subset_compl
- \+/\- *theorem* union_subset_union
- \+ *theorem* union_subset_union_left
- \+ *theorem* union_subset_union_right
- \+/\- *theorem* inter_subset_inter_left
- \+/\- *theorem* inter_subset_inter_right
- \+ *theorem* union_inter_cancel_left
- \+ *theorem* union_inter_cancel_right
- \+ *theorem* union_diff_cancel_left
- \+ *theorem* union_diff_cancel_right
- \+ *theorem* union_diff_left
- \+ *theorem* union_diff_right
- \+ *theorem* inter_diff_assoc
- \+ *theorem* inter_diff_self
- \+ *theorem* inter_union_diff
- \+ *theorem* diff_subset_diff_left
- \+ *theorem* diff_subset_diff_right
- \+ *theorem* diff_eq_empty
- \+ *theorem* insert_diff
- \+ *theorem* union_diff_self
- \+ *theorem* diff_union_self
- \+ *theorem* diff_inter_self
- \+ *theorem* diff_eq_self
- \+ *theorem* diff_singleton_eq_self
- \+ *theorem* insert_diff_singleton
- \+/\- *theorem* union_subset_union
- \+/\- *theorem* inter_subset_inter_right
- \+/\- *theorem* inter_subset_inter_left
- \- *theorem* diff_right_antimono
- \- *theorem* diff_neq_empty
- \- *theorem* insert_sdiff

Modified data/set/disjointed.lean

Modified data/set/finite.lean

Modified data/set/lattice.lean
- \+ *lemma* sUnion_eq_bUnion
- \+ *lemma* sInter_eq_bInter
- \+/\- *lemma* sUnion_eq_Union
- \+ *lemma* sInter_eq_Inter
- \+ *lemma* union_eq_Union
- \+ *lemma* inter_eq_Inter
- \+/\- *lemma* sUnion_eq_Union
- \- *lemma* sUnion_eq_Union'
- \- *lemma* compl_subset_compl_iff_subset
- \- *lemma* union_of_subset_right
- \- *lemma* sdiff_empty
- \- *lemma* sdiff_eq:
- \- *lemma* union_sdiff_left
- \- *lemma* union_sdiff_right
- \- *lemma* disjoint_comm
- \+ *theorem* mem_Union
- \+/\- *theorem* mem_Inter
- \+ *theorem* mem_Inter_of_mem
- \+/\- *theorem* subset_Union
- \+ *theorem* Inter_subset
- \+ *theorem* Union_const
- \+ *theorem* Inter_const
- \+/\- *theorem* compl_Union
- \+/\- *theorem* compl_Inter
- \+/\- *theorem* Union_eq_comp_Inter_comp
- \+/\- *theorem* Inter_eq_comp_Union_comp
- \+ *theorem* inter_Union_left
- \+ *theorem* inter_Union_right
- \+ *theorem* Union_union_distrib
- \+ *theorem* Inter_inter_distrib
- \+ *theorem* union_Union_left
- \+ *theorem* union_Union_right
- \+ *theorem* inter_Inter_left
- \+ *theorem* inter_Inter_right
- \+ *theorem* union_Inter_left
- \+ *theorem* diff_Union_right
- \+ *theorem* diff_Union_left
- \+ *theorem* diff_Inter_left
- \+ *theorem* bUnion_eq_Union
- \+ *theorem* bInter_eq_Inter
- \+ *theorem* mem_sUnion_of_mem
- \+/\- *theorem* mem_sUnion
- \+/\- *theorem* mem_sInter
- \+/\- *theorem* sInter_subset_of_mem
- \+/\- *theorem* subset_sUnion_of_mem
- \+/\- *theorem* sUnion_subset_iff
- \+ *theorem* sUnion_subset_sUnion
- \+ *theorem* sInter_subset_sInter
- \+ *theorem* Union_eq_sUnion_range
- \+ *theorem* Inter_eq_sInter_range
- \+ *theorem* range_sigma_eq_Union_range
- \+ *theorem* Union_eq_range_sigma
- \+ *theorem* sub_eq_diff
- \+ *theorem* disjoint.eq_bot
- \+ *theorem* disjoint_iff
- \+ *theorem* disjoint.comm
- \+ *theorem* disjoint.symm
- \+/\- *theorem* disjoint_bot_left
- \+/\- *theorem* disjoint_bot_right
- \+ *theorem* set.disjoint_diff
- \- *theorem* mem_Union_eq
- \- *theorem* mem_Inter_eq
- \+/\- *theorem* mem_Inter
- \+/\- *theorem* compl_Union
- \+/\- *theorem* compl_Inter
- \+/\- *theorem* Union_eq_comp_Inter_comp
- \+/\- *theorem* Inter_eq_comp_Union_comp
- \- *theorem* inter_distrib_Union_left
- \- *theorem* inter_distrib_Union_right
- \- *theorem* union_distrib_Inter_left
- \+/\- *theorem* subset_Union
- \+/\- *theorem* mem_sUnion
- \- *theorem* mem_sUnion_eq
- \+/\- *theorem* mem_sInter
- \- *theorem* mem_sInter_eq
- \+/\- *theorem* sInter_subset_of_mem
- \+/\- *theorem* subset_sUnion_of_mem
- \+/\- *theorem* sUnion_subset_iff
- \- *theorem* Union_eq_sUnion_image
- \- *theorem* Inter_eq_sInter_image
- \- *theorem* union_sdiff_same
- \- *theorem* sdiff_union_same
- \- *theorem* sdiff_inter_same
- \- *theorem* sdiff_subset_sdiff
- \- *theorem* union_same_compl
- \- *theorem* sdiff_singleton_eq_same
- \- *theorem* insert_sdiff_singleton
- \- *theorem* disjoint_symm
- \+/\- *theorem* disjoint_bot_left
- \+/\- *theorem* disjoint_bot_right
- \+/\- *def* disjoint
- \+/\- *def* disjoint

Modified linear_algebra/basic.lean

Modified logic/schroeder_bernstein.lean

Modified order/filter.lean

Modified order/galois_connection.lean



## [2018-07-16 20:17:22-04:00](https://github.com/leanprover-community/mathlib/commit/9f6bcd0)
refactor(data/bool): decidable forall bool
#### Estimated changes
Modified data/bool.lean
- \+ *theorem* forall_bool
- \+ *theorem* exists_bool
- \+/\- *theorem* eq_tt_of_ne_ff
- \+/\- *theorem* eq_ff_of_ne_tt
- \+/\- *theorem* bor_comm
- \+/\- *theorem* bor_assoc
- \+/\- *theorem* bor_left_comm
- \+/\- *theorem* band_comm
- \+/\- *theorem* band_assoc
- \+/\- *theorem* band_left_comm
- \+/\- *theorem* band_elim_left
- \+/\- *theorem* band_intro
- \+/\- *theorem* band_elim_right
- \+/\- *theorem* eq_tt_of_bnot_eq_ff
- \+/\- *theorem* eq_ff_of_bnot_eq_tt
- \+/\- *theorem* bxor_comm
- \+/\- *theorem* bxor_assoc
- \+/\- *theorem* bxor_left_comm
- \+/\- *theorem* eq_tt_of_ne_ff
- \+/\- *theorem* eq_ff_of_ne_tt
- \- *theorem* absurd_of_eq_ff_of_eq_tt
- \+/\- *theorem* bor_comm
- \+/\- *theorem* bor_assoc
- \+/\- *theorem* bor_left_comm
- \+/\- *theorem* band_comm
- \+/\- *theorem* band_assoc
- \+/\- *theorem* band_left_comm
- \+/\- *theorem* band_elim_left
- \+/\- *theorem* band_intro
- \+/\- *theorem* band_elim_right
- \+/\- *theorem* eq_tt_of_bnot_eq_ff
- \+/\- *theorem* eq_ff_of_bnot_eq_tt
- \+/\- *theorem* bxor_comm
- \+/\- *theorem* bxor_assoc
- \+/\- *theorem* bxor_left_comm



## [2018-07-16 20:16:24-04:00](https://github.com/leanprover-community/mathlib/commit/8685bf2)
refactor(topology/continuity): remove inhabited from dense extend
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* extend_eq
- \+ *lemma* extend_e_eq
- \+ *lemma* tendsto_extend
- \+ *lemma* continuous_extend
- \- *lemma* ext_eq
- \- *lemma* ext_e_eq
- \- *lemma* tendsto_ext
- \- *lemma* continuous_ext
- \+ *def* extend
- \- *def* ext

Modified analysis/topology/uniform_space.lean



## [2018-07-16 20:03:13-04:00](https://github.com/leanprover-community/mathlib/commit/57f07e0)
refactor(data/set/basic): rename set.set_eq_def -> set.ext_iff
#### Estimated changes
Modified analysis/metric_space.lean

Modified data/finset.lean
- \+/\- *lemma* coe_union
- \+/\- *lemma* coe_inter
- \+/\- *lemma* coe_image
- \+/\- *lemma* coe_union
- \+/\- *lemma* coe_inter
- \+/\- *lemma* coe_image

Modified data/semiquot.lean

Modified data/set/basic.lean
- \+ *theorem* ext_iff
- \- *theorem* set_eq_def

Modified data/set/finite.lean

Modified group_theory/subgroup.lean

Modified linear_algebra/basic.lean

Modified order/filter.lean

Modified ring_theory/ideals.lean

Modified set_theory/zfc.lean



## [2018-07-16 19:52:54-04:00](https://github.com/leanprover-community/mathlib/commit/4c6d7e2)
feat(tactic/interactive): add apply_rules tactic ([#190](https://github.com/leanprover-community/mathlib/pull/190))
#### Estimated changes
Modified docs/tactics.md
- \+ *lemma* my_test

Modified tactic/basic.lean

Modified tactic/interactive.lean
- \+ *lemma* my_test

Modified tests/tactics.lean



## [2018-07-16 19:44:31-04:00](https://github.com/leanprover-community/mathlib/commit/6495c20)
feat(algebra/order_functions): abs_eq
#### Estimated changes
Modified algebra/order_functions.lean
- \+ *lemma* abs_eq



## [2018-07-16 19:42:41-04:00](https://github.com/leanprover-community/mathlib/commit/b0de694)
feat(tactic/tauto): improve coverage and performances of tauto ([#180](https://github.com/leanprover-community/mathlib/pull/180))
#### Estimated changes
Modified logic/basic.lean
- \+ *theorem* iff_iff_and_or_not_and_not

Modified tactic/basic.lean

Modified tactic/interactive.lean

Created tactic/tauto.lean

Modified tests/examples.lean

Modified tests/tactics.lean



## [2018-07-16 19:40:28-04:00](https://github.com/leanprover-community/mathlib/commit/c3e24f3)
docs(code-review): add check list ([#195](https://github.com/leanprover-community/mathlib/pull/195)) [ci-skip]
#### Estimated changes
Created PULL_REQUEST_TEMPLATE.md

Created docs/code-review.md



## [2018-07-16 19:39:17-04:00](https://github.com/leanprover-community/mathlib/commit/3a79975)
feat(data/quot): quot.hrec_on₂, quotient.hrec_on₂ ([#197](https://github.com/leanprover-community/mathlib/pull/197))
#### Estimated changes
Modified data/quot.lean



## [2018-07-16 19:34:21-04:00](https://github.com/leanprover-community/mathlib/commit/dd6cc57)
chore(build): make travis build fail quicker when errors are found
#### Estimated changes
Modified .travis.yml

Created travis_long.sh



## [2018-07-16 19:33:09-04:00](https://github.com/leanprover-community/mathlib/commit/631207b)
feat(data/multiset,...): card_eq_one
based on [#200](https://github.com/leanprover-community/mathlib/pull/200)
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* neg_one_pow_eq_or

Modified data/list/basic.lean
- \+ *theorem* length_eq_one

Modified data/multiset.lean
- \+ *theorem* empty_eq_zero
- \+ *theorem* strong_induction_eq
- \+ *theorem* card_eq_one

Modified logic/basic.lean
- \+ *lemma* and.congr_right_iff



## [2018-07-16 19:25:02-04:00](https://github.com/leanprover-community/mathlib/commit/ab8813a)
feat(tactic/interactive): alias "rintros" for "rintro"
#### Estimated changes
Modified tactic/interactive.lean



## [2018-07-16 15:11:29+01:00](https://github.com/leanprover-community/mathlib/commit/df8fc18)
feat(data/list/perm): extract cons_subperm_of_mem from subperm_of_subset_nodup ([#173](https://github.com/leanprover-community/mathlib/pull/173))
#### Estimated changes
Modified data/list/perm.lean
- \+ *theorem* cons_subperm_of_mem



## [2018-07-16 14:06:55+02:00](https://github.com/leanprover-community/mathlib/commit/20fca1c)
feat(data/finset): disjoint finsets
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* disjoint_iff_inter_eq_empty
- \+ *theorem* disjoint_left
- \+ *theorem* disjoint_right
- \+ *theorem* disjoint_iff_ne
- \+ *theorem* disjoint_of_subset_left
- \+ *theorem* disjoint_of_subset_right
- \+ *theorem* disjoint_empty_left
- \+ *theorem* disjoint_empty_right
- \+ *theorem* singleton_disjoint
- \+ *theorem* disjoint_singleton
- \+ *theorem* disjoint_insert_left
- \+ *theorem* disjoint_insert_right
- \+ *theorem* disjoint_union_left
- \+ *theorem* disjoint_union_right
- \+ *theorem* card_disjoint_union
- \- *theorem* inter_eq_empty_iff_disjoint

Modified data/set/lattice.lean
- \+ *lemma* disjoint_comm



## [2018-07-16 12:59:35+01:00](https://github.com/leanprover-community/mathlib/commit/844c665)
feat(category/applicative): `id` and `comp` functors; proofs by `norm` ([#184](https://github.com/leanprover-community/mathlib/pull/184))
#### Estimated changes
Created category/applicative.lean
- \+ *lemma* applicative.map_seq_map
- \+ *lemma* applicative.pure_seq_eq_map'
- \+ *lemma* map_pure
- \+ *lemma* seq_pure
- \+ *lemma* seq_assoc
- \+ *lemma* pure_seq_eq_map
- \+ *lemma* comp.seq_mk

Modified category/basic.lean
- \- *theorem* map_map
- \+ *def* mzip_with
- \+ *def* mzip_with'
- \- *def* mmap₂

Created category/functor.lean
- \+ *lemma* functor.map_id
- \+ *lemma* functor.map_comp_map
- \+ *lemma* comp.map_mk
- \+ *def* id.mk

Modified data/prod.lean

Modified data/set/basic.lean

Created tactic/ext.lean

Modified tactic/interactive.lean

Modified tests/tactics.lean



## [2018-07-12 18:02:46-04:00](https://github.com/leanprover-community/mathlib/commit/8dda9cd)
fix(analysis/topology/continuity): remove an extraneous constraint
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+/\- *lemma* continuous_subtype_is_closed_cover
- \+/\- *lemma* continuous_subtype_is_closed_cover



## [2018-07-12 18:00:11-04:00](https://github.com/leanprover-community/mathlib/commit/42ba098)
feat(data/set/basic): diff_subset_iff, diff_subset_comm
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* diff_subset_iff
- \+ *lemma* diff_subset_comm



## [2018-07-12 17:59:05-04:00](https://github.com/leanprover-community/mathlib/commit/17bf1ae)
feat(analysis/topology/continuity): embedding_inl, embedding_inr
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* embedding_inl
- \+ *lemma* embedding_inr



## [2018-07-12 08:42:03-04:00](https://github.com/leanprover-community/mathlib/commit/21b918b)
feat(data/fintype): decidable forall and exists ([#189](https://github.com/leanprover-community/mathlib/pull/189))
#### Estimated changes
Modified data/finset.lean

Modified data/fintype.lean

Modified data/multiset.lean
- \+ *def* decidable_exists_multiset



## [2018-07-11 21:00:56-04:00](https://github.com/leanprover-community/mathlib/commit/b1a314f)
chore(build): Break build process into two parts
#### Estimated changes
Modified .travis.yml



## [2018-07-11 01:33:37-04:00](https://github.com/leanprover-community/mathlib/commit/8d72f62)
Revert "chore(build): Break build process into two parts"
This reverts commit 890847df6618c5559a4170c36d61bf693f57086d.
#### Estimated changes
Modified .travis.yml



## [2018-07-11 00:08:43-04:00](https://github.com/leanprover-community/mathlib/commit/890847d)
chore(build): Break build process into two parts
#### Estimated changes
Modified .travis.yml



## [2018-07-08 15:26:47-04:00](https://github.com/leanprover-community/mathlib/commit/c8ad5cf)
fix(computability/turing_machine): fix import
#### Estimated changes
Modified computability/turing_machine.lean



## [2018-07-08 14:39:57-04:00](https://github.com/leanprover-community/mathlib/commit/e5d5abd)
feat(data/pfun,...): add some isomorphism theorems
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *theorem* set_value_eq
- \+ *def* set_value

Modified data/fintype.lean

Modified data/list/basic.lean
- \+ *theorem* filter_of_map

Modified data/multiset.lean
- \- *lemma* strong_induction_on
- \+ *def* strong_induction_on

Modified data/pfun.lean
- \+ *theorem* eta
- \+ *theorem* of_option_dom
- \+ *theorem* of_option_eq_get
- \+ *def* equiv_subtype



## [2018-07-07 02:03:44-04:00](https://github.com/leanprover-community/mathlib/commit/71953e0)
feat(order/basic): add extensionality for order structures
#### Estimated changes
Modified order/basic.lean
- \+ *theorem* preorder.ext
- \+ *theorem* partial_order.ext
- \+ *theorem* linear_order.ext

Modified order/bounded_lattice.lean
- \+ *theorem* order_top.ext_top
- \+ *theorem* order_top.ext
- \+ *theorem* order_bot.ext_bot
- \+ *theorem* order_bot.ext
- \+ *theorem* bounded_lattice.ext
- \+ *theorem* lattice_eq_DLO
- \+ *theorem* sup_eq_max
- \+ *theorem* inf_eq_min
- \+ *theorem* lattice_eq_DLO
- \+ *theorem* sup_eq_max
- \+ *theorem* inf_eq_min

Modified order/lattice.lean
- \+ *theorem* semilattice_sup.ext_sup
- \+ *theorem* semilattice_sup.ext
- \+ *theorem* semilattice_inf.ext_inf
- \+ *theorem* semilattice_inf.ext
- \+ *theorem* lattice.ext
- \+ *theorem* sup_eq_max
- \+ *theorem* inf_eq_min



## [2018-07-06 09:04:17-04:00](https://github.com/leanprover-community/mathlib/commit/ab1861a)
feat(data/subtype): setoid (subtype p)
#### Estimated changes
Modified data/subtype.lean
- \+ *theorem* equiv_iff
- \+ *theorem* equivalence



## [2018-07-06 09:04:17-04:00](https://github.com/leanprover-community/mathlib/commit/d54950a)
refactor(data/subtype): move out of data/sigma/basic.lean
#### Estimated changes
Modified data/equiv/denumerable.lean

Modified data/set/basic.lean

Modified data/sigma/basic.lean
- \- *lemma* subtype.ext
- \- *theorem* subtype.val_injective
- \- *theorem* subtype.coe_eta
- \- *theorem* subtype.coe_mk
- \- *theorem* subtype.mk_eq_mk
- \- *theorem* subtype.forall
- \- *theorem* subtype.exists
- \- *theorem* map_comp
- \- *theorem* map_id
- \- *def* map

Created data/subtype.lean
- \+ *lemma* subtype.ext
- \+ *theorem* subtype.val_injective
- \+ *theorem* subtype.coe_eta
- \+ *theorem* subtype.coe_mk
- \+ *theorem* subtype.mk_eq_mk
- \+ *theorem* subtype.forall
- \+ *theorem* subtype.exists
- \+ *theorem* map_comp
- \+ *theorem* map_id
- \+ *def* map

Modified data/vector2.lean

Modified order/basic.lean



## [2018-07-06 03:46:34-04:00](https://github.com/leanprover-community/mathlib/commit/d194f38)
refactor(tactic/rcases): use haveI in tactic.cache
#### Estimated changes
Modified tactic/rcases.lean



## [2018-07-06 03:44:23-04:00](https://github.com/leanprover-community/mathlib/commit/28e011d)
feat(tactic/cache): split cache related tactics off from `tactic.interactive`
#### Estimated changes
Modified data/option.lean

Modified logic/basic.lean
- \+ *theorem* not_iff

Created tactic/cache.lean

Modified tactic/interactive.lean
- \- *lemma* iff.trans
- \- *theorem* or_iff_not_imp_left
- \- *theorem* or_iff_not_imp_right
- \- *theorem* imp.swap
- \- *theorem* imp_not_comm
- \- *theorem* not_and_of_not_or_not
- \- *theorem* not_and_distrib
- \- *theorem* not_and_distrib'
- \- *theorem* not_or_distrib

Modified tests/examples.lean



## [2018-07-06 03:44:23-04:00](https://github.com/leanprover-community/mathlib/commit/06f4778)
feat(tactic/tauto): handle `or` in goal
#### Estimated changes
Modified tactic/interactive.lean
- \+ *lemma* iff.trans
- \+ *theorem* or_iff_not_imp_left
- \+ *theorem* or_iff_not_imp_right
- \+ *theorem* imp.swap
- \+ *theorem* imp_not_comm
- \+ *theorem* not_and_of_not_or_not
- \+ *theorem* not_and_distrib
- \+ *theorem* not_and_distrib'
- \+ *theorem* not_or_distrib

Modified tests/examples.lean



## [2018-07-06 02:31:12-04:00](https://github.com/leanprover-community/mathlib/commit/b4a8548)
feat(tactic/rcases): add rintro tactic
#### Estimated changes
Modified docs/tactics.md

Modified tactic/interactive.lean

Modified tactic/rcases.lean



## [2018-07-04 13:08:30-04:00](https://github.com/leanprover-community/mathlib/commit/a784602)
feat(tactic/tauto): consider `true` and `false`
#### Estimated changes
Modified tactic/interactive.lean

Modified tests/examples.lean



## [2018-07-02 18:50:42-04:00](https://github.com/leanprover-community/mathlib/commit/a2e847d)
fix(algebra/ordered_group): define (0:with_bot) to unfold correctly
#### Estimated changes
Modified algebra/ordered_group.lean



## [2018-07-02 07:22:16-04:00](https://github.com/leanprover-community/mathlib/commit/ff4eeed)
feat(computability/turing_machine): reduce to 2-symbol TMs
#### Estimated changes
Modified computability/turing_machine.lean
- \+ *theorem* tape.map_fst
- \+ *theorem* tape.map_write
- \+ *theorem* tape.map_move
- \+ *theorem* tape.map_mk
- \+ *theorem* reaches₁_fwd
- \+ *theorem* reaches₀.trans
- \+ *theorem* reaches₀.refl
- \+ *theorem* reaches₀.single
- \+ *theorem* reaches₀.head
- \+ *theorem* reaches₀.tail
- \+ *theorem* reaches₀_eq
- \+ *theorem* reaches₁.to₀
- \+ *theorem* reaches.to₀
- \+ *theorem* reaches₀.tail'
- \+/\- *theorem* step_supports
- \+ *theorem* univ_supports
- \+ *theorem* machine.map_step
- \+ *theorem* map_init
- \+ *theorem* machine.map_respects
- \+/\- *theorem* tr_supports
- \+ *theorem* exists_enc_dec
- \+ *theorem* tr_tape_drop_right
- \+ *theorem* tr_tape_take_right
- \+ *theorem* tr_tape'_move_left
- \+ *theorem* tr_tape'_move_right
- \+ *theorem* step_aux_move
- \+ *theorem* step_aux_read
- \+ *theorem* step_aux_write
- \+ *theorem* tr_respects
- \+ *theorem* supports_stmt_move
- \+ *theorem* supports_stmt_write
- \+ *theorem* supports_stmt_read
- \+/\- *theorem* tr_supports
- \+ *theorem* tr_respects
- \+/\- *theorem* tr_respects_aux₃
- \+/\- *theorem* step_supports
- \+/\- *theorem* tr_supports
- \+/\- *theorem* tr_respects_aux₃
- \+ *def* tape.mk'
- \+/\- *def* tape.write
- \+ *def* tape.map
- \+ *def* pointed_map
- \+ *def* reaches₀
- \+/\- *def* init
- \+/\- *def* supports
- \+ *def* stmt.map
- \+ *def* cfg.map
- \+ *def* machine.map
- \+/\- *def* step_aux
- \+/\- *def* init
- \+/\- *def* tr_cfg
- \+ *def* read_aux
- \+ *def* move
- \+ *def* read
- \+ *def* write
- \+ *def* tr_normal
- \+ *def* tr_tape'
- \+ *def* tr_tape
- \+ *def* tr
- \+/\- *def* tr_cfg
- \+ *def* tr
- \+/\- *def* tr_cfg
- \+/\- *def* step_aux
- \+/\- *def* init
- \+/\- *def* tape.write
- \+/\- *def* init
- \+/\- *def* supports
- \+/\- *def* step_aux
- \+/\- *def* init
- \+/\- *def* tr_cfg
- \+/\- *def* step_aux
- \+/\- *def* init
- \- *def* Λ'_inh

Modified data/bool.lean
- \+ *theorem* to_bool_eq
- \+ *theorem* default_bool

Modified data/fin.lean
- \+ *def* add_nat

Modified data/finset.lean
- \+ *lemma* mem_coe
- \+ *lemma* coe_empty
- \+ *lemma* coe_singleton
- \+ *lemma* coe_insert
- \+ *lemma* coe_union
- \+ *lemma* coe_inter
- \+ *lemma* coe_erase
- \+ *lemma* coe_sdiff
- \+ *lemma* coe_filter
- \+ *lemma* coe_image
- \+ *theorem* coe_inj
- \+ *theorem* coe_subset
- \+ *def* to_set

Modified data/fintype.lean

Modified data/list/basic.lean
- \+ *theorem* ne_nil_of_mem
- \+ *theorem* bind_append
- \+ *theorem* reverse_repeat
- \+ *theorem* take_left
- \+ *theorem* take_left'
- \+ *theorem* drop_one
- \+ *theorem* drop_add
- \+ *theorem* drop_left
- \+ *theorem* drop_left'
- \+ *theorem* take'_length
- \+ *theorem* take'_nil
- \+ *theorem* take'_eq_take
- \+ *theorem* take'_left
- \+ *theorem* take'_left'
- \+ *def* take'

Modified data/set/finite.lean
- \- *lemma* mem_coe
- \- *lemma* coe_eq_coe
- \- *lemma* coe_subseteq_coe
- \- *lemma* coe_empty
- \- *lemma* coe_image
- \- *lemma* coe_filter
- \- *lemma* coe_insert
- \- *lemma* coe_erase
- \- *lemma* coe_sdiff
- \- *lemma* coe_singleton
- \- *lemma* coe_union
- \- *lemma* coe_inter
- \- *def* to_set

Modified data/vector2.lean
- \+/\- *theorem* mk_to_list
- \+/\- *theorem* mk_to_list
- \+ *def* reverse

Modified linear_algebra/basic.lean

Modified logic/embedding.lean
- \+ *theorem* set_value_eq



## [2018-07-02 13:11:51+02:00](https://github.com/leanprover-community/mathlib/commit/b5e07ad)
fix(analysis/topology): prod.ext is now prod.ext_iff
#### Estimated changes
Modified analysis/topology/continuity.lean



## [2018-07-02 11:47:11+02:00](https://github.com/leanprover-community/mathlib/commit/3f66b3a)
feat(analysis/topology/continuity): generalized tube lemma and some corollaries
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* continuous_swap
- \+ *lemma* nhds_contain_boxes.symm
- \+ *lemma* nhds_contain_boxes.comm
- \+ *lemma* nhds_contain_boxes_of_singleton
- \+ *lemma* nhds_contain_boxes_of_compact
- \+ *lemma* generalized_tube_lemma
- \+ *lemma* diagonal_eq_range_diagonal_map
- \+ *lemma* prod_subset_compl_diagonal_iff_disjoint
- \+ *lemma* compact_compact_separated
- \+ *lemma* closed_of_compact
- \+ *def* nhds_contain_boxes

Modified analysis/topology/topological_space.lean
- \+ *lemma* is_open_bUnion
- \+ *lemma* is_open_bInter



## [2018-07-02 11:47:11+02:00](https://github.com/leanprover-community/mathlib/commit/225dd84)
feat(data/set/lattice): add more lemmas pertaining to bInter, bUnion
#### Estimated changes
Modified data/set/lattice.lean
- \+ *theorem* bUnion_subset_bUnion_right
- \+ *theorem* bInter_subset_bInter_right
- \+ *theorem* compl_bUnion
- \+ *theorem* compl_bInter

