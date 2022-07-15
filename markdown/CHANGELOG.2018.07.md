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
- \+ *lemma* euclidean_domain.lt_one
- \+ *theorem* euclidean_domain.mod_lt
- \+ *theorem* euclidean_domain.mul_right_not_lt
- \+/\- *lemma* euclidean_domain.val_dvd_le
- \- *theorem* euclidean_domain.val_le_mul_right
- \- *lemma* euclidean_domain.val_lt_one
- \- *theorem* euclidean_domain.val_mod_lt

Modified data/polynomial.lean
- \+ *lemma* polynomial.degree_add_div
- \+ *lemma* polynomial.degree_le_mul_left
- \+ *lemma* polynomial.div_def
- \+ *lemma* polynomial.div_eq_zero_iff
- \+ *lemma* polynomial.mod_def
- \+ *lemma* polynomial.mod_eq_self_iff



## [2018-07-30 11:48:54+02:00](https://github.com/leanprover-community/mathlib/commit/08e0e1d)
feat(category/traversable): instances for various collections ([#217](https://github.com/leanprover-community/mathlib/pull/217))
#### Estimated changes
Added category/traversable/equiv.lean


Modified data/array/lemmas.lean
- \+ *theorem* array.to_list_of_heq
- \+ *def* equiv.vector_equiv_array
- \+ *def* equiv.vector_equiv_fin

Added data/buffer/basic.lean
- \+ *lemma* buffer.append_list_mk_buffer
- \+ *lemma* buffer.ext
- \+ *def* buffer.list_equiv_buffer
- \+ *lemma* buffer.to_list_append_list

Added data/dlist/instances.lean
- \+ *def* dlist.list_equiv_dlist

Modified data/equiv/basic.lean


Added data/lazy_list2.lean
- \+ *def* lazy_list.list_equiv_lazy_list
- \+ *def* lazy_list.thunk.mk

Modified data/multiset.lean


Modified data/vector2.lean
- \- *def* equiv.vector_equiv_array
- \- *def* equiv.vector_equiv_fin

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


Added tactic/pi_instances.lean




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
- \+ *lemma* equiv.inverse_trans_apply
- \+ *lemma* equiv.perm.apply_inv_self
- \+ *lemma* equiv.perm.inv_apply_self
- \+ *lemma* equiv.perm.inv_def
- \+ *theorem* equiv.perm.mul_apply
- \+ *lemma* equiv.perm.mul_def
- \- *theorem* equiv.perm.mul_val
- \+ *theorem* equiv.perm.one_apply
- \+ *lemma* equiv.perm.one_def
- \- *theorem* equiv.perm.one_val

Modified data/fintype.lean




## [2018-07-30 10:41:45+02:00](https://github.com/leanprover-community/mathlib/commit/e67f2ad)
chore(analysis/topology/uniform_space): remove redundant prod_uniformity (redundant to uniformity_prod)
#### Estimated changes
Modified analysis/metric_space.lean


Modified analysis/topology/uniform_space.lean
- \- *theorem* prod_uniformity
- \+ *theorem* uniformity_prod
- \- *lemma* uniformity_prod



## [2018-07-30 10:25:10+02:00](https://github.com/leanprover-community/mathlib/commit/8d4f582)
chore(data/list): add prod.erase; cleanup
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.eq_or_ne_mem_of_mem
- \+ *theorem* list.prod_erase
- \+/\- *theorem* list.take'_eq_take



## [2018-07-27 23:51:05-04:00](https://github.com/leanprover-community/mathlib/commit/460df5e)
feat(tactic/norm_num): add support for primality proving
#### Estimated changes
Modified data/nat/gcd.lean
- \+ *theorem* nat.exists_coprime'
- \+/\- *theorem* nat.exists_eq_prod_and_dvd_and_dvd

Modified data/nat/prime.lean
- \+/\- *theorem* nat.min_fac_eq
- \+/\- *theorem* nat.min_fac_le_of_dvd
- \+ *theorem* nat.not_prime_mul

Modified tactic/norm_num.lean
- \+ *lemma* norm_num.is_prime_helper
- \+ *lemma* norm_num.min_fac_bit0
- \+ *theorem* norm_num.min_fac_helper.n_pos
- \+ *def* norm_num.min_fac_helper
- \+ *lemma* norm_num.min_fac_helper_0
- \+ *lemma* norm_num.min_fac_helper_1
- \+ *lemma* norm_num.min_fac_helper_2
- \+ *lemma* norm_num.min_fac_helper_3
- \+ *lemma* norm_num.min_fac_helper_4
- \+ *lemma* norm_num.min_fac_helper_5
- \+ *lemma* norm_num.min_fac_ne_bit0
- \+ *lemma* norm_num.not_prime_helper

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
Added category/traversable/basic.lean
- \+ *lemma* applicative_transformation.preserves_map
- \+ *lemma* applicative_transformation.preserves_pure
- \+ *lemma* applicative_transformation.preserves_seq
- \+ *def* sequence

Added category/traversable/default.lean


Added category/traversable/instances.lean
- \+ *lemma* id.comp_traverse
- \+ *lemma* id.id_traverse
- \+ *lemma* id.map_traverse
- \+ *lemma* id.naturality
- \+ *lemma* id.traverse_map
- \+ *lemma* list.comp_traverse
- \+ *lemma* list.id_traverse
- \+ *lemma* list.map_traverse
- \+ *lemma* list.naturality
- \+ *lemma* list.traverse_map
- \+ *lemma* option.comp_traverse
- \+ *lemma* option.id_traverse
- \+ *lemma* option.map_traverse
- \+ *lemma* option.naturality
- \+ *lemma* option.traverse_map

Added category/traversable/lemmas.lean
- \+ *lemma* traversable.comp_sequence
- \+ *lemma* traversable.id_sequence
- \+ *lemma* traversable.naturality'
- \+ *def* traversable.pure_transformation
- \+ *lemma* traversable.purity
- \+ *lemma* traversable.traverse_eq_map_ident



## [2018-07-24 05:15:31-04:00](https://github.com/leanprover-community/mathlib/commit/8270475)
doc(wip): finite map ([#215](https://github.com/leanprover-community/mathlib/pull/215)) [ci-skip]
#### Estimated changes
Modified docs/wip.md




## [2018-07-23 20:06:20-04:00](https://github.com/leanprover-community/mathlib/commit/6abb0d4)
feat(algebra/pi_instances): more pi instances
#### Estimated changes
Modified algebra/pi_instances.lean


Modified order/basic.lean


Modified order/bounded_lattice.lean


Modified order/complete_lattice.lean




## [2018-07-22 15:03:49-04:00](https://github.com/leanprover-community/mathlib/commit/e74ff76)
refactor(data/nat/gcd): simplify proof of pow_dvd_pow_iff
#### Estimated changes
Modified algebra/ring.lean


Modified data/nat/basic.lean
- \+ *theorem* nat.pow_dvd_pow_of_dvd

Modified data/nat/gcd.lean
- \- *lemma* nat.dvd_of_pow_dvd_pow
- \+ *theorem* nat.pow_dvd_pow_iff



## [2018-07-22 14:37:11-04:00](https://github.com/leanprover-community/mathlib/commit/ffb7229)
feat(data/nat/gcd): dvd_of_pow_dvd_pow
#### Estimated changes
Modified data/nat/basic.lean
- \+ *theorem* nat.mul_pow

Modified data/nat/gcd.lean
- \+ *lemma* nat.dvd_of_pow_dvd_pow



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
- \+/\- *theorem* option.bind_eq_some
- \+/\- *theorem* option.map_eq_some
- \+/\- *theorem* option.map_none
- \+/\- *theorem* option.map_some
- \+/\- *theorem* option.none_bind
- \+/\- *theorem* option.seq_some
- \+/\- *theorem* option.some_bind

Modified data/seq/seq.lean


Modified data/seq/wseq.lean




## [2018-07-21 02:09:53-04:00](https://github.com/leanprover-community/mathlib/commit/fb952fe)
refactor(analysis/ennreal): split and move to data.real
#### Estimated changes
Modified analysis/ennreal.lean
- \- *lemma* ennreal.add_infty
- \- *lemma* ennreal.add_left_inj
- \- *lemma* ennreal.add_right_inj
- \- *lemma* ennreal.add_sub_cancel_of_le
- \- *lemma* ennreal.add_sub_self'
- \- *lemma* ennreal.add_sub_self
- \- *lemma* ennreal.forall_ennreal
- \- *lemma* ennreal.infty_add
- \- *lemma* ennreal.infty_le_iff
- \- *lemma* ennreal.infty_mem_upper_bounds
- \- *lemma* ennreal.infty_mul
- \- *lemma* ennreal.infty_mul_of_real
- \- *lemma* ennreal.infty_ne_of_real
- \- *lemma* ennreal.infty_ne_zero
- \- *lemma* ennreal.infty_sub_of_real
- \- *lemma* ennreal.inv_infty
- \- *lemma* ennreal.inv_inv
- \- *lemma* ennreal.inv_of_real
- \- *lemma* ennreal.inv_zero
- \- *lemma* ennreal.is_lub_of_real
- \- *lemma* ennreal.le_add_left
- \- *lemma* ennreal.le_add_right
- \- *theorem* ennreal.le_def
- \- *lemma* ennreal.le_infty
- \- *lemma* ennreal.le_of_forall_epsilon_le
- \- *lemma* ennreal.le_of_real_iff
- \- *lemma* ennreal.le_zero_iff_eq
- \- *lemma* ennreal.lt_add_right
- \- *lemma* ennreal.lt_iff_exists_of_real
- \- *lemma* ennreal.mul_infty
- \- *lemma* ennreal.mul_le_mul
- \- *lemma* ennreal.not_infty_lt
- \- *lemma* ennreal.not_lt_zero
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
- \- *lemma* ennreal.one_eq_of_real_iff
- \- *lemma* ennreal.one_le_of_real_iff
- \- *lemma* ennreal.sub_add_cancel_of_le
- \- *lemma* ennreal.sub_add_self_eq_max
- \- *lemma* ennreal.sub_eq_zero_of_le
- \- *lemma* ennreal.sub_infty
- \- *lemma* ennreal.sub_le_self
- \- *lemma* ennreal.sub_le_sub
- \- *lemma* ennreal.sub_sub_cancel
- \- *lemma* ennreal.sub_zero
- \- *lemma* ennreal.sum_of_real
- \- *lemma* ennreal.zero_eq_of_real_iff
- \- *lemma* ennreal.zero_le_of_ennreal
- \- *lemma* ennreal.zero_lt_of_real_iff
- \- *lemma* ennreal.zero_ne_infty
- \- *lemma* ennreal.zero_sub

Modified data/real/basic.lean
- \+ *lemma* real.Sup_is_lub

Added data/real/ennreal.lean
- \+ *lemma* ennreal.add_infty
- \+ *lemma* ennreal.add_left_inj
- \+ *lemma* ennreal.add_right_inj
- \+ *lemma* ennreal.add_sub_cancel_of_le
- \+ *lemma* ennreal.add_sub_self'
- \+ *lemma* ennreal.add_sub_self
- \+ *lemma* ennreal.forall_ennreal
- \+ *lemma* ennreal.infty_add
- \+ *lemma* ennreal.infty_le_iff
- \+ *lemma* ennreal.infty_mem_upper_bounds
- \+ *lemma* ennreal.infty_mul
- \+ *lemma* ennreal.infty_mul_of_real
- \+ *lemma* ennreal.infty_ne_of_real
- \+ *lemma* ennreal.infty_ne_zero
- \+ *lemma* ennreal.infty_sub_of_real
- \+ *lemma* ennreal.inv_infty
- \+ *lemma* ennreal.inv_inv
- \+ *lemma* ennreal.inv_of_real
- \+ *lemma* ennreal.inv_zero
- \+ *lemma* ennreal.is_lub_of_real
- \+ *lemma* ennreal.le_add_left
- \+ *lemma* ennreal.le_add_right
- \+ *theorem* ennreal.le_def
- \+ *lemma* ennreal.le_infty
- \+ *lemma* ennreal.le_of_forall_epsilon_le
- \+ *lemma* ennreal.le_of_real_iff
- \+ *lemma* ennreal.le_zero_iff_eq
- \+ *lemma* ennreal.lt_add_right
- \+ *lemma* ennreal.lt_iff_exists_of_real
- \+ *lemma* ennreal.mul_infty
- \+ *lemma* ennreal.mul_le_mul
- \+ *lemma* ennreal.not_infty_lt
- \+ *lemma* ennreal.not_lt_zero
- \+ *def* ennreal.of_ennreal
- \+ *lemma* ennreal.of_ennreal_of_real
- \+ *lemma* ennreal.of_nonneg_real_eq_of_real
- \+ *def* ennreal.of_real
- \+ *lemma* ennreal.of_real_add
- \+ *lemma* ennreal.of_real_add_le
- \+ *lemma* ennreal.of_real_eq_of_real_of
- \+ *lemma* ennreal.of_real_eq_one_iff
- \+ *lemma* ennreal.of_real_eq_zero_iff
- \+ *lemma* ennreal.of_real_le_of_real
- \+ *lemma* ennreal.of_real_le_of_real_iff
- \+ *lemma* ennreal.of_real_lt_infty
- \+ *lemma* ennreal.of_real_lt_of_real_iff
- \+ *lemma* ennreal.of_real_lt_of_real_iff_cases
- \+ *lemma* ennreal.of_real_mem_upper_bounds
- \+ *lemma* ennreal.of_real_mul_infty
- \+ *lemma* ennreal.of_real_mul_of_real
- \+ *lemma* ennreal.of_real_ne_infty
- \+ *lemma* ennreal.of_real_ne_of_real_of
- \+ *lemma* ennreal.of_real_of_ennreal
- \+ *lemma* ennreal.of_real_of_nonpos
- \+ *lemma* ennreal.of_real_of_not_nonneg
- \+ *lemma* ennreal.of_real_one
- \+ *lemma* ennreal.of_real_sub_of_real
- \+ *lemma* ennreal.of_real_zero
- \+ *lemma* ennreal.one_eq_of_real_iff
- \+ *lemma* ennreal.one_le_of_real_iff
- \+ *lemma* ennreal.sub_add_cancel_of_le
- \+ *lemma* ennreal.sub_add_self_eq_max
- \+ *lemma* ennreal.sub_eq_zero_of_le
- \+ *lemma* ennreal.sub_infty
- \+ *lemma* ennreal.sub_le_self
- \+ *lemma* ennreal.sub_le_sub
- \+ *lemma* ennreal.sub_sub_cancel
- \+ *lemma* ennreal.sub_zero
- \+ *lemma* ennreal.sum_of_real
- \+ *lemma* ennreal.zero_eq_of_real_iff
- \+ *lemma* ennreal.zero_le_of_ennreal
- \+ *lemma* ennreal.zero_lt_of_real_iff
- \+ *lemma* ennreal.zero_ne_infty
- \+ *lemma* ennreal.zero_sub

Modified data/set/lattice.lean
- \+ *def* set.kern_image

Modified order/bounds.lean


Modified order/galois_connection.lean
- \- *def* set.kern_image



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
- \+ *lemma* one_half_lt_one
- \+ *lemma* one_half_pos

Modified analysis/ennreal.lean
- \+ *lemma* ennreal.add_left_inj
- \+ *lemma* ennreal.add_right_inj
- \+ *lemma* ennreal.add_sub_self'
- \+ *lemma* ennreal.add_supr
- \+ *theorem* ennreal.exists_pos_sum_of_encodable
- \+ *lemma* ennreal.of_real_add_le
- \+ *lemma* ennreal.sub_infi
- \+ *lemma* ennreal.sub_le_self
- \+ *lemma* ennreal.sub_sub_cancel
- \+/\- *lemma* ennreal.sub_supr
- \+ *lemma* ennreal.supr_add_supr

Modified analysis/limits.lean
- \+ *lemma* is_sum_geometric_two
- \+ *def* pos_sum_of_encodable

Modified analysis/measure_theory/borel_space.lean
- \+ *def* measure_theory.borel
- \- *lemma* measure_theory.borel_eq_generate_from_Iio_rat
- \- *lemma* measure_theory.borel_eq_generate_from_Ioo_rat
- \+ *lemma* measure_theory.borel_prod_le
- \- *lemma* measure_theory.is_topological_basis_Ioo_rat
- \+ *lemma* real.borel_eq_generate_from_Iio_rat
- \+ *lemma* real.borel_eq_generate_from_Ioo_rat

Modified analysis/measure_theory/lebesgue_measure.lean
- \+ *lemma* measure_theory.is_lebesgue_measurable_Iio
- \- *lemma* measure_theory.le_lebesgue_length
- \+/\- *def* measure_theory.lebesgue
- \+ *lemma* measure_theory.lebesgue_Icc
- \+/\- *def* measure_theory.lebesgue_length
- \+ *lemma* measure_theory.lebesgue_length_Icc
- \- *lemma* measure_theory.lebesgue_length_Ico'
- \+/\- *lemma* measure_theory.lebesgue_length_Ico
- \+ *lemma* measure_theory.lebesgue_length_Ioo
- \+ *lemma* measure_theory.lebesgue_length_eq_infi_Icc
- \+ *lemma* measure_theory.lebesgue_length_eq_infi_Ioo
- \+ *lemma* measure_theory.lebesgue_length_mono
- \+ *lemma* measure_theory.lebesgue_outer_Icc
- \+/\- *lemma* measure_theory.lebesgue_outer_Ico
- \+ *lemma* measure_theory.lebesgue_outer_Ioo
- \- *lemma* measure_theory.lebesgue_outer_is_measurable_Iio
- \+ *lemma* measure_theory.lebesgue_outer_le_length
- \+ *lemma* measure_theory.lebesgue_outer_singleton
- \+ *theorem* measure_theory.lebesgue_outer_trim
- \+/\- *lemma* measure_theory.lebesgue_singleton
- \+ *theorem* measure_theory.lebesgue_to_outer_measure
- \+ *theorem* measure_theory.lebesgue_val
- \- *lemma* measure_theory.tendsto_of_nat_at_top_at_top

Modified analysis/measure_theory/measurable_space.lean
- \+ *lemma* encodable.Union_decode2
- \+ *lemma* encodable.Union_decode2_cases
- \+ *lemma* is_measurable.Inter
- \+ *lemma* is_measurable.Union
- \+ *lemma* is_measurable.bInter
- \+ *lemma* is_measurable.bUnion
- \+ *lemma* is_measurable.compl
- \+ *lemma* is_measurable.compl_iff
- \+ *lemma* is_measurable.diff
- \+ *lemma* is_measurable.disjointed
- \+ *lemma* is_measurable.empty
- \+ *lemma* is_measurable.inter
- \+ *lemma* is_measurable.sInter
- \+ *lemma* is_measurable.sUnion
- \+ *lemma* is_measurable.sub
- \+ *lemma* is_measurable.union
- \+/\- *def* is_measurable
- \- *lemma* is_measurable_Inter
- \- *lemma* is_measurable_Union
- \- *lemma* is_measurable_Union_nat
- \- *lemma* is_measurable_bInter
- \- *lemma* is_measurable_bUnion
- \- *lemma* is_measurable_compl
- \- *lemma* is_measurable_disjointed
- \- *lemma* is_measurable_empty
- \- *lemma* is_measurable_inter
- \- *lemma* is_measurable_sInter
- \- *lemma* is_measurable_sUnion
- \- *lemma* is_measurable_sdiff
- \- *lemma* is_measurable_sub
- \- *lemma* is_measurable_union
- \+ *lemma* measurable.comp
- \+ *lemma* measurable.if
- \+ *lemma* measurable.preimage
- \+ *lemma* measurable.prod
- \- *lemma* measurable_comp
- \- *lemma* measurable_if
- \- *lemma* measurable_prod
- \+ *theorem* measurable_space.Union_decode2_disjoint_on
- \- *lemma* measurable_space.dynkin_system.dynkin_system_eq
- \+ *lemma* measurable_space.dynkin_system.ext
- \+/\- *lemma* measurable_space.dynkin_system.generate_le
- \+ *theorem* measurable_space.dynkin_system.has_Union
- \+ *lemma* measurable_space.dynkin_system.has_compl_iff
- \+ *lemma* measurable_space.dynkin_system.has_diff
- \- *lemma* measurable_space.dynkin_system.has_sdiff
- \+ *theorem* measurable_space.dynkin_system.has_union
- \- *lemma* measurable_space.dynkin_system.has_union
- \+/\- *def* measurable_space.dynkin_system.restrict_on
- \+ *lemma* measurable_space.ext
- \+ *theorem* measurable_space.is_measurable_Inf
- \+ *theorem* measurable_space.is_measurable_inf
- \+ *theorem* measurable_space.is_measurable_infi
- \- *lemma* measurable_space_eq

Modified analysis/measure_theory/measure_space.lean
- \+ *def* completion
- \+ *theorem* is_measurable.diff_null
- \+ *theorem* is_measurable.is_null_measurable
- \+ *theorem* is_null_measurable.Union_nat
- \+ *theorem* is_null_measurable.compl
- \+ *theorem* is_null_measurable.diff_null
- \+ *theorem* is_null_measurable.union_null
- \+ *def* is_null_measurable
- \+ *theorem* is_null_measurable_iff
- \+ *theorem* is_null_measurable_measure_eq
- \+ *theorem* is_null_measurable_of_complete
- \+/\- *lemma* measure_theory.le_to_outer_measure_caratheodory
- \+ *def* measure_theory.measure'
- \+ *lemma* measure_theory.measure'_Union
- \+ *lemma* measure_theory.measure'_Union_le_tsum_nat'
- \+ *lemma* measure_theory.measure'_Union_le_tsum_nat
- \+ *lemma* measure_theory.measure'_Union_nat
- \+ *lemma* measure_theory.measure'_empty
- \+ *lemma* measure_theory.measure'_eq
- \+ *lemma* measure_theory.measure'_mono
- \+ *lemma* measure_theory.measure'_union
- \+ *theorem* measure_theory.measure.add_apply
- \+ *theorem* measure_theory.measure.add_to_outer_measure
- \+ *def* measure_theory.measure.count
- \+ *def* measure_theory.measure.dirac
- \+ *lemma* measure_theory.measure.dirac_apply
- \+ *lemma* measure_theory.measure.ext
- \+ *def* measure_theory.measure.is_complete
- \+ *theorem* measure_theory.measure.le_iff'
- \+ *theorem* measure_theory.measure.le_iff
- \+ *def* measure_theory.measure.map
- \+ *theorem* measure_theory.measure.map_apply
- \+ *lemma* measure_theory.measure.map_id
- \+ *lemma* measure_theory.measure.map_map
- \+ *def* measure_theory.measure.of_measurable
- \+ *def* measure_theory.measure.sum
- \+ *theorem* measure_theory.measure.to_outer_measure_le
- \+ *theorem* measure_theory.measure.zero_apply
- \+ *theorem* measure_theory.measure.zero_to_outer_measure
- \+ *lemma* measure_theory.measure_Union
- \+ *theorem* measure_theory.measure_Union_le
- \- *lemma* measure_theory.measure_Union_le_tsum_nat
- \- *lemma* measure_theory.measure_Union_nat
- \+ *lemma* measure_theory.measure_Union_null
- \+/\- *lemma* measure_theory.measure_bUnion
- \+ *lemma* measure_theory.measure_diff
- \+/\- *lemma* measure_theory.measure_empty
- \+ *lemma* measure_theory.measure_eq_infi
- \+ *lemma* measure_theory.measure_eq_measure'
- \+ *lemma* measure_theory.measure_eq_outer_measure'
- \+ *lemma* measure_theory.measure_eq_trim
- \+/\- *lemma* measure_theory.measure_mono
- \+ *lemma* measure_theory.measure_mono_null
- \+/\- *lemma* measure_theory.measure_sUnion
- \- *lemma* measure_theory.measure_sdiff
- \- *def* measure_theory.measure_space.count
- \- *def* measure_theory.measure_space.dirac
- \- *def* measure_theory.measure_space.map
- \- *lemma* measure_theory.measure_space.map_comp
- \- *lemma* measure_theory.measure_space.map_id
- \- *lemma* measure_theory.measure_space.map_measure
- \- *def* measure_theory.measure_space.sum
- \- *lemma* measure_theory.measure_space_eq
- \- *lemma* measure_theory.measure_space_eq_of
- \+ *theorem* measure_theory.measure_union_le
- \+ *lemma* measure_theory.measure_union_null
- \+ *def* measure_theory.outer_measure'
- \+ *lemma* measure_theory.outer_measure'_eq
- \+ *lemma* measure_theory.outer_measure'_eq_measure'
- \+ *theorem* measure_theory.outer_measure.le_trim_iff
- \+/\- *def* measure_theory.outer_measure.to_measure
- \+ *def* measure_theory.outer_measure.trim
- \+ *theorem* measure_theory.outer_measure.trim_add
- \+ *theorem* measure_theory.outer_measure.trim_congr
- \+ *theorem* measure_theory.outer_measure.trim_eq
- \+ *theorem* measure_theory.outer_measure.trim_eq_infi'
- \+ *theorem* measure_theory.outer_measure.trim_eq_infi
- \+ *theorem* measure_theory.outer_measure.trim_ge
- \+ *theorem* measure_theory.outer_measure.trim_le_trim
- \+ *theorem* measure_theory.outer_measure.trim_sum_ge
- \+ *theorem* measure_theory.outer_measure.trim_trim
- \+ *theorem* measure_theory.outer_measure.trim_zero
- \+ *lemma* measure_theory.to_measure_apply
- \+ *lemma* measure_theory.to_measure_to_outer_measure
- \+ *lemma* measure_theory.to_outer_measure_apply
- \+ *lemma* measure_theory.to_outer_measure_eq_outer_measure'
- \+/\- *lemma* measure_theory.to_outer_measure_to_measure
- \+ *theorem* null_is_null_measurable
- \+ *def* null_measurable

Modified analysis/measure_theory/outer_measure.lean
- \+ *theorem* measure_theory.outer_measure.Sup_apply
- \+ *theorem* measure_theory.outer_measure.Union_aux
- \+ *lemma* measure_theory.outer_measure.Union_null
- \+ *theorem* measure_theory.outer_measure.add_apply
- \+ *theorem* measure_theory.outer_measure.add_smul
- \- *lemma* measure_theory.outer_measure.caratheodory_is_measurable_eq
- \+ *def* measure_theory.outer_measure.dirac
- \+ *theorem* measure_theory.outer_measure.dirac_apply
- \+ *theorem* measure_theory.outer_measure.dirac_caratheodory
- \+ *theorem* measure_theory.outer_measure.empty'
- \+ *lemma* measure_theory.outer_measure.ext
- \+ *lemma* measure_theory.outer_measure.is_caratheodory
- \+ *lemma* measure_theory.outer_measure.is_caratheodory_le
- \+ *theorem* measure_theory.outer_measure.le_add_caratheodory
- \+ *theorem* measure_theory.outer_measure.le_of_function
- \+ *theorem* measure_theory.outer_measure.le_smul_caratheodory
- \+ *theorem* measure_theory.outer_measure.le_sum_caratheodory
- \+ *def* measure_theory.outer_measure.map
- \+ *theorem* measure_theory.outer_measure.map_apply
- \+ *theorem* measure_theory.outer_measure.map_id
- \+ *theorem* measure_theory.outer_measure.map_map
- \+ *theorem* measure_theory.outer_measure.mono'
- \+ *theorem* measure_theory.outer_measure.mul_smul
- \+ *theorem* measure_theory.outer_measure.one_smul
- \- *lemma* measure_theory.outer_measure.outer_measure_eq
- \+ *def* measure_theory.outer_measure.smul
- \+ *theorem* measure_theory.outer_measure.smul_add
- \+ *theorem* measure_theory.outer_measure.smul_apply
- \+ *theorem* measure_theory.outer_measure.smul_dirac_apply
- \+ *theorem* measure_theory.outer_measure.smul_zero
- \- *lemma* measure_theory.outer_measure.subadditive
- \+ *def* measure_theory.outer_measure.sum
- \+ *theorem* measure_theory.outer_measure.sum_apply
- \+ *theorem* measure_theory.outer_measure.sup_apply
- \+ *theorem* measure_theory.outer_measure.supr_apply
- \+ *theorem* measure_theory.outer_measure.top_apply
- \+ *lemma* measure_theory.outer_measure.union_null
- \+ *theorem* measure_theory.outer_measure.zero_apply
- \+ *theorem* measure_theory.outer_measure.zero_caratheodory
- \+ *theorem* measure_theory.outer_measure.zero_smul

Modified analysis/real.lean
- \+ *lemma* compact_Icc
- \- *lemma* compact_ivl
- \+/\- *lemma* rat.totally_bounded_Icc
- \+ *lemma* real.is_topological_basis_Ioo_rat
- \+/\- *lemma* real.totally_bounded_Icc
- \+ *lemma* tendsto_of_nat_at_top_at_top

Modified analysis/topology/infinite_sum.lean
- \+/\- *lemma* has_sum_mul_left
- \+/\- *lemma* has_sum_mul_right
- \+/\- *lemma* is_sum_mul_left
- \+/\- *lemma* is_sum_mul_right
- \+ *lemma* tsum_equiv
- \+ *lemma* tsum_fintype
- \+/\- *lemma* tsum_mul_left
- \+/\- *lemma* tsum_mul_right

Modified analysis/topology/topological_space.lean
- \+ *lemma* topological_space.is_open_sUnion_countable

Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* closure_le_eq
- \+ *lemma* is_closed_Icc

Modified data/set/basic.lean
- \+/\- *theorem* set.mem_diff
- \- *theorem* set.mem_diff_eq
- \- *theorem* set.mem_diff_iff
- \+ *theorem* set.mem_diff_of_mem
- \+ *theorem* set.union_diff_distrib

Modified data/set/countable.lean


Modified data/set/disjointed.lean
- \+ *theorem* pairwise_disjoint_on_bool
- \+ *theorem* pairwise_on_bool
- \+ *lemma* set.Inter_lt_succ
- \+ *lemma* set.Union_disjointed
- \+ *lemma* set.Union_disjointed_of_mono
- \+ *lemma* set.Union_lt_succ
- \- *lemma* set.disjointed_Union

Modified data/set/intervals.lean
- \+ *def* set.Icc
- \+ *lemma* set.Icc_diff_Ico_eq_singleton
- \+ *lemma* set.Icc_eq_empty
- \+ *lemma* set.Icc_eq_empty_iff
- \+ *lemma* set.Icc_self
- \+ *lemma* set.Icc_subset_Icc
- \+ *lemma* set.Icc_subset_Icc_left
- \+ *lemma* set.Icc_subset_Icc_right
- \+ *lemma* set.Icc_subset_Ico_right
- \+ *lemma* set.Ico_diff_Iio
- \+ *lemma* set.Ico_diff_Ioo_eq_singleton
- \+/\- *lemma* set.Ico_eq_Ico_iff
- \+/\- *lemma* set.Ico_eq_empty
- \+/\- *lemma* set.Ico_eq_empty_iff
- \+ *lemma* set.Ico_inter_Iio
- \- *lemma* set.Ico_inter_Iio_eq
- \- *lemma* set.Ico_sdiff_Iio_eq
- \- *lemma* set.Ico_sdiff_Ioo_eq_singleton
- \+/\- *lemma* set.Ico_self
- \+ *lemma* set.Ico_subset_Icc_self
- \+ *lemma* set.Ico_subset_Ico
- \+/\- *lemma* set.Ico_subset_Ico_iff
- \+/\- *lemma* set.Ico_subset_Ico_left
- \+/\- *lemma* set.Ico_subset_Ico_right
- \+/\- *lemma* set.Ico_subset_Iio_self
- \+ *lemma* set.Iio_ne_empty
- \+ *lemma* set.Ioo_eq_empty
- \+ *lemma* set.Ioo_eq_empty_iff
- \- *lemma* set.Ioo_eq_empty_of_ge
- \+/\- *lemma* set.Ioo_self
- \+ *lemma* set.Ioo_subset_Icc_self
- \+/\- *lemma* set.Ioo_subset_Ico_self
- \+ *lemma* set.Ioo_subset_Ioo
- \+ *lemma* set.Ioo_subset_Ioo_iff
- \+ *lemma* set.Ioo_subset_Ioo_left
- \+ *lemma* set.Ioo_subset_Ioo_right
- \+ *lemma* set.mem_Icc
- \+ *lemma* set.mem_Ico
- \+ *lemma* set.mem_Iio
- \+ *lemma* set.mem_Ioo

Modified order/complete_lattice.lean
- \+/\- *theorem* lattice.infi_and
- \+/\- *theorem* lattice.infi_prod
- \+/\- *theorem* lattice.infi_sigma
- \+/\- *theorem* lattice.infi_subtype
- \+/\- *theorem* lattice.supr_and
- \+/\- *theorem* lattice.supr_prod
- \+/\- *theorem* lattice.supr_sigma
- \+/\- *theorem* lattice.supr_subtype



## [2018-07-19 10:10:59-04:00](https://github.com/leanprover-community/mathlib/commit/bd90a93)
fix(group_theory/group_action): move is_group_action out of namespace
#### Estimated changes
Modified group_theory/group_action.lean




## [2018-07-19 09:29:24-04:00](https://github.com/leanprover-community/mathlib/commit/2b9780a)
feat(data/finset): disjoint_val ([#206](https://github.com/leanprover-community/mathlib/pull/206))
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* finset.disjoint_val



## [2018-07-19 09:29:24-04:00](https://github.com/leanprover-community/mathlib/commit/1e0c38b)
feat(data/multiset): sup and inf for multisets
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* finset.inf_val
- \+ *lemma* finset.sup_val

Modified data/multiset.lean
- \+ *def* multiset.inf
- \+ *lemma* multiset.inf_add
- \+ *lemma* multiset.inf_cons
- \+ *lemma* multiset.inf_erase_dup
- \+ *lemma* multiset.inf_le
- \+ *lemma* multiset.inf_mono
- \+ *lemma* multiset.inf_ndinsert
- \+ *lemma* multiset.inf_ndunion
- \+ *lemma* multiset.inf_singleton
- \+ *lemma* multiset.inf_union
- \+ *lemma* multiset.inf_zero
- \+ *lemma* multiset.le_inf
- \+ *lemma* multiset.le_sup
- \+ *theorem* multiset.prod_singleton
- \+ *def* multiset.sup
- \+ *lemma* multiset.sup_add
- \+ *lemma* multiset.sup_cons
- \+ *lemma* multiset.sup_erase_dup
- \+ *lemma* multiset.sup_le
- \+ *lemma* multiset.sup_mono
- \+ *lemma* multiset.sup_ndinsert
- \+ *lemma* multiset.sup_ndunion
- \+ *lemma* multiset.sup_singleton
- \+ *lemma* multiset.sup_union
- \+ *lemma* multiset.sup_zero



## [2018-07-19 06:54:38-04:00](https://github.com/leanprover-community/mathlib/commit/50f18e6)
feat(group_theory/group_action): group actions and orbit stabilizer ([#204](https://github.com/leanprover-community/mathlib/pull/204))
#### Estimated changes
Added group_theory/group_action.lean
- \+ *lemma* is_group_action.bijective
- \+ *lemma* is_group_action.orbit_eq_iff
- \+ *def* is_group_action.to_perm
- \+ *def* is_monoid_action.fixed_points
- \+ *lemma* is_monoid_action.mem_fixed_points'
- \+ *lemma* is_monoid_action.mem_fixed_points
- \+ *lemma* is_monoid_action.mem_orbit
- \+ *lemma* is_monoid_action.mem_orbit_iff
- \+ *lemma* is_monoid_action.mem_orbit_self
- \+ *lemma* is_monoid_action.mem_stabilizer_iff
- \+ *def* is_monoid_action.orbit
- \+ *def* is_monoid_action.stabilizer



## [2018-07-19 03:56:30-04:00](https://github.com/leanprover-community/mathlib/commit/9f79309)
fix(data/multiset): fix build, cleanup mem_pi
#### Estimated changes
Modified data/multiset.lean
- \+/\- *theorem* multiset.mem_singleton
- \+/\- *lemma* multiset.pi_zero
- \+ *theorem* multiset.singleton_eq_singleton



## [2018-07-19 03:18:09-04:00](https://github.com/leanprover-community/mathlib/commit/37f3e32)
fix(algebra/big_operators): fix build
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* finset.card_pi

Modified data/finset.lean
- \+ *theorem* finset.card_singleton
- \+/\- *theorem* finset.insert_empty_eq_singleton
- \+/\- *lemma* finset.pi_empty
- \+/\- *theorem* finset.singleton_eq_singleton

Modified data/multiset.lean
- \+/\- *theorem* multiset.card_singleton
- \+/\- *lemma* multiset.pi_zero



## [2018-07-19 02:36:49-04:00](https://github.com/leanprover-community/mathlib/commit/aedbc12)
feat(data/fintype): card lemmas ([#168](https://github.com/leanprover-community/mathlib/pull/168))
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.card_pi
- \+ *lemma* finset.prod_const
- \+ *lemma* finset.sum_const

Modified data/fintype.lean
- \+ *lemma* fintype.card_eq_one_iff
- \+ *lemma* fintype.card_eq_zero_iff
- \+ *lemma* fintype.card_fun
- \+ *lemma* fintype.card_le_of_injective
- \+ *lemma* fintype.card_le_one_iff
- \+ *lemma* fintype.card_pi
- \+ *lemma* fintype.card_pos_iff



## [2018-07-19 00:25:14-04:00](https://github.com/leanprover-community/mathlib/commit/c2f54ad)
fix(tactic/refine_struct): fix support for source structures
#### Estimated changes
Modified tactic/interactive.lean


Modified tests/examples.lean




## [2018-07-18 14:10:50+02:00](https://github.com/leanprover-community/mathlib/commit/9a30235)
chore(data/polynomial): move auxiliary definitions/theorems to appropriate places
#### Estimated changes
Modified algebra/ordered_group.lean
- \+ *lemma* with_bot.add_bot
- \+ *lemma* with_bot.bot_add
- \+ *lemma* with_bot.bot_lt_some
- \+ *lemma* with_bot.coe_add
- \+ *lemma* with_bot.coe_lt_coe

Modified algebra/ring.lean


Modified data/finsupp.lean
- \+ *lemma* finsupp.mul_sum
- \+ *lemma* finsupp.sum_mul

Modified data/polynomial.lean
- \- *lemma* finsupp.mul_sum
- \- *lemma* finsupp.sum_mul
- \- *lemma* with_bot.add_bot
- \- *lemma* with_bot.bot_add
- \- *lemma* with_bot.bot_lt_some
- \- *lemma* with_bot.coe_add
- \- *lemma* with_bot.coe_lt_coe



## [2018-07-18 14:10:50+02:00](https://github.com/leanprover-community/mathlib/commit/d9daeff)
refactor(data/polynomial): move polynomials to data; replace monomial by `C a * X^n`
#### Estimated changes
Modified algebra/big_operators.lean


Modified data/finsupp.lean


Renamed linear_algebra/univariate_polynomial.lean to data/polynomial.lean
- \+ *lemma* finsupp.mul_sum
- \+ *lemma* finsupp.sum_mul
- \+/\- *def* polynomial.C
- \+/\- *lemma* polynomial.C_0
- \- *lemma* polynomial.C_mul_monomial
- \+/\- *def* polynomial.X
- \+/\- *lemma* polynomial.X_apply_one
- \+ *lemma* polynomial.X_pow_apply
- \- *lemma* polynomial.X_pow_eq_monomial
- \+/\- *lemma* polynomial.add_apply
- \+/\- *lemma* polynomial.degree_C
- \+ *lemma* polynomial.degree_C_le
- \+/\- *lemma* polynomial.degree_X
- \+/\- *lemma* polynomial.degree_add_div_by_monic
- \+/\- *lemma* polynomial.degree_div_by_monic_lt
- \+/\- *def* polynomial.degree_lt_wf
- \+/\- *lemma* polynomial.degree_mod_by_monic_lt
- \+/\- *lemma* polynomial.degree_monomial
- \+/\- *lemma* polynomial.degree_monomial_le
- \+ *lemma* polynomial.degree_one_le
- \+/\- *lemma* polynomial.degree_pow_eq
- \+/\- *def* polynomial.div
- \+/\- *def* polynomial.div_mod_by_monic_aux
- \- *lemma* polynomial.eval_monomial
- \- *lemma* polynomial.eval_mul_monomial
- \+ *lemma* polynomial.eval_one
- \- *lemma* polynomial.induction_on
- \+/\- *lemma* polynomial.leading_coeff_X
- \+/\- *lemma* polynomial.leading_coeff_monomial
- \+/\- *lemma* polynomial.leading_coeff_mul
- \+/\- *lemma* polynomial.leading_coeff_one
- \+/\- *lemma* polynomial.mod_by_monic_add_div
- \+/\- *lemma* polynomial.monic_mul_leading_coeff_inv
- \- *def* polynomial.monomial
- \- *lemma* polynomial.monomial_add_left
- \- *lemma* polynomial.monomial_add_right
- \- *lemma* polynomial.monomial_apply
- \- *lemma* polynomial.monomial_apply_self
- \- *lemma* polynomial.monomial_eq
- \- *lemma* polynomial.monomial_induction_on
- \- *lemma* polynomial.monomial_mul_monomial
- \- *lemma* polynomial.monomial_zero_right
- \+/\- *lemma* polynomial.mul_div_by_monic_eq_iff_is_root
- \+/\- *def* polynomial.nat_degree
- \+/\- *lemma* polynomial.ne_zero_of_monic
- \+/\- *lemma* polynomial.ne_zero_of_ne_zero_of_monic
- \+/\- *lemma* polynomial.root_X_sub_C
- \+ *lemma* polynomial.single_eq_C_mul_X
- \+/\- *lemma* polynomial.subsingleton_of_monic_zero
- \+/\- *lemma* with_bot.coe_add



## [2018-07-18 14:10:50+02:00](https://github.com/leanprover-community/mathlib/commit/ce990c5)
feat(linear_algebra/univariate_polynomial): univariate polynomials
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* finset.max_eq_none
- \+ *theorem* finset.min_eq_none

Added linear_algebra/univariate_polynomial.lean
- \+ *def* polynomial.C
- \+ *lemma* polynomial.C_0
- \+ *lemma* polynomial.C_1
- \+ *lemma* polynomial.C_apply
- \+ *lemma* polynomial.C_apply_zero
- \+ *lemma* polynomial.C_mul_C
- \+ *lemma* polynomial.C_mul_apply
- \+ *lemma* polynomial.C_mul_monomial
- \+ *def* polynomial.X
- \+ *lemma* polynomial.X_apply_one
- \+ *lemma* polynomial.X_pow_eq_monomial
- \+ *lemma* polynomial.add_apply
- \+ *lemma* polynomial.card_roots
- \+ *def* polynomial.degree
- \+ *lemma* polynomial.degree_C
- \+ *lemma* polynomial.degree_X
- \+ *lemma* polynomial.degree_X_sub_C
- \+ *lemma* polynomial.degree_add_div_by_monic
- \+ *lemma* polynomial.degree_add_eq_of_degree_lt
- \+ *lemma* polynomial.degree_add_eq_of_leading_coeff_add_ne_zero
- \+ *lemma* polynomial.degree_add_le
- \+ *lemma* polynomial.degree_div_by_monic_le
- \+ *lemma* polynomial.degree_div_by_monic_lt
- \+ *lemma* polynomial.degree_eq_bot
- \+ *lemma* polynomial.degree_eq_nat_degree
- \+ *lemma* polynomial.degree_erase_le
- \+ *lemma* polynomial.degree_erase_lt
- \+ *def* polynomial.degree_lt_wf
- \+ *lemma* polynomial.degree_mod_by_monic_lt
- \+ *lemma* polynomial.degree_monomial
- \+ *lemma* polynomial.degree_monomial_le
- \+ *lemma* polynomial.degree_mul_eq'
- \+ *lemma* polynomial.degree_mul_eq
- \+ *lemma* polynomial.degree_mul_le
- \+ *lemma* polynomial.degree_mul_leading_coeff_inv
- \+ *lemma* polynomial.degree_neg
- \+ *lemma* polynomial.degree_one
- \+ *lemma* polynomial.degree_pos_of_root
- \+ *lemma* polynomial.degree_pow_eq'
- \+ *lemma* polynomial.degree_pow_eq
- \+ *lemma* polynomial.degree_pow_le
- \+ *lemma* polynomial.degree_sub_lt
- \+ *lemma* polynomial.degree_sum_le
- \+ *lemma* polynomial.degree_zero
- \+ *def* polynomial.div
- \+ *def* polynomial.div_by_monic
- \+ *lemma* polynomial.div_by_monic_eq_div
- \+ *lemma* polynomial.div_by_monic_eq_of_not_monic
- \+ *lemma* polynomial.div_by_monic_eq_zero_iff
- \+ *lemma* polynomial.div_by_monic_zero
- \+ *def* polynomial.div_mod_by_monic_aux
- \+ *lemma* polynomial.div_wf_lemma
- \+ *lemma* polynomial.dvd_iff_mod_by_monic_eq_zero
- \+ *lemma* polynomial.eq_C_of_degree_le_zero
- \+ *lemma* polynomial.eq_zero_of_degree_lt
- \+ *def* polynomial.eval
- \+ *lemma* polynomial.eval_C
- \+ *lemma* polynomial.eval_X
- \+ *lemma* polynomial.eval_add
- \+ *lemma* polynomial.eval_monomial
- \+ *lemma* polynomial.eval_mul
- \+ *lemma* polynomial.eval_mul_monomial
- \+ *lemma* polynomial.eval_neg
- \+ *lemma* polynomial.eval_sub
- \+ *lemma* polynomial.eval_zero
- \+ *lemma* polynomial.exists_finset_roots
- \+ *lemma* polynomial.induction_on
- \+ *lemma* polynomial.is_root.def
- \+ *def* polynomial.is_root
- \+ *lemma* polynomial.le_degree_of_ne_zero
- \+ *def* polynomial.leading_coeff
- \+ *lemma* polynomial.leading_coeff_C
- \+ *lemma* polynomial.leading_coeff_X
- \+ *lemma* polynomial.leading_coeff_add_of_degree_eq
- \+ *lemma* polynomial.leading_coeff_add_of_degree_lt
- \+ *lemma* polynomial.leading_coeff_eq_zero
- \+ *lemma* polynomial.leading_coeff_monomial
- \+ *lemma* polynomial.leading_coeff_mul'
- \+ *lemma* polynomial.leading_coeff_mul
- \+ *lemma* polynomial.leading_coeff_one
- \+ *lemma* polynomial.leading_coeff_pow'
- \+ *lemma* polynomial.leading_coeff_pow
- \+ *lemma* polynomial.leading_coeff_zero
- \+ *lemma* polynomial.mem_roots
- \+ *def* polynomial.mod
- \+ *lemma* polynomial.mod_X_sub_C_eq_C_eval
- \+ *def* polynomial.mod_by_monic
- \+ *lemma* polynomial.mod_by_monic_X_sub_C_eq_C_eval
- \+ *lemma* polynomial.mod_by_monic_add_div
- \+ *lemma* polynomial.mod_by_monic_eq_mod
- \+ *lemma* polynomial.mod_by_monic_eq_of_not_monic
- \+ *lemma* polynomial.mod_by_monic_eq_self_iff
- \+ *lemma* polynomial.mod_by_monic_eq_sub_mul_div
- \+ *lemma* polynomial.mod_by_monic_zero
- \+ *lemma* polynomial.monic.def
- \+ *def* polynomial.monic
- \+ *lemma* polynomial.monic_X_sub_C
- \+ *lemma* polynomial.monic_mul_leading_coeff_inv
- \+ *lemma* polynomial.monic_one
- \+ *def* polynomial.monomial
- \+ *lemma* polynomial.monomial_add_left
- \+ *lemma* polynomial.monomial_add_right
- \+ *lemma* polynomial.monomial_apply
- \+ *lemma* polynomial.monomial_apply_self
- \+ *lemma* polynomial.monomial_eq
- \+ *lemma* polynomial.monomial_induction_on
- \+ *lemma* polynomial.monomial_mul_monomial
- \+ *lemma* polynomial.monomial_zero_right
- \+ *lemma* polynomial.mul_apply_degree_add_degree
- \+ *lemma* polynomial.mul_div_by_monic_eq_iff_is_root
- \+ *lemma* polynomial.mul_div_eq_iff_is_root
- \+ *def* polynomial.nat_degree
- \+ *lemma* polynomial.nat_degree_C
- \+ *lemma* polynomial.nat_degree_eq_of_degree_eq
- \+ *lemma* polynomial.nat_degree_mul_eq'
- \+ *lemma* polynomial.ne_zero_of_degree_gt
- \+ *lemma* polynomial.ne_zero_of_monic
- \+ *lemma* polynomial.ne_zero_of_ne_zero_of_monic
- \+ *lemma* polynomial.neg_apply
- \+ *lemma* polynomial.not_monic_zero
- \+ *lemma* polynomial.one_apply_zero
- \+ *lemma* polynomial.root_X_sub_C
- \+ *lemma* polynomial.root_mul_left_of_is_root
- \+ *lemma* polynomial.root_mul_right_of_is_root
- \+ *lemma* polynomial.root_or_root_of_root_mul
- \+ *lemma* polynomial.subsingleton_of_monic_zero
- \+ *lemma* polynomial.support_zero
- \+ *lemma* polynomial.zero_apply
- \+ *lemma* polynomial.zero_div_by_monic
- \+ *lemma* polynomial.zero_mod_by_monic
- \+ *def* polynomial
- \+ *lemma* with_bot.add_bot
- \+ *lemma* with_bot.bot_add
- \+ *lemma* with_bot.bot_lt_some
- \+ *lemma* with_bot.coe_add
- \+ *lemma* with_bot.coe_lt_coe

Modified order/bounded_lattice.lean
- \+ *lemma* with_bot.well_founded_lt
- \+ *lemma* with_top.well_founded_lt



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
- \+ *lemma* is_ideal.exists_inv
- \+ *lemma* is_ideal.mul_left
- \+ *lemma* is_ideal.mul_right
- \+ *lemma* is_ideal.neg_iff
- \+ *def* is_ideal.quotient
- \+ *lemma* is_ideal.quotient_eq_zero_iff_mem
- \+ *def* is_ideal.quotient_rel
- \+ *lemma* is_proper_ideal_iff_one_not_mem
- \- *theorem* not_unit_of_mem_maximal_ideal
- \+ *theorem* not_unit_of_mem_proper_ideal



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
- \+ *theorem* encodable.decode2_is_partial_inv
- \+ *theorem* encodable.mem_decode2'

Modified data/set/countable.lean
- \+ *def* set.countable.to_encodable
- \- *lemma* set.countable.to_encodable
- \+/\- *def* set.countable
- \+/\- *lemma* set.countable_encodable'
- \+/\- *lemma* set.countable_encodable
- \+ *lemma* set.countable_iff_exists_inj_on
- \+ *lemma* set.countable_iff_exists_injective
- \+/\- *lemma* set.countable_image
- \+ *lemma* set.countable_range
- \+/\- *lemma* set.countable_set_of_finite_subset
- \+/\- *lemma* set.countable_singleton

Modified data/set/function.lean
- \+ *lemma* set.inj_on_iff_injective
- \+ *lemma* set.surj_on_iff_surjective

Modified logic/function.lean
- \+ *theorem* function.is_partial_inv_left
- \+ *theorem* function.partial_inv_left



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
- \+/\- *theorem* finset.disjoint_empty_left
- \+/\- *theorem* finset.disjoint_empty_right
- \+ *theorem* finset.inf_eq_inter
- \+ *theorem* finset.sup_eq_union

Modified data/set/disjointed.lean




## [2018-07-16 20:46:11-04:00](https://github.com/leanprover-community/mathlib/commit/bdc90f6)
feat(data/set/basic): more set theorems, normalize naming
#### Estimated changes
Modified algebra/module.lean
- \- *lemma* set.sInter_eq_Inter

Modified analysis/topology/topological_space.lean
- \+/\- *lemma* is_open_diff

Modified analysis/topology/uniform_space.lean


Modified data/analysis/topology.lean


Modified data/set/basic.lean
- \+ *lemma* set.compl_subset_compl
- \+ *theorem* set.diff_eq_empty
- \+ *theorem* set.diff_eq_self
- \+ *theorem* set.diff_inter_self
- \- *theorem* set.diff_neq_empty
- \- *theorem* set.diff_right_antimono
- \+ *theorem* set.diff_singleton_eq_self
- \+ *theorem* set.diff_subset_diff_left
- \+ *theorem* set.diff_subset_diff_right
- \+ *theorem* set.diff_union_self
- \+ *theorem* set.insert_diff
- \+ *theorem* set.insert_diff_singleton
- \- *theorem* set.insert_sdiff
- \+ *theorem* set.inter_diff_assoc
- \+ *theorem* set.inter_diff_self
- \+/\- *theorem* set.inter_subset_inter_left
- \+/\- *theorem* set.inter_subset_inter_right
- \+ *theorem* set.inter_union_diff
- \+ *theorem* set.union_diff_cancel_left
- \+ *theorem* set.union_diff_cancel_right
- \+ *theorem* set.union_diff_left
- \+ *theorem* set.union_diff_right
- \+ *theorem* set.union_diff_self
- \+ *theorem* set.union_inter_cancel_left
- \+ *theorem* set.union_inter_cancel_right
- \+/\- *theorem* set.union_subset_union
- \+ *theorem* set.union_subset_union_left
- \+ *theorem* set.union_subset_union_right

Modified data/set/disjointed.lean


Modified data/set/finite.lean


Modified data/set/lattice.lean
- \+ *theorem* disjoint.comm
- \+ *theorem* disjoint.eq_bot
- \+ *theorem* disjoint.symm
- \+/\- *def* disjoint
- \+/\- *theorem* disjoint_bot_left
- \+/\- *theorem* disjoint_bot_right
- \- *lemma* disjoint_comm
- \+ *theorem* disjoint_iff
- \- *theorem* disjoint_symm
- \+ *theorem* set.Inter_const
- \+/\- *theorem* set.Inter_eq_comp_Union_comp
- \- *theorem* set.Inter_eq_sInter_image
- \+ *theorem* set.Inter_eq_sInter_range
- \+ *theorem* set.Inter_inter_distrib
- \+ *theorem* set.Inter_subset
- \+ *theorem* set.Union_const
- \+/\- *theorem* set.Union_eq_comp_Inter_comp
- \+ *theorem* set.Union_eq_range_sigma
- \- *theorem* set.Union_eq_sUnion_image
- \+ *theorem* set.Union_eq_sUnion_range
- \+ *theorem* set.Union_union_distrib
- \+ *theorem* set.bInter_eq_Inter
- \+ *theorem* set.bUnion_eq_Union
- \+/\- *theorem* set.compl_Inter
- \+/\- *theorem* set.compl_Union
- \- *lemma* set.compl_subset_compl_iff_subset
- \+ *theorem* set.diff_Inter_left
- \+ *theorem* set.diff_Union_left
- \+ *theorem* set.diff_Union_right
- \+ *theorem* set.disjoint_diff
- \- *theorem* set.insert_sdiff_singleton
- \+ *theorem* set.inter_Inter_left
- \+ *theorem* set.inter_Inter_right
- \+ *theorem* set.inter_Union_left
- \+ *theorem* set.inter_Union_right
- \- *theorem* set.inter_distrib_Union_left
- \- *theorem* set.inter_distrib_Union_right
- \+ *lemma* set.inter_eq_Inter
- \+/\- *theorem* set.mem_Inter
- \- *theorem* set.mem_Inter_eq
- \+ *theorem* set.mem_Inter_of_mem
- \+ *theorem* set.mem_Union
- \- *theorem* set.mem_Union_eq
- \+/\- *theorem* set.mem_sInter
- \- *theorem* set.mem_sInter_eq
- \+/\- *theorem* set.mem_sUnion
- \- *theorem* set.mem_sUnion_eq
- \+ *theorem* set.mem_sUnion_of_mem
- \+ *theorem* set.range_sigma_eq_Union_range
- \+ *lemma* set.sInter_eq_Inter
- \+ *lemma* set.sInter_eq_bInter
- \+/\- *theorem* set.sInter_subset_of_mem
- \+ *theorem* set.sInter_subset_sInter
- \- *lemma* set.sUnion_eq_Union'
- \+/\- *lemma* set.sUnion_eq_Union
- \+ *lemma* set.sUnion_eq_bUnion
- \+/\- *theorem* set.sUnion_subset_iff
- \+ *theorem* set.sUnion_subset_sUnion
- \- *lemma* set.sdiff_empty
- \- *lemma* set.sdiff_eq:
- \- *theorem* set.sdiff_inter_same
- \- *theorem* set.sdiff_singleton_eq_same
- \- *theorem* set.sdiff_subset_sdiff
- \- *theorem* set.sdiff_union_same
- \+ *theorem* set.sub_eq_diff
- \+/\- *theorem* set.subset_Union
- \+/\- *theorem* set.subset_sUnion_of_mem
- \+ *theorem* set.union_Inter_left
- \+ *theorem* set.union_Union_left
- \+ *theorem* set.union_Union_right
- \- *theorem* set.union_distrib_Inter_left
- \+ *lemma* set.union_eq_Union
- \- *lemma* set.union_of_subset_right
- \- *theorem* set.union_same_compl
- \- *lemma* set.union_sdiff_left
- \- *lemma* set.union_sdiff_right
- \- *theorem* set.union_sdiff_same

Modified linear_algebra/basic.lean


Modified logic/schroeder_bernstein.lean


Modified order/filter.lean


Modified order/galois_connection.lean




## [2018-07-16 20:17:22-04:00](https://github.com/leanprover-community/mathlib/commit/9f6bcd0)
refactor(data/bool): decidable forall bool
#### Estimated changes
Modified data/bool.lean
- \- *theorem* bool.absurd_of_eq_ff_of_eq_tt
- \+/\- *theorem* bool.band_assoc
- \+/\- *theorem* bool.band_comm
- \+/\- *theorem* bool.band_elim_left
- \+/\- *theorem* bool.band_elim_right
- \+/\- *theorem* bool.band_intro
- \+/\- *theorem* bool.band_left_comm
- \+/\- *theorem* bool.bor_assoc
- \+/\- *theorem* bool.bor_comm
- \+/\- *theorem* bool.bor_left_comm
- \+/\- *theorem* bool.bxor_assoc
- \+/\- *theorem* bool.bxor_comm
- \+/\- *theorem* bool.bxor_left_comm
- \+/\- *theorem* bool.eq_ff_of_bnot_eq_tt
- \+/\- *theorem* bool.eq_ff_of_ne_tt
- \+/\- *theorem* bool.eq_tt_of_bnot_eq_ff
- \+/\- *theorem* bool.eq_tt_of_ne_ff
- \+ *theorem* bool.exists_bool
- \+ *theorem* bool.forall_bool



## [2018-07-16 20:16:24-04:00](https://github.com/leanprover-community/mathlib/commit/8685bf2)
refactor(topology/continuity): remove inhabited from dense extend
#### Estimated changes
Modified analysis/topology/continuity.lean
- \- *lemma* dense_embedding.continuous_ext
- \+ *lemma* dense_embedding.continuous_extend
- \- *def* dense_embedding.ext
- \- *lemma* dense_embedding.ext_e_eq
- \- *lemma* dense_embedding.ext_eq
- \+ *def* dense_embedding.extend
- \+ *lemma* dense_embedding.extend_e_eq
- \+ *lemma* dense_embedding.extend_eq
- \- *lemma* dense_embedding.tendsto_ext
- \+ *lemma* dense_embedding.tendsto_extend

Modified analysis/topology/uniform_space.lean




## [2018-07-16 20:03:13-04:00](https://github.com/leanprover-community/mathlib/commit/57f07e0)
refactor(data/set/basic): rename set.set_eq_def -> set.ext_iff
#### Estimated changes
Modified analysis/metric_space.lean


Modified data/finset.lean
- \+/\- *lemma* finset.coe_image
- \+/\- *lemma* finset.coe_inter
- \+/\- *lemma* finset.coe_union

Modified data/semiquot.lean


Modified data/set/basic.lean
- \+ *theorem* set.ext_iff
- \- *theorem* set.set_eq_def

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


Modified tactic/basic.lean


Modified tactic/interactive.lean


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


Added tactic/tauto.lean


Modified tests/examples.lean


Modified tests/tactics.lean




## [2018-07-16 19:40:28-04:00](https://github.com/leanprover-community/mathlib/commit/c3e24f3)
docs(code-review): add check list ([#195](https://github.com/leanprover-community/mathlib/pull/195)) [ci-skip]
#### Estimated changes
Added PULL_REQUEST_TEMPLATE.md


Added docs/code-review.md




## [2018-07-16 19:39:17-04:00](https://github.com/leanprover-community/mathlib/commit/3a79975)
feat(data/quot): quot.hrec_on₂, quotient.hrec_on₂ ([#197](https://github.com/leanprover-community/mathlib/pull/197))
#### Estimated changes
Modified data/quot.lean




## [2018-07-16 19:34:21-04:00](https://github.com/leanprover-community/mathlib/commit/dd6cc57)
chore(build): make travis build fail quicker when errors are found
#### Estimated changes
Modified .travis.yml


Added travis_long.sh




## [2018-07-16 19:33:09-04:00](https://github.com/leanprover-community/mathlib/commit/631207b)
feat(data/multiset,...): card_eq_one
based on [#200](https://github.com/leanprover-community/mathlib/pull/200)
#### Estimated changes
Modified algebra/group_power.lean
- \+ *theorem* neg_one_pow_eq_or

Modified data/list/basic.lean
- \+ *theorem* list.length_eq_one

Modified data/multiset.lean
- \+ *theorem* multiset.card_eq_one
- \+ *theorem* multiset.empty_eq_zero
- \+ *theorem* multiset.strong_induction_eq

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
- \+ *theorem* list.cons_subperm_of_mem



## [2018-07-16 14:06:55+02:00](https://github.com/leanprover-community/mathlib/commit/20fca1c)
feat(data/finset): disjoint finsets
#### Estimated changes
Modified data/finset.lean
- \+ *theorem* finset.card_disjoint_union
- \+ *theorem* finset.disjoint_empty_left
- \+ *theorem* finset.disjoint_empty_right
- \+ *theorem* finset.disjoint_iff_inter_eq_empty
- \+ *theorem* finset.disjoint_iff_ne
- \+ *theorem* finset.disjoint_insert_left
- \+ *theorem* finset.disjoint_insert_right
- \+ *theorem* finset.disjoint_left
- \+ *theorem* finset.disjoint_of_subset_left
- \+ *theorem* finset.disjoint_of_subset_right
- \+ *theorem* finset.disjoint_right
- \+ *theorem* finset.disjoint_singleton
- \+ *theorem* finset.disjoint_union_left
- \+ *theorem* finset.disjoint_union_right
- \- *theorem* finset.inter_eq_empty_iff_disjoint
- \+ *theorem* finset.singleton_disjoint

Modified data/set/lattice.lean
- \+ *lemma* disjoint_comm



## [2018-07-16 12:59:35+01:00](https://github.com/leanprover-community/mathlib/commit/844c665)
feat(category/applicative): `id` and `comp` functors; proofs by `norm` ([#184](https://github.com/leanprover-community/mathlib/pull/184))
#### Estimated changes
Added category/applicative.lean
- \+ *lemma* applicative.map_seq_map
- \+ *lemma* applicative.pure_seq_eq_map'
- \+ *lemma* comp.map_pure
- \+ *lemma* comp.pure_seq_eq_map
- \+ *lemma* comp.seq_assoc
- \+ *lemma* comp.seq_mk
- \+ *lemma* comp.seq_pure

Modified category/basic.lean
- \- *theorem* map_map
- \- *def* mmap₂
- \+ *def* mzip_with'
- \+ *def* mzip_with

Added category/functor.lean
- \+ *lemma* functor.comp.map_mk
- \+ *lemma* functor.map_comp_map
- \+ *lemma* functor.map_id
- \+ *def* id.mk

Modified data/prod.lean


Modified data/set/basic.lean


Added tactic/ext.lean


Modified tactic/interactive.lean


Modified tests/tactics.lean




## [2018-07-12 18:02:46-04:00](https://github.com/leanprover-community/mathlib/commit/8dda9cd)
fix(analysis/topology/continuity): remove an extraneous constraint
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+/\- *lemma* continuous_subtype_is_closed_cover



## [2018-07-12 18:00:11-04:00](https://github.com/leanprover-community/mathlib/commit/42ba098)
feat(data/set/basic): diff_subset_iff, diff_subset_comm
#### Estimated changes
Modified data/set/basic.lean
- \+ *lemma* set.diff_subset_comm
- \+ *lemma* set.diff_subset_iff



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
- \+ *def* multiset.decidable_exists_multiset



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
- \+ *def* equiv.set_value
- \+ *theorem* equiv.set_value_eq

Modified data/fintype.lean


Modified data/list/basic.lean
- \+ *theorem* list.filter_of_map

Modified data/multiset.lean
- \+ *def* multiset.strong_induction_on
- \- *lemma* multiset.strong_induction_on

Modified data/pfun.lean
- \+ *def* pfun.equiv_subtype
- \+ *theorem* roption.eta
- \+ *theorem* roption.of_option_dom
- \+ *theorem* roption.of_option_eq_get



## [2018-07-07 02:03:44-04:00](https://github.com/leanprover-community/mathlib/commit/71953e0)
feat(order/basic): add extensionality for order structures
#### Estimated changes
Modified order/basic.lean
- \+ *theorem* linear_order.ext
- \+ *theorem* partial_order.ext
- \+ *theorem* preorder.ext

Modified order/bounded_lattice.lean
- \+ *theorem* lattice.bounded_lattice.ext
- \+ *theorem* lattice.order_bot.ext
- \+ *theorem* lattice.order_bot.ext_bot
- \+ *theorem* lattice.order_top.ext
- \+ *theorem* lattice.order_top.ext_top
- \+ *theorem* with_bot.inf_eq_min
- \+ *theorem* with_bot.lattice_eq_DLO
- \+ *theorem* with_bot.sup_eq_max
- \+ *theorem* with_top.inf_eq_min
- \+ *theorem* with_top.lattice_eq_DLO
- \+ *theorem* with_top.sup_eq_max

Modified order/lattice.lean
- \+ *theorem* lattice.inf_eq_min
- \+ *theorem* lattice.lattice.ext
- \+ *theorem* lattice.semilattice_inf.ext
- \+ *theorem* lattice.semilattice_inf.ext_inf
- \+ *theorem* lattice.semilattice_sup.ext
- \+ *theorem* lattice.semilattice_sup.ext_sup
- \+ *theorem* lattice.sup_eq_max



## [2018-07-06 09:04:17-04:00](https://github.com/leanprover-community/mathlib/commit/ab1861a)
feat(data/subtype): setoid (subtype p)
#### Estimated changes
Modified data/subtype.lean
- \+ *theorem* subtype.equiv_iff
- \+ *theorem* subtype.equivalence



## [2018-07-06 09:04:17-04:00](https://github.com/leanprover-community/mathlib/commit/d54950a)
refactor(data/subtype): move out of data/sigma/basic.lean
#### Estimated changes
Modified data/equiv/denumerable.lean


Modified data/set/basic.lean


Modified data/sigma/basic.lean
- \- *theorem* subtype.coe_eta
- \- *theorem* subtype.coe_mk
- \- *theorem* subtype.exists
- \- *lemma* subtype.ext
- \- *theorem* subtype.forall
- \- *def* subtype.map
- \- *theorem* subtype.map_comp
- \- *theorem* subtype.map_id
- \- *theorem* subtype.mk_eq_mk
- \- *theorem* subtype.val_injective

Added data/subtype.lean
- \+ *theorem* subtype.coe_eta
- \+ *theorem* subtype.coe_mk
- \+ *theorem* subtype.exists
- \+ *lemma* subtype.ext
- \+ *theorem* subtype.forall
- \+ *def* subtype.map
- \+ *theorem* subtype.map_comp
- \+ *theorem* subtype.map_id
- \+ *theorem* subtype.mk_eq_mk
- \+ *theorem* subtype.val_injective

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

Added tactic/cache.lean


Modified tactic/interactive.lean
- \- *lemma* tactic.interactive.iff.trans
- \- *theorem* tactic.interactive.imp.swap
- \- *theorem* tactic.interactive.imp_not_comm
- \- *theorem* tactic.interactive.not_and_distrib'
- \- *theorem* tactic.interactive.not_and_distrib
- \- *theorem* tactic.interactive.not_and_of_not_or_not
- \- *theorem* tactic.interactive.not_or_distrib
- \- *theorem* tactic.interactive.or_iff_not_imp_left
- \- *theorem* tactic.interactive.or_iff_not_imp_right

Modified tests/examples.lean




## [2018-07-06 03:44:23-04:00](https://github.com/leanprover-community/mathlib/commit/06f4778)
feat(tactic/tauto): handle `or` in goal
#### Estimated changes
Modified tactic/interactive.lean
- \+ *lemma* tactic.interactive.iff.trans
- \+ *theorem* tactic.interactive.imp.swap
- \+ *theorem* tactic.interactive.imp_not_comm
- \+ *theorem* tactic.interactive.not_and_distrib'
- \+ *theorem* tactic.interactive.not_and_distrib
- \+ *theorem* tactic.interactive.not_and_of_not_or_not
- \+ *theorem* tactic.interactive.not_or_distrib
- \+ *theorem* tactic.interactive.or_iff_not_imp_left
- \+ *theorem* tactic.interactive.or_iff_not_imp_right

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
- \+ *def* turing.TM0.cfg.map
- \+/\- *def* turing.TM0.init
- \+ *def* turing.TM0.machine.map
- \+ *theorem* turing.TM0.machine.map_respects
- \+ *theorem* turing.TM0.machine.map_step
- \+ *theorem* turing.TM0.map_init
- \+/\- *theorem* turing.TM0.step_supports
- \+ *def* turing.TM0.stmt.map
- \+/\- *def* turing.TM0.supports
- \+ *theorem* turing.TM0.univ_supports
- \+ *def* turing.TM0to1.tr
- \+ *def* turing.TM0to1.tr_cfg
- \+ *theorem* turing.TM0to1.tr_respects
- \+/\- *def* turing.TM1.init
- \+/\- *def* turing.TM1.step_aux
- \+/\- *def* turing.TM1to0.tr_cfg
- \+/\- *theorem* turing.TM1to0.tr_supports
- \+ *theorem* turing.TM1to1.exists_enc_dec
- \+ *def* turing.TM1to1.move
- \+ *def* turing.TM1to1.read
- \+ *def* turing.TM1to1.read_aux
- \+ *theorem* turing.TM1to1.step_aux_move
- \+ *theorem* turing.TM1to1.step_aux_read
- \+ *theorem* turing.TM1to1.step_aux_write
- \+ *theorem* turing.TM1to1.supports_stmt_move
- \+ *theorem* turing.TM1to1.supports_stmt_read
- \+ *theorem* turing.TM1to1.supports_stmt_write
- \+ *def* turing.TM1to1.tr
- \+ *def* turing.TM1to1.tr_cfg
- \+ *def* turing.TM1to1.tr_normal
- \+ *theorem* turing.TM1to1.tr_respects
- \+ *theorem* turing.TM1to1.tr_supports
- \+ *def* turing.TM1to1.tr_tape'
- \+ *theorem* turing.TM1to1.tr_tape'_move_left
- \+ *theorem* turing.TM1to1.tr_tape'_move_right
- \+ *def* turing.TM1to1.tr_tape
- \+ *theorem* turing.TM1to1.tr_tape_drop_right
- \+ *theorem* turing.TM1to1.tr_tape_take_right
- \+ *def* turing.TM1to1.write
- \+/\- *def* turing.TM2.init
- \+/\- *def* turing.TM2.step_aux
- \+/\- *theorem* turing.TM2to1.tr_respects_aux₃
- \- *def* turing.TM2to1.Λ'_inh
- \+ *def* turing.pointed_map
- \+ *theorem* turing.reaches.to₀
- \+ *theorem* turing.reaches₀.head
- \+ *theorem* turing.reaches₀.refl
- \+ *theorem* turing.reaches₀.single
- \+ *theorem* turing.reaches₀.tail'
- \+ *theorem* turing.reaches₀.tail
- \+ *theorem* turing.reaches₀.trans
- \+ *def* turing.reaches₀
- \+ *theorem* turing.reaches₀_eq
- \+ *theorem* turing.reaches₁.to₀
- \+ *theorem* turing.reaches₁_fwd
- \+ *def* turing.tape.map
- \+ *theorem* turing.tape.map_fst
- \+ *theorem* turing.tape.map_mk
- \+ *theorem* turing.tape.map_move
- \+ *theorem* turing.tape.map_write
- \+ *def* turing.tape.mk'

Modified data/bool.lean
- \+ *theorem* bool.default_bool
- \+ *theorem* bool.to_bool_eq

Modified data/fin.lean
- \+ *def* fin.add_nat

Modified data/finset.lean
- \+ *lemma* finset.coe_empty
- \+ *lemma* finset.coe_erase
- \+ *lemma* finset.coe_filter
- \+ *lemma* finset.coe_image
- \+ *theorem* finset.coe_inj
- \+ *lemma* finset.coe_insert
- \+ *lemma* finset.coe_inter
- \+ *lemma* finset.coe_sdiff
- \+ *lemma* finset.coe_singleton
- \+ *theorem* finset.coe_subset
- \+ *lemma* finset.coe_union
- \+ *lemma* finset.mem_coe
- \+ *def* finset.to_set

Modified data/fintype.lean


Modified data/list/basic.lean
- \+ *theorem* list.bind_append
- \+ *theorem* list.drop_add
- \+ *theorem* list.drop_left'
- \+ *theorem* list.drop_left
- \+ *theorem* list.drop_one
- \+ *theorem* list.ne_nil_of_mem
- \+ *theorem* list.reverse_repeat
- \+ *def* list.take'
- \+ *theorem* list.take'_eq_take
- \+ *theorem* list.take'_left'
- \+ *theorem* list.take'_left
- \+ *theorem* list.take'_length
- \+ *theorem* list.take'_nil
- \+ *theorem* list.take_left'
- \+ *theorem* list.take_left

Modified data/set/finite.lean
- \- *lemma* finset.coe_empty
- \- *lemma* finset.coe_eq_coe
- \- *lemma* finset.coe_erase
- \- *lemma* finset.coe_filter
- \- *lemma* finset.coe_image
- \- *lemma* finset.coe_insert
- \- *lemma* finset.coe_inter
- \- *lemma* finset.coe_sdiff
- \- *lemma* finset.coe_singleton
- \- *lemma* finset.coe_subseteq_coe
- \- *lemma* finset.coe_union
- \- *lemma* finset.mem_coe
- \- *def* finset.to_set

Modified data/vector2.lean
- \+/\- *theorem* vector.mk_to_list
- \+ *def* vector.reverse

Modified linear_algebra/basic.lean


Modified logic/embedding.lean
- \+ *theorem* function.embedding.set_value_eq



## [2018-07-02 13:11:51+02:00](https://github.com/leanprover-community/mathlib/commit/b5e07ad)
fix(analysis/topology): prod.ext is now prod.ext_iff
#### Estimated changes
Modified analysis/topology/continuity.lean




## [2018-07-02 11:47:11+02:00](https://github.com/leanprover-community/mathlib/commit/3f66b3a)
feat(analysis/topology/continuity): generalized tube lemma and some corollaries
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* closed_of_compact
- \+ *lemma* compact_compact_separated
- \+ *lemma* continuous_swap
- \+ *lemma* diagonal_eq_range_diagonal_map
- \+ *lemma* generalized_tube_lemma
- \+ *lemma* nhds_contain_boxes.comm
- \+ *lemma* nhds_contain_boxes.symm
- \+ *def* nhds_contain_boxes
- \+ *lemma* nhds_contain_boxes_of_compact
- \+ *lemma* nhds_contain_boxes_of_singleton
- \+ *lemma* prod_subset_compl_diagonal_iff_disjoint

Modified analysis/topology/topological_space.lean
- \+ *lemma* is_open_bInter
- \+ *lemma* is_open_bUnion



## [2018-07-02 11:47:11+02:00](https://github.com/leanprover-community/mathlib/commit/225dd84)
feat(data/set/lattice): add more lemmas pertaining to bInter, bUnion
#### Estimated changes
Modified data/set/lattice.lean
- \+ *theorem* set.bInter_subset_bInter_right
- \+ *theorem* set.bUnion_subset_bUnion_right
- \+ *theorem* set.compl_bInter
- \+ *theorem* set.compl_bUnion

