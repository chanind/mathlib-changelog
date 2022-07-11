## [2018-01-26 03:15:01-05:00](https://github.com/leanprover-community/mathlib/commit/edd62de)
fix(set_theory/zfc): update to lean
#### Estimated changes
Modified set_theory/zfc.lean
- \+/\- *theorem* mem_hom_left
- \+/\- *theorem* mem_hom_right
- \+/\- *def* fval



## [2018-01-26 02:52:13-05:00](https://github.com/leanprover-community/mathlib/commit/f46d32b)
feat(algebra/archimedean): generalize real thms to archimedean fields
#### Estimated changes
Created algebra/archimedean.lean
- \+ *theorem* le_floor
- \+ *theorem* floor_lt
- \+ *theorem* floor_le
- \+ *theorem* floor_nonneg
- \+ *theorem* lt_succ_floor
- \+ *theorem* lt_floor_add_one
- \+ *theorem* sub_one_lt_floor
- \+ *theorem* floor_coe
- \+ *theorem* floor_mono
- \+ *theorem* floor_add_int
- \+ *theorem* floor_sub_int
- \+ *theorem* ceil_le
- \+ *theorem* lt_ceil
- \+ *theorem* le_ceil
- \+ *theorem* ceil_coe
- \+ *theorem* ceil_mono
- \+ *theorem* ceil_add_int
- \+ *theorem* ceil_sub_int
- \+ *theorem* ceil_lt_add_one
- \+ *theorem* exists_nat_gt
- \+ *theorem* exists_int_gt
- \+ *theorem* exists_int_lt
- \+ *theorem* exists_floor
- \+ *theorem* archimedean_iff_nat_lt
- \+ *theorem* archimedean_iff_nat_le
- \+ *theorem* exists_rat_gt
- \+ *theorem* archimedean_iff_rat_lt
- \+ *theorem* archimedean_iff_rat_le
- \+ *theorem* exists_rat_lt
- \+ *theorem* exists_pos_rat_lt
- \+ *theorem* exists_rat_btwn
- \+ *theorem* exists_rat_near
- \+ *def* floor
- \+ *def* ceil

Modified algebra/group_power.lean
- \+ *theorem* add_monoid.one_smul
- \+ *theorem* add_monoid.smul_eq_mul
- \+ *theorem* add_monoid.smul_eq_mul'
- \+ *theorem* add_monoid.mul_smul_assoc
- \+ *theorem* add_monoid.mul_smul_right
- \+ *theorem* gsmul_eq_mul
- \+ *theorem* gsmul_eq_mul'
- \+ *theorem* mul_gsmul_assoc
- \+ *theorem* mul_gsmul_right
- \+ *theorem* add_monoid.smul_nonneg
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_nonneg
- \+ *theorem* one_le_pow_of_one_le
- \+ *theorem* pow_ge_one_add_mul
- \+ *theorem* pow_ge_one_add_sub_mul
- \- *theorem* pow_ge_one_of_ge_one

Modified analysis/complex.lean


Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/borel_space.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/real.lean


Renamed data/complex.lean to data/complex/basic.lean
- \+ *lemma* re_add_im
- \+ *lemma* abs_le_abs_re_add_abs_im
- \+ *theorem* is_cau_seq_re
- \+ *theorem* is_cau_seq_im
- \+ *theorem* equiv_lim

Modified data/rat.lean
- \+ *theorem* coe_int_num
- \+ *theorem* coe_int_denom
- \+ *theorem* coe_nat_num
- \+ *theorem* coe_nat_denom

Modified data/real/basic.lean
- \+/\- *theorem* le_mk_of_forall_le
- \+/\- *theorem* mk_le_of_forall_le
- \+/\- *theorem* mk_near_of_forall_near
- \- *theorem* exists_rat_gt
- \- *theorem* exists_nat_gt
- \- *theorem* exists_int_gt
- \- *theorem* exists_int_lt
- \- *theorem* exists_rat_lt
- \- *theorem* exists_pos_rat_lt
- \- *theorem* exists_rat_near'
- \- *theorem* exists_rat_near
- \- *theorem* exists_rat_btwn
- \- *theorem* le_floor
- \- *theorem* floor_lt
- \- *theorem* floor_le
- \- *theorem* floor_nonneg
- \- *theorem* lt_succ_floor
- \- *theorem* lt_floor_add_one
- \- *theorem* sub_one_lt_floor
- \- *theorem* floor_coe
- \- *theorem* floor_mono
- \- *theorem* floor_add_int
- \- *theorem* floor_sub_int
- \- *theorem* ceil_le
- \- *theorem* lt_ceil
- \- *theorem* le_ceil
- \- *theorem* ceil_coe
- \- *theorem* ceil_mono
- \- *theorem* ceil_add_int
- \- *theorem* ceil_sub_int
- \- *theorem* ceil_lt_add_one

Modified data/real/cau_seq.lean
- \+ *theorem* mk_to_fun
- \+ *theorem* is_cau

Modified set_theory/ordinal_notation.lean




## [2018-01-25 01:34:48-05:00](https://github.com/leanprover-community/mathlib/commit/0e42187)
fix(algebra/module): fix module typeclass resolution
Before this change, any looping typeclass instance on `ring` (like `ring A -> ring (f A)`) would cause unrelated typeclass problems such as `has_add B` to search for `module ?M B` and then `ring ?M`, leading to an infinite number of applications of the looping ring instance. leanprover/lean[#1881](https://github.com/leanprover-community/mathlib/pull/1881) promises to fix this, but until then here is a workaround.
#### Estimated changes
Modified algebra/linear_algebra/linear_map_module.lean


Modified algebra/linear_algebra/prod_module.lean


Modified algebra/linear_algebra/quotient_module.lean


Modified algebra/linear_algebra/subtype_module.lean


Modified algebra/module.lean




## [2018-01-24 14:25:32-05:00](https://github.com/leanprover-community/mathlib/commit/7fba1af)
fix(analysis/metric_space): remove superfluous typeclass assumptions
#### Estimated changes
Modified analysis/metric_space.lean
- \+/\- *theorem* uniform_continuous_of_metric
- \+/\- *theorem* uniform_embedding_of_metric
- \+/\- *theorem* tendsto_nhds_of_metric
- \+/\- *theorem* continuous_of_metric
- \+/\- *theorem* tendsto_dist



## [2018-01-23 03:30:58-05:00](https://github.com/leanprover-community/mathlib/commit/acb9093)
feat(analysis/complex): complex numbers are a top ring
#### Estimated changes
Modified analysis/complex.lean
- \+ *lemma* uniform_continuous_inv
- \+ *lemma* uniform_continuous_abs
- \+ *lemma* continuous_abs
- \+ *lemma* tendsto_inv
- \+ *lemma* continuous_inv'
- \+ *lemma* continuous_inv
- \+ *lemma* uniform_continuous_mul_const
- \+ *lemma* uniform_continuous_mul
- \+ *lemma* continuous_mul
- \+ *theorem* dist_eq
- \+ *theorem* uniform_continuous_add
- \+ *theorem* uniform_continuous_neg
- \- *theorem* complex.dist_eq

Modified data/complex.lean
- \+ *lemma* abs_abs_sub_le_abs_sub

Modified data/real/cau_seq.lean
- \+ *lemma* sub_abv_le_abv_sub
- \+ *lemma* abs_abv_sub_le_abv_sub



## [2018-01-23 03:07:52-05:00](https://github.com/leanprover-community/mathlib/commit/65c5cb9)
refactor(data/real): generalize cau_seq to arbitrary metrics
the intent is to use this also for the complex numbers
#### Estimated changes
Modified analysis/metric_space.lean


Modified analysis/real.lean


Modified data/complex.lean
- \+/\- *lemma* mul_self_abs
- \+/\- *lemma* abs_abs
- \+/\- *lemma* abs_pos
- \+/\- *lemma* abs_neg
- \+/\- *lemma* abs_sub
- \+/\- *lemma* abs_sub_le
- \+ *theorem* abs_inv
- \+ *theorem* abs_div

Renamed data/real.lean to data/real/basic.lean
- \+/\- *theorem* mk_add
- \+/\- *theorem* mk_neg
- \+/\- *theorem* mk_mul
- \+/\- *theorem* mk_lt
- \+/\- *theorem* mk_pos
- \+/\- *theorem* mk_le
- \+/\- *theorem* le_mk_of_forall_le
- \+/\- *theorem* mk_le_of_forall_le
- \+/\- *theorem* mk_near_of_forall_near
- \+/\- *theorem* is_cau_seq_iff_lift
- \+/\- *theorem* cau_seq_converges
- \+/\- *theorem* equiv_lim
- \+/\- *theorem* sqrt_aux_nonneg
- \+/\- *theorem* sqrt_aux_converges
- \- *theorem* exists_forall_ge_and
- \- *theorem* rat_add_continuous_lemma
- \- *theorem* rat_mul_continuous_lemma
- \- *theorem* rat_inv_continuous_lemma
- \- *theorem* cauchy₂
- \- *theorem* cauchy₃
- \- *theorem* ext
- \- *theorem* cauchy
- \- *theorem* bounded
- \- *theorem* bounded'
- \- *theorem* add_apply
- \- *theorem* mul_apply
- \- *theorem* const_apply
- \- *theorem* const_inj
- \- *theorem* zero_apply
- \- *theorem* one_apply
- \- *theorem* const_add
- \- *theorem* const_mul
- \- *theorem* neg_apply
- \- *theorem* const_neg
- \- *theorem* const_sub
- \- *theorem* sub_apply
- \- *theorem* add_lim_zero
- \- *theorem* mul_lim_zero
- \- *theorem* neg_lim_zero
- \- *theorem* sub_lim_zero
- \- *theorem* zero_lim_zero
- \- *theorem* const_lim_zero
- \- *theorem* equiv_def₃
- \- *theorem* lim_zero_congr
- \- *theorem* abs_pos_of_not_lim_zero
- \- *theorem* inv_aux
- \- *theorem* inv_apply
- \- *theorem* inv_mul_cancel
- \- *theorem* not_lim_zero_of_pos
- \- *theorem* const_pos
- \- *theorem* add_pos
- \- *theorem* pos_add_lim_zero
- \- *theorem* mul_pos
- \- *theorem* trichotomy
- \- *theorem* lt_of_lt_of_eq
- \- *theorem* lt_of_eq_of_lt
- \- *theorem* lt_trans
- \- *theorem* lt_irrefl
- \- *theorem* le_antisymm
- \- *theorem* lt_total
- \- *theorem* le_total
- \- *theorem* const_lt
- \- *theorem* const_equiv
- \- *theorem* const_le
- \- *theorem* exists_gt
- \- *theorem* exists_lt
- \- *theorem* of_near
- \- *theorem* sqrt_two_irrational
- \+/\- *def* real
- \+/\- *def* mk
- \+/\- *def* of_rat
- \+/\- *def* sqrt_aux
- \- *def* is_cau_seq
- \- *def* cau_seq
- \- *def* of_eq
- \- *def* const
- \- *def* lim_zero
- \- *def* inv
- \- *def* pos
- \- *def* irrational

Created data/real/cau_seq.lean
- \+ *lemma* abv_sub_le
- \+ *theorem* abv_zero
- \+ *theorem* abv_one'
- \+ *theorem* abv_one
- \+ *theorem* abv_pos
- \+ *theorem* abv_neg
- \+ *theorem* abv_sub
- \+ *theorem* abv_inv
- \+ *theorem* abv_div
- \+ *theorem* exists_forall_ge_and
- \+ *theorem* rat_add_continuous_lemma
- \+ *theorem* rat_mul_continuous_lemma
- \+ *theorem* rat_inv_continuous_lemma
- \+ *theorem* cauchy₂
- \+ *theorem* cauchy₃
- \+ *theorem* ext
- \+ *theorem* cauchy
- \+ *theorem* bounded
- \+ *theorem* bounded'
- \+ *theorem* add_apply
- \+ *theorem* const_apply
- \+ *theorem* const_inj
- \+ *theorem* zero_apply
- \+ *theorem* one_apply
- \+ *theorem* const_add
- \+ *theorem* mul_apply
- \+ *theorem* const_mul
- \+ *theorem* neg_apply
- \+ *theorem* const_neg
- \+ *theorem* const_sub
- \+ *theorem* sub_apply
- \+ *theorem* add_lim_zero
- \+ *theorem* mul_lim_zero
- \+ *theorem* neg_lim_zero
- \+ *theorem* sub_lim_zero
- \+ *theorem* zero_lim_zero
- \+ *theorem* const_lim_zero
- \+ *theorem* equiv_def₃
- \+ *theorem* lim_zero_congr
- \+ *theorem* abv_pos_of_not_lim_zero
- \+ *theorem* of_near
- \+ *theorem* inv_aux
- \+ *theorem* inv_apply
- \+ *theorem* inv_mul_cancel
- \+ *theorem* not_lim_zero_of_pos
- \+ *theorem* const_pos
- \+ *theorem* add_pos
- \+ *theorem* pos_add_lim_zero
- \+ *theorem* mul_pos
- \+ *theorem* trichotomy
- \+ *theorem* lt_of_lt_of_eq
- \+ *theorem* lt_of_eq_of_lt
- \+ *theorem* lt_trans
- \+ *theorem* lt_irrefl
- \+ *theorem* le_antisymm
- \+ *theorem* lt_total
- \+ *theorem* le_total
- \+ *theorem* const_lt
- \+ *theorem* const_equiv
- \+ *theorem* const_le
- \+ *theorem* exists_gt
- \+ *theorem* exists_lt
- \+ *def* is_cau_seq
- \+ *def* cau_seq
- \+ *def* of_eq
- \+ *def* const
- \+ *def* lim_zero
- \+ *def* inv
- \+ *def* pos

Created data/real/irrational.lean
- \+ *theorem* sqrt_two_irrational
- \+ *def* irrational



## [2018-01-23 00:14:20-05:00](https://github.com/leanprover-community/mathlib/commit/5fe8fbf)
feat(data/complex): properties of the complex absolute value function
#### Estimated changes
Modified algebra/field.lean


Created analysis/complex.lean
- \+ *theorem* complex.dist_eq

Modified data/complex.lean
- \+ *lemma* conj_zero
- \+ *lemma* conj_one
- \+ *lemma* conj_I
- \+ *lemma* conj_add
- \+ *lemma* conj_neg
- \+ *lemma* conj_mul
- \+ *lemma* conj_conj
- \+ *lemma* conj_bijective
- \+ *lemma* conj_inj
- \+ *lemma* conj_eq_zero
- \+/\- *lemma* norm_sq_zero
- \+/\- *lemma* norm_sq_one
- \+ *lemma* norm_sq_I
- \+ *lemma* norm_sq_neg
- \+ *lemma* norm_sq_conj
- \+ *lemma* norm_sq_mul
- \+ *lemma* norm_sq_add
- \+ *lemma* re_sq_le_norm_sq
- \+ *lemma* im_sq_le_norm_sq
- \+ *lemma* norm_sq_sub
- \+ *lemma* conj_inv
- \+ *lemma* conj_div
- \+ *lemma* norm_sq_inv
- \+ *lemma* norm_sq_div
- \+ *lemma* abs_of_real
- \+ *lemma* abs_of_nonneg
- \+ *lemma* abs_zero
- \+ *lemma* abs_one
- \+ *lemma* abs_I
- \+ *lemma* abs_nonneg
- \+ *lemma* abs_abs
- \+ *lemma* abs_eq_zero
- \+ *lemma* abs_pos
- \+ *lemma* abs_neg
- \+ *lemma* abs_sub
- \+ *lemma* abs_conj
- \+ *lemma* abs_mul
- \+ *lemma* mul_self_abs
- \+ *lemma* abs_re_le_abs
- \+ *lemma* abs_im_le_abs
- \+ *lemma* re_le_abs
- \+ *lemma* im_le_abs
- \+ *lemma* abs_add
- \+ *lemma* abs_sub_le

Modified data/real.lean
- \+ *theorem* sqrt_mul_self_eq_abs
- \+ *theorem* sqrt_sqr_eq_abs



## [2018-01-21 23:57:42-05:00](https://github.com/leanprover-community/mathlib/commit/5a65212)
feat(data/real): real square root function, sqrt 2 is irrational
#### Estimated changes
Created algebra/char_zero.lean
- \+ *lemma* two_ne_zero'
- \+ *lemma* add_self_eq_zero
- \+ *lemma* bit0_eq_zero
- \+ *lemma* half_add_self
- \+ *lemma* add_halves'
- \+ *lemma* sub_half
- \+ *lemma* half_sub
- \+ *theorem* char_zero_of_inj_zero
- \+ *theorem* add_group.char_zero_of_inj_zero
- \+ *theorem* ordered_cancel_comm_monoid.char_zero_of_inj_zero
- \+ *theorem* cast_inj
- \+ *theorem* cast_injective
- \+ *theorem* cast_eq_zero
- \+ *theorem* cast_ne_zero

Modified algebra/field.lean
- \+ *lemma* div_eq_iff_mul_eq

Modified algebra/group_power.lean
- \+ *theorem* pow_two
- \+ *theorem* smul_two

Modified algebra/ordered_field.lean
- \+ *lemma* inv_lt_zero
- \+ *lemma* mul_self_inj_of_nonneg
- \+ *lemma* inv_pos'
- \+ *lemma* inv_neg'
- \+ *lemma* inv_nonneg
- \+ *lemma* inv_nonpos
- \+ *lemma* div_nonneg'

Modified algebra/ring.lean


Modified data/complex.lean
- \+ *lemma* of_real_bit0
- \+ *lemma* of_real_bit1
- \+ *lemma* eq_conj_iff_real
- \+ *lemma* of_real_div
- \+ *theorem* add_conj
- \+ *theorem* sub_conj
- \+ *theorem* re_eq_add_conj

Modified data/int/basic.lean


Modified data/nat/cast.lean
- \- *theorem* char_zero_of_inj_zero
- \- *theorem* add_group.char_zero_of_inj_zero
- \- *theorem* ordered_cancel_comm_monoid.char_zero_of_inj_zero
- \- *theorem* cast_inj
- \- *theorem* cast_injective
- \- *theorem* cast_eq_zero
- \- *theorem* cast_ne_zero

Modified data/nat/prime.lean
- \+ *theorem* prime.dvd_of_dvd_pow
- \- *theorem* dvd_of_prime_of_dvd_pow

Modified data/real.lean
- \+/\- *theorem* cauchy₂
- \+/\- *theorem* cauchy₃
- \+ *theorem* of_near
- \+ *theorem* mk_near_of_forall_near
- \+ *theorem* is_cau_seq_iff_lift
- \+ *theorem* sqrt_exists
- \+ *theorem* sqrt_aux_nonneg
- \+ *theorem* sqrt_aux_converges
- \+ *theorem* sqrt_prop
- \+ *theorem* sqrt_eq_zero_of_nonpos
- \+ *theorem* sqrt_nonneg
- \+ *theorem* mul_self_sqrt
- \+ *theorem* sqrt_mul_self
- \+ *theorem* sqrt_eq_iff_mul_self_eq
- \+ *theorem* sqr_sqrt
- \+ *theorem* sqrt_sqr
- \+ *theorem* sqrt_eq_iff_sqr_eq
- \+ *theorem* sqrt_zero
- \+ *theorem* sqrt_one
- \+ *theorem* sqrt_le
- \+ *theorem* sqrt_lt
- \+ *theorem* sqrt_inj
- \+ *theorem* sqrt_eq_zero
- \+ *theorem* sqrt_eq_zero'
- \+ *theorem* sqrt_pos
- \+ *theorem* sqrt_mul'
- \+ *theorem* sqrt_mul
- \+ *theorem* sqrt_inv
- \+ *theorem* sqrt_div
- \+ *theorem* sqrt_two_irrational
- \- *theorem* mk_of_near_fun
- \- *theorem* mk_of_near_equiv
- \+ *def* is_cau_seq
- \+/\- *def* cau_seq
- \+ *def* sqrt_aux
- \+ *def* irrational
- \- *def* mk_of_near



## [2018-01-20 21:28:43-05:00](https://github.com/leanprover-community/mathlib/commit/ffafdc6)
feat(tactic/ring): extend ring tactic to allow division by constants
#### Estimated changes
Modified tactic/ring.lean




## [2018-01-20 17:03:57-05:00](https://github.com/leanprover-community/mathlib/commit/bcbf0d5)
refactor(data/complex): clean up proofs
#### Estimated changes
Modified data/complex.lean
- \+/\- *lemma* of_real_eq_coe
- \+ *lemma* of_real_re
- \+ *lemma* of_real_im
- \+/\- *lemma* zero_re
- \+/\- *lemma* zero_im
- \+/\- *lemma* of_real_zero
- \+/\- *lemma* one_re
- \+/\- *lemma* one_im
- \+/\- *lemma* of_real_one
- \+/\- *lemma* I_re
- \+/\- *lemma* I_im
- \+/\- *lemma* add_re
- \+/\- *lemma* add_im
- \+/\- *lemma* of_real_add
- \+/\- *lemma* neg_re
- \+/\- *lemma* neg_im
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* mul_re
- \+/\- *lemma* mul_im
- \+/\- *lemma* of_real_mul
- \+ *lemma* mk_eq_add_mul_I
- \+/\- *lemma* conj_re
- \+/\- *lemma* conj_im
- \+ *lemma* conj_of_real
- \+ *lemma* norm_sq_of_real
- \+ *lemma* norm_sq_zero
- \+ *lemma* norm_sq_one
- \+ *lemma* norm_sq_nonneg
- \+ *lemma* norm_sq_eq_zero
- \+ *lemma* norm_sq_pos
- \+/\- *lemma* sub_re
- \+/\- *lemma* sub_im
- \+/\- *lemma* of_real_sub
- \+ *lemma* inv_re
- \+ *lemma* inv_im
- \+/\- *lemma* of_real_inv
- \+ *lemma* inv_zero
- \- *lemma* proj_re
- \- *lemma* proj_im
- \- *lemma* coe_re
- \- *lemma* coe_im
- \- *lemma* norm_squared_pos_of_nonzero
- \- *lemma* of_real_injective
- \- *lemma* of_real_abs_squared
- \+/\- *theorem* eta
- \+ *theorem* ext
- \+ *theorem* ext_iff
- \+ *theorem* of_real_inj
- \+ *theorem* of_real_eq_zero
- \+ *theorem* of_real_ne_zero
- \+ *theorem* mul_conj
- \+ *theorem* inv_def
- \+ *theorem* mul_inv_cancel
- \+ *theorem* of_real_int_cast
- \+ *theorem* of_real_nat_cast
- \+ *theorem* of_real_rat_cast
- \- *theorem* eq_of_re_eq_and_im_eq
- \- *theorem* eq_iff_re_eq_and_im_eq
- \- *theorem* im_eq_zero_of_complex_nat
- \- *theorem* of_real_nat_eq_complex_nat
- \- *theorem* of_real_int_eq_complex_int
- \- *theorem* of_real_rat_eq_complex_rat
- \+/\- *def* of_real
- \+/\- *def* I
- \+ *def* conj
- \+ *def* norm_sq
- \- *def* conjugate
- \- *def* norm_squared

Modified data/real.lean


Modified tactic/interactive.lean


Modified tactic/ring.lean




## [2018-01-19 17:05:43-05:00](https://github.com/leanprover-community/mathlib/commit/baa4b09)
feat(analysis/real): swap out the definition of real, shorten proofs
#### Estimated changes
Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/borel_space.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/metric_space.lean


Modified analysis/real.lean
- \+ *lemma* real.uniform_continuous_inv
- \+ *lemma* real.uniform_continuous_abs
- \+ *lemma* real.continuous_abs
- \+ *lemma* rat.uniform_continuous_abs
- \+ *lemma* rat.continuous_abs
- \+ *lemma* real.tendsto_inv
- \+ *lemma* real.continuous_inv'
- \+ *lemma* real.continuous_inv
- \+ *lemma* real.uniform_continuous_mul_const
- \+ *lemma* real.uniform_continuous_mul
- \+ *lemma* real.continuous_mul
- \+ *lemma* rat.continuous_mul
- \+ *lemma* real.totally_bounded_Ioo
- \+ *lemma* real.totally_bounded_ball
- \+ *lemma* real.totally_bounded_Ico
- \+ *lemma* real.totally_bounded_Icc
- \+ *lemma* rat.totally_bounded_Icc
- \+ *lemma* closure_of_rat_image_lt
- \+/\- *lemma* closure_of_rat_image_le_eq
- \+/\- *lemma* compact_ivl
- \- *lemma* mem_zero_nhd
- \- *lemma* mem_zero_nhd_le
- \- *lemma* mem_zero_nhd_iff
- \- *lemma* tendsto_zero_nhds
- \- *lemma* pure_zero_le_zero_nhd
- \- *lemma* tendsto_neg_rat_zero
- \- *lemma* tendsto_add_rat_zero
- \- *lemma* tendsto_add_rat_zero'
- \- *lemma* tendsto_sub_rat'
- \- *lemma* tendsto_mul_bnd_rat
- \- *lemma* tendsto_mul_bnd_rat'
- \- *lemma* tendsto_mul_rat'
- \- *lemma* uniformity_rat
- \- *lemma* mem_uniformity_rat
- \- *lemma* uniform_continuous_rat
- \- *lemma* tendsto_sub_uniformity_zero_nhd
- \- *lemma* tendsto_sub_uniformity_zero_nhd'
- \- *lemma* uniform_continuous_add_rat
- \- *lemma* uniform_continuous_neg_rat
- \- *lemma* nhds_eq_map_zero_nhd
- \- *lemma* nhds_0_eq_zero_nhd
- \- *lemma* uniform_continuous_inv_pos_rat
- \- *lemma* uniform_continuous_rat'
- \- *lemma* uniform_continuous_abs_rat
- \- *lemma* continuous_abs_rat
- \- *lemma* tendsto_inv_pos_rat
- \- *lemma* tendsto_inv_rat
- \- *lemma* uniform_continuous_mul_rat
- \- *lemma* totally_bounded_01_rat
- \- *lemma* of_rat_injective
- \- *lemma* of_rat_inj
- \- *lemma* uniform_embedding_of_rat
- \- *lemma* dense_embedding_of_rat
- \- *lemma* dense_embedding_of_rat_of_rat
- \- *lemma* lift_rat_fun_of_rat
- \- *lemma* lift_rat_op_of_rat_of_rat
- \- *lemma* of_rat_zero
- \- *lemma* of_rat_one
- \- *lemma* of_rat_neg
- \- *lemma* of_rat_add
- \- *lemma* of_rat_sub
- \- *lemma* of_rat_mul
- \- *lemma* of_rat_inv
- \- *lemma* uniform_continuous_neg_real
- \- *lemma* uniform_continuous_add_real
- \- *lemma* of_rat_mem_nonneg
- \- *lemma* of_rat_mem_nonneg_iff
- \- *lemma* of_rat_le
- \- *lemma* two_eq_of_rat_two
- \- *lemma* mem_nonneg_of_continuous2
- \- *lemma* zero_le_iff_nonneg
- \- *lemma* nonneg_antisymm
- \- *lemma* real.neg_preimage_closure
- \- *lemma* of_rat_lt
- \- *lemma* preimage_neg_rat
- \- *lemma* map_neg_real
- \- *lemma* map_neg_rat
- \- *lemma* abs_real_eq_abs
- \- *lemma* uniform_continuous_abs_real
- \- *lemma* continuous_abs_real
- \- *lemma* of_rat_abs
- \- *lemma* min_of_rat
- \- *lemma* max_of_rat
- \- *lemma* exists_pos_of_rat
- \- *lemma* mem_uniformity_real_iff
- \- *lemma* nhds_eq_real
- \- *lemma* exists_lt_of_rat
- \- *lemma* exists_gt_of_rat
- \- *lemma* continuous_mul_real
- \- *lemma* continuous_mul_real'
- \- *lemma* tendsto_inv_real
- \- *lemma* continuous_inv_real'
- \- *lemma* continuous_inv_real
- \- *lemma* exists_rat_btwn
- \- *lemma* exists_lt_rat
- \- *lemma* exists_rat_lt
- \- *lemma* exists_lt_nat
- \+ *theorem* rat.dist_eq
- \+ *theorem* uniform_continuous_of_rat
- \+ *theorem* uniform_embedding_of_rat
- \+ *theorem* dense_embedding_of_rat
- \+ *theorem* embedding_of_rat
- \+ *theorem* continuous_of_rat
- \+ *theorem* real.uniform_continuous_add
- \+ *theorem* rat.uniform_continuous_add
- \+ *theorem* real.uniform_continuous_neg
- \+ *theorem* rat.uniform_continuous_neg
- \+ *theorem* real.ball_eq_Ioo
- \+ *theorem* real.Ioo_eq_ball
- \+ *theorem* real.Cauchy_eq
- \- *theorem* real.le_def
- \- *theorem* coe_rat_eq_of_rat
- \- *def* zero_nhd
- \- *def* real
- \- *def* of_rat
- \- *def* lift_rat_fun
- \- *def* lift_rat_op
- \- *def* nonneg

Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* is_closed_le'
- \+/\- *lemma* is_closed_ge'

Renamed analysis/complex.lean to data/complex.lean




## [2018-01-19 16:18:40-05:00](https://github.com/leanprover-community/mathlib/commit/bb1a9f2)
feat(data/real,*): supporting material for metric spaces
#### Estimated changes
Modified algebra/functions.lean
- \+ *lemma* abs_sub_le_iff
- \+ *lemma* abs_sub_lt_iff
- \+ *lemma* abs_abs_sub_le_abs_sub
- \+ *def* sub_abs_le_abs_sub

Modified algebra/group.lean


Modified algebra/module.lean


Modified algebra/ordered_field.lean
- \+ *lemma* le_div_iff'
- \+ *lemma* div_le_iff'
- \+ *lemma* lt_div_iff'
- \+ *lemma* div_lt_iff'

Modified algebra/ordered_group.lean
- \+ *lemma* le_sub_iff_add_le'
- \+ *lemma* le_sub_iff_add_le
- \+ *lemma* sub_le_iff_le_add'
- \+ *lemma* sub_le_iff_le_add
- \+ *lemma* add_neg_le_iff_le_add
- \+ *lemma* add_neg_le_iff_le_add'
- \+ *lemma* neg_add_le_iff_le_add'
- \+ *lemma* neg_le_sub_iff_le_add'
- \+ *lemma* lt_sub_iff_add_lt'
- \+ *lemma* lt_sub_iff_add_lt
- \+ *lemma* sub_lt_iff_lt_add'
- \+ *lemma* sub_lt_iff_lt_add
- \+ *lemma* neg_lt_sub_iff_lt_add'
- \- *lemma* le_sub_left_iff_add_le
- \- *lemma* le_sub_right_iff_add_le
- \- *lemma* sub_left_le_iff_le_add
- \- *lemma* sub_right_le_iff_le_add
- \- *lemma* neg_add_le_iff_le_add_right
- \- *lemma* neg_le_sub_iff_le_add_left
- \- *lemma* lt_sub_left_iff_add_lt
- \- *lemma* lt_sub_right_iff_add_lt
- \- *lemma* sub_left_lt_iff_lt_add
- \- *lemma* sub_right_lt_iff_lt_add
- \- *lemma* neg_lt_sub_iff_lt_add_left

Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/metric_space.lean
- \+ *lemma* cauchy_of_metric
- \+ *theorem* uniformity_dist_of_mem_uniformity
- \+ *theorem* dist_eq_zero
- \+ *theorem* zero_eq_dist
- \+ *theorem* dist_triangle_left
- \+ *theorem* dist_triangle_right
- \+ *theorem* swap_dist
- \+ *theorem* abs_dist_sub_le
- \+ *theorem* dist_le_zero
- \+ *theorem* dist_pos
- \+ *theorem* mem_ball
- \+ *theorem* mem_ball'
- \+ *theorem* mem_closed_ball
- \+ *theorem* pos_of_mem_ball
- \+ *theorem* mem_ball_self
- \+ *theorem* mem_ball_comm
- \+ *theorem* ball_subset_ball
- \+ *theorem* ball_disjoint
- \+ *theorem* ball_disjoint_same
- \+ *theorem* ball_subset
- \+ *theorem* ball_half_subset
- \+ *theorem* exists_ball_subset_ball
- \+ *theorem* ball_eq_empty_iff_nonpos
- \+/\- *theorem* uniformity_dist
- \+/\- *theorem* uniformity_dist'
- \+/\- *theorem* mem_uniformity_dist
- \+ *theorem* dist_mem_uniformity
- \+ *theorem* uniform_continuous_of_metric
- \+ *theorem* uniform_embedding_of_metric
- \+ *theorem* totally_bounded_of_metric
- \+/\- *theorem* nhds_eq_metric
- \+ *theorem* mem_nhds_iff_metric
- \+/\- *theorem* is_open_metric
- \+ *theorem* is_open_ball
- \+ *theorem* ball_mem_nhds
- \+ *theorem* tendsto_nhds_of_metric
- \+ *theorem* continuous_of_metric
- \+/\- *theorem* eq_of_forall_dist_le
- \+ *theorem* real.dist_eq
- \+ *theorem* metric_space.induced_uniform_embedding
- \+ *theorem* subtype.dist_eq
- \+/\- *theorem* uniform_continuous_dist'
- \+/\- *theorem* uniform_continuous_dist
- \+/\- *theorem* continuous_dist'
- \+/\- *theorem* continuous_dist
- \+/\- *theorem* tendsto_dist
- \+ *theorem* is_closed_ball
- \- *theorem* dist_eq_zero_iff
- \- *theorem* zero_eq_dist_iff
- \- *theorem* dist_pos_of_ne
- \- *theorem* dist_le_zero_iff
- \- *theorem* ne_of_dist_pos
- \- *theorem* open_ball_eq_empty_of_nonpos
- \- *theorem* pos_of_mem_open_ball
- \- *theorem* mem_open_ball
- \- *theorem* is_open_open_ball
- \- *theorem* is_closed_closed_ball
- \- *theorem* open_ball_subset_open_ball_of_le
- \- *theorem* mem_nhds_sets_iff_metric
- \+ *def* ball
- \+/\- *def* closed_ball
- \+ *def* metric_space.replace_uniformity
- \+ *def* metric_space.induced
- \- *def* open_ball

Modified analysis/real.lean
- \+ *lemma* real.neg_preimage_closure
- \- *lemma* tendsto_of_uniform_continuous_subtype
- \- *lemma* preimage_neg_real
- \- *lemma* neg_preimage_closure

Modified analysis/topology/continuity.lean
- \+ *lemma* continuous.comp
- \+ *lemma* continuous.tendsto
- \+ *lemma* continuous_iff_le_coinduced
- \+ *lemma* continuous_le_dom
- \+ *lemma* continuous_le_rng
- \+/\- *lemma* continuous_inf_rng_left
- \+/\- *lemma* continuous_inf_rng_right
- \+/\- *lemma* continuous_sup_dom_left
- \+/\- *lemma* continuous_sup_dom_right
- \+ *lemma* continuous.prod_mk
- \+/\- *lemma* is_open_prod
- \+ *lemma* embedding.tendsto_nhds_iff
- \+ *lemma* embedding.continuous_iff
- \+/\- *lemma* inj_iff
- \+ *lemma* closure_range
- \- *lemma* continuous_compose
- \- *lemma* continuous_eq_le_coinduced
- \- *lemma* continuous_prod_mk
- \- *lemma* tendsto_nhds_iff_of_embedding
- \- *lemma* continuous_iff_of_embedding
- \- *lemma* closure_image_univ
- \+ *theorem* dense_embedding.mk'

Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean
- \+ *theorem* mem_closure_iff
- \+ *theorem* mem_closure_iff_nhds

Modified analysis/topology/topological_structures.lean
- \+ *lemma* preimage_neg
- \+ *lemma* filter.map_neg
- \+ *lemma* neg_preimage_closure
- \+ *theorem* uniform_add_group.mk'
- \+ *theorem* induced_orderable_topology'
- \+ *theorem* induced_orderable_topology

Modified analysis/topology/uniform_space.lean
- \+/\- *lemma* mem_nhds_left
- \+/\- *lemma* mem_nhds_right
- \+ *lemma* uniform_continuous.comp
- \+ *lemma* uniform_embedding.uniform_continuous
- \+ *lemma* uniform_embedding.uniform_continuous_iff
- \+ *lemma* uniform_embedding.dense_embedding
- \+ *lemma* uniform_continuous.continuous
- \+ *lemma* totally_bounded_preimage
- \+/\- *lemma* pure_cauchy_dense
- \+ *lemma* tendsto_of_uniform_continuous_subtype
- \+ *lemma* uniform_continuous.prod_mk
- \+ *lemma* uniform_embedding.prod
- \- *lemma* uniform_continuous_compose
- \- *lemma* uniform_continuous_of_embedding
- \- *lemma* dense_embedding_of_uniform_embedding
- \- *lemma* continuous_of_uniform
- \- *lemma* uniform_continuous_prod_mk
- \- *lemma* uniform_embedding_prod
- \+ *theorem* mem_id_rel
- \+ *theorem* id_rel_subset
- \+ *theorem* mem_comp_rel
- \+ *theorem* uniform_continuous_def
- \+ *theorem* uniform_embedding_def
- \+ *theorem* uniform_embedding_def'
- \+ *theorem* separated_def
- \+ *theorem* separated_def'
- \+ *theorem* totally_bounded_iff_subset
- \+ *theorem* le_nhds_lim_of_cauchy
- \+ *theorem* mem_uniformity
- \+ *theorem* mem_uniformity'
- \+ *def* uniform_space.core.mk'
- \+ *def* uniform_continuous
- \+ *def* uniform_embedding
- \+ *def* separated

Modified data/analysis/filter.lean


Modified data/equiv.lean


Modified data/fp/basic.lean


Modified data/hash_map.lean


Modified data/int/basic.lean
- \+ *theorem* cast_injective

Modified data/list/basic.lean


Modified data/list/perm.lean


Modified data/nat/cast.lean
- \+ *theorem* cast_injective

Modified data/rat.lean
- \+ *theorem* cast_injective

Modified data/real.lean
- \+ *theorem* rat_add_continuous_lemma
- \+ *theorem* rat_mul_continuous_lemma
- \+ *theorem* rat_inv_continuous_lemma
- \+/\- *theorem* ext
- \+/\- *theorem* cauchy
- \+/\- *theorem* cauchy₂
- \+/\- *theorem* cauchy₃
- \+/\- *theorem* bounded
- \+/\- *theorem* bounded'
- \+/\- *theorem* add_apply
- \+/\- *theorem* mul_apply
- \+ *theorem* const_apply
- \+ *theorem* const_inj
- \+/\- *theorem* zero_apply
- \+/\- *theorem* one_apply
- \+ *theorem* const_add
- \+ *theorem* const_mul
- \+/\- *theorem* neg_apply
- \+ *theorem* const_neg
- \+ *theorem* const_sub
- \+/\- *theorem* sub_apply
- \+/\- *theorem* add_lim_zero
- \+/\- *theorem* mul_lim_zero
- \+/\- *theorem* neg_lim_zero
- \+/\- *theorem* sub_lim_zero
- \+/\- *theorem* zero_lim_zero
- \+ *theorem* const_lim_zero
- \+ *theorem* equiv_def₃
- \+/\- *theorem* lim_zero_congr
- \+/\- *theorem* abs_pos_of_not_lim_zero
- \+/\- *theorem* inv_aux
- \+/\- *theorem* inv_apply
- \+/\- *theorem* inv_mul_cancel
- \+/\- *theorem* not_lim_zero_of_pos
- \+ *theorem* const_pos
- \+/\- *theorem* add_pos
- \+/\- *theorem* pos_add_lim_zero
- \+/\- *theorem* mul_pos
- \+/\- *theorem* trichotomy
- \+/\- *theorem* lt_of_lt_of_eq
- \+/\- *theorem* lt_of_eq_of_lt
- \+/\- *theorem* lt_trans
- \+/\- *theorem* lt_irrefl
- \+/\- *theorem* le_antisymm
- \+ *theorem* lt_total
- \+/\- *theorem* le_total
- \+ *theorem* const_lt
- \+ *theorem* const_equiv
- \+ *theorem* const_le
- \+ *theorem* exists_gt
- \+ *theorem* exists_lt
- \+ *theorem* mk_of_near_fun
- \+ *theorem* mk_of_near_equiv
- \+/\- *theorem* mk_add
- \+/\- *theorem* mk_neg
- \+/\- *theorem* mk_mul
- \+/\- *theorem* mk_lt
- \+/\- *theorem* mk_pos
- \+/\- *theorem* mk_le
- \+/\- *theorem* of_rat_lt
- \+/\- *theorem* le_mk_of_forall_le
- \+/\- *theorem* mk_le_of_forall_le
- \+ *theorem* floor_nonneg
- \+ *theorem* lt_Sup
- \+ *theorem* Inf_lt
- \+ *theorem* cau_seq_converges
- \+ *theorem* equiv_lim
- \- *theorem* of_rat_apply
- \- *theorem* of_rat_add
- \- *theorem* of_rat_mul
- \- *theorem* of_rat_neg
- \- *theorem* of_rat_sub
- \- *theorem* of_rat_lim_zero
- \- *theorem* of_rat_pos
- \+/\- *def* cau_seq
- \+/\- *def* of_eq
- \+ *def* const
- \+/\- *def* lim_zero
- \+/\- *def* inv
- \+/\- *def* pos
- \+ *def* mk_of_near
- \+/\- *def* real
- \+/\- *def* mk
- \+/\- *def* of_rat

Modified data/set/basic.lean
- \+/\- *theorem* preimage_image_eq
- \+/\- *theorem* mem_range
- \+ *theorem* image_univ
- \+ *theorem* range_comp
- \+ *theorem* range_subset_iff
- \+ *theorem* image_preimage_eq_inter_range
- \+ *theorem* quot_mk_range_eq
- \+ *theorem* prod_range_range_eq
- \- *theorem* image_preimage_eq_inter_rng
- \- *theorem* quot_mk_image_univ_eq
- \- *theorem* range_eq_image
- \- *theorem* range_compose

Modified data/set/finite.lean
- \+ *theorem* finite_preimage

Modified data/set/lattice.lean
- \+ *lemma* subtype_val_range
- \+ *theorem* bUnion_subset_bUnion_left
- \+ *theorem* bInter_subset_bInter_left
- \+/\- *theorem* Union_eq_sUnion_image
- \+/\- *theorem* Inter_eq_sInter_image

Modified logic/basic.lean
- \- *theorem* forall_of_forall
- \- *theorem* exists_of_exists
- \+ *def* Exists.imp

Modified logic/function.lean
- \+ *lemma* injective_iff_has_left_inverse
- \+ *lemma* left_inverse_surj_inv
- \+ *lemma* surjective_iff_has_right_inverse
- \+ *lemma* bijective_iff_has_inverse

Modified order/filter.lean
- \+ *lemma* filter_eq_iff
- \+ *lemma* filter.ext
- \+/\- *lemma* mem_principal_sets
- \+ *lemma* mem_principal_self
- \+ *lemma* mem_Sup_sets
- \+ *lemma* mem_supr_sets
- \+/\- *lemma* mem_map
- \+/\- *lemma* monotone_map
- \+/\- *lemma* monotone_vmap
- \+/\- *lemma* mem_bind_sets
- \+ *lemma* mem_pure_sets
- \+/\- *lemma* mem_return_sets
- \+ *lemma* pure_neq_bot
- \+ *lemma* tendsto_def
- \+ *lemma* tendsto_iff_vmap
- \+ *lemma* tendsto.comp
- \+ *lemma* tendsto_le_left
- \+ *lemma* tendsto_le_right
- \+/\- *lemma* tendsto_inf
- \+/\- *lemma* tendsto_infi
- \+/\- *lemma* tendsto_infi'
- \+/\- *lemma* tendsto_principal
- \+/\- *lemma* tendsto_principal_principal
- \+ *lemma* mem_lift_sets
- \+ *lemma* mem_lift'_sets
- \+ *lemma* mem_prod_sets
- \+ *lemma* tendsto.prod_mk
- \+ *lemma* mem_at_top_sets
- \- *lemma* return_neq_bot
- \- *lemma* tendsto_compose
- \- *lemma* tendsto_inf_left
- \- *lemma* mem_lift_iff
- \- *lemma* mem_lift'_iff
- \- *lemma* mem_prod_iff
- \- *lemma* tendsto_prod_mk
- \- *lemma* mem_at_top_iff
- \+ *theorem* le_def
- \+ *theorem* mem_vmap_sets
- \- *theorem* mem_vmap

Modified order/galois_connection.lean




## [2018-01-17 17:53:52-05:00](https://github.com/leanprover-community/mathlib/commit/0ac694c)
fix(tactic/interactive): update to lean
#### Estimated changes
Modified tactic/interactive.lean




## [2018-01-16 16:08:50-05:00](https://github.com/leanprover-community/mathlib/commit/e11da6e)
feat(data/real): variants on archimedean property
#### Estimated changes
Modified data/real.lean
- \+ *theorem* exists_rat_gt
- \+ *theorem* exists_nat_gt
- \+ *theorem* exists_int_gt
- \+ *theorem* exists_int_lt
- \+ *theorem* exists_rat_lt
- \- *theorem* archimedean



## [2018-01-16 05:29:44-05:00](https://github.com/leanprover-community/mathlib/commit/d84dfb1)
feat(data/real): completeness of the (new) real numbers
#### Estimated changes
Modified algebra/group.lean
- \- *theorem* le_sub_iff_add_le
- \- *theorem* sub_le_iff_le_add

Modified algebra/ordered_field.lean
- \+/\- *lemma* inv_pos
- \+/\- *lemma* inv_le_inv
- \+ *lemma* inv_le
- \+ *lemma* le_inv
- \+ *lemma* inv_lt
- \+ *lemma* lt_inv
- \+ *lemma* inv_le_inv_of_le
- \- *lemma* inv_le_inv'
- \+/\- *def* div_pos

Modified algebra/ordered_group.lean
- \+/\- *lemma* le_neg_add_iff_add_le
- \+/\- *lemma* le_sub_right_iff_add_le
- \+/\- *lemma* sub_right_le_iff_le_add
- \+/\- *lemma* lt_sub_right_iff_add_lt
- \+/\- *lemma* sub_right_lt_iff_lt_add
- \+ *theorem* le_sub

Modified algebra/ordered_ring.lean
- \+ *lemma* sub_one_lt

Modified analysis/ennreal.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measurable_space.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/metric_space.lean


Modified analysis/real.lean


Modified analysis/topology/topological_structures.lean


Modified data/int/basic.lean
- \+/\- *theorem* nat_succ_eq_int_succ
- \+/\- *theorem* pred_succ
- \+/\- *theorem* succ_pred
- \+/\- *theorem* neg_succ
- \+/\- *theorem* succ_neg_succ
- \+/\- *theorem* neg_pred
- \+/\- *theorem* pred_neg_pred
- \+/\- *theorem* pred_nat_succ
- \+/\- *theorem* neg_nat_succ
- \+/\- *theorem* succ_neg_nat_succ
- \+/\- *theorem* lt_succ_self
- \+/\- *theorem* pred_self_lt
- \+ *theorem* add_one_le_iff
- \+ *theorem* lt_add_one_iff
- \+ *theorem* sub_one_le_iff
- \+ *theorem* le_sub_one_iff
- \+/\- *theorem* of_nat_add_neg_succ_of_nat_of_lt
- \+/\- *theorem* of_nat_add_neg_succ_of_nat_of_ge
- \+ *theorem* exists_least_of_bdd
- \+ *theorem* exists_greatest_of_bdd
- \+/\- *def* succ
- \+/\- *def* pred

Modified data/int/order.lean
- \- *theorem* exists_least_of_bdd
- \- *theorem* exists_greatest_of_bdd

Modified data/pnat.lean
- \+ *theorem* coe_nat_coe

Modified data/rat.lean
- \+/\- *def* ceil

Modified data/real.lean
- \+ *theorem* le_mk_of_forall_le
- \+ *theorem* mk_le_of_forall_le
- \+ *theorem* exists_floor
- \+ *theorem* le_floor
- \+ *theorem* floor_lt
- \+ *theorem* floor_le
- \+ *theorem* lt_succ_floor
- \+ *theorem* lt_floor_add_one
- \+ *theorem* sub_one_lt_floor
- \+ *theorem* floor_coe
- \+ *theorem* floor_mono
- \+ *theorem* floor_add_int
- \+ *theorem* floor_sub_int
- \+ *theorem* ceil_le
- \+ *theorem* lt_ceil
- \+ *theorem* le_ceil
- \+ *theorem* ceil_coe
- \+ *theorem* ceil_mono
- \+ *theorem* ceil_add_int
- \+ *theorem* ceil_sub_int
- \+ *theorem* ceil_lt_add_one
- \+ *theorem* exists_sup
- \+ *theorem* Sup_le
- \+ *theorem* le_Sup
- \+ *theorem* Sup_le_ub
- \+ *theorem* le_Inf
- \+ *theorem* Inf_le
- \+ *theorem* lb_le_Inf



## [2018-01-15 07:59:59-05:00](https://github.com/leanprover-community/mathlib/commit/04cac95)
feat(data/real): reals from first principles
This is beginning work on a simpler implementation of real numbers, based on Cauchy sequences, to help alleviate some of the issues we have seen with loading times and timeouts when working with real numbers. If everything goes according to plan, `analysis/real.lean` will be the development for the topology of the reals, but the initial construction will have no topology prerequisites.
#### Estimated changes
Modified algebra/functions.lean
- \+ *lemma* abs_pos_iff

Created algebra/linear_algebra/dimension.lean
- \+ *theorem* mk_basis
- \+ *def* dim

Modified algebra/linear_algebra/linear_map_module.lean


Modified analysis/ennreal.lean


Modified analysis/real.lean


Modified data/bool.lean
- \+ *lemma* of_to_bool_iff

Modified data/int/basic.lean
- \+ *theorem* eq_cast
- \+/\- *theorem* cast_id

Modified data/nat/basic.lean


Modified data/nat/cast.lean
- \+ *theorem* eq_cast
- \+ *theorem* eq_cast'
- \+/\- *theorem* cast_id

Modified data/rat.lean
- \+ *theorem* eq_cast_of_ne_zero
- \+ *theorem* eq_cast

Created data/real.lean
- \+ *theorem* exists_forall_ge_and
- \+ *theorem* ext
- \+ *theorem* cauchy
- \+ *theorem* cauchy₂
- \+ *theorem* cauchy₃
- \+ *theorem* bounded
- \+ *theorem* bounded'
- \+ *theorem* add_apply
- \+ *theorem* mul_apply
- \+ *theorem* of_rat_apply
- \+ *theorem* zero_apply
- \+ *theorem* one_apply
- \+ *theorem* of_rat_add
- \+ *theorem* of_rat_mul
- \+ *theorem* neg_apply
- \+ *theorem* of_rat_neg
- \+ *theorem* of_rat_sub
- \+ *theorem* sub_apply
- \+ *theorem* add_lim_zero
- \+ *theorem* mul_lim_zero
- \+ *theorem* neg_lim_zero
- \+ *theorem* sub_lim_zero
- \+ *theorem* zero_lim_zero
- \+ *theorem* of_rat_lim_zero
- \+ *theorem* lim_zero_congr
- \+ *theorem* abs_pos_of_not_lim_zero
- \+ *theorem* inv_aux
- \+ *theorem* inv_apply
- \+ *theorem* inv_mul_cancel
- \+ *theorem* not_lim_zero_of_pos
- \+ *theorem* of_rat_pos
- \+ *theorem* add_pos
- \+ *theorem* pos_add_lim_zero
- \+ *theorem* mul_pos
- \+ *theorem* trichotomy
- \+ *theorem* lt_of_lt_of_eq
- \+ *theorem* lt_of_eq_of_lt
- \+ *theorem* lt_trans
- \+ *theorem* lt_irrefl
- \+ *theorem* le_antisymm
- \+ *theorem* le_total
- \+ *theorem* mk_eq_mk
- \+ *theorem* mk_eq
- \+ *theorem* of_rat_zero
- \+ *theorem* of_rat_one
- \+ *theorem* mk_eq_zero
- \+ *theorem* mk_add
- \+ *theorem* mk_neg
- \+ *theorem* mk_mul
- \+ *theorem* mk_lt
- \+ *theorem* mk_pos
- \+ *theorem* mk_le
- \+ *theorem* add_lt_add_iff_left
- \+ *theorem* of_rat_lt
- \+ *theorem* inv_zero
- \+ *theorem* inv_mk
- \+ *theorem* of_rat_eq_cast
- \+ *theorem* archimedean
- \+ *theorem* exists_pos_rat_lt
- \+ *theorem* exists_rat_near'
- \+ *theorem* exists_rat_near
- \+ *theorem* exists_rat_btwn
- \+ *def* cau_seq
- \+ *def* of_eq
- \+ *def* of_rat
- \+ *def* lim_zero
- \+ *def* inv
- \+ *def* pos
- \+ *def* real
- \+ *def* mk

Modified pending/default.lean
- \- *lemma* of_to_bool_iff

Modified tactic/alias.lean




## [2018-01-14 21:59:50-05:00](https://github.com/leanprover-community/mathlib/commit/65db966)
feat(algebra/field): more division lemmas
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* single_le_sum

Modified algebra/field.lean
- \+ *lemma* div_eq_mul_inv
- \+ *lemma* inv_div
- \+ *lemma* inv_div_left
- \+ *lemma* neg_inv
- \+/\- *lemma* division_ring.inv_comm_of_comm
- \+ *lemma* div_ne_zero
- \+ *lemma* div_ne_zero_iff
- \+ *lemma* div_eq_zero_iff
- \+ *lemma* add_div
- \+ *lemma* div_right_inj
- \+ *lemma* sub_div
- \+ *lemma* division_ring.inv_inj
- \+ *lemma* division_ring.inv_eq_iff
- \+ *lemma* div_neg
- \+/\- *lemma* div_eq_inv_mul
- \+ *lemma* inv_add_inv
- \+ *lemma* inv_sub_inv
- \+ *lemma* mul_div_right_comm
- \+ *lemma* mul_comm_div
- \+ *lemma* div_mul_comm
- \+ *lemma* mul_div_comm
- \+ *lemma* field.div_right_comm
- \+ *lemma* field.div_div_div_cancel_right
- \+ *lemma* field.div_mul_div_cancel
- \+ *lemma* div_eq_div_iff
- \+ *lemma* field.div_div_cancel
- \+/\- *lemma* inv_sub_inv_eq
- \+ *lemma* div_right_comm
- \+ *lemma* div_div_div_cancel_right
- \+ *lemma* div_mul_div_cancel
- \+ *lemma* div_div_cancel
- \- *lemma* division_ring.inv_div
- \- *lemma* division_ring.neg_inv
- \- *lemma* le_div_iff_mul_le_of_pos
- \- *lemma* div_le_iff_le_mul_of_pos
- \- *lemma* lt_div_iff
- \- *lemma* ivl_translate
- \- *lemma* ivl_stretch
- \- *lemma* inv_pos
- \- *lemma* inv_lt_one
- \- *lemma* one_lt_inv
- \- *lemma* abs_inv
- \- *lemma* inv_neg
- \- *lemma* inv_le_inv
- \+ *theorem* ne_zero
- \+ *theorem* inv_eq_inv
- \+ *theorem* mk0_val
- \+ *theorem* mk0_inv
- \+ *theorem* divp_eq_div
- \+ *theorem* divp_mk0
- \+ *def* mk0

Modified algebra/functions.lean
- \+ *def* abs_add

Modified algebra/group.lean
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_right_inj

Modified algebra/group_power.lean


Modified algebra/linear_algebra/basic.lean
- \- *lemma* is_submodule_span

Modified algebra/module.lean


Modified algebra/order.lean
- \+ *lemma* exists_ge_of_linear

Created algebra/ordered_field.lean
- \+ *lemma* one_le_div_iff_le
- \+ *lemma* one_lt_div_iff_lt
- \+ *lemma* div_le_one_iff_le
- \+ *lemma* div_lt_one_iff_lt
- \+ *lemma* le_div_iff
- \+ *lemma* div_le_iff
- \+ *lemma* lt_div_iff
- \+ *lemma* div_le_iff_of_neg
- \+ *lemma* div_lt_iff
- \+ *lemma* div_lt_iff_of_neg
- \+ *lemma* inv_le_inv'
- \+ *lemma* one_div_le_one_div
- \+ *lemma* inv_lt_inv
- \+ *lemma* one_div_lt_one_div
- \+ *lemma* div_lt_div_right
- \+ *lemma* div_le_div_right
- \+ *lemma* div_lt_div_right_of_neg
- \+ *lemma* div_le_div_right_of_neg
- \+ *lemma* div_lt_div_left
- \+ *lemma* div_le_div_left
- \+ *lemma* div_lt_div_iff
- \+ *lemma* div_lt_div
- \+ *lemma* div_lt_div'
- \+ *lemma* half_pos
- \+ *lemma* ivl_translate
- \+ *lemma* ivl_stretch
- \+ *lemma* inv_pos
- \+ *lemma* inv_lt_one
- \+ *lemma* one_lt_inv
- \+ *lemma* abs_inv
- \+ *lemma* inv_neg
- \+ *lemma* inv_le_inv
- \+ *def* div_pos
- \+ *def* div_nonneg
- \+ *def* half_lt_self

Modified algebra/ordered_group.lean


Modified algebra/ordered_ring.lean
- \+ *lemma* lt_add_one
- \+/\- *lemma* one_lt_two

Modified algebra/ring.lean
- \- *lemma* add_div
- \- *lemma* div_eq_mul_inv
- \- *lemma* neg_inv



## [2018-01-14 17:36:13-05:00](https://github.com/leanprover-community/mathlib/commit/0d6d12a)
feat(tactic/interactive): replace tactic
#### Estimated changes
Modified tactic/interactive.lean




## [2018-01-14 01:53:04-05:00](https://github.com/leanprover-community/mathlib/commit/edde6f5)
feat(tactic/ring): use `ring` for rewriting into pretty print format
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/ring.lean
- \+ *theorem* horner_def'
- \+ *theorem* mul_assoc_rev
- \+ *theorem* pow_add_rev
- \+ *theorem* pow_add_rev_right
- \+ *theorem* add_neg_eq_sub



## [2018-01-13 19:43:41-05:00](https://github.com/leanprover-community/mathlib/commit/c75b072)
fix(*): update to lean
#### Estimated changes
Modified data/array/lemmas.lean


Modified data/list/basic.lean


Modified data/list/perm.lean


Modified data/option.lean
- \+/\- *lemma* some_inj
- \- *lemma* none_ne_some

Modified data/rat.lean


Modified data/seq/wseq.lean


Modified set_theory/ordinal_notation.lean


Modified tactic/converter/binders.lean




## [2018-01-13 10:22:46-05:00](https://github.com/leanprover-community/mathlib/commit/df7175f)
fix(tactic/ring): bugfix
#### Estimated changes
Modified tactic/ring.lean




## [2018-01-13 04:32:47-05:00](https://github.com/leanprover-community/mathlib/commit/341fd51)
fix(tactic/ring): bugfix
#### Estimated changes
Modified tactic/ring.lean
- \+/\- *theorem* zero_horner
- \+/\- *theorem* horner_horner
- \+/\- *theorem* horner_add_horner_eq



## [2018-01-13 03:25:35-05:00](https://github.com/leanprover-community/mathlib/commit/2e2d89b)
feat(tactic/ring): tactic for ring equality
#### Estimated changes
Modified algebra/group_power.lean
- \+/\- *theorem* pow_one
- \+/\- *theorem* add_monoid.smul_one

Modified data/pnat.lean
- \+/\- *def* to_pnat

Created tactic/basic.lean


Modified tactic/interactive.lean


Modified tactic/norm_num.lean


Created tactic/ring.lean
- \+ *lemma* subst_into_neg
- \+ *lemma* subst_into_pow
- \+ *theorem* const_add_horner
- \+ *theorem* horner_add_const
- \+ *theorem* horner_add_horner_lt
- \+ *theorem* horner_add_horner_gt
- \+ *theorem* horner_add_horner_eq
- \+ *theorem* horner_neg
- \+ *theorem* horner_const_mul
- \+ *theorem* horner_mul_const
- \+ *theorem* zero_horner
- \+ *theorem* horner_horner
- \+ *theorem* horner_mul_horner_zero
- \+ *theorem* horner_mul_horner
- \+ *theorem* horner_pow
- \+ *theorem* horner_atom
- \+ *def* horner



## [2018-01-12 13:08:48-05:00](https://github.com/leanprover-community/mathlib/commit/c39b43f)
feat(analysis/metric_space): sup metric for product of metric spaces
#### Estimated changes
Modified algebra/linear_algebra/multivariate_polynomial.lean


Modified analysis/metric_space.lean
- \+ *theorem* dist_le_zero_iff

Modified analysis/topology/topological_space.lean


Modified analysis/topology/uniform_space.lean
- \+ *theorem* prod_uniformity

Modified data/equiv.lean


Modified data/prod.lean
- \+/\- *lemma* mk.eta
- \+ *lemma* ext

Modified order/complete_lattice.lean
- \+/\- *theorem* infi_inf_eq



## [2018-01-11 23:22:32-05:00](https://github.com/leanprover-community/mathlib/commit/1dddcf6)
doc(*): blurbs galore
Document all `def`, `class`, and `inductive` that are reasonably public-facing
#### Estimated changes
Modified algebra/big_operators.lean


Modified algebra/group.lean


Modified algebra/group_power.lean


Modified algebra/linear_algebra/basic.lean


Modified algebra/linear_algebra/linear_map_module.lean


Modified algebra/linear_algebra/multivariate_polynomial.lean


Modified algebra/linear_algebra/quotient_module.lean


Modified algebra/module.lean


Modified algebra/order.lean


Modified algebra/ordered_group.lean


Modified algebra/ordered_ring.lean


Modified algebra/ring.lean


Modified analysis/ennreal.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measurable_space.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/metric_space.lean


Modified analysis/topology/continuity.lean
- \+/\- *theorem* is_open_induced
- \+/\- *def* continuous

Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean
- \+/\- *lemma* tendsto_nhds

Modified analysis/topology/topological_structures.lean


Modified analysis/topology/uniform_space.lean
- \+ *def* cauchy

Modified data/analysis/filter.lean


Modified data/analysis/topology.lean


Modified data/encodable.lean


Modified data/equiv.lean


Modified data/fin.lean


Modified data/finset.lean


Modified data/finsupp.lean
- \+/\- *lemma* one_def
- \+/\- *lemma* comap_domain_apply
- \+/\- *lemma* comap_domain_zero
- \+/\- *lemma* smul_apply

Modified data/fintype.lean


Modified data/fp/basic.lean


Modified data/hash_map.lean
- \+/\- *def* write
- \+/\- *def* modify
- \+/\- *def* of_list

Modified data/int/basic.lean


Modified data/list/basic.lean


Modified data/list/perm.lean


Modified data/list/sort.lean


Modified data/multiset.lean


Modified data/nat/basic.lean


Modified data/nat/cast.lean


Modified data/nat/dist.lean


Modified data/nat/gcd.lean


Modified data/nat/modeq.lean


Modified data/nat/pairing.lean


Modified data/nat/prime.lean


Modified data/nat/sqrt.lean


Modified data/num/basic.lean


Modified data/option.lean


Modified data/pfun.lean


Modified data/pnat.lean


Modified data/prod.lean
- \+/\- *lemma* swap_swap
- \+/\- *lemma* fst_swap
- \+/\- *lemma* snd_swap
- \+/\- *def* swap

Modified data/quot.lean


Modified data/rat.lean


Modified data/seq/computation.lean
- \+ *theorem* get_mem
- \+ *theorem* get_eq_of_mem
- \+ *theorem* mem_of_get_eq
- \+ *theorem* get_promises
- \+ *theorem* mem_of_promises
- \+ *theorem* get_eq_of_promises
- \+ *theorem* results_of_terminates
- \+ *theorem* results_of_terminates'
- \+ *theorem* results.mem
- \+ *theorem* results.terminates
- \+ *theorem* results.length
- \+ *theorem* results.val_unique
- \+ *theorem* results.len_unique
- \+ *theorem* exists_results_of_mem
- \+ *theorem* eq_thinkN
- \+ *theorem* eq_thinkN'
- \+/\- *theorem* ret_orelse
- \+/\- *theorem* orelse_ret
- \+/\- *theorem* orelse_think
- \+/\- *theorem* terminates_congr
- \+/\- *theorem* promises_congr
- \+/\- *theorem* get_equiv
- \+/\- *theorem* lift_eq_iff_equiv
- \+ *theorem* lift_rel.refl
- \+ *theorem* lift_rel.symm
- \+ *theorem* lift_rel.trans
- \+ *theorem* lift_rel.equiv
- \+ *theorem* lift_rel.imp
- \+ *theorem* terminates_of_lift_rel
- \+ *theorem* rel_of_lift_rel
- \+/\- *def* destruct
- \+/\- *def* orelse
- \+/\- *def* equiv
- \- *def* get_mem
- \- *def* get_eq_of_mem
- \- *def* mem_of_get_eq
- \- *def* get_promises
- \- *def* mem_of_promises
- \- *def* get_eq_of_promises
- \- *def* results_of_terminates
- \- *def* results_of_terminates'
- \- *def* results.mem
- \- *def* results.terminates
- \- *def* results.length
- \- *def* results.val_unique
- \- *def* results.len_unique
- \- *def* exists_results_of_mem
- \- *def* eq_thinkN
- \- *def* eq_thinkN'
- \- *def* lift_rel.refl
- \- *def* lift_rel.symm
- \- *def* lift_rel.trans
- \- *def* lift_rel.equiv
- \- *def* lift_rel.imp
- \- *def* terminates_of_lift_rel
- \- *def* rel_of_lift_rel

Modified data/seq/parallel.lean


Modified data/seq/seq.lean
- \+ *theorem* corec_eq
- \+ *theorem* of_list_nil
- \+ *theorem* of_list_cons
- \+ *theorem* of_stream_cons
- \+ *theorem* of_list_append
- \+ *theorem* of_stream_append
- \+ *theorem* of_mem_append
- \+ *theorem* mem_append_left
- \+/\- *def* omap
- \- *def* corec_eq
- \- *def* of_list_nil
- \- *def* of_list_cons
- \- *def* of_stream_cons
- \- *def* of_list_append
- \- *def* of_stream_append
- \- *def* of_mem_append
- \- *def* mem_append_left

Modified data/seq/wseq.lean
- \+ *theorem* lift_rel.refl
- \+ *theorem* lift_rel_o.swap
- \+ *theorem* lift_rel.swap_lem
- \+ *theorem* lift_rel.swap
- \+ *theorem* lift_rel.symm
- \+ *theorem* lift_rel.trans
- \+ *theorem* lift_rel.equiv
- \+ *theorem* join_nil
- \+ *theorem* join_think
- \+ *theorem* join_cons
- \+ *theorem* drop.aux_none
- \+ *theorem* of_mem_append
- \+ *theorem* mem_append_left
- \+ *theorem* lift_rel_nil
- \+ *theorem* lift_rel_cons
- \+ *theorem* lift_rel_think_left
- \+ *theorem* lift_rel_think_right
- \+ *theorem* of_list_nil
- \+ *theorem* of_list_cons
- \+ *theorem* to_list'_nil
- \+ *theorem* to_list'_cons
- \+ *theorem* to_list'_think
- \+ *theorem* to_list'_map
- \+ *theorem* to_list_cons
- \+ *theorem* to_list_nil
- \+/\- *def* lift_rel_o
- \+/\- *def* bisim_o
- \+/\- *def* tail.aux
- \+/\- *def* drop.aux
- \+/\- *def* destruct_append.aux
- \+/\- *def* destruct_join.aux
- \- *def* lift_rel.refl
- \- *def* lift_rel_o.swap
- \- *def* lift_rel.swap_lem
- \- *def* lift_rel.swap
- \- *def* lift_rel.symm
- \- *def* lift_rel.trans
- \- *def* lift_rel.equiv
- \- *def* join_nil
- \- *def* join_think
- \- *def* join_cons
- \- *def* drop.aux_none
- \- *def* of_mem_append
- \- *def* mem_append_left
- \- *def* lift_rel_nil
- \- *def* lift_rel_cons
- \- *def* lift_rel_think_left
- \- *def* lift_rel_think_right
- \- *def* of_list_nil
- \- *def* of_list_cons
- \- *def* to_list'_nil
- \- *def* to_list'_cons
- \- *def* to_list'_think
- \- *def* to_list'_map
- \- *def* to_list_cons
- \- *def* to_list_nil

Modified data/set/basic.lean
- \+ *theorem* mem_image_elim
- \+ *theorem* mem_image_elim_on
- \- *def* mem_image_elim
- \- *def* mem_image_elim_on

Modified data/set/disjointed.lean


Modified data/set/finite.lean


Modified data/set/function.lean
- \+ *theorem* maps_to_univ
- \- *theorem* maps_to_univ_univ
- \+/\- *def* maps_to

Modified data/set/lattice.lean


Modified data/sigma/basic.lean


Modified data/sum.lean
- \+/\- *def* swap

Modified logic/embedding.lean


Modified logic/function.lean


Modified number_theory/dioph.lean
- \+ *lemma* eq_nat_abs_iff_mul
- \+ *theorem* cons_fz
- \+ *theorem* cons_fs
- \+ *theorem* eq_nil
- \+ *theorem* cons_head_tail
- \+ *theorem* cons_elim_cons
- \+ *theorem* rec_on_nil
- \+ *theorem* rec_on_cons
- \+ *theorem* append_nil
- \+ *theorem* append_cons
- \+ *theorem* append_left
- \+ *theorem* append_add
- \+ *theorem* insert_fz
- \+ *theorem* insert_fs
- \+ *theorem* append_insert
- \+ *def* elim0
- \+ *def* to_nat
- \+ *def* opt_of_nat
- \+ *def* add
- \+ *def* left
- \+ *def* insert_perm
- \+ *def* remap_left
- \+ *def* of_nat'
- \+ *def* nil
- \+ *def* cons
- \+ *def* nth
- \+ *def* of_fn
- \+ *def* head
- \+ *def* tail
- \+ *def* nil_elim
- \+ *def* cons_elim
- \+ *def* append
- \+ *def* insert
- \+/\- *def* list_all
- \+ *def* join
- \- *def* pow

Modified number_theory/pell.lean


Modified order/basic.lean
- \+ *theorem* is_irrefl_of_is_asymm
- \+ *theorem* is_irrefl.swap
- \+ *theorem* is_trans.swap
- \+ *theorem* is_strict_order.swap
- \+ *theorem* is_trichotomous.swap
- \+ *theorem* is_strict_total_order'.swap
- \+ *theorem* is_strict_weak_order_of_is_order_connected
- \- *def* is_irrefl_of_is_asymm
- \- *def* is_irrefl.swap
- \- *def* is_trans.swap
- \- *def* is_strict_order.swap
- \- *def* is_trichotomous.swap
- \- *def* is_strict_total_order'.swap
- \- *def* is_strict_weak_order_of_is_order_connected

Modified order/boolean_algebra.lean


Modified order/bounded_lattice.lean


Modified order/complete_boolean_algebra.lean


Modified order/complete_lattice.lean
- \+/\- *theorem* le_Sup
- \+/\- *theorem* Inf_le

Modified order/filter.lean
- \+/\- *lemma* lift_le
- \+/\- *def* directed
- \+/\- *def* directed_on
- \+/\- *def* tendsto
- \- *def* upwards

Modified order/fixed_points.lean


Modified order/galois_connection.lean


Modified order/lattice.lean


Modified order/order_iso.lean


Modified order/zorn.lean


Modified set_theory/cardinal.lean


Modified set_theory/cofinality.lean
- \+/\- *theorem* lt_cof_power

Modified set_theory/ordinal.lean
- \+ *theorem* unique_of_extensional
- \+/\- *theorem* collapse_apply
- \+/\- *def* cod_restrict
- \+/\- *def* typein
- \- *def* unique_of_extensional

Modified set_theory/ordinal_notation.lean


Modified set_theory/zfc.lean
- \+ *theorem* mk_type_func
- \+ *theorem* equiv.refl
- \+ *theorem* equiv.euc
- \+ *theorem* equiv.symm
- \+ *theorem* equiv.trans
- \+ *theorem* equiv.ext
- \+ *theorem* subset.congr_left
- \+ *theorem* subset.congr_right
- \+ *theorem* mem.mk
- \+ *theorem* mem.ext
- \+ *theorem* mem.congr_right
- \+ *theorem* mem.congr_left
- \+ *theorem* equiv.eq
- \+ *theorem* mem_empty
- \+ *theorem* mem_powerset
- \+ *theorem* mem_Union
- \+ *theorem* mem_image
- \+ *theorem* lift_mem_embed
- \+ *theorem* resp.refl
- \+ *theorem* resp.euc
- \+ *theorem* definable.eq
- \+ *theorem* mk_eq
- \+ *theorem* subset_iff
- \+ *theorem* ext
- \+ *theorem* ext_iff
- \+ *theorem* eq_empty
- \+ *theorem* mem_insert
- \+ *theorem* mem_singleton
- \+ *theorem* mem_singleton'
- \+ *theorem* mem_pair
- \+ *theorem* omega_zero
- \+ *theorem* omega_succ
- \+ *theorem* mem_sep
- \+ *theorem* Union_lem
- \+ *theorem* Union_singleton
- \+ *theorem* singleton_inj
- \+ *theorem* mem_union
- \+ *theorem* mem_inter
- \+ *theorem* mem_diff
- \+ *theorem* induction_on
- \+ *theorem* regularity
- \+ *theorem* image.mk
- \+ *theorem* mem_pair_sep
- \+ *theorem* pair_inj
- \+ *theorem* mem_prod
- \+ *theorem* pair_mem_prod
- \+ *theorem* mem_funs
- \+ *theorem* mem_map
- \+ *theorem* map_unique
- \+ *theorem* map_is_func
- \+ *theorem* mem_univ
- \+ *theorem* of_Set.inj
- \+ *theorem* to_Set_of_Set
- \+ *theorem* mem_hom_left
- \+ *theorem* mem_hom_right
- \+ *theorem* subset_hom
- \+ *theorem* sep_hom
- \+ *theorem* empty_hom
- \+ *theorem* insert_hom
- \+ *theorem* union_hom
- \+ *theorem* inter_hom
- \+ *theorem* diff_hom
- \+ *theorem* powerset_hom
- \+ *theorem* Union_hom
- \+ *theorem* iota_val
- \+ *theorem* iota_ex
- \+ *theorem* fval_ex
- \+ *theorem* map_fval
- \+ *theorem* choice_mem_aux
- \+ *theorem* choice_is_func
- \+ *theorem* choice_mem
- \+ *def* type
- \+ *def* func
- \+ *def* equiv
- \+ *def* mem
- \+ *def* to_set
- \+ *def* of_nat
- \+ *def* omega
- \+ *def* powerset
- \+ *def* Union
- \+ *def* image
- \+ *def* embed
- \+ *def* arity.equiv
- \+ *def* resp
- \+ *def* resp.f
- \+ *def* resp.equiv
- \+ *def* eval_aux
- \+ *def* eval
- \+ *def* eval_val
- \+ *def* definable.eq_mk
- \+ *def* definable.resp
- \+ *def* mk
- \+ *def* empty
- \+ *def* pair
- \+ *def* pair_sep
- \+ *def* prod
- \+ *def* is_func
- \+ *def* funs
- \+ *def* of_Set
- \+ *def* univ
- \+ *def* to_Set
- \+ *def* Cong_to_Class
- \+ *def* Class_to_Cong
- \+ *def* iota
- \+ *def* fval

Modified tactic/interactive.lean


Modified tactic/norm_num.lean




## [2018-01-11 16:26:08-05:00](https://github.com/leanprover-community/mathlib/commit/2ffd72c)
refactor(order/basic): remove "increasing/decreasing" unusual defs
#### Estimated changes
Modified order/basic.lean
- \+ *def* preorder.dual
- \+ *def* partial_order.dual
- \- *def* preorder_dual
- \- *def* partial_order_dual

Modified order/galois_connection.lean
- \+/\- *lemma* increasing_u_l
- \+/\- *lemma* decreasing_l_u
- \+ *def* kern_image



## [2018-01-11 16:21:21-05:00](https://github.com/leanprover-community/mathlib/commit/09e0899)
fix(analysis/ennreal): fix long-running proofs
#### Estimated changes
Modified algebra/functions.lean
- \+/\- *lemma* abs_lt
- \+/\- *theorem* abs_le

Modified algebra/linear_algebra/basic.lean


Modified analysis/ennreal.lean
- \+ *lemma* of_real_add
- \- *lemma* of_real_add_of_real

Modified analysis/measure_theory/lebesgue_measure.lean


Modified order/filter.lean


Modified order/zorn.lean


Modified set_theory/ordinal.lean




## [2018-01-11 12:23:27-05:00](https://github.com/leanprover-community/mathlib/commit/7fd7ea8)
fix(analysis/real): more irreducible
#### Estimated changes
Modified algebra/linear_algebra/prod_module.lean


Modified analysis/ennreal.lean


Modified analysis/real.lean
- \+ *lemma* of_rat_le
- \+/\- *lemma* two_eq_of_rat_two
- \+ *lemma* min_of_rat
- \+ *lemma* max_of_rat
- \- *lemma* of_rat_le_of_rat
- \- *lemma* min_of_rat_of_rat
- \- *lemma* max_of_rat_of_rat
- \+ *theorem* real.le_def



## [2018-01-11 06:57:19-05:00](https://github.com/leanprover-community/mathlib/commit/27920e9)
fix(data/list/basic,...): update to lean
#### Estimated changes
Modified data/hash_map.lean


Modified data/list/basic.lean




## [2018-01-10 03:03:39-05:00](https://github.com/leanprover-community/mathlib/commit/dc28573)
fix(number_theory/pell,...): update to lean
#### Estimated changes
Modified number_theory/pell.lean


Modified set_theory/ordinal_notation.lean




## [2018-01-07 14:32:08-05:00](https://github.com/leanprover-community/mathlib/commit/5ff51dc)
feat(analysis/complex): complex numbers as a field
#### Estimated changes
Created analysis/complex.lean
- \+ *lemma* proj_re
- \+ *lemma* proj_im
- \+ *lemma* coe_re
- \+ *lemma* coe_im
- \+ *lemma* zero_re
- \+ *lemma* zero_im
- \+ *lemma* one_re
- \+ *lemma* one_im
- \+ *lemma* I_re
- \+ *lemma* I_im
- \+ *lemma* conj_re
- \+ *lemma* conj_im
- \+ *lemma* add_re
- \+ *lemma* add_im
- \+ *lemma* neg_re
- \+ *lemma* neg_im
- \+ *lemma* sub_re
- \+ *lemma* sub_im
- \+ *lemma* mul_re
- \+ *lemma* mul_im
- \+ *lemma* norm_squared_pos_of_nonzero
- \+ *lemma* of_real_injective
- \+ *lemma* of_real_zero
- \+ *lemma* of_real_one
- \+ *lemma* of_real_eq_coe
- \+ *lemma* of_real_neg
- \+ *lemma* of_real_add
- \+ *lemma* of_real_sub
- \+ *lemma* of_real_mul
- \+ *lemma* of_real_inv
- \+ *lemma* of_real_abs_squared
- \+ *theorem* eta
- \+ *theorem* eq_of_re_eq_and_im_eq
- \+ *theorem* eq_iff_re_eq_and_im_eq
- \+ *theorem* im_eq_zero_of_complex_nat
- \+ *theorem* of_real_nat_eq_complex_nat
- \+ *theorem* of_real_int_eq_complex_int
- \+ *theorem* of_real_rat_eq_complex_rat
- \+ *def* of_real
- \+ *def* I
- \+ *def* conjugate
- \+ *def* norm_squared



## [2018-01-06 18:57:25-05:00](https://github.com/leanprover-community/mathlib/commit/182c303)
feat(set_theory/cofinality): regular/inaccessible cards, Konig's theorem, next fixpoint function
#### Estimated changes
Modified algebra/functions.lean
- \+ *lemma* abs_one

Modified data/equiv.lean
- \+ *def* Pi_congr_right

Modified logic/embedding.lean
- \+ *def* sigma_congr_right
- \+ *def* Pi_congr_right

Modified logic/function.lean
- \+ *lemma* inv_fun_surjective

Modified set_theory/cardinal.lean
- \+ *theorem* mk_out
- \+ *theorem* add_def
- \+ *theorem* mul_def
- \+ *theorem* power_def
- \+ *theorem* power_ne_zero
- \+ *theorem* pos_iff_ne_zero
- \+ *theorem* lt_succ
- \+ *theorem* sum_mk
- \+ *theorem* sum_const
- \+ *theorem* sum_le_sum
- \+ *theorem* sup_le_sup
- \+ *theorem* sup_le_sum
- \+ *theorem* sum_le_sup
- \+ *theorem* prod_mk
- \+ *theorem* prod_const
- \+ *theorem* prod_le_prod
- \+ *theorem* prod_ne_zero
- \+ *theorem* prod_eq_zero
- \+ *theorem* lift_id'
- \+/\- *theorem* lift_id
- \+ *theorem* lift_two_power
- \+ *theorem* lift_succ
- \+ *theorem* omega_pos
- \+ *theorem* cantor'
- \+ *theorem* one_le_iff_pos
- \+ *theorem* one_le_iff_ne_zero
- \+ *theorem* sum_lt_prod
- \+/\- *def* sum
- \+ *def* prod

Created set_theory/cofinality.lean
- \+ *theorem* order_iso.cof.aux
- \+ *theorem* order_iso.cof
- \+ *theorem* le_cof_type
- \+ *theorem* cof_type_le
- \+ *theorem* lt_cof_type
- \+ *theorem* cof_eq
- \+ *theorem* ord_cof_eq
- \+ *theorem* lift_cof
- \+ *theorem* cof_le_card
- \+ *theorem* cof_ord_le
- \+ *theorem* cof_zero
- \+ *theorem* cof_eq_zero
- \+ *theorem* cof_succ
- \+ *theorem* cof_eq_one_iff_is_succ
- \+ *theorem* cof_add
- \+ *theorem* cof_cof
- \+ *theorem* omega_le_cof
- \+ *theorem* cof_omega
- \+ *theorem* cof_eq'
- \+ *theorem* cof_sup_le_lift
- \+ *theorem* cof_sup_le
- \+ *theorem* cof_bsup_le_lift
- \+ *theorem* cof_bsup_le
- \+ *theorem* cof_univ
- \+ *theorem* is_strong_limit.is_limit
- \+ *theorem* cof_is_regular
- \+ *theorem* omega_is_regular
- \+ *theorem* succ_is_regular
- \+ *theorem* is_inaccessible.mk
- \+ *theorem* univ_inaccessible
- \+ *theorem* lt_power_cof
- \+ *theorem* lt_cof_power
- \+ *def* order.cof
- \+ *def* cof
- \+ *def* is_limit
- \+ *def* is_strong_limit
- \+ *def* is_regular
- \+ *def* is_inaccessible

Modified set_theory/ordinal.lean
- \+ *theorem* lift_type
- \+ *theorem* lift_id'
- \+/\- *theorem* lift_id
- \+ *theorem* not_zero_is_limit
- \+ *theorem* univ_id
- \+ *theorem* lift_univ
- \+ *theorem* univ_umax
- \+/\- *theorem* lift.principal_seg_top
- \+ *theorem* lift_lt_univ
- \+ *theorem* lift_lt_univ'
- \+ *theorem* ord_univ
- \+ *theorem* lt_univ
- \+ *theorem* lt_univ'
- \+ *theorem* card_univ
- \+ *theorem* lt_sup
- \+ *theorem* is_normal.sup
- \+ *theorem* is_normal.bsup
- \+ *theorem* foldr_le_nfp
- \+ *theorem* le_nfp_self
- \+ *theorem* is_normal.lt_nfp
- \+ *theorem* is_normal.nfp_le
- \+ *theorem* is_normal.nfp_le_fp
- \+ *theorem* is_normal.nfp_fp
- \+ *theorem* is_normal.le_nfp
- \+ *theorem* deriv_zero
- \+ *theorem* deriv_succ
- \+ *theorem* deriv_limit
- \+ *theorem* deriv_is_normal
- \+ *theorem* is_normal.deriv_fp
- \+ *theorem* is_normal.fp_iff_deriv
- \+ *theorem* type_cardinal
- \+ *theorem* mk_cardinal
- \- *theorem* order_iso.cof.aux
- \- *theorem* order_iso.cof
- \- *theorem* le_cof_type
- \- *theorem* cof_type_le
- \- *theorem* lt_cof_type
- \- *theorem* cof_eq
- \- *theorem* ord_cof_eq
- \- *theorem* cof_le_card
- \- *theorem* cof_zero
- \- *theorem* cof_eq_zero
- \- *theorem* cof_succ
- \- *theorem* cof_eq_one_iff_is_succ
- \- *theorem* cof_add
- \- *theorem* cof_cof
- \- *theorem* cof_sup_le_lift
- \- *theorem* cof_sup_le
- \- *theorem* cof_bsup_le_lift
- \- *theorem* cof_bsup_le
- \+ *def* univ
- \+ *def* nfp
- \+ *def* deriv
- \- *def* order.cof
- \- *def* cof

Modified set_theory/ordinal_notation.lean




## [2018-01-06 00:50:12+01:00](https://github.com/leanprover-community/mathlib/commit/4f7835e)
feat(analysis): add default setup for uniform space of metric space
#### Estimated changes
Modified analysis/metric_space.lean
- \+ *def* metric_space.uniform_space_of_dist



## [2018-01-04 09:05:50-05:00](https://github.com/leanprover-community/mathlib/commit/0b7b912)
feat(set_theory/ordinal_notation): correctness of ordinal power
#### Estimated changes
Modified algebra/order.lean
- \+/\- *lemma* le_or_lt

Modified data/pnat.lean
- \+ *theorem* succ_pnat_coe
- \+ *theorem* pos
- \+ *theorem* eq
- \+ *theorem* mk_coe
- \+ *theorem* add_coe
- \+/\- *theorem* ne_zero
- \+ *theorem* nat_coe_coe
- \+ *theorem* one_coe
- \+ *theorem* mul_coe
- \- *theorem* to_pnat'_val
- \- *theorem* nat_coe_val
- \+ *def* pow

Modified logic/basic.lean
- \+ *theorem* coe_coe

Modified set_theory/ordinal.lean
- \+ *theorem* nat_cast_succ
- \+ *theorem* add_le_add_iff_right
- \+ *theorem* add_right_cancel
- \+ *theorem* lt_limit
- \+ *theorem* is_normal.limit_le
- \+ *theorem* sub_eq_of_add_eq
- \+ *theorem* sub_sub
- \+ *theorem* add_sub_add_cancel
- \+ *theorem* sub_is_limit
- \+ *theorem* mul_is_limit_left
- \+ *theorem* mul_sub
- \+ *theorem* dvd_trans
- \+ *theorem* dvd_mul_of_dvd
- \+ *theorem* dvd_add_iff
- \+ *theorem* dvd_add
- \+/\- *theorem* zero_dvd
- \+ *theorem* le_of_dvd
- \+ *theorem* dvd_antisymm
- \+ *theorem* power_dvd_power
- \+ *theorem* power_dvd_power_iff
- \+ *theorem* is_limit_iff_omega_dvd
- \+ *theorem* power_lt_omega
- \+ *theorem* add_lt_omega_power
- \+ *theorem* mul_lt_omega_power
- \+ *theorem* mul_omega_dvd
- \+ *theorem* power_omega
- \- *theorem* succ_nat_cast
- \- *theorem* mul_one
- \- *theorem* one_mul
- \- *theorem* mul_assoc
- \- *theorem* mul_omega_power

Modified set_theory/ordinal_notation.lean
- \+/\- *theorem* lt_def
- \+/\- *theorem* le_def
- \+/\- *theorem* omega_le_oadd
- \+/\- *theorem* oadd_pos
- \+/\- *theorem* NF_below.oadd
- \+/\- *theorem* NF_below.fst
- \+/\- *theorem* NF.fst
- \+/\- *theorem* NF_below.snd
- \+/\- *theorem* NF.snd'
- \+/\- *theorem* NF.snd
- \+/\- *theorem* NF.oadd
- \+/\- *theorem* NF_below.lt
- \+ *theorem* NF.zero_of_zero
- \+/\- *theorem* NF_below.repr_lt
- \+/\- *theorem* NF.below_of_lt
- \+ *theorem* NF.below_of_lt'
- \+/\- *theorem* oadd_lt_oadd_3
- \+/\- *theorem* cmp_compares
- \+/\- *theorem* repr_inj
- \+ *theorem* NF.of_dvd_omega_power
- \+ *theorem* NF.of_dvd_omega
- \+/\- *theorem* NF_below_iff_top_below
- \+ *theorem* zero_add
- \+ *theorem* oadd_add
- \+/\- *theorem* repr_add
- \+ *theorem* sub_NF_below
- \+ *theorem* repr_sub
- \+ *theorem* zero_mul
- \+ *theorem* mul_zero
- \+ *theorem* oadd_mul
- \+/\- *theorem* repr_mul
- \+ *theorem* split_eq_scale_split'
- \+ *theorem* NF_repr_split'
- \+ *theorem* scale_eq_mul
- \+ *theorem* repr_scale
- \+ *theorem* NF_repr_split
- \+ *theorem* split_dvd
- \+ *theorem* split_add_lt
- \+ *theorem* mul_nat_eq_mul
- \+ *theorem* scale_power_aux
- \+ *theorem* repr_power_aux₁
- \+ *theorem* repr_power_aux₂
- \+ *theorem* repr_power
- \- *theorem* repr_add_nat
- \- *theorem* succ_zero
- \- *theorem* repr_succ
- \- *theorem* lt_succ_self
- \- *theorem* succ_le
- \- *theorem* NF.zero
- \- *theorem* NF_of_nat
- \- *theorem* NF_below_add_nat
- \- *theorem* NF_add_nat
- \- *theorem* add_NF
- \- *theorem* mul_NF
- \+ *def* omega
- \+ *def* to_string_aux1
- \+ *def* to_string
- \+ *def* repr'
- \+/\- *def* NF
- \+/\- *def* split'
- \+/\- *def* split
- \+/\- *def* scale
- \+ *def* mul_nat
- \+/\- *def* power_aux
- \+ *def* mk
- \+ *def* below
- \+ *def* oadd
- \+ *def* rec_on
- \+ *def* power
- \- *def* add_nat
- \- *def* succ



## [2018-01-04 09:05:02-05:00](https://github.com/leanprover-community/mathlib/commit/3f2435e)
refactor(algebra/group): clean up PR commit
#### Estimated changes
Modified algebra/big_operators.lean
- \- *lemma* mph_prod
- \- *lemma* anti_mph_prod
- \- *lemma* inv_prod
- \+ *theorem* is_group_hom.prod
- \+ *theorem* is_group_anti_hom.prod
- \+ *theorem* inv_prod

Modified algebra/group.lean
- \- *lemma* one
- \- *lemma* inv
- \- *lemma* inv_is_group_anti_hom
- \+ *theorem* mul
- \+ *theorem* one
- \+ *theorem* inv
- \+ *theorem* inv_is_group_anti_hom



## [2018-01-02 16:52:49-05:00](https://github.com/leanprover-community/mathlib/commit/12bd22b)
Group morphisms ([#30](https://github.com/leanprover-community/mathlib/pull/30))
* feat(algebra/group): morphisms and antimorphisms
Definitions, image of one and inverses,
and computation on a product of more than two elements in big_operators.
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* mph_prod
- \+ *lemma* anti_mph_prod
- \+ *lemma* inv_prod

Modified algebra/group.lean
- \+ *lemma* one
- \+ *lemma* inv
- \+ *lemma* inv_is_group_anti_hom
- \+ *def* is_group_hom
- \+ *def* is_group_anti_hom



## [2018-01-02 04:28:01-05:00](https://github.com/leanprover-community/mathlib/commit/37c3120)
feat(set_theory/ordinal_notation): ordinal notations for ordinals < e0
This allows us to compute with small countable ordinals using trees of nats.
#### Estimated changes
Modified algebra/order.lean
- \+/\- *lemma* lt_iff_lt_of_strict_mono
- \+ *lemma* injective_of_strict_mono
- \+ *theorem* compares.eq_lt
- \+ *theorem* compares.eq_eq
- \+ *theorem* compares.eq_gt
- \+ *theorem* compares.inj
- \+ *theorem* compares_of_strict_mono
- \+ *def* compares

Modified data/nat/cast.lean
- \+/\- *theorem* cast_add_one

Modified data/pnat.lean
- \+ *theorem* ne_zero
- \+ *theorem* to_pnat'_val
- \+ *theorem* nat_coe_val
- \+ *theorem* to_pnat'_coe
- \+ *def* to_pnat
- \+ *def* succ_pnat
- \+ *def* to_pnat'

Modified logic/basic.lean
- \+ *theorem* imp_or_distrib
- \+ *theorem* imp_or_distrib'

Renamed theories/number_theory/dioph.lean to number_theory/dioph.lean


Renamed theories/number_theory/pell.lean to number_theory/pell.lean


Renamed data/cardinal.lean to set_theory/cardinal.lean


Renamed data/ordinal.lean to set_theory/ordinal.lean
- \+ *theorem* bsup_type
- \+ *theorem* nat_cast_pos
- \+ *theorem* add_mul_limit_aux
- \+ *theorem* add_mul_succ
- \+ *theorem* add_mul_limit
- \+/\- *theorem* cof_bsup_le_lift
- \+ *theorem* cof_bsup_le

Created set_theory/ordinal_notation.lean
- \+ *theorem* zero_def
- \+ *theorem* lt_def
- \+ *theorem* le_def
- \+ *theorem* of_nat_one
- \+ *theorem* repr_of_nat
- \+ *theorem* repr_one
- \+ *theorem* repr_add_nat
- \+ *theorem* succ_zero
- \+ *theorem* repr_succ
- \+ *theorem* lt_succ_self
- \+ *theorem* succ_le
- \+ *theorem* omega_le_oadd
- \+ *theorem* oadd_pos
- \+ *theorem* eq_of_cmp_eq
- \+ *theorem* zero_lt_one
- \+ *theorem* NF.zero
- \+ *theorem* NF_below.oadd
- \+ *theorem* NF_below.fst
- \+ *theorem* NF.fst
- \+ *theorem* NF_below.snd
- \+ *theorem* NF.snd'
- \+ *theorem* NF.snd
- \+ *theorem* NF.oadd
- \+ *theorem* NF_below.lt
- \+ *theorem* NF_below_zero
- \+ *theorem* NF_below.repr_lt
- \+ *theorem* NF_below.mono
- \+ *theorem* NF.below_of_lt
- \+ *theorem* NF_below_of_nat
- \+ *theorem* NF_of_nat
- \+ *theorem* NF_below_add_nat
- \+ *theorem* NF_add_nat
- \+ *theorem* oadd_lt_oadd_1
- \+ *theorem* oadd_lt_oadd_2
- \+ *theorem* oadd_lt_oadd_3
- \+ *theorem* cmp_compares
- \+ *theorem* repr_inj
- \+ *theorem* NF_below_iff_top_below
- \+ *theorem* add_NF_below
- \+ *theorem* add_NF
- \+ *theorem* repr_add
- \+ *theorem* oadd_mul_NF_below
- \+ *theorem* mul_NF
- \+ *theorem* repr_mul
- \+ *def* of_nat
- \+ *def* add_nat
- \+ *def* succ
- \+ *def* cmp
- \+ *def* NF
- \+ *def* top_below
- \+ *def* add
- \+ *def* sub
- \+ *def* mul
- \+ *def* split'
- \+ *def* split
- \+ *def* scale
- \+ *def* power_aux
- \+ *def* power
- \+ *def* nonote

Renamed theories/set_theory.lean to set_theory/zfc.lean


Modified tactic/interactive.lean


