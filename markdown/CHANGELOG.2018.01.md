## [2018-01-26 03:15:01-05:00](https://github.com/leanprover-community/mathlib/commit/edd62de)
fix(set_theory/zfc): update to lean
#### Estimated changes
Modified set_theory/zfc.lean
- \+/\- *def* Class.fval
- \+/\- *theorem* Class.mem_hom_left
- \+/\- *theorem* Class.mem_hom_right



## [2018-01-26 02:52:13-05:00](https://github.com/leanprover-community/mathlib/commit/f46d32b)
feat(algebra/archimedean): generalize real thms to archimedean fields
#### Estimated changes
Added algebra/archimedean.lean
- \+ *theorem* archimedean_iff_nat_le
- \+ *theorem* archimedean_iff_nat_lt
- \+ *theorem* archimedean_iff_rat_le
- \+ *theorem* archimedean_iff_rat_lt
- \+ *def* ceil
- \+ *theorem* ceil_add_int
- \+ *theorem* ceil_coe
- \+ *theorem* ceil_le
- \+ *theorem* ceil_lt_add_one
- \+ *theorem* ceil_mono
- \+ *theorem* ceil_sub_int
- \+ *theorem* exists_floor
- \+ *theorem* exists_int_gt
- \+ *theorem* exists_int_lt
- \+ *theorem* exists_nat_gt
- \+ *theorem* exists_pos_rat_lt
- \+ *theorem* exists_rat_btwn
- \+ *theorem* exists_rat_gt
- \+ *theorem* exists_rat_lt
- \+ *theorem* exists_rat_near
- \+ *def* floor
- \+ *theorem* floor_add_int
- \+ *theorem* floor_coe
- \+ *theorem* floor_le
- \+ *theorem* floor_lt
- \+ *theorem* floor_mono
- \+ *theorem* floor_nonneg
- \+ *theorem* floor_sub_int
- \+ *theorem* le_ceil
- \+ *theorem* le_floor
- \+ *theorem* lt_ceil
- \+ *theorem* lt_floor_add_one
- \+ *theorem* lt_succ_floor
- \+ *theorem* sub_one_lt_floor

Modified algebra/group_power.lean
- \+ *theorem* add_monoid.mul_smul_assoc
- \+ *theorem* add_monoid.mul_smul_right
- \+ *theorem* add_monoid.one_smul
- \+ *theorem* add_monoid.smul_eq_mul'
- \+ *theorem* add_monoid.smul_eq_mul
- \+ *theorem* add_monoid.smul_nonneg
- \+ *theorem* gsmul_eq_mul'
- \+ *theorem* gsmul_eq_mul
- \+ *theorem* mul_gsmul_assoc
- \+ *theorem* mul_gsmul_right
- \+ *theorem* one_le_pow_of_one_le
- \+ *theorem* pow_ge_one_add_mul
- \+ *theorem* pow_ge_one_add_sub_mul
- \- *theorem* pow_ge_one_of_ge_one
- \+/\- *theorem* pow_nonneg
- \+/\- *theorem* pow_pos

Modified analysis/complex.lean


Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/borel_space.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/real.lean


Renamed data/complex.lean to data/complex/basic.lean
- \+ *lemma* complex.abs_le_abs_re_add_abs_im
- \+ *theorem* complex.equiv_lim
- \+ *theorem* complex.is_cau_seq_im
- \+ *theorem* complex.is_cau_seq_re
- \+ *lemma* complex.re_add_im

Modified data/rat.lean
- \+ *theorem* rat.coe_int_denom
- \+ *theorem* rat.coe_int_num
- \+ *theorem* rat.coe_nat_denom
- \+ *theorem* rat.coe_nat_num

Modified data/real/basic.lean
- \- *theorem* real.ceil_add_int
- \- *theorem* real.ceil_coe
- \- *theorem* real.ceil_le
- \- *theorem* real.ceil_lt_add_one
- \- *theorem* real.ceil_mono
- \- *theorem* real.ceil_sub_int
- \- *theorem* real.exists_int_gt
- \- *theorem* real.exists_int_lt
- \- *theorem* real.exists_nat_gt
- \- *theorem* real.exists_pos_rat_lt
- \- *theorem* real.exists_rat_btwn
- \- *theorem* real.exists_rat_gt
- \- *theorem* real.exists_rat_lt
- \- *theorem* real.exists_rat_near'
- \- *theorem* real.exists_rat_near
- \- *theorem* real.floor_add_int
- \- *theorem* real.floor_coe
- \- *theorem* real.floor_le
- \- *theorem* real.floor_lt
- \- *theorem* real.floor_mono
- \- *theorem* real.floor_nonneg
- \- *theorem* real.floor_sub_int
- \- *theorem* real.le_ceil
- \- *theorem* real.le_floor
- \+/\- *theorem* real.le_mk_of_forall_le
- \- *theorem* real.lt_ceil
- \- *theorem* real.lt_floor_add_one
- \- *theorem* real.lt_succ_floor
- \+/\- *theorem* real.mk_le_of_forall_le
- \+/\- *theorem* real.mk_near_of_forall_near
- \- *theorem* real.sub_one_lt_floor

Modified data/real/cau_seq.lean
- \+ *theorem* cau_seq.is_cau
- \+ *theorem* cau_seq.mk_to_fun

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
- \+/\- *theorem* continuous_of_metric
- \+/\- *theorem* tendsto_dist
- \+/\- *theorem* tendsto_nhds_of_metric
- \+/\- *theorem* uniform_continuous_of_metric
- \+/\- *theorem* uniform_embedding_of_metric



## [2018-01-23 03:30:58-05:00](https://github.com/leanprover-community/mathlib/commit/acb9093)
feat(analysis/complex): complex numbers are a top ring
#### Estimated changes
Modified analysis/complex.lean
- \+ *lemma* complex.continuous_abs
- \+ *lemma* complex.continuous_inv'
- \+ *lemma* complex.continuous_inv
- \+ *lemma* complex.continuous_mul
- \+/\- *theorem* complex.dist_eq
- \+ *lemma* complex.tendsto_inv
- \+ *lemma* complex.uniform_continuous_abs
- \+ *theorem* complex.uniform_continuous_add
- \+ *lemma* complex.uniform_continuous_inv
- \+ *lemma* complex.uniform_continuous_mul
- \+ *lemma* complex.uniform_continuous_mul_const
- \+ *theorem* complex.uniform_continuous_neg

Modified data/complex.lean
- \+ *lemma* complex.abs_abs_sub_le_abs_sub

Modified data/real/cau_seq.lean
- \+ *lemma* is_absolute_value.abs_abv_sub_le_abv_sub
- \+ *lemma* is_absolute_value.sub_abv_le_abv_sub



## [2018-01-23 03:07:52-05:00](https://github.com/leanprover-community/mathlib/commit/65c5cb9)
refactor(data/real): generalize cau_seq to arbitrary metrics
the intent is to use this also for the complex numbers
#### Estimated changes
Modified analysis/metric_space.lean


Modified analysis/real.lean


Modified data/complex.lean
- \+ *theorem* complex.abs_div
- \+ *theorem* complex.abs_inv
- \+/\- *lemma* complex.abs_neg
- \+/\- *lemma* complex.abs_pos
- \+/\- *lemma* complex.abs_sub
- \+/\- *lemma* complex.abs_sub_le

Renamed data/real.lean to data/real/basic.lean
- \- *theorem* cau_seq.abs_pos_of_not_lim_zero
- \- *theorem* cau_seq.add_apply
- \- *theorem* cau_seq.add_lim_zero
- \- *theorem* cau_seq.add_pos
- \- *theorem* cau_seq.bounded'
- \- *theorem* cau_seq.bounded
- \- *theorem* cau_seq.cauchy
- \- *theorem* cau_seq.cauchy₂
- \- *theorem* cau_seq.cauchy₃
- \- *def* cau_seq.const
- \- *theorem* cau_seq.const_add
- \- *theorem* cau_seq.const_apply
- \- *theorem* cau_seq.const_equiv
- \- *theorem* cau_seq.const_inj
- \- *theorem* cau_seq.const_le
- \- *theorem* cau_seq.const_lim_zero
- \- *theorem* cau_seq.const_lt
- \- *theorem* cau_seq.const_mul
- \- *theorem* cau_seq.const_neg
- \- *theorem* cau_seq.const_pos
- \- *theorem* cau_seq.const_sub
- \- *theorem* cau_seq.equiv_def₃
- \- *theorem* cau_seq.exists_gt
- \- *theorem* cau_seq.exists_lt
- \- *theorem* cau_seq.ext
- \- *def* cau_seq.inv
- \- *theorem* cau_seq.inv_apply
- \- *theorem* cau_seq.inv_aux
- \- *theorem* cau_seq.inv_mul_cancel
- \- *theorem* cau_seq.le_antisymm
- \- *theorem* cau_seq.le_total
- \- *def* cau_seq.lim_zero
- \- *theorem* cau_seq.lim_zero_congr
- \- *theorem* cau_seq.lt_irrefl
- \- *theorem* cau_seq.lt_of_eq_of_lt
- \- *theorem* cau_seq.lt_of_lt_of_eq
- \- *theorem* cau_seq.lt_total
- \- *theorem* cau_seq.lt_trans
- \- *theorem* cau_seq.mul_apply
- \- *theorem* cau_seq.mul_lim_zero
- \- *theorem* cau_seq.mul_pos
- \- *theorem* cau_seq.neg_apply
- \- *theorem* cau_seq.neg_lim_zero
- \- *theorem* cau_seq.not_lim_zero_of_pos
- \- *def* cau_seq.of_eq
- \- *theorem* cau_seq.of_near
- \- *theorem* cau_seq.one_apply
- \- *def* cau_seq.pos
- \- *theorem* cau_seq.pos_add_lim_zero
- \- *theorem* cau_seq.sub_apply
- \- *theorem* cau_seq.sub_lim_zero
- \- *theorem* cau_seq.trichotomy
- \- *theorem* cau_seq.zero_apply
- \- *theorem* cau_seq.zero_lim_zero
- \- *def* cau_seq
- \- *theorem* exists_forall_ge_and
- \- *theorem* is_cau_seq.cauchy₂
- \- *theorem* is_cau_seq.cauchy₃
- \- *def* is_cau_seq
- \- *theorem* rat_add_continuous_lemma
- \- *theorem* rat_inv_continuous_lemma
- \- *theorem* rat_mul_continuous_lemma
- \+/\- *theorem* real.cau_seq_converges
- \+/\- *theorem* real.equiv_lim
- \- *def* real.irrational
- \+/\- *theorem* real.is_cau_seq_iff_lift
- \+/\- *theorem* real.le_mk_of_forall_le
- \+/\- *def* real.mk
- \+/\- *theorem* real.mk_add
- \+/\- *theorem* real.mk_le
- \+/\- *theorem* real.mk_le_of_forall_le
- \+/\- *theorem* real.mk_lt
- \+/\- *theorem* real.mk_mul
- \+/\- *theorem* real.mk_near_of_forall_near
- \+/\- *theorem* real.mk_neg
- \+/\- *theorem* real.mk_pos
- \+/\- *def* real.of_rat
- \+/\- *def* real.sqrt_aux
- \+/\- *theorem* real.sqrt_aux_nonneg
- \- *theorem* real.sqrt_two_irrational
- \+/\- *def* real

Added data/real/cau_seq.lean
- \+ *theorem* cau_seq.abv_pos_of_not_lim_zero
- \+ *theorem* cau_seq.add_apply
- \+ *theorem* cau_seq.add_lim_zero
- \+ *theorem* cau_seq.add_pos
- \+ *theorem* cau_seq.bounded'
- \+ *theorem* cau_seq.bounded
- \+ *theorem* cau_seq.cauchy
- \+ *theorem* cau_seq.cauchy₂
- \+ *theorem* cau_seq.cauchy₃
- \+ *def* cau_seq.const
- \+ *theorem* cau_seq.const_add
- \+ *theorem* cau_seq.const_apply
- \+ *theorem* cau_seq.const_equiv
- \+ *theorem* cau_seq.const_inj
- \+ *theorem* cau_seq.const_le
- \+ *theorem* cau_seq.const_lim_zero
- \+ *theorem* cau_seq.const_lt
- \+ *theorem* cau_seq.const_mul
- \+ *theorem* cau_seq.const_neg
- \+ *theorem* cau_seq.const_pos
- \+ *theorem* cau_seq.const_sub
- \+ *theorem* cau_seq.equiv_def₃
- \+ *theorem* cau_seq.exists_gt
- \+ *theorem* cau_seq.exists_lt
- \+ *theorem* cau_seq.ext
- \+ *def* cau_seq.inv
- \+ *theorem* cau_seq.inv_apply
- \+ *theorem* cau_seq.inv_aux
- \+ *theorem* cau_seq.inv_mul_cancel
- \+ *theorem* cau_seq.le_antisymm
- \+ *theorem* cau_seq.le_total
- \+ *def* cau_seq.lim_zero
- \+ *theorem* cau_seq.lim_zero_congr
- \+ *theorem* cau_seq.lt_irrefl
- \+ *theorem* cau_seq.lt_of_eq_of_lt
- \+ *theorem* cau_seq.lt_of_lt_of_eq
- \+ *theorem* cau_seq.lt_total
- \+ *theorem* cau_seq.lt_trans
- \+ *theorem* cau_seq.mul_apply
- \+ *theorem* cau_seq.mul_lim_zero
- \+ *theorem* cau_seq.mul_pos
- \+ *theorem* cau_seq.neg_apply
- \+ *theorem* cau_seq.neg_lim_zero
- \+ *theorem* cau_seq.not_lim_zero_of_pos
- \+ *def* cau_seq.of_eq
- \+ *theorem* cau_seq.of_near
- \+ *theorem* cau_seq.one_apply
- \+ *def* cau_seq.pos
- \+ *theorem* cau_seq.pos_add_lim_zero
- \+ *theorem* cau_seq.sub_apply
- \+ *theorem* cau_seq.sub_lim_zero
- \+ *theorem* cau_seq.trichotomy
- \+ *theorem* cau_seq.zero_apply
- \+ *theorem* cau_seq.zero_lim_zero
- \+ *def* cau_seq
- \+ *theorem* exists_forall_ge_and
- \+ *theorem* is_absolute_value.abv_div
- \+ *theorem* is_absolute_value.abv_inv
- \+ *theorem* is_absolute_value.abv_neg
- \+ *theorem* is_absolute_value.abv_one'
- \+ *theorem* is_absolute_value.abv_one
- \+ *theorem* is_absolute_value.abv_pos
- \+ *theorem* is_absolute_value.abv_sub
- \+ *lemma* is_absolute_value.abv_sub_le
- \+ *theorem* is_absolute_value.abv_zero
- \+ *theorem* is_cau_seq.cauchy₂
- \+ *theorem* is_cau_seq.cauchy₃
- \+ *def* is_cau_seq
- \+ *theorem* rat_add_continuous_lemma
- \+ *theorem* rat_inv_continuous_lemma
- \+ *theorem* rat_mul_continuous_lemma

Added data/real/irrational.lean
- \+ *def* irrational
- \+ *theorem* sqrt_two_irrational



## [2018-01-23 00:14:20-05:00](https://github.com/leanprover-community/mathlib/commit/5fe8fbf)
feat(data/complex): properties of the complex absolute value function
#### Estimated changes
Modified algebra/field.lean


Added analysis/complex.lean
- \+ *theorem* complex.dist_eq

Modified data/complex.lean
- \+ *lemma* complex.abs_I
- \+ *lemma* complex.abs_abs
- \+ *lemma* complex.abs_add
- \+ *lemma* complex.abs_conj
- \+ *lemma* complex.abs_eq_zero
- \+ *lemma* complex.abs_im_le_abs
- \+ *lemma* complex.abs_mul
- \+ *lemma* complex.abs_neg
- \+ *lemma* complex.abs_nonneg
- \+ *lemma* complex.abs_of_nonneg
- \+ *lemma* complex.abs_of_real
- \+ *lemma* complex.abs_one
- \+ *lemma* complex.abs_pos
- \+ *lemma* complex.abs_re_le_abs
- \+ *lemma* complex.abs_sub
- \+ *lemma* complex.abs_sub_le
- \+ *lemma* complex.abs_zero
- \+ *lemma* complex.conj_I
- \+ *lemma* complex.conj_add
- \+ *lemma* complex.conj_bijective
- \+ *lemma* complex.conj_conj
- \+ *lemma* complex.conj_div
- \+ *lemma* complex.conj_eq_zero
- \+ *lemma* complex.conj_inj
- \+ *lemma* complex.conj_inv
- \+ *lemma* complex.conj_mul
- \+ *lemma* complex.conj_neg
- \+ *lemma* complex.conj_one
- \+ *lemma* complex.conj_zero
- \+ *lemma* complex.im_le_abs
- \+ *lemma* complex.im_sq_le_norm_sq
- \+ *lemma* complex.mul_self_abs
- \+ *lemma* complex.norm_sq_I
- \+ *lemma* complex.norm_sq_add
- \+ *lemma* complex.norm_sq_conj
- \+ *lemma* complex.norm_sq_div
- \+ *lemma* complex.norm_sq_inv
- \+ *lemma* complex.norm_sq_mul
- \+ *lemma* complex.norm_sq_neg
- \+/\- *lemma* complex.norm_sq_one
- \+ *lemma* complex.norm_sq_sub
- \+/\- *lemma* complex.norm_sq_zero
- \+ *lemma* complex.re_le_abs
- \+ *lemma* complex.re_sq_le_norm_sq

Modified data/real.lean
- \+ *theorem* real.sqrt_mul_self_eq_abs
- \+ *theorem* real.sqrt_sqr_eq_abs



## [2018-01-21 23:57:42-05:00](https://github.com/leanprover-community/mathlib/commit/5a65212)
feat(data/real): real square root function, sqrt 2 is irrational
#### Estimated changes
Added algebra/char_zero.lean
- \+ *theorem* add_group.char_zero_of_inj_zero
- \+ *lemma* add_halves'
- \+ *lemma* add_self_eq_zero
- \+ *lemma* bit0_eq_zero
- \+ *theorem* char_zero_of_inj_zero
- \+ *lemma* half_add_self
- \+ *lemma* half_sub
- \+ *theorem* nat.cast_eq_zero
- \+ *theorem* nat.cast_inj
- \+ *theorem* nat.cast_injective
- \+ *theorem* nat.cast_ne_zero
- \+ *theorem* ordered_cancel_comm_monoid.char_zero_of_inj_zero
- \+ *lemma* sub_half
- \+ *lemma* two_ne_zero'

Modified algebra/field.lean
- \+ *lemma* div_eq_iff_mul_eq

Modified algebra/group_power.lean
- \+ *theorem* pow_two
- \+ *theorem* smul_two

Modified algebra/ordered_field.lean
- \+ *lemma* div_nonneg'
- \+ *lemma* inv_lt_zero
- \+ *lemma* inv_neg'
- \+ *lemma* inv_nonneg
- \+ *lemma* inv_nonpos
- \+ *lemma* inv_pos'
- \+ *lemma* mul_self_inj_of_nonneg

Modified algebra/ring.lean
- \+ *theorem* bit0_eq_two_mul

Modified data/complex.lean
- \+ *theorem* complex.add_conj
- \+ *lemma* complex.eq_conj_iff_real
- \+ *lemma* complex.of_real_bit0
- \+ *lemma* complex.of_real_bit1
- \+ *lemma* complex.of_real_div
- \+ *theorem* complex.re_eq_add_conj
- \+ *theorem* complex.sub_conj

Modified data/int/basic.lean


Modified data/nat/cast.lean
- \- *theorem* add_group.char_zero_of_inj_zero
- \- *theorem* char_zero_of_inj_zero
- \- *theorem* nat.cast_eq_zero
- \- *theorem* nat.cast_inj
- \- *theorem* nat.cast_injective
- \- *theorem* nat.cast_ne_zero
- \- *theorem* ordered_cancel_comm_monoid.char_zero_of_inj_zero

Modified data/nat/prime.lean
- \- *theorem* nat.dvd_of_prime_of_dvd_pow
- \+ *theorem* nat.prime.dvd_of_dvd_pow

Modified data/real.lean
- \+/\- *theorem* cau_seq.cauchy₂
- \+/\- *theorem* cau_seq.cauchy₃
- \- *def* cau_seq.mk_of_near
- \- *theorem* cau_seq.mk_of_near_equiv
- \- *theorem* cau_seq.mk_of_near_fun
- \+ *theorem* cau_seq.of_near
- \+/\- *def* cau_seq
- \+ *theorem* is_cau_seq.cauchy₂
- \+ *theorem* is_cau_seq.cauchy₃
- \+ *def* is_cau_seq
- \+ *def* real.irrational
- \+ *theorem* real.is_cau_seq_iff_lift
- \+ *theorem* real.mk_near_of_forall_near
- \+ *theorem* real.mul_self_sqrt
- \+ *theorem* real.of_near
- \+ *theorem* real.sqr_sqrt
- \+ *def* real.sqrt_aux
- \+ *theorem* real.sqrt_aux_nonneg
- \+ *theorem* real.sqrt_div
- \+ *theorem* real.sqrt_eq_iff_mul_self_eq
- \+ *theorem* real.sqrt_eq_iff_sqr_eq
- \+ *theorem* real.sqrt_eq_zero'
- \+ *theorem* real.sqrt_eq_zero
- \+ *theorem* real.sqrt_eq_zero_of_nonpos
- \+ *theorem* real.sqrt_exists
- \+ *theorem* real.sqrt_inj
- \+ *theorem* real.sqrt_inv
- \+ *theorem* real.sqrt_le
- \+ *theorem* real.sqrt_lt
- \+ *theorem* real.sqrt_mul'
- \+ *theorem* real.sqrt_mul
- \+ *theorem* real.sqrt_mul_self
- \+ *theorem* real.sqrt_nonneg
- \+ *theorem* real.sqrt_one
- \+ *theorem* real.sqrt_pos
- \+ *theorem* real.sqrt_prop
- \+ *theorem* real.sqrt_sqr
- \+ *theorem* real.sqrt_two_irrational
- \+ *theorem* real.sqrt_zero



## [2018-01-20 21:28:43-05:00](https://github.com/leanprover-community/mathlib/commit/ffafdc6)
feat(tactic/ring): extend ring tactic to allow division by constants
#### Estimated changes
Modified tactic/ring.lean




## [2018-01-20 17:03:57-05:00](https://github.com/leanprover-community/mathlib/commit/bcbf0d5)
refactor(data/complex): clean up proofs
#### Estimated changes
Modified data/complex.lean
- \+/\- *def* complex.I
- \+/\- *lemma* complex.I_im
- \+/\- *lemma* complex.I_re
- \+/\- *lemma* complex.add_im
- \+/\- *lemma* complex.add_re
- \- *lemma* complex.coe_im
- \- *lemma* complex.coe_re
- \+ *def* complex.conj
- \+/\- *lemma* complex.conj_im
- \+ *lemma* complex.conj_of_real
- \+/\- *lemma* complex.conj_re
- \- *def* complex.conjugate
- \- *theorem* complex.eq_iff_re_eq_and_im_eq
- \- *theorem* complex.eq_of_re_eq_and_im_eq
- \+/\- *theorem* complex.eta
- \+ *theorem* complex.ext
- \+ *theorem* complex.ext_iff
- \- *theorem* complex.im_eq_zero_of_complex_nat
- \+ *theorem* complex.inv_def
- \+ *lemma* complex.inv_im
- \+ *lemma* complex.inv_re
- \+ *lemma* complex.inv_zero
- \+ *lemma* complex.mk_eq_add_mul_I
- \+ *theorem* complex.mul_conj
- \+/\- *lemma* complex.mul_im
- \+ *theorem* complex.mul_inv_cancel
- \+/\- *lemma* complex.mul_re
- \+/\- *lemma* complex.neg_im
- \+/\- *lemma* complex.neg_re
- \+ *def* complex.norm_sq
- \+ *lemma* complex.norm_sq_eq_zero
- \+ *lemma* complex.norm_sq_nonneg
- \+ *lemma* complex.norm_sq_of_real
- \+ *lemma* complex.norm_sq_one
- \+ *lemma* complex.norm_sq_pos
- \+ *lemma* complex.norm_sq_zero
- \- *def* complex.norm_squared
- \- *lemma* complex.norm_squared_pos_of_nonzero
- \+/\- *def* complex.of_real
- \- *lemma* complex.of_real_abs_squared
- \+/\- *lemma* complex.of_real_add
- \+/\- *lemma* complex.of_real_eq_coe
- \+ *theorem* complex.of_real_eq_zero
- \+ *lemma* complex.of_real_im
- \+ *theorem* complex.of_real_inj
- \- *lemma* complex.of_real_injective
- \+ *theorem* complex.of_real_int_cast
- \- *theorem* complex.of_real_int_eq_complex_int
- \+/\- *lemma* complex.of_real_inv
- \+/\- *lemma* complex.of_real_mul
- \+ *theorem* complex.of_real_nat_cast
- \- *theorem* complex.of_real_nat_eq_complex_nat
- \+ *theorem* complex.of_real_ne_zero
- \+/\- *lemma* complex.of_real_neg
- \+/\- *lemma* complex.of_real_one
- \+ *theorem* complex.of_real_rat_cast
- \+ *lemma* complex.of_real_re
- \+/\- *lemma* complex.of_real_sub
- \+/\- *lemma* complex.of_real_zero
- \+/\- *lemma* complex.one_im
- \+/\- *lemma* complex.one_re
- \- *lemma* complex.proj_im
- \- *lemma* complex.proj_re
- \+/\- *lemma* complex.sub_im
- \+/\- *lemma* complex.sub_re
- \+/\- *lemma* complex.zero_im
- \+/\- *lemma* complex.zero_re

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
- \- *lemma* abs_real_eq_abs
- \- *lemma* closure_of_rat_image_le_eq
- \- *lemma* closure_of_rat_image_le_le_eq
- \+ *lemma* closure_of_rat_image_lt
- \- *theorem* coe_rat_eq_of_rat
- \+/\- *lemma* compact_ivl
- \- *lemma* continuous_abs_rat
- \- *lemma* continuous_abs_real
- \- *lemma* continuous_inv_real'
- \- *lemma* continuous_inv_real
- \- *lemma* continuous_mul_real'
- \- *lemma* continuous_mul_real
- \+ *theorem* continuous_of_rat
- \+ *theorem* dense_embedding_of_rat
- \- *lemma* dense_embedding_of_rat
- \- *lemma* dense_embedding_of_rat_of_rat
- \+ *theorem* embedding_of_rat
- \- *lemma* exists_gt_of_rat
- \- *lemma* exists_lt_nat
- \- *lemma* exists_lt_of_rat
- \- *lemma* exists_lt_rat
- \- *lemma* exists_pos_of_rat
- \- *lemma* exists_rat_btwn
- \- *lemma* exists_rat_lt
- \- *def* lift_rat_fun
- \- *lemma* lift_rat_fun_of_rat
- \- *def* lift_rat_op
- \- *lemma* lift_rat_op_of_rat_of_rat
- \- *lemma* map_neg_rat
- \- *lemma* map_neg_real
- \- *lemma* max_of_rat
- \- *lemma* mem_nonneg_of_continuous2
- \- *lemma* mem_uniformity_rat
- \- *lemma* mem_uniformity_real_iff
- \- *lemma* mem_zero_nhd
- \- *lemma* mem_zero_nhd_iff
- \- *lemma* mem_zero_nhd_le
- \- *lemma* min_of_rat
- \- *lemma* nhds_0_eq_zero_nhd
- \- *lemma* nhds_eq_map_zero_nhd
- \- *lemma* nhds_eq_real
- \- *def* nonneg
- \- *lemma* nonneg_antisymm
- \- *def* of_rat
- \- *lemma* of_rat_abs
- \- *lemma* of_rat_add
- \- *lemma* of_rat_inj
- \- *lemma* of_rat_injective
- \- *lemma* of_rat_inv
- \- *lemma* of_rat_le
- \- *lemma* of_rat_lt
- \- *lemma* of_rat_mem_nonneg
- \- *lemma* of_rat_mem_nonneg_iff
- \- *lemma* of_rat_mul
- \- *lemma* of_rat_neg
- \- *lemma* of_rat_one
- \- *lemma* of_rat_sub
- \- *lemma* of_rat_zero
- \- *lemma* preimage_neg_rat
- \- *lemma* pure_zero_le_zero_nhd
- \+ *lemma* rat.continuous_abs
- \+ *lemma* rat.continuous_mul
- \+ *theorem* rat.dist_eq
- \+ *lemma* rat.totally_bounded_Icc
- \+ *lemma* rat.uniform_continuous_abs
- \+ *theorem* rat.uniform_continuous_add
- \+ *theorem* rat.uniform_continuous_neg
- \+ *theorem* real.Cauchy_eq
- \+ *theorem* real.Ioo_eq_ball
- \+ *theorem* real.ball_eq_Ioo
- \+ *lemma* real.continuous_abs
- \+ *lemma* real.continuous_inv'
- \+ *lemma* real.continuous_inv
- \+ *lemma* real.continuous_mul
- \- *theorem* real.le_def
- \- *lemma* real.neg_preimage_closure
- \+ *lemma* real.tendsto_inv
- \+ *lemma* real.totally_bounded_Icc
- \+ *lemma* real.totally_bounded_Ico
- \+ *lemma* real.totally_bounded_Ioo
- \+ *lemma* real.totally_bounded_ball
- \+ *lemma* real.uniform_continuous_abs
- \+ *theorem* real.uniform_continuous_add
- \+ *lemma* real.uniform_continuous_inv
- \+ *lemma* real.uniform_continuous_mul
- \+ *lemma* real.uniform_continuous_mul_const
- \+ *theorem* real.uniform_continuous_neg
- \- *def* real
- \- *lemma* tendsto_add_rat_zero'
- \- *lemma* tendsto_add_rat_zero
- \- *lemma* tendsto_inv_pos_rat
- \- *lemma* tendsto_inv_rat
- \- *lemma* tendsto_inv_real
- \- *lemma* tendsto_mul_bnd_rat'
- \- *lemma* tendsto_mul_bnd_rat
- \- *lemma* tendsto_mul_rat'
- \- *lemma* tendsto_neg_rat_zero
- \- *lemma* tendsto_sub_rat'
- \- *lemma* tendsto_sub_uniformity_zero_nhd'
- \- *lemma* tendsto_sub_uniformity_zero_nhd
- \- *lemma* tendsto_zero_nhds
- \- *lemma* totally_bounded_01_rat
- \- *lemma* two_eq_of_rat_two
- \- *lemma* uniform_continuous_abs_rat
- \- *lemma* uniform_continuous_abs_real
- \- *lemma* uniform_continuous_add_rat
- \- *lemma* uniform_continuous_add_real
- \- *lemma* uniform_continuous_inv_pos_rat
- \- *lemma* uniform_continuous_mul_rat
- \- *lemma* uniform_continuous_neg_rat
- \- *lemma* uniform_continuous_neg_real
- \+ *theorem* uniform_continuous_of_rat
- \- *lemma* uniform_continuous_rat'
- \- *lemma* uniform_continuous_rat
- \- *lemma* uniform_embedding_add_rat
- \- *lemma* uniform_embedding_mul_rat
- \+ *theorem* uniform_embedding_of_rat
- \- *lemma* uniform_embedding_of_rat
- \- *lemma* uniformity_rat
- \- *lemma* zero_le_iff_nonneg
- \- *def* zero_nhd

Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* is_closed_ge'
- \+/\- *lemma* is_closed_le'

Renamed analysis/complex.lean to data/complex.lean




## [2018-01-19 16:18:40-05:00](https://github.com/leanprover-community/mathlib/commit/bb1a9f2)
feat(data/real,*): supporting material for metric spaces
#### Estimated changes
Modified algebra/functions.lean
- \+ *lemma* abs_abs_sub_le_abs_sub
- \+ *lemma* abs_sub_le_iff
- \+ *lemma* abs_sub_lt_iff
- \+ *def* sub_abs_le_abs_sub

Modified algebra/group.lean
- \+ *lemma* sub_right_comm
- \+ *def* sub_sub_cancel
- \- *lemma* sub_sub_swap

Modified algebra/module.lean


Modified algebra/ordered_field.lean
- \+ *lemma* div_le_iff'
- \+ *lemma* div_lt_iff'
- \+ *lemma* le_div_iff'
- \+ *lemma* lt_div_iff'

Modified algebra/ordered_group.lean
- \+ *lemma* add_neg_le_iff_le_add'
- \+ *lemma* add_neg_le_iff_le_add
- \+ *lemma* le_sub_iff_add_le'
- \+ *lemma* le_sub_iff_add_le
- \- *lemma* le_sub_left_iff_add_le
- \- *lemma* le_sub_right_iff_add_le
- \+ *lemma* lt_sub_iff_add_lt'
- \+ *lemma* lt_sub_iff_add_lt
- \- *lemma* lt_sub_left_iff_add_lt
- \- *lemma* lt_sub_right_iff_add_lt
- \+ *lemma* neg_add_le_iff_le_add'
- \- *lemma* neg_add_le_iff_le_add_right
- \+ *lemma* neg_le_sub_iff_le_add'
- \- *lemma* neg_le_sub_iff_le_add_left
- \+ *lemma* neg_lt_sub_iff_lt_add'
- \- *lemma* neg_lt_sub_iff_lt_add_left
- \+ *lemma* sub_le_iff_le_add'
- \+ *lemma* sub_le_iff_le_add
- \- *lemma* sub_left_le_iff_le_add
- \- *lemma* sub_left_lt_iff_lt_add
- \+ *lemma* sub_lt_iff_lt_add'
- \+ *lemma* sub_lt_iff_lt_add
- \- *lemma* sub_right_le_iff_le_add
- \- *lemma* sub_right_lt_iff_lt_add

Modified analysis/ennreal.lean


Modified analysis/limits.lean


Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/metric_space.lean
- \+ *theorem* abs_dist_sub_le
- \+ *def* ball
- \+ *theorem* ball_disjoint
- \+ *theorem* ball_disjoint_same
- \+ *theorem* ball_eq_empty_iff_nonpos
- \+ *theorem* ball_half_subset
- \+ *theorem* ball_mem_nhds
- \+ *theorem* ball_subset
- \+ *theorem* ball_subset_ball
- \+ *lemma* cauchy_of_metric
- \+ *theorem* continuous_of_metric
- \+ *theorem* dist_eq_zero
- \- *theorem* dist_eq_zero_iff
- \+ *theorem* dist_le_zero
- \- *theorem* dist_le_zero_iff
- \+ *theorem* dist_mem_uniformity
- \+ *theorem* dist_pos
- \- *theorem* dist_pos_of_ne
- \+ *theorem* dist_triangle_left
- \+ *theorem* dist_triangle_right
- \+ *theorem* exists_ball_subset_ball
- \+ *theorem* is_closed_ball
- \- *theorem* is_closed_closed_ball
- \+ *theorem* is_open_ball
- \+/\- *theorem* is_open_metric
- \- *theorem* is_open_open_ball
- \+ *theorem* mem_ball'
- \+ *theorem* mem_ball
- \+ *theorem* mem_ball_comm
- \+ *theorem* mem_ball_self
- \+ *theorem* mem_closed_ball
- \+ *theorem* mem_nhds_iff_metric
- \- *theorem* mem_nhds_sets_iff_metric
- \- *theorem* mem_open_ball
- \+ *def* metric_space.induced
- \+ *theorem* metric_space.induced_uniform_embedding
- \+ *def* metric_space.replace_uniformity
- \- *theorem* ne_of_dist_pos
- \+/\- *theorem* nhds_eq_metric
- \- *def* open_ball
- \- *theorem* open_ball_eq_empty_of_nonpos
- \- *theorem* open_ball_subset_open_ball_of_le
- \+ *theorem* pos_of_mem_ball
- \- *theorem* pos_of_mem_open_ball
- \+ *theorem* real.dist_eq
- \+ *theorem* subtype.dist_eq
- \+ *theorem* swap_dist
- \+ *theorem* tendsto_nhds_of_metric
- \+ *theorem* totally_bounded_of_metric
- \+ *theorem* uniform_continuous_of_metric
- \+ *theorem* uniform_embedding_of_metric
- \+ *theorem* uniformity_dist_of_mem_uniformity
- \+ *theorem* zero_eq_dist
- \- *theorem* zero_eq_dist_iff

Modified analysis/real.lean
- \- *lemma* neg_preimage_closure
- \- *lemma* preimage_neg_real
- \+ *lemma* real.neg_preimage_closure
- \- *lemma* tendsto_of_uniform_continuous_subtype

Modified analysis/topology/continuity.lean
- \+ *lemma* continuous.comp
- \+ *lemma* continuous.prod_mk
- \+ *lemma* continuous.tendsto
- \- *lemma* continuous_compose
- \- *lemma* continuous_eq_le_coinduced
- \+ *lemma* continuous_iff_le_coinduced
- \- *lemma* continuous_iff_of_embedding
- \+/\- *lemma* continuous_inf_rng_left
- \+/\- *lemma* continuous_inf_rng_right
- \+ *lemma* continuous_le_dom
- \+ *lemma* continuous_le_rng
- \- *lemma* continuous_prod_mk
- \+/\- *lemma* continuous_sup_dom_left
- \+/\- *lemma* continuous_sup_dom_right
- \- *lemma* dense_embedding.closure_image_univ
- \+ *lemma* dense_embedding.closure_range
- \+/\- *lemma* dense_embedding.inj_iff
- \+ *theorem* dense_embedding.mk'
- \+ *lemma* embedding.continuous_iff
- \+ *lemma* embedding.tendsto_nhds_iff
- \+/\- *lemma* is_open_prod
- \- *lemma* tendsto_nhds_iff_of_embedding

Modified analysis/topology/infinite_sum.lean


Modified analysis/topology/topological_space.lean
- \+ *theorem* mem_closure_iff
- \+ *theorem* mem_closure_iff_nhds

Modified analysis/topology/topological_structures.lean
- \+ *lemma* filter.map_neg
- \+ *theorem* induced_orderable_topology'
- \+ *theorem* induced_orderable_topology
- \+ *lemma* neg_preimage_closure
- \+ *lemma* preimage_neg
- \+ *theorem* uniform_add_group.mk'

Modified analysis/topology/uniform_space.lean
- \+ *theorem* Cauchy.mem_uniformity'
- \+ *theorem* Cauchy.mem_uniformity
- \+/\- *lemma* Cauchy.pure_cauchy_dense
- \- *lemma* continuous_of_uniform
- \- *lemma* dense_embedding_of_uniform_embedding
- \+ *theorem* id_rel_subset
- \+ *theorem* le_nhds_lim_of_cauchy
- \+ *theorem* mem_comp_rel
- \+ *theorem* mem_id_rel
- \+/\- *lemma* mem_nhds_left
- \+/\- *lemma* mem_nhds_right
- \+ *def* separated
- \+ *theorem* separated_def'
- \+ *theorem* separated_def
- \+ *lemma* tendsto_of_uniform_continuous_subtype
- \+ *theorem* totally_bounded_iff_subset
- \+ *lemma* totally_bounded_preimage
- \+ *lemma* uniform_continuous.comp
- \+ *lemma* uniform_continuous.continuous
- \+ *lemma* uniform_continuous.prod_mk
- \+ *def* uniform_continuous
- \- *lemma* uniform_continuous_compose
- \+ *theorem* uniform_continuous_def
- \- *lemma* uniform_continuous_of_embedding
- \- *lemma* uniform_continuous_prod_mk
- \+ *lemma* uniform_embedding.dense_embedding
- \+ *lemma* uniform_embedding.prod
- \+ *lemma* uniform_embedding.uniform_continuous
- \+ *lemma* uniform_embedding.uniform_continuous_iff
- \+ *def* uniform_embedding
- \+ *theorem* uniform_embedding_def'
- \+ *theorem* uniform_embedding_def
- \- *lemma* uniform_embedding_prod
- \+ *def* uniform_space.core.mk'

Modified data/analysis/filter.lean


Modified data/equiv.lean


Modified data/fp/basic.lean


Modified data/hash_map.lean


Modified data/int/basic.lean
- \+ *theorem* int.cast_injective

Modified data/list/basic.lean


Modified data/list/perm.lean


Modified data/nat/cast.lean
- \+ *theorem* nat.cast_injective

Modified data/rat.lean
- \+ *theorem* rat.cast_injective

Modified data/real.lean
- \- *theorem* NEW.real.Inf_le
- \- *theorem* NEW.real.Sup_le
- \- *theorem* NEW.real.Sup_le_ub
- \- *theorem* NEW.real.add_lt_add_iff_left
- \- *theorem* NEW.real.ceil_add_int
- \- *theorem* NEW.real.ceil_coe
- \- *theorem* NEW.real.ceil_le
- \- *theorem* NEW.real.ceil_lt_add_one
- \- *theorem* NEW.real.ceil_mono
- \- *theorem* NEW.real.ceil_sub_int
- \- *theorem* NEW.real.exists_floor
- \- *theorem* NEW.real.exists_int_gt
- \- *theorem* NEW.real.exists_int_lt
- \- *theorem* NEW.real.exists_nat_gt
- \- *theorem* NEW.real.exists_pos_rat_lt
- \- *theorem* NEW.real.exists_rat_btwn
- \- *theorem* NEW.real.exists_rat_gt
- \- *theorem* NEW.real.exists_rat_lt
- \- *theorem* NEW.real.exists_rat_near'
- \- *theorem* NEW.real.exists_rat_near
- \- *theorem* NEW.real.exists_sup
- \- *theorem* NEW.real.floor_add_int
- \- *theorem* NEW.real.floor_coe
- \- *theorem* NEW.real.floor_le
- \- *theorem* NEW.real.floor_lt
- \- *theorem* NEW.real.floor_mono
- \- *theorem* NEW.real.floor_sub_int
- \- *theorem* NEW.real.inv_mk
- \- *theorem* NEW.real.inv_zero
- \- *theorem* NEW.real.lb_le_Inf
- \- *theorem* NEW.real.le_Inf
- \- *theorem* NEW.real.le_Sup
- \- *theorem* NEW.real.le_ceil
- \- *theorem* NEW.real.le_floor
- \- *theorem* NEW.real.le_mk_of_forall_le
- \- *theorem* NEW.real.lt_ceil
- \- *theorem* NEW.real.lt_floor_add_one
- \- *theorem* NEW.real.lt_succ_floor
- \- *def* NEW.real.mk
- \- *theorem* NEW.real.mk_add
- \- *theorem* NEW.real.mk_eq
- \- *theorem* NEW.real.mk_eq_mk
- \- *theorem* NEW.real.mk_eq_zero
- \- *theorem* NEW.real.mk_le
- \- *theorem* NEW.real.mk_le_of_forall_le
- \- *theorem* NEW.real.mk_lt
- \- *theorem* NEW.real.mk_mul
- \- *theorem* NEW.real.mk_neg
- \- *theorem* NEW.real.mk_pos
- \- *def* NEW.real.of_rat
- \- *theorem* NEW.real.of_rat_add
- \- *theorem* NEW.real.of_rat_eq_cast
- \- *theorem* NEW.real.of_rat_lt
- \- *theorem* NEW.real.of_rat_mul
- \- *theorem* NEW.real.of_rat_neg
- \- *theorem* NEW.real.of_rat_one
- \- *theorem* NEW.real.of_rat_sub
- \- *theorem* NEW.real.of_rat_zero
- \- *theorem* NEW.real.sub_one_lt_floor
- \- *def* NEW.real
- \+ *theorem* cau_seq.abs_pos_of_not_lim_zero
- \+ *theorem* cau_seq.add_apply
- \+ *theorem* cau_seq.add_lim_zero
- \+ *theorem* cau_seq.add_pos
- \+ *theorem* cau_seq.bounded'
- \+ *theorem* cau_seq.bounded
- \+ *theorem* cau_seq.cauchy
- \+ *theorem* cau_seq.cauchy₂
- \+ *theorem* cau_seq.cauchy₃
- \+ *def* cau_seq.const
- \+ *theorem* cau_seq.const_add
- \+ *theorem* cau_seq.const_apply
- \+ *theorem* cau_seq.const_equiv
- \+ *theorem* cau_seq.const_inj
- \+ *theorem* cau_seq.const_le
- \+ *theorem* cau_seq.const_lim_zero
- \+ *theorem* cau_seq.const_lt
- \+ *theorem* cau_seq.const_mul
- \+ *theorem* cau_seq.const_neg
- \+ *theorem* cau_seq.const_pos
- \+ *theorem* cau_seq.const_sub
- \+ *theorem* cau_seq.equiv_def₃
- \+ *theorem* cau_seq.exists_gt
- \+ *theorem* cau_seq.exists_lt
- \+ *theorem* cau_seq.ext
- \+ *def* cau_seq.inv
- \+ *theorem* cau_seq.inv_apply
- \+ *theorem* cau_seq.inv_aux
- \+ *theorem* cau_seq.inv_mul_cancel
- \+ *theorem* cau_seq.le_antisymm
- \+ *theorem* cau_seq.le_total
- \+ *def* cau_seq.lim_zero
- \+ *theorem* cau_seq.lim_zero_congr
- \+ *theorem* cau_seq.lt_irrefl
- \+ *theorem* cau_seq.lt_of_eq_of_lt
- \+ *theorem* cau_seq.lt_of_lt_of_eq
- \+ *theorem* cau_seq.lt_total
- \+ *theorem* cau_seq.lt_trans
- \+ *def* cau_seq.mk_of_near
- \+ *theorem* cau_seq.mk_of_near_equiv
- \+ *theorem* cau_seq.mk_of_near_fun
- \+ *theorem* cau_seq.mul_apply
- \+ *theorem* cau_seq.mul_lim_zero
- \+ *theorem* cau_seq.mul_pos
- \+ *theorem* cau_seq.neg_apply
- \+ *theorem* cau_seq.neg_lim_zero
- \+ *theorem* cau_seq.not_lim_zero_of_pos
- \+ *def* cau_seq.of_eq
- \+ *theorem* cau_seq.one_apply
- \+ *def* cau_seq.pos
- \+ *theorem* cau_seq.pos_add_lim_zero
- \+ *theorem* cau_seq.sub_apply
- \+ *theorem* cau_seq.sub_lim_zero
- \+ *theorem* cau_seq.trichotomy
- \+ *theorem* cau_seq.zero_apply
- \+ *theorem* cau_seq.zero_lim_zero
- \+ *def* cau_seq
- \- *theorem* rat.cau_seq.abs_pos_of_not_lim_zero
- \- *theorem* rat.cau_seq.add_apply
- \- *theorem* rat.cau_seq.add_lim_zero
- \- *theorem* rat.cau_seq.add_pos
- \- *theorem* rat.cau_seq.bounded'
- \- *theorem* rat.cau_seq.bounded
- \- *theorem* rat.cau_seq.cauchy
- \- *theorem* rat.cau_seq.cauchy₂
- \- *theorem* rat.cau_seq.cauchy₃
- \- *theorem* rat.cau_seq.ext
- \- *def* rat.cau_seq.inv
- \- *theorem* rat.cau_seq.inv_apply
- \- *theorem* rat.cau_seq.inv_aux
- \- *theorem* rat.cau_seq.inv_mul_cancel
- \- *theorem* rat.cau_seq.le_antisymm
- \- *theorem* rat.cau_seq.le_total
- \- *def* rat.cau_seq.lim_zero
- \- *theorem* rat.cau_seq.lim_zero_congr
- \- *theorem* rat.cau_seq.lt_irrefl
- \- *theorem* rat.cau_seq.lt_of_eq_of_lt
- \- *theorem* rat.cau_seq.lt_of_lt_of_eq
- \- *theorem* rat.cau_seq.lt_trans
- \- *theorem* rat.cau_seq.mul_apply
- \- *theorem* rat.cau_seq.mul_lim_zero
- \- *theorem* rat.cau_seq.mul_pos
- \- *theorem* rat.cau_seq.neg_apply
- \- *theorem* rat.cau_seq.neg_lim_zero
- \- *theorem* rat.cau_seq.not_lim_zero_of_pos
- \- *def* rat.cau_seq.of_eq
- \- *def* rat.cau_seq.of_rat
- \- *theorem* rat.cau_seq.of_rat_add
- \- *theorem* rat.cau_seq.of_rat_apply
- \- *theorem* rat.cau_seq.of_rat_lim_zero
- \- *theorem* rat.cau_seq.of_rat_mul
- \- *theorem* rat.cau_seq.of_rat_neg
- \- *theorem* rat.cau_seq.of_rat_pos
- \- *theorem* rat.cau_seq.of_rat_sub
- \- *theorem* rat.cau_seq.one_apply
- \- *def* rat.cau_seq.pos
- \- *theorem* rat.cau_seq.pos_add_lim_zero
- \- *theorem* rat.cau_seq.sub_apply
- \- *theorem* rat.cau_seq.sub_lim_zero
- \- *theorem* rat.cau_seq.trichotomy
- \- *theorem* rat.cau_seq.zero_apply
- \- *theorem* rat.cau_seq.zero_lim_zero
- \- *def* rat.cau_seq
- \+ *theorem* rat_add_continuous_lemma
- \+ *theorem* rat_inv_continuous_lemma
- \+ *theorem* rat_mul_continuous_lemma
- \+ *theorem* real.Inf_le
- \+ *theorem* real.Inf_lt
- \+ *theorem* real.Sup_le
- \+ *theorem* real.Sup_le_ub
- \+ *theorem* real.add_lt_add_iff_left
- \+ *theorem* real.cau_seq_converges
- \+ *theorem* real.ceil_add_int
- \+ *theorem* real.ceil_coe
- \+ *theorem* real.ceil_le
- \+ *theorem* real.ceil_lt_add_one
- \+ *theorem* real.ceil_mono
- \+ *theorem* real.ceil_sub_int
- \+ *theorem* real.equiv_lim
- \+ *theorem* real.exists_floor
- \+ *theorem* real.exists_int_gt
- \+ *theorem* real.exists_int_lt
- \+ *theorem* real.exists_nat_gt
- \+ *theorem* real.exists_pos_rat_lt
- \+ *theorem* real.exists_rat_btwn
- \+ *theorem* real.exists_rat_gt
- \+ *theorem* real.exists_rat_lt
- \+ *theorem* real.exists_rat_near'
- \+ *theorem* real.exists_rat_near
- \+ *theorem* real.exists_sup
- \+ *theorem* real.floor_add_int
- \+ *theorem* real.floor_coe
- \+ *theorem* real.floor_le
- \+ *theorem* real.floor_lt
- \+ *theorem* real.floor_mono
- \+ *theorem* real.floor_nonneg
- \+ *theorem* real.floor_sub_int
- \+ *theorem* real.inv_mk
- \+ *theorem* real.inv_zero
- \+ *theorem* real.lb_le_Inf
- \+ *theorem* real.le_Inf
- \+ *theorem* real.le_Sup
- \+ *theorem* real.le_ceil
- \+ *theorem* real.le_floor
- \+ *theorem* real.le_mk_of_forall_le
- \+ *theorem* real.lt_Sup
- \+ *theorem* real.lt_ceil
- \+ *theorem* real.lt_floor_add_one
- \+ *theorem* real.lt_succ_floor
- \+ *def* real.mk
- \+ *theorem* real.mk_add
- \+ *theorem* real.mk_eq
- \+ *theorem* real.mk_eq_mk
- \+ *theorem* real.mk_eq_zero
- \+ *theorem* real.mk_le
- \+ *theorem* real.mk_le_of_forall_le
- \+ *theorem* real.mk_lt
- \+ *theorem* real.mk_mul
- \+ *theorem* real.mk_neg
- \+ *theorem* real.mk_pos
- \+ *def* real.of_rat
- \+ *theorem* real.of_rat_add
- \+ *theorem* real.of_rat_eq_cast
- \+ *theorem* real.of_rat_lt
- \+ *theorem* real.of_rat_mul
- \+ *theorem* real.of_rat_neg
- \+ *theorem* real.of_rat_one
- \+ *theorem* real.of_rat_sub
- \+ *theorem* real.of_rat_zero
- \+ *theorem* real.sub_one_lt_floor
- \+ *def* real

Modified data/set/basic.lean
- \+ *theorem* set.image_preimage_eq_inter_range
- \- *theorem* set.image_preimage_eq_inter_rng
- \+ *theorem* set.image_univ
- \+/\- *theorem* set.mem_range
- \+/\- *theorem* set.preimage_image_eq
- \+ *theorem* set.prod_range_range_eq
- \- *theorem* set.quot_mk_image_univ_eq
- \+ *theorem* set.quot_mk_range_eq
- \+ *theorem* set.range_comp
- \- *theorem* set.range_compose
- \- *theorem* set.range_eq_image
- \+ *theorem* set.range_subset_iff

Modified data/set/finite.lean
- \+ *theorem* set.finite_preimage

Modified data/set/lattice.lean
- \+/\- *theorem* set.Inter_eq_sInter_image
- \+/\- *theorem* set.Union_eq_sUnion_image
- \+ *theorem* set.bInter_subset_bInter_left
- \+ *theorem* set.bUnion_subset_bUnion_left
- \+ *lemma* set.subtype_val_range

Modified logic/basic.lean
- \+ *def* Exists.imp
- \- *theorem* exists_of_exists
- \- *theorem* forall_of_forall

Modified logic/function.lean
- \+ *lemma* function.bijective_iff_has_inverse
- \+ *lemma* function.injective_iff_has_left_inverse
- \+ *lemma* function.left_inverse_surj_inv
- \+ *lemma* function.surjective_iff_has_right_inverse

Modified order/filter.lean
- \+ *lemma* filter.filter.ext
- \+ *lemma* filter.filter_eq_iff
- \+ *theorem* filter.le_def
- \+ *lemma* filter.mem_Sup_sets
- \- *lemma* filter.mem_at_top_iff
- \+ *lemma* filter.mem_at_top_sets
- \+/\- *lemma* filter.mem_bind_sets
- \- *lemma* filter.mem_lift'_iff
- \+ *lemma* filter.mem_lift'_sets
- \- *lemma* filter.mem_lift_iff
- \+ *lemma* filter.mem_lift_sets
- \+/\- *lemma* filter.mem_map
- \+ *lemma* filter.mem_principal_self
- \+/\- *lemma* filter.mem_principal_sets
- \- *lemma* filter.mem_prod_iff
- \+ *lemma* filter.mem_prod_sets
- \+ *lemma* filter.mem_pure_sets
- \+/\- *lemma* filter.mem_return_sets
- \+ *lemma* filter.mem_supr_sets
- \- *theorem* filter.mem_vmap
- \+ *theorem* filter.mem_vmap_sets
- \+/\- *lemma* filter.monotone_map
- \+/\- *lemma* filter.monotone_vmap
- \+ *lemma* filter.pure_neq_bot
- \- *lemma* filter.return_neq_bot
- \+ *lemma* filter.tendsto.comp
- \+ *lemma* filter.tendsto.prod_mk
- \- *lemma* filter.tendsto_compose
- \+ *lemma* filter.tendsto_def
- \+ *lemma* filter.tendsto_iff_vmap
- \+/\- *lemma* filter.tendsto_inf
- \- *lemma* filter.tendsto_inf_left
- \+/\- *lemma* filter.tendsto_infi'
- \+/\- *lemma* filter.tendsto_infi
- \+ *lemma* filter.tendsto_le_left
- \+ *lemma* filter.tendsto_le_right
- \+/\- *lemma* filter.tendsto_principal
- \+/\- *lemma* filter.tendsto_principal_principal
- \- *lemma* filter.tendsto_prod_mk

Modified order/galois_connection.lean




## [2018-01-17 17:53:52-05:00](https://github.com/leanprover-community/mathlib/commit/0ac694c)
fix(tactic/interactive): update to lean
#### Estimated changes
Modified tactic/interactive.lean




## [2018-01-16 16:08:50-05:00](https://github.com/leanprover-community/mathlib/commit/e11da6e)
feat(data/real): variants on archimedean property
#### Estimated changes
Modified data/real.lean
- \- *theorem* NEW.real.archimedean
- \+ *theorem* NEW.real.exists_int_gt
- \+ *theorem* NEW.real.exists_int_lt
- \+ *theorem* NEW.real.exists_nat_gt
- \+ *theorem* NEW.real.exists_rat_gt
- \+ *theorem* NEW.real.exists_rat_lt



## [2018-01-16 05:29:44-05:00](https://github.com/leanprover-community/mathlib/commit/d84dfb1)
feat(data/real): completeness of the (new) real numbers
#### Estimated changes
Modified algebra/group.lean
- \- *theorem* le_sub_iff_add_le
- \+ *lemma* sub_add_sub_cancel'
- \- *theorem* sub_le_iff_le_add

Modified algebra/ordered_field.lean
- \+ *lemma* inv_le
- \- *lemma* inv_le_inv'
- \+/\- *lemma* inv_le_inv
- \+ *lemma* inv_le_inv_of_le
- \+ *lemma* inv_lt
- \+ *lemma* le_inv
- \+ *lemma* lt_inv

Modified algebra/ordered_group.lean
- \+/\- *lemma* le_neg_add_iff_add_le
- \+ *theorem* le_sub
- \+/\- *lemma* le_sub_right_iff_add_le
- \+/\- *lemma* lt_sub_right_iff_add_lt
- \+/\- *lemma* sub_right_le_iff_le_add
- \+/\- *lemma* sub_right_lt_iff_lt_add

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
- \+ *theorem* int.add_one_le_iff
- \+ *theorem* int.exists_greatest_of_bdd
- \+ *theorem* int.exists_least_of_bdd
- \+ *theorem* int.le_sub_one_iff
- \+ *theorem* int.lt_add_one_iff
- \+/\- *theorem* int.of_nat_add_neg_succ_of_nat_of_ge
- \+/\- *theorem* int.of_nat_add_neg_succ_of_nat_of_lt
- \+ *theorem* int.sub_one_le_iff

Modified data/int/order.lean
- \- *theorem* int.exists_greatest_of_bdd
- \- *theorem* int.exists_least_of_bdd

Modified data/pnat.lean
- \+ *theorem* pnat.coe_nat_coe

Modified data/rat.lean


Modified data/real.lean
- \+ *theorem* NEW.real.Inf_le
- \+ *theorem* NEW.real.Sup_le
- \+ *theorem* NEW.real.Sup_le_ub
- \+ *theorem* NEW.real.ceil_add_int
- \+ *theorem* NEW.real.ceil_coe
- \+ *theorem* NEW.real.ceil_le
- \+ *theorem* NEW.real.ceil_lt_add_one
- \+ *theorem* NEW.real.ceil_mono
- \+ *theorem* NEW.real.ceil_sub_int
- \+ *theorem* NEW.real.exists_floor
- \+ *theorem* NEW.real.exists_sup
- \+ *theorem* NEW.real.floor_add_int
- \+ *theorem* NEW.real.floor_coe
- \+ *theorem* NEW.real.floor_le
- \+ *theorem* NEW.real.floor_lt
- \+ *theorem* NEW.real.floor_mono
- \+ *theorem* NEW.real.floor_sub_int
- \+ *theorem* NEW.real.lb_le_Inf
- \+ *theorem* NEW.real.le_Inf
- \+ *theorem* NEW.real.le_Sup
- \+ *theorem* NEW.real.le_ceil
- \+ *theorem* NEW.real.le_floor
- \+ *theorem* NEW.real.le_mk_of_forall_le
- \+ *theorem* NEW.real.lt_ceil
- \+ *theorem* NEW.real.lt_floor_add_one
- \+ *theorem* NEW.real.lt_succ_floor
- \+ *theorem* NEW.real.mk_le_of_forall_le
- \+ *theorem* NEW.real.sub_one_lt_floor



## [2018-01-15 07:59:59-05:00](https://github.com/leanprover-community/mathlib/commit/04cac95)
feat(data/real): reals from first principles
This is beginning work on a simpler implementation of real numbers, based on Cauchy sequences, to help alleviate some of the issues we have seen with loading times and timeouts when working with real numbers. If everything goes according to plan, `analysis/real.lean` will be the development for the topology of the reals, but the initial construction will have no topology prerequisites.
#### Estimated changes
Modified algebra/functions.lean
- \+ *lemma* abs_pos_iff

Added algebra/linear_algebra/dimension.lean
- \+ *def* vector_space.dim

Modified algebra/linear_algebra/linear_map_module.lean


Modified analysis/ennreal.lean


Modified analysis/real.lean


Modified data/bool.lean
- \+ *lemma* bool.of_to_bool_iff

Modified data/int/basic.lean
- \+/\- *theorem* int.cast_id
- \+ *theorem* int.eq_cast

Modified data/nat/basic.lean


Modified data/nat/cast.lean
- \+/\- *theorem* nat.cast_id
- \+ *theorem* nat.eq_cast'
- \+ *theorem* nat.eq_cast

Modified data/rat.lean
- \+ *theorem* rat.eq_cast
- \+ *theorem* rat.eq_cast_of_ne_zero

Added data/real.lean
- \+ *theorem* NEW.real.add_lt_add_iff_left
- \+ *theorem* NEW.real.archimedean
- \+ *theorem* NEW.real.exists_pos_rat_lt
- \+ *theorem* NEW.real.exists_rat_btwn
- \+ *theorem* NEW.real.exists_rat_near'
- \+ *theorem* NEW.real.exists_rat_near
- \+ *theorem* NEW.real.inv_mk
- \+ *theorem* NEW.real.inv_zero
- \+ *def* NEW.real.mk
- \+ *theorem* NEW.real.mk_add
- \+ *theorem* NEW.real.mk_eq
- \+ *theorem* NEW.real.mk_eq_mk
- \+ *theorem* NEW.real.mk_eq_zero
- \+ *theorem* NEW.real.mk_le
- \+ *theorem* NEW.real.mk_lt
- \+ *theorem* NEW.real.mk_mul
- \+ *theorem* NEW.real.mk_neg
- \+ *theorem* NEW.real.mk_pos
- \+ *def* NEW.real.of_rat
- \+ *theorem* NEW.real.of_rat_add
- \+ *theorem* NEW.real.of_rat_eq_cast
- \+ *theorem* NEW.real.of_rat_lt
- \+ *theorem* NEW.real.of_rat_mul
- \+ *theorem* NEW.real.of_rat_neg
- \+ *theorem* NEW.real.of_rat_one
- \+ *theorem* NEW.real.of_rat_sub
- \+ *theorem* NEW.real.of_rat_zero
- \+ *def* NEW.real
- \+ *theorem* exists_forall_ge_and
- \+ *theorem* rat.cau_seq.abs_pos_of_not_lim_zero
- \+ *theorem* rat.cau_seq.add_apply
- \+ *theorem* rat.cau_seq.add_lim_zero
- \+ *theorem* rat.cau_seq.add_pos
- \+ *theorem* rat.cau_seq.bounded'
- \+ *theorem* rat.cau_seq.bounded
- \+ *theorem* rat.cau_seq.cauchy
- \+ *theorem* rat.cau_seq.cauchy₂
- \+ *theorem* rat.cau_seq.cauchy₃
- \+ *theorem* rat.cau_seq.ext
- \+ *def* rat.cau_seq.inv
- \+ *theorem* rat.cau_seq.inv_apply
- \+ *theorem* rat.cau_seq.inv_aux
- \+ *theorem* rat.cau_seq.inv_mul_cancel
- \+ *theorem* rat.cau_seq.le_antisymm
- \+ *theorem* rat.cau_seq.le_total
- \+ *def* rat.cau_seq.lim_zero
- \+ *theorem* rat.cau_seq.lim_zero_congr
- \+ *theorem* rat.cau_seq.lt_irrefl
- \+ *theorem* rat.cau_seq.lt_of_eq_of_lt
- \+ *theorem* rat.cau_seq.lt_of_lt_of_eq
- \+ *theorem* rat.cau_seq.lt_trans
- \+ *theorem* rat.cau_seq.mul_apply
- \+ *theorem* rat.cau_seq.mul_lim_zero
- \+ *theorem* rat.cau_seq.mul_pos
- \+ *theorem* rat.cau_seq.neg_apply
- \+ *theorem* rat.cau_seq.neg_lim_zero
- \+ *theorem* rat.cau_seq.not_lim_zero_of_pos
- \+ *def* rat.cau_seq.of_eq
- \+ *def* rat.cau_seq.of_rat
- \+ *theorem* rat.cau_seq.of_rat_add
- \+ *theorem* rat.cau_seq.of_rat_apply
- \+ *theorem* rat.cau_seq.of_rat_lim_zero
- \+ *theorem* rat.cau_seq.of_rat_mul
- \+ *theorem* rat.cau_seq.of_rat_neg
- \+ *theorem* rat.cau_seq.of_rat_pos
- \+ *theorem* rat.cau_seq.of_rat_sub
- \+ *theorem* rat.cau_seq.one_apply
- \+ *def* rat.cau_seq.pos
- \+ *theorem* rat.cau_seq.pos_add_lim_zero
- \+ *theorem* rat.cau_seq.sub_apply
- \+ *theorem* rat.cau_seq.sub_lim_zero
- \+ *theorem* rat.cau_seq.trichotomy
- \+ *theorem* rat.cau_seq.zero_apply
- \+ *theorem* rat.cau_seq.zero_lim_zero
- \+ *def* rat.cau_seq

Modified pending/default.lean
- \- *lemma* of_to_bool_iff

Modified tactic/alias.lean




## [2018-01-14 21:59:50-05:00](https://github.com/leanprover-community/mathlib/commit/65db966)
feat(algebra/field): more division lemmas
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.single_le_sum

Modified algebra/field.lean
- \- *lemma* abs_inv
- \+ *lemma* add_div
- \+ *lemma* div_div_cancel
- \+ *lemma* div_div_div_cancel_right
- \+ *lemma* div_eq_div_iff
- \+ *lemma* div_eq_mul_inv
- \+ *lemma* div_eq_zero_iff
- \- *lemma* div_le_iff_le_mul_of_pos
- \+ *lemma* div_mul_comm
- \+ *lemma* div_mul_div_cancel
- \+ *lemma* div_ne_zero
- \+ *lemma* div_ne_zero_iff
- \+ *lemma* div_neg
- \+ *lemma* div_right_comm
- \+ *lemma* div_right_inj
- \+/\- *lemma* division_ring.inv_comm_of_comm
- \- *lemma* division_ring.inv_div
- \+ *lemma* division_ring.inv_eq_iff
- \+ *lemma* division_ring.inv_inj
- \- *lemma* division_ring.neg_inv
- \+ *theorem* divp_eq_div
- \+ *theorem* divp_mk0
- \+ *lemma* field.div_div_cancel
- \+ *lemma* field.div_div_div_cancel_right
- \+ *lemma* field.div_mul_div_cancel
- \+ *lemma* field.div_right_comm
- \+ *lemma* inv_add_inv
- \+ *lemma* inv_div
- \+ *lemma* inv_div_left
- \- *lemma* inv_le_inv
- \- *lemma* inv_lt_one
- \- *lemma* inv_neg
- \- *lemma* inv_pos
- \+ *lemma* inv_sub_inv
- \- *lemma* ivl_stretch
- \- *lemma* ivl_translate
- \- *lemma* le_div_iff_mul_le_of_pos
- \- *lemma* lt_div_iff
- \+ *lemma* mul_comm_div
- \+ *lemma* mul_div_comm
- \+ *lemma* mul_div_right_comm
- \+ *lemma* neg_inv
- \- *lemma* one_lt_inv
- \+ *lemma* sub_div
- \+ *theorem* units.inv_eq_inv
- \+ *def* units.mk0
- \+ *theorem* units.mk0_inv
- \+ *theorem* units.mk0_val
- \+ *theorem* units.ne_zero

Modified algebra/functions.lean
- \+ *def* abs_add

Modified algebra/group.lean
- \+ *def* divp
- \+ *theorem* divp_assoc
- \+ *theorem* divp_eq_one
- \+ *theorem* divp_mul_cancel
- \+ *theorem* divp_one
- \+ *theorem* divp_right_inj
- \+ *theorem* divp_self
- \+ *theorem* mul_divp_cancel
- \+/\- *theorem* mul_left_inj
- \+/\- *theorem* mul_right_inj
- \+ *theorem* one_divp
- \+ *theorem* units.ext
- \+ *lemma* units.inv_coe
- \+ *lemma* units.inv_mul
- \+ *lemma* units.inv_mul_cancel_left
- \+ *lemma* units.inv_mul_cancel_right
- \+ *lemma* units.mul_coe
- \+ *lemma* units.mul_inv
- \+ *lemma* units.mul_inv_cancel_left
- \+ *lemma* units.mul_inv_cancel_right
- \+ *theorem* units.mul_left_inj
- \+ *theorem* units.mul_right_inj
- \+ *lemma* units.one_coe
- \+ *lemma* units.val_coe

Modified algebra/group_power.lean


Modified algebra/linear_algebra/basic.lean
- \- *lemma* is_submodule_span

Modified algebra/module.lean


Modified algebra/order.lean
- \+ *lemma* exists_ge_of_linear

Added algebra/ordered_field.lean
- \+ *lemma* abs_inv
- \+ *lemma* div_le_div_left
- \+ *lemma* div_le_div_right
- \+ *lemma* div_le_div_right_of_neg
- \+ *lemma* div_le_iff
- \+ *lemma* div_le_iff_of_neg
- \+ *lemma* div_le_one_iff_le
- \+ *lemma* div_lt_div'
- \+ *lemma* div_lt_div
- \+ *lemma* div_lt_div_iff
- \+ *lemma* div_lt_div_left
- \+ *lemma* div_lt_div_right
- \+ *lemma* div_lt_div_right_of_neg
- \+ *lemma* div_lt_iff
- \+ *lemma* div_lt_iff_of_neg
- \+ *lemma* div_lt_one_iff_lt
- \+ *def* div_nonneg
- \+ *def* div_pos
- \+ *def* half_lt_self
- \+ *lemma* half_pos
- \+ *lemma* inv_le_inv'
- \+ *lemma* inv_le_inv
- \+ *lemma* inv_lt_inv
- \+ *lemma* inv_lt_one
- \+ *lemma* inv_neg
- \+ *lemma* inv_pos
- \+ *lemma* ivl_stretch
- \+ *lemma* ivl_translate
- \+ *lemma* le_div_iff
- \+ *lemma* lt_div_iff
- \+ *lemma* one_div_le_one_div
- \+ *lemma* one_div_lt_one_div
- \+ *lemma* one_le_div_iff_le
- \+ *lemma* one_lt_div_iff_lt
- \+ *lemma* one_lt_inv

Modified algebra/ordered_group.lean


Modified algebra/ordered_ring.lean
- \+ *lemma* lt_add_one
- \+/\- *lemma* one_lt_two

Modified algebra/ring.lean
- \- *lemma* add_div
- \- *lemma* div_eq_mul_inv
- \- *lemma* neg_inv
- \- *theorem* units.ext
- \- *lemma* units.inv_coe
- \- *lemma* units.inv_mul
- \- *lemma* units.mul_coe
- \- *lemma* units.mul_inv
- \- *lemma* units.one_coe
- \- *lemma* units.val_coe



## [2018-01-14 17:36:13-05:00](https://github.com/leanprover-community/mathlib/commit/0d6d12a)
feat(tactic/interactive): replace tactic
#### Estimated changes
Modified tactic/interactive.lean




## [2018-01-14 01:53:04-05:00](https://github.com/leanprover-community/mathlib/commit/edde6f5)
feat(tactic/ring): use `ring` for rewriting into pretty print format
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/ring.lean
- \+ *theorem* tactic.ring.add_neg_eq_sub
- \+ *theorem* tactic.ring.horner_def'
- \+ *theorem* tactic.ring.mul_assoc_rev
- \+ *theorem* tactic.ring.pow_add_rev
- \+ *theorem* tactic.ring.pow_add_rev_right



## [2018-01-13 19:43:41-05:00](https://github.com/leanprover-community/mathlib/commit/c75b072)
fix(*): update to lean
#### Estimated changes
Modified data/array/lemmas.lean


Modified data/list/basic.lean


Modified data/list/perm.lean


Modified data/option.lean
- \- *lemma* option.none_ne_some
- \+/\- *lemma* option.some_inj

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
- \+/\- *theorem* tactic.ring.horner_add_horner_eq



## [2018-01-13 03:25:35-05:00](https://github.com/leanprover-community/mathlib/commit/2e2d89b)
feat(tactic/ring): tactic for ring equality
#### Estimated changes
Modified algebra/group_power.lean
- \+/\- *theorem* add_monoid.smul_one
- \+/\- *theorem* pow_one

Modified data/pnat.lean
- \+/\- *def* nat.to_pnat

Added tactic/basic.lean


Modified tactic/interactive.lean


Modified tactic/norm_num.lean


Added tactic/ring.lean
- \+ *def* horner
- \+ *theorem* tactic.ring.const_add_horner
- \+ *theorem* tactic.ring.horner_add_const
- \+ *theorem* tactic.ring.horner_add_horner_eq
- \+ *theorem* tactic.ring.horner_add_horner_gt
- \+ *theorem* tactic.ring.horner_add_horner_lt
- \+ *theorem* tactic.ring.horner_atom
- \+ *theorem* tactic.ring.horner_const_mul
- \+ *theorem* tactic.ring.horner_horner
- \+ *theorem* tactic.ring.horner_mul_const
- \+ *theorem* tactic.ring.horner_mul_horner
- \+ *theorem* tactic.ring.horner_mul_horner_zero
- \+ *theorem* tactic.ring.horner_neg
- \+ *theorem* tactic.ring.horner_pow
- \+ *lemma* tactic.ring.subst_into_neg
- \+ *lemma* tactic.ring.subst_into_pow
- \+ *theorem* tactic.ring.zero_horner



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
- \+ *lemma* prod.ext
- \+/\- *lemma* prod.mk.eta

Modified order/complete_lattice.lean
- \+/\- *theorem* lattice.infi_inf_eq



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
- \+/\- *def* continuous
- \+/\- *theorem* is_open_induced

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
- \+/\- *lemma* finsupp.comap_domain_apply
- \+/\- *lemma* finsupp.comap_domain_zero
- \+/\- *lemma* finsupp.one_def
- \+/\- *lemma* finsupp.smul_apply

Modified data/fintype.lean


Modified data/fp/basic.lean


Modified data/hash_map.lean
- \+/\- *def* bucket_array.modify
- \+/\- *def* bucket_array.write
- \+/\- *def* hash_map.of_list

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
- \+/\- *theorem* snum.bit_one

Modified data/option.lean


Modified data/pfun.lean


Modified data/pnat.lean


Modified data/prod.lean
- \+/\- *lemma* prod.fst_swap
- \+/\- *lemma* prod.snd_swap
- \+/\- *def* prod.swap
- \+/\- *lemma* prod.swap_swap

Modified data/quot.lean


Modified data/rat.lean


Modified data/seq/computation.lean
- \+/\- *def* computation.destruct
- \+ *theorem* computation.eq_thinkN'
- \- *def* computation.eq_thinkN'
- \+ *theorem* computation.eq_thinkN
- \- *def* computation.eq_thinkN
- \+/\- *def* computation.equiv
- \+ *theorem* computation.exists_results_of_mem
- \- *def* computation.exists_results_of_mem
- \+ *theorem* computation.get_eq_of_mem
- \- *def* computation.get_eq_of_mem
- \+ *theorem* computation.get_eq_of_promises
- \- *def* computation.get_eq_of_promises
- \+/\- *theorem* computation.get_equiv
- \+ *theorem* computation.get_mem
- \- *def* computation.get_mem
- \+ *theorem* computation.get_promises
- \- *def* computation.get_promises
- \+/\- *theorem* computation.lift_eq_iff_equiv
- \+ *theorem* computation.lift_rel.equiv
- \- *def* computation.lift_rel.equiv
- \+ *theorem* computation.lift_rel.imp
- \- *def* computation.lift_rel.imp
- \+ *theorem* computation.lift_rel.refl
- \- *def* computation.lift_rel.refl
- \+ *theorem* computation.lift_rel.symm
- \- *def* computation.lift_rel.symm
- \+ *theorem* computation.lift_rel.trans
- \- *def* computation.lift_rel.trans
- \+ *theorem* computation.mem_of_get_eq
- \- *def* computation.mem_of_get_eq
- \+ *theorem* computation.mem_of_promises
- \- *def* computation.mem_of_promises
- \+/\- *def* computation.orelse
- \+/\- *theorem* computation.orelse_ret
- \+/\- *theorem* computation.orelse_think
- \+/\- *theorem* computation.promises_congr
- \+ *theorem* computation.rel_of_lift_rel
- \- *def* computation.rel_of_lift_rel
- \+ *theorem* computation.results.len_unique
- \- *def* computation.results.len_unique
- \+ *theorem* computation.results.length
- \- *def* computation.results.length
- \+ *theorem* computation.results.mem
- \- *def* computation.results.mem
- \+ *theorem* computation.results.terminates
- \- *def* computation.results.terminates
- \+ *theorem* computation.results.val_unique
- \- *def* computation.results.val_unique
- \+ *theorem* computation.results_of_terminates'
- \- *def* computation.results_of_terminates'
- \+ *theorem* computation.results_of_terminates
- \- *def* computation.results_of_terminates
- \+/\- *theorem* computation.ret_orelse
- \+/\- *theorem* computation.terminates_congr
- \+ *theorem* computation.terminates_of_lift_rel
- \- *def* computation.terminates_of_lift_rel

Modified data/seq/parallel.lean


Modified data/seq/seq.lean
- \+ *theorem* seq.corec_eq
- \- *def* seq.corec_eq
- \+ *theorem* seq.mem_append_left
- \- *def* seq.mem_append_left
- \+ *theorem* seq.of_list_append
- \- *def* seq.of_list_append
- \+ *theorem* seq.of_list_cons
- \- *def* seq.of_list_cons
- \+ *theorem* seq.of_list_nil
- \- *def* seq.of_list_nil
- \+ *theorem* seq.of_mem_append
- \- *def* seq.of_mem_append
- \+ *theorem* seq.of_stream_append
- \- *def* seq.of_stream_append
- \+ *theorem* seq.of_stream_cons
- \- *def* seq.of_stream_cons
- \+/\- *def* seq.omap

Modified data/seq/wseq.lean
- \+/\- *def* wseq.bisim_o
- \+/\- *def* wseq.destruct_append.aux
- \+/\- *def* wseq.destruct_join.aux
- \+/\- *def* wseq.drop.aux
- \+ *theorem* wseq.drop.aux_none
- \- *def* wseq.drop.aux_none
- \+ *theorem* wseq.join_cons
- \- *def* wseq.join_cons
- \+ *theorem* wseq.join_nil
- \- *def* wseq.join_nil
- \+ *theorem* wseq.join_think
- \- *def* wseq.join_think
- \+ *theorem* wseq.lift_rel.equiv
- \- *def* wseq.lift_rel.equiv
- \+ *theorem* wseq.lift_rel.refl
- \- *def* wseq.lift_rel.refl
- \+ *theorem* wseq.lift_rel.swap
- \- *def* wseq.lift_rel.swap
- \+ *theorem* wseq.lift_rel.swap_lem
- \- *def* wseq.lift_rel.swap_lem
- \+ *theorem* wseq.lift_rel.symm
- \- *def* wseq.lift_rel.symm
- \+ *theorem* wseq.lift_rel.trans
- \- *def* wseq.lift_rel.trans
- \+ *theorem* wseq.lift_rel_cons
- \- *def* wseq.lift_rel_cons
- \+ *theorem* wseq.lift_rel_nil
- \- *def* wseq.lift_rel_nil
- \+ *theorem* wseq.lift_rel_o.swap
- \- *def* wseq.lift_rel_o.swap
- \+/\- *def* wseq.lift_rel_o
- \+ *theorem* wseq.lift_rel_think_left
- \- *def* wseq.lift_rel_think_left
- \+ *theorem* wseq.lift_rel_think_right
- \- *def* wseq.lift_rel_think_right
- \+ *theorem* wseq.mem_append_left
- \- *def* wseq.mem_append_left
- \+ *theorem* wseq.of_list_cons
- \- *def* wseq.of_list_cons
- \+ *theorem* wseq.of_list_nil
- \- *def* wseq.of_list_nil
- \+ *theorem* wseq.of_mem_append
- \- *def* wseq.of_mem_append
- \+/\- *def* wseq.tail.aux
- \+ *theorem* wseq.to_list'_cons
- \- *def* wseq.to_list'_cons
- \+ *theorem* wseq.to_list'_map
- \- *def* wseq.to_list'_map
- \+ *theorem* wseq.to_list'_nil
- \- *def* wseq.to_list'_nil
- \+ *theorem* wseq.to_list'_think
- \- *def* wseq.to_list'_think
- \+ *theorem* wseq.to_list_cons
- \- *def* wseq.to_list_cons
- \+ *theorem* wseq.to_list_nil
- \- *def* wseq.to_list_nil

Modified data/set/basic.lean
- \+ *theorem* set.mem_image_elim
- \- *def* set.mem_image_elim
- \+ *theorem* set.mem_image_elim_on
- \- *def* set.mem_image_elim_on

Modified data/set/disjointed.lean


Modified data/set/finite.lean


Modified data/set/function.lean
- \+/\- *def* set.maps_to
- \+ *theorem* set.maps_to_univ
- \- *theorem* set.maps_to_univ_univ

Modified data/set/lattice.lean


Modified data/sigma/basic.lean


Modified data/sum.lean
- \+/\- *def* sum.swap

Modified logic/embedding.lean


Modified logic/function.lean


Modified number_theory/dioph.lean
- \+ *theorem* dioph.proj_dioph_of_nat
- \- *def* dioph.proj_dioph_of_nat
- \+/\- *def* fin2.add
- \+/\- *def* fin2.elim0
- \+/\- *def* fin2.insert_perm
- \+/\- *def* fin2.left
- \+/\- *def* fin2.of_nat'
- \+/\- *def* fin2.opt_of_nat
- \+/\- *def* fin2.remap_left
- \+ *def* fin2.to_nat
- \+/\- *lemma* int.eq_nat_abs_iff_mul
- \+/\- *def* list_all
- \+/\- *def* option.cons
- \+ *theorem* option.cons_head_tail
- \- *def* option.cons_head_tail
- \- *def* poly.pow
- \+/\- *def* sum.join
- \+/\- *def* vector3.append
- \+/\- *theorem* vector3.append_add
- \+/\- *theorem* vector3.append_cons
- \+/\- *theorem* vector3.append_insert
- \+/\- *theorem* vector3.append_left
- \+/\- *theorem* vector3.append_nil
- \+/\- *def* vector3.cons
- \+/\- *def* vector3.cons_elim
- \+/\- *theorem* vector3.cons_elim_cons
- \+/\- *theorem* vector3.cons_fs
- \+/\- *theorem* vector3.cons_fz
- \+/\- *theorem* vector3.cons_head_tail
- \+/\- *theorem* vector3.eq_nil
- \+/\- *def* vector3.head
- \+/\- *def* vector3.insert
- \+/\- *theorem* vector3.insert_fs
- \+/\- *theorem* vector3.insert_fz
- \+/\- *def* vector3.nil
- \+/\- *def* vector3.nil_elim
- \+/\- *def* vector3.nth
- \+/\- *def* vector3.of_fn
- \+/\- *theorem* vector3.rec_on_cons
- \+/\- *theorem* vector3.rec_on_nil
- \+/\- *def* vector3.tail

Modified number_theory/pell.lean
- \+ *theorem* pell.is_pell_conj
- \- *def* pell.is_pell_conj
- \+ *theorem* pell.is_pell_mul
- \- *def* pell.is_pell_mul
- \+ *theorem* pell.is_pell_nat
- \- *def* pell.is_pell_nat
- \+ *theorem* pell.is_pell_norm
- \- *def* pell.is_pell_norm
- \+ *theorem* pell.is_pell_one
- \- *def* pell.is_pell_one
- \+ *theorem* pell.is_pell_pell_zd
- \- *def* pell.is_pell_pell_zd
- \+ *theorem* pell.n_lt_a_pow
- \- *def* pell.n_lt_a_pow
- \+/\- *def* pell.pell
- \+ *theorem* pell.xn_ge_a_pow
- \- *def* pell.xn_ge_a_pow
- \+ *theorem* zsqrtd.nonnegg_cases_left
- \- *def* zsqrtd.nonnegg_cases_left
- \+ *theorem* zsqrtd.nonnegg_cases_right
- \- *def* zsqrtd.nonnegg_cases_right
- \+ *theorem* zsqrtd.nonnegg_comm
- \- *def* zsqrtd.nonnegg_comm
- \+ *theorem* zsqrtd.nonnegg_neg_pos
- \- *def* zsqrtd.nonnegg_neg_pos
- \+ *theorem* zsqrtd.nonnegg_pos_neg
- \- *def* zsqrtd.nonnegg_pos_neg

Modified order/basic.lean
- \+ *theorem* is_irrefl.swap
- \- *def* is_irrefl.swap
- \+ *theorem* is_irrefl_of_is_asymm
- \- *def* is_irrefl_of_is_asymm
- \+ *theorem* is_strict_order.swap
- \- *def* is_strict_order.swap
- \+ *theorem* is_strict_total_order'.swap
- \- *def* is_strict_total_order'.swap
- \+ *theorem* is_strict_weak_order_of_is_order_connected
- \- *def* is_strict_weak_order_of_is_order_connected
- \+ *theorem* is_trans.swap
- \- *def* is_trans.swap
- \+ *theorem* is_trichotomous.swap
- \- *def* is_trichotomous.swap

Modified order/boolean_algebra.lean


Modified order/bounded_lattice.lean


Modified order/complete_boolean_algebra.lean


Modified order/complete_lattice.lean
- \+/\- *theorem* lattice.Inf_le
- \+/\- *theorem* lattice.le_Sup

Modified order/filter.lean
- \+/\- *def* directed
- \+/\- *def* directed_on
- \+/\- *lemma* filter.lift_le
- \+/\- *def* filter.tendsto
- \- *def* upwards

Modified order/fixed_points.lean


Modified order/galois_connection.lean


Modified order/lattice.lean


Modified order/order_iso.lean


Modified order/zorn.lean


Modified set_theory/cardinal.lean


Modified set_theory/cofinality.lean
- \+/\- *theorem* cardinal.lt_cof_power

Modified set_theory/ordinal.lean
- \+ *theorem* initial_seg.unique_of_extensional
- \- *def* initial_seg.unique_of_extensional
- \+/\- *theorem* order_embedding.collapse_apply
- \+/\- *def* ordinal.typein
- \+/\- *def* principal_seg.cod_restrict

Modified set_theory/ordinal_notation.lean


Modified set_theory/zfc.lean
- \+/\- *def* Class.Class_to_Cong
- \+/\- *def* Class.Cong_to_Class
- \+/\- *def* Class.Union
- \+/\- *theorem* Class.Union_hom
- \+/\- *theorem* Class.diff_hom
- \+/\- *theorem* Class.empty_hom
- \+/\- *def* Class.fval
- \+/\- *theorem* Class.fval_ex
- \+/\- *theorem* Class.insert_hom
- \+/\- *theorem* Class.inter_hom
- \+/\- *def* Class.iota
- \+/\- *theorem* Class.iota_ex
- \+/\- *theorem* Class.iota_val
- \+/\- *theorem* Class.mem_hom_left
- \+/\- *theorem* Class.mem_hom_right
- \+/\- *theorem* Class.mem_univ
- \+/\- *theorem* Class.of_Set.inj
- \+/\- *def* Class.of_Set
- \+/\- *def* Class.powerset
- \+/\- *theorem* Class.powerset_hom
- \+/\- *theorem* Class.sep_hom
- \+/\- *theorem* Class.subset_hom
- \+/\- *def* Class.to_Set
- \+/\- *theorem* Class.to_Set_of_Set
- \+/\- *theorem* Class.union_hom
- \+/\- *def* Class.univ
- \+/\- *def* Set.Union
- \+/\- *theorem* Set.Union_lem
- \+/\- *theorem* Set.Union_singleton
- \+ *theorem* Set.choice_is_func
- \- *def* Set.choice_is_func
- \+ *theorem* Set.choice_mem
- \- *def* Set.choice_mem
- \+ *theorem* Set.choice_mem_aux
- \- *def* Set.choice_mem_aux
- \+/\- *def* Set.empty
- \+ *theorem* Set.eq_empty
- \- *def* Set.eq_empty
- \+ *theorem* Set.ext
- \- *def* Set.ext
- \+ *theorem* Set.ext_iff
- \- *def* Set.ext_iff
- \+/\- *def* Set.funs
- \+ *theorem* Set.image.mk
- \- *def* Set.image.mk
- \+/\- *def* Set.image
- \+/\- *theorem* Set.induction_on
- \+/\- *def* Set.is_func
- \+ *theorem* Set.map_fval
- \- *def* Set.map_fval
- \+/\- *theorem* Set.map_is_func
- \+/\- *theorem* Set.map_unique
- \+/\- *def* Set.mem
- \+/\- *theorem* Set.mem_Union
- \+/\- *theorem* Set.mem_diff
- \+ *theorem* Set.mem_empty
- \- *def* Set.mem_empty
- \+ *theorem* Set.mem_funs
- \- *def* Set.mem_funs
- \+ *theorem* Set.mem_image
- \- *def* Set.mem_image
- \+ *theorem* Set.mem_insert
- \- *def* Set.mem_insert
- \+/\- *theorem* Set.mem_inter
- \+/\- *theorem* Set.mem_map
- \+/\- *theorem* Set.mem_pair
- \+/\- *theorem* Set.mem_pair_sep
- \+/\- *theorem* Set.mem_powerset
- \+ *theorem* Set.mem_prod
- \- *def* Set.mem_prod
- \+/\- *theorem* Set.mem_sep
- \+/\- *theorem* Set.mem_singleton'
- \+/\- *theorem* Set.mem_singleton
- \+/\- *theorem* Set.mem_union
- \+ *def* Set.mk
- \+ *theorem* Set.mk_eq
- \+/\- *def* Set.omega
- \+/\- *theorem* Set.omega_succ
- \+/\- *theorem* Set.omega_zero
- \+/\- *def* Set.pair
- \+ *theorem* Set.pair_inj
- \- *def* Set.pair_inj
- \+ *theorem* Set.pair_mem_prod
- \- *def* Set.pair_mem_prod
- \+/\- *def* Set.pair_sep
- \+/\- *def* Set.powerset
- \+/\- *def* Set.prod
- \+/\- *theorem* Set.regularity
- \+/\- *theorem* Set.singleton_inj
- \+/\- *theorem* Set.subset_iff
- \+/\- *def* Set.to_set
- \+/\- *def* pSet.Union
- \+/\- *def* pSet.arity.equiv
- \+ *theorem* pSet.definable.eq
- \- *def* pSet.definable.eq
- \+/\- *def* pSet.definable.eq_mk
- \+/\- *def* pSet.definable.resp
- \+/\- *def* pSet.embed
- \+ *theorem* pSet.equiv.eq
- \- *def* pSet.equiv.eq
- \+ *theorem* pSet.equiv.euc
- \- *def* pSet.equiv.euc
- \+ *theorem* pSet.equiv.ext
- \- *def* pSet.equiv.ext
- \+ *theorem* pSet.equiv.refl
- \- *def* pSet.equiv.refl
- \+ *theorem* pSet.equiv.symm
- \- *def* pSet.equiv.symm
- \+ *theorem* pSet.equiv.trans
- \- *def* pSet.equiv.trans
- \+/\- *def* pSet.equiv
- \+/\- *def* pSet.func
- \+/\- *def* pSet.image
- \+ *theorem* pSet.lift_mem_embed
- \- *def* pSet.lift_mem_embed
- \+ *theorem* pSet.mem.congr_left
- \- *def* pSet.mem.congr_left
- \+ *theorem* pSet.mem.congr_right
- \- *def* pSet.mem.congr_right
- \+ *theorem* pSet.mem.ext
- \- *def* pSet.mem.ext
- \+ *theorem* pSet.mem.mk
- \- *def* pSet.mem.mk
- \+/\- *def* pSet.mem
- \+/\- *theorem* pSet.mem_Union
- \+ *theorem* pSet.mem_empty
- \- *def* pSet.mem_empty
- \+ *theorem* pSet.mem_image
- \- *def* pSet.mem_image
- \+/\- *theorem* pSet.mem_powerset
- \+ *theorem* pSet.mk_type_func
- \- *def* pSet.mk_type_func
- \+/\- *def* pSet.of_nat
- \+/\- *def* pSet.omega
- \+/\- *def* pSet.powerset
- \+/\- *def* pSet.resp.equiv
- \+ *theorem* pSet.resp.euc
- \- *def* pSet.resp.euc
- \+/\- *def* pSet.resp.eval
- \+/\- *def* pSet.resp.eval_aux
- \+/\- *def* pSet.resp.eval_val
- \+/\- *def* pSet.resp.f
- \+ *theorem* pSet.resp.refl
- \- *def* pSet.resp.refl
- \+/\- *def* pSet.resp
- \+ *theorem* pSet.subset.congr_left
- \- *def* pSet.subset.congr_left
- \+ *theorem* pSet.subset.congr_right
- \- *def* pSet.subset.congr_right
- \+/\- *def* pSet.to_set
- \+/\- *def* pSet.type

Modified tactic/interactive.lean


Modified tactic/norm_num.lean




## [2018-01-11 16:26:08-05:00](https://github.com/leanprover-community/mathlib/commit/2ffd72c)
refactor(order/basic): remove "increasing/decreasing" unusual defs
#### Estimated changes
Modified order/basic.lean
- \+ *def* partial_order.dual
- \- *def* partial_order_dual
- \+ *def* preorder.dual
- \- *def* preorder_dual

Modified order/galois_connection.lean
- \+/\- *lemma* galois_connection.decreasing_l_u
- \+/\- *lemma* galois_connection.increasing_u_l
- \+ *def* set.kern_image



## [2018-01-11 16:21:21-05:00](https://github.com/leanprover-community/mathlib/commit/09e0899)
fix(analysis/ennreal): fix long-running proofs
#### Estimated changes
Modified algebra/functions.lean
- \+/\- *theorem* abs_le
- \+/\- *lemma* abs_lt

Modified algebra/linear_algebra/basic.lean


Modified analysis/ennreal.lean
- \+ *lemma* ennreal.of_real_add
- \- *lemma* ennreal.of_real_add_of_real

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
- \+ *lemma* max_of_rat
- \- *lemma* max_of_rat_of_rat
- \+ *lemma* min_of_rat
- \- *lemma* min_of_rat_of_rat
- \+ *lemma* of_rat_le
- \- *lemma* of_rat_le_of_rat
- \+ *theorem* real.le_def
- \+/\- *lemma* two_eq_of_rat_two



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
Added analysis/complex.lean
- \+ *def* complex.I
- \+ *lemma* complex.I_im
- \+ *lemma* complex.I_re
- \+ *lemma* complex.add_im
- \+ *lemma* complex.add_re
- \+ *lemma* complex.coe_im
- \+ *lemma* complex.coe_re
- \+ *lemma* complex.conj_im
- \+ *lemma* complex.conj_re
- \+ *def* complex.conjugate
- \+ *theorem* complex.eq_iff_re_eq_and_im_eq
- \+ *theorem* complex.eq_of_re_eq_and_im_eq
- \+ *theorem* complex.eta
- \+ *theorem* complex.im_eq_zero_of_complex_nat
- \+ *lemma* complex.mul_im
- \+ *lemma* complex.mul_re
- \+ *lemma* complex.neg_im
- \+ *lemma* complex.neg_re
- \+ *def* complex.norm_squared
- \+ *lemma* complex.norm_squared_pos_of_nonzero
- \+ *def* complex.of_real
- \+ *lemma* complex.of_real_abs_squared
- \+ *lemma* complex.of_real_add
- \+ *lemma* complex.of_real_eq_coe
- \+ *lemma* complex.of_real_injective
- \+ *theorem* complex.of_real_int_eq_complex_int
- \+ *lemma* complex.of_real_inv
- \+ *lemma* complex.of_real_mul
- \+ *theorem* complex.of_real_nat_eq_complex_nat
- \+ *lemma* complex.of_real_neg
- \+ *lemma* complex.of_real_one
- \+ *lemma* complex.of_real_sub
- \+ *lemma* complex.of_real_zero
- \+ *lemma* complex.one_im
- \+ *lemma* complex.one_re
- \+ *lemma* complex.proj_im
- \+ *lemma* complex.proj_re
- \+ *lemma* complex.sub_im
- \+ *lemma* complex.sub_re
- \+ *lemma* complex.zero_im
- \+ *lemma* complex.zero_re



## [2018-01-06 18:57:25-05:00](https://github.com/leanprover-community/mathlib/commit/182c303)
feat(set_theory/cofinality): regular/inaccessible cards, Konig's theorem, next fixpoint function
#### Estimated changes
Modified algebra/functions.lean
- \+ *lemma* abs_one

Modified data/equiv.lean
- \+ *def* equiv.Pi_congr_right

Modified logic/embedding.lean
- \+ *def* function.embedding.Pi_congr_right
- \+ *def* function.embedding.sigma_congr_right

Modified logic/function.lean
- \+ *lemma* function.inv_fun_surjective

Modified set_theory/cardinal.lean
- \+ *theorem* cardinal.add_def
- \+ *theorem* cardinal.cantor'
- \+ *theorem* cardinal.lift_id'
- \+/\- *theorem* cardinal.lift_id
- \+ *theorem* cardinal.lift_succ
- \+ *theorem* cardinal.lift_two_power
- \+ *theorem* cardinal.lt_succ
- \+ *theorem* cardinal.mk_out
- \+ *theorem* cardinal.mul_def
- \+ *theorem* cardinal.omega_pos
- \+ *theorem* cardinal.one_le_iff_ne_zero
- \+ *theorem* cardinal.one_le_iff_pos
- \+ *theorem* cardinal.pos_iff_ne_zero
- \+ *theorem* cardinal.power_def
- \+ *theorem* cardinal.power_ne_zero
- \+ *def* cardinal.prod
- \+ *theorem* cardinal.prod_const
- \+ *theorem* cardinal.prod_eq_zero
- \+ *theorem* cardinal.prod_le_prod
- \+ *theorem* cardinal.prod_mk
- \+ *theorem* cardinal.prod_ne_zero
- \+/\- *def* cardinal.sum
- \+ *theorem* cardinal.sum_const
- \+ *theorem* cardinal.sum_le_sum
- \+ *theorem* cardinal.sum_le_sup
- \+ *theorem* cardinal.sum_lt_prod
- \+ *theorem* cardinal.sum_mk
- \+ *theorem* cardinal.sup_le_sum
- \+ *theorem* cardinal.sup_le_sup

Added set_theory/cofinality.lean
- \+ *theorem* cardinal.cof_is_regular
- \+ *theorem* cardinal.is_inaccessible.mk
- \+ *def* cardinal.is_inaccessible
- \+ *def* cardinal.is_limit
- \+ *def* cardinal.is_regular
- \+ *theorem* cardinal.is_strong_limit.is_limit
- \+ *def* cardinal.is_strong_limit
- \+ *theorem* cardinal.lt_cof_power
- \+ *theorem* cardinal.lt_power_cof
- \+ *theorem* cardinal.omega_is_regular
- \+ *theorem* cardinal.succ_is_regular
- \+ *theorem* cardinal.univ_inaccessible
- \+ *def* order.cof
- \+ *theorem* order_iso.cof.aux
- \+ *theorem* order_iso.cof
- \+ *def* ordinal.cof
- \+ *theorem* ordinal.cof_add
- \+ *theorem* ordinal.cof_bsup_le
- \+ *theorem* ordinal.cof_bsup_le_lift
- \+ *theorem* ordinal.cof_cof
- \+ *theorem* ordinal.cof_eq'
- \+ *theorem* ordinal.cof_eq
- \+ *theorem* ordinal.cof_eq_one_iff_is_succ
- \+ *theorem* ordinal.cof_eq_zero
- \+ *theorem* ordinal.cof_le_card
- \+ *theorem* ordinal.cof_omega
- \+ *theorem* ordinal.cof_ord_le
- \+ *theorem* ordinal.cof_succ
- \+ *theorem* ordinal.cof_sup_le
- \+ *theorem* ordinal.cof_sup_le_lift
- \+ *theorem* ordinal.cof_type_le
- \+ *theorem* ordinal.cof_univ
- \+ *theorem* ordinal.cof_zero
- \+ *theorem* ordinal.le_cof_type
- \+ *theorem* ordinal.lift_cof
- \+ *theorem* ordinal.lt_cof_type
- \+ *theorem* ordinal.omega_le_cof
- \+ *theorem* ordinal.ord_cof_eq

Modified set_theory/ordinal.lean
- \+ *theorem* cardinal.lift_lt_univ'
- \+ *theorem* cardinal.lift_lt_univ
- \+ *theorem* cardinal.lift_univ
- \+ *theorem* cardinal.lt_univ'
- \+ *theorem* cardinal.lt_univ
- \+ *theorem* cardinal.mk_cardinal
- \+ *theorem* cardinal.ord_univ
- \+ *theorem* cardinal.type_cardinal
- \+ *def* cardinal.univ
- \+ *theorem* cardinal.univ_id
- \+ *theorem* cardinal.univ_umax
- \- *def* cof
- \- *def* order.cof
- \- *theorem* order_iso.cof.aux
- \- *theorem* order_iso.cof
- \+ *theorem* ordinal.card_univ
- \- *theorem* ordinal.cof_add
- \- *theorem* ordinal.cof_bsup_le
- \- *theorem* ordinal.cof_bsup_le_lift
- \- *theorem* ordinal.cof_cof
- \- *theorem* ordinal.cof_eq
- \- *theorem* ordinal.cof_eq_one_iff_is_succ
- \- *theorem* ordinal.cof_eq_zero
- \- *theorem* ordinal.cof_le_card
- \- *theorem* ordinal.cof_succ
- \- *theorem* ordinal.cof_sup_le
- \- *theorem* ordinal.cof_sup_le_lift
- \- *theorem* ordinal.cof_type_le
- \- *theorem* ordinal.cof_zero
- \+ *def* ordinal.deriv
- \+ *theorem* ordinal.deriv_is_normal
- \+ *theorem* ordinal.deriv_limit
- \+ *theorem* ordinal.deriv_succ
- \+ *theorem* ordinal.deriv_zero
- \+ *theorem* ordinal.foldr_le_nfp
- \+ *theorem* ordinal.is_normal.bsup
- \+ *theorem* ordinal.is_normal.deriv_fp
- \+ *theorem* ordinal.is_normal.fp_iff_deriv
- \+ *theorem* ordinal.is_normal.le_nfp
- \+ *theorem* ordinal.is_normal.lt_nfp
- \+ *theorem* ordinal.is_normal.nfp_fp
- \+ *theorem* ordinal.is_normal.nfp_le
- \+ *theorem* ordinal.is_normal.nfp_le_fp
- \+ *theorem* ordinal.is_normal.sup
- \- *theorem* ordinal.le_cof_type
- \+ *theorem* ordinal.le_nfp_self
- \+/\- *theorem* ordinal.lift.principal_seg_top
- \+ *theorem* ordinal.lift_id'
- \+/\- *theorem* ordinal.lift_id
- \+ *theorem* ordinal.lift_type
- \+ *theorem* ordinal.lift_univ
- \- *theorem* ordinal.lt_cof_type
- \+ *theorem* ordinal.lt_sup
- \+ *def* ordinal.nfp
- \+ *theorem* ordinal.not_zero_is_limit
- \- *theorem* ordinal.ord_cof_eq
- \+ *def* ordinal.univ
- \+ *theorem* ordinal.univ_id
- \+ *theorem* ordinal.univ_umax

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
- \+ *theorem* nat.succ_pnat_coe
- \+ *theorem* pnat.add_coe
- \+ *theorem* pnat.eq
- \+ *theorem* pnat.mk_coe
- \+ *theorem* pnat.mul_coe
- \+ *theorem* pnat.nat_coe_coe
- \- *theorem* pnat.nat_coe_val
- \+/\- *theorem* pnat.ne_zero
- \+ *theorem* pnat.one_coe
- \+ *theorem* pnat.pos
- \+ *def* pnat.pow
- \- *theorem* pnat.to_pnat'_val

Modified logic/basic.lean
- \+ *theorem* coe_coe

Modified set_theory/ordinal.lean
- \+ *theorem* ordinal.add_le_add_iff_right
- \+ *theorem* ordinal.add_lt_omega_power
- \+ *theorem* ordinal.add_right_cancel
- \+ *theorem* ordinal.add_sub_add_cancel
- \+ *theorem* ordinal.dvd_add
- \+ *theorem* ordinal.dvd_add_iff
- \+ *theorem* ordinal.dvd_antisymm
- \+ *theorem* ordinal.dvd_mul_of_dvd
- \+ *theorem* ordinal.dvd_trans
- \+ *theorem* ordinal.is_limit_iff_omega_dvd
- \+ *theorem* ordinal.is_normal.limit_le
- \+ *theorem* ordinal.le_of_dvd
- \+ *theorem* ordinal.lt_limit
- \- *theorem* ordinal.mul_assoc
- \+ *theorem* ordinal.mul_is_limit_left
- \+ *theorem* ordinal.mul_lt_omega_power
- \+ *theorem* ordinal.mul_omega_dvd
- \- *theorem* ordinal.mul_omega_power
- \- *theorem* ordinal.mul_one
- \+ *theorem* ordinal.mul_sub
- \+ *theorem* ordinal.nat_cast_succ
- \- *theorem* ordinal.one_mul
- \+ *theorem* ordinal.power_dvd_power
- \+ *theorem* ordinal.power_dvd_power_iff
- \+ *theorem* ordinal.power_lt_omega
- \+ *theorem* ordinal.power_omega
- \+ *theorem* ordinal.sub_eq_of_add_eq
- \+ *theorem* ordinal.sub_is_limit
- \+ *theorem* ordinal.sub_sub
- \- *theorem* ordinal.succ_nat_cast
- \+/\- *theorem* ordinal.zero_dvd

Modified set_theory/ordinal_notation.lean
- \+ *def* nonote.below
- \+ *def* nonote.mk
- \+ *def* nonote.oadd
- \+ *def* nonote.power
- \+ *def* nonote.rec_on
- \+/\- *theorem* nonote.repr_add
- \+/\- *theorem* nonote.repr_mul
- \+ *theorem* nonote.repr_power
- \+ *theorem* nonote.repr_sub
- \+ *theorem* onote.NF.below_of_lt'
- \+/\- *theorem* onote.NF.below_of_lt
- \+/\- *theorem* onote.NF.fst
- \+/\- *theorem* onote.NF.oadd
- \+ *theorem* onote.NF.of_dvd_omega
- \+ *theorem* onote.NF.of_dvd_omega_power
- \+/\- *theorem* onote.NF.snd'
- \+/\- *theorem* onote.NF.snd
- \- *theorem* onote.NF.zero
- \+ *theorem* onote.NF.zero_of_zero
- \+/\- *def* onote.NF
- \+/\- *theorem* onote.NF_below.fst
- \+/\- *theorem* onote.NF_below.lt
- \+/\- *theorem* onote.NF_below.oadd
- \+/\- *theorem* onote.NF_below.repr_lt
- \+/\- *theorem* onote.NF_below.snd
- \+/\- *theorem* onote.NF_below_iff_top_below
- \- *theorem* onote.NF_of_nat
- \+ *theorem* onote.NF_repr_split'
- \+ *theorem* onote.NF_repr_split
- \- *theorem* onote.add_NF
- \+/\- *theorem* onote.cmp_compares
- \+/\- *theorem* onote.le_def
- \+/\- *theorem* onote.lt_def
- \- *theorem* onote.mul_NF
- \+ *def* onote.mul_nat
- \+ *theorem* onote.mul_nat_eq_mul
- \+ *theorem* onote.mul_zero
- \+ *theorem* onote.oadd_add
- \+/\- *theorem* onote.oadd_lt_oadd_3
- \+ *theorem* onote.oadd_mul
- \+/\- *theorem* onote.oadd_pos
- \+ *def* onote.omega
- \+/\- *theorem* onote.omega_le_oadd
- \+/\- *def* onote.power_aux
- \+ *def* onote.repr'
- \+/\- *theorem* onote.repr_add
- \+/\- *theorem* onote.repr_inj
- \+/\- *theorem* onote.repr_mul
- \+ *theorem* onote.repr_power
- \+ *theorem* onote.repr_power_aux₁
- \+ *theorem* onote.repr_power_aux₂
- \+ *theorem* onote.repr_scale
- \+ *theorem* onote.repr_sub
- \+/\- *def* onote.scale
- \+ *theorem* onote.scale_eq_mul
- \+ *theorem* onote.scale_power_aux
- \+/\- *def* onote.split'
- \+/\- *def* onote.split
- \+ *theorem* onote.split_add_lt
- \+ *theorem* onote.split_dvd
- \+ *theorem* onote.split_eq_scale_split'
- \+ *theorem* onote.sub_NF_below
- \+ *def* onote.to_string
- \+ *def* onote.to_string_aux1
- \+ *theorem* onote.zero_add
- \+ *theorem* onote.zero_mul



## [2018-01-04 09:05:02-05:00](https://github.com/leanprover-community/mathlib/commit/3f2435e)
refactor(algebra/group): clean up PR commit
#### Estimated changes
Modified algebra/big_operators.lean
- \- *lemma* anti_mph_prod
- \+ *theorem* inv_prod
- \- *lemma* inv_prod
- \+ *theorem* is_group_anti_hom.prod
- \+ *theorem* is_group_hom.prod
- \- *lemma* mph_prod

Modified algebra/group.lean
- \- *lemma* group_anti_hom.inv
- \- *lemma* group_anti_hom.inv_is_group_anti_hom
- \- *lemma* group_anti_hom.one
- \- *lemma* group_hom.inv
- \- *lemma* group_hom.one
- \+ *theorem* inv_is_group_anti_hom
- \+ *theorem* is_group_anti_hom.inv
- \+ *theorem* is_group_anti_hom.mul
- \+ *theorem* is_group_anti_hom.one
- \+ *theorem* is_group_hom.inv
- \+ *theorem* is_group_hom.mul
- \+ *theorem* is_group_hom.one



## [2018-01-02 16:52:49-05:00](https://github.com/leanprover-community/mathlib/commit/12bd22b)
Group morphisms ([#30](https://github.com/leanprover-community/mathlib/pull/30))
* feat(algebra/group): morphisms and antimorphisms
Definitions, image of one and inverses,
and computation on a product of more than two elements in big_operators.
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* anti_mph_prod
- \+ *lemma* inv_prod
- \+ *lemma* mph_prod

Modified algebra/group.lean
- \+ *lemma* group_anti_hom.inv
- \+ *lemma* group_anti_hom.inv_is_group_anti_hom
- \+ *lemma* group_anti_hom.one
- \+ *lemma* group_hom.inv
- \+ *lemma* group_hom.one
- \+ *def* is_group_anti_hom
- \+ *def* is_group_hom



## [2018-01-02 04:28:01-05:00](https://github.com/leanprover-community/mathlib/commit/37c3120)
feat(set_theory/ordinal_notation): ordinal notations for ordinals < e0
This allows us to compute with small countable ordinals using trees of nats.
#### Estimated changes
Modified algebra/order.lean
- \+ *lemma* injective_of_strict_mono
- \+/\- *lemma* lt_iff_lt_of_strict_mono
- \+ *theorem* ordering.compares.eq_eq
- \+ *theorem* ordering.compares.eq_gt
- \+ *theorem* ordering.compares.eq_lt
- \+ *theorem* ordering.compares.inj
- \+ *def* ordering.compares
- \+ *theorem* ordering.compares_of_strict_mono

Modified data/nat/cast.lean
- \+/\- *theorem* nat.cast_add_one

Modified data/pnat.lean
- \+/\- *def* nat.succ_pnat
- \+/\- *def* nat.to_pnat'
- \+/\- *def* nat.to_pnat
- \+/\- *theorem* pnat.nat_coe_val
- \+ *theorem* pnat.ne_zero
- \+/\- *theorem* pnat.to_pnat'_coe
- \+/\- *theorem* pnat.to_pnat'_val

Modified logic/basic.lean
- \+ *theorem* imp_or_distrib'
- \+ *theorem* imp_or_distrib

Renamed theories/number_theory/dioph.lean to number_theory/dioph.lean


Renamed theories/number_theory/pell.lean to number_theory/pell.lean


Renamed data/cardinal.lean to set_theory/cardinal.lean


Renamed data/ordinal.lean to set_theory/ordinal.lean
- \+ *theorem* ordinal.add_mul_limit
- \+ *theorem* ordinal.add_mul_limit_aux
- \+ *theorem* ordinal.add_mul_succ
- \+ *theorem* ordinal.bsup_type
- \+ *theorem* ordinal.cof_bsup_le
- \+ *theorem* ordinal.cof_bsup_le_lift
- \+ *theorem* ordinal.nat_cast_pos

Added set_theory/ordinal_notation.lean
- \+ *def* nonote.cmp
- \+ *theorem* nonote.cmp_compares
- \+ *def* nonote.of_nat
- \+ *theorem* nonote.repr_add
- \+ *theorem* nonote.repr_mul
- \+ *def* nonote
- \+ *theorem* onote.NF.below_of_lt
- \+ *theorem* onote.NF.fst
- \+ *theorem* onote.NF.oadd
- \+ *theorem* onote.NF.snd'
- \+ *theorem* onote.NF.snd
- \+ *theorem* onote.NF.zero
- \+ *def* onote.NF
- \+ *theorem* onote.NF_below.fst
- \+ *theorem* onote.NF_below.lt
- \+ *theorem* onote.NF_below.mono
- \+ *theorem* onote.NF_below.oadd
- \+ *theorem* onote.NF_below.repr_lt
- \+ *theorem* onote.NF_below.snd
- \+ *theorem* onote.NF_below_iff_top_below
- \+ *theorem* onote.NF_below_of_nat
- \+ *theorem* onote.NF_below_zero
- \+ *theorem* onote.NF_of_nat
- \+ *def* onote.add
- \+ *theorem* onote.add_NF
- \+ *theorem* onote.add_NF_below
- \+ *def* onote.cmp
- \+ *theorem* onote.cmp_compares
- \+ *theorem* onote.eq_of_cmp_eq
- \+ *theorem* onote.le_def
- \+ *theorem* onote.lt_def
- \+ *def* onote.mul
- \+ *theorem* onote.mul_NF
- \+ *theorem* onote.oadd_lt_oadd_1
- \+ *theorem* onote.oadd_lt_oadd_2
- \+ *theorem* onote.oadd_lt_oadd_3
- \+ *theorem* onote.oadd_mul_NF_below
- \+ *theorem* onote.oadd_pos
- \+ *def* onote.of_nat
- \+ *theorem* onote.of_nat_one
- \+ *theorem* onote.omega_le_oadd
- \+ *def* onote.power
- \+ *def* onote.power_aux
- \+ *theorem* onote.repr_add
- \+ *theorem* onote.repr_inj
- \+ *theorem* onote.repr_mul
- \+ *theorem* onote.repr_of_nat
- \+ *theorem* onote.repr_one
- \+ *def* onote.scale
- \+ *def* onote.split'
- \+ *def* onote.split
- \+ *def* onote.sub
- \+ *def* onote.top_below
- \+ *theorem* onote.zero_def
- \+ *theorem* onote.zero_lt_one

Renamed theories/set_theory.lean to set_theory/zfc.lean


Modified tactic/interactive.lean


