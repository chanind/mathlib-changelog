## [2018-10-31 21:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/74ae8ce)
fix(data/real,data/rat): make orders on real and rat irreducible
#### Estimated changes
Modified analysis/complex.lean


Modified data/rat.lean


Modified data/real/basic.lean




## [2018-10-30 12:26:55-04:00](https://github.com/leanprover-community/mathlib/commit/58909bd)
feat(*): monovariate and multivariate eval\2 now do not take is_semiring_hom as an argument
#### Estimated changes
Modified data/polynomial.lean


Modified linear_algebra/multivariate_polynomial.lean




## [2018-10-30 12:24:35-04:00](https://github.com/leanprover-community/mathlib/commit/90982d7)
feat(tactic/fin_cases): a tactic to case bash on `fin n` ([#352](https://github.com/leanprover-community/mathlib/pull/352))
* feat(tactic/fin_cases): a tactic to case bash on `fin n`
* using core is_numeral
* removing guard
just rely on eval_expr to decide if we have an explicit nat
* add parsing, tests, documentation
* don't fail if the rewrite fails
* fixes
#### Estimated changes
Modified data/fin.lean
- \+ *def* fin.mk_val

Modified docs/tactics.md


Added tactic/fin_cases.lean


Added tests/fin_cases.lean




## [2018-10-30 12:23:50-04:00](https://github.com/leanprover-community/mathlib/commit/e585bed)
feat(data/int/basic): bounded forall is decidable for integers
#### Estimated changes
Modified data/int/basic.lean
- \+ *theorem* int.mem_range_iff
- \+ *def* int.range



## [2018-10-30 12:23:04-04:00](https://github.com/leanprover-community/mathlib/commit/489050b)
feat(tactic/tauto): add an option for `tauto` to work in classical logic
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/interactive.lean


Modified tactic/tauto.lean


Modified tactic/wlog.lean


Modified tests/tactics.lean




## [2018-10-19 00:14:30+02:00](https://github.com/leanprover-community/mathlib/commit/ed84298)
feat(analysis/topology): add continuity rules for list and vector insert/remove_nth
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* list.continuous_insert_nth
- \+ *lemma* list.continuous_remove_nth
- \+ *lemma* list.tendsto_cons'
- \+ *lemma* list.tendsto_cons
- \+ *lemma* list.tendsto_cons_iff
- \+ *lemma* list.tendsto_insert_nth'
- \+ *lemma* list.tendsto_insert_nth
- \+ *lemma* list.tendsto_length
- \+ *lemma* list.tendsto_nhds
- \+ *lemma* list.tendsto_remove_nth
- \+ *lemma* tendsto_subtype_rng
- \+ *lemma* tendsto_subtype_val
- \+ *lemma* vector.cons_val
- \+ *lemma* vector.continuous_insert_nth'
- \+ *lemma* vector.continuous_insert_nth
- \+ *lemma* vector.continuous_remove_nth
- \+ *lemma* vector.tendsto_cons
- \+ *lemma* vector.tendsto_insert_nth
- \+ *lemma* vector.tendsto_remove_nth

Modified analysis/topology/topological_space.lean
- \+ *lemma* nhds_cons
- \+ *lemma* nhds_nil

Modified analysis/topology/uniform_space.lean




## [2018-10-19 00:03:08+02:00](https://github.com/leanprover-community/mathlib/commit/f6812d5)
feat(analysis/topology): add type class for discrete topological spaces
#### Estimated changes
Modified analysis/topology/continuity.lean


Modified analysis/topology/topological_space.lean
- \+ *lemma* is_open_discrete
- \- *lemma* is_open_top
- \+ *lemma* nhds_discrete
- \+ *lemma* nhds_top
- \- *lemma* t2_space_top
- \+ *lemma* tendsto_pure_nhds

Modified order/filter.lean
- \+ *lemma* filter.map_prod
- \+ *lemma* filter.mem_map_seq_iff
- \+ *lemma* filter.mem_pure_iff
- \+ *lemma* filter.prod_eq
- \+ *lemma* filter.tendsto_const_pure
- \+ *lemma* filter.tendsto_pure_pure



## [2018-10-18 23:05:00+02:00](https://github.com/leanprover-community/mathlib/commit/99e14cd)
feat(group_theory/quotient_group): add map : quotient N -> quotient M
#### Estimated changes
Modified group_theory/quotient_group.lean
- \+ *def* quotient_group.map



## [2018-10-18 23:02:03+02:00](https://github.com/leanprover-community/mathlib/commit/f52d2cc)
chore(group_theory/free_abelian_group, abelianization): rename to_comm_group, to_add_comm_group -> lift
#### Estimated changes
Modified group_theory/abelianization.lean
- \+ *lemma* abelianization.lift.of
- \+ *theorem* abelianization.lift.unique
- \+ *def* abelianization.lift
- \- *def* abelianization.to_comm_group.is_group_hom
- \- *lemma* abelianization.to_comm_group.of
- \- *theorem* abelianization.to_comm_group.unique
- \- *def* abelianization.to_comm_group

Modified group_theory/free_abelian_group.lean
- \+ *lemma* free_abelian_group.lift.map_hom
- \+ *def* free_abelian_group.lift.universal
- \+ *def* free_abelian_group.lift
- \- *def* free_abelian_group.to_add_comm_group.UMP
- \- *def* free_abelian_group.to_add_comm_group

Modified group_theory/subgroup.lean
- \+ *lemma* group.closure_subset_iff

Modified linear_algebra/tensor_product.lean




## [2018-10-18 13:48:14+02:00](https://github.com/leanprover-community/mathlib/commit/c3e489c)
chore(data/fin): add cast_add
#### Estimated changes
Modified data/fin.lean
- \+ *def* fin.cast_add
- \+/\- *def* fin.cast_le
- \+/\- *def* fin.cast_succ



## [2018-10-18 09:43:01+02:00](https://github.com/leanprover-community/mathlib/commit/f2beca8)
feat(ring_theory): prove principal_ideal_domain is unique factorization domain
#### Estimated changes
Modified linear_algebra/submodule.lean
- \+ *lemma* submodule.mem_span_singleton
- \+ *lemma* submodule.span_singleton_subset

Modified ring_theory/associated.lean
- \- *theorem* associated.associated_of_dvd_dvd
- \- *theorem* associated.associated_one_iff_is_unit
- \- *theorem* associated.associated_one_of_associated_mul_one
- \- *theorem* associated.associated_one_of_mul_eq_one
- \- *theorem* associated.associated_zero_iff_eq_zero
- \- *theorem* associated.unit_associated_one
- \+ *lemma* associated_mul_mul
- \+ *theorem* associated_of_dvd_dvd
- \+ *theorem* associated_one_iff_is_unit
- \+ *theorem* associated_one_of_associated_mul_one
- \+ *theorem* associated_one_of_mul_eq_one
- \+ *theorem* associated_zero_iff_eq_zero
- \+ *lemma* associates.dvd_eq_le
- \+ *lemma* associates.eq_of_mul_eq_mul_left
- \+ *lemma* associates.exists_mem_multiset_le_of_prime
- \+ *lemma* associates.le_of_mul_le_mul_left
- \+ *lemma* associates.one_or_eq_of_le_of_prime
- \+ *def* associates.prime
- \+ *lemma* associates.prime_mk
- \+ *lemma* exists_mem_multiset_dvd_of_prime
- \+/\- *theorem* is_unit_iff_dvd_one
- \+/\- *theorem* is_unit_iff_forall_dvd
- \- *theorem* is_unit_mul_units
- \+ *lemma* is_unit_of_dvd_one
- \+ *theorem* is_unit_of_mul_one
- \+ *lemma* not_prime_zero
- \+ *def* prime
- \+ *theorem* unit_associated_one
- \+ *theorem* units.is_unit_mul_units
- \- *theorem* units.is_unit_of_mul_one

Modified ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* is_prime_ideal.to_maximal_ideal
- \+/\- *lemma* mod_mem_iff
- \+ *lemma* principal_ideal_domain.associated_of_associated_prod_prod
- \+ *lemma* principal_ideal_domain.associates_prime_of_irreducible
- \+ *lemma* principal_ideal_domain.eq_of_prod_eq_associates
- \+ *lemma* principal_ideal_domain.exists_factors
- \+ *lemma* principal_ideal_domain.factors_decreasing
- \+ *lemma* principal_ideal_domain.factors_spec
- \+ *lemma* principal_ideal_domain.is_maximal_ideal_of_irreducible
- \+ *lemma* principal_ideal_domain.is_noetherian_ring
- \+ *lemma* principal_ideal_domain.prime_of_irreducible



## [2018-10-18 09:41:00+02:00](https://github.com/leanprover-community/mathlib/commit/7b876a2)
cleanup(data/nat/choose,binomial): move binomial into choose
#### Estimated changes
Modified data/complex/exponential.lean


Deleted data/nat/binomial.lean
- \- *theorem* add_pow

Modified data/nat/choose.lean
- \+ *theorem* add_pow

Modified data/padics/hensel.lean


Modified data/polynomial.lean




## [2018-10-18 09:08:54+02:00](https://github.com/leanprover-community/mathlib/commit/a46e8f7)
cleanup(ring_theory/principal_ideal_domain): restructure
#### Estimated changes
Modified ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* is_prime_ideal.to_maximal_ideal



## [2018-10-18 00:33:42+02:00](https://github.com/leanprover-community/mathlib/commit/a3ac630)
feat(algebra,group_theory): add various closure properties of subgroup and is_group_hom w.r.t gsmul, prod, sum
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.gsmul_sum
- \+ *lemma* finset.prod_eq_one
- \+ *lemma* is_group_hom.finset_prod
- \+ *lemma* is_group_hom.multiset_prod
- \+ *lemma* is_group_hom_finset_prod

Modified algebra/group.lean
- \+ *lemma* is_add_group_hom_sub
- \+ *lemma* is_group_hom_inv
- \+ *lemma* is_group_hom_mul

Modified algebra/group_power.lean
- \+ *theorem* gsmul_neg
- \+ *theorem* gsmul_sub
- \+ *theorem* is_add_group_hom.gsmul
- \+ *theorem* is_add_group_hom.smul
- \+ *theorem* is_add_group_hom_gsmul

Modified algebra/pi_instances.lean
- \+ *lemma* pi.finset_prod_apply
- \+ *lemma* pi.list_prod_apply
- \+ *lemma* pi.multiset_prod_apply

Modified group_theory/subgroup.lean
- \+ *theorem* is_add_subgroup.sub_mem

Modified group_theory/submonoid.lean
- \+ *lemma* is_submonoid.finset_prod_mem
- \+/\- *lemma* is_submonoid.list_prod_mem
- \+ *lemma* is_submonoid.multiset_prod_mem



## [2018-10-17 23:01:03+02:00](https://github.com/leanprover-community/mathlib/commit/ea962a7)
chore(analysis/topology/continuity): locally_compact_space is Prop
#### Estimated changes
Modified analysis/topology/continuity.lean




## [2018-10-17 22:49:26+02:00](https://github.com/leanprover-community/mathlib/commit/bac655d)
feature(data/vector2, data/list): add insert_nth for vectors and lists
#### Estimated changes
Modified data/equiv/fin.lean


Modified data/fin.lean
- \+ *lemma* fin.cast_succ_inj
- \+ *lemma* fin.eq_iff_veq
- \+ *lemma* fin.pred_inj

Modified data/list/basic.lean
- \+ *def* list.insert_nth
- \+ *lemma* list.insert_nth_comm
- \+ *lemma* list.insert_nth_nil
- \+ *lemma* list.insert_nth_remove_nth_of_ge
- \+ *lemma* list.insert_nth_remove_nth_of_le
- \+ *lemma* list.length_insert_nth
- \+ *lemma* list.modify_nth_tail_id
- \+ *lemma* list.modify_nth_tail_modify_nth_tail
- \+ *lemma* list.modify_nth_tail_modify_nth_tail_le
- \+ *lemma* list.modify_nth_tail_modify_nth_tail_same
- \+ *lemma* list.remove_nth_insert_nth

Modified data/vector2.lean
- \+ *def* vector.insert_nth
- \+ *lemma* vector.insert_nth_comm
- \+ *lemma* vector.insert_nth_val
- \+ *def* vector.m_of_fn
- \+ *def* vector.mmap
- \+ *lemma* vector.remove_nth_insert_nth
- \+ *lemma* vector.remove_nth_insert_nth_ne
- \+ *lemma* vector.remove_nth_val
- \- *def* vector.{u}



## [2018-10-17 20:57:36+02:00](https://github.com/leanprover-community/mathlib/commit/085b1bc)
cleanup(algebra/group_power): remove inactive to_additive
#### Estimated changes
Modified algebra/group_power.lean




## [2018-10-17 20:56:45+02:00](https://github.com/leanprover-community/mathlib/commit/1008f08)
cleanup(tactic): remove example
#### Estimated changes
Modified tactic/interactive.lean




## [2018-10-17 16:12:26+02:00](https://github.com/leanprover-community/mathlib/commit/5a8e28d)
doc(docs/tactic): unify choose doc ([#426](https://github.com/leanprover-community/mathlib/pull/426))
#### Estimated changes
Modified docs/tactics.md


Modified tactic/interactive.lean




## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/72308d8)
chore(data/fin): use uniform names; restructure
#### Estimated changes
Modified data/equiv/fin.lean
- \+ *def* fin_one_equiv
- \+ *def* fin_two_equiv
- \+ *def* fin_zero_equiv

Modified data/fin.lean
- \+/\- *def* fin.add_nat
- \+ *lemma* fin.add_nat_val
- \- *def* fin.ascend
- \- *lemma* fin.ascend_descend
- \- *theorem* fin.ascend_ne
- \+/\- *def* fin.cases
- \+/\- *theorem* fin.cases_succ
- \+/\- *theorem* fin.cases_zero
- \+ *def* fin.cast
- \+ *def* fin.cast_le
- \+ *def* fin.cast_lt
- \+ *lemma* fin.cast_lt_val
- \+ *def* fin.cast_succ
- \+ *lemma* fin.cast_succ_cast_lt
- \+ *lemma* fin.cast_succ_val
- \- *def* fin.descend
- \- *lemma* fin.descend_ascend
- \- *theorem* fin.eq_of_lt_succ_of_not_lt
- \- *lemma* fin.fin.raise_val
- \- *def* fin.fin_zero_elim
- \+ *lemma* fin.le_iff_val_le_val
- \- *def* fin.lower
- \- *def* fin.lower_left
- \- *def* fin.lower_right
- \- *lemma* fin.lower_val
- \+ *lemma* fin.lt_iff_val_lt_val
- \- *def* fin.nat_add
- \+ *def* fin.pred_above
- \+ *lemma* fin.pred_above_succ_above
- \- *def* fin.raise
- \- *lemma* fin.raise_lower
- \- *def* fin.raise_nat
- \- *lemma* fin.raise_val
- \+ *def* fin.sub_nat
- \+ *lemma* fin.sub_nat_val
- \+ *def* fin.succ_above
- \+ *lemma* fin.succ_above_descend
- \+ *theorem* fin.succ_above_ne
- \+/\- *theorem* fin.succ_rec_on_succ
- \+/\- *theorem* fin.succ_rec_on_zero
- \+ *lemma* fin.zero_le
- \+ *def* fin_zero_elim

Modified data/nat/basic.lean
- \+ *theorem* nat.eq_of_lt_succ_of_not_lt



## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/d2b3940)
feat(data/fin): ascend / descend for fin
#### Estimated changes
Modified data/fin.lean
- \- *theorem* eq_of_lt_succ_of_not_lt
- \+ *def* fin.ascend
- \+ *lemma* fin.ascend_descend
- \+ *theorem* fin.ascend_ne
- \+/\- *def* fin.cases
- \+/\- *theorem* fin.cases_succ
- \+/\- *theorem* fin.cases_zero
- \+ *def* fin.descend
- \+ *lemma* fin.descend_ascend
- \+ *theorem* fin.eq_of_lt_succ_of_not_lt
- \+ *lemma* fin.fin.raise_val
- \+ *def* fin.fin_zero_elim
- \+ *def* fin.lower
- \+ *def* fin.lower_left
- \+ *def* fin.lower_right
- \+ *lemma* fin.lower_val
- \+ *lemma* fin.pred_succ
- \+ *lemma* fin.raise_lower
- \+ *def* fin.raise_nat
- \+ *lemma* fin.raise_val
- \+ *lemma* fin.succ_pred
- \+/\- *def* fin.succ_rec
- \+/\- *def* fin.succ_rec_on
- \+/\- *theorem* fin.succ_rec_on_succ
- \+/\- *theorem* fin.succ_rec_on_zero
- \- *def* lower_left
- \- *def* lower_right
- \- *def* raise_nat



## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/f789969)
feat(data/finset): add min' / max' for non-empty finset
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* finset.filter_true
- \+ *theorem* finset.le_max'
- \+ *theorem* finset.le_min'
- \+ *theorem* finset.lt_wf
- \+ *def* finset.max'
- \+ *theorem* finset.max'_le
- \+ *theorem* finset.max'_mem
- \+ *def* finset.min'
- \+ *theorem* finset.min'_le
- \+ *theorem* finset.min'_lt_max'
- \+ *theorem* finset.min'_mem



## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/ef9566d)
feat(data/equiv): equivalences for fin * fin and fin + fin
#### Estimated changes
Modified data/equiv/basic.lean
- \- *theorem* equiv.apply_eq_iff_eq_inverse_apply
- \+ *lemma* equiv.eq_symm_apply
- \+/\- *lemma* equiv.ext
- \+ *lemma* equiv.perm.ext
- \+ *lemma* equiv.symm_apply_eq

Added data/equiv/fin.lean
- \+ *def* fin_prod_fin_equiv
- \+ *def* sum_fin_sum_equiv



## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/b085915)
feat(data/list): length_attach, nth_le_attach, nth_le_range, of_fn_eq_pmap, nodup_of_fn (by @kckennylau)
#### Estimated changes
Modified data/fintype.lean
- \+/\- *lemma* finset.coe_univ

Modified data/list/basic.lean
- \+ *lemma* list.length_attach
- \+/\- *theorem* list.length_of_fn
- \+ *theorem* list.nodup_of_fn
- \+ *lemma* list.nth_le_attach
- \+/\- *theorem* list.nth_le_of_fn
- \+ *lemma* list.nth_le_range
- \+ *theorem* list.of_fn_eq_pmap



## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/b454dae)
feat(group_theory/perm): swap_mul_swal / swap_swap_apply (by @kckennylau)
#### Estimated changes
Modified data/nat/basic.lean
- \+ *theorem* nat.pred_eq_of_eq_succ

Modified group_theory/perm.lean
- \+/\- *lemma* equiv.perm.eq_sign_of_surjective_hom
- \+/\- *lemma* equiv.perm.sign_aux3_symm_trans_trans
- \+/\- *lemma* equiv.perm.sign_bij
- \+/\- *lemma* equiv.perm.sign_eq_of_is_swap
- \+/\- *lemma* equiv.perm.sign_eq_sign_of_equiv
- \+/\- *lemma* equiv.perm.sign_inv
- \+/\- *lemma* equiv.perm.sign_mul
- \+/\- *lemma* equiv.perm.sign_of_subtype
- \+/\- *lemma* equiv.perm.sign_one
- \+/\- *lemma* equiv.perm.sign_prod_list_swap
- \+ *lemma* equiv.perm.sign_refl
- \+/\- *lemma* equiv.perm.sign_subtype_perm
- \+ *lemma* equiv.perm.sign_swap'
- \+/\- *lemma* equiv.perm.sign_swap
- \+/\- *lemma* equiv.perm.sign_symm_trans_trans
- \+ *lemma* equiv.perm.swap_mul_self
- \+ *lemma* equiv.perm.swap_swap_apply



## [2018-10-17 09:46:54+02:00](https://github.com/leanprover-community/mathlib/commit/530e1d1)
refactor (data/finset): explicit arguments for subset_union_* and inter_subset_*
This change makes them a little easier to apply, and also makes them consistent with their analogues in set.basic.
#### Estimated changes
Modified analysis/topology/infinite_sum.lean


Modified data/finset.lean
- \+/\- *theorem* finset.inter_subset_left
- \+/\- *theorem* finset.inter_subset_right
- \+/\- *theorem* finset.subset_union_left
- \+/\- *theorem* finset.subset_union_right

Modified data/finsupp.lean




## [2018-10-17 09:25:02+02:00](https://github.com/leanprover-community/mathlib/commit/b5cd974)
feat(*): trigonometric functions: exp, log, sin, cos, tan, sinh, cosh, tanh, pi, arcsin, argcos, arg ([#386](https://github.com/leanprover-community/mathlib/pull/386))
* `floor_ring` now is parameterized on a `linear_ordered_ring` instead of extending it.
*
#### Estimated changes
Modified algebra/archimedean.lean
- \+ *lemma* sub_floor_div_mul_lt
- \+ *lemma* sub_floor_div_mul_nonneg

Modified algebra/group_power.lean
- \+ *lemma* inv_pow'
- \+ *lemma* pow_le_one

Modified algebra/ordered_field.lean
- \+ *lemma* div_le_div_of_le_left
- \+ *lemma* one_le_inv

Modified algebra/ordered_ring.lean
- \+ *lemma* mul_le_of_le_one_left
- \+ *lemma* mul_le_of_le_one_right
- \+ *lemma* mul_lt_one_of_nonneg_of_lt_one_left
- \+ *lemma* mul_lt_one_of_nonneg_of_lt_one_right
- \+ *lemma* one_lt_mul_of_le_of_lt
- \+ *lemma* one_lt_mul_of_lt_of_le

Modified analysis/complex.lean
- \+ *lemma* complex.continuous_im
- \- *lemma* complex.continuous_mul
- \+ *lemma* complex.continuous_of_real
- \+ *lemma* complex.continuous_re
- \+ *lemma* complex.uniform_continuous_im
- \+ *lemma* complex.uniform_continuous_of_real
- \+ *lemma* complex.uniform_continuous_re

Added analysis/exponential.lean
- \+ *lemma* complex.arg_I
- \+ *lemma* complex.arg_cos_add_sin_mul_I
- \+ *lemma* complex.arg_eq_arg_iff
- \+ *lemma* complex.arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg
- \+ *lemma* complex.arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg
- \+ *lemma* complex.arg_le_pi
- \+ *lemma* complex.arg_neg_I
- \+ *lemma* complex.arg_neg_one
- \+ *lemma* complex.arg_of_real_of_neg
- \+ *lemma* complex.arg_of_real_of_nonneg
- \+ *lemma* complex.arg_one
- \+ *lemma* complex.arg_real_mul
- \+ *lemma* complex.arg_zero
- \+ *lemma* complex.continuous_cos
- \+ *lemma* complex.continuous_cosh
- \+ *lemma* complex.continuous_exp
- \+ *lemma* complex.continuous_sin
- \+ *lemma* complex.continuous_sinh
- \+ *lemma* complex.continuous_tan
- \+ *lemma* complex.cos_add_pi
- \+ *lemma* complex.cos_add_pi_div_two
- \+ *lemma* complex.cos_add_two_pi
- \+ *lemma* complex.cos_arg
- \+ *lemma* complex.cos_int_mul_two_pi
- \+ *lemma* complex.cos_int_mul_two_pi_add_pi
- \+ *lemma* complex.cos_nat_mul_two_pi
- \+ *lemma* complex.cos_pi
- \+ *lemma* complex.cos_pi_div_two
- \+ *lemma* complex.cos_pi_div_two_sub
- \+ *lemma* complex.cos_pi_sub
- \+ *lemma* complex.cos_sub_pi_div_two
- \+ *lemma* complex.cos_two_pi
- \+ *lemma* complex.exp_inj_of_neg_pi_lt_of_le_pi
- \+ *lemma* complex.exp_log
- \+ *lemma* complex.ext_abs_arg
- \+ *lemma* complex.log_I
- \+ *lemma* complex.log_exp
- \+ *lemma* complex.log_im
- \+ *lemma* complex.log_neg_I
- \+ *lemma* complex.log_neg_one
- \+ *lemma* complex.log_one
- \+ *lemma* complex.log_re
- \+ *lemma* complex.log_zero
- \+ *lemma* complex.neg_pi_lt_arg
- \+ *lemma* complex.of_real_log
- \+ *lemma* complex.sin_add_pi
- \+ *lemma* complex.sin_add_pi_div_two
- \+ *lemma* complex.sin_add_two_pi
- \+ *lemma* complex.sin_arg
- \+ *lemma* complex.sin_int_mul_pi
- \+ *lemma* complex.sin_nat_mul_pi
- \+ *lemma* complex.sin_pi
- \+ *lemma* complex.sin_pi_div_two
- \+ *lemma* complex.sin_pi_div_two_sub
- \+ *lemma* complex.sin_pi_sub
- \+ *lemma* complex.sin_sub_pi_div_two
- \+ *lemma* complex.sin_two_pi
- \+ *lemma* complex.tan_arg
- \+ *lemma* complex.tendsto_exp_zero_one
- \+ *lemma* real.abs_div_sqrt_one_add_lt
- \+ *lemma* real.arccos_cos
- \+ *lemma* real.arccos_eq_pi_div_two_sub_arcsin
- \+ *lemma* real.arccos_inj
- \+ *lemma* real.arccos_le_pi
- \+ *lemma* real.arccos_neg
- \+ *lemma* real.arccos_neg_one
- \+ *lemma* real.arccos_nonneg
- \+ *lemma* real.arccos_one
- \+ *lemma* real.arccos_zero
- \+ *lemma* real.arcsin_eq_pi_div_two_sub_arccos
- \+ *lemma* real.arcsin_eq_zero_iff
- \+ *lemma* real.arcsin_inj
- \+ *lemma* real.arcsin_le_pi_div_two
- \+ *lemma* real.arcsin_neg
- \+ *lemma* real.arcsin_neg_one
- \+ *lemma* real.arcsin_nonneg
- \+ *lemma* real.arcsin_nonpos
- \+ *lemma* real.arcsin_one
- \+ *lemma* real.arcsin_pos
- \+ *lemma* real.arcsin_sin
- \+ *lemma* real.arcsin_zero
- \+ *lemma* real.arctan_lt_pi_div_two
- \+ *lemma* real.arctan_neg
- \+ *lemma* real.arctan_tan
- \+ *lemma* real.arctan_zero
- \+ *lemma* real.continuous_cos
- \+ *lemma* real.continuous_cosh
- \+ *lemma* real.continuous_exp
- \+ *lemma* real.continuous_sin
- \+ *lemma* real.continuous_sinh
- \+ *lemma* real.continuous_tan
- \+ *lemma* real.cos_add_pi
- \+ *lemma* real.cos_add_pi_div_two
- \+ *lemma* real.cos_add_two_pi
- \+ *lemma* real.cos_arccos
- \+ *lemma* real.cos_arcsin
- \+ *lemma* real.cos_arcsin_nonneg
- \+ *lemma* real.cos_arctan
- \+ *lemma* real.cos_eq_one_iff
- \+ *lemma* real.cos_eq_one_iff_of_lt_of_lt
- \+ *lemma* real.cos_inj_of_nonneg_of_le_pi
- \+ *lemma* real.cos_int_mul_two_pi
- \+ *lemma* real.cos_int_mul_two_pi_add_pi
- \+ *lemma* real.cos_le_cos_of_nonneg_of_le_pi
- \+ *lemma* real.cos_lt_cos_of_nonneg_of_le_pi
- \+ *lemma* real.cos_lt_cos_of_nonneg_of_le_pi_div_two
- \+ *lemma* real.cos_nat_mul_two_pi
- \+ *lemma* real.cos_neg_of_pi_div_two_lt_of_lt
- \+ *lemma* real.cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two
- \+ *lemma* real.cos_nonpos_of_pi_div_two_le_of_le
- \+ *lemma* real.cos_pi
- \+ *lemma* real.cos_pi_div_two
- \+ *lemma* real.cos_pi_div_two_sub
- \+ *lemma* real.cos_pi_sub
- \+ *lemma* real.cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two
- \+ *lemma* real.cos_sub_pi_div_two
- \+ *lemma* real.cos_two_pi
- \+ *lemma* real.div_sqrt_one_add_lt_one
- \+ *lemma* real.exists_cos_eq_zero
- \+ *lemma* real.exists_exp_eq_of_pos
- \+ *lemma* real.exists_sin_eq
- \+ *lemma* real.exp_log
- \+ *lemma* real.log_exp
- \+ *lemma* real.log_one
- \+ *lemma* real.log_zero
- \+ *lemma* real.neg_one_lt_div_sqrt_one_add
- \+ *lemma* real.neg_pi_div_two_le_arcsin
- \+ *lemma* real.neg_pi_div_two_lt_arctan
- \+ *lemma* real.one_le_pi_div_two
- \+ *lemma* real.pi_div_two_le_two
- \+ *lemma* real.pi_div_two_pos
- \+ *lemma* real.pi_le_four
- \+ *lemma* real.pi_pos
- \+ *lemma* real.sin_add_pi
- \+ *lemma* real.sin_add_pi_div_two
- \+ *lemma* real.sin_add_two_pi
- \+ *lemma* real.sin_arccos
- \+ *lemma* real.sin_arcsin
- \+ *lemma* real.sin_arctan
- \+ *lemma* real.sin_eq_zero_iff
- \+ *lemma* real.sin_eq_zero_iff_cos_eq
- \+ *lemma* real.sin_eq_zero_iff_of_lt_of_lt
- \+ *lemma* real.sin_inj_of_le_of_le_pi_div_two
- \+ *lemma* real.sin_int_mul_pi
- \+ *lemma* real.sin_le_sin_of_le_of_le_pi_div_two
- \+ *lemma* real.sin_lt_sin_of_le_of_le_pi_div_two
- \+ *lemma* real.sin_nat_mul_pi
- \+ *lemma* real.sin_neg_of_neg_of_neg_pi_lt
- \+ *lemma* real.sin_nonneg_of_nonneg_of_le_pi
- \+ *lemma* real.sin_nonpos_of_nonnpos_of_neg_pi_le
- \+ *lemma* real.sin_pi
- \+ *lemma* real.sin_pi_div_two
- \+ *lemma* real.sin_pi_div_two_sub
- \+ *lemma* real.sin_pi_sub
- \+ *lemma* real.sin_pos_of_pos_of_lt_pi
- \+ *lemma* real.sin_sub_pi_div_two
- \+ *lemma* real.sin_two_pi
- \+ *lemma* real.tan_arctan
- \+ *lemma* real.tan_inj_of_lt_of_lt_pi_div_two
- \+ *lemma* real.tan_lt_tan_of_lt_of_lt_pi_div_two
- \+ *lemma* real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
- \+ *lemma* real.tan_neg_of_neg_of_pi_div_two_lt
- \+ *lemma* real.tan_nonneg_of_nonneg_of_le_pi_div_two
- \+ *lemma* real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le
- \+ *lemma* real.tan_pos_of_pos_of_lt_pi_div_two
- \+ *lemma* real.tan_surjective
- \+ *lemma* real.two_le_pi
- \+ *lemma* real.two_pi_pos

Modified analysis/real.lean
- \- *lemma* real.continuous_mul
- \+ *lemma* real.intermediate_value'
- \+ *lemma* real.intermediate_value

Modified data/complex/basic.lean
- \+ *lemma* complex.I_mul_I
- \+ *lemma* complex.abs_cast_nat
- \+ *lemma* complex.abs_im_div_abs_le_one
- \+ *lemma* complex.abs_re_div_abs_le_one
- \+ *lemma* complex.abs_two
- \+ *lemma* complex.bit0_im
- \+ *lemma* complex.bit0_re
- \+ *lemma* complex.bit1_im
- \+ *lemma* complex.bit1_re
- \+ *lemma* complex.conj_neg_I
- \+ *lemma* complex.conj_pow
- \+ *lemma* complex.conj_sub
- \+ *lemma* complex.conj_two
- \+ *lemma* complex.eq_lim_of_const_equiv
- \+ *lemma* complex.im_const_equiv_of_const_equiv
- \+ *lemma* complex.is_cau_seq_abs
- \+ *lemma* complex.is_cau_seq_conj
- \+ *lemma* complex.lim_abs
- \+ *lemma* complex.lim_add
- \+ *lemma* complex.lim_conj
- \+ *lemma* complex.lim_const
- \+ *lemma* complex.lim_eq_lim_of_equiv
- \+ *lemma* complex.lim_eq_of_equiv_const
- \+ *lemma* complex.lim_eq_zero_iff
- \+ *lemma* complex.lim_inv
- \+ *lemma* complex.lim_mul
- \+ *lemma* complex.lim_mul_lim
- \+ *lemma* complex.lim_neg
- \+ *lemma* complex.norm_sq_eq_abs
- \+ *lemma* complex.of_real_pow
- \+/\- *lemma* complex.of_real_zero
- \+ *lemma* complex.re_const_equiv_of_const_equiv

Added data/complex/exponential.lean
- \+ *lemma* abv_sum_le_sum_abv
- \+ *lemma* cauchy_product
- \+ *lemma* complex.abs_cos_add_sin_mul_I
- \+ *lemma* complex.abs_exp_eq_iff_re_eq
- \+ *lemma* complex.abs_exp_of_real
- \+ *lemma* complex.abs_exp_sub_one_le
- \+ *def* complex.cos
- \+ *lemma* complex.cos_add
- \+ *lemma* complex.cos_conj
- \+ *lemma* complex.cos_neg
- \+ *lemma* complex.cos_of_real_im
- \+ *lemma* complex.cos_of_real_re
- \+ *lemma* complex.cos_sub
- \+ *lemma* complex.cos_two_mul
- \+ *lemma* complex.cos_zero
- \+ *def* complex.cosh
- \+ *lemma* complex.cosh_add
- \+ *lemma* complex.cosh_conj
- \+ *lemma* complex.cosh_neg
- \+ *lemma* complex.cosh_of_real_im
- \+ *lemma* complex.cosh_of_real_re
- \+ *lemma* complex.cosh_sub
- \+ *lemma* complex.cosh_zero
- \+ *def* complex.exp'
- \+ *def* complex.exp
- \+ *lemma* complex.exp_add
- \+ *lemma* complex.exp_add_mul_I
- \+ *lemma* complex.exp_bound
- \+ *lemma* complex.exp_conj
- \+ *lemma* complex.exp_eq_exp_re_mul_sin_add_cos
- \+ *lemma* complex.exp_mul_I
- \+ *lemma* complex.exp_ne_zero
- \+ *lemma* complex.exp_neg
- \+ *lemma* complex.exp_of_real_im
- \+ *lemma* complex.exp_of_real_re
- \+ *lemma* complex.exp_sub
- \+ *lemma* complex.exp_zero
- \+ *lemma* complex.is_cau_abs_exp
- \+ *lemma* complex.is_cau_exp
- \+ *lemma* complex.of_real_cos
- \+ *lemma* complex.of_real_cos_of_real_re
- \+ *lemma* complex.of_real_cosh
- \+ *lemma* complex.of_real_cosh_of_real_re
- \+ *lemma* complex.of_real_exp
- \+ *lemma* complex.of_real_exp_of_real_re
- \+ *lemma* complex.of_real_sin
- \+ *lemma* complex.of_real_sin_of_real_re
- \+ *lemma* complex.of_real_sinh
- \+ *lemma* complex.of_real_sinh_of_real_re
- \+ *lemma* complex.of_real_tan
- \+ *lemma* complex.of_real_tan_of_real_re
- \+ *lemma* complex.of_real_tanh
- \+ *lemma* complex.of_real_tanh_of_real_re
- \+ *def* complex.sin
- \+ *lemma* complex.sin_add
- \+ *lemma* complex.sin_conj
- \+ *lemma* complex.sin_neg
- \+ *lemma* complex.sin_of_real_im
- \+ *lemma* complex.sin_of_real_re
- \+ *lemma* complex.sin_pow_two_add_cos_pow_two
- \+ *lemma* complex.sin_sub
- \+ *lemma* complex.sin_two_mul
- \+ *lemma* complex.sin_zero
- \+ *def* complex.sinh
- \+ *lemma* complex.sinh_add
- \+ *lemma* complex.sinh_conj
- \+ *lemma* complex.sinh_neg
- \+ *lemma* complex.sinh_of_real_im
- \+ *lemma* complex.sinh_of_real_re
- \+ *lemma* complex.sinh_sub
- \+ *lemma* complex.sinh_zero
- \+ *lemma* complex.sum_div_fact_le
- \+ *def* complex.tan
- \+ *lemma* complex.tan_conj
- \+ *lemma* complex.tan_eq_sin_div_cos
- \+ *lemma* complex.tan_neg
- \+ *lemma* complex.tan_of_real_im
- \+ *lemma* complex.tan_of_real_re
- \+ *lemma* complex.tan_zero
- \+ *def* complex.tanh
- \+ *lemma* complex.tanh_conj
- \+ *lemma* complex.tanh_eq_sinh_div_cosh
- \+ *lemma* complex.tanh_neg
- \+ *lemma* complex.tanh_of_real_im
- \+ *lemma* complex.tanh_of_real_re
- \+ *lemma* complex.tanh_zero
- \+ *lemma* forall_ge_le_of_forall_le_succ
- \+ *lemma* geo_sum_eq
- \+ *lemma* geo_sum_inv_eq
- \+ *lemma* is_cau_geo_series
- \+ *lemma* is_cau_geo_series_const
- \+ *lemma* is_cau_of_decreasing_bounded
- \+ *lemma* is_cau_of_mono_bounded
- \+ *lemma* is_cau_series_of_abv_cau
- \+ *lemma* is_cau_series_of_abv_le_cau
- \+ *lemma* real.abs_cos_le_one
- \+ *lemma* real.abs_exp
- \+ *lemma* real.abs_sin_le_one
- \+ *lemma* real.add_one_le_exp_of_nonneg
- \+ *def* real.cos
- \+ *lemma* real.cos_add
- \+ *lemma* real.cos_bound
- \+ *lemma* real.cos_le_one
- \+ *lemma* real.cos_neg
- \+ *lemma* real.cos_one_le
- \+ *lemma* real.cos_one_pos
- \+ *lemma* real.cos_pos_of_le_one
- \+ *lemma* real.cos_pow_two_le_one
- \+ *lemma* real.cos_sub
- \+ *lemma* real.cos_two_mul
- \+ *lemma* real.cos_two_neg
- \+ *lemma* real.cos_zero
- \+ *def* real.cosh
- \+ *lemma* real.cosh_add
- \+ *lemma* real.cosh_neg
- \+ *lemma* real.cosh_sub
- \+ *lemma* real.cosh_zero
- \+ *def* real.exp
- \+ *lemma* real.exp_add
- \+ *lemma* real.exp_injective
- \+ *lemma* real.exp_le_exp
- \+ *lemma* real.exp_lt_exp
- \+ *lemma* real.exp_ne_zero
- \+ *lemma* real.exp_neg
- \+ *lemma* real.exp_pos
- \+ *lemma* real.exp_sub
- \+ *lemma* real.exp_zero
- \+ *lemma* real.neg_one_le_cos
- \+ *lemma* real.neg_one_le_sin
- \+ *lemma* real.one_le_exp
- \+ *def* real.sin
- \+ *lemma* real.sin_add
- \+ *lemma* real.sin_bound
- \+ *lemma* real.sin_le_one
- \+ *lemma* real.sin_neg
- \+ *lemma* real.sin_pos_of_pos_of_le_one
- \+ *lemma* real.sin_pos_of_pos_of_le_two
- \+ *lemma* real.sin_pow_two_add_cos_pow_two
- \+ *lemma* real.sin_pow_two_le_one
- \+ *lemma* real.sin_sub
- \+ *lemma* real.sin_two_mul
- \+ *lemma* real.sin_zero
- \+ *def* real.sinh
- \+ *lemma* real.sinh_add
- \+ *lemma* real.sinh_neg
- \+ *lemma* real.sinh_sub
- \+ *lemma* real.sinh_zero
- \+ *def* real.tan
- \+ *lemma* real.tan_eq_sin_div_cos
- \+ *lemma* real.tan_neg
- \+ *lemma* real.tan_zero
- \+ *def* real.tanh
- \+ *lemma* real.tanh_eq_sinh_div_cosh
- \+ *lemma* real.tanh_neg
- \+ *lemma* real.tanh_zero
- \+ *lemma* series_ratio_test
- \+ *lemma* sum_range_diag_flip
- \+ *lemma* sum_range_sub_sum_range

Modified data/int/basic.lean
- \+ *lemma* int.cast_two
- \+ *lemma* int.mod_two_eq_zero_or_one

Modified data/nat/basic.lean
- \+ *lemma* nat.fact_mul_pow_le_fact

Modified data/nat/cast.lean
- \+ *lemma* nat.cast_two

Modified data/real/basic.lean
- \+ *lemma* real.le_lim
- \+ *lemma* real.lim_le
- \+ *lemma* real.lim_lt
- \+ *lemma* real.lt_lim

Modified data/real/cau_seq.lean
- \+ *lemma* cau_seq.le_of_eq_of_le
- \+ *lemma* cau_seq.le_of_exists
- \+ *lemma* cau_seq.le_of_le_of_eq
- \+ *lemma* is_absolute_value.abv_pow



## [2018-10-16 13:07:50+02:00](https://github.com/leanprover-community/mathlib/commit/792c673)
feat(order/galois_connection): make arguemnts to dual implicit
#### Estimated changes
Modified order/galois_connection.lean




## [2018-10-15 17:21:09+02:00](https://github.com/leanprover-community/mathlib/commit/80d688e)
feat(data/nat/choose): nat.prime.dvd_choose ([#419](https://github.com/leanprover-community/mathlib/pull/419))
* feat(data/nat/choose): nat/prime.dvd_choose
* use nat namespace
* Update prime.lean
* improve readability
#### Estimated changes
Modified data/nat/choose.lean
- \+ *lemma* nat.prime.dvd_choose

Modified data/nat/prime.lean
- \+ *lemma* nat.prime.dvd_fact



## [2018-10-15 15:12:23+02:00](https://github.com/leanprover-community/mathlib/commit/c5930f5)
feat(group_theory.order_of_element): subgroups of cyclic groups are cyclic ([#423](https://github.com/leanprover-community/mathlib/pull/423))
* feat(group_theory.order_of_element): subgroups of cyclic groups are cyclic
* delete new line
#### Estimated changes
Modified group_theory/order_of_element.lean


Modified group_theory/subgroup.lean
- \+ *lemma* is_add_subgroup.gsmul_coe
- \+ *lemma* is_subgroup.coe_gpow
- \+ *lemma* is_subgroup.coe_inv

Modified group_theory/submonoid.lean
- \+ *lemma* is_add_submonoid.smul_coe
- \+ *lemma* is_submonoid.coe_mul
- \+ *lemma* is_submonoid.coe_one
- \+ *lemma* is_submonoid.coe_pow



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/a33ab12)
refactor(analysis/topology): move separation ring to quotient_topological_structures
#### Estimated changes
Modified analysis/topology/completion.lean
- \- *lemma* uniform_space.eq_mpr_heq
- \- *lemma* uniform_space.ring_sep_quot
- \- *lemma* uniform_space.ring_sep_rel

Modified analysis/topology/quotient_topological_structures.lean
- \- *lemma* is_open_map_mul_left
- \- *lemma* is_open_map_mul_right
- \- *lemma* quotient_ring.quotient_map
- \+ *lemma* quotient_ring.quotient_map_coe_coe
- \+ *lemma* uniform_space.ring_sep_quot
- \+ *lemma* uniform_space.ring_sep_rel
- \+ *def* uniform_space.sep_quot_equiv_ring_quot
- \+ *lemma* {u}

Modified analysis/topology/topological_structures.lean
- \+ *lemma* is_open_map_mul_left
- \+ *lemma* is_open_map_mul_right



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/1308077)
feature(data/equiv/algebra): add mul left/right and inverse as equivalences
#### Estimated changes
Modified analysis/topology/topological_structures.lean


Added data/equiv/algebra.lean


Modified data/equiv/basic.lean




## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/c8ecae8)
feature(analysis/topology/continuity): start homeomorphism
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* homeomorph.coe_eq_to_equiv
- \+ *lemma* homeomorph.coinduced_eq
- \+ *lemma* homeomorph.image_symm
- \+ *lemma* homeomorph.induced_eq
- \+ *lemma* homeomorph.preimage_symm
- \+ *def* homeomorph.prod_assoc
- \+ *def* homeomorph.prod_comm
- \+ *def* homeomorph.prod_congr
- \+ *lemma* homeomorph.range_coe
- \+ *lemma* homeomorph.self_comp_symm
- \+ *lemma* homeomorph.symm_comp_self
- \+ *structure* homeomorph

Modified data/equiv/basic.lean
- \+/\- *def* equiv.prod_congr



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/af434b5)
refactor(analysis/topology): move is_open_map to continuity
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* is_open_map.of_inverse
- \+ *lemma* is_open_map.to_quotient_map
- \+ *def* is_open_map
- \+ *lemma* is_open_map_iff_nhds_le
- \- *lemma* quotient_map.continuous
- \- *lemma* quotient_map.continuous_iff
- \- *lemma* quotient_map_compose
- \- *lemma* quotient_map_id
- \- *lemma* quotient_map_of_quotient_map_compose

Modified analysis/topology/quotient_topological_structures.lean
- \- *lemma* is_open_coinduced
- \- *lemma* is_open_map.of_inverse
- \- *lemma* is_open_map.to_quotient_map
- \- *def* is_open_map
- \- *lemma* is_open_map_iff_nhds_le

Modified analysis/topology/topological_space.lean
- \+ *lemma* is_open_coinduced
- \+ *lemma* is_open_induced_iff



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/29675ad)
refactor(analysis/topology/topological_structures): use to_additive to derive topological_add_monoid and topological_add_group
#### Estimated changes
Modified analysis/topology/quotient_topological_structures.lean
- \- *lemma* continuous_inv'
- \- *lemma* continuous_inv
- \- *lemma* is_open_add_translate
- \+ *lemma* is_open_coinduced
- \+/\- *lemma* is_open_map.of_inverse
- \- *lemma* is_open_map.quotient_map_of_open_of_surj_of_cont
- \+ *lemma* is_open_map.to_quotient_map
- \- *lemma* is_open_map_iff_nhds_sets
- \+ *lemma* is_open_map_mul_left
- \+ *lemma* is_open_map_mul_right
- \- *lemma* is_open_ring_add_translate
- \- *lemma* is_open_translate
- \- *lemma* quotient_add_group.open_coe
- \- *lemma* quotient_add_group_saturate
- \- *lemma* quotient_ring.is_open_map
- \+ *lemma* quotient_ring.is_open_map_coe
- \- *lemma* quotient_ring.open_coe
- \+ *lemma* quotient_ring.quotient_map

Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean
- \- *lemma* continuous_add'
- \- *lemma* continuous_add
- \- *lemma* continuous_finset_sum
- \+ *lemma* continuous_inv'
- \+ *lemma* continuous_inv
- \- *lemma* continuous_list_sum
- \- *lemma* continuous_multiset_sum
- \- *lemma* continuous_neg'
- \- *lemma* continuous_neg
- \- *lemma* exists_nhds_half
- \- *lemma* exists_nhds_quarter
- \+ *lemma* exists_nhds_split4
- \+ *lemma* exists_nhds_split
- \+ *lemma* nhds_one_symm
- \+ *lemma* nhds_translation_mul_inv
- \- *lemma* nhds_zero_symm
- \- *lemma* tendsto_add'
- \- *lemma* tendsto_add
- \- *lemma* tendsto_finset_sum
- \+ *lemma* tendsto_inv
- \- *lemma* tendsto_list_sum
- \- *lemma* tendsto_multiset_sum
- \- *lemma* tendsto_neg



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/75046c2)
chore(data/quot): add setoid.ext
#### Estimated changes
Modified analysis/topology/completion.lean


Modified data/quot.lean
- \+ *lemma* setoid.ext



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/2395183)
feat(analysis/topology/quotient_topological_structures): endow quotient
of topological groups, add groups and rings with a topological whatever
structure
This is not yet sorted. I'd like to push completions before cleaning
this.
#### Estimated changes
Modified analysis/topology/completion.lean
- \+ *lemma* uniform_space.eq_mpr_heq
- \+ *lemma* uniform_space.ring_sep_quot
- \+ *lemma* uniform_space.ring_sep_rel

Added analysis/topology/quotient_topological_structures.lean
- \+ *lemma* continuous_inv'
- \+ *lemma* continuous_inv
- \+ *lemma* is_open_add_translate
- \+ *lemma* is_open_map.of_inverse
- \+ *lemma* is_open_map.quotient_map_of_open_of_surj_of_cont
- \+ *def* is_open_map
- \+ *lemma* is_open_map_iff_nhds_le
- \+ *lemma* is_open_map_iff_nhds_sets
- \+ *lemma* is_open_ring_add_translate
- \+ *lemma* is_open_translate
- \+ *lemma* quotient_add_group.open_coe
- \+ *lemma* quotient_add_group_saturate
- \+ *lemma* quotient_group.open_coe
- \+ *lemma* quotient_group_saturate
- \+ *lemma* quotient_ring.is_open_map
- \+ *lemma* quotient_ring.open_coe
- \+ *lemma* quotient_ring_saturate



## [2018-10-15 13:35:49+02:00](https://github.com/leanprover-community/mathlib/commit/7358605)
feat(analysis/topology/completion): comm_ring on separation quotient, completion (separation_quotient A) is equivalent to completion A
#### Estimated changes
Modified analysis/topology/completion.lean
- \- *lemma* filter.prod_pure_pure
- \- *lemma* uniform_space.cauchy_prod
- \- *lemma* uniform_space.complete_space_separation
- \+ *def* uniform_space.completion.completion_separation_quotient_equiv
- \+ *lemma* uniform_space.completion.ext
- \+ *lemma* uniform_space.completion.extension_map
- \+ *lemma* uniform_space.completion.map_comp
- \+ *lemma* uniform_space.completion.map_id
- \+ *lemma* uniform_space.completion.map_unique
- \+ *lemma* uniform_space.completion.uniform_continuous_completion_separation_quotient_equiv
- \+ *lemma* uniform_space.completion.uniform_continuous_completion_separation_quotient_equiv_symm
- \- *lemma* uniform_space.separated_separation
- \+ *def* uniform_space.separation_quotient.lift
- \+ *lemma* uniform_space.separation_quotient.lift_mk
- \+ *def* uniform_space.separation_quotient.map
- \+ *lemma* uniform_space.separation_quotient.map_comp
- \+ *lemma* uniform_space.separation_quotient.map_id
- \+ *lemma* uniform_space.separation_quotient.map_mk
- \+ *lemma* uniform_space.separation_quotient.map_unique
- \+ *lemma* uniform_space.separation_quotient.uniform_continuous_lift
- \+ *lemma* uniform_space.separation_quotient.uniform_continuous_map
- \+ *def* uniform_space.separation_quotient
- \- *lemma* uniform_space.uniform_continuous_of_const

Modified analysis/topology/continuity.lean
- \+ *lemma* mem_closure2
- \+ *lemma* mem_closure

Modified analysis/topology/topological_structures.lean
- \- *lemma* is_ideal_iff

Modified data/quot.lean
- \+ *lemma* nonempty_quotient_iff

Modified data/set/basic.lean
- \- *lemma* set.image_subset_iff'

Modified order/filter.lean
- \+ *lemma* filter.prod_pure_pure



## [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/13be74f)
feat(analysis/topology/topological_structure): ideal closure is ideal
#### Estimated changes
Modified analysis/topology/topological_structures.lean
- \+ *lemma* is_ideal_iff

Modified data/set/basic.lean
- \+ *lemma* set.image_subset_iff'



## [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/7697a84)
feat(analysis/topology/topological_groups): construct topologies out of a group and a neighbourhood filter at 0
#### Estimated changes
Deleted analysis/topology/complete_groups.lean
- \- *lemma* add_comm_group.is_Z_bilin.neg_left
- \- *lemma* add_comm_group.is_Z_bilin.neg_right
- \- *lemma* add_comm_group.is_Z_bilin.sub_left
- \- *lemma* add_comm_group.is_Z_bilin.sub_right
- \- *lemma* add_comm_group.is_Z_bilin.zero
- \- *lemma* add_comm_group.is_Z_bilin.zero_left
- \- *lemma* add_comm_group.is_Z_bilin.zero_right
- \- *theorem* dense_embedding.extend_Z_bilin
- \- *lemma* is_Z_bilin.tendsto_zero_left
- \- *lemma* is_Z_bilin.tendsto_zero_right
- \- *lemma* tendsto_sub_comap_self

Modified analysis/topology/completion.lean
- \+ *lemma* add_comm_group.is_Z_bilin.neg_left
- \+ *lemma* add_comm_group.is_Z_bilin.neg_right
- \+ *lemma* add_comm_group.is_Z_bilin.sub_left
- \+ *lemma* add_comm_group.is_Z_bilin.sub_right
- \+ *lemma* add_comm_group.is_Z_bilin.zero
- \+ *lemma* add_comm_group.is_Z_bilin.zero_left
- \+ *lemma* add_comm_group.is_Z_bilin.zero_right
- \+ *theorem* dense_embedding.extend_Z_bilin
- \+ *lemma* is_Z_bilin.tendsto_zero_left
- \+ *lemma* is_Z_bilin.tendsto_zero_right
- \+ *lemma* tendsto_sub_comap_self
- \+ *lemma* uniform_space.completion.coe_mul
- \+ *lemma* uniform_space.completion.coe_one
- \+ *lemma* uniform_space.completion.continuous_mul'
- \+ *lemma* uniform_space.completion.continuous_mul
- \+/\- *lemma* uniform_space.completion.dense
- \+ *lemma* uniform_space.completion.dense_embedding_coe

Modified analysis/topology/topological_groups.lean
- \+ *lemma* add_group_with_zero_nhd.add_Z
- \+ *lemma* add_group_with_zero_nhd.exists_Z_half
- \+ *lemma* add_group_with_zero_nhd.neg_Z
- \+ *lemma* add_group_with_zero_nhd.nhds_eq
- \+ *lemma* add_group_with_zero_nhd.nhds_zero_eq_Z
- \- *lemma* half_nhd
- \- *lemma* nhds_translation
- \- *lemma* nhds_zero_symm
- \- *lemma* quarter_nhd
- \+ *lemma* to_uniform_space_eq
- \+ *lemma* topological_add_group_is_uniform
- \+ *lemma* uniformity_eq_comap_nhds_zero'
- \- *lemma* uniformity_eq_comap_nhds_zero
- \- *def* Δ
- \- *def* δ

Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean
- \+ *lemma* exists_nhds_half
- \+ *lemma* exists_nhds_quarter
- \+ *lemma* nhds_translation
- \+ *lemma* nhds_zero_symm

Modified order/filter.lean
- \+/\- *lemma* filter.comap_eq_of_inverse
- \+ *lemma* filter.map_eq_of_inverse



## [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/96d3f95)
doc(analysis/topology/completion): document changed organization
#### Estimated changes
Modified analysis/topology/completion.lean




## [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/fbb6e9b)
feat(analysis/topology): group completion
#### Estimated changes
Modified analysis/real.lean
- \- *theorem* real.Cauchy_eq

Added analysis/topology/complete_groups.lean
- \+ *lemma* add_comm_group.is_Z_bilin.neg_left
- \+ *lemma* add_comm_group.is_Z_bilin.neg_right
- \+ *lemma* add_comm_group.is_Z_bilin.sub_left
- \+ *lemma* add_comm_group.is_Z_bilin.sub_right
- \+ *lemma* add_comm_group.is_Z_bilin.zero
- \+ *lemma* add_comm_group.is_Z_bilin.zero_left
- \+ *lemma* add_comm_group.is_Z_bilin.zero_right
- \+ *theorem* dense_embedding.extend_Z_bilin
- \+ *lemma* is_Z_bilin.tendsto_zero_left
- \+ *lemma* is_Z_bilin.tendsto_zero_right
- \+ *lemma* tendsto_sub_comap_self

Added analysis/topology/completion.lean
- \+ *theorem* Cauchy.Cauchy_eq
- \+ *lemma* Cauchy.dense_embedding_pure_cauchy
- \+ *def* Cauchy.extend
- \+ *lemma* Cauchy.extend_pure_cauchy
- \+ *def* Cauchy.gen
- \+ *lemma* Cauchy.injective_separated_pure_cauchy
- \+ *theorem* Cauchy.mem_uniformity'
- \+ *theorem* Cauchy.mem_uniformity
- \+ *lemma* Cauchy.monotone_gen
- \+ *lemma* Cauchy.nonempty_Cauchy_iff
- \+ *def* Cauchy.prod
- \+ *lemma* Cauchy.prod_pure_cauchy_pure_cauchy
- \+ *def* Cauchy.pure_cauchy
- \+ *lemma* Cauchy.pure_cauchy_dense
- \+ *lemma* Cauchy.uniform_continuous_extend
- \+ *lemma* Cauchy.uniform_continuous_prod
- \+ *lemma* Cauchy.uniform_embedding_pure_cauchy
- \+ *def* Cauchy
- \+ *lemma* filter.prod_pure_pure
- \+ *lemma* uniform_space.cauchy_prod
- \+ *lemma* uniform_space.comap_quotient_eq_uniformity
- \+ *lemma* uniform_space.comap_quotient_le_uniformity
- \+ *lemma* uniform_space.complete_space_separation
- \+ *lemma* uniform_space.completion.coe_add
- \+ *lemma* uniform_space.completion.coe_neg
- \+ *lemma* uniform_space.completion.coe_zero
- \+ *lemma* uniform_space.completion.comap_coe_eq_uniformity
- \+ *lemma* uniform_space.completion.continuous_coe
- \+ *lemma* uniform_space.completion.continuous_extension
- \+ *lemma* uniform_space.completion.continuous_map
- \+ *lemma* uniform_space.completion.continuous_map₂
- \+ *lemma* uniform_space.completion.dense
- \+ *lemma* uniform_space.completion.dense₂
- \+ *lemma* uniform_space.completion.dense₃
- \+ *lemma* uniform_space.completion.extension_coe
- \+ *lemma* uniform_space.completion.induction_on
- \+ *lemma* uniform_space.completion.induction_on₂
- \+ *lemma* uniform_space.completion.induction_on₃
- \+ *lemma* uniform_space.completion.induction_on₄
- \+ *lemma* uniform_space.completion.is_add_group_hom_extension
- \+ *lemma* uniform_space.completion.is_add_group_hom_map
- \+ *lemma* uniform_space.completion.is_add_group_hom_prod
- \+ *lemma* uniform_space.completion.map_coe
- \+ *lemma* uniform_space.completion.map₂_coe_coe
- \+ *lemma* uniform_space.completion.prod_coe_coe
- \+ *lemma* uniform_space.completion.uniform_continuous_coe
- \+ *lemma* uniform_space.completion.uniform_continuous_extension
- \+ *lemma* uniform_space.completion.uniform_continuous_map
- \+ *lemma* uniform_space.completion.uniform_continuous_map₂'
- \+ *lemma* uniform_space.completion.uniform_continuous_prod
- \+ *lemma* uniform_space.completion.uniform_embedding_coe
- \+ *def* uniform_space.completion
- \+ *lemma* uniform_space.eq_of_separated_of_uniform_continuous
- \+ *lemma* uniform_space.separated_of_uniform_continuous
- \+ *lemma* uniform_space.separated_separation
- \+ *lemma* uniform_space.separation_prod
- \+ *def* uniform_space.separation_setoid
- \+ *lemma* uniform_space.uniform_continuous_of_const
- \+ *lemma* uniform_space.uniform_continuous_quotient
- \+ *lemma* uniform_space.uniform_continuous_quotient_lift
- \+ *lemma* uniform_space.uniform_continuous_quotient_lift₂
- \+ *lemma* uniform_space.uniform_continuous_quotient_mk
- \+ *lemma* uniform_space.uniformity_quotient

Modified analysis/topology/continuity.lean
- \+/\- *lemma* dense_embedding.extend_e_eq
- \+/\- *lemma* dense_embedding.extend_eq
- \+ *lemma* embedding.closure_eq_preimage_closure_image

Added analysis/topology/topological_groups.lean
- \+ *lemma* half_nhd
- \+ *lemma* nhds_translation
- \+ *lemma* nhds_zero_symm
- \+ *lemma* quarter_nhd
- \+ *def* topological_add_group.to_uniform_space
- \+ *lemma* uniformity_eq_comap_nhds_zero
- \+ *def* Δ
- \+ *def* δ

Modified analysis/topology/topological_structures.lean
- \- *lemma* dense_or_discrete
- \+ *lemma* group_separation_rel
- \+/\- *lemma* uniform_continuous_add'
- \+/\- *lemma* uniform_continuous_add
- \+/\- *lemma* uniform_continuous_neg'
- \+/\- *lemma* uniform_continuous_neg
- \+ *lemma* uniform_continuous_of_continuous
- \+ *lemma* uniform_continuous_of_tendsto_zero
- \+/\- *lemma* uniform_continuous_sub'
- \+/\- *lemma* uniform_continuous_sub
- \+ *lemma* uniform_embedding_translate
- \+ *lemma* uniformity_eq_comap_nhds_zero
- \+ *lemma* uniformity_translate

Modified analysis/topology/uniform_space.lean
- \- *def* Cauchy.gen
- \- *lemma* Cauchy.injective_separated_pure_cauchy
- \- *theorem* Cauchy.mem_uniformity'
- \- *theorem* Cauchy.mem_uniformity
- \- *lemma* Cauchy.monotone_gen
- \- *def* Cauchy.pure_cauchy
- \- *lemma* Cauchy.pure_cauchy_dense
- \- *lemma* Cauchy.uniform_embedding_pure_cauchy
- \- *def* Cauchy
- \+ *lemma* cauchy_prod
- \- *lemma* comap_quotient_eq_uniformity
- \- *lemma* comap_quotient_le_uniformity
- \- *lemma* complete_space_separation
- \+ *lemma* dense_embedding.continuous_extend_of_cauchy
- \- *lemma* eq_of_separated_of_uniform_continuous
- \+ *lemma* mem_uniformity_of_uniform_continuous_invarant
- \- *lemma* separated_of_uniform_continuous
- \- *lemma* separated_separation
- \- *lemma* separation_prod
- \+ *lemma* uniform_continuous_of_const
- \- *lemma* uniform_continuous_quotient
- \- *lemma* uniform_continuous_quotient_lift
- \- *lemma* uniform_continuous_quotient_lift₂
- \- *lemma* uniform_continuous_quotient_mk
- \+/\- *lemma* uniform_continuous_uniformly_extend
- \+ *lemma* uniform_embedding.embedding
- \- *lemma* uniformity_quotient
- \+/\- *lemma* uniformly_extend_exists
- \+/\- *lemma* uniformly_extend_of_emb
- \+/\- *lemma* uniformly_extend_spec

Modified data/set/basic.lean
- \+ *lemma* set.prod_quotient_preimage_eq_image

Modified data/set/lattice.lean
- \+ *lemma* set.preimage_Inter
- \+ *lemma* set.preimage_bInter

Modified order/basic.lean
- \+ *lemma* dense_or_discrete



## [2018-10-14 23:27:04-04:00](https://github.com/leanprover-community/mathlib/commit/8150f19)
feat(logic/basic): classical.not_not ([#418](https://github.com/leanprover-community/mathlib/pull/418))
* feat(logic/basic): classical.not_not
* mark as protected
#### Estimated changes
Modified logic/basic.lean




## [2018-10-12 23:59:58+02:00](https://github.com/leanprover-community/mathlib/commit/019b236)
fix(category_theory/open_set): Restore the correct order on open_set
#### Estimated changes
Modified category_theory/examples/topological_spaces.lean




## [2018-10-12 10:55:25+02:00](https://github.com/leanprover-community/mathlib/commit/131cf14)
feat(group_theory/quotient_group): add to_additive attribute
#### Estimated changes
Modified group_theory/quotient_group.lean




## [2018-10-12 10:54:58+02:00](https://github.com/leanprover-community/mathlib/commit/c8d3c96)
feat(tactic/interactive): congr' tries harder
#### Estimated changes
Modified tactic/interactive.lean




## [2018-10-11 08:53:11-04:00](https://github.com/leanprover-community/mathlib/commit/62451d3)
cleanup(data/polynomial): simplify proof of coeff_mul_left ([#414](https://github.com/leanprover-community/mathlib/pull/414))
#### Estimated changes
Modified data/polynomial.lean




## [2018-10-11 13:22:43+02:00](https://github.com/leanprover-community/mathlib/commit/0fe2849)
chore(analysis/measure_theory): finish characterization of lintegral
#### Estimated changes
Modified analysis/measure_theory/integration.lean
- \+ *lemma* measure_theory.lintegral_const_mul
- \+ *lemma* measure_theory.lintegral_supr_const
- \+/\- *theorem* measure_theory.simple_func.bind_const
- \+/\- *def* measure_theory.simple_func.const
- \+/\- *theorem* measure_theory.simple_func.const_apply
- \+/\- *lemma* measure_theory.simple_func.const_mul_eq_map
- \+/\- *def* measure_theory.simple_func.map



## [2018-10-10 22:50:06+02:00](https://github.com/leanprover-community/mathlib/commit/40f5565)
feat(analysis/measure_theory): lower Lebesgue integral under addition, supremum
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.prod_hom_rel
- \+ *lemma* finset.prod_image'

Modified analysis/ennreal.lean
- \- *lemma* ennreal.coe_nat
- \+ *lemma* ennreal.finset_sum_supr_nat
- \+ *lemma* ennreal.mul_Sup
- \+ *lemma* ennreal.mul_supr
- \+/\- *lemma* ennreal.supr_add_supr
- \+ *lemma* ennreal.supr_add_supr_of_monotone
- \+ *lemma* ennreal.supr_mul
- \+ *lemma* ennreal.tendsto_coe_nnreal_nhds_top

Modified analysis/measure_theory/borel_space.lean
- \+ *lemma* measure_theory.measurable_coe_int_real
- \+ *lemma* measure_theory.measurable_le

Modified analysis/measure_theory/integration.lean
- \- *def* measure_theory.indicator.size
- \- *def* measure_theory.indicator.to_fun
- \- *theorem* measure_theory.indicator.to_fun_val
- \- *structure* measure_theory.indicator
- \+ *def* measure_theory.lintegral
- \+ *lemma* measure_theory.lintegral_add
- \+ *lemma* measure_theory.lintegral_eq_nnreal
- \+ *lemma* measure_theory.lintegral_eq_supr_eapprox_integral
- \+ *lemma* measure_theory.lintegral_le_lintegral
- \+ *theorem* measure_theory.lintegral_supr
- \+ *lemma* measure_theory.lintegral_zero
- \- *def* measure_theory.simple_func'.bind
- \- *theorem* measure_theory.simple_func'.bind_apply
- \- *theorem* measure_theory.simple_func'.bind_const
- \- *lemma* measure_theory.simple_func'.bind_itg
- \- *lemma* measure_theory.simple_func'.bind_sum_measure
- \- *theorem* measure_theory.simple_func'.coe_def
- \- *theorem* measure_theory.simple_func'.coe_le_coe
- \- *def* measure_theory.simple_func'.const
- \- *theorem* measure_theory.simple_func'.const_apply
- \- *theorem* measure_theory.simple_func'.ext
- \- *lemma* measure_theory.simple_func'.is_measurable_cut
- \- *def* measure_theory.simple_func'.ite
- \- *theorem* measure_theory.simple_func'.ite_apply
- \- *def* measure_theory.simple_func'.itg
- \- *theorem* measure_theory.simple_func'.le_def
- \- *def* measure_theory.simple_func'.map
- \- *theorem* measure_theory.simple_func'.map_apply
- \- *lemma* measure_theory.simple_func'.map_itg
- \- *theorem* measure_theory.simple_func'.measurable
- \- *theorem* measure_theory.simple_func'.mem_range
- \- *def* measure_theory.simple_func'.pair
- \- *theorem* measure_theory.simple_func'.preimage_measurable
- \- *def* measure_theory.simple_func'.restrict
- \- *theorem* measure_theory.simple_func'.restrict_apply
- \- *theorem* measure_theory.simple_func'.restrict_preimage
- \- *def* measure_theory.simple_func'.seq
- \- *lemma* measure_theory.simple_func'.seq_itg
- \- *theorem* measure_theory.simple_func.add_congr
- \+ *lemma* measure_theory.simple_func.add_eq_map₂
- \+ *lemma* measure_theory.simple_func.add_integral
- \- *theorem* measure_theory.simple_func.add_sub_cancel_of_le
- \+ *def* measure_theory.simple_func.approx
- \+ *lemma* measure_theory.simple_func.approx_apply
- \+ *def* measure_theory.simple_func.bind
- \+ *theorem* measure_theory.simple_func.bind_apply
- \+ *theorem* measure_theory.simple_func.bind_const
- \- *theorem* measure_theory.simple_func.coe_add
- \- *theorem* measure_theory.simple_func.coe_def
- \- *theorem* measure_theory.simple_func.coe_le_coe
- \+ *theorem* measure_theory.simple_func.coe_map
- \+ *def* measure_theory.simple_func.const
- \+ *theorem* measure_theory.simple_func.const_apply
- \+ *lemma* measure_theory.simple_func.const_mul_eq_map
- \+ *lemma* measure_theory.simple_func.const_mul_integral
- \+ *def* measure_theory.simple_func.eapprox
- \+ *def* measure_theory.simple_func.ennreal_rat_embed
- \+ *lemma* measure_theory.simple_func.ennreal_rat_embed_encode
- \- *theorem* measure_theory.simple_func.equiv_def
- \- *theorem* measure_theory.simple_func.equiv_iff
- \+ *theorem* measure_theory.simple_func.ext
- \- *theorem* measure_theory.simple_func.finite_range
- \+ *lemma* measure_theory.simple_func.finset_sup_apply
- \+ *def* measure_theory.simple_func.integral
- \+ *lemma* measure_theory.simple_func.integral_congr
- \+ *lemma* measure_theory.simple_func.integral_le_integral
- \+ *lemma* measure_theory.simple_func.integral_sup_le
- \+ *lemma* measure_theory.simple_func.is_measurable_cut
- \+ *def* measure_theory.simple_func.ite
- \+ *theorem* measure_theory.simple_func.ite_apply
- \- *def* measure_theory.simple_func.itg'
- \- *theorem* measure_theory.simple_func.itg'_add
- \- *theorem* measure_theory.simple_func.itg'_eq_sum
- \- *theorem* measure_theory.simple_func.itg'_eq_sum_of_subset
- \- *theorem* measure_theory.simple_func.itg'_indicator
- \- *theorem* measure_theory.simple_func.itg'_mono
- \- *theorem* measure_theory.simple_func.itg'_zero
- \- *def* measure_theory.simple_func.itg
- \- *theorem* measure_theory.simple_func.itg_add
- \- *theorem* measure_theory.simple_func.itg_mono
- \- *theorem* measure_theory.simple_func.itg_zero
- \- *theorem* measure_theory.simple_func.le_antisymm
- \- *theorem* measure_theory.simple_func.le_antisymm_iff
- \- *theorem* measure_theory.simple_func.le_def
- \- *theorem* measure_theory.simple_func.le_iff_exists_add
- \- *theorem* measure_theory.simple_func.le_of_multiset_le
- \- *def* measure_theory.simple_func.lift₂
- \- *lemma* measure_theory.simple_func.lift₂_finite
- \- *lemma* measure_theory.simple_func.lift₂_is_measurable
- \- *theorem* measure_theory.simple_func.lift₂_val
- \+ *theorem* measure_theory.simple_func.lintegral_eq_integral
- \+ *def* measure_theory.simple_func.map
- \+ *theorem* measure_theory.simple_func.map_apply
- \+ *lemma* measure_theory.simple_func.map_integral
- \+ *theorem* measure_theory.simple_func.map_map
- \+/\- *theorem* measure_theory.simple_func.measurable
- \+ *theorem* measure_theory.simple_func.mem_range
- \+ *lemma* measure_theory.simple_func.mem_restrict_range
- \+ *lemma* measure_theory.simple_func.monotone_approx
- \+ *lemma* measure_theory.simple_func.monotone_eapprox
- \+ *lemma* measure_theory.simple_func.mul_apply
- \- *def* measure_theory.simple_func.of_fun
- \- *theorem* measure_theory.simple_func.of_fun_apply
- \- *theorem* measure_theory.simple_func.of_fun_val
- \+ *def* measure_theory.simple_func.pair
- \+ *lemma* measure_theory.simple_func.pair_apply
- \+/\- *theorem* measure_theory.simple_func.preimage_measurable
- \+ *lemma* measure_theory.simple_func.range_const
- \+ *theorem* measure_theory.simple_func.range_map
- \+ *def* measure_theory.simple_func.restrict
- \+ *theorem* measure_theory.simple_func.restrict_apply
- \+ *lemma* measure_theory.simple_func.restrict_const_integral
- \+ *lemma* measure_theory.simple_func.restrict_integral
- \+ *lemma* measure_theory.simple_func.restrict_preimage'
- \+ *theorem* measure_theory.simple_func.restrict_preimage
- \+ *def* measure_theory.simple_func.seq
- \- *theorem* measure_theory.simple_func.sub_add_cancel_of_le
- \- *theorem* measure_theory.simple_func.sub_val
- \+ *lemma* measure_theory.simple_func.sup_apply
- \+ *lemma* measure_theory.simple_func.sup_eq_map₂
- \+ *lemma* measure_theory.simple_func.supr_approx_apply
- \+ *lemma* measure_theory.simple_func.supr_eapprox_apply
- \- *def* measure_theory.simple_func.to_fun
- \+ *lemma* measure_theory.simple_func.zero_integral
- \- *def* measure_theory.simple_func
- \- *theorem* measure_theory.simple_itg_eq
- \- *def* measure_theory.upper_itg
- \- *theorem* measure_theory.upper_itg_add_le
- \- *def* measure_theory.upper_itg_def_subtype
- \- *theorem* measure_theory.upper_itg_simple
- \+/\- *structure* measure_theory.{u
- \+ *lemma* supr_eq_of_tendsto

Modified analysis/measure_theory/measurable_space.lean
- \+ *lemma* measurable_const

Modified analysis/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.volume_bUnion_finset

Modified data/finset.lean
- \+ *lemma* finset.image_bind_filter_eq
- \+ *lemma* finset.inf_eq_infi
- \+ *lemma* finset.sup_eq_supr

Modified data/real/ennreal.lean
- \+ *lemma* ennreal.coe_nat
- \+ *lemma* ennreal.coe_to_nnreal_le_self
- \+ *lemma* ennreal.le_of_forall_lt_one_mul_lt
- \+ *lemma* ennreal.mul_inv_cancel
- \+ *lemma* ennreal.mul_le_if_le_inv
- \+ *lemma* ennreal.supr_coe_nat

Modified data/real/nnreal.lean
- \+ *lemma* nnreal.le_of_forall_lt_one_mul_lt
- \+ *lemma* nnreal.lt_inv_iff_mul_lt
- \+ *lemma* nnreal.mul_le_if_le_inv

Modified data/set/basic.lean
- \+ *lemma* set.compl_set_of
- \+ *theorem* set.exists_range_iff

Modified order/complete_lattice.lean
- \+ *lemma* lattice.Inf_eq_bot
- \+/\- *lemma* lattice.infi_eq_bot
- \+ *lemma* lattice.supr_eq_bot
- \+ *lemma* lattice.supr_eq_top

Modified order/filter.lean
- \+ *lemma* filter.tendsto_at_top



## [2018-10-10 22:50:06+02:00](https://github.com/leanprover-community/mathlib/commit/a25e4a8)
feat(analysis/measure_theory/integration): lebesgue integration [WIP]
#### Estimated changes
Modified analysis/measure_theory/borel_space.lean
- \+ *lemma* measure_theory.borel_eq_generate_Iio
- \+ *lemma* measure_theory.borel_eq_generate_Ioi
- \+ *lemma* measure_theory.measurable.infi
- \+ *lemma* measure_theory.measurable.is_glb
- \+ *lemma* measure_theory.measurable.is_lub
- \+ *lemma* measure_theory.measurable.supr

Added analysis/measure_theory/integration.lean
- \+ *def* measure_theory.indicator.size
- \+ *def* measure_theory.indicator.to_fun
- \+ *theorem* measure_theory.indicator.to_fun_val
- \+ *structure* measure_theory.indicator
- \+ *def* measure_theory.simple_func'.bind
- \+ *theorem* measure_theory.simple_func'.bind_apply
- \+ *theorem* measure_theory.simple_func'.bind_const
- \+ *lemma* measure_theory.simple_func'.bind_itg
- \+ *lemma* measure_theory.simple_func'.bind_sum_measure
- \+ *theorem* measure_theory.simple_func'.coe_def
- \+ *theorem* measure_theory.simple_func'.coe_le_coe
- \+ *def* measure_theory.simple_func'.const
- \+ *theorem* measure_theory.simple_func'.const_apply
- \+ *theorem* measure_theory.simple_func'.ext
- \+ *lemma* measure_theory.simple_func'.is_measurable_cut
- \+ *def* measure_theory.simple_func'.ite
- \+ *theorem* measure_theory.simple_func'.ite_apply
- \+ *def* measure_theory.simple_func'.itg
- \+ *theorem* measure_theory.simple_func'.le_def
- \+ *def* measure_theory.simple_func'.map
- \+ *theorem* measure_theory.simple_func'.map_apply
- \+ *lemma* measure_theory.simple_func'.map_itg
- \+ *theorem* measure_theory.simple_func'.measurable
- \+ *theorem* measure_theory.simple_func'.mem_range
- \+ *def* measure_theory.simple_func'.pair
- \+ *theorem* measure_theory.simple_func'.preimage_measurable
- \+ *def* measure_theory.simple_func'.restrict
- \+ *theorem* measure_theory.simple_func'.restrict_apply
- \+ *theorem* measure_theory.simple_func'.restrict_preimage
- \+ *def* measure_theory.simple_func'.seq
- \+ *lemma* measure_theory.simple_func'.seq_itg
- \+ *theorem* measure_theory.simple_func.add_congr
- \+ *theorem* measure_theory.simple_func.add_sub_cancel_of_le
- \+ *theorem* measure_theory.simple_func.coe_add
- \+ *theorem* measure_theory.simple_func.coe_def
- \+ *theorem* measure_theory.simple_func.coe_le_coe
- \+ *theorem* measure_theory.simple_func.equiv_def
- \+ *theorem* measure_theory.simple_func.equiv_iff
- \+ *theorem* measure_theory.simple_func.finite_range
- \+ *def* measure_theory.simple_func.itg'
- \+ *theorem* measure_theory.simple_func.itg'_add
- \+ *theorem* measure_theory.simple_func.itg'_eq_sum
- \+ *theorem* measure_theory.simple_func.itg'_eq_sum_of_subset
- \+ *theorem* measure_theory.simple_func.itg'_indicator
- \+ *theorem* measure_theory.simple_func.itg'_mono
- \+ *theorem* measure_theory.simple_func.itg'_zero
- \+ *def* measure_theory.simple_func.itg
- \+ *theorem* measure_theory.simple_func.itg_add
- \+ *theorem* measure_theory.simple_func.itg_mono
- \+ *theorem* measure_theory.simple_func.itg_zero
- \+ *theorem* measure_theory.simple_func.le_antisymm
- \+ *theorem* measure_theory.simple_func.le_antisymm_iff
- \+ *theorem* measure_theory.simple_func.le_def
- \+ *theorem* measure_theory.simple_func.le_iff_exists_add
- \+ *theorem* measure_theory.simple_func.le_of_multiset_le
- \+ *def* measure_theory.simple_func.lift₂
- \+ *lemma* measure_theory.simple_func.lift₂_finite
- \+ *lemma* measure_theory.simple_func.lift₂_is_measurable
- \+ *theorem* measure_theory.simple_func.lift₂_val
- \+ *theorem* measure_theory.simple_func.measurable
- \+ *def* measure_theory.simple_func.of_fun
- \+ *theorem* measure_theory.simple_func.of_fun_apply
- \+ *theorem* measure_theory.simple_func.of_fun_val
- \+ *theorem* measure_theory.simple_func.preimage_measurable
- \+ *theorem* measure_theory.simple_func.sub_add_cancel_of_le
- \+ *theorem* measure_theory.simple_func.sub_val
- \+ *def* measure_theory.simple_func.to_fun
- \+ *def* measure_theory.simple_func
- \+ *theorem* measure_theory.simple_itg_eq
- \+ *def* measure_theory.upper_itg
- \+ *theorem* measure_theory.upper_itg_add_le
- \+ *def* measure_theory.upper_itg_def_subtype
- \+ *theorem* measure_theory.upper_itg_simple
- \+ *structure* measure_theory.{u

Modified analysis/measure_theory/lebesgue_measure.lean
- \- *def* measure_theory.lebesgue
- \- *lemma* measure_theory.lebesgue_Icc
- \- *lemma* measure_theory.lebesgue_Ico
- \- *lemma* measure_theory.lebesgue_Ioo
- \- *lemma* measure_theory.lebesgue_singleton
- \+/\- *theorem* measure_theory.lebesgue_to_outer_measure
- \- *theorem* measure_theory.lebesgue_val
- \+ *lemma* measure_theory.real.volume_Icc
- \+ *lemma* measure_theory.real.volume_Ico
- \+ *lemma* measure_theory.real.volume_Ioo
- \+ *lemma* measure_theory.real.volume_singleton
- \+ *theorem* measure_theory.real.volume_val

Modified analysis/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable.Inter_Prop
- \+ *lemma* is_measurable.Union_Prop
- \+ *lemma* is_measurable.const
- \+ *lemma* is_measurable.univ
- \- *lemma* is_measurable_univ

Modified analysis/measure_theory/measure_space.lean
- \+ *def* measure_theory.measure.a_e
- \+/\- *lemma* measure_theory.measure_sUnion
- \+ *def* measure_theory.volume
- \+ *lemma* measure_theory.volume_Union
- \+ *theorem* measure_theory.volume_Union_le
- \+ *lemma* measure_theory.volume_Union_null
- \+ *lemma* measure_theory.volume_bUnion
- \+ *lemma* measure_theory.volume_diff
- \+ *lemma* measure_theory.volume_empty
- \+ *lemma* measure_theory.volume_mono
- \+ *lemma* measure_theory.volume_mono_null
- \+ *lemma* measure_theory.volume_sUnion
- \+ *lemma* measure_theory.volume_union
- \+ *theorem* measure_theory.volume_union_le
- \+ *lemma* measure_theory.volume_union_null

Modified analysis/topology/topological_space.lean
- \+ *lemma* topological_space.is_open_Union_countable

Modified data/set/basic.lean
- \+ *theorem* set.image_subset_range
- \+ *theorem* set.preimage_image_preimage
- \+ *theorem* set.preimage_inter_range

Modified data/set/finite.lean
- \+/\- *theorem* set.finite_bUnion

Modified data/set/lattice.lean
- \+ *theorem* set.bUnion_of_singleton
- \+ *theorem* set.bUnion_subset_Union
- \+ *theorem* set.preimage_bUnion

Modified order/bounds.lean
- \+/\- *lemma* is_glb_Inf
- \+ *lemma* is_glb_lt_iff
- \+/\- *lemma* is_lub_Sup
- \+ *lemma* is_lub_le_iff
- \+ *lemma* le_is_glb_iff
- \+ *lemma* lower_bounds_mono
- \+ *lemma* lt_is_lub_iff
- \+ *lemma* upper_bounds_mono

Modified order/order_iso.lean
- \+ *theorem* preimage_equivalence

Modified tactic/interactive.lean




## [2018-10-10 12:53:24-04:00](https://github.com/leanprover-community/mathlib/commit/4dbe0cd)
doc(elan): further improvements to installation instructions ([#412](https://github.com/leanprover-community/mathlib/pull/412)) [ci-skip]
#### Estimated changes
Modified docs/elan.md




## [2018-10-10 04:04:54-04:00](https://github.com/leanprover-community/mathlib/commit/979e238)
fix(*): fix build continued
#### Estimated changes
Modified data/nat/prime.lean


Modified set_theory/lists.lean




## [2018-10-10 03:27:18-04:00](https://github.com/leanprover-community/mathlib/commit/1a4156d)
fix(data/nat): fix build
#### Estimated changes
Modified data/int/basic.lean
- \+/\- *lemma* int.coe_nat_nonneg

Modified data/list/basic.lean


Modified data/nat/choose.lean




## [2018-10-10 03:03:09-04:00](https://github.com/leanprover-community/mathlib/commit/fedee98)
feat(data/nat/basic): a few choiceless proofs
not sure I can take this much farther without modifying core...
#### Estimated changes
Modified algebra/archimedean.lean


Modified algebra/order.lean
- \+ *lemma* decidable.eq_or_lt_of_le
- \+ *lemma* decidable.le_iff_le_iff_lt_iff_lt
- \+ *lemma* decidable.le_iff_lt_or_eq
- \+ *lemma* decidable.le_imp_le_iff_lt_imp_lt
- \+ *lemma* decidable.le_imp_le_of_lt_imp_lt
- \+ *lemma* decidable.le_of_not_lt
- \+ *lemma* decidable.le_or_lt
- \+ *lemma* decidable.lt_or_eq_of_le
- \+ *lemma* decidable.lt_or_gt_of_ne
- \+ *lemma* decidable.lt_or_le
- \+ *lemma* decidable.lt_trichotomy
- \+ *lemma* decidable.ne_iff_lt_or_gt
- \+ *lemma* decidable.not_lt
- \+ *lemma* le_imp_le_of_lt_imp_lt
- \+ *lemma* lt_iff_lt_of_le_iff_le'
- \+ *lemma* lt_iff_lt_of_le_iff_le
- \+ *lemma* lt_iff_not_ge'
- \+ *lemma* lt_imp_lt_of_le_imp_le
- \+ *lemma* lt_of_le_of_ne'
- \+ *lemma* lt_of_not_ge'
- \+/\- *lemma* not_le

Modified algebra/ordered_field.lean


Modified algebra/ordered_ring.lean
- \+ *lemma* decidable.mul_le_mul_left
- \+ *lemma* decidable.mul_le_mul_right

Modified computability/partrec.lean


Modified data/nat/basic.lean
- \+ *theorem* nat.div_lt_iff_lt_mul'
- \+ *theorem* nat.div_mul_le_self'
- \+ *theorem* nat.le_div_iff_mul_le'

Modified data/nat/sqrt.lean


Modified data/rat.lean


Modified data/real/basic.lean


Modified set_theory/cardinal.lean


Modified set_theory/cofinality.lean


Modified set_theory/ordinal.lean




## [2018-10-10 03:01:34-04:00](https://github.com/leanprover-community/mathlib/commit/1daf4a8)
fix(data/set/lattice): fixing simp lemmas for set monad
#### Estimated changes
Modified data/set/lattice.lean
- \+/\- *lemma* set.fmap_eq_image
- \+/\- *lemma* set.mem_seq_iff
- \+/\- *lemma* set.pure_def
- \+/\- *lemma* set.seq_eq_set_seq



## [2018-10-09 22:59:15-04:00](https://github.com/leanprover-community/mathlib/commit/d867240)
feat(data/set/finite): finiteness of set monad ops
#### Estimated changes
Modified data/set/finite.lean
- \+ *theorem* set.finite_bUnion
- \+ *theorem* set.finite_bind
- \+ *theorem* set.finite_map
- \+ *theorem* set.finite_pure
- \+ *theorem* set.finite_seq
- \+ *def* set.fintype_bUnion
- \+ *def* set.fintype_bind
- \+ *def* set.fintype_seq



## [2018-10-09 01:14:15-04:00](https://github.com/leanprover-community/mathlib/commit/5c209ed)
fix(linear_algebra/dimension): fix build
#### Estimated changes
Modified algebra/big_operators.lean


Modified linear_algebra/dimension.lean




## [2018-10-08 15:17:51-04:00](https://github.com/leanprover-community/mathlib/commit/2c11641)
refactor(data/polynomial): consistently use coeff not apply ([#409](https://github.com/leanprover-community/mathlib/pull/409))
#### Estimated changes
Modified data/polynomial.lean
- \- *lemma* polynomial.C_apply
- \- *lemma* polynomial.C_apply_zero
- \- *lemma* polynomial.C_mul_apply
- \- *lemma* polynomial.X_apply_one
- \- *lemma* polynomial.X_pow_apply
- \- *lemma* polynomial.add_apply
- \+ *lemma* polynomial.apply_eq_coeff
- \- *lemma* polynomial.apply_nat_degree_eq_zero_of_degree_lt
- \+/\- *def* polynomial.coeff
- \+/\- *lemma* polynomial.coeff_C
- \+ *lemma* polynomial.coeff_C_mul
- \+ *lemma* polynomial.coeff_C_zero
- \- *lemma* polynomial.coeff_X
- \+ *lemma* polynomial.coeff_X_one
- \+/\- *lemma* polynomial.coeff_add
- \+ *lemma* polynomial.coeff_derivative
- \+ *lemma* polynomial.coeff_eq_zero_of_degree_lt
- \+/\- *lemma* polynomial.coeff_is_linear
- \+ *lemma* polynomial.coeff_mul_degree_add_degree
- \+ *lemma* polynomial.coeff_nat_degree_eq_zero_of_degree_lt
- \+ *lemma* polynomial.coeff_neg
- \+ *lemma* polynomial.coeff_one_zero
- \+ *lemma* polynomial.coeff_single
- \+ *lemma* polynomial.coeff_sum
- \+/\- *lemma* polynomial.degree_le_degree
- \- *lemma* polynomial.derivative_apply
- \+/\- *lemma* polynomial.eq_C_of_degree_le_zero
- \- *lemma* polynomial.eq_zero_of_degree_lt
- \+/\- *theorem* polynomial.ext
- \+/\- *lemma* polynomial.le_degree_of_ne_zero
- \+/\- *lemma* polynomial.le_nat_degree_of_ne_zero
- \+/\- *def* polynomial.leading_coeff
- \- *lemma* polynomial.mul_apply_degree_add_degree
- \- *lemma* polynomial.neg_apply
- \- *lemma* polynomial.one_apply_zero
- \+ *def* polynomial.polynomial.has_coe_to_fun
- \- *lemma* polynomial.zero_apply



## [2018-10-08 14:51:29-04:00](https://github.com/leanprover-community/mathlib/commit/a694628)
fix(tactic/rcases): declare ? token
#### Estimated changes
Modified tactic/rcases.lean




## [2018-10-08 14:30:13-04:00](https://github.com/leanprover-community/mathlib/commit/3aeb64c)
refactor(*): touching up proofs from 'faster' branch
#### Estimated changes
Modified algebra/big_operators.lean


Modified algebra/euclidean_domain.lean


Modified algebra/field.lean
- \- *lemma* inv_sub_inv_eq

Modified algebra/gcd_domain.lean
- \+/\- *lemma* dvd_lcm_left
- \+/\- *lemma* dvd_lcm_right
- \+/\- *lemma* lcm_dvd_iff

Modified algebra/group_power.lean
- \+/\- *theorem* neg_one_pow_eq_or

Modified algebra/ordered_group.lean
- \+ *lemma* add_eq_zero_iff'
- \- *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'

Modified analysis/topology/topological_space.lean


Modified data/finset.lean
- \+/\- *theorem* finset.card_insert_of_not_mem
- \+/\- *lemma* finset.coe_empty
- \+/\- *lemma* finset.coe_singleton
- \+/\- *theorem* finset.fold_singleton
- \+/\- *theorem* finset.max_singleton'
- \+/\- *theorem* finset.max_singleton
- \+/\- *theorem* finset.mem_singleton
- \+/\- *theorem* finset.min_empty
- \+/\- *theorem* finset.min_singleton
- \+/\- *theorem* list.to_finset_card_of_nodup

Modified data/finsupp.lean
- \+/\- *lemma* finsupp.mem_support_iff
- \+ *lemma* finsupp.not_mem_support_iff
- \+/\- *lemma* finsupp.single_apply
- \+/\- *lemma* finsupp.single_eq_of_ne
- \+/\- *lemma* finsupp.single_eq_same

Modified data/list/basic.lean
- \+/\- *theorem* list.count_singleton
- \+/\- *theorem* list.forall_mem_nil
- \+/\- *theorem* list.join_eq_nil
- \+/\- *theorem* list.not_exists_mem_nil
- \+/\- *theorem* list.take_zero
- \+/\- *theorem* option.to_list_nodup

Modified data/nat/basic.lean
- \+ *theorem* nat.succ_inj'

Modified data/polynomial.lean
- \+/\- *lemma* polynomial.nat_degree_zero

Modified data/set/lattice.lean
- \+ *theorem* set.sInter_pair
- \+ *theorem* set.sUnion_pair

Modified order/basic.lean


Modified order/conditionally_complete_lattice.lean
- \+/\- *lemma* bdd_above_finite
- \+/\- *lemma* bdd_above_subset
- \+/\- *lemma* bdd_below_subset

Modified order/filter.lean


Modified set_theory/ordinal.lean




## [2018-10-08 14:30:12-04:00](https://github.com/leanprover-community/mathlib/commit/f02a88b)
chore(*): replace rec_on with induction and match for readability
#### Estimated changes
Modified algebra/big_operators.lean


Modified algebra/group.lean


Modified algebra/group_power.lean


Modified data/finset.lean


Modified data/list/basic.lean


Modified set_theory/ordinal.lean




## [2018-10-08 14:30:12-04:00](https://github.com/leanprover-community/mathlib/commit/cc2e1ec)
refactor(*): making mathlib faster again
#### Estimated changes
Modified algebra/archimedean.lean


Modified algebra/big_operators.lean
- \+/\- *lemma* finset.sum_le_zero'
- \+/\- *lemma* finset.sum_le_zero
- \+/\- *lemma* finset.zero_le_sum'
- \+/\- *lemma* finset.zero_le_sum

Modified algebra/char_zero.lean


Modified algebra/euclidean_domain.lean


Modified algebra/field.lean


Modified algebra/field_power.lean


Modified algebra/gcd_domain.lean


Modified algebra/group.lean
- \+/\- *lemma* bit1_zero
- \+/\- *theorem* divp_one
- \+/\- *theorem* divp_self
- \+/\- *lemma* is_conj_refl

Modified algebra/group_power.lean
- \+/\- *theorem* add_monoid.smul_eq_mul'
- \+/\- *theorem* gpow_neg_one
- \+/\- *theorem* inv_pow
- \+/\- *theorem* list.prod_repeat
- \+/\- *theorem* mul_pow
- \+/\- *theorem* neg_one_gsmul
- \+/\- *theorem* neg_one_pow_eq_or
- \+/\- *theorem* one_div_pow
- \+/\- *theorem* pow_mul

Modified analysis/topology/topological_space.lean
- \+/\- *lemma* is_closed_empty
- \+/\- *lemma* is_closed_univ

Modified analysis/topology/uniform_space.lean


Modified computability/turing_machine.lean


Modified data/complex/basic.lean
- \+/\- *lemma* complex.conj_I
- \+/\- *lemma* complex.conj_neg
- \+/\- *lemma* complex.conj_of_real
- \+/\- *lemma* complex.conj_one
- \+/\- *lemma* complex.conj_zero
- \+/\- *lemma* complex.norm_sq_I
- \+/\- *lemma* complex.norm_sq_one
- \+/\- *lemma* complex.norm_sq_zero
- \+/\- *lemma* complex.of_real_neg

Modified data/finset.lean
- \+/\- *lemma* finset.coe_image
- \+/\- *lemma* finset.coe_inter
- \+/\- *lemma* finset.coe_union
- \+/\- *theorem* finset.empty_inter
- \+/\- *theorem* finset.empty_union
- \+/\- *theorem* finset.image_id
- \+/\- *theorem* finset.image_to_finset
- \+/\- *theorem* finset.insert_eq
- \+/\- *theorem* finset.inter_assoc
- \+/\- *theorem* finset.inter_comm
- \+/\- *theorem* finset.inter_distrib_left
- \+/\- *theorem* finset.inter_distrib_right
- \+/\- *theorem* finset.inter_empty
- \+/\- *theorem* finset.inter_left_comm
- \+/\- *theorem* finset.inter_right_comm
- \+/\- *theorem* finset.inter_self
- \+/\- *theorem* finset.map_refl
- \+/\- *theorem* finset.max_empty
- \+/\- *theorem* finset.mem_erase_of_ne_of_mem
- \+/\- *theorem* finset.mem_image
- \+/\- *theorem* finset.mem_insert_of_mem
- \+/\- *theorem* finset.mem_insert_self
- \+/\- *theorem* finset.mem_map
- \+/\- *theorem* finset.mem_singleton_self
- \+/\- *theorem* finset.mem_union_left
- \+/\- *theorem* finset.mem_union_right
- \+/\- *theorem* finset.ne_of_mem_erase
- \+/\- *theorem* finset.not_mem_erase
- \+/\- *theorem* finset.not_mem_singleton
- \+/\- *theorem* finset.range_succ
- \+/\- *theorem* finset.sigma_mono
- \+/\- *theorem* finset.singleton_inter_of_mem
- \+/\- *theorem* finset.singleton_inter_of_not_mem
- \+/\- *theorem* finset.union_comm
- \+/\- *theorem* finset.union_distrib_left
- \+/\- *theorem* finset.union_distrib_right
- \+/\- *theorem* finset.union_empty
- \+/\- *theorem* finset.union_idempotent
- \+/\- *theorem* finset.union_right_comm
- \+/\- *theorem* finset.union_self

Modified data/finsupp.lean


Modified data/list/basic.lean
- \+/\- *theorem* list.concat_cons
- \+/\- *theorem* list.index_of_eq_length
- \+/\- *theorem* list.nil_diff
- \+/\- *theorem* list.prefix_concat
- \+/\- *theorem* list.take_zero

Modified data/polynomial.lean
- \+/\- *lemma* polynomial.C_0

Modified order/conditionally_complete_lattice.lean


Modified order/filter.lean
- \+/\- *lemma* filter.singleton_mem_pure_sets

Modified order/lattice.lean


Modified set_theory/ordinal.lean
- \+/\- *theorem* cardinal.aleph_zero
- \+/\- *theorem* ordinal.lift_type_fin
- \+/\- *theorem* ordinal.one_lt_omega

Modified tactic/squeeze.lean




## [2018-10-08 04:07:24-04:00](https://github.com/leanprover-community/mathlib/commit/136ef25)
feat(ring_theory/determinants): det is a monoid_hom ([#406](https://github.com/leanprover-community/mathlib/pull/406))
#### Estimated changes
Modified ring_theory/determinant.lean




## [2018-10-08 03:07:28-04:00](https://github.com/leanprover-community/mathlib/commit/61d8776)
fix(ring_theory/determinant): remove #print ([#405](https://github.com/leanprover-community/mathlib/pull/405))
#### Estimated changes
Modified ring_theory/determinant.lean




## [2018-10-08 00:49:30-04:00](https://github.com/leanprover-community/mathlib/commit/13febee)
fix(group_theory/perm): fix to_additive use
#### Estimated changes
Modified group_theory/perm.lean
- \+ *lemma* finset.sum_univ_perm



## [2018-10-07 21:29:00-04:00](https://github.com/leanprover-community/mathlib/commit/73f51b8)
feat(ring_theory/determinant): determinants ([#404](https://github.com/leanprover-community/mathlib/pull/404))
* clean up determinant PR
* remove unnecessary type annotations
* update copyright
* add additive version of prod_attach_univ
#### Estimated changes
Modified data/equiv/basic.lean
- \+ *lemma* equiv.swap_apply_self
- \+ *lemma* equiv.swap_mul_self

Modified data/fintype.lean
- \+ *lemma* finset.prod_attach_univ

Modified group_theory/perm.lean
- \+ *lemma* finset.prod_univ_perm

Added ring_theory/determinant.lean
- \+ *lemma* matrix.det_diagonal
- \+ *lemma* matrix.det_mul
- \+ *lemma* matrix.det_mul_aux
- \+ *lemma* matrix.det_one
- \+ *lemma* matrix.det_zero



## [2018-10-07 21:27:20-04:00](https://github.com/leanprover-community/mathlib/commit/04d8c15)
feat(solve_by_elim): improve backtracking behaviour when there are multiple subgoals ([#393](https://github.com/leanprover-community/mathlib/pull/393))
#### Estimated changes
Modified data/real/cau_seq_filter.lean


Modified tactic/basic.lean


Modified tests/solve_by_elim.lean




## [2018-10-07 09:22:24-04:00](https://github.com/leanprover-community/mathlib/commit/8c68fd1)
feat(tactic/auto_cases): split `iff`s into two implications ([#344](https://github.com/leanprover-community/mathlib/pull/344))
* feat(tactic/auto_cases): split `iff`s into two implications
* add Johan's test case
#### Estimated changes
Modified tactic/auto_cases.lean


Modified tests/tidy.lean
- \+ *def* tidy.test.g



## [2018-10-07 09:17:40-04:00](https://github.com/leanprover-community/mathlib/commit/49fea31)
feat(tactics/solve_by_elim): add or remove lemmas from the set to apply, with `simp`-like parsing ([#382](https://github.com/leanprover-community/mathlib/pull/382))
* feat(tactic/solve_by_elim): modify set of lemmas to apply using `simp`-like syntax
* update to syntax: use `with attr` to request all lemmas tagged with an attribute
* use non-interactive solve_by_elim in tfae
* fix parser
#### Estimated changes
Modified category_theory/examples/rings.lean


Modified docs/tactics.md


Modified tactic/basic.lean


Modified tactic/interactive.lean


Modified tactic/tfae.lean


Modified tactic/wlog.lean


Added tests/solve_by_elim.lean
- \+ *def* f

Modified tests/tactics.lean




## [2018-10-07 09:12:40-04:00](https://github.com/leanprover-community/mathlib/commit/3b09151)
feat(tactic/squeeze): squeeze_simp tactic ([#396](https://github.com/leanprover-community/mathlib/pull/396))
* feat(tactic/squeeze): just the squeeze_simp tactic
* docs(tactic/squeeze): add header comments and documentation
* Provide a means for other tactics to use squeeze
#### Estimated changes
Modified docs/tactics.md


Modified tactic/basic.lean


Added tactic/squeeze.lean




## [2018-10-07 09:09:49-04:00](https://github.com/leanprover-community/mathlib/commit/c1f13c0)
fix(data/int.basic): rename sub_one_le_iff ([#394](https://github.com/leanprover-community/mathlib/pull/394))
#### Estimated changes
Modified data/int/basic.lean
- \+/\- *lemma* int.dvd_of_pow_dvd
- \- *theorem* int.sub_one_le_iff
- \+ *theorem* int.sub_one_lt_iff



## [2018-10-07 09:09:28-04:00](https://github.com/leanprover-community/mathlib/commit/d1e34fd)
fix(algebra/big_operators): remove `comm_monoid` assumption from `sum_nat_cast` ([#401](https://github.com/leanprover-community/mathlib/pull/401))
#### Estimated changes
Modified algebra/big_operators.lean




## [2018-10-07 09:08:52-04:00](https://github.com/leanprover-community/mathlib/commit/276c472)
fix(algebra/ring): delete duplicate lemma zero_dvd_iff_eq_zero ([#399](https://github.com/leanprover-community/mathlib/pull/399))
#### Estimated changes
Modified algebra/ring.lean
- \- *lemma* zero_dvd_iff_eq_zero



## [2018-10-07 07:16:14-04:00](https://github.com/leanprover-community/mathlib/commit/e4ce469)
fix(docs/elan): fix homebrew instructions for macOS ([#395](https://github.com/leanprover-community/mathlib/pull/395))
#### Estimated changes
Modified docs/elan.md




## [2018-10-07 07:15:56-04:00](https://github.com/leanprover-community/mathlib/commit/64431ae)
doc(hole/instance_stub) ([#400](https://github.com/leanprover-community/mathlib/pull/400))
#### Estimated changes
Modified README.md


Added docs/holes.md




## [2018-10-07 06:35:55-04:00](https://github.com/leanprover-community/mathlib/commit/46a37a7)
feat(hole/instance_stub): tool support for providing snippets ([#397](https://github.com/leanprover-community/mathlib/pull/397))
#### Estimated changes
Modified tactic/basic.lean




## [2018-10-07 02:28:18-04:00](https://github.com/leanprover-community/mathlib/commit/0ddb58c)
workaround(tactic/tfae): tfae is broken, comment out its tests ([#398](https://github.com/leanprover-community/mathlib/pull/398))
#### Estimated changes
Modified tests/tactics.lean




## [2018-10-06 22:41:00-04:00](https://github.com/leanprover-community/mathlib/commit/2bf7b4b)
refactor(tactic/tfae): minor tfae modifications
#### Estimated changes
Modified data/list/basic.lean


Modified tactic/tfae.lean




## [2018-10-06 22:33:52-04:00](https://github.com/leanprover-community/mathlib/commit/568e405)
feat(data/finset): embedding properties of finset.map
#### Estimated changes
Modified data/finset.lean
- \+ *def* finset.map_embedding
- \+ *theorem* finset.map_embedding_apply
- \+ *theorem* finset.map_inj
- \+/\- *theorem* finset.map_subset_map
- \+ *theorem* finset.mem_map'
- \+/\- *theorem* finset.mem_map_of_mem
- \+ *theorem* finset.subset.antisymm_iff



## [2018-10-05 02:18:56-04:00](https://github.com/leanprover-community/mathlib/commit/74f52f1)
Expand and contract fin ([#387](https://github.com/leanprover-community/mathlib/pull/387))
#### Estimated changes
Modified data/fin.lean
- \+ *def* fin.nat_add
- \+ *def* lower_left
- \+ *def* lower_right
- \+ *def* raise_nat



## [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/9ec21e4)
perf(tactic/scc): produce smaller proofs
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* list.tfae_of_forall

Modified tactic/scc.lean


Modified tactic/tfae.lean




## [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/025b73a)
chore(tactic/scc): small cleanup
#### Estimated changes
Modified tactic/scc.lean




## [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/ff12b35)
docs(tactic/tfae): move doc string
#### Estimated changes
Modified data/list/basic.lean




## [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/d935519)
docs(tactic/tfae): fix oversights
#### Estimated changes
Modified docs/tactics.md


Modified tactic/scc.lean


Modified tests/tactics.lean




## [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/b7d314f)
feat(tactic/tfae): tactic for decomposing a proof into a set of
equivalent propositions which can be proved equivalent by cyclical
implications
#### Estimated changes
Modified category/basic.lean
- \+ *def* list.mmap_accuml
- \+ *def* list.mmap_accumr

Modified data/list/basic.lean
- \+ *def* list.last'
- \+ *theorem* list.last'_mem
- \+ *theorem* list.tfae.out
- \+ *def* list.tfae
- \+ *theorem* list.tfae_cons_cons
- \+ *theorem* list.tfae_cons_of_mem
- \+ *theorem* list.tfae_nil
- \+ *theorem* list.tfae_of_cycle
- \+ *theorem* list.tfae_singleton

Modified docs/tactics.md


Added tactic/scc.lean


Added tactic/tfae.lean
- \+ *inductive* tactic.tfae.arrow

Modified tests/tactics.lean




## [2018-10-03 12:54:45+02:00](https://github.com/leanprover-community/mathlib/commit/a243126)
chore(*): replace more axiom_of_choice, classical.some and classical.choice using the choose tactic
#### Estimated changes
Modified analysis/real.lean


Modified analysis/topology/uniform_space.lean


Modified data/multiset.lean


Modified data/set/finite.lean


Modified tests/examples.lean




## [2018-10-03 11:24:50+02:00](https://github.com/leanprover-community/mathlib/commit/c1f9f2e)
refactor(tactics/interactive, *): rename choice to choose and change syntax; use chooose instead of cases of axiom_of_choice
#### Estimated changes
Modified analysis/measure_theory/lebesgue_measure.lean


Modified analysis/measure_theory/measure_space.lean


Modified analysis/measure_theory/outer_measure.lean


Modified analysis/topology/continuity.lean


Modified analysis/topology/topological_space.lean


Modified data/real/basic.lean


Modified docs/tactics.md


Modified ring_theory/noetherian.lean


Modified set_theory/cardinal.lean


Modified tactic/basic.lean


Modified tactic/interactive.lean


Modified tests/examples.lean




## [2018-10-03 09:30:54+02:00](https://github.com/leanprover-community/mathlib/commit/0cfbf5a)
feat(tactic/linarith): handle negations of linear hypotheses
#### Estimated changes
Modified tactic/linarith.lean


Modified tests/linarith.lean




## [2018-10-02 22:17:27+02:00](https://github.com/leanprover-community/mathlib/commit/fff12f5)
chore(analysis/topology): remove duplicate theorems interior_compl_eq and closure_compl_eq (as discovered by @kckennylau)
#### Estimated changes
Modified analysis/topology/topological_space.lean
- \+/\- *lemma* closure_compl
- \- *lemma* closure_compl_eq
- \+/\- *lemma* interior_compl
- \- *lemma* interior_compl_eq



## [2018-10-02 22:13:59+02:00](https://github.com/leanprover-community/mathlib/commit/c2df6b1)
feat(tactics/interactive): add choice (closes [#38](https://github.com/leanprover-community/mathlib/pull/38))
#### Estimated changes
Modified docs/tactics.md


Modified tactic/basic.lean


Modified tactic/interactive.lean


Modified tests/examples.lean




## [2018-10-02 15:12:09+02:00](https://github.com/leanprover-community/mathlib/commit/b84e2db)
feat(docs/theories): document padics development (close [#337](https://github.com/leanprover-community/mathlib/pull/337))
(it hurts to write "maths in lean")
#### Estimated changes
Added docs/theories/padics.md




## [2018-10-02 14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/1562cc2)
feat(data/padics): use prime typeclass
#### Estimated changes
Added analysis/polynomial.lean
- \+ *lemma* polynomial.continuous_eval

Modified data/padics/hensel.lean
- \+/\- *lemma* hensels_lemma
- \+/\- *lemma* limit_zero_of_norm_tendsto_zero
- \+/\- *lemma* padic_polynomial_dist

Modified data/padics/padic_integers.lean
- \+/\- *def* padic_int.add
- \+/\- *lemma* padic_int.add_def
- \+/\- *lemma* padic_int.cast_pow
- \- *def* padic_int.cau_seq_lim
- \- *lemma* padic_int.cau_seq_lim_spec
- \+/\- *lemma* padic_int.coe_add
- \+/\- *lemma* padic_int.coe_coe
- \+/\- *lemma* padic_int.coe_mul
- \+/\- *lemma* padic_int.coe_neg
- \+/\- *lemma* padic_int.coe_one
- \+/\- *lemma* padic_int.coe_sub
- \+/\- *lemma* padic_int.coe_zero
- \+/\- *def* padic_int.inv
- \+/\- *lemma* padic_int.inv_mul
- \+/\- *def* padic_int.maximal_ideal
- \+/\- *lemma* padic_int.maximal_ideal_add
- \+/\- *lemma* padic_int.maximal_ideal_eq_nonunits
- \+/\- *lemma* padic_int.maximal_ideal_eq_or_univ_of_subset
- \+/\- *lemma* padic_int.maximal_ideal_mul
- \+/\- *lemma* padic_int.maximal_ideal_ne_univ
- \+/\- *lemma* padic_int.maximal_ideal_unique
- \+/\- *lemma* padic_int.mk_coe
- \+/\- *lemma* padic_int.mk_zero
- \+/\- *def* padic_int.mul
- \+/\- *lemma* padic_int.mul_def
- \+/\- *lemma* padic_int.mul_inv
- \+/\- *def* padic_int.neg
- \- *lemma* padic_int.tendsto_limit
- \+/\- *lemma* padic_int.val_eq_coe
- \+/\- *lemma* padic_int.zero_def
- \+/\- *def* padic_int
- \+/\- *theorem* padic_norm_z.add_eq_max_of_ne
- \+/\- *lemma* padic_norm_z.eq_of_norm_add_lt_left
- \+/\- *lemma* padic_norm_z.eq_of_norm_add_lt_right
- \+/\- *lemma* padic_norm_z.le_one
- \+/\- *lemma* padic_norm_z.mul
- \+/\- *theorem* padic_norm_z.nonarchimedean
- \+/\- *lemma* padic_norm_z.norm_one
- \+/\- *lemma* padic_norm_z.one
- \+/\- *lemma* padic_norm_z.padic_norm_e_of_padic_int
- \+/\- *lemma* padic_norm_z.padic_norm_z_eq_padic_norm_e
- \+/\- *lemma* padic_norm_z.pow
- \+/\- *def* padic_norm_z

Modified data/padics/padic_norm.lean
- \+/\- *lemma* padic_norm.add_eq_max_of_ne
- \+/\- *lemma* padic_norm.le_of_dvd
- \+/\- *theorem* padic_norm.triangle_ineq
- \+/\- *lemma* padic_norm.zero_of_padic_norm_eq_zero
- \+/\- *def* padic_norm

Modified data/padics/padic_numbers.lean
- \+/\- *lemma* padic.cast_eq_of_rat
- \+/\- *lemma* padic.cast_eq_of_rat_of_int
- \+/\- *lemma* padic.cast_eq_of_rat_of_nat
- \- *def* padic.cau_seq_lim
- \- *lemma* padic.cau_seq_lim_spec
- \+/\- *theorem* padic.complete'
- \+/\- *lemma* padic.const_equiv
- \+/\- *lemma* padic.exi_rat_seq_conv_cauchy
- \+/\- *def* padic.mk
- \+/\- *lemma* padic.mk_eq
- \+/\- *def* padic.of_rat
- \+/\- *lemma* padic.of_rat_add
- \+/\- *lemma* padic.of_rat_div
- \+/\- *lemma* padic.of_rat_eq
- \+/\- *lemma* padic.of_rat_mul
- \+/\- *lemma* padic.of_rat_neg
- \+/\- *lemma* padic.of_rat_one
- \+/\- *lemma* padic.of_rat_sub
- \+/\- *lemma* padic.of_rat_zero
- \+/\- *lemma* padic.padic_norm_e_lim_le
- \+/\- *theorem* padic.rat_dense'
- \+/\- *theorem* padic.rat_dense
- \- *lemma* padic.tendsto_limit
- \+/\- *def* padic
- \+/\- *theorem* padic_norm_e.add_eq_max_of_ne'
- \+/\- *theorem* padic_norm_e.add_eq_max_of_ne
- \+/\- *lemma* padic_norm_e.defn
- \+/\- *lemma* padic_norm_e.eq_of_norm_add_lt_left
- \+/\- *lemma* padic_norm_e.eq_of_norm_add_lt_right
- \+/\- *lemma* padic_norm_e.eq_padic_norm'
- \+/\- *lemma* padic_norm_e.eq_padic_norm
- \+/\- *lemma* padic_norm_e.eq_rat_norm
- \+/\- *theorem* padic_norm_e.nonarchimedean'
- \+/\- *theorem* padic_norm_e.nonarchimedean
- \+/\- *theorem* padic_norm_e.norm_rat_le_one
- \+/\- *def* padic_norm_e.rat_norm
- \+/\- *lemma* padic_norm_e.sub_rev
- \+/\- *lemma* padic_norm_e.triangle_ineq
- \+/\- *lemma* padic_norm_e.zero_def
- \+/\- *lemma* padic_norm_e.zero_iff
- \+/\- *def* padic_norm_e
- \+/\- *lemma* padic_seq.add_eq_max_of_ne
- \+/\- *lemma* padic_seq.eq_zero_iff_equiv_zero
- \+/\- *lemma* padic_seq.equiv_zero_of_val_eq_of_equiv_zero
- \+/\- *lemma* padic_seq.lift_index_left
- \+/\- *lemma* padic_seq.lift_index_left_left
- \+/\- *lemma* padic_seq.lift_index_right
- \+/\- *lemma* padic_seq.ne_zero_iff_nequiv_zero
- \+/\- *def* padic_seq.norm
- \+/\- *lemma* padic_seq.norm_const
- \+/\- *lemma* padic_seq.norm_eq
- \+/\- *lemma* padic_seq.norm_eq_norm_app_of_nonzero
- \+/\- *lemma* padic_seq.norm_eq_of_add_equiv_zero
- \+/\- *theorem* padic_seq.norm_equiv
- \+/\- *lemma* padic_seq.norm_image
- \+/\- *lemma* padic_seq.norm_mul
- \+/\- *lemma* padic_seq.norm_neg
- \+/\- *theorem* padic_seq.norm_nonarchimedean
- \+/\- *lemma* padic_seq.norm_nonneg
- \+/\- *lemma* padic_seq.norm_nonzero_of_not_equiv_zero
- \+/\- *lemma* padic_seq.norm_one
- \+/\- *lemma* padic_seq.norm_zero_iff
- \+/\- *lemma* padic_seq.not_equiv_zero_const_of_nonzero
- \+/\- *lemma* padic_seq.not_lim_zero_const_of_nonzero
- \+/\- *lemma* padic_seq.stationary
- \+/\- *def* padic_seq.stationary_point
- \+/\- *lemma* padic_seq.stationary_point_spec
- \+/\- *def* padic_seq

Modified data/polynomial.lean
- \- *lemma* polynomial.continuous_eval

Modified data/real/basic.lean
- \+/\- *lemma* real.lim_add
- \+/\- *lemma* real.lim_const
- \+/\- *lemma* real.lim_eq_lim_of_equiv
- \+/\- *lemma* real.lim_mul_lim

Modified data/real/cau_seq.lean
- \+ *theorem* cau_seq.lim_zero_sub_rev

Modified data/real/cau_seq_completion.lean
- \+ *lemma* cau_seq.complete
- \+ *lemma* cau_seq.lim_spec

Modified data/real/cau_seq_filter.lean
- \+/\- *lemma* cau_filter_lim_spec
- \- *lemma* cau_seq_lim_spec
- \- *theorem* complete_space_of_cauchy_complete
- \+ *lemma* le_nhds_cau_filter_lim
- \- *lemma* le_nhds_cau_seq_lim
- \+/\- *lemma* set_seq_of_cau_filter_monotone
- \+ *lemma* tendsto_limit



## [2018-10-02 14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/e6a1bc3)
feat(data/real/cau_seq): relate cauchy sequence completeness and filter completeness
#### Estimated changes
Modified algebra/archimedean.lean
- \+ *theorem* exists_nat_one_div_lt

Modified algebra/field_power.lean


Modified analysis/limits.lean
- \+ *lemma* tendsto_inverse_at_top_nhds_0_nat
- \+ *lemma* tendsto_one_div_at_top_nhds_0_nat

Modified data/padics/padic_integers.lean
- \+/\- *def* padic_int.cau_seq_lim
- \- *theorem* padic_int.complete

Modified data/padics/padic_numbers.lean
- \+/\- *def* padic.cau_seq_lim
- \+/\- *lemma* padic.cau_seq_lim_spec
- \+/\- *lemma* padic.padic_norm_e_lim_le

Modified data/real/cau_seq_completion.lean
- \+/\- *def* cau_seq.completion.Cauchy
- \+/\- *lemma* cau_seq.completion.cau_seq_zero_ne_one

Modified data/real/cau_seq_filter.lean
- \+ *lemma* cau_filter_lim_spec
- \+ *lemma* cau_seq_lim_spec
- \+ *lemma* cau_seq_of_cau_filter_mem_set_seq
- \+ *theorem* complete_space_of_cauchy_complete
- \+ *lemma* is_cau_seq_of_dist_tendsto_0
- \+ *lemma* le_nhds_cau_seq_lim
- \+ *lemma* mono_of_mono_succ
- \+ *lemma* seq_of_cau_filter_is_cauchy'
- \+ *lemma* seq_of_cau_filter_is_cauchy
- \+ *lemma* seq_of_cau_filter_mem_set_seq
- \+ *def* set_seq_of_cau_filter
- \+ *lemma* set_seq_of_cau_filter_inhabited
- \+ *lemma* set_seq_of_cau_filter_mem_sets
- \+ *lemma* set_seq_of_cau_filter_monotone'
- \+ *lemma* set_seq_of_cau_filter_monotone
- \+ *lemma* set_seq_of_cau_filter_spec
- \+ *lemma* tendsto_div



## [2018-10-02 14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/e0b0c53)
feat(data/padics): prove Hensel's lemma
#### Estimated changes
Modified algebra/field_power.lean
- \+ *lemma* fpow_ge_one_of_nonneg
- \+ *lemma* fpow_le_one_of_nonpos
- \+ *lemma* fpow_neg
- \+ *lemma* fpow_pos_of_pos
- \+ *lemma* fpow_sub
- \+ *lemma* one_lt_fpow
- \+ *lemma* one_lt_pow

Modified algebra/group_power.lean
- \+ *lemma* div_sq_cancel
- \+ *lemma* neg_square
- \+ *lemma* pow_le_pow_of_le_left
- \+ *lemma* pow_le_pow_of_le_one
- \+ *lemma* pow_lt_pow_of_lt_one

Modified algebra/ordered_ring.lean
- \+ *lemma* mul_le_iff_le_one_left
- \+ *lemma* mul_le_iff_le_one_right
- \+ *lemma* mul_lt_iff_lt_one_left
- \+ *lemma* mul_lt_iff_lt_one_right

Modified analysis/limits.lean
- \+ *lemma* tendsto_coe_iff
- \+ *lemma* tendsto_pow_at_top_at_top_of_gt_1_nat

Modified analysis/normed_space.lean
- \+/\- *lemma* norm_div
- \+/\- *lemma* norm_inv
- \+/\- *lemma* norm_one
- \+ *lemma* norm_pow
- \+ *lemma* normed_field.norm_pow

Modified analysis/topology/topological_structures.lean
- \+ *lemma* continuous_pow

Modified data/finsupp.lean
- \+ *lemma* finsupp.sum_sub

Modified data/int/modeq.lean
- \+ *lemma* int.modeq.exists_unique_equiv
- \+ *lemma* int.modeq.exists_unique_equiv_nat
- \+ *lemma* int.modeq.mod_coprime
- \+ *theorem* int.modeq.modeq_add_fac

Modified data/nat/basic.lean
- \+/\- *lemma* nat.dvd_of_pow_dvd
- \+ *lemma* nat.exists_eq_add_of_le
- \+ *lemma* nat.exists_eq_add_of_lt

Added data/padics/default.lean


Added data/padics/hensel.lean
- \+ *lemma* hensels_lemma
- \+ *lemma* limit_zero_of_norm_tendsto_zero
- \+ *lemma* padic_polynomial_dist

Modified data/padics/padic_integers.lean
- \+/\- *lemma* padic_int.add_def
- \+ *lemma* padic_int.cast_pow
- \+ *def* padic_int.cau_seq_lim
- \+ *lemma* padic_int.cau_seq_lim_spec
- \+/\- *lemma* padic_int.coe_add
- \+/\- *lemma* padic_int.coe_mul
- \+/\- *lemma* padic_int.coe_one
- \+/\- *lemma* padic_int.coe_sub
- \+ *lemma* padic_int.coe_zero
- \+ *theorem* padic_int.complete
- \+/\- *lemma* padic_int.inv_mul
- \+/\- *lemma* padic_int.maximal_ideal_add
- \+/\- *lemma* padic_int.maximal_ideal_mul
- \+/\- *lemma* padic_int.maximal_ideal_ne_univ
- \+/\- *lemma* padic_int.mul_def
- \+/\- *lemma* padic_int.mul_inv
- \+ *lemma* padic_int.tendsto_limit
- \+/\- *lemma* padic_int.zero_def
- \+ *theorem* padic_norm_z.add_eq_max_of_ne
- \+ *lemma* padic_norm_z.eq_of_norm_add_lt_left
- \+ *lemma* padic_norm_z.eq_of_norm_add_lt_right
- \+/\- *lemma* padic_norm_z.le_one
- \+/\- *lemma* padic_norm_z.norm_one
- \+ *lemma* padic_norm_z.one
- \+ *lemma* padic_norm_z.padic_norm_e_of_padic_int
- \+ *lemma* padic_norm_z.padic_norm_z_eq_padic_norm_e
- \+ *lemma* padic_norm_z.padic_val_of_cong_pow_p
- \+ *lemma* padic_norm_z.pow

Modified data/padics/padic_norm.lean
- \+ *lemma* padic_norm.le_of_dvd
- \+/\- *lemma* padic_val.padic_val_eq_zero_of_coprime
- \+ *lemma* padic_val.pow_dvd_iff_le_padic_val
- \+ *lemma* padic_val.pow_dvd_of_le_padic_val
- \+ *lemma* padic_val_rat.padic_val_rat_of_int

Renamed data/padics/padic_rationals.lean to data/padics/padic_numbers.lean
- \+ *def* padic.cau_seq_lim
- \+ *lemma* padic.cau_seq_lim_spec
- \+/\- *theorem* padic.complete'
- \+ *lemma* padic.padic_norm_e_lim_le
- \+ *lemma* padic.tendsto_limit
- \+ *theorem* padic_norm_e.add_eq_max_of_ne'
- \+ *theorem* padic_norm_e.add_eq_max_of_ne
- \+/\- *lemma* padic_norm_e.defn
- \+ *lemma* padic_norm_e.eq_of_norm_add_lt_left
- \+ *lemma* padic_norm_e.eq_of_norm_add_lt_right
- \+ *theorem* padic_norm_e.norm_rat_le_one
- \+ *lemma* padic_seq.add_eq_max_of_ne
- \+ *lemma* padic_seq.lift_index_left
- \+ *lemma* padic_seq.lift_index_left_left
- \+ *lemma* padic_seq.lift_index_right
- \+ *lemma* padic_seq.norm_eq_of_add_equiv_zero
- \+/\- *theorem* padic_seq.norm_nonarchimedean

Modified data/polynomial.lean
- \+ *def* polynomial.binom_expansion
- \+ *lemma* polynomial.continuous_eval
- \+ *lemma* polynomial.derivative_eval
- \+ *def* polynomial.eval_sub_factor
- \+ *lemma* polynomial.eval_sum
- \+ *def* polynomial.pow_add_expansion
- \+ *def* polynomial.pow_sub_pow_factor

Modified data/rat.lean
- \+ *lemma* rat.div_num_denom
- \+ *lemma* rat.zero_iff_num_zero

Modified data/real/cau_seq.lean


Added data/real/cau_seq_filter.lean
- \+ *lemma* cauchy_of_filter_cauchy
- \+ *lemma* filter_cauchy_of_cauchy



## [2018-10-02 14:02:23+02:00](https://github.com/leanprover-community/mathlib/commit/f040aef)
feat(data/padics): use has_norm typeclasses for padics
#### Estimated changes
Modified algebra/archimedean.lean
- \+/\- *lemma* ceil_nonneg
- \+ *theorem* ceil_zero

Modified algebra/field_power.lean


Modified analysis/normed_space.lean
- \+ *lemma* norm_div
- \+ *lemma* norm_inv
- \+ *lemma* norm_one
- \+ *lemma* norm_sub_rev

Modified data/int/basic.lean
- \+ *lemma* int.dvd_of_pow_dvd
- \- *lemma* int.pow_div_of_le_of_pow_div_int
- \+ *lemma* int.pow_dvd_of_le_of_pow_dvd

Modified data/nat/basic.lean
- \+ *lemma* nat.div_mul_div
- \+ *lemma* nat.dvd_of_pow_dvd
- \- *lemma* nat.nat.div_mul_div
- \- *lemma* nat.pow_div_of_le_of_pow_div
- \+ *lemma* nat.pow_dvd_of_le_of_pow_dvd

Modified data/padics/padic_integers.lean
- \+ *lemma* padic_int.add_def
- \+ *lemma* padic_int.coe_add
- \+ *lemma* padic_int.coe_coe
- \+ *lemma* padic_int.coe_mul
- \+ *lemma* padic_int.coe_neg
- \+ *lemma* padic_int.coe_one
- \+ *lemma* padic_int.coe_sub
- \+ *def* padic_int.inv
- \+ *lemma* padic_int.inv_mul
- \+ *def* padic_int.maximal_ideal
- \+ *lemma* padic_int.maximal_ideal_add
- \+ *lemma* padic_int.maximal_ideal_eq_nonunits
- \+ *lemma* padic_int.maximal_ideal_eq_or_univ_of_subset
- \+ *lemma* padic_int.maximal_ideal_mul
- \+ *lemma* padic_int.maximal_ideal_ne_univ
- \+ *lemma* padic_int.maximal_ideal_unique
- \+ *lemma* padic_int.mk_coe
- \+ *lemma* padic_int.mk_zero
- \+ *lemma* padic_int.mul_def
- \+ *lemma* padic_int.mul_inv
- \+ *lemma* padic_int.val_eq_coe
- \+ *lemma* padic_int.zero_def
- \+/\- *def* padic_int
- \+ *lemma* padic_norm_z.le_one
- \+ *lemma* padic_norm_z.mul
- \+ *theorem* padic_norm_z.nonarchimedean
- \+ *lemma* padic_norm_z.norm_one
- \+ *def* padic_norm_z

Modified data/padics/padic_norm.lean
- \+ *lemma* padic_val.dvd_of_padic_val_pos
- \- *lemma* padic_val.le_padic_val_of_pow_div
- \+ *lemma* padic_val.le_padic_val_of_pow_dvd
- \+ *lemma* padic_val.padic_val_eq_zero_of_coprime
- \+ *lemma* padic_val.padic_val_eq_zero_of_not_dvd'
- \+ *lemma* padic_val.padic_val_eq_zero_of_not_dvd

Modified data/padics/padic_rationals.lean
- \+ *theorem* padic.complete'
- \- *theorem* padic.complete
- \+/\- *def* padic.lim_seq
- \+ *theorem* padic.rat_dense'
- \+/\- *theorem* padic.rat_dense
- \+/\- *def* padic
- \+ *lemma* padic_norm_e.eq_padic_norm'
- \+/\- *lemma* padic_norm_e.eq_padic_norm
- \+ *lemma* padic_norm_e.eq_rat_norm
- \+ *theorem* padic_norm_e.nonarchimedean'
- \+/\- *theorem* padic_norm_e.nonarchimedean
- \+ *def* padic_norm_e.rat_norm
- \+ *lemma* padic_norm_e.triangle_ineq
- \+/\- *theorem* padic_seq.norm_equiv
- \+/\- *lemma* padic_seq.norm_mul



## [2018-10-02 13:38:45+02:00](https://github.com/leanprover-community/mathlib/commit/963fc83)
doc(docs/elan.md): instructions for building all of a dependency
Closes [#308](https://github.com/leanprover-community/mathlib/pull/308).
#### Estimated changes
Modified docs/elan.md




## [2018-10-02 13:38:05+02:00](https://github.com/leanprover-community/mathlib/commit/9339754)
docs(elan): updating documentation on installing via elan ([#371](https://github.com/leanprover-community/mathlib/pull/371))
* updating documentation for elan
* minor
* further update of elan docs
* update instructions for elan 0.7.1
* noting additional prerequisite on macOS
#### Estimated changes
Modified docs/elan.md




## [2018-10-02 13:36:09+02:00](https://github.com/leanprover-community/mathlib/commit/28443c8)
feat(ring_theory/noetherian): zero ring (and finite rings) are Noetherian (closes [#341](https://github.com/leanprover-community/mathlib/pull/341))
#### Estimated changes
Modified algebra/ring.lean
- \+ *lemma* eq_zero_of_zero_eq_one
- \+ *theorem* subsingleton_of_zero_eq_one

Modified data/polynomial.lean
- \+ *lemma* polynomial.leading_coeff_eq_zero_iff_deg_eq_bot

Modified ring_theory/noetherian.lean
- \+ *theorem* ring.is_noetherian_of_fintype
- \+ *theorem* ring.is_noetherian_of_zero_eq_one



## [2018-10-02 11:34:24+02:00](https://github.com/leanprover-community/mathlib/commit/44b55e6)
feat(category_theory/groupoid): groupoids
#### Estimated changes
Added category_theory/groupoid.lean
- \+ *abbreviation* category_theory.large_groupoid
- \+ *abbreviation* category_theory.small_groupoid



## [2018-10-02 11:34:04+02:00](https://github.com/leanprover-community/mathlib/commit/efa9459)
feat(category_theory/whiskering): whiskering nat_trans by functors ([#360](https://github.com/leanprover-community/mathlib/pull/360))
* feat(category_theory/whiskering): whiskering nat_trans by functors
* simplify whiskering
#### Estimated changes
Added category_theory/whiskering.lean
- \+ *lemma* category_theory.whisker_left.app
- \+ *def* category_theory.whisker_left
- \+ *lemma* category_theory.whisker_left_twice
- \+ *lemma* category_theory.whisker_left_vcomp
- \+ *lemma* category_theory.whisker_right.app
- \+ *def* category_theory.whisker_right
- \+ *lemma* category_theory.whisker_right_left
- \+ *lemma* category_theory.whisker_right_twice
- \+ *lemma* category_theory.whisker_right_vcomp
- \+ *def* category_theory.whiskering_left
- \+ *def* category_theory.whiskering_right



## [2018-10-02 08:05:06+02:00](https://github.com/leanprover-community/mathlib/commit/470b6da)
feat(data/sum): add monad instance
#### Estimated changes
Modified category/applicative.lean


Modified category/basic.lean


Modified category/functor.lean


Modified category/traversable/instances.lean




## [2018-10-01 20:53:49+02:00](https://github.com/leanprover-community/mathlib/commit/dbb3ff0)
feat(data/zmod/quadratic_reciprocity): quadratic reciprocity ([#327](https://github.com/leanprover-community/mathlib/pull/327))
* multiplicative group of finite field is cyclic
* more stuff
* change chinese remainder to def
* get rid of nonsense
* delete extra line break
* one prod_bij left
* move lemmas to correct places
* delete prod_instances
* almost done
* move lamms to correct places
* more moving lemmas
* finished off moving lemmas
* fix build
* move quadratic reciprocity to zmod
* improve readability
* remove unnecessary alphas
* move `prod_range_id`
* fix build
* fix build
* fix build
* fix build
* delete mk_of_ne_zero
* move odd_mul_odd_div_two
* extra a few lemmas
* improving readability
* delete duplicate lemmas
* forgot to save
* delete duplicate lemma
* indent calc proofs
* fix build
* fix build
* forgot to save
* fix build
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* finset.card_bind
- \+ *lemma* finset.card_bind_le
- \+/\- *lemma* finset.prod_const
- \+/\- *lemma* finset.prod_image
- \+ *lemma* finset.prod_involution
- \+ *lemma* finset.prod_nat_pow
- \+ *lemma* finset.prod_pow
- \+ *lemma* finset.prod_range_id_eq_fact
- \+/\- *lemma* finset.sum_const
- \+ *lemma* finset.sum_smul

Modified algebra/field.lean
- \+ *lemma* units.units.mk0_inj

Modified algebra/field_power.lean


Modified algebra/group.lean
- \+ *lemma* units.coe_inv
- \+ *lemma* units.coe_mul
- \+ *lemma* units.coe_one
- \- *lemma* units.inv_coe
- \- *lemma* units.mul_coe
- \- *lemma* units.one_coe

Modified algebra/group_power.lean
- \+ *lemma* neg_one_pow_eq_pow_mod_two
- \+ *lemma* units.coe_pow

Modified algebra/ordered_ring.lean
- \+ *lemma* one_lt_mul

Modified algebra/pi_instances.lean
- \+ *lemma* finset.prod_mk_prod

Modified algebra/ring.lean
- \+ *lemma* units.coe_ne_zero
- \+ *lemma* units.inv_eq_self_iff

Modified data/finset.lean
- \+/\- *theorem* finset.card_attach
- \+ *lemma* finset.card_congr
- \+/\- *theorem* finset.card_range
- \+ *lemma* finset.card_union_add_card_inter
- \+ *lemma* finset.card_union_le
- \+/\- *theorem* finset.fold_image
- \+ *lemma* finset.surj_on_of_inj_on_of_card_le

Modified data/int/modeq.lean
- \+ *lemma* int.mod_mul_left_mod
- \+ *lemma* int.mod_mul_right_mod
- \+ *lemma* int.modeq.gcd_a_modeq
- \+ *theorem* int.modeq.mod_modeq
- \+ *lemma* int.modeq.modeq_and_modeq_iff_modeq_mul
- \+ *theorem* int.modeq.modeq_of_modeq_mul_left
- \+ *theorem* int.modeq.modeq_of_modeq_mul_right

Modified data/nat/basic.lean
- \+ *lemma* nat.div_dvd_of_dvd
- \+ *lemma* nat.mod_mul_left_div_self
- \+ *lemma* nat.mod_mul_right_div_self
- \+ *lemma* nat.pred_eq_sub_one
- \+ *lemma* nat.succ_le_iff
- \+ *lemma* nat.two_mul_odd_div_two

Modified data/nat/gcd.lean
- \+ *lemma* nat.coprime.mul_dvd_of_dvd_of_dvd
- \+ *lemma* nat.coprime_mul_iff_left
- \+ *lemma* nat.coprime_mul_iff_right

Modified data/nat/modeq.lean
- \+ *lemma* nat.mod_mul_left_mod
- \+ *lemma* nat.mod_mul_right_mod
- \+ *def* nat.modeq.chinese_remainder
- \- *theorem* nat.modeq.chinese_remainder
- \+ *lemma* nat.modeq.coprime_of_mul_modeq_one
- \+ *lemma* nat.modeq.modeq_and_modeq_iff_modeq_mul
- \+ *theorem* nat.modeq.modeq_of_modeq_mul_left
- \+ *theorem* nat.modeq.modeq_of_modeq_mul_right
- \+ *lemma* nat.odd_mul_odd
- \+ *lemma* nat.odd_mul_odd_div_two
- \+ *lemma* nat.odd_of_mod_four_eq_one
- \+ *lemma* nat.odd_of_mod_four_eq_three

Modified data/nat/prime.lean
- \+ *lemma* nat.prime.eq_two_or_odd

Added data/nat/totient.lean
- \+ *lemma* nat.sum_totient
- \+ *def* nat.totient
- \+ *lemma* nat.totient_le
- \+ *lemma* nat.totient_pos

Modified data/quot.lean
- \+/\- *theorem* quotient.mk_out'

Modified data/set/basic.lean


Modified data/set/finite.lean
- \+ *lemma* set.card_le_of_subset
- \+ *lemma* set.eq_of_subset_of_card_le

Renamed data/zmod.lean to data/zmod/basic.lean
- \+ *lemma* zmod.cast_mul_left_val_cast
- \+ *lemma* zmod.cast_mul_right_val_cast
- \+ *lemma* zmod.cast_val_cast_of_dvd
- \+ *lemma* zmod.coe_val_cast_int
- \+ *lemma* zmod.eq_zero_iff_dvd_int
- \+ *lemma* zmod.eq_zero_iff_dvd_nat
- \+ *lemma* zmod.le_div_two_iff_lt_neg
- \+ *lemma* zmod.ne_neg_self
- \+ *def* zmod.units_equiv_coprime
- \+ *lemma* zmodp.card_zmodp
- \+ *lemma* zmodp.coe_val_cast_int
- \+ *lemma* zmodp.eq_zero_iff_dvd_int
- \+ *lemma* zmodp.eq_zero_iff_dvd_nat
- \- *lemma* zmodp.gcd_a_modeq
- \+ *lemma* zmodp.le_div_two_iff_lt_neg
- \+ *lemma* zmodp.ne_neg_self
- \+ *lemma* zmodp.prime_ne_zero

Added data/zmod/quadratic_reciprocity.lean
- \+ *lemma* quadratic_reciprocity_aux.card_range_p_mul_q_filter_not_coprime
- \+ *lemma* quadratic_reciprocity_aux.filter_range_p_mul_q_div_two_eq
- \+ *lemma* quadratic_reciprocity_aux.prod_filter_range_p_mul_q_div_two_eq
- \+ *lemma* quadratic_reciprocity_aux.prod_filter_range_p_mul_q_div_two_eq_prod_product
- \+ *lemma* quadratic_reciprocity_aux.prod_filter_range_p_mul_q_div_two_mod_p_eq
- \+ *lemma* quadratic_reciprocity_aux.prod_filter_range_p_mul_q_not_coprime_eq
- \+ *lemma* quadratic_reciprocity_aux.prod_range_div_two_erase_zero
- \+ *lemma* quadratic_reciprocity_aux.prod_range_p_mul_q_div_two_ite_eq
- \+ *lemma* quadratic_reciprocity_aux.prod_range_p_mul_q_filter_coprime_mod_p
- \+ *lemma* quadratic_reciprocity_aux.range_p_product_range_q_div_two_prod
- \+ *lemma* zmodp.card_units_zmodp
- \+ *lemma* zmodp.euler_criterion
- \+ *lemma* zmodp.euler_criterion_units
- \+ *theorem* zmodp.fermat_little
- \+ *lemma* zmodp.is_square_iff_is_not_square_of_mod_four_eq_three
- \+ *lemma* zmodp.is_square_iff_is_square_of_mod_four_eq_one
- \+ *def* zmodp.legendre_sym
- \+ *lemma* zmodp.legendre_sym_eq_one_or_neg_one
- \+ *lemma* zmodp.legendre_sym_eq_pow
- \+ *lemma* zmodp.pow_div_two_eq_neg_one_or_one
- \+ *lemma* zmodp.prod_range_prime_erase_zero
- \+ *theorem* zmodp.quadratic_reciprocity
- \+ *lemma* zmodp.wilsons_lemma

Added field_theory/finite.lean
- \+ *lemma* coe_units_equiv_ne_zero
- \+ *lemma* finite_field.card_nth_roots_units
- \+ *lemma* finite_field.card_order_of_eq_totient
- \+ *lemma* finite_field.card_pow_eq_one_eq_order_of
- \+ *lemma* finite_field.card_units
- \+ *lemma* finite_field.prod_univ_units_id_eq_neg_one
- \+ *lemma* order_of_pow
- \+ *def* units_equiv_ne_zero

Modified group_theory/order_of_element.lean
- \+ *lemma* is_cyclic_of_order_of_eq_card
- \+ *lemma* order_of_dvd_of_pow_eq_one
- \+ *lemma* order_of_eq_card_of_forall_mem_gppowers
- \+ *lemma* order_of_le_of_pow_eq_one
- \+ *lemma* pow_card_eq_one
- \+ *lemma* powers_eq_gpowers
- \+ *lemma* sum_card_order_of_eq_card_pow_eq_one

Modified number_theory/pell.lean


Modified ring_theory/associated.lean




## [2018-10-01 20:35:10+02:00](https://github.com/leanprover-community/mathlib/commit/f3850c2)
feat(algebra/group): add units.map and prove that it is a group hom ([#374](https://github.com/leanprover-community/mathlib/pull/374))
#### Estimated changes
Modified algebra/group.lean




## [2018-10-01 20:34:14+02:00](https://github.com/leanprover-community/mathlib/commit/decb030)
style(tactic/*): minor simplifications to tidy-related tactics
#### Estimated changes
Modified tactic/basic.lean


Modified tactic/chain.lean


Modified tactic/interactive.lean


Modified tactic/tidy.lean




## [2018-10-01 20:26:32+02:00](https://github.com/leanprover-community/mathlib/commit/87a963b)
feat(tactic/ext): add apply_cfg argument to ext1 ([#346](https://github.com/leanprover-community/mathlib/pull/346))
* feat(tactics/ext): use `applyc _ {new_goals := new_goals.all}`
This causes goals to appear in the same order they appear as hypotheses of the
`@[extensionality]` lemma, rather than being reordered to put dependent
goals first.
This doesn't appear to affect any uses of `ext` in mathlib,
but is occasionally helpful in the development of category theory.
(Indeed, I have been running into tactic mode proofs that fail to
typecheck, when using ext, and this avoids the problem)
* adding configuration to non-interactive ext1
and a wrapper so tidy can sometimes produce shorter tactic scripts
#### Estimated changes
Modified tactic/ext.lean


Modified tactic/tidy.lean


Modified tests/tactics.lean
- \+ *structure* dependent_fields
- \+ *lemma* df.ext



## [2018-10-01 20:24:42+02:00](https://github.com/leanprover-community/mathlib/commit/1923c23)
feat(data/polynomial): interface general coefficients of a polynomial ([#339](https://github.com/leanprover-community/mathlib/pull/339))
* feat(data/polynomial): interface general coefficients of a polynomial
* fix(data/polynomial): fixing the code I broke when defining polynomial.ext
* fix(data/polynomial): tidy up comments
* Update polynomial.lean
* adding interface for scalar multiplication and coefficients
* feat(data/polynomial): coeff is R-linear
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* polynomial.C_mul'
- \+ *def* polynomial.coeff
- \+ *lemma* polynomial.coeff_C
- \+ *lemma* polynomial.coeff_C_mul_X
- \+ *lemma* polynomial.coeff_X
- \+ *lemma* polynomial.coeff_X_pow
- \+ *lemma* polynomial.coeff_add
- \+ *lemma* polynomial.coeff_is_linear
- \+ *theorem* polynomial.coeff_mul_X
- \+ *theorem* polynomial.coeff_mul_X_pow
- \+ *lemma* polynomial.coeff_mul_left
- \+ *lemma* polynomial.coeff_mul_right
- \+ *lemma* polynomial.coeff_one
- \+ *lemma* polynomial.coeff_smul
- \+ *lemma* polynomial.coeff_zero
- \+ *theorem* polynomial.ext
- \+ *theorem* polynomial.mul_X_pow_eq_zero



## [2018-10-01 20:19:59+02:00](https://github.com/leanprover-community/mathlib/commit/282754c)
fix(tactic/linarith): symmetric case
#### Estimated changes
Modified tactic/linarith.lean
- \+ *lemma* linarith.int.coe_nat_mul_bit0
- \+ *lemma* linarith.int.coe_nat_mul_bit1
- \+ *lemma* linarith.int.coe_nat_mul_one
- \+ *lemma* linarith.int.coe_nat_mul_zero



## [2018-10-01 20:19:59+02:00](https://github.com/leanprover-community/mathlib/commit/31ef46a)
feat(tactic/linarith): don't reject nonlinear hypotheses
#### Estimated changes
Modified tactic/linarith.lean
- \+ *lemma* linarith.int.coe_nat_bit0_mul
- \+ *lemma* linarith.int.coe_nat_bit1_mul
- \+ *lemma* linarith.int.coe_nat_one_mul
- \+ *lemma* linarith.int.coe_nat_zero_mul

Modified tests/linarith.lean




## [2018-10-01 18:10:17+02:00](https://github.com/leanprover-community/mathlib/commit/4ba7f23)
cleanup(data/holor)
#### Estimated changes
Modified data/holor.lean
- \+/\- *lemma* holor.cast_type
- \+/\- *def* holor
- \+/\- *lemma* holor_index.cast_type
- \+/\- *def* holor_index

Modified data/list/basic.lean
- \+/\- *theorem* list.drop_drop



## [2018-10-01 14:51:42+02:00](https://github.com/leanprover-community/mathlib/commit/7c361fa)
feat(data/holor): holor library
#### Estimated changes
Added data/holor.lean
- \+ *def* holor.assoc_left
- \+ *def* holor.assoc_right
- \+ *lemma* holor.cast_type
- \+ *inductive* holor.cprank_max1
- \+ *inductive* holor.cprank_max
- \+ *lemma* holor.cprank_max_1
- \+ *lemma* holor.cprank_max_add
- \+ *lemma* holor.cprank_max_mul
- \+ *lemma* holor.cprank_max_nil
- \+ *lemma* holor.cprank_max_sum
- \+ *lemma* holor.cprank_max_upper_bound
- \+ *lemma* holor.cprank_upper_bound
- \+ *lemma* holor.holor_index_cons_decomp
- \+ *def* holor.mul
- \+ *lemma* holor.mul_assoc0
- \+ *lemma* holor.mul_assoc
- \+ *lemma* holor.mul_left_distrib
- \+ *lemma* holor.mul_right_distrib
- \+ *lemma* holor.mul_scalar_mul
- \+ *lemma* holor.mul_zero
- \+ *def* holor.slice
- \+ *lemma* holor.slice_add
- \+ *lemma* holor.slice_eq
- \+ *lemma* holor.slice_sum
- \+ *lemma* holor.slice_unit_vec_mul
- \+ *lemma* holor.slice_zero
- \+ *lemma* holor.sum_unit_vec_mul_slice
- \+ *def* holor.unit_vec
- \+ *lemma* holor.zero_mul
- \+ *def* holor
- \+ *def* holor_index.assoc_left
- \+ *def* holor_index.assoc_right
- \+ *lemma* holor_index.cast_type
- \+ *def* holor_index.drop
- \+ *lemma* holor_index.drop_drop
- \+ *lemma* holor_index.drop_take
- \+ *def* holor_index.take
- \+ *lemma* holor_index.take_take
- \+ *def* holor_index

Modified data/list/basic.lean
- \+ *theorem* list.drop_drop
- \+ *theorem* list.drop_take
- \+ *theorem* list.forall₂_drop
- \+ *theorem* list.forall₂_drop_append
- \+ *theorem* list.forall₂_take
- \+ *theorem* list.forall₂_take_append



## [2018-10-01 14:40:27+02:00](https://github.com/leanprover-community/mathlib/commit/b66614d)
refactor(analysis/topology): renamed compact_open to continuous_map; moved locally_compact to a more general position
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* locally_compact_of_compact
- \+ *lemma* locally_compact_of_compact_nhds

Renamed analysis/topology/compact_open.lean to analysis/topology/continuous_map.lean
- \- *def* coev
- \- *def* compact_open
- \- *def* compact_open_gen
- \- *lemma* continuous_coev
- \- *lemma* continuous_ev
- \- *lemma* continuous_induced
- \+ *def* continuous_map.coev
- \+ *def* continuous_map.compact_open.gen
- \+ *lemma* continuous_map.continuous_coev
- \+ *lemma* continuous_map.continuous_ev
- \+ *lemma* continuous_map.continuous_induced
- \+ *def* continuous_map.ev
- \+ *lemma* continuous_map.image_coev
- \+/\- *def* continuous_map.induced
- \+ *def* continuous_map
- \- *def* ev
- \- *lemma* image_coev
- \- *lemma* locally_compact_of_compact
- \- *lemma* locally_compact_of_compact_nhds

