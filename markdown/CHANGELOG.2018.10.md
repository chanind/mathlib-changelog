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
- \+ *def* mk_val

Modified docs/tactics.md


Created tactic/fin_cases.lean


Created tests/fin_cases.lean




## [2018-10-30 12:23:50-04:00](https://github.com/leanprover-community/mathlib/commit/e585bed)
feat(data/int/basic): bounded forall is decidable for integers
#### Estimated changes
Modified data/int/basic.lean
- \+ *theorem* mem_range_iff
- \+ *def* range



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
- \+/\- *lemma* embedding_graph
- \+/\- *lemma* embedding_subtype_val
- \+/\- *lemma* continuous_subtype_val
- \+/\- *lemma* continuous_subtype_mk
- \+ *lemma* tendsto_subtype_val
- \+ *lemma* tendsto_subtype_rng
- \+ *lemma* tendsto_cons'
- \+ *lemma* tendsto_cons
- \+ *lemma* tendsto_cons_iff
- \+ *lemma* tendsto_nhds
- \+ *lemma* tendsto_length
- \+ *lemma* tendsto_insert_nth'
- \+ *lemma* tendsto_insert_nth
- \+ *lemma* continuous_insert_nth
- \+ *lemma* tendsto_remove_nth
- \+ *lemma* continuous_remove_nth
- \+ *lemma* cons_val
- \+ *lemma* continuous_insert_nth'

Modified analysis/topology/topological_space.lean
- \+ *lemma* nhds_nil
- \+ *lemma* nhds_cons

Modified analysis/topology/uniform_space.lean




## [2018-10-19 00:03:08+02:00](https://github.com/leanprover-community/mathlib/commit/f6812d5)
feat(analysis/topology): add type class for discrete topological spaces
#### Estimated changes
Modified analysis/topology/continuity.lean


Modified analysis/topology/topological_space.lean
- \+ *lemma* tendsto_pure_nhds
- \+ *lemma* is_open_discrete
- \+ *lemma* nhds_top
- \+ *lemma* nhds_discrete
- \- *lemma* is_open_top
- \- *lemma* t2_space_top

Modified order/filter.lean
- \+ *lemma* mem_pure_iff
- \+ *lemma* mem_map_seq_iff
- \+ *lemma* tendsto_pure_pure
- \+ *lemma* tendsto_const_pure
- \+ *lemma* map_prod
- \+ *lemma* prod_eq



## [2018-10-18 23:05:00+02:00](https://github.com/leanprover-community/mathlib/commit/99e14cd)
feat(group_theory/quotient_group): add map : quotient N -> quotient M
#### Estimated changes
Modified group_theory/quotient_group.lean
- \+ *def* map



## [2018-10-18 23:02:03+02:00](https://github.com/leanprover-community/mathlib/commit/f52d2cc)
chore(group_theory/free_abelian_group, abelianization): rename to_comm_group, to_add_comm_group -> lift
#### Estimated changes
Modified group_theory/abelianization.lean
- \+ *lemma* lift.of
- \- *lemma* to_comm_group.of
- \+ *theorem* lift.unique
- \- *theorem* to_comm_group.unique
- \+/\- *def* commutator
- \+/\- *def* abelianization
- \+/\- *def* of
- \+ *def* lift
- \- *def* to_comm_group
- \- *def* to_comm_group.is_group_hom

Modified group_theory/free_abelian_group.lean
- \+ *lemma* map_hom
- \+/\- *def* free_abelian_group
- \+/\- *def* of
- \+ *def* lift
- \+ *def* universal
- \- *def* to_add_comm_group
- \- *def* UMP

Modified group_theory/subgroup.lean
- \+ *lemma* closure_subset_iff

Modified linear_algebra/tensor_product.lean
- \+/\- *lemma* tmul.add_left
- \+/\- *lemma* tmul.add_right
- \+/\- *lemma* tmul.smul
- \+/\- *lemma* smul.is_add_group_hom
- \+/\- *lemma* add_tmul
- \+/\- *lemma* tmul_add
- \+/\- *lemma* smul_tmul
- \+/\- *lemma* tmul_smul
- \+/\- *lemma* to_module.add
- \+/\- *lemma* to_module.smul
- \+/\- *lemma* to_module.tmul
- \+/\- *theorem* zero_left
- \+/\- *theorem* zero_right
- \+/\- *theorem* neg_left
- \+/\- *theorem* neg_right
- \+/\- *theorem* linear_left
- \+/\- *theorem* linear_right
- \+/\- *theorem* comm
- \+/\- *theorem* comp
- \+/\- *theorem* bilinear
- \+/\- *theorem* to_module.unique
- \+/\- *theorem* to_module.ext
- \+/\- *def* relators
- \+/\- *def* tensor_product
- \+/\- *def* tmul
- \+/\- *def* smul.aux
- \+/\- *def* smul
- \+/\- *def* to_module
- \+/\- *def* to_module.linear
- \+/\- *def* to_module.equiv



## [2018-10-18 13:48:14+02:00](https://github.com/leanprover-community/mathlib/commit/c3e489c)
chore(data/fin): add cast_add
#### Estimated changes
Modified data/fin.lean
- \+/\- *def* cast_lt
- \+/\- *def* cast_le
- \+ *def* cast_add
- \+/\- *def* cast_succ



## [2018-10-18 09:43:01+02:00](https://github.com/leanprover-community/mathlib/commit/f2beca8)
feat(ring_theory): prove principal_ideal_domain is unique factorization domain
#### Estimated changes
Modified linear_algebra/submodule.lean
- \+ *lemma* span_singleton_subset
- \+ *lemma* mem_span_singleton

Modified ring_theory/associated.lean
- \+ *lemma* is_unit_of_dvd_one
- \+ *lemma* not_prime_zero
- \+ *lemma* exists_mem_multiset_dvd_of_prime
- \+ *lemma* associated_mul_mul
- \+ *lemma* dvd_eq_le
- \+ *lemma* exists_mem_multiset_le_of_prime
- \+ *lemma* prime_mk
- \+ *lemma* eq_of_mul_eq_mul_left
- \+ *lemma* le_of_mul_le_mul_left
- \+ *lemma* one_or_eq_of_le_of_prime
- \+ *theorem* is_unit_of_mul_one
- \+ *theorem* units.is_unit_mul_units
- \+/\- *theorem* is_unit_iff_dvd_one
- \+/\- *theorem* is_unit_iff_forall_dvd
- \- *theorem* units.is_unit_of_mul_one
- \- *theorem* is_unit_mul_units
- \+ *def* prime

Modified ring_theory/principal_ideal_domain.lean
- \+/\- *lemma* to_maximal_ideal
- \+/\- *lemma* mod_mem_iff
- \+ *lemma* is_noetherian_ring
- \+ *lemma* factors_decreasing
- \+ *lemma* exists_factors
- \+ *lemma* is_maximal_ideal_of_irreducible
- \+ *lemma* prime_of_irreducible
- \+ *lemma* associates_prime_of_irreducible
- \+ *lemma* eq_of_prod_eq_associates
- \+ *lemma* associated_of_associated_prod_prod
- \+ *lemma* factors_spec



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
- \+ *lemma* to_maximal_ideal
- \- *lemma* is_prime_ideal.to_maximal_ideal



## [2018-10-18 00:33:42+02:00](https://github.com/leanprover-community/mathlib/commit/a3ac630)
feat(algebra,group_theory): add various closure properties of subgroup and is_group_hom w.r.t gsmul, prod, sum
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* prod_eq_one
- \+ *lemma* gsmul_sum
- \+ *lemma* is_group_hom.multiset_prod
- \+ *lemma* is_group_hom.finset_prod
- \+ *lemma* is_group_hom_finset_prod

Modified algebra/group.lean
- \+ *lemma* is_group_hom_mul
- \+ *lemma* is_group_hom_inv
- \+ *lemma* is_add_group_hom_sub

Modified algebra/group_power.lean
- \+ *theorem* gsmul_neg
- \+ *theorem* smul
- \+ *theorem* gsmul
- \+ *theorem* gsmul_sub
- \+ *theorem* is_add_group_hom_gsmul

Modified algebra/pi_instances.lean
- \+ *lemma* list_prod_apply
- \+ *lemma* multiset_prod_apply
- \+ *lemma* finset_prod_apply

Modified group_theory/subgroup.lean
- \+ *theorem* is_add_subgroup.sub_mem

Modified group_theory/submonoid.lean
- \+ *lemma* list_prod_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* finset_prod_mem
- \- *lemma* is_submonoid.list_prod_mem



## [2018-10-17 23:01:03+02:00](https://github.com/leanprover-community/mathlib/commit/ea962a7)
chore(analysis/topology/continuity): locally_compact_space is Prop
#### Estimated changes
Modified analysis/topology/continuity.lean




## [2018-10-17 22:49:26+02:00](https://github.com/leanprover-community/mathlib/commit/bac655d)
feature(data/vector2, data/list): add insert_nth for vectors and lists
#### Estimated changes
Modified data/equiv/fin.lean


Modified data/fin.lean
- \+ *lemma* eq_iff_veq
- \+ *lemma* pred_inj
- \+ *lemma* cast_succ_inj

Modified data/list/basic.lean
- \+ *lemma* modify_nth_tail_modify_nth_tail
- \+ *lemma* modify_nth_tail_modify_nth_tail_le
- \+ *lemma* modify_nth_tail_modify_nth_tail_same
- \+ *lemma* modify_nth_tail_id
- \+ *lemma* insert_nth_nil
- \+ *lemma* length_insert_nth
- \+ *lemma* remove_nth_insert_nth
- \+ *lemma* insert_nth_remove_nth_of_ge
- \+ *lemma* insert_nth_remove_nth_of_le
- \+ *lemma* insert_nth_comm
- \+ *def* insert_nth

Modified data/vector2.lean
- \+ *lemma* insert_nth_val
- \+ *lemma* remove_nth_val
- \+ *lemma* remove_nth_insert_nth
- \+ *lemma* remove_nth_insert_nth_ne
- \+ *lemma* insert_nth_comm
- \+ *def* m_of_fn
- \+ *def* mmap
- \+ *def* insert_nth
- \- *def* {u}



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
- \+ *def* fin_zero_equiv
- \+ *def* fin_one_equiv
- \+ *def* fin_two_equiv

Modified data/fin.lean
- \+ *lemma* zero_le
- \+ *lemma* lt_iff_val_lt_val
- \+ *lemma* le_iff_val_le_val
- \+/\- *lemma* succ_val
- \+/\- *lemma* pred_val
- \+/\- *lemma* succ_pred
- \+/\- *lemma* pred_succ
- \+ *lemma* cast_succ_val
- \+ *lemma* cast_lt_val
- \+ *lemma* cast_succ_cast_lt
- \+ *lemma* sub_nat_val
- \+ *lemma* add_nat_val
- \+ *lemma* succ_above_descend
- \+ *lemma* pred_above_succ_above
- \- *lemma* fin.raise_val
- \- *lemma* lower_val
- \- *lemma* raise_val
- \- *lemma* raise_lower
- \- *lemma* ascend_descend
- \- *lemma* descend_ascend
- \+/\- *theorem* le_last
- \+ *theorem* succ_above_ne
- \+/\- *theorem* succ_rec_on_zero
- \+/\- *theorem* succ_rec_on_succ
- \+/\- *theorem* cases_zero
- \+/\- *theorem* cases_succ
- \- *theorem* eq_of_lt_succ_of_not_lt
- \- *theorem* ascend_ne
- \+/\- *def* fin_zero_elim
- \+/\- *def* last
- \+ *def* cast_le
- \+ *def* cast
- \+ *def* cast_succ
- \+ *def* cast_lt
- \+ *def* succ_above
- \+ *def* pred_above
- \+ *def* sub_nat
- \+/\- *def* add_nat
- \+/\- *def* succ_rec
- \+/\- *def* succ_rec_on
- \+/\- *def* cases
- \- *def* nat_add
- \- *def* raise
- \- *def* lower
- \- *def* raise_nat
- \- *def* lower_left
- \- *def* lower_right
- \- *def* ascend
- \- *def* descend

Modified data/nat/basic.lean
- \+ *theorem* eq_of_lt_succ_of_not_lt



## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/d2b3940)
feat(data/fin): ascend / descend for fin
#### Estimated changes
Modified data/fin.lean
- \+ *lemma* fin.raise_val
- \+ *lemma* lower_val
- \+ *lemma* succ_pred
- \+ *lemma* pred_succ
- \+ *lemma* raise_val
- \+ *lemma* raise_lower
- \+ *lemma* ascend_descend
- \+ *lemma* descend_ascend
- \+ *theorem* succ_rec_on_zero
- \+ *theorem* succ_rec_on_succ
- \+ *theorem* cases_zero
- \+ *theorem* cases_succ
- \+ *theorem* ascend_ne
- \- *theorem* fin.succ_rec_on_zero
- \- *theorem* fin.succ_rec_on_succ
- \- *theorem* fin.cases_zero
- \- *theorem* fin.cases_succ
- \+/\- *def* raise
- \+ *def* lower
- \+ *def* succ_rec
- \+ *def* succ_rec_on
- \+ *def* cases
- \+ *def* fin_zero_elim
- \+ *def* ascend
- \+ *def* descend
- \- *def* fin.succ_rec
- \- *def* fin.succ_rec_on
- \- *def* fin.cases



## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/f789969)
feat(data/finset): add min' / max' for non-empty finset
#### Estimated changes
Modified data/finset.lean
- \+ *lemma* filter_true
- \+ *theorem* lt_wf
- \+ *theorem* min'_mem
- \+ *theorem* min'_le
- \+ *theorem* le_min'
- \+ *theorem* max'_mem
- \+ *theorem* le_max'
- \+ *theorem* max'_le
- \+ *theorem* min'_lt_max'
- \+ *def* min'
- \+ *def* max'



## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/ef9566d)
feat(data/equiv): equivalences for fin * fin and fin + fin
#### Estimated changes
Modified data/equiv/basic.lean
- \+/\- *lemma* ext
- \+ *lemma* perm.ext
- \+ *lemma* symm_apply_eq
- \+ *lemma* eq_symm_apply
- \- *theorem* apply_eq_iff_eq_inverse_apply

Created data/equiv/fin.lean
- \+ *def* sum_fin_sum_equiv
- \+ *def* fin_prod_fin_equiv



## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/b085915)
feat(data/list): length_attach, nth_le_attach, nth_le_range, of_fn_eq_pmap, nodup_of_fn (by @kckennylau)
#### Estimated changes
Modified data/fintype.lean
- \+/\- *lemma* coe_univ

Modified data/list/basic.lean
- \+ *lemma* length_attach
- \+ *lemma* nth_le_attach
- \+ *lemma* nth_le_range
- \+/\- *theorem* length_of_fn
- \+/\- *theorem* nth_le_of_fn
- \+ *theorem* of_fn_eq_pmap
- \+ *theorem* nodup_of_fn



## [2018-10-17 13:50:02+02:00](https://github.com/leanprover-community/mathlib/commit/b454dae)
feat(group_theory/perm): swap_mul_swal / swap_swap_apply (by @kckennylau)
#### Estimated changes
Modified data/nat/basic.lean
- \+ *theorem* pred_eq_of_eq_succ

Modified group_theory/perm.lean
- \+ *lemma* swap_mul_self
- \+ *lemma* swap_swap_apply
- \+/\- *lemma* sign_mul
- \+/\- *lemma* sign_one
- \+ *lemma* sign_refl
- \+/\- *lemma* sign_inv
- \+/\- *lemma* sign_swap
- \+ *lemma* sign_swap'
- \+/\- *lemma* sign_eq_of_is_swap
- \+/\- *lemma* sign_aux3_symm_trans_trans
- \+/\- *lemma* sign_symm_trans_trans
- \+/\- *lemma* sign_prod_list_swap
- \+/\- *lemma* eq_sign_of_surjective_hom
- \+/\- *lemma* sign_subtype_perm
- \+/\- *lemma* sign_of_subtype
- \+/\- *lemma* sign_eq_sign_of_equiv
- \+/\- *lemma* sign_bij



## [2018-10-17 09:46:54+02:00](https://github.com/leanprover-community/mathlib/commit/530e1d1)
refactor (data/finset): explicit arguments for subset_union_* and inter_subset_*
This change makes them a little easier to apply, and also makes them consistent with their analogues in set.basic.
#### Estimated changes
Modified analysis/topology/infinite_sum.lean


Modified data/finset.lean
- \+/\- *theorem* subset_union_left
- \+/\- *theorem* subset_union_right
- \+/\- *theorem* inter_subset_left
- \+/\- *theorem* inter_subset_right

Modified data/finsupp.lean




## [2018-10-17 09:25:02+02:00](https://github.com/leanprover-community/mathlib/commit/b5cd974)
feat(*): trigonometric functions: exp, log, sin, cos, tan, sinh, cosh, tanh, pi, arcsin, argcos, arg ([#386](https://github.com/leanprover-community/mathlib/pull/386))
* `floor_ring` now is parameterized on a `linear_ordered_ring` instead of extending it.
*
#### Estimated changes
Modified algebra/archimedean.lean
- \+ *lemma* sub_floor_div_mul_nonneg
- \+ *lemma* sub_floor_div_mul_lt

Modified algebra/group_power.lean
- \+ *lemma* inv_pow'
- \+ *lemma* pow_le_one

Modified algebra/ordered_field.lean
- \+ *lemma* one_le_inv
- \+ *lemma* div_le_div_of_le_left

Modified algebra/ordered_ring.lean
- \+ *lemma* one_lt_mul_of_le_of_lt
- \+ *lemma* one_lt_mul_of_lt_of_le
- \+ *lemma* mul_le_of_le_one_right
- \+ *lemma* mul_le_of_le_one_left
- \+ *lemma* mul_lt_one_of_nonneg_of_lt_one_left
- \+ *lemma* mul_lt_one_of_nonneg_of_lt_one_right

Modified analysis/complex.lean
- \+ *lemma* uniform_continuous_re
- \+ *lemma* continuous_re
- \+ *lemma* uniform_continuous_im
- \+ *lemma* continuous_im
- \+ *lemma* uniform_continuous_of_real
- \+ *lemma* continuous_of_real
- \- *lemma* continuous_mul

Created analysis/exponential.lean
- \+ *lemma* tendsto_exp_zero_one
- \+ *lemma* continuous_exp
- \+ *lemma* continuous_sin
- \+ *lemma* continuous_cos
- \+ *lemma* continuous_tan
- \+ *lemma* continuous_sinh
- \+ *lemma* continuous_cosh
- \+ *lemma* exists_exp_eq_of_pos
- \+ *lemma* exp_log
- \+ *lemma* log_exp
- \+ *lemma* log_zero
- \+ *lemma* log_one
- \+ *lemma* exists_cos_eq_zero
- \+ *lemma* cos_pi_div_two
- \+ *lemma* one_le_pi_div_two
- \+ *lemma* pi_div_two_le_two
- \+ *lemma* two_le_pi
- \+ *lemma* pi_le_four
- \+ *lemma* pi_pos
- \+ *lemma* pi_div_two_pos
- \+ *lemma* two_pi_pos
- \+ *lemma* sin_pi
- \+ *lemma* cos_pi
- \+ *lemma* sin_two_pi
- \+ *lemma* cos_two_pi
- \+ *lemma* sin_add_pi
- \+ *lemma* sin_add_two_pi
- \+ *lemma* cos_add_two_pi
- \+ *lemma* sin_pi_sub
- \+ *lemma* cos_add_pi
- \+ *lemma* cos_pi_sub
- \+ *lemma* sin_pos_of_pos_of_lt_pi
- \+ *lemma* sin_nonneg_of_nonneg_of_le_pi
- \+ *lemma* sin_neg_of_neg_of_neg_pi_lt
- \+ *lemma* sin_nonpos_of_nonnpos_of_neg_pi_le
- \+ *lemma* sin_pi_div_two
- \+ *lemma* sin_add_pi_div_two
- \+ *lemma* sin_sub_pi_div_two
- \+ *lemma* sin_pi_div_two_sub
- \+ *lemma* cos_add_pi_div_two
- \+ *lemma* cos_sub_pi_div_two
- \+ *lemma* cos_pi_div_two_sub
- \+ *lemma* cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two
- \+ *lemma* cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two
- \+ *lemma* cos_neg_of_pi_div_two_lt_of_lt
- \+ *lemma* cos_nonpos_of_pi_div_two_le_of_le
- \+ *lemma* sin_nat_mul_pi
- \+ *lemma* sin_int_mul_pi
- \+ *lemma* cos_nat_mul_two_pi
- \+ *lemma* cos_int_mul_two_pi
- \+ *lemma* cos_int_mul_two_pi_add_pi
- \+ *lemma* sin_eq_zero_iff_of_lt_of_lt
- \+ *lemma* sin_eq_zero_iff
- \+ *lemma* sin_eq_zero_iff_cos_eq
- \+ *lemma* cos_eq_one_iff
- \+ *lemma* cos_eq_one_iff_of_lt_of_lt
- \+ *lemma* cos_lt_cos_of_nonneg_of_le_pi_div_two
- \+ *lemma* cos_lt_cos_of_nonneg_of_le_pi
- \+ *lemma* cos_le_cos_of_nonneg_of_le_pi
- \+ *lemma* sin_lt_sin_of_le_of_le_pi_div_two
- \+ *lemma* sin_le_sin_of_le_of_le_pi_div_two
- \+ *lemma* sin_inj_of_le_of_le_pi_div_two
- \+ *lemma* cos_inj_of_nonneg_of_le_pi
- \+ *lemma* exists_sin_eq
- \+ *lemma* arcsin_le_pi_div_two
- \+ *lemma* neg_pi_div_two_le_arcsin
- \+ *lemma* sin_arcsin
- \+ *lemma* arcsin_sin
- \+ *lemma* arcsin_inj
- \+ *lemma* arcsin_zero
- \+ *lemma* arcsin_one
- \+ *lemma* arcsin_neg
- \+ *lemma* arcsin_neg_one
- \+ *lemma* arcsin_nonneg
- \+ *lemma* arcsin_eq_zero_iff
- \+ *lemma* arcsin_pos
- \+ *lemma* arcsin_nonpos
- \+ *lemma* arccos_eq_pi_div_two_sub_arcsin
- \+ *lemma* arcsin_eq_pi_div_two_sub_arccos
- \+ *lemma* arccos_le_pi
- \+ *lemma* arccos_nonneg
- \+ *lemma* cos_arccos
- \+ *lemma* arccos_cos
- \+ *lemma* arccos_inj
- \+ *lemma* arccos_zero
- \+ *lemma* arccos_one
- \+ *lemma* arccos_neg_one
- \+ *lemma* arccos_neg
- \+ *lemma* cos_arcsin_nonneg
- \+ *lemma* cos_arcsin
- \+ *lemma* sin_arccos
- \+ *lemma* abs_div_sqrt_one_add_lt
- \+ *lemma* div_sqrt_one_add_lt_one
- \+ *lemma* neg_one_lt_div_sqrt_one_add
- \+ *lemma* tan_pos_of_pos_of_lt_pi_div_two
- \+ *lemma* tan_nonneg_of_nonneg_of_le_pi_div_two
- \+ *lemma* tan_neg_of_neg_of_pi_div_two_lt
- \+ *lemma* tan_nonpos_of_nonpos_of_neg_pi_div_two_le
- \+ *lemma* tan_lt_tan_of_nonneg_of_lt_pi_div_two
- \+ *lemma* tan_lt_tan_of_lt_of_lt_pi_div_two
- \+ *lemma* tan_inj_of_lt_of_lt_pi_div_two
- \+ *lemma* sin_arctan
- \+ *lemma* cos_arctan
- \+ *lemma* tan_arctan
- \+ *lemma* arctan_lt_pi_div_two
- \+ *lemma* neg_pi_div_two_lt_arctan
- \+ *lemma* tan_surjective
- \+ *lemma* arctan_tan
- \+ *lemma* arctan_zero
- \+ *lemma* arctan_neg
- \+ *lemma* arg_le_pi
- \+ *lemma* neg_pi_lt_arg
- \+ *lemma* arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg
- \+ *lemma* arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg
- \+ *lemma* arg_zero
- \+ *lemma* arg_one
- \+ *lemma* arg_neg_one
- \+ *lemma* arg_I
- \+ *lemma* arg_neg_I
- \+ *lemma* sin_arg
- \+ *lemma* cos_arg
- \+ *lemma* tan_arg
- \+ *lemma* arg_cos_add_sin_mul_I
- \+ *lemma* arg_eq_arg_iff
- \+ *lemma* arg_real_mul
- \+ *lemma* ext_abs_arg
- \+ *lemma* arg_of_real_of_nonneg
- \+ *lemma* arg_of_real_of_neg
- \+ *lemma* log_re
- \+ *lemma* log_im
- \+ *lemma* exp_inj_of_neg_pi_lt_of_le_pi
- \+ *lemma* of_real_log
- \+ *lemma* log_neg_one
- \+ *lemma* log_I
- \+ *lemma* log_neg_I

Modified analysis/real.lean
- \+ *lemma* real.intermediate_value
- \+ *lemma* real.intermediate_value'
- \- *lemma* real.continuous_mul

Modified data/complex/basic.lean
- \+/\- *lemma* of_real_zero
- \+ *lemma* I_mul_I
- \+ *lemma* conj_neg_I
- \+ *lemma* bit0_re
- \+ *lemma* bit1_re
- \+ *lemma* bit0_im
- \+ *lemma* bit1_im
- \+ *lemma* of_real_pow
- \+ *lemma* conj_pow
- \+ *lemma* conj_two
- \+ *lemma* conj_sub
- \+ *lemma* abs_two
- \+ *lemma* abs_re_div_abs_le_one
- \+ *lemma* abs_im_div_abs_le_one
- \+ *lemma* abs_cast_nat
- \+ *lemma* norm_sq_eq_abs
- \+ *lemma* is_cau_seq_abs
- \+ *lemma* re_const_equiv_of_const_equiv
- \+ *lemma* im_const_equiv_of_const_equiv
- \+ *lemma* eq_lim_of_const_equiv
- \+ *lemma* lim_eq_of_equiv_const
- \+ *lemma* lim_eq_lim_of_equiv
- \+ *lemma* lim_const
- \+ *lemma* lim_add
- \+ *lemma* lim_mul_lim
- \+ *lemma* lim_mul
- \+ *lemma* lim_neg
- \+ *lemma* is_cau_seq_conj
- \+ *lemma* lim_conj
- \+ *lemma* lim_eq_zero_iff
- \+ *lemma* lim_inv
- \+ *lemma* lim_abs

Created data/complex/exponential.lean
- \+ *lemma* geo_sum_eq
- \+ *lemma* geo_sum_inv_eq
- \+ *lemma* forall_ge_le_of_forall_le_succ
- \+ *lemma* is_cau_of_decreasing_bounded
- \+ *lemma* is_cau_of_mono_bounded
- \+ *lemma* is_cau_series_of_abv_le_cau
- \+ *lemma* is_cau_series_of_abv_cau
- \+ *lemma* is_cau_geo_series
- \+ *lemma* is_cau_geo_series_const
- \+ *lemma* series_ratio_test
- \+ *lemma* sum_range_diag_flip
- \+ *lemma* abv_sum_le_sum_abv
- \+ *lemma* sum_range_sub_sum_range
- \+ *lemma* cauchy_product
- \+ *lemma* is_cau_abs_exp
- \+ *lemma* is_cau_exp
- \+ *lemma* exp_zero
- \+ *lemma* exp_add
- \+ *lemma* exp_ne_zero
- \+ *lemma* exp_neg
- \+ *lemma* exp_sub
- \+ *lemma* exp_conj
- \+ *lemma* exp_of_real_im
- \+ *lemma* exp_of_real_re
- \+ *lemma* of_real_exp_of_real_re
- \+ *lemma* of_real_exp
- \+ *lemma* sin_zero
- \+ *lemma* sin_neg
- \+ *lemma* sin_add
- \+ *lemma* cos_zero
- \+ *lemma* cos_neg
- \+ *lemma* cos_add
- \+ *lemma* sin_sub
- \+ *lemma* cos_sub
- \+ *lemma* sin_conj
- \+ *lemma* sin_of_real_im
- \+ *lemma* sin_of_real_re
- \+ *lemma* of_real_sin_of_real_re
- \+ *lemma* of_real_sin
- \+ *lemma* cos_conj
- \+ *lemma* cos_of_real_im
- \+ *lemma* cos_of_real_re
- \+ *lemma* of_real_cos_of_real_re
- \+ *lemma* of_real_cos
- \+ *lemma* tan_zero
- \+ *lemma* tan_eq_sin_div_cos
- \+ *lemma* tan_neg
- \+ *lemma* tan_conj
- \+ *lemma* tan_of_real_im
- \+ *lemma* tan_of_real_re
- \+ *lemma* of_real_tan_of_real_re
- \+ *lemma* of_real_tan
- \+ *lemma* sin_pow_two_add_cos_pow_two
- \+ *lemma* cos_two_mul
- \+ *lemma* sin_two_mul
- \+ *lemma* exp_mul_I
- \+ *lemma* exp_add_mul_I
- \+ *lemma* exp_eq_exp_re_mul_sin_add_cos
- \+ *lemma* sinh_zero
- \+ *lemma* sinh_neg
- \+ *lemma* sinh_add
- \+ *lemma* cosh_zero
- \+ *lemma* cosh_neg
- \+ *lemma* cosh_add
- \+ *lemma* sinh_sub
- \+ *lemma* cosh_sub
- \+ *lemma* sinh_conj
- \+ *lemma* sinh_of_real_im
- \+ *lemma* sinh_of_real_re
- \+ *lemma* of_real_sinh_of_real_re
- \+ *lemma* of_real_sinh
- \+ *lemma* cosh_conj
- \+ *lemma* cosh_of_real_im
- \+ *lemma* cosh_of_real_re
- \+ *lemma* of_real_cosh_of_real_re
- \+ *lemma* of_real_cosh
- \+ *lemma* tanh_eq_sinh_div_cosh
- \+ *lemma* tanh_zero
- \+ *lemma* tanh_neg
- \+ *lemma* tanh_conj
- \+ *lemma* tanh_of_real_im
- \+ *lemma* tanh_of_real_re
- \+ *lemma* of_real_tanh_of_real_re
- \+ *lemma* of_real_tanh
- \+ *lemma* abs_sin_le_one
- \+ *lemma* abs_cos_le_one
- \+ *lemma* sin_le_one
- \+ *lemma* cos_le_one
- \+ *lemma* neg_one_le_sin
- \+ *lemma* neg_one_le_cos
- \+ *lemma* sin_pow_two_le_one
- \+ *lemma* cos_pow_two_le_one
- \+ *lemma* add_one_le_exp_of_nonneg
- \+ *lemma* one_le_exp
- \+ *lemma* exp_pos
- \+ *lemma* abs_exp
- \+ *lemma* exp_le_exp
- \+ *lemma* exp_lt_exp
- \+ *lemma* exp_injective
- \+ *lemma* sum_div_fact_le
- \+ *lemma* exp_bound
- \+ *lemma* abs_exp_sub_one_le
- \+ *lemma* cos_bound
- \+ *lemma* sin_bound
- \+ *lemma* cos_pos_of_le_one
- \+ *lemma* sin_pos_of_pos_of_le_one
- \+ *lemma* sin_pos_of_pos_of_le_two
- \+ *lemma* cos_one_le
- \+ *lemma* cos_one_pos
- \+ *lemma* cos_two_neg
- \+ *lemma* abs_cos_add_sin_mul_I
- \+ *lemma* abs_exp_eq_iff_re_eq
- \+ *lemma* abs_exp_of_real
- \+ *def* exp'
- \+ *def* exp
- \+ *def* sin
- \+ *def* cos
- \+ *def* tan
- \+ *def* sinh
- \+ *def* cosh
- \+ *def* tanh

Modified data/int/basic.lean
- \+ *lemma* mod_two_eq_zero_or_one
- \+ *lemma* cast_two

Modified data/nat/basic.lean
- \+ *lemma* fact_mul_pow_le_fact

Modified data/nat/cast.lean
- \+ *lemma* cast_two

Modified data/real/basic.lean
- \+ *lemma* lim_le
- \+ *lemma* le_lim
- \+ *lemma* lt_lim
- \+ *lemma* lim_lt

Modified data/real/cau_seq.lean
- \+ *lemma* abv_pow
- \+ *lemma* le_of_eq_of_le
- \+ *lemma* le_of_le_of_eq
- \+ *lemma* le_of_exists



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
- \+ *lemma* prime.dvd_fact



## [2018-10-15 15:12:23+02:00](https://github.com/leanprover-community/mathlib/commit/c5930f5)
feat(group_theory.order_of_element): subgroups of cyclic groups are cyclic ([#423](https://github.com/leanprover-community/mathlib/pull/423))
* feat(group_theory.order_of_element): subgroups of cyclic groups are cyclic
* delete new line
#### Estimated changes
Modified group_theory/order_of_element.lean


Modified group_theory/subgroup.lean
- \+ *lemma* is_subgroup.coe_inv
- \+ *lemma* is_subgroup.coe_gpow
- \+ *lemma* is_add_subgroup.gsmul_coe

Modified group_theory/submonoid.lean
- \+ *lemma* is_submonoid.coe_one
- \+ *lemma* is_submonoid.coe_mul
- \+ *lemma* is_submonoid.coe_pow
- \+ *lemma* is_add_submonoid.smul_coe



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/a33ab12)
refactor(analysis/topology): move separation ring to quotient_topological_structures
#### Estimated changes
Modified analysis/topology/completion.lean
- \- *lemma* ring_sep_rel
- \- *lemma* ring_sep_quot
- \- *lemma* eq_mpr_heq

Modified analysis/topology/quotient_topological_structures.lean
- \+ *lemma* {u}
- \+ *lemma* quotient_ring.quotient_map_coe_coe
- \+ *lemma* ring_sep_rel
- \+ *lemma* ring_sep_quot
- \- *lemma* is_open_map_mul_left
- \- *lemma* is_open_map_mul_right
- \- *lemma* quotient_ring.quotient_map
- \+ *def* comm_ring_congr
- \+ *def* sep_quot_equiv_ring_quot

Modified analysis/topology/topological_structures.lean
- \+ *lemma* is_open_map_mul_left
- \+ *lemma* is_open_map_mul_right



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/1308077)
feature(data/equiv/algebra): add mul left/right and inverse as equivalences
#### Estimated changes
Modified analysis/topology/topological_structures.lean


Created data/equiv/algebra.lean


Modified data/equiv/basic.lean




## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/c8ecae8)
feature(analysis/topology/continuity): start homeomorphism
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* coe_eq_to_equiv
- \+ *lemma* symm_comp_self
- \+ *lemma* self_comp_symm
- \+ *lemma* range_coe
- \+ *lemma* image_symm
- \+ *lemma* preimage_symm
- \+ *lemma* induced_eq
- \+ *lemma* coinduced_eq
- \+ *def* prod_congr
- \+ *def* prod_comm
- \+ *def* prod_assoc

Modified data/equiv/basic.lean
- \+/\- *def* prod_congr



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/af434b5)
refactor(analysis/topology): move is_open_map to continuity
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* is_open_map_iff_nhds_le
- \+ *lemma* of_inverse
- \+ *lemma* to_quotient_map
- \- *lemma* quotient_map_id
- \- *lemma* quotient_map_compose
- \- *lemma* quotient_map_of_quotient_map_compose
- \- *lemma* quotient_map.continuous_iff
- \- *lemma* quotient_map.continuous
- \+ *def* is_open_map

Modified analysis/topology/quotient_topological_structures.lean
- \- *lemma* is_open_map_iff_nhds_le
- \- *lemma* of_inverse
- \- *lemma* to_quotient_map
- \- *lemma* is_open_coinduced
- \- *def* is_open_map

Modified analysis/topology/topological_space.lean
- \+ *lemma* is_open_induced_iff
- \+ *lemma* is_open_coinduced



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/29675ad)
refactor(analysis/topology/topological_structures): use to_additive to derive topological_add_monoid and topological_add_group
#### Estimated changes
Modified analysis/topology/quotient_topological_structures.lean
- \+/\- *lemma* of_inverse
- \+ *lemma* to_quotient_map
- \+ *lemma* is_open_coinduced
- \+ *lemma* is_open_map_mul_left
- \+ *lemma* is_open_map_mul_right
- \+ *lemma* quotient_ring.is_open_map_coe
- \+ *lemma* quotient_ring.quotient_map
- \- *lemma* is_open_map_iff_nhds_sets
- \- *lemma* quotient_map_of_open_of_surj_of_cont
- \- *lemma* continuous_inv'
- \- *lemma* continuous_inv
- \- *lemma* is_open_translate
- \- *lemma* quotient_add_group_saturate
- \- *lemma* is_open_add_translate
- \- *lemma* quotient_add_group.open_coe
- \- *lemma* is_open_ring_add_translate
- \- *lemma* quotient_ring.open_coe
- \- *lemma* quotient_ring.is_open_map

Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean
- \+ *lemma* continuous_inv'
- \+ *lemma* continuous_inv
- \+ *lemma* tendsto_inv
- \+ *lemma* exists_nhds_split
- \+ *lemma* exists_nhds_split4
- \+ *lemma* nhds_one_symm
- \+ *lemma* nhds_translation_mul_inv
- \+/\- *lemma* continuous_sub
- \+/\- *lemma* continuous_sub'
- \+/\- *lemma* tendsto_sub
- \+/\- *lemma* nhds_translation
- \- *lemma* continuous_add'
- \- *lemma* continuous_add
- \- *lemma* tendsto_add'
- \- *lemma* tendsto_add
- \- *lemma* tendsto_list_sum
- \- *lemma* continuous_list_sum
- \- *lemma* tendsto_multiset_sum
- \- *lemma* tendsto_finset_sum
- \- *lemma* continuous_multiset_sum
- \- *lemma* continuous_finset_sum
- \- *lemma* continuous_neg'
- \- *lemma* continuous_neg
- \- *lemma* tendsto_neg
- \- *lemma* exists_nhds_half
- \- *lemma* exists_nhds_quarter
- \- *lemma* nhds_zero_symm



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/75046c2)
chore(data/quot): add setoid.ext
#### Estimated changes
Modified analysis/topology/completion.lean


Modified data/quot.lean
- \+ *lemma* ext



## [2018-10-15 13:39:24+02:00](https://github.com/leanprover-community/mathlib/commit/2395183)
feat(analysis/topology/quotient_topological_structures): endow quotient
of topological groups, add groups and rings with a topological whatever
structure
This is not yet sorted. I'd like to push completions before cleaning
this.
#### Estimated changes
Modified analysis/topology/completion.lean
- \+ *lemma* ring_sep_rel
- \+ *lemma* ring_sep_quot
- \+ *lemma* eq_mpr_heq

Created analysis/topology/quotient_topological_structures.lean
- \+ *lemma* is_open_map_iff_nhds_sets
- \+ *lemma* is_open_map_iff_nhds_le
- \+ *lemma* of_inverse
- \+ *lemma* quotient_map_of_open_of_surj_of_cont
- \+ *lemma* continuous_inv'
- \+ *lemma* continuous_inv
- \+ *lemma* quotient_group_saturate
- \+ *lemma* is_open_translate
- \+ *lemma* quotient_group.open_coe
- \+ *lemma* quotient_add_group_saturate
- \+ *lemma* is_open_add_translate
- \+ *lemma* quotient_add_group.open_coe
- \+ *lemma* is_open_ring_add_translate
- \+ *lemma* quotient_ring_saturate
- \+ *lemma* quotient_ring.open_coe
- \+ *lemma* quotient_ring.is_open_map
- \+ *def* is_open_map



## [2018-10-15 13:35:49+02:00](https://github.com/leanprover-community/mathlib/commit/7358605)
feat(analysis/topology/completion): comm_ring on separation quotient, completion (separation_quotient A) is equivalent to completion A
#### Estimated changes
Modified analysis/topology/completion.lean
- \+ *lemma* lift_mk
- \+ *lemma* uniform_continuous_lift
- \+ *lemma* map_mk
- \+ *lemma* uniform_continuous_map
- \+ *lemma* map_unique
- \+ *lemma* map_id
- \+ *lemma* map_comp
- \+ *lemma* ext
- \+ *lemma* extension_map
- \+ *lemma* uniform_continuous_completion_separation_quotient_equiv
- \+ *lemma* uniform_continuous_completion_separation_quotient_equiv_symm
- \- *lemma* prod_pure_pure
- \- *lemma* uniform_continuous_of_const
- \- *lemma* cauchy_prod
- \- *lemma* complete_space_separation
- \- *lemma* separated_separation
- \+ *def* separation_quotient
- \+ *def* lift
- \+ *def* map
- \+ *def* completion_separation_quotient_equiv

Modified analysis/topology/continuity.lean
- \+ *lemma* mem_closure
- \+ *lemma* mem_closure2

Modified analysis/topology/topological_structures.lean
- \- *lemma* is_ideal_iff

Modified data/quot.lean
- \+ *lemma* nonempty_quotient_iff

Modified data/set/basic.lean
- \- *lemma* image_subset_iff'

Modified order/filter.lean
- \+ *lemma* prod_pure_pure



## [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/13be74f)
feat(analysis/topology/topological_structure): ideal closure is ideal
#### Estimated changes
Modified analysis/topology/topological_structures.lean
- \+ *lemma* is_ideal_iff

Modified data/set/basic.lean
- \+ *lemma* image_subset_iff'



## [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/7697a84)
feat(analysis/topology/topological_groups): construct topologies out of a group and a neighbourhood filter at 0
#### Estimated changes
Deleted analysis/topology/complete_groups.lean
- \- *lemma* tendsto_sub_comap_self
- \- *lemma* is_Z_bilin.zero_left
- \- *lemma* is_Z_bilin.zero_right
- \- *lemma* is_Z_bilin.zero
- \- *lemma* is_Z_bilin.neg_left
- \- *lemma* is_Z_bilin.neg_right
- \- *lemma* is_Z_bilin.sub_left
- \- *lemma* is_Z_bilin.sub_right
- \- *lemma* is_Z_bilin.tendsto_zero_left
- \- *lemma* is_Z_bilin.tendsto_zero_right
- \- *theorem* extend_Z_bilin

Modified analysis/topology/completion.lean
- \+/\- *lemma* dense
- \+ *lemma* dense_embedding_coe
- \+ *lemma* is_Z_bilin.zero_left
- \+ *lemma* is_Z_bilin.zero_right
- \+ *lemma* is_Z_bilin.zero
- \+ *lemma* is_Z_bilin.neg_left
- \+ *lemma* is_Z_bilin.neg_right
- \+ *lemma* is_Z_bilin.sub_left
- \+ *lemma* is_Z_bilin.sub_right
- \+ *lemma* is_Z_bilin.tendsto_zero_left
- \+ *lemma* is_Z_bilin.tendsto_zero_right
- \+ *lemma* tendsto_sub_comap_self
- \+ *lemma* coe_one
- \+ *lemma* continuous_mul'
- \+ *lemma* coe_mul
- \+ *lemma* continuous_mul
- \+ *theorem* extend_Z_bilin

Modified analysis/topology/topological_groups.lean
- \+ *lemma* uniformity_eq_comap_nhds_zero'
- \+ *lemma* topological_add_group_is_uniform
- \+ *lemma* to_uniform_space_eq
- \+ *lemma* neg_Z
- \+ *lemma* add_Z
- \+ *lemma* exists_Z_half
- \+ *lemma* nhds_eq
- \+ *lemma* nhds_zero_eq_Z
- \- *lemma* half_nhd
- \- *lemma* quarter_nhd
- \- *lemma* nhds_zero_symm
- \- *lemma* nhds_translation
- \- *lemma* uniformity_eq_comap_nhds_zero
- \- *def* δ
- \- *def* Δ

Modified analysis/topology/topological_space.lean


Modified analysis/topology/topological_structures.lean
- \+ *lemma* exists_nhds_half
- \+ *lemma* exists_nhds_quarter
- \+ *lemma* nhds_zero_symm
- \+ *lemma* nhds_translation

Modified order/filter.lean
- \+/\- *lemma* comap_eq_of_inverse
- \+ *lemma* map_eq_of_inverse



## [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/96d3f95)
doc(analysis/topology/completion): document changed organization
#### Estimated changes
Modified analysis/topology/completion.lean




## [2018-10-15 13:33:05+02:00](https://github.com/leanprover-community/mathlib/commit/fbb6e9b)
feat(analysis/topology): group completion
#### Estimated changes
Modified analysis/real.lean
- \- *theorem* real.Cauchy_eq

Created analysis/topology/complete_groups.lean
- \+ *lemma* tendsto_sub_comap_self
- \+ *lemma* is_Z_bilin.zero_left
- \+ *lemma* is_Z_bilin.zero_right
- \+ *lemma* is_Z_bilin.zero
- \+ *lemma* is_Z_bilin.neg_left
- \+ *lemma* is_Z_bilin.neg_right
- \+ *lemma* is_Z_bilin.sub_left
- \+ *lemma* is_Z_bilin.sub_right
- \+ *lemma* is_Z_bilin.tendsto_zero_left
- \+ *lemma* is_Z_bilin.tendsto_zero_right
- \+ *theorem* extend_Z_bilin

Created analysis/topology/completion.lean
- \+ *lemma* prod_pure_pure
- \+ *lemma* uniform_continuous_of_const
- \+ *lemma* cauchy_prod
- \+ *lemma* uniformity_quotient
- \+ *lemma* uniform_continuous_quotient_mk
- \+ *lemma* uniform_continuous_quotient
- \+ *lemma* uniform_continuous_quotient_lift
- \+ *lemma* uniform_continuous_quotient_lift₂
- \+ *lemma* comap_quotient_le_uniformity
- \+ *lemma* comap_quotient_eq_uniformity
- \+ *lemma* complete_space_separation
- \+ *lemma* separated_separation
- \+ *lemma* separated_of_uniform_continuous
- \+ *lemma* eq_of_separated_of_uniform_continuous
- \+ *lemma* separation_prod
- \+ *lemma* monotone_gen
- \+ *lemma* uniform_embedding_pure_cauchy
- \+ *lemma* pure_cauchy_dense
- \+ *lemma* dense_embedding_pure_cauchy
- \+ *lemma* nonempty_Cauchy_iff
- \+ *lemma* extend_pure_cauchy
- \+ *lemma* uniform_continuous_extend
- \+ *lemma* injective_separated_pure_cauchy
- \+ *lemma* prod_pure_cauchy_pure_cauchy
- \+ *lemma* uniform_continuous_prod
- \+ *lemma* uniform_continuous_coe
- \+ *lemma* continuous_coe
- \+ *lemma* comap_coe_eq_uniformity
- \+ *lemma* uniform_embedding_coe
- \+ *lemma* dense
- \+ *lemma* dense₂
- \+ *lemma* dense₃
- \+ *lemma* induction_on
- \+ *lemma* induction_on₂
- \+ *lemma* induction_on₃
- \+ *lemma* induction_on₄
- \+ *lemma* uniform_continuous_extension
- \+ *lemma* continuous_extension
- \+ *lemma* extension_coe
- \+ *lemma* uniform_continuous_map
- \+ *lemma* continuous_map
- \+ *lemma* map_coe
- \+ *lemma* prod_coe_coe
- \+ *lemma* uniform_continuous_map₂'
- \+ *lemma* continuous_map₂
- \+ *lemma* map₂_coe_coe
- \+ *lemma* coe_zero
- \+ *lemma* coe_neg
- \+ *lemma* coe_add
- \+ *lemma* is_add_group_hom_extension
- \+ *lemma* is_add_group_hom_map
- \+ *lemma* is_add_group_hom_prod
- \+ *theorem* mem_uniformity
- \+ *theorem* mem_uniformity'
- \+ *theorem* Cauchy_eq
- \+ *def* separation_setoid
- \+ *def* Cauchy
- \+ *def* gen
- \+ *def* pure_cauchy
- \+ *def* extend
- \+ *def* prod
- \+ *def* completion

Modified analysis/topology/continuity.lean
- \+ *lemma* embedding.closure_eq_preimage_closure_image
- \+/\- *lemma* extend_e_eq
- \+/\- *lemma* extend_eq

Created analysis/topology/topological_groups.lean
- \+ *lemma* half_nhd
- \+ *lemma* quarter_nhd
- \+ *lemma* nhds_zero_symm
- \+ *lemma* nhds_translation
- \+ *lemma* uniformity_eq_comap_nhds_zero
- \+ *def* δ
- \+ *def* Δ
- \+ *def* topological_add_group.to_uniform_space

Modified analysis/topology/topological_structures.lean
- \+/\- *lemma* uniform_continuous_sub'
- \+/\- *lemma* uniform_continuous_sub
- \+/\- *lemma* uniform_continuous_neg
- \+/\- *lemma* uniform_continuous_neg'
- \+/\- *lemma* uniform_continuous_add
- \+/\- *lemma* uniform_continuous_add'
- \+ *lemma* uniformity_translate
- \+ *lemma* uniform_embedding_translate
- \+ *lemma* uniformity_eq_comap_nhds_zero
- \+ *lemma* group_separation_rel
- \+ *lemma* uniform_continuous_of_tendsto_zero
- \+ *lemma* uniform_continuous_of_continuous
- \- *lemma* dense_or_discrete

Modified analysis/topology/uniform_space.lean
- \+ *lemma* uniform_continuous_of_const
- \+ *lemma* uniform_embedding.embedding
- \+/\- *lemma* uniformly_extend_of_emb
- \+/\- *lemma* uniformly_extend_exists
- \+/\- *lemma* uniformly_extend_spec
- \+/\- *lemma* uniform_continuous_uniformly_extend
- \+ *lemma* mem_uniformity_of_uniform_continuous_invarant
- \+ *lemma* cauchy_prod
- \+ *lemma* continuous_extend_of_cauchy
- \- *lemma* uniform_continuous_quotient_mk
- \- *lemma* comap_quotient_le_uniformity
- \- *lemma* comap_quotient_eq_uniformity
- \- *lemma* complete_space_separation
- \- *lemma* separated_separation
- \- *lemma* uniform_continuous_quotient
- \- *lemma* uniform_continuous_quotient_lift
- \- *lemma* uniformity_quotient
- \- *lemma* separated_of_uniform_continuous
- \- *lemma* eq_of_separated_of_uniform_continuous
- \- *lemma* monotone_gen
- \- *lemma* uniform_embedding_pure_cauchy
- \- *lemma* pure_cauchy_dense
- \- *lemma* injective_separated_pure_cauchy
- \- *lemma* uniform_continuous_quotient_lift₂
- \- *lemma* separation_prod
- \+/\- *theorem* uniformity_prod
- \- *theorem* mem_uniformity
- \- *theorem* mem_uniformity'
- \- *def* Cauchy
- \- *def* gen
- \- *def* pure_cauchy

Modified data/set/basic.lean
- \+ *lemma* prod_quotient_preimage_eq_image

Modified data/set/lattice.lean
- \+ *lemma* preimage_Inter
- \+ *lemma* preimage_bInter

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
- \+/\- *lemma* const_mul_eq_map
- \+ *lemma* lintegral_const_mul
- \+ *lemma* lintegral_supr_const
- \+/\- *theorem* const_apply
- \+/\- *theorem* bind_const
- \+/\- *def* const
- \+/\- *def* map
- \+ *def* integral
- \+ *def* measure.with_density



## [2018-10-10 22:50:06+02:00](https://github.com/leanprover-community/mathlib/commit/40f5565)
feat(analysis/measure_theory): lower Lebesgue integral under addition, supremum
#### Estimated changes
Modified algebra/big_operators.lean
- \+ *lemma* prod_image'
- \+ *lemma* prod_hom_rel

Modified analysis/ennreal.lean
- \+ *lemma* tendsto_coe_nnreal_nhds_top
- \+/\- *lemma* supr_add_supr
- \+ *lemma* supr_add_supr_of_monotone
- \+ *lemma* finset_sum_supr_nat
- \+ *lemma* mul_Sup
- \+ *lemma* mul_supr
- \+ *lemma* supr_mul
- \- *lemma* coe_nat
- \- *lemma* nhds_top
- \- *lemma* nhds_of_real_eq_map_of_real_nhds_nonneg

Modified analysis/measure_theory/borel_space.lean
- \+ *lemma* measurable_le
- \+ *lemma* measurable_coe_int_real

Modified analysis/measure_theory/integration.lean
- \+ *lemma* supr_eq_of_tendsto
- \+ *lemma* range_const
- \+ *lemma* pair_apply
- \+ *lemma* sup_apply
- \+ *lemma* mul_apply
- \+ *lemma* add_eq_map₂
- \+ *lemma* sup_eq_map₂
- \+ *lemma* const_mul_eq_map
- \+ *lemma* finset_sup_apply
- \+ *lemma* approx_apply
- \+ *lemma* monotone_approx
- \+ *lemma* supr_approx_apply
- \+ *lemma* ennreal_rat_embed_encode
- \+ *lemma* monotone_eapprox
- \+ *lemma* supr_eapprox_apply
- \+ *lemma* map_integral
- \+ *lemma* zero_integral
- \+ *lemma* add_integral
- \+ *lemma* const_mul_integral
- \+ *lemma* mem_restrict_range
- \+ *lemma* restrict_preimage'
- \+ *lemma* restrict_integral
- \+ *lemma* restrict_const_integral
- \+ *lemma* integral_sup_le
- \+ *lemma* integral_le_integral
- \+ *lemma* integral_congr
- \+ *lemma* lintegral_le_lintegral
- \+ *lemma* lintegral_eq_nnreal
- \+ *lemma* lintegral_eq_supr_eapprox_integral
- \+ *lemma* lintegral_add
- \+ *lemma* lintegral_zero
- \- *lemma* bind_itg
- \- *lemma* map_itg
- \- *lemma* seq_itg
- \- *lemma* bind_sum_measure
- \- *lemma* lift₂_is_measurable
- \- *lemma* lift₂_finite
- \+/\- *theorem* mem_range
- \+ *theorem* map_map
- \+ *theorem* coe_map
- \+ *theorem* range_map
- \+/\- *theorem* bind_const
- \+ *theorem* simple_func.lintegral_eq_integral
- \+ *theorem* lintegral_supr
- \- *theorem* map_apply
- \- *theorem* coe_def
- \- *theorem* le_def
- \- *theorem* coe_le_coe
- \- *theorem* indicator.to_fun_val
- \- *theorem* equiv_def
- \- *theorem* equiv_iff
- \- *theorem* le_antisymm
- \- *theorem* le_antisymm_iff
- \- *theorem* coe_add
- \- *theorem* add_congr
- \- *theorem* le_of_multiset_le
- \- *theorem* itg_zero
- \- *theorem* itg_add
- \- *theorem* refined_zero
- \- *theorem* refined_equiv
- \- *theorem* refines.trans
- \- *theorem* preimage_measurable
- \- *theorem* measurable
- \- *theorem* of_fun_val
- \- *theorem* of_fun_apply
- \- *theorem* finite_range
- \- *theorem* lift₂_val
- \- *theorem* sub_val
- \- *theorem* add_sub_cancel_of_le
- \- *theorem* sub_add_cancel_of_le
- \- *theorem* le_iff_exists_add
- \- *theorem* itg'_eq_sum_of_subset
- \- *theorem* itg'_eq_sum
- \- *theorem* itg'_zero
- \- *theorem* itg'_indicator
- \- *theorem* itg'_add
- \- *theorem* itg'_mono
- \- *theorem* itg_mono
- \- *theorem* upper_itg_add_le
- \- *theorem* simple_itg_eq
- \- *theorem* upper_itg_simple
- \+/\- *def* seq
- \+/\- *def* pair
- \+ *def* approx
- \+ *def* ennreal_rat_embed
- \+ *def* eapprox
- \+ *def* integral
- \+ *def* lintegral
- \- *def* itg
- \- *def* indicator.size
- \- *def* indicator.to_fun
- \- *def* simple_func
- \- *def* to_fun
- \- *def* refines
- \- *def* refined
- \- *def* of_fun
- \- *def* lift₂
- \- *def* itg'
- \- *def* upper_itg
- \- *def* upper_itg_def_subtype

Modified analysis/measure_theory/measurable_space.lean
- \+ *lemma* measurable_const

Modified analysis/measure_theory/measure_space.lean
- \+ *lemma* volume_bUnion_finset

Modified data/finset.lean
- \+ *lemma* image_bind_filter_eq
- \+ *lemma* sup_eq_supr
- \+ *lemma* inf_eq_infi

Modified data/real/ennreal.lean
- \+ *lemma* coe_to_nnreal_le_self
- \+ *lemma* coe_nat
- \+ *lemma* mul_inv_cancel
- \+ *lemma* mul_le_if_le_inv
- \+ *lemma* le_of_forall_lt_one_mul_lt
- \+ *lemma* supr_coe_nat

Modified data/real/nnreal.lean
- \+ *lemma* lt_inv_iff_mul_lt
- \+ *lemma* mul_le_if_le_inv
- \+ *lemma* le_of_forall_lt_one_mul_lt

Modified data/set/basic.lean
- \+ *lemma* compl_set_of
- \+ *theorem* exists_range_iff

Modified order/complete_lattice.lean
- \+ *lemma* Inf_eq_bot
- \+ *lemma* supr_eq_bot
- \+ *lemma* supr_eq_top
- \+/\- *lemma* infi_eq_bot

Modified order/filter.lean
- \+ *lemma* tendsto_at_top



## [2018-10-10 22:50:06+02:00](https://github.com/leanprover-community/mathlib/commit/a25e4a8)
feat(analysis/measure_theory/integration): lebesgue integration [WIP]
#### Estimated changes
Modified analysis/measure_theory/borel_space.lean
- \+ *lemma* borel_eq_generate_Iio
- \+ *lemma* borel_eq_generate_Ioi
- \+ *lemma* measurable.is_lub
- \+ *lemma* measurable.is_glb
- \+ *lemma* measurable.supr
- \+ *lemma* measurable.infi

Created analysis/measure_theory/integration.lean
- \+ *lemma* is_measurable_cut
- \+ *lemma* bind_itg
- \+ *lemma* map_itg
- \+ *lemma* seq_itg
- \+ *lemma* bind_sum_measure
- \+ *lemma* lift₂_is_measurable
- \+ *lemma* lift₂_finite
- \+ *theorem* ext
- \+ *theorem* mem_range
- \+ *theorem* const_apply
- \+ *theorem* preimage_measurable
- \+ *theorem* measurable
- \+ *theorem* ite_apply
- \+ *theorem* bind_apply
- \+ *theorem* restrict_apply
- \+ *theorem* restrict_preimage
- \+ *theorem* map_apply
- \+ *theorem* bind_const
- \+ *theorem* coe_def
- \+ *theorem* le_def
- \+ *theorem* coe_le_coe
- \+ *theorem* indicator.to_fun_val
- \+ *theorem* equiv_def
- \+ *theorem* equiv_iff
- \+ *theorem* le_antisymm
- \+ *theorem* le_antisymm_iff
- \+ *theorem* coe_add
- \+ *theorem* add_congr
- \+ *theorem* le_of_multiset_le
- \+ *theorem* itg_zero
- \+ *theorem* itg_add
- \+ *theorem* refined_zero
- \+ *theorem* refined_equiv
- \+ *theorem* refines.trans
- \+ *theorem* of_fun_val
- \+ *theorem* of_fun_apply
- \+ *theorem* finite_range
- \+ *theorem* lift₂_val
- \+ *theorem* sub_val
- \+ *theorem* add_sub_cancel_of_le
- \+ *theorem* sub_add_cancel_of_le
- \+ *theorem* le_iff_exists_add
- \+ *theorem* itg'_eq_sum_of_subset
- \+ *theorem* itg'_eq_sum
- \+ *theorem* itg'_zero
- \+ *theorem* itg'_indicator
- \+ *theorem* itg'_add
- \+ *theorem* itg'_mono
- \+ *theorem* itg_mono
- \+ *theorem* upper_itg_add_le
- \+ *theorem* simple_itg_eq
- \+ *theorem* upper_itg_simple
- \+ *def* itg
- \+ *def* const
- \+ *def* ite
- \+ *def* bind
- \+ *def* restrict
- \+ *def* map
- \+ *def* seq
- \+ *def* pair
- \+ *def* indicator.size
- \+ *def* indicator.to_fun
- \+ *def* simple_func
- \+ *def* to_fun
- \+ *def* refines
- \+ *def* refined
- \+ *def* of_fun
- \+ *def* lift₂
- \+ *def* itg'
- \+ *def* upper_itg
- \+ *def* upper_itg_def_subtype

Modified analysis/measure_theory/lebesgue_measure.lean
- \+ *lemma* real.volume_Ico
- \+ *lemma* real.volume_Icc
- \+ *lemma* real.volume_Ioo
- \+ *lemma* real.volume_singleton
- \- *lemma* lebesgue_Ico
- \- *lemma* lebesgue_Icc
- \- *lemma* lebesgue_Ioo
- \- *lemma* lebesgue_singleton
- \+/\- *theorem* lebesgue_to_outer_measure
- \+ *theorem* real.volume_val
- \+ *theorem* vitali_aux_mem
- \+ *theorem* vitali_aux_rel
- \+ *theorem* vitali_nonmeasurable
- \- *theorem* lebesgue_val
- \+ *def* vitali_aux_h
- \+ *def* vitali_aux
- \+ *def* vitali
- \- *def* lebesgue

Modified analysis/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable.univ
- \+ *lemma* is_measurable.Union_Prop
- \+ *lemma* is_measurable.Inter_Prop
- \+ *lemma* is_measurable.const
- \- *lemma* is_measurable_univ

Modified analysis/measure_theory/measure_space.lean
- \+/\- *lemma* measure_sUnion
- \+ *lemma* volume_empty
- \+ *lemma* volume_mono
- \+ *lemma* volume_mono_null
- \+ *lemma* volume_Union_null
- \+ *lemma* volume_union_null
- \+ *lemma* volume_Union
- \+ *lemma* volume_union
- \+ *lemma* volume_bUnion
- \+ *lemma* volume_sUnion
- \+ *lemma* volume_diff
- \+ *theorem* volume_Union_le
- \+ *theorem* volume_union_le
- \+ *def* a_e
- \+ *def* volume

Modified analysis/topology/topological_space.lean
- \+ *lemma* is_open_Union_countable
- \+/\- *lemma* is_open_sUnion_countable

Modified data/set/basic.lean
- \+ *theorem* image_subset_range
- \+ *theorem* preimage_inter_range
- \+ *theorem* preimage_image_preimage

Modified data/set/finite.lean
- \+/\- *theorem* finite_bUnion

Modified data/set/lattice.lean
- \+ *theorem* bUnion_of_singleton
- \+ *theorem* bUnion_subset_Union
- \+ *theorem* preimage_bUnion

Modified order/bounds.lean
- \+ *lemma* upper_bounds_mono
- \+ *lemma* lower_bounds_mono
- \+ *lemma* is_lub_le_iff
- \+ *lemma* le_is_glb_iff
- \+ *lemma* lt_is_lub_iff
- \+ *lemma* is_glb_lt_iff
- \+/\- *lemma* is_lub_Sup
- \+/\- *lemma* is_glb_Inf

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
- \+/\- *lemma* coe_nat_nonneg

Modified data/list/basic.lean


Modified data/nat/choose.lean




## [2018-10-10 03:03:09-04:00](https://github.com/leanprover-community/mathlib/commit/fedee98)
feat(data/nat/basic): a few choiceless proofs
not sure I can take this much farther without modifying core...
#### Estimated changes
Modified algebra/archimedean.lean


Modified algebra/order.lean
- \+ *lemma* lt_of_le_of_ne'
- \+ *lemma* lt_of_not_ge'
- \+ *lemma* lt_iff_not_ge'
- \+/\- *lemma* not_le
- \+ *lemma* lt_imp_lt_of_le_imp_le
- \+ *lemma* le_imp_le_of_lt_imp_lt
- \+ *lemma* lt_iff_lt_of_le_iff_le'
- \+ *lemma* lt_iff_lt_of_le_iff_le
- \+ *lemma* lt_or_eq_of_le
- \+ *lemma* eq_or_lt_of_le
- \+ *lemma* le_iff_lt_or_eq
- \+ *lemma* le_of_not_lt
- \+ *lemma* not_lt
- \+ *lemma* lt_or_le
- \+ *lemma* le_or_lt
- \+ *lemma* lt_trichotomy
- \+ *lemma* lt_or_gt_of_ne
- \+ *lemma* ne_iff_lt_or_gt
- \+ *lemma* le_imp_le_iff_lt_imp_lt
- \+ *lemma* le_iff_le_iff_lt_iff_lt

Modified algebra/ordered_field.lean


Modified algebra/ordered_ring.lean
- \+ *lemma* decidable.mul_le_mul_left
- \+ *lemma* decidable.mul_le_mul_right

Modified computability/partrec.lean


Modified data/nat/basic.lean
- \+/\- *lemma* succ_le_iff
- \+/\- *theorem* succ_le_succ_iff
- \+/\- *theorem* lt_succ_iff
- \+ *theorem* le_div_iff_mul_le'
- \+ *theorem* div_mul_le_self'
- \+ *theorem* div_lt_iff_lt_mul'

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
- \+/\- *lemma* mem_seq_iff
- \+/\- *lemma* fmap_eq_image
- \+/\- *lemma* seq_eq_set_seq
- \+/\- *lemma* pure_def



## [2018-10-09 22:59:15-04:00](https://github.com/leanprover-community/mathlib/commit/d867240)
feat(data/set/finite): finiteness of set monad ops
#### Estimated changes
Modified data/set/finite.lean
- \+ *theorem* finite_pure
- \+ *theorem* finite_map
- \+ *theorem* finite_bUnion
- \+ *theorem* finite_bind
- \+ *theorem* finite_seq
- \+ *def* fintype_bUnion
- \+ *def* fintype_bind
- \+ *def* fintype_seq



## [2018-10-09 01:14:15-04:00](https://github.com/leanprover-community/mathlib/commit/5c209ed)
fix(linear_algebra/dimension): fix build
#### Estimated changes
Modified algebra/big_operators.lean


Modified linear_algebra/dimension.lean




## [2018-10-08 15:17:51-04:00](https://github.com/leanprover-community/mathlib/commit/2c11641)
refactor(data/polynomial): consistently use coeff not apply ([#409](https://github.com/leanprover-community/mathlib/pull/409))
#### Estimated changes
Modified data/polynomial.lean
- \+ *lemma* apply_eq_coeff
- \+/\- *lemma* coeff_zero
- \+ *lemma* coeff_one_zero
- \+/\- *lemma* coeff_add
- \+/\- *lemma* coeff_C
- \+ *lemma* coeff_C_zero
- \+ *lemma* coeff_X_one
- \+ *lemma* coeff_sum
- \+ *lemma* coeff_single
- \+ *lemma* coeff_C_mul
- \+/\- *lemma* C_inj
- \+/\- *lemma* le_degree_of_ne_zero
- \+/\- *lemma* le_nat_degree_of_ne_zero
- \+/\- *lemma* degree_le_degree
- \+ *lemma* coeff_eq_zero_of_degree_lt
- \+ *lemma* coeff_nat_degree_eq_zero_of_degree_lt
- \+/\- *lemma* eq_C_of_degree_le_zero
- \+ *lemma* coeff_mul_degree_add_degree
- \+/\- *lemma* coeff_is_linear
- \+ *lemma* coeff_neg
- \+ *lemma* coeff_derivative
- \- *lemma* zero_apply
- \- *lemma* one_apply_zero
- \- *lemma* add_apply
- \- *lemma* C_apply
- \- *lemma* C_apply_zero
- \- *lemma* X_apply_one
- \- *lemma* C_mul_apply
- \- *lemma* X_pow_apply
- \- *lemma* coeff_X
- \- *lemma* eq_zero_of_degree_lt
- \- *lemma* apply_nat_degree_eq_zero_of_degree_lt
- \- *lemma* mul_apply_degree_add_degree
- \- *lemma* neg_apply
- \- *lemma* derivative_apply
- \+/\- *theorem* ext
- \+ *def* polynomial.has_coe_to_fun
- \+/\- *def* coeff
- \+/\- *def* leading_coeff



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
- \+/\- *lemma* lcm_dvd_iff
- \+/\- *lemma* dvd_lcm_left
- \+/\- *lemma* dvd_lcm_right

Modified algebra/group_power.lean
- \+/\- *theorem* neg_one_pow_eq_or

Modified algebra/ordered_group.lean
- \+ *lemma* add_eq_zero_iff'
- \- *lemma* add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'

Modified analysis/topology/topological_space.lean
- \+/\- *lemma* is_open_union

Modified data/finset.lean
- \+/\- *lemma* coe_empty
- \+/\- *lemma* coe_singleton
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* card_insert_of_not_mem
- \+/\- *theorem* fold_singleton
- \+/\- *theorem* max_singleton
- \+/\- *theorem* max_singleton'
- \+/\- *theorem* min_empty
- \+/\- *theorem* min_singleton
- \+/\- *theorem* to_finset_card_of_nodup

Modified data/finsupp.lean
- \+/\- *lemma* mem_support_iff
- \+ *lemma* not_mem_support_iff
- \+/\- *lemma* single_apply
- \+/\- *lemma* single_eq_same
- \+/\- *lemma* single_eq_of_ne

Modified data/list/basic.lean
- \+/\- *theorem* forall_mem_nil
- \+/\- *theorem* forall_mem_cons'
- \+/\- *theorem* forall_mem_cons
- \+/\- *theorem* forall_mem_of_forall_mem_cons
- \+/\- *theorem* forall_mem_singleton
- \+/\- *theorem* forall_mem_append
- \+/\- *theorem* not_exists_mem_nil
- \+/\- *theorem* exists_mem_cons_of
- \+/\- *theorem* exists_mem_cons_of_exists
- \+/\- *theorem* or_exists_of_exists_mem_cons
- \+/\- *theorem* exists_mem_cons_iff
- \+/\- *theorem* join_eq_nil
- \+/\- *theorem* take_zero
- \+/\- *theorem* count_singleton
- \+/\- *theorem* option.to_list_nodup

Modified data/nat/basic.lean
- \+ *theorem* succ_inj'

Modified data/polynomial.lean
- \+/\- *lemma* nat_degree_zero

Modified data/set/lattice.lean
- \+ *theorem* sUnion_pair
- \+ *theorem* sInter_pair

Modified order/basic.lean


Modified order/conditionally_complete_lattice.lean
- \+/\- *lemma* bdd_above_subset
- \+/\- *lemma* bdd_below_subset
- \+/\- *lemma* bdd_above_finite

Modified order/filter.lean


Modified set_theory/ordinal.lean
- \+/\- *theorem* mul_le_of_limit



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
- \+/\- *theorem* exists_pos_rat_lt

Modified algebra/big_operators.lean
- \+/\- *lemma* zero_le_sum
- \+/\- *lemma* sum_le_zero
- \+/\- *lemma* zero_le_sum'
- \+/\- *lemma* sum_le_zero'

Modified algebra/char_zero.lean


Modified algebra/euclidean_domain.lean


Modified algebra/field.lean


Modified algebra/field_power.lean


Modified algebra/gcd_domain.lean


Modified algebra/group.lean
- \+/\- *lemma* is_conj_refl

Modified algebra/group_power.lean
- \+/\- *theorem* pow_mul
- \+/\- *theorem* list.prod_repeat
- \+/\- *theorem* mul_pow
- \+/\- *theorem* inv_pow
- \+/\- *theorem* gpow_neg_one
- \+/\- *theorem* neg_one_gsmul
- \+/\- *theorem* add_monoid.smul_eq_mul'
- \+/\- *theorem* neg_one_pow_eq_or
- \+/\- *theorem* one_div_pow

Modified analysis/topology/topological_space.lean
- \+/\- *lemma* is_closed_empty
- \+/\- *lemma* is_closed_univ

Modified analysis/topology/uniform_space.lean


Modified computability/turing_machine.lean


Modified data/complex/basic.lean
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* conj_of_real
- \+/\- *lemma* conj_zero
- \+/\- *lemma* conj_one
- \+/\- *lemma* conj_I
- \+/\- *lemma* conj_neg
- \+/\- *lemma* norm_sq_zero
- \+/\- *lemma* norm_sq_one
- \+/\- *lemma* norm_sq_I

Modified data/finset.lean
- \+/\- *lemma* coe_union
- \+/\- *lemma* coe_inter
- \+/\- *lemma* coe_image
- \+/\- *theorem* not_mem_singleton
- \+/\- *theorem* mem_singleton_self
- \+/\- *theorem* mem_insert_self
- \+/\- *theorem* mem_insert_of_mem
- \+/\- *theorem* mem_union_left
- \+/\- *theorem* mem_union_right
- \+/\- *theorem* union_comm
- \+/\- *theorem* union_idempotent
- \+/\- *theorem* union_right_comm
- \+/\- *theorem* union_self
- \+/\- *theorem* union_empty
- \+/\- *theorem* empty_union
- \+/\- *theorem* insert_eq
- \+/\- *theorem* inter_comm
- \+/\- *theorem* inter_assoc
- \+/\- *theorem* inter_left_comm
- \+/\- *theorem* inter_right_comm
- \+/\- *theorem* inter_self
- \+/\- *theorem* inter_empty
- \+/\- *theorem* empty_inter
- \+/\- *theorem* singleton_inter_of_mem
- \+/\- *theorem* singleton_inter_of_not_mem
- \+/\- *theorem* inter_distrib_left
- \+/\- *theorem* inter_distrib_right
- \+/\- *theorem* union_distrib_left
- \+/\- *theorem* union_distrib_right
- \+/\- *theorem* not_mem_erase
- \+/\- *theorem* ne_of_mem_erase
- \+/\- *theorem* mem_erase_of_ne_of_mem
- \+/\- *theorem* range_succ
- \+/\- *theorem* mem_map
- \+/\- *theorem* map_refl
- \+/\- *theorem* mem_image
- \+/\- *theorem* image_to_finset
- \+/\- *theorem* image_id
- \+/\- *theorem* sigma_mono
- \+/\- *theorem* max_empty

Modified data/finsupp.lean


Modified data/list/basic.lean
- \+/\- *theorem* concat_cons
- \+/\- *theorem* index_of_eq_length
- \+/\- *theorem* take_zero
- \+/\- *theorem* prefix_concat
- \+/\- *theorem* nil_diff

Modified data/polynomial.lean
- \+/\- *lemma* C_0

Modified order/conditionally_complete_lattice.lean


Modified order/filter.lean
- \+/\- *lemma* singleton_mem_pure_sets

Modified order/lattice.lean


Modified set_theory/ordinal.lean
- \+/\- *theorem* lift_type_fin
- \+/\- *theorem* one_lt_omega
- \+/\- *theorem* aleph_zero

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
- \+ *lemma* swap_mul_self
- \+ *lemma* swap_apply_self

Modified data/fintype.lean
- \+ *lemma* finset.prod_attach_univ

Modified group_theory/perm.lean
- \+ *lemma* finset.prod_univ_perm

Created ring_theory/determinant.lean
- \+ *lemma* det_diagonal
- \+ *lemma* det_zero
- \+ *lemma* det_one
- \+ *lemma* det_mul_aux
- \+ *lemma* det_mul



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
- \+ *def* g



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


Created tests/solve_by_elim.lean
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


Created tactic/squeeze.lean




## [2018-10-07 09:09:49-04:00](https://github.com/leanprover-community/mathlib/commit/c1f13c0)
fix(data/int.basic): rename sub_one_le_iff ([#394](https://github.com/leanprover-community/mathlib/pull/394))
#### Estimated changes
Modified data/int/basic.lean
- \+/\- *lemma* dvd_of_pow_dvd
- \+ *theorem* sub_one_lt_iff
- \- *theorem* sub_one_le_iff



## [2018-10-07 09:09:28-04:00](https://github.com/leanprover-community/mathlib/commit/d1e34fd)
fix(algebra/big_operators): remove `comm_monoid` assumption from `sum_nat_cast` ([#401](https://github.com/leanprover-community/mathlib/pull/401))
#### Estimated changes
Modified algebra/big_operators.lean
- \+/\- *lemma* sum_nat_cast



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


Created docs/holes.md




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
- \+ *theorem* subset.antisymm_iff
- \+ *theorem* mem_map'
- \+/\- *theorem* mem_map_of_mem
- \+/\- *theorem* map_subset_map
- \+ *theorem* map_inj
- \+ *theorem* map_embedding_apply
- \+ *def* map_embedding



## [2018-10-05 02:18:56-04:00](https://github.com/leanprover-community/mathlib/commit/74f52f1)
Expand and contract fin ([#387](https://github.com/leanprover-community/mathlib/pull/387))
#### Estimated changes
Modified data/fin.lean
- \+ *def* nat_add
- \+ *def* raise_nat
- \+ *def* lower_left
- \+ *def* lower_right



## [2018-10-04 15:08:19+02:00](https://github.com/leanprover-community/mathlib/commit/9ec21e4)
perf(tactic/scc): produce smaller proofs
#### Estimated changes
Modified data/list/basic.lean
- \+ *theorem* tfae_of_forall

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
- \+ *def* list.mmap_accumr
- \+ *def* list.mmap_accuml

Modified data/list/basic.lean
- \+ *theorem* last'_mem
- \+ *theorem* tfae_nil
- \+ *theorem* tfae_singleton
- \+ *theorem* tfae_cons_of_mem
- \+ *theorem* tfae_cons_cons
- \+ *theorem* tfae_of_cycle
- \+ *theorem* tfae.out
- \+ *def* last'
- \+ *def* tfae

Modified docs/tactics.md


Created tactic/scc.lean


Created tactic/tfae.lean


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
- \+/\- *lemma* interior_compl
- \+/\- *lemma* closure_compl
- \- *lemma* interior_compl_eq
- \- *lemma* closure_compl_eq



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
Created docs/theories/padics.md




## [2018-10-02 14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/1562cc2)
feat(data/padics): use prime typeclass
#### Estimated changes
Created analysis/polynomial.lean
- \+ *lemma* polynomial.continuous_eval

Modified data/padics/hensel.lean
- \+/\- *lemma* padic_polynomial_dist
- \+/\- *lemma* limit_zero_of_norm_tendsto_zero
- \+/\- *lemma* hensels_lemma

Modified data/padics/padic_integers.lean
- \+/\- *lemma* zero_def
- \+/\- *lemma* add_def
- \+/\- *lemma* mul_def
- \+/\- *lemma* mk_zero
- \+/\- *lemma* val_eq_coe
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* cast_pow
- \+/\- *lemma* mk_coe
- \+/\- *lemma* le_one
- \+/\- *lemma* one
- \+/\- *lemma* mul
- \+/\- *lemma* pow
- \+/\- *lemma* norm_one
- \+/\- *lemma* eq_of_norm_add_lt_right
- \+/\- *lemma* eq_of_norm_add_lt_left
- \+/\- *lemma* padic_norm_e_of_padic_int
- \+/\- *lemma* padic_norm_z_eq_padic_norm_e
- \+/\- *lemma* mul_inv
- \+/\- *lemma* inv_mul
- \+/\- *lemma* maximal_ideal_add
- \+/\- *lemma* maximal_ideal_mul
- \+/\- *lemma* maximal_ideal_ne_univ
- \+/\- *lemma* maximal_ideal_eq_nonunits
- \+/\- *lemma* maximal_ideal_eq_or_univ_of_subset
- \+/\- *lemma* maximal_ideal_unique
- \- *lemma* cau_seq_lim_spec
- \- *lemma* tendsto_limit
- \+/\- *theorem* nonarchimedean
- \+/\- *theorem* add_eq_max_of_ne
- \+/\- *def* padic_int
- \+/\- *def* add
- \+/\- *def* mul
- \+/\- *def* neg
- \+/\- *def* inv
- \+/\- *def* padic_norm_z
- \+/\- *def* maximal_ideal
- \- *def* cau_seq_lim

Modified data/padics/padic_norm.lean
- \+/\- *lemma* zero_of_padic_norm_eq_zero
- \+/\- *lemma* add_eq_max_of_ne
- \+/\- *lemma* le_of_dvd
- \+/\- *theorem* triangle_ineq
- \+/\- *def* padic_norm

Modified data/padics/padic_numbers.lean
- \+/\- *lemma* stationary
- \+/\- *lemma* stationary_point_spec
- \+/\- *lemma* norm_zero_iff
- \+/\- *lemma* equiv_zero_of_val_eq_of_equiv_zero
- \+/\- *lemma* norm_nonzero_of_not_equiv_zero
- \+/\- *lemma* norm_eq_norm_app_of_nonzero
- \+/\- *lemma* not_lim_zero_const_of_nonzero
- \+/\- *lemma* not_equiv_zero_const_of_nonzero
- \+/\- *lemma* norm_nonneg
- \+/\- *lemma* lift_index_left_left
- \+/\- *lemma* lift_index_left
- \+/\- *lemma* lift_index_right
- \+/\- *lemma* norm_mul
- \+/\- *lemma* eq_zero_iff_equiv_zero
- \+/\- *lemma* ne_zero_iff_nequiv_zero
- \+/\- *lemma* norm_const
- \+/\- *lemma* norm_image
- \+/\- *lemma* norm_one
- \+/\- *lemma* norm_eq
- \+/\- *lemma* norm_neg
- \+/\- *lemma* norm_eq_of_add_equiv_zero
- \+/\- *lemma* add_eq_max_of_ne
- \+/\- *lemma* mk_eq
- \+/\- *lemma* of_rat_add
- \+/\- *lemma* of_rat_neg
- \+/\- *lemma* of_rat_mul
- \+/\- *lemma* of_rat_sub
- \+/\- *lemma* of_rat_div
- \+/\- *lemma* of_rat_one
- \+/\- *lemma* of_rat_zero
- \+/\- *lemma* cast_eq_of_rat_of_nat
- \+/\- *lemma* cast_eq_of_rat_of_int
- \+/\- *lemma* cast_eq_of_rat
- \+/\- *lemma* const_equiv
- \+/\- *lemma* of_rat_eq
- \+/\- *lemma* defn
- \+/\- *lemma* zero_def
- \+/\- *lemma* zero_iff
- \+/\- *lemma* triangle_ineq
- \+/\- *lemma* eq_padic_norm'
- \+/\- *lemma* sub_rev
- \+/\- *lemma* exi_rat_seq_conv_cauchy
- \+/\- *lemma* eq_padic_norm
- \+/\- *lemma* eq_rat_norm
- \+/\- *lemma* eq_of_norm_add_lt_right
- \+/\- *lemma* eq_of_norm_add_lt_left
- \+/\- *lemma* padic_norm_e_lim_le
- \- *lemma* cau_seq_lim_spec
- \- *lemma* tendsto_limit
- \+/\- *theorem* norm_equiv
- \+/\- *theorem* norm_nonarchimedean
- \+/\- *theorem* nonarchimedean'
- \+/\- *theorem* add_eq_max_of_ne'
- \+/\- *theorem* rat_dense'
- \+/\- *theorem* complete'
- \+/\- *theorem* rat_dense
- \+/\- *theorem* nonarchimedean
- \+/\- *theorem* add_eq_max_of_ne
- \+/\- *theorem* norm_rat_le_one
- \+/\- *def* padic_seq
- \+/\- *def* stationary_point
- \+/\- *def* norm
- \+/\- *def* padic
- \+/\- *def* mk
- \+/\- *def* of_rat
- \+/\- *def* padic_norm_e
- \+/\- *def* rat_norm
- \- *def* cau_seq_lim

Modified data/polynomial.lean
- \- *lemma* continuous_eval

Modified data/real/basic.lean
- \+/\- *lemma* lim_eq_lim_of_equiv
- \+/\- *lemma* lim_const
- \+/\- *lemma* lim_add
- \+/\- *lemma* lim_mul_lim

Modified data/real/cau_seq.lean
- \+ *theorem* lim_zero_sub_rev

Modified data/real/cau_seq_completion.lean
- \+ *lemma* complete
- \+ *lemma* lim_spec

Modified data/real/cau_seq_filter.lean
- \+ *lemma* tendsto_limit
- \+/\- *lemma* set_seq_of_cau_filter_monotone
- \+/\- *lemma* cau_filter_lim_spec
- \+ *lemma* le_nhds_cau_filter_lim
- \- *lemma* cau_seq_lim_spec
- \- *lemma* le_nhds_cau_seq_lim
- \- *theorem* complete_space_of_cauchy_complete



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
- \- *theorem* complete
- \+/\- *def* cau_seq_lim

Modified data/padics/padic_numbers.lean
- \+/\- *lemma* cau_seq_lim_spec
- \+/\- *lemma* padic_norm_e_lim_le
- \+/\- *def* cau_seq_lim

Modified data/real/cau_seq_completion.lean
- \+/\- *lemma* cau_seq_zero_ne_one
- \+/\- *def* Cauchy

Modified data/real/cau_seq_filter.lean
- \+ *lemma* set_seq_of_cau_filter_mem_sets
- \+ *lemma* set_seq_of_cau_filter_inhabited
- \+ *lemma* set_seq_of_cau_filter_spec
- \+ *lemma* mono_of_mono_succ
- \+ *lemma* set_seq_of_cau_filter_monotone'
- \+ *lemma* set_seq_of_cau_filter_monotone
- \+ *lemma* seq_of_cau_filter_mem_set_seq
- \+ *lemma* seq_of_cau_filter_is_cauchy'
- \+ *lemma* is_cau_seq_of_dist_tendsto_0
- \+ *lemma* tendsto_div
- \+ *lemma* seq_of_cau_filter_is_cauchy
- \+ *lemma* cau_seq_of_cau_filter_mem_set_seq
- \+ *lemma* cau_seq_lim_spec
- \+ *lemma* cau_filter_lim_spec
- \+ *lemma* le_nhds_cau_seq_lim
- \+ *theorem* complete_space_of_cauchy_complete
- \+ *theorem* cauchy_complete_of_complete_space
- \+ *def* set_seq_of_cau_filter



## [2018-10-02 14:08:34+02:00](https://github.com/leanprover-community/mathlib/commit/e0b0c53)
feat(data/padics): prove Hensel's lemma
#### Estimated changes
Modified algebra/field_power.lean
- \+ *lemma* fpow_neg
- \+ *lemma* fpow_sub
- \+ *lemma* fpow_pos_of_pos
- \+ *lemma* fpow_le_one_of_nonpos
- \+ *lemma* fpow_ge_one_of_nonneg
- \+ *lemma* one_lt_pow
- \+ *lemma* one_lt_fpow

Modified algebra/group_power.lean
- \+ *lemma* pow_le_pow_of_le_left
- \+ *lemma* pow_lt_pow_of_lt_one
- \+ *lemma* pow_le_pow_of_le_one
- \+ *lemma* neg_square
- \+ *lemma* div_sq_cancel

Modified algebra/ordered_ring.lean
- \+ *lemma* mul_le_iff_le_one_left
- \+ *lemma* mul_lt_iff_lt_one_left
- \+ *lemma* mul_le_iff_le_one_right
- \+ *lemma* mul_lt_iff_lt_one_right

Modified analysis/limits.lean
- \+ *lemma* tendsto_coe_iff
- \+ *lemma* tendsto_pow_at_top_at_top_of_gt_1_nat

Modified analysis/normed_space.lean
- \+ *lemma* norm_pow
- \+/\- *lemma* norm_one
- \+/\- *lemma* norm_div
- \+/\- *lemma* norm_inv
- \+ *lemma* normed_field.norm_pow

Modified analysis/topology/topological_structures.lean
- \+ *lemma* continuous_pow

Modified data/finsupp.lean
- \+ *lemma* sum_sub

Modified data/int/modeq.lean
- \+ *lemma* mod_coprime
- \+ *lemma* exists_unique_equiv
- \+ *lemma* exists_unique_equiv_nat
- \+ *theorem* modeq_add_fac

Modified data/nat/basic.lean
- \+/\- *lemma* dvd_of_pow_dvd
- \+ *lemma* exists_eq_add_of_le
- \+ *lemma* exists_eq_add_of_lt

Created data/padics/default.lean


Created data/padics/hensel.lean
- \+ *lemma* padic_polynomial_dist
- \+ *lemma* limit_zero_of_norm_tendsto_zero
- \+ *lemma* hensels_lemma

Modified data/padics/padic_integers.lean
- \+/\- *lemma* zero_def
- \+/\- *lemma* add_def
- \+/\- *lemma* mul_def
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_one
- \+ *lemma* coe_zero
- \+ *lemma* cast_pow
- \+/\- *lemma* le_one
- \+ *lemma* one
- \+ *lemma* pow
- \+/\- *lemma* norm_one
- \+ *lemma* eq_of_norm_add_lt_right
- \+ *lemma* eq_of_norm_add_lt_left
- \+ *lemma* padic_norm_e_of_padic_int
- \+ *lemma* padic_norm_z_eq_padic_norm_e
- \+/\- *lemma* mul_inv
- \+/\- *lemma* inv_mul
- \+/\- *lemma* maximal_ideal_add
- \+/\- *lemma* maximal_ideal_mul
- \+/\- *lemma* maximal_ideal_ne_univ
- \+ *lemma* cau_seq_lim_spec
- \+ *lemma* tendsto_limit
- \+ *lemma* padic_val_of_cong_pow_p
- \+ *theorem* add_eq_max_of_ne
- \+ *theorem* complete
- \+ *def* cau_seq_lim

Modified data/padics/padic_norm.lean
- \+ *lemma* pow_dvd_of_le_padic_val
- \+ *lemma* pow_dvd_iff_le_padic_val
- \+/\- *lemma* padic_val_eq_zero_of_coprime
- \+ *lemma* padic_val_rat_of_int
- \+ *lemma* le_of_dvd

Renamed data/padics/padic_rationals.lean to data/padics/padic_numbers.lean
- \+ *lemma* lift_index_left_left
- \+ *lemma* lift_index_left
- \+ *lemma* lift_index_right
- \+ *lemma* norm_eq_of_add_equiv_zero
- \+ *lemma* add_eq_max_of_ne
- \+/\- *lemma* defn
- \+ *lemma* eq_of_norm_add_lt_right
- \+ *lemma* eq_of_norm_add_lt_left
- \+ *lemma* cau_seq_lim_spec
- \+ *lemma* padic_norm_e_lim_le
- \+ *lemma* tendsto_limit
- \+/\- *theorem* norm_nonarchimedean
- \+ *theorem* add_eq_max_of_ne'
- \+/\- *theorem* complete'
- \+ *theorem* add_eq_max_of_ne
- \+ *theorem* norm_rat_le_one
- \+ *def* cau_seq_lim

Modified data/polynomial.lean
- \+ *lemma* eval_sum
- \+ *lemma* continuous_eval
- \+ *lemma* derivative_eval
- \+ *def* pow_add_expansion
- \+ *def* binom_expansion
- \+ *def* pow_sub_pow_factor
- \+ *def* eval_sub_factor

Modified data/rat.lean
- \+ *lemma* zero_iff_num_zero
- \+ *lemma* div_num_denom

Modified data/real/cau_seq.lean


Created data/real/cau_seq_filter.lean
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
- \+ *lemma* norm_sub_rev
- \+ *lemma* norm_one
- \+ *lemma* norm_div
- \+ *lemma* norm_inv

Modified data/int/basic.lean
- \+ *lemma* pow_dvd_of_le_of_pow_dvd
- \+ *lemma* dvd_of_pow_dvd
- \- *lemma* pow_div_of_le_of_pow_div_int

Modified data/nat/basic.lean
- \+ *lemma* div_mul_div
- \+ *lemma* pow_dvd_of_le_of_pow_dvd
- \+ *lemma* dvd_of_pow_dvd
- \- *lemma* nat.div_mul_div
- \- *lemma* pow_div_of_le_of_pow_div

Modified data/padics/padic_integers.lean
- \+ *lemma* zero_def
- \+ *lemma* add_def
- \+ *lemma* mul_def
- \+ *lemma* mk_zero
- \+ *lemma* val_eq_coe
- \+ *lemma* coe_add
- \+ *lemma* coe_mul
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *lemma* coe_coe
- \+ *lemma* coe_one
- \+ *lemma* mk_coe
- \+ *lemma* le_one
- \+ *lemma* mul
- \+ *lemma* norm_one
- \+ *lemma* mul_inv
- \+ *lemma* inv_mul
- \+ *lemma* maximal_ideal_add
- \+ *lemma* maximal_ideal_mul
- \+ *lemma* maximal_ideal_ne_univ
- \+ *lemma* maximal_ideal_eq_nonunits
- \+ *lemma* maximal_ideal_eq_or_univ_of_subset
- \+ *lemma* maximal_ideal_unique
- \+ *theorem* nonarchimedean
- \+/\- *def* padic_int
- \+ *def* inv
- \+ *def* padic_norm_z
- \+ *def* maximal_ideal

Modified data/padics/padic_norm.lean
- \+ *lemma* le_padic_val_of_pow_dvd
- \+ *lemma* padic_val_eq_zero_of_not_dvd
- \+ *lemma* padic_val_eq_zero_of_not_dvd'
- \+ *lemma* dvd_of_padic_val_pos
- \+ *lemma* padic_val_eq_zero_of_coprime
- \- *lemma* le_padic_val_of_pow_div
- \+/\- *theorem* triangle_ineq

Modified data/padics/padic_rationals.lean
- \+/\- *lemma* norm_mul
- \+ *lemma* triangle_ineq
- \+ *lemma* eq_padic_norm'
- \+/\- *lemma* eq_padic_norm
- \+ *lemma* eq_rat_norm
- \+/\- *theorem* norm_equiv
- \+ *theorem* nonarchimedean'
- \+ *theorem* rat_dense'
- \+ *theorem* complete'
- \+/\- *theorem* rat_dense
- \+/\- *theorem* nonarchimedean
- \- *theorem* complete
- \+/\- *def* padic
- \+/\- *def* lim_seq
- \+ *def* rat_norm



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
- \+ *lemma* leading_coeff_eq_zero_iff_deg_eq_bot

Modified ring_theory/noetherian.lean
- \+ *theorem* ring.is_noetherian_of_fintype
- \+ *theorem* ring.is_noetherian_of_zero_eq_one



## [2018-10-02 11:34:24+02:00](https://github.com/leanprover-community/mathlib/commit/44b55e6)
feat(category_theory/groupoid): groupoids
#### Estimated changes
Created category_theory/groupoid.lean




## [2018-10-02 11:34:04+02:00](https://github.com/leanprover-community/mathlib/commit/efa9459)
feat(category_theory/whiskering): whiskering nat_trans by functors ([#360](https://github.com/leanprover-community/mathlib/pull/360))
* feat(category_theory/whiskering): whiskering nat_trans by functors
* simplify whiskering
#### Estimated changes
Created category_theory/whiskering.lean
- \+ *lemma* whisker_left.app
- \+ *lemma* whisker_right.app
- \+ *lemma* whisker_left_vcomp
- \+ *lemma* whisker_right_vcomp
- \+ *lemma* whisker_left_twice
- \+ *lemma* whisker_right_twice
- \+ *lemma* whisker_right_left
- \+ *def* whiskering_left
- \+ *def* whiskering_right
- \+ *def* whisker_left
- \+ *def* whisker_right



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
- \+/\- *lemma* prod_image
- \+/\- *lemma* prod_const
- \+ *lemma* prod_pow
- \+ *lemma* prod_nat_pow
- \+ *lemma* prod_involution
- \+ *lemma* sum_smul
- \+/\- *lemma* sum_const
- \+ *lemma* card_bind
- \+ *lemma* card_bind_le
- \+ *lemma* prod_range_id_eq_fact

Modified algebra/field.lean
- \+ *lemma* units.mk0_inj

Modified algebra/field_power.lean


Modified algebra/group.lean
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_inv
- \- *lemma* mul_coe
- \- *lemma* one_coe
- \- *lemma* inv_coe

Modified algebra/group_power.lean
- \+ *lemma* units.coe_pow
- \+ *lemma* neg_one_pow_eq_pow_mod_two

Modified algebra/ordered_ring.lean
- \+ *lemma* one_lt_mul

Modified algebra/pi_instances.lean
- \+ *lemma* prod_mk_prod

Modified algebra/ring.lean
- \+ *lemma* units.coe_ne_zero

Modified data/finset.lean
- \+ *lemma* card_congr
- \+ *lemma* card_union_add_card_inter
- \+ *lemma* card_union_le
- \+ *lemma* surj_on_of_inj_on_of_card_le
- \+/\- *theorem* card_range
- \+/\- *theorem* card_attach
- \+/\- *theorem* fold_image

Modified data/int/modeq.lean
- \+ *lemma* modeq_and_modeq_iff_modeq_mul
- \+ *lemma* gcd_a_modeq
- \+ *lemma* mod_mul_right_mod
- \+ *lemma* mod_mul_left_mod
- \+ *theorem* mod_modeq
- \+ *theorem* modeq_of_modeq_mul_left
- \+ *theorem* modeq_of_modeq_mul_right

Modified data/nat/basic.lean
- \+ *lemma* pred_eq_sub_one
- \+ *lemma* two_mul_odd_div_two
- \+ *lemma* div_dvd_of_dvd
- \+ *lemma* mod_mul_right_div_self
- \+ *lemma* mod_mul_left_div_self
- \+ *lemma* succ_le_iff

Modified data/nat/gcd.lean
- \+ *lemma* coprime_mul_iff_left
- \+ *lemma* coprime_mul_iff_right
- \+ *lemma* coprime.mul_dvd_of_dvd_of_dvd

Modified data/nat/modeq.lean
- \+ *lemma* modeq_and_modeq_iff_modeq_mul
- \+ *lemma* coprime_of_mul_modeq_one
- \+ *lemma* mod_mul_right_mod
- \+ *lemma* mod_mul_left_mod
- \+ *lemma* odd_mul_odd
- \+ *lemma* odd_mul_odd_div_two
- \+ *lemma* odd_of_mod_four_eq_one
- \+ *lemma* odd_of_mod_four_eq_three
- \+ *theorem* modeq_of_modeq_mul_left
- \+ *theorem* modeq_of_modeq_mul_right
- \- *theorem* chinese_remainder
- \+ *def* chinese_remainder

Modified data/nat/prime.lean
- \+ *lemma* prime.eq_two_or_odd

Created data/nat/totient.lean
- \+ *lemma* totient_le
- \+ *lemma* totient_pos
- \+ *lemma* sum_totient
- \+ *def* totient

Modified data/quot.lean
- \+/\- *theorem* mk_out'

Modified data/set/basic.lean


Modified data/set/finite.lean
- \+ *lemma* card_le_of_subset
- \+ *lemma* eq_of_subset_of_card_le

Renamed data/zmod.lean to data/zmod/basic.lean
- \+ *lemma* coe_val_cast_int
- \+ *lemma* eq_zero_iff_dvd_nat
- \+ *lemma* eq_zero_iff_dvd_int
- \+ *lemma* le_div_two_iff_lt_neg
- \+ *lemma* ne_neg_self
- \+ *lemma* cast_mul_right_val_cast
- \+ *lemma* cast_mul_left_val_cast
- \+ *lemma* cast_val_cast_of_dvd
- \+ *lemma* card_zmodp
- \+ *lemma* prime_ne_zero
- \- *lemma* gcd_a_modeq
- \+ *def* units_equiv_coprime

Created data/zmod/quadratic_reciprocity.lean
- \+ *lemma* card_units_zmodp
- \+ *lemma* euler_criterion_units
- \+ *lemma* euler_criterion
- \+ *lemma* pow_div_two_eq_neg_one_or_one
- \+ *lemma* wilsons_lemma
- \+ *lemma* prod_range_prime_erase_zero
- \+ *lemma* filter_range_p_mul_q_div_two_eq
- \+ *lemma* prod_filter_range_p_mul_q_div_two_eq
- \+ *lemma* prod_filter_range_p_mul_q_div_two_mod_p_eq
- \+ *lemma* prod_filter_range_p_mul_q_not_coprime_eq
- \+ *lemma* prod_range_p_mul_q_filter_coprime_mod_p
- \+ *lemma* card_range_p_mul_q_filter_not_coprime
- \+ *lemma* prod_filter_range_p_mul_q_div_two_eq_prod_product
- \+ *lemma* prod_range_div_two_erase_zero
- \+ *lemma* range_p_product_range_q_div_two_prod
- \+ *lemma* prod_range_p_mul_q_div_two_ite_eq
- \+ *lemma* legendre_sym_eq_pow
- \+ *lemma* legendre_sym_eq_one_or_neg_one
- \+ *lemma* is_square_iff_is_square_of_mod_four_eq_one
- \+ *lemma* is_square_iff_is_not_square_of_mod_four_eq_three
- \+ *theorem* fermat_little
- \+ *theorem* quadratic_reciprocity
- \+ *def* legendre_sym

Created field_theory/finite.lean
- \+ *lemma* order_of_pow
- \+ *lemma* coe_units_equiv_ne_zero
- \+ *lemma* card_units
- \+ *lemma* card_nth_roots_units
- \+ *lemma* card_pow_eq_one_eq_order_of
- \+ *lemma* card_order_of_eq_totient
- \+ *lemma* prod_univ_units_id_eq_neg_one
- \+ *def* units_equiv_ne_zero

Modified group_theory/order_of_element.lean
- \+ *lemma* order_of_dvd_of_pow_eq_one
- \+ *lemma* order_of_le_of_pow_eq_one
- \+ *lemma* sum_card_order_of_eq_card_pow_eq_one
- \+ *lemma* pow_card_eq_one
- \+ *lemma* powers_eq_gpowers
- \+ *lemma* is_cyclic_of_order_of_eq_card
- \+ *lemma* order_of_eq_card_of_forall_mem_gppowers

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
- \+ *lemma* coeff_zero
- \+ *lemma* coeff_C_mul_X
- \+ *lemma* coeff_C
- \+ *lemma* coeff_one
- \+ *lemma* coeff_X_pow
- \+ *lemma* coeff_X
- \+ *lemma* coeff_add
- \+ *lemma* coeff_mul_left
- \+ *lemma* coeff_mul_right
- \+ *lemma* coeff_smul
- \+ *lemma* C_mul'
- \+ *lemma* coeff_is_linear
- \+ *theorem* ext
- \+ *theorem* coeff_mul_X_pow
- \+ *theorem* coeff_mul_X
- \+ *theorem* mul_X_pow_eq_zero
- \+ *def* coeff



## [2018-10-01 20:19:59+02:00](https://github.com/leanprover-community/mathlib/commit/282754c)
fix(tactic/linarith): symmetric case
#### Estimated changes
Modified tactic/linarith.lean
- \+ *lemma* int.coe_nat_mul_bit0
- \+ *lemma* int.coe_nat_mul_bit1
- \+ *lemma* int.coe_nat_mul_one
- \+ *lemma* int.coe_nat_mul_zero



## [2018-10-01 20:19:59+02:00](https://github.com/leanprover-community/mathlib/commit/31ef46a)
feat(tactic/linarith): don't reject nonlinear hypotheses
#### Estimated changes
Modified tactic/linarith.lean
- \+ *lemma* int.coe_nat_bit0_mul
- \+ *lemma* int.coe_nat_bit1_mul
- \+ *lemma* int.coe_nat_one_mul
- \+ *lemma* int.coe_nat_zero_mul

Modified tests/linarith.lean




## [2018-10-01 18:10:17+02:00](https://github.com/leanprover-community/mathlib/commit/4ba7f23)
cleanup(data/holor)
#### Estimated changes
Modified data/holor.lean
- \+/\- *lemma* cast_type
- \+/\- *def* holor_index
- \+/\- *def* holor

Modified data/list/basic.lean
- \+/\- *theorem* drop_drop



## [2018-10-01 14:51:42+02:00](https://github.com/leanprover-community/mathlib/commit/7c361fa)
feat(data/holor): holor library
#### Estimated changes
Created data/holor.lean
- \+ *lemma* cast_type
- \+ *lemma* take_take
- \+ *lemma* drop_take
- \+ *lemma* drop_drop
- \+ *lemma* mul_assoc0
- \+ *lemma* mul_assoc
- \+ *lemma* mul_left_distrib
- \+ *lemma* mul_right_distrib
- \+ *lemma* zero_mul
- \+ *lemma* mul_zero
- \+ *lemma* mul_scalar_mul
- \+ *lemma* holor_index_cons_decomp
- \+ *lemma* slice_eq
- \+ *lemma* slice_unit_vec_mul
- \+ *lemma* slice_add
- \+ *lemma* slice_zero
- \+ *lemma* slice_sum
- \+ *lemma* sum_unit_vec_mul_slice
- \+ *lemma* cprank_max_nil
- \+ *lemma* cprank_max_1
- \+ *lemma* cprank_max_add
- \+ *lemma* cprank_max_mul
- \+ *lemma* cprank_max_sum
- \+ *lemma* cprank_max_upper_bound
- \+ *lemma* cprank_upper_bound
- \+ *def* holor_index
- \+ *def* take
- \+ *def* drop
- \+ *def* assoc_right
- \+ *def* assoc_left
- \+ *def* holor
- \+ *def* mul
- \+ *def* slice
- \+ *def* unit_vec

Modified data/list/basic.lean
- \+ *theorem* drop_drop
- \+ *theorem* drop_take
- \+ *theorem* forall₂_take
- \+ *theorem* forall₂_drop
- \+ *theorem* forall₂_take_append
- \+ *theorem* forall₂_drop_append



## [2018-10-01 14:40:27+02:00](https://github.com/leanprover-community/mathlib/commit/b66614d)
refactor(analysis/topology): renamed compact_open to continuous_map; moved locally_compact to a more general position
#### Estimated changes
Modified analysis/topology/continuity.lean
- \+ *lemma* locally_compact_of_compact_nhds
- \+ *lemma* locally_compact_of_compact

Renamed analysis/topology/compact_open.lean to analysis/topology/continuous_map.lean
- \- *lemma* locally_compact_of_compact_nhds
- \- *lemma* locally_compact_of_compact
- \+ *def* continuous_map
- \+ *def* compact_open.gen
- \+ *def* induced
- \+/\- *def* ev
- \+/\- *def* coev
- \- *def* compact_open_gen
- \- *def* compact_open
- \- *def* continuous_map.induced

