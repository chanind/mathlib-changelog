## [2019-02-28 20:55:23](https://github.com/leanprover-community/mathlib/commit/05449a0)
refactor(ring_theory/localization): rename of to mk, and define of ([#765](https://github.com/leanprover-community/mathlib/pull/765))
* refactor(ring_theory/localization): rename of to mk, and define of
* Make submonoid implicit variable of 'of'
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+ *lemma* localization.coe_mul_mk
- \- *lemma* localization.coe_mul_of
- \+ *lemma* localization.eq_zero_of
- \+ *def* localization.mk
- \+ *lemma* localization.mk_eq_div
- \+ *lemma* localization.mk_eq_mul_mk_one
- \+ *lemma* localization.mk_mul_cancel_left
- \+ *lemma* localization.mk_mul_cancel_right
- \+ *lemma* localization.mk_mul_mk
- \+ *lemma* localization.mk_self''
- \+ *lemma* localization.mk_self'
- \+ *lemma* localization.mk_self
- \+ *lemma* localization.of.injective
- \+/\- *def* localization.of
- \+/\- *lemma* localization.of_add
- \- *lemma* localization.of_eq_div
- \- *lemma* localization.of_eq_mul_of_one
- \+/\- *lemma* localization.of_mul
- \- *lemma* localization.of_mul_cancel_left
- \- *lemma* localization.of_mul_cancel_right
- \- *lemma* localization.of_mul_of
- \+/\- *lemma* localization.of_neg
- \+/\- *lemma* localization.of_one
- \+/\- *lemma* localization.of_pow
- \- *lemma* localization.of_self''
- \- *lemma* localization.of_self'
- \- *lemma* localization.of_self
- \+/\- *lemma* localization.of_sub
- \+/\- *lemma* localization.of_zero



## [2019-02-28 19:14:55](https://github.com/leanprover-community/mathlib/commit/eb033cf)
feat(ring_theory/ideals): make ideal.quotient.field a discrete_field ([#777](https://github.com/leanprover-community/mathlib/pull/777))
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/ideals.lean




## [2019-02-28 17:20:01](https://github.com/leanprover-community/mathlib/commit/e6a3ca8)
refactor(algebra/group): generalise and extend the API for with_zero ([#762](https://github.com/leanprover-community/mathlib/pull/762))
* refactor(algebra/group): generalise and extend the API for with_zero
* Shorter proof. Thanks Chris
* Travis, try your best
#### Estimated changes
Modified src/algebra/group.lean
- \+ *lemma* with_one.coe_inj
- \+ *lemma* with_one.coe_ne_one
- \+ *lemma* with_one.mul_coe
- \+ *lemma* with_one.ne_one_iff_exists
- \+ *lemma* with_one.one_ne_coe
- \+ *lemma* with_zero.coe_one
- \+ *lemma* with_zero.div_coe
- \+ *lemma* with_zero.div_eq_div
- \+ *lemma* with_zero.div_eq_iff_mul_eq
- \+ *lemma* with_zero.div_mul_cancel
- \+ *lemma* with_zero.div_one
- \+ *lemma* with_zero.div_zero
- \+ *lemma* with_zero.inv_coe
- \+ *lemma* with_zero.inv_one
- \+ *lemma* with_zero.inv_zero
- \+ *lemma* with_zero.mul_coe
- \+ *lemma* with_zero.mul_div_cancel
- \+ *lemma* with_zero.mul_inv_rev
- \+ *lemma* with_zero.mul_left_inv
- \+ *lemma* with_zero.mul_right_inv
- \+ *lemma* with_zero.one_div
- \+ *lemma* with_zero.zero_div



## [2019-02-28 16:55:44](https://github.com/leanprover-community/mathlib/commit/781d187)
feat(group_theory/quotient_group): define ker_lift and prove simp-lemmas ([#764](https://github.com/leanprover-community/mathlib/pull/764))
* feat(group_theory/quotient_group): define ker_lift and prove simp-lemmas
* Add docstring
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+/\- *lemma* quotient_group.injective_ker_lift
- \+ *def* quotient_group.ker_lift
- \+ *lemma* quotient_group.ker_lift_mk'
- \+ *lemma* quotient_group.ker_lift_mk



## [2019-02-28 11:09:35+01:00](https://github.com/leanprover-community/mathlib/commit/81f8530)
fix(tactic/linarith): typo
#### Estimated changes
Modified src/tactic/linarith.lean




## [2019-02-28 10:33:40+01:00](https://github.com/leanprover-community/mathlib/commit/08d4d17)
feat(topology/basic): Add instances for subset/inter/union for opens(X) ([#763](https://github.com/leanprover-community/mathlib/pull/763))
* feat(topology/basic): Add instances for subset/inter/union for opens(X)
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* topological_space.opens.empty_eq
- \+ *lemma* topological_space.opens.inter_eq
- \+ *lemma* topological_space.opens.union_eq



## [2019-02-27 23:53:37+01:00](https://github.com/leanprover-community/mathlib/commit/477338d)
refactor(data/subtype): organise in namespaces, use variables, add two simp-lemmas ([#760](https://github.com/leanprover-community/mathlib/pull/760))
#### Estimated changes
Modified src/data/subtype.lean
- \+/\- *theorem* subtype.coe_eta
- \+/\- *lemma* subtype.coe_ext
- \+/\- *theorem* subtype.coe_mk
- \+/\- *theorem* subtype.exists
- \+/\- *lemma* subtype.ext
- \+/\- *theorem* subtype.forall
- \+/\- *theorem* subtype.mk_eq_mk
- \+/\- *theorem* subtype.val_injective
- \+ *lemma* subtype.val_prop'
- \+ *lemma* subtype.val_prop



## [2019-02-27 22:46:52](https://github.com/leanprover-community/mathlib/commit/af2cf74)
feat(group_theory/quotient_group): map is a group hom ([#761](https://github.com/leanprover-community/mathlib/pull/761))
#### Estimated changes
Modified src/group_theory/quotient_group.lean




## [2019-02-27 22:37:11](https://github.com/leanprover-community/mathlib/commit/dfa855c)
feat(data/finset) remove unnecessary assumption from card_eq_succ ([#772](https://github.com/leanprover-community/mathlib/pull/772))
#### Estimated changes
Modified src/data/finset.lean
- \+/\- *lemma* finset.card_eq_succ



## [2019-02-27 23:14:03+01:00](https://github.com/leanprover-community/mathlib/commit/cfde449)
fix(doc/tactics): linarith doc is outdated [ci-skip]
#### Estimated changes
Modified docs/tactics.md




## [2019-02-27 21:33:02+01:00](https://github.com/leanprover-community/mathlib/commit/6c71ac0)
fix(tactic/linarith): fix bug in strengthening of strict nat/int inequalities
#### Estimated changes
Modified src/tactic/linarith.lean


Modified test/linarith.lean




## [2019-02-27 15:25:19](https://github.com/leanprover-community/mathlib/commit/4667d2c)
feat(ring_theory/ideal_operations): ideals form a commutative semiring ([#771](https://github.com/leanprover-community/mathlib/pull/771))
#### Estimated changes
Modified src/ring_theory/ideal_operations.lean




## [2019-02-27 14:06:24](https://github.com/leanprover-community/mathlib/commit/05d1d33)
fix(algebra/archimedean): swap names of floor_add_fract and fract_add_floor ([#770](https://github.com/leanprover-community/mathlib/pull/770))
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+/\- *lemma* floor_add_fract
- \+/\- *lemma* fract_add_floor



## [2019-02-27 12:02:24+01:00](https://github.com/leanprover-community/mathlib/commit/42d1ed7)
feat(linarith): improve handling of strict inequalities in nat and int ([#769](https://github.com/leanprover-community/mathlib/pull/769))
* feat(linarith): perform slightly better on ℕ and ℤ by strengthening t < 0 hyps to t + 1 ≤ 0
* remove already completed TODO item
#### Estimated changes
Modified src/tactic/linarith.lean


Modified test/linarith.lean




## [2019-02-26 22:04:45+01:00](https://github.com/leanprover-community/mathlib/commit/3f47739)
fix(docs/howto-contribute): main repository has moved
#### Estimated changes
Modified docs/howto-contribute.md




## [2019-02-26 12:57:23-05:00](https://github.com/leanprover-community/mathlib/commit/7450cc5)
fix(scripts/update_mathlib): improve python style and error handling ([#759](https://github.com/leanprover-community/mathlib/pull/759))
#### Estimated changes
Modified scripts/update-mathlib.py




## [2019-02-25 16:20:56-05:00](https://github.com/leanprover-community/mathlib/commit/71a7e1c)
fix(scripts/update-mathlib): cached archived were never expanded
#### Estimated changes
Modified scripts/update-mathlib.py




## [2019-02-25 16:01:35-05:00](https://github.com/leanprover-community/mathlib/commit/4222483)
fix(scripts/update-mathlib): fix the commit check
#### Estimated changes
Modified scripts/update-mathlib.py




## [2019-02-24 23:52:02-05:00](https://github.com/leanprover-community/mathlib/commit/e23553a)
doc(nat/decidable_prime): add docstrings explaining the two decidable_prime instances ([#757](https://github.com/leanprover-community/mathlib/pull/757))
#### Estimated changes
Modified docs/theories/naturals.md


Modified src/data/nat/prime.lean




## [2019-02-24 15:36:34](https://github.com/leanprover-community/mathlib/commit/f922086)
feat(ring_theory/polynomial): more operations on polynomials ([#679](https://github.com/leanprover-community/mathlib/pull/679))
#### Estimated changes
Modified src/ring_theory/polynomial.lean
- \+ *theorem* is_noetherian_ring_mv_polynomial_fin
- \+ *theorem* is_noetherian_ring_mv_polynomial_of_fintype
- \+ *theorem* polynomial.coeff_restriction'
- \+ *theorem* polynomial.coeff_restriction
- \+ *theorem* polynomial.coeff_to_subring'
- \+ *theorem* polynomial.coeff_to_subring
- \+ *theorem* polynomial.degree_restriction
- \+ *theorem* polynomial.degree_to_subring
- \+ *theorem* polynomial.eval₂_restriction
- \+ *theorem* polynomial.frange_of_subring
- \+ *theorem* polynomial.monic_restriction
- \+ *theorem* polynomial.monic_to_subring
- \+ *theorem* polynomial.nat_degree_restriction
- \+ *theorem* polynomial.nat_degree_to_subring
- \+ *def* polynomial.of_subring
- \+ *def* polynomial.restriction
- \+ *theorem* polynomial.restriction_one
- \+ *theorem* polynomial.restriction_zero
- \+ *def* polynomial.to_subring
- \+ *theorem* polynomial.to_subring_one
- \+ *theorem* polynomial.to_subring_zero



## [2019-02-24 11:59:27](https://github.com/leanprover-community/mathlib/commit/c9b2d0e)
chore(linear_algebra/multivariate_polynomial): remove unnecessary decidable_eq assumption ([#755](https://github.com/leanprover-community/mathlib/pull/755))
#### Estimated changes
Modified src/linear_algebra/multivariate_polynomial.lean




## [2019-02-23 11:37:37](https://github.com/leanprover-community/mathlib/commit/ddc016c)
feat(*): polar co-ordinates, de moivre, trig identities, quotient group for angles ([#745](https://github.com/leanprover-community/mathlib/pull/745))
* feat(algebra/group_power): re-PRing polar co-ords
* Update group_power.lean
* feat(analysis/exponential): re-PRing polar stuff
* feat(data.complex.exponential): re-PR polar stuff
* fix(analysis.exponential): stylistic
* fix(data.complex.exponential): stylistic
* fix(analysis/exponential.lean): angle_eq_iff_two_pi_dvd_sub
* fix(analysis/exponential): angle_eq_iff_two_pi_dvd_sub
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *theorem* pow_lt_pow_of_lt_left
- \+ *theorem* pow_right_inj

Modified src/analysis/exponential.lean
- \+ *def* real.angle.angle
- \+ *lemma* real.angle.angle_eq_iff_two_pi_dvd_sub
- \+ *lemma* real.angle.coe_add
- \+ *lemma* real.angle.coe_gsmul
- \+ *lemma* real.angle.coe_neg
- \+ *lemma* real.angle.coe_sub
- \+ *lemma* real.angle.coe_two_pi
- \+ *lemma* real.angle.coe_zero
- \+ *theorem* real.angle.cos_eq_iff_eq_or_eq_neg
- \+ *theorem* real.angle.cos_sin_inj
- \+ *theorem* real.angle.sin_eq_iff_eq_or_add_eq_pi
- \+ *theorem* real.cos_eq_zero_iff
- \+ *theorem* real.cos_sub_cos
- \+ *theorem* real.sin_sub_sin

Modified src/data/complex/exponential.lean
- \+ *theorem* complex.cos_add_sin_mul_I_pow
- \+ *lemma* complex.exp_nat_mul
- \+ *lemma* real.exp_nat_mul



## [2019-02-23 00:41:40](https://github.com/leanprover-community/mathlib/commit/63fa61d)
fix(analysis/specific_limits): remove useless assumption ([#751](https://github.com/leanprover-community/mathlib/pull/751))
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+/\- *lemma* has_sum_of_absolute_convergence_real



## [2019-02-21 21:35:05](https://github.com/leanprover-community/mathlib/commit/e739cf5)
feat(order_dual): instances for order_dual and shortening proofs ([#746](https://github.com/leanprover-community/mathlib/pull/746))
* feat(order_bot): instances for order_bot and shortening proofs
* fix(topological_structure); remove unused import
#### Estimated changes
Modified src/order/basic.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/topology/algebra/topological_structures.lean
- \+/\- *theorem* Liminf_nhds
- \+/\- *theorem* Limsup_eq_of_le_nhds
- \+/\- *lemma* exists_forall_ge_of_compact_of_continuous
- \+/\- *theorem* gt_mem_sets_of_Liminf_gt
- \+/\- *lemma* is_glb_of_is_lub_of_tendsto
- \+/\- *lemma* is_glb_of_mem_nhds
- \+ *lemma* is_lub_of_is_glb_of_tendsto
- \+/\- *lemma* nhds_principal_ne_bot_of_is_glb



## [2019-02-21 16:24:47](https://github.com/leanprover-community/mathlib/commit/3c3a052)
feat(field_theory/subfield): closure of subset in field ([#742](https://github.com/leanprover-community/mathlib/pull/742))
#### Estimated changes
Modified src/field_theory/subfield.lean
- \+ *def* field.closure
- \+ *theorem* field.closure_mono
- \+ *theorem* field.closure_subset
- \+ *theorem* field.closure_subset_iff
- \+ *theorem* field.mem_closure
- \+ *theorem* field.ring_closure_subset
- \+ *theorem* field.subset_closure



## [2019-02-20 18:08:04-05:00](https://github.com/leanprover-community/mathlib/commit/9656485)
feat(data/finmap): lift_on₂ ([#716](https://github.com/leanprover-community/mathlib/pull/716))
* feat(data/finmap): define lift_on₂ with lift_on
#### Estimated changes
Modified src/data/finmap.lean
- \+ *def* finmap.lift_on₂
- \+ *theorem* finmap.lift_on₂_to_finmap



## [2019-02-20 17:32:07](https://github.com/leanprover-community/mathlib/commit/8b8ae32)
fix(order/basic): give order_dual the correct lt ([#741](https://github.com/leanprover-community/mathlib/pull/741))
#### Estimated changes
Modified src/order/basic.lean




## [2019-02-20 12:33:02](https://github.com/leanprover-community/mathlib/commit/c7202e5)
feat(analysis/exponential): pow_nat_rpow_nat_inv ([#740](https://github.com/leanprover-community/mathlib/pull/740))
#### Estimated changes
Modified src/analysis/exponential.lean
- \+ *lemma* complex.abs_cpow_inv_nat
- \+ *lemma* real.pow_nat_rpow_nat_inv



## [2019-02-18 18:07:10](https://github.com/leanprover-community/mathlib/commit/78ce6e4)
feat(data/fintype): fintype.of_injective
#### Estimated changes
Modified src/data/fintype.lean




## [2019-02-18 09:48:21-05:00](https://github.com/leanprover-community/mathlib/commit/9a2c13a)
feat(data/alist,data/finmap): always insert key-value pair ([#722](https://github.com/leanprover-community/mathlib/pull/722))
* Change {alist,finmap}.insert to always insert the key-value pair
  instead of doing nothing if the inserted key is found. This allows for
  useful theorems such as lookup_insert.
* Add list.keys and used key membership instead of exists/forall. This
  makes proofs easier in some places.
* Add a few other useful theorems such as lookup_eq_none,
  lookup_erase, lookup_erase_ne.
#### Estimated changes
Modified src/data/finmap.lean
- \- *theorem* finmap.insert_of_pos
- \+ *theorem* finmap.lookup_eq_none
- \+ *theorem* finmap.lookup_erase
- \+ *theorem* finmap.lookup_erase_ne
- \+ *theorem* finmap.lookup_insert
- \- *theorem* finmap.not_mem_empty_entries
- \+ *theorem* multiset.coe_keys
- \+ *def* multiset.keys

Modified src/data/list/alist.lean
- \+ *theorem* alist.insert_entries
- \+/\- *theorem* alist.insert_entries_of_neg
- \- *theorem* alist.insert_of_pos
- \+/\- *def* alist.keys
- \+/\- *theorem* alist.keys_insert
- \+ *theorem* alist.lookup_eq_none
- \+ *theorem* alist.lookup_erase
- \+ *theorem* alist.lookup_erase_ne
- \+ *theorem* alist.lookup_insert
- \+ *theorem* alist.lookup_insert_ne
- \- *theorem* alist.mem_def
- \+/\- *theorem* alist.mem_insert
- \+/\- *theorem* alist.mem_keys
- \+/\- *theorem* alist.not_mem_empty
- \- *theorem* alist.not_mem_empty_entries
- \+/\- *theorem* alist.perm_insert

Modified src/data/list/sigma.lean
- \+ *theorem* list.exists_of_kerase
- \+ *theorem* list.exists_of_mem_keys
- \+ *theorem* list.kerase_cons_eq
- \+ *theorem* list.kerase_cons_ne
- \+ *theorem* list.kerase_keys_subset
- \- *theorem* list.kerase_map_fst
- \+ *theorem* list.kerase_nil
- \+ *theorem* list.kerase_of_not_mem_keys
- \+ *def* list.keys
- \+ *theorem* list.keys_cons
- \+ *theorem* list.keys_kerase
- \+ *theorem* list.keys_kreplace
- \+ *theorem* list.keys_nil
- \+ *def* list.kinsert
- \+ *theorem* list.kinsert_def
- \+ *theorem* list.kinsert_nodupkeys
- \- *theorem* list.kreplace_map_fst
- \+ *theorem* list.lookup_kerase
- \+ *theorem* list.lookup_kerase_ne
- \+ *theorem* list.lookup_kinsert
- \+ *theorem* list.lookup_kinsert_ne
- \+ *theorem* list.mem_keys
- \+ *theorem* list.mem_keys_kerase_of_ne
- \+ *theorem* list.mem_keys_kinsert
- \+ *theorem* list.mem_keys_of_mem
- \+ *theorem* list.mem_keys_of_mem_keys_kerase
- \+ *theorem* list.mem_lookup
- \+/\- *theorem* list.nodupkeys_cons
- \+ *theorem* list.not_eq_key
- \+ *theorem* list.not_mem_keys
- \+ *theorem* list.not_mem_keys_kerase
- \+ *theorem* list.perm_kinsert



## [2019-02-18 09:45:57](https://github.com/leanprover-community/mathlib/commit/6b4435b)
feat(data/polynomial): create nonzero_comm_semiring and generalize nonzero_comm_ring lemmas ([#736](https://github.com/leanprover-community/mathlib/pull/736))
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *def* nonzero_comm_semiring.of_ne
- \+/\- *lemma* units.coe_ne_zero

Modified src/data/polynomial.lean




## [2019-02-16 21:24:09](https://github.com/leanprover-community/mathlib/commit/c64b67e)
feat(ring_theory/localization): revamp, ideal embedding ([#481](https://github.com/leanprover-community/mathlib/pull/481))
#### Estimated changes
Modified src/ring_theory/localization.lean
- \+/\- *def* localization.at_prime
- \+ *def* localization.away.inv_self
- \+/\- *def* localization.away
- \+ *lemma* localization.coe_add
- \+ *lemma* localization.coe_mul
- \+ *lemma* localization.coe_mul_of
- \+ *lemma* localization.coe_neg
- \+ *lemma* localization.coe_one
- \+ *lemma* localization.coe_pow
- \+ *lemma* localization.coe_sub
- \+ *lemma* localization.coe_zero
- \+ *def* localization.fraction_ring
- \+/\- *def* localization.inv_aux
- \+ *def* localization.le_order_embedding
- \+ *theorem* localization.map_comap
- \+ *def* localization.of
- \+ *lemma* localization.of_add
- \- *def* localization.of_comm_ring
- \+ *lemma* localization.of_eq_div
- \+ *lemma* localization.of_eq_mul_of_one
- \+ *lemma* localization.of_mul
- \+ *lemma* localization.of_mul_cancel_left
- \+ *lemma* localization.of_mul_cancel_right
- \+ *lemma* localization.of_mul_of
- \+ *lemma* localization.of_neg
- \+ *lemma* localization.of_one
- \+ *lemma* localization.of_pow
- \+ *lemma* localization.of_self''
- \+ *lemma* localization.of_self'
- \+ *lemma* localization.of_self
- \+ *lemma* localization.of_sub
- \+ *lemma* localization.of_zero
- \- *def* localization.quotient_ring.field.of_integral_domain
- \- *def* localization.quotient_ring
- \+/\- *def* localization.r
- \+/\- *theorem* localization.r_of_eq
- \+/\- *theorem* localization.symm



## [2019-02-15 17:29:36-05:00](https://github.com/leanprover-community/mathlib/commit/17f9bef)
feat(category/monad/cont): continuation passing monad ([#728](https://github.com/leanprover-community/mathlib/pull/728))
#### Estimated changes
Added src/category/monad/cont.lean
- \+ *def* cont_t.map
- \+ *lemma* cont_t.monad_lift_bind
- \+ *def* cont_t.run
- \+ *lemma* cont_t.run_cont_t_map_cont_t
- \+ *lemma* cont_t.run_with_cont_t
- \+ *def* cont_t.with_cont_t
- \+ *def* cont_t
- \+ *def* monad_cont.goto
- \+ *structure* monad_cont.label



## [2019-02-15 19:37:56](https://github.com/leanprover-community/mathlib/commit/0a6e705)
refactor(data/equiv/algebra): move polynomial lemmas from equiv/algebra to mv_polynomial ([#731](https://github.com/leanprover-community/mathlib/pull/731))
* refactor(data/equiv/algebra): move polynomial lemma from equiv/algebra to mv_polynomial
* remove update-mathlib.py
#### Estimated changes
Modified src/category_theory/instances/rings.lean


Modified src/data/equiv/algebra.lean
- \- *def* mv_polynomial.iter_to_sum
- \- *lemma* mv_polynomial.iter_to_sum_C_C
- \- *lemma* mv_polynomial.iter_to_sum_C_X
- \- *lemma* mv_polynomial.iter_to_sum_X
- \- *def* mv_polynomial.mv_polynomial_equiv_mv_polynomial
- \- *def* mv_polynomial.option_equiv_left
- \- *def* mv_polynomial.option_equiv_right
- \- *def* mv_polynomial.pempty_ring_equiv
- \- *def* mv_polynomial.punit_ring_equiv
- \- *def* mv_polynomial.ring_equiv_congr
- \- *def* mv_polynomial.ring_equiv_of_equiv
- \- *def* mv_polynomial.sum_ring_equiv
- \- *def* mv_polynomial.sum_to_iter
- \- *lemma* mv_polynomial.sum_to_iter_C
- \- *lemma* mv_polynomial.sum_to_iter_Xl
- \- *lemma* mv_polynomial.sum_to_iter_Xr

Modified src/linear_algebra/multivariate_polynomial.lean
- \+ *def* mv_polynomial.iter_to_sum
- \+ *lemma* mv_polynomial.iter_to_sum_C_C
- \+ *lemma* mv_polynomial.iter_to_sum_C_X
- \+ *lemma* mv_polynomial.iter_to_sum_X
- \+ *def* mv_polynomial.mv_polynomial_equiv_mv_polynomial
- \+ *def* mv_polynomial.option_equiv_left
- \+ *def* mv_polynomial.option_equiv_right
- \+ *def* mv_polynomial.pempty_ring_equiv
- \+ *def* mv_polynomial.punit_ring_equiv
- \+ *def* mv_polynomial.ring_equiv_congr
- \+ *def* mv_polynomial.ring_equiv_of_equiv
- \+ *def* mv_polynomial.sum_ring_equiv
- \+ *def* mv_polynomial.sum_to_iter
- \+ *lemma* mv_polynomial.sum_to_iter_C
- \+ *lemma* mv_polynomial.sum_to_iter_Xl
- \+ *lemma* mv_polynomial.sum_to_iter_Xr

Modified src/ring_theory/noetherian.lean




## [2019-02-15 14:26:25+01:00](https://github.com/leanprover-community/mathlib/commit/d80b03e)
chore(order/filter/basic): update documentation of filter_upwards
#### Estimated changes
Modified src/order/filter/basic.lean




## [2019-02-15 07:40:09](https://github.com/leanprover-community/mathlib/commit/8730619)
chore(topology/algebra/topological_structures): remove unused import ([#729](https://github.com/leanprover-community/mathlib/pull/729))
#### Estimated changes
Modified src/topology/algebra/topological_structures.lean




## [2019-02-14 18:26:14+01:00](https://github.com/leanprover-community/mathlib/commit/ce580d7)
refactor(data/equiv): rename subtype_equiv_of_subtype to subtype_congr and subtype_congr to subtype_congr_prop
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.subtype_congr
- \+ *def* equiv.subtype_congr_prop
- \- *def* equiv.subtype_equiv_of_subtype



## [2019-02-14 18:04:51+01:00](https://github.com/leanprover-community/mathlib/commit/683519f)
feat(data/equiv/basic): generalise subtype_equiv_of_subtype ([#724](https://github.com/leanprover-community/mathlib/pull/724))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.subtype_equiv_of_subtype'
- \+/\- *def* equiv.subtype_equiv_of_subtype



## [2019-02-14 18:04:24+01:00](https://github.com/leanprover-community/mathlib/commit/d4568a4)
fix(data/subtype): don't use pattern matching in subtype.map ([#725](https://github.com/leanprover-community/mathlib/pull/725))
#### Estimated changes
Modified src/data/subtype.lean




## [2019-02-13 19:51:35-05:00](https://github.com/leanprover-community/mathlib/commit/5da8605)
chore(deploy): clean up deploy_nightly.sh ([#720](https://github.com/leanprover-community/mathlib/pull/720))
#### Estimated changes
Modified scripts/deploy_nightly.sh




## [2019-02-13 23:30:38+01:00](https://github.com/leanprover-community/mathlib/commit/a6150a3)
refactor(data/real): move cau_seq_filter to analysis/metric_space ([#723](https://github.com/leanprover-community/mathlib/pull/723))
#### Estimated changes
Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_numbers.lean


Modified src/topology/bounded_continuous_function.lean


Renamed src/data/real/cau_seq_filter.lean to src/topology/metric_space/cau_seq_filter.lean




## [2019-02-13 17:01:08+01:00](https://github.com/leanprover-community/mathlib/commit/3fd0e60)
refactor(topology/algebra/infinite_sum): Cauchy condition for infinite sums generalized to complete topological groups
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* ball_0_eq
- \+ *lemma* has_sum_iff_vanishing_norm
- \+ *lemma* has_sum_of_has_sum_norm
- \+ *lemma* has_sum_of_norm_bounded
- \+ *lemma* norm_tsum_le_tsum_norm

Modified src/analysis/specific_limits.lean
- \- *lemma* has_sum_iff_cauchy
- \- *lemma* has_sum_of_has_sum_norm

Modified src/measure_theory/probability_mass_function.lean
- \+/\- *def* pmf.pure

Modified src/order/filter/basic.lean
- \+ *lemma* filter.tendsto_at_top'
- \+/\- *lemma* filter.tendsto_at_top

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum_comp_of_has_sum_of_injective
- \+ *lemma* has_sum_iff_cauchy
- \+ *lemma* has_sum_iff_has_sum_ne_zero_bij
- \+ *lemma* has_sum_iff_vanishing
- \+/\- *lemma* has_sum_of_has_sum_of_sub
- \+ *lemma* is_sum_iff_is_sum_of_ne_zero_bij
- \- *lemma* is_sum_ite
- \+ *lemma* is_sum_ite_eq
- \+ *lemma* is_sum_le_inj
- \+ *def* option.cases_on'
- \- *lemma* tsum_ite
- \+ *lemma* tsum_ite_eq

Modified src/topology/algebra/topological_structures.lean
- \+ *lemma* exists_nhds_split_inv



## [2019-02-12 22:44:40+01:00](https://github.com/leanprover-community/mathlib/commit/246c280)
feat(tactic/basic,tactic/interactive): improvements to set tactic ([#712](https://github.com/leanprover-community/mathlib/pull/712))
* feat(tactic/basic,tactic/interactive): improvements to set tactic
* feat(tactic/interactive): take optional explicit type in set tactic
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/basic.lean


Modified src/tactic/interactive.lean


Modified src/tactic/linarith.lean




## [2019-02-12 15:50:35-05:00](https://github.com/leanprover-community/mathlib/commit/f6ca16e)
fix(nightly): improve conditional ([#719](https://github.com/leanprover-community/mathlib/pull/719))
#### Estimated changes
Modified scripts/deploy_nightly.sh




## [2019-02-12 20:15:49+01:00](https://github.com/leanprover-community/mathlib/commit/a4afa90)
refactor(analysis/specific_limits): generalize has_sum_of_absolute_convergence to normed_groups
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_triangle_sub
- \+ *lemma* norm_triangle_sum

Modified src/analysis/specific_limits.lean
- \+ *lemma* has_sum_iff_cauchy
- \- *lemma* has_sum_of_absolute_convergence
- \+ *lemma* has_sum_of_absolute_convergence_real
- \+ *lemma* has_sum_of_has_sum_norm
- \- *lemma* is_sum_iff_tendsto_nat_of_nonneg

Modified src/data/finset.lean
- \+ *lemma* finset.disjoint_sdiff

Modified src/measure_theory/decomposition.lean


Modified src/measure_theory/measure_space.lean
- \- *lemma* tendsto_at_top_infi_nat
- \- *lemma* tendsto_at_top_supr_nat

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.tendsto_at_top_at_top
- \+ *theorem* filter.tendsto_at_top_principal

Modified src/topology/algebra/topological_structures.lean
- \+ *lemma* infi_eq_of_tendsto
- \+ *lemma* tendsto_at_top_infi_nat
- \+ *lemma* tendsto_at_top_supr_nat

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.is_sum_iff_tendsto_nat
- \+/\- *lemma* has_sum_of_nonneg_of_le
- \+ *lemma* is_sum_iff_tendsto_nat_of_nonneg
- \+/\- *lemma* nnreal.exists_le_is_sum_of_le
- \+ *lemma* nnreal.is_sum_iff_tendsto_nat

Modified src/topology/metric_space/basic.lean
- \+/\- *theorem* metric.tendsto_at_top

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* cauchy_iff_exists_le_nhds
- \+ *lemma* cauchy_map_iff
- \+ *lemma* cauchy_map_iff_exists_tendsto



## [2019-02-12 09:33:43-05:00](https://github.com/leanprover-community/mathlib/commit/503a423)
feat(update-mathlib): improve setup and error messages
#### Estimated changes
Modified scripts/remote-install-update-mathlib.sh


Modified scripts/setup-update-mathlib.sh


Modified scripts/update-mathlib.py




## [2019-02-12 15:28:42+01:00](https://github.com/leanprover-community/mathlib/commit/b6a4763)
refactor(order/filter): replace tendsto_comp_succ_at_top_iff by tendsto_add_at_top_iff_nat
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \- *lemma* tendsto_comp_succ_at_top_iff
- \+/\- *lemma* tendsto_one_div_add_at_top_nhds_0_nat
- \+/\- *lemma* tendsto_pow_at_top_at_top_of_gt_1_nat

Modified src/order/filter/basic.lean
- \+ *lemma* filter.tendsto_add_at_top_iff_nat

Modified src/topology/metric_space/lipschitz.lean




## [2019-02-12 08:46:53-05:00](https://github.com/leanprover-community/mathlib/commit/c4e8414)
fix(update-mathlib): install from anywhere in your directory structure
#### Estimated changes
Modified scripts/remote-install-update-mathlib.sh




## [2019-02-12 14:09:42+01:00](https://github.com/leanprover-community/mathlib/commit/f5a85f1)
refactor(order/filter): move lift and lift' to separate file
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.prod_eq_empty_iff

Modified src/order/filter/basic.lean
- \+ *lemma* filter.bot_prod
- \- *theorem* filter.comap_eq_lift'
- \- *theorem* filter.comap_lift'_eq2
- \- *theorem* filter.comap_lift'_eq
- \- *theorem* filter.comap_lift_eq2
- \- *lemma* filter.comap_lift_eq
- \- *lemma* filter.le_lift'
- \- *lemma* filter.le_lift
- \- *lemma* filter.lift'_cong
- \- *lemma* filter.lift'_id
- \- *lemma* filter.lift'_inf_principal_eq
- \- *lemma* filter.lift'_infi
- \- *lemma* filter.lift'_le
- \- *lemma* filter.lift'_lift'_assoc
- \- *lemma* filter.lift'_lift_assoc
- \- *lemma* filter.lift'_mono'
- \- *lemma* filter.lift'_mono
- \- *lemma* filter.lift'_neq_bot_iff
- \- *lemma* filter.lift'_principal
- \- *lemma* filter.lift_assoc
- \- *lemma* filter.lift_comm
- \- *lemma* filter.lift_const
- \- *lemma* filter.lift_inf
- \- *lemma* filter.lift_infi'
- \- *lemma* filter.lift_infi
- \- *lemma* filter.lift_le
- \- *lemma* filter.lift_lift'_assoc
- \- *lemma* filter.lift_lift'_same_eq_lift'
- \- *lemma* filter.lift_lift'_same_le_lift'
- \- *lemma* filter.lift_lift_same_eq_lift
- \- *lemma* filter.lift_lift_same_le_lift
- \- *lemma* filter.lift_mono'
- \- *lemma* filter.lift_mono
- \- *lemma* filter.lift_neq_bot_iff
- \- *lemma* filter.lift_principal2
- \- *lemma* filter.lift_principal
- \- *lemma* filter.lift_sets_eq
- \- *lemma* filter.map_lift'_eq2
- \- *lemma* filter.map_lift'_eq
- \- *lemma* filter.map_lift_eq2
- \- *lemma* filter.map_lift_eq
- \- *lemma* filter.mem_lift'
- \- *lemma* filter.mem_lift'_sets
- \- *lemma* filter.mem_lift
- \- *lemma* filter.mem_lift_sets
- \- *lemma* filter.mem_prod_same_iff
- \- *theorem* filter.monotone_lift'
- \- *theorem* filter.monotone_lift
- \- *lemma* filter.principal_le_lift'
- \- *lemma* filter.prod_bot1
- \- *lemma* filter.prod_bot2
- \+ *lemma* filter.prod_bot
- \- *lemma* filter.prod_def
- \+ *lemma* filter.prod_eq_bot
- \- *lemma* filter.prod_lift'_lift'
- \- *lemma* filter.prod_lift_lift
- \- *lemma* filter.prod_same_eq
- \- *lemma* filter.tendsto_prod_self_iff

Added src/order/filter/lift.lean
- \+ *theorem* filter.comap_eq_lift'
- \+ *theorem* filter.comap_lift'_eq2
- \+ *theorem* filter.comap_lift'_eq
- \+ *theorem* filter.comap_lift_eq2
- \+ *lemma* filter.comap_lift_eq
- \+ *lemma* filter.le_lift'
- \+ *lemma* filter.le_lift
- \+ *lemma* filter.lift'_cong
- \+ *lemma* filter.lift'_id
- \+ *lemma* filter.lift'_inf_principal_eq
- \+ *lemma* filter.lift'_infi
- \+ *lemma* filter.lift'_le
- \+ *lemma* filter.lift'_lift'_assoc
- \+ *lemma* filter.lift'_lift_assoc
- \+ *lemma* filter.lift'_mono'
- \+ *lemma* filter.lift'_mono
- \+ *lemma* filter.lift'_neq_bot_iff
- \+ *lemma* filter.lift'_principal
- \+ *lemma* filter.lift_assoc
- \+ *lemma* filter.lift_comm
- \+ *lemma* filter.lift_const
- \+ *lemma* filter.lift_inf
- \+ *lemma* filter.lift_infi'
- \+ *lemma* filter.lift_infi
- \+ *lemma* filter.lift_le
- \+ *lemma* filter.lift_lift'_assoc
- \+ *lemma* filter.lift_lift'_same_eq_lift'
- \+ *lemma* filter.lift_lift'_same_le_lift'
- \+ *lemma* filter.lift_lift_same_eq_lift
- \+ *lemma* filter.lift_lift_same_le_lift
- \+ *lemma* filter.lift_mono'
- \+ *lemma* filter.lift_mono
- \+ *lemma* filter.lift_neq_bot_iff
- \+ *lemma* filter.lift_principal2
- \+ *lemma* filter.lift_principal
- \+ *lemma* filter.lift_sets_eq
- \+ *lemma* filter.map_lift'_eq2
- \+ *lemma* filter.map_lift'_eq
- \+ *lemma* filter.map_lift_eq2
- \+ *lemma* filter.map_lift_eq
- \+ *lemma* filter.mem_lift'
- \+ *lemma* filter.mem_lift'_sets
- \+ *lemma* filter.mem_lift
- \+ *lemma* filter.mem_lift_sets
- \+ *lemma* filter.mem_prod_same_iff
- \+ *theorem* filter.monotone_lift'
- \+ *theorem* filter.monotone_lift
- \+ *lemma* filter.principal_le_lift'
- \+ *lemma* filter.prod_def
- \+ *lemma* filter.prod_lift'_lift'
- \+ *lemma* filter.prod_lift_lift
- \+ *lemma* filter.prod_same_eq
- \+ *lemma* filter.tendsto_prod_self_iff

Modified src/topology/uniform_space/basic.lean




## [2019-02-12 11:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/253fe33)
refactor(order/filter): generalize map_succ_at_top_eq to arbitrary Galois insertions; generalize tendsto_coe_iff to arbitary order-preserving embeddings
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \- *lemma* map_succ_at_top_eq
- \- *lemma* tendsto_coe_iff
- \+/\- *lemma* tendsto_comp_succ_at_top_iff

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.at_top_ne_bot
- \+ *lemma* filter.map_add_at_top_eq_nat
- \+/\- *lemma* filter.map_at_top_eq
- \+ *lemma* filter.map_at_top_eq_of_gc
- \+ *lemma* filter.map_div_at_top_eq_nat
- \+ *lemma* filter.map_sub_at_top_eq_nat
- \+/\- *lemma* filter.mem_at_top_sets
- \+ *lemma* filter.tendso_add_at_top_nat
- \+ *lemma* filter.tendso_sub_at_top_nat
- \+ *lemma* filter.tendsto_at_top_embedding

Modified src/topology/instances/real.lean
- \+ *lemma* tendsto_coe_int_real_at_top_at_top
- \+ *lemma* tendsto_coe_int_real_at_top_iff
- \+ *lemma* tendsto_coe_nat_real_at_top_at_top
- \+ *lemma* tendsto_coe_nat_real_at_top_iff
- \- *lemma* tendsto_of_nat_at_top_at_top



## [2019-02-12 11:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/c853c33)
chore(analysis/specific_limits): replace mul_add_one_le_pow by pow_ge_one_add_mul
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \- *lemma* mul_add_one_le_pow



## [2019-02-12 09:12:26](https://github.com/leanprover-community/mathlib/commit/41e3b6f)
refactor(data/list): add prop arg for easier usage ([#715](https://github.com/leanprover-community/mathlib/pull/715))
#### Estimated changes
Modified src/data/list/basic.lean
- \+/\- *theorem* list.exists_or_eq_self_of_erasep



## [2019-02-11 20:48:17-05:00](https://github.com/leanprover-community/mathlib/commit/d1ef181)
feat(topology/metric_space/gluing): Gluing metric spaces ([#695](https://github.com/leanprover-community/mathlib/pull/695))
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \- *def* metric_space_sum
- \- *lemma* sum.dist_eq
- \- *lemma* sum.one_dist_le'
- \- *lemma* sum.one_dist_le

Added src/topology/metric_space/gluing.lean
- \+ *def* metric.glue_dist
- \+ *lemma* metric.glue_dist_glued_points
- \+ *def* metric.glue_metric_approx
- \+ *def* metric.glue_premetric
- \+ *def* metric.glue_space
- \+ *lemma* metric.isometry_on_inl
- \+ *lemma* metric.isometry_on_inr
- \+ *def* metric.metric_space_sum
- \+ *def* metric.sum.dist
- \+ *lemma* metric.sum.dist_eq
- \+ *lemma* metric.sum.dist_eq_glue_dist
- \+ *lemma* metric.sum.one_dist_le'
- \+ *lemma* metric.sum.one_dist_le
- \+ *lemma* metric.to_glue_commute
- \+ *def* metric.to_glue_l
- \+ *lemma* metric.to_glue_l_isometry
- \+ *def* metric.to_glue_r
- \+ *lemma* metric.to_glue_r_isometry



## [2019-02-11 15:43:36-05:00](https://github.com/leanprover-community/mathlib/commit/8243300)
build(nightly): fix nightly
#### Estimated changes
Modified .travis.yml


Modified scripts/deploy_nightly.sh


Modified scripts/lean_version.py




## [2019-02-11 16:50:18](https://github.com/leanprover-community/mathlib/commit/fb7e42d)
fix(group_theory/quotient_group): remove duplicate group_hom instance ([#713](https://github.com/leanprover-community/mathlib/pull/713))
#### Estimated changes
Modified src/group_theory/quotient_group.lean




## [2019-02-11 10:13:54+01:00](https://github.com/leanprover-community/mathlib/commit/4b84aac)
fix(data/finsupp): duplicated instance
#### Estimated changes
Modified src/data/finsupp.lean
- \+/\- *lemma* finsupp.mul_sum



## [2019-02-10 21:50:00](https://github.com/leanprover-community/mathlib/commit/091cad7)
feat(algebra/gcd_domain): normalize ([#668](https://github.com/leanprover-community/mathlib/pull/668))
#### Estimated changes
Modified src/algebra/gcd_domain.lean
- \+ *theorem* associated_normalize
- \- *theorem* associated_of_dvd_of_dvd
- \- *lemma* associates.norm_unit_out
- \+ *lemma* associates.normalize_out
- \+/\- *lemma* associates.out_mk
- \- *theorem* dvd_antisymm_of_norm
- \+ *theorem* dvd_antisymm_of_normalize_eq
- \+ *lemma* dvd_normalize_iff
- \+/\- *theorem* gcd_eq_left_iff
- \- *theorem* gcd_eq_mul_norm_unit
- \+ *theorem* gcd_eq_normalize
- \+/\- *theorem* gcd_eq_right_iff
- \+/\- *theorem* gcd_mul_lcm
- \+/\- *theorem* gcd_mul_left
- \+/\- *theorem* gcd_mul_right
- \+/\- *theorem* gcd_same
- \+/\- *theorem* gcd_zero_left
- \+/\- *theorem* gcd_zero_right
- \- *theorem* int.coe_nat_abs_eq_mul_norm_unit
- \+ *theorem* int.coe_nat_abs_eq_normalize
- \- *lemma* int.norm_unit_nat_coe
- \- *lemma* int.norm_unit_of_neg
- \- *lemma* int.norm_unit_of_nonneg
- \+ *lemma* int.normalize_coe_nat
- \+ *lemma* int.normalize_of_neg
- \+ *lemma* int.normalize_of_nonneg
- \+/\- *theorem* lcm_eq_left_iff
- \- *lemma* lcm_eq_mul_norm_unit
- \+ *lemma* lcm_eq_normalize
- \+/\- *theorem* lcm_eq_right_iff
- \+/\- *theorem* lcm_mul_left
- \+/\- *theorem* lcm_mul_right
- \+/\- *theorem* lcm_one_left
- \+/\- *theorem* lcm_one_right
- \+/\- *theorem* lcm_same
- \+/\- *theorem* lcm_units_coe_left
- \+/\- *theorem* lcm_units_coe_right
- \- *theorem* mul_norm_unit_eq_mul_norm_unit
- \- *theorem* norm_unit_gcd
- \- *lemma* norm_unit_lcm
- \+ *def* normalize
- \+ *theorem* normalize_associated
- \+ *lemma* normalize_coe_units
- \+ *lemma* normalize_dvd_iff
- \+ *theorem* normalize_eq_normalize
- \+ *lemma* normalize_eq_normalize_iff
- \+ *lemma* normalize_eq_one
- \+ *lemma* normalize_eq_zero
- \+ *theorem* normalize_gcd
- \+ *theorem* normalize_idem
- \+ *lemma* normalize_lcm
- \+ *theorem* normalize_mul
- \+ *lemma* normalize_one
- \+ *lemma* normalize_zero

Modified src/data/polynomial.lean
- \- *lemma* polynomial.monic_mul_norm_unit
- \+ *lemma* polynomial.monic_normalize

Modified src/ring_theory/unique_factorization_domain.lean




## [2019-02-10 12:36:00-05:00](https://github.com/leanprover-community/mathlib/commit/cfe582f)
Automate the deployment of nightly builds ([#707](https://github.com/leanprover-community/mathlib/pull/707))
* build(nightly): automate nightly releases of mathlib
#### Estimated changes
Modified .travis.yml


Added scripts/deploy_nightly.sh


Added scripts/lean_version.py


Modified scripts/update-mathlib.py




## [2019-02-10 16:44:30](https://github.com/leanprover-community/mathlib/commit/9b28db0)
refactor(*): refactor associates ([#710](https://github.com/leanprover-community/mathlib/pull/710))
#### Estimated changes
Renamed src/ring_theory/associated.lean to src/algebra/associated.lean
- \- *lemma* associates.dvd_out_iff
- \- *lemma* associates.norm_unit_out
- \- *lemma* associates.out_dvd_iff
- \- *lemma* associates.out_mk
- \- *lemma* associates.out_mul
- \- *lemma* associates.out_one
- \- *lemma* associates.out_top
- \- *def* associates_int_equiv_nat
- \- *theorem* irreducible_iff_nat_prime
- \- *lemma* nat.prime_iff_prime
- \- *lemma* nat.prime_iff_prime_int

Modified src/algebra/gcd_domain.lean
- \+ *lemma* associates.dvd_out_iff
- \+ *lemma* associates.norm_unit_out
- \+ *lemma* associates.out_dvd_iff
- \+ *lemma* associates.out_mk
- \+ *lemma* associates.out_mul
- \+ *lemma* associates.out_one
- \+ *lemma* associates.out_top
- \+ *def* associates_int_equiv_nat
- \+ *lemma* int.coe_gcd
- \+ *lemma* int.coe_lcm
- \+ *theorem* int.coe_nat_abs_eq_mul_norm_unit
- \+ *theorem* int.dvd_gcd
- \+ *theorem* int.dvd_lcm_left
- \+ *theorem* int.dvd_lcm_right
- \+ *theorem* int.gcd_assoc
- \+ *theorem* int.gcd_comm
- \+ *theorem* int.gcd_div
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
- \+ *theorem* int.gcd_eq_zero_iff
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
- \+ *lemma* int.nat_abs_gcd
- \+ *lemma* int.nat_abs_lcm
- \+ *lemma* int.norm_unit_nat_coe
- \+ *lemma* int.norm_unit_of_neg
- \+ *lemma* int.norm_unit_of_nonneg
- \+ *theorem* irreducible_iff_nat_prime
- \+ *lemma* nat.prime_iff_prime
- \+ *lemma* nat.prime_iff_prime_int

Modified src/data/int/gcd.lean
- \- *lemma* int.coe_gcd
- \- *lemma* int.coe_lcm
- \- *theorem* int.coe_nat_abs_eq_mul_norm_unit
- \- *theorem* int.dvd_gcd
- \- *theorem* int.dvd_lcm_left
- \- *theorem* int.dvd_lcm_right
- \- *theorem* int.gcd_assoc
- \- *theorem* int.gcd_comm
- \- *theorem* int.gcd_div
- \- *theorem* int.gcd_dvd_gcd_mul_left
- \- *theorem* int.gcd_dvd_gcd_mul_left_right
- \- *theorem* int.gcd_dvd_gcd_mul_right
- \- *theorem* int.gcd_dvd_gcd_mul_right_right
- \- *theorem* int.gcd_dvd_gcd_of_dvd_left
- \- *theorem* int.gcd_dvd_gcd_of_dvd_right
- \- *theorem* int.gcd_dvd_left
- \- *theorem* int.gcd_dvd_right
- \- *theorem* int.gcd_eq_left
- \- *theorem* int.gcd_eq_right
- \- *theorem* int.gcd_eq_zero_iff
- \- *theorem* int.gcd_mul_lcm
- \- *theorem* int.gcd_mul_left
- \- *theorem* int.gcd_mul_right
- \- *theorem* int.gcd_one_left
- \- *theorem* int.gcd_one_right
- \- *theorem* int.gcd_pos_of_non_zero_left
- \- *theorem* int.gcd_pos_of_non_zero_right
- \- *theorem* int.gcd_self
- \- *theorem* int.gcd_zero_left
- \- *theorem* int.gcd_zero_right
- \- *def* int.lcm
- \- *theorem* int.lcm_assoc
- \- *theorem* int.lcm_comm
- \- *theorem* int.lcm_def
- \- *theorem* int.lcm_dvd
- \- *theorem* int.lcm_one_left
- \- *theorem* int.lcm_one_right
- \- *theorem* int.lcm_self
- \- *theorem* int.lcm_zero_left
- \- *theorem* int.lcm_zero_right
- \- *lemma* int.nat_abs_gcd
- \- *lemma* int.nat_abs_lcm
- \- *lemma* int.norm_unit_nat_coe
- \- *lemma* int.norm_unit_of_neg
- \- *lemma* int.norm_unit_of_nonneg

Modified src/data/padics/padic_norm.lean


Modified src/data/polynomial.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2019-02-10 14:25:05](https://github.com/leanprover-community/mathlib/commit/c25122b)
feat(algebra/archimedean): add fractional parts of floor_rings ([#709](https://github.com/leanprover-community/mathlib/pull/709))
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+ *lemma* floor_add_fract
- \+ *lemma* floor_eq_iff
- \+ *lemma* floor_fract
- \+ *def* fract
- \+ *theorem* fract_add
- \+ *lemma* fract_add_floor
- \+ *lemma* fract_coe
- \+ *theorem* fract_eq_fract
- \+ *theorem* fract_eq_iff
- \+ *lemma* fract_floor
- \+ *lemma* fract_fract
- \+ *theorem* fract_lt_one
- \+ *theorem* fract_mul_nat
- \+ *theorem* fract_nonneg
- \+ *lemma* fract_zero

Modified src/algebra/group.lean
- \+ *lemma* sub_eq_sub_iff_sub_eq_sub



## [2019-02-10 14:01:02+01:00](https://github.com/leanprover-community/mathlib/commit/d6f84da)
feat(tactic/tidy): add `tidy?` syntax for reporting a tactic script ([#704](https://github.com/leanprover-community/mathlib/pull/704))
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/tidy.lean


Modified test/tidy.lean
- \+/\- *structure* tidy.test.B
- \+/\- *def* tidy.test.d
- \+/\- *def* tidy.test.tidy_test_0
- \+/\- *def* tidy.test.tidy_test_1



## [2019-02-10 10:39:51](https://github.com/leanprover-community/mathlib/commit/ed4c536)
feat(data/polynomial): multiplicity of roots of polynomials ([#656](https://github.com/leanprover-community/mathlib/pull/656))
* feat(data/polynomial): multiplicity of roots of polynomials
* rename lemmas
* use section
* use `nonzero_comm_ring.of_ne`
* refactor(polynomial): weaken decidablility hypothesis
* indentation
* swap order of arguments
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *def* nonzero_comm_ring.of_ne

Modified src/data/polynomial.lean
- \+ *def* polynomial.decidable_dvd_monic
- \+ *lemma* polynomial.div_by_monic_mul_pow_root_multiplicity_eq
- \+ *lemma* polynomial.eval_div_by_monic_pow_root_multiplicity_ne_zero
- \+ *lemma* polynomial.monic_mul
- \+ *lemma* polynomial.monic_pow
- \+ *lemma* polynomial.multiplicity_X_sub_C_finite
- \+ *lemma* polynomial.multiplicity_finite_of_degree_pos_of_monic
- \+ *def* polynomial.nonzero_comm_ring.of_polynomial_ne
- \+ *lemma* polynomial.pow_root_multiplicity_dvd
- \+ *def* polynomial.root_multiplicity
- \+ *lemma* polynomial.root_multiplicity_eq_multiplicity



## [2019-02-09 15:41:40](https://github.com/leanprover-community/mathlib/commit/088f753)
refactor(geo_sum): remove duplicate proofs about geometric sums ([#706](https://github.com/leanprover-community/mathlib/pull/706))
* feat(data/finset): add range_add_one
* feat(algebra/big_operators): geometric sum for semiring, ring and division ring
* refactor(geo_sum): remove duplicate proofs about geometric sums
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *theorem* geom_sum
- \+ *lemma* geom_sum_inv

Modified src/analysis/specific_limits.lean
- \- *lemma* sum_geometric'
- \- *lemma* sum_geometric

Modified src/data/complex/basic.lean
- \- *lemma* complex.inv_zero
- \- *theorem* complex.mul_inv_cancel

Modified src/data/complex/exponential.lean
- \- *lemma* geo_sum_eq
- \- *lemma* geo_sum_inv_eq



## [2019-02-09 15:38:37](https://github.com/leanprover-community/mathlib/commit/484d864)
add geometric sum ([#701](https://github.com/leanprover-community/mathlib/pull/701))
* feat(data/finset): add range_add_one
* feat(algebra/big_operators): geometric sum for semiring, ring and division ring
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *theorem* geom_sum
- \+ *theorem* geom_sum_mul
- \+ *theorem* geom_sum_mul_add

Modified src/data/finset.lean
- \+ *theorem* finset.range_add_one



## [2019-02-08 20:56:33-05:00](https://github.com/leanprover-community/mathlib/commit/22c7179)
build(update-mathlib): adjust the header of python script
#### Estimated changes
Modified scripts/update-mathlib.py




## [2019-02-08 18:41:17-05:00](https://github.com/leanprover-community/mathlib/commit/8b51017)
build(update-mathlib): fix installation and documentation
#### Estimated changes
Modified scripts/remote-install-update-mathlib.sh


Modified scripts/setup-update-mathlib.sh


Modified scripts/update-mathlib.py




## [2019-02-08 17:13:15-05:00](https://github.com/leanprover-community/mathlib/commit/650237b)
build(update-mathlib): install update-mathlib into `~/.mathlib/bin`
#### Estimated changes
Modified scripts/remote-install-update-mathlib.sh


Modified scripts/setup-update-mathlib.sh




## [2019-02-08 17:01:46-05:00](https://github.com/leanprover-community/mathlib/commit/814cb03)
build(update-mathlib): fix installation and documentation
#### Estimated changes
Modified README.md


Added scripts/remote-install-update-mathlib.sh




## [2019-02-08 16:55:19-05:00](https://github.com/leanprover-community/mathlib/commit/64065f4)
build(update-mathlib): improve installation and documentation
#### Estimated changes
Modified .travis.yml


Modified README.md


Modified scripts/update-mathlib.py




## [2019-02-08 16:11:45-05:00](https://github.com/leanprover-community/mathlib/commit/4227f5c)
Deploy olean ([#697](https://github.com/leanprover-community/mathlib/pull/697))
* deploy(olean): deploy the olean files for every successful builds
#### Estimated changes
Modified .travis.yml


Modified README.md


Added scripts/setup-update-mathlib.sh


Added scripts/update-mathlib.py




## [2019-02-08 19:05:45](https://github.com/leanprover-community/mathlib/commit/11e19d8)
refactor(ring_theory/noetherian): make is_noetherian and is_noetherian_ring classes ([#689](https://github.com/leanprover-community/mathlib/pull/689))
* refactor(ring_theory/noetherian): make is_noetherian and is_noetherian_ring classes
* correct spelling mistake.
* add well_founded_submodule_gt
#### Estimated changes
Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/noetherian.lean
- \- *def* is_noetherian
- \- *theorem* is_noetherian_pi
- \- *theorem* is_noetherian_prod
- \+/\- *def* is_noetherian_ring
- \- *theorem* is_noetherian_ring_range
- \- *theorem* ring.is_noetherian_of_fintype
- \+ *lemma* well_founded_submodule_gt

Modified src/ring_theory/polynomial.lean
- \+/\- *theorem* ideal.is_fg_degree_le
- \+/\- *theorem* is_noetherian_ring_polynomial

Modified src/ring_theory/principal_ideal_domain.lean
- \- *lemma* principal_ideal_domain.is_noetherian_ring



## [2019-02-08 13:11:06-05:00](https://github.com/leanprover-community/mathlib/commit/1f50e0d)
fix(build): fix the output keeping travis builds alive ([#702](https://github.com/leanprover-community/mathlib/pull/702))
#### Estimated changes
Modified .travis.yml




## [2019-02-08 09:43:02-05:00](https://github.com/leanprover-community/mathlib/commit/0f2562e)
fix(build): fix the output keeping travis builds alive ([#700](https://github.com/leanprover-community/mathlib/pull/700))
#### Estimated changes
Modified .travis.yml




## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/cfd2b75)
feat(order/filter): break filter into smaller files
#### Estimated changes
Renamed src/order/filter.lean to src/order/filter/basic.lean
- \- *def* filter.mem_pmap
- \- *def* filter.mem_rcomap'
- \- *theorem* filter.mem_rmap
- \- *def* filter.pcomap'
- \- *def* filter.pmap
- \- *theorem* filter.pmap_res
- \- *def* filter.ptendsto'
- \- *theorem* filter.ptendsto'_def
- \- *theorem* filter.ptendsto'_of_ptendsto
- \- *def* filter.ptendsto
- \- *theorem* filter.ptendsto_def
- \- *theorem* filter.ptendsto_iff_rtendsto
- \- *theorem* filter.ptendsto_of_ptendsto'
- \- *def* filter.rcomap'
- \- *lemma* filter.rcomap'_compose
- \- *theorem* filter.rcomap'_rcomap'
- \- *theorem* filter.rcomap'_sets
- \- *def* filter.rcomap
- \- *lemma* filter.rcomap_compose
- \- *theorem* filter.rcomap_rcomap
- \- *theorem* filter.rcomap_sets
- \- *def* filter.rmap
- \- *lemma* filter.rmap_compose
- \- *theorem* filter.rmap_rmap
- \- *theorem* filter.rmap_sets
- \- *def* filter.rtendsto'
- \- *theorem* filter.rtendsto'_def
- \- *def* filter.rtendsto
- \- *theorem* filter.rtendsto_def
- \- *theorem* filter.rtendsto_iff_le_comap
- \- *theorem* filter.tendsto_iff_ptendsto
- \- *theorem* filter.tendsto_iff_ptendsto_univ
- \- *theorem* filter.tendsto_iff_rtendsto'
- \- *theorem* filter.tendsto_iff_rtendsto

Added src/order/filter/default.lean


Added src/order/filter/partial.lean
- \+ *def* filter.mem_pmap
- \+ *def* filter.mem_rcomap'
- \+ *theorem* filter.mem_rmap
- \+ *def* filter.pcomap'
- \+ *def* filter.pmap
- \+ *theorem* filter.pmap_res
- \+ *def* filter.ptendsto'
- \+ *theorem* filter.ptendsto'_def
- \+ *theorem* filter.ptendsto'_of_ptendsto
- \+ *def* filter.ptendsto
- \+ *theorem* filter.ptendsto_def
- \+ *theorem* filter.ptendsto_iff_rtendsto
- \+ *theorem* filter.ptendsto_of_ptendsto'
- \+ *def* filter.rcomap'
- \+ *lemma* filter.rcomap'_compose
- \+ *theorem* filter.rcomap'_rcomap'
- \+ *theorem* filter.rcomap'_sets
- \+ *def* filter.rcomap
- \+ *lemma* filter.rcomap_compose
- \+ *theorem* filter.rcomap_rcomap
- \+ *theorem* filter.rcomap_sets
- \+ *def* filter.rmap
- \+ *lemma* filter.rmap_compose
- \+ *theorem* filter.rmap_rmap
- \+ *theorem* filter.rmap_sets
- \+ *def* filter.rtendsto'
- \+ *theorem* filter.rtendsto'_def
- \+ *def* filter.rtendsto
- \+ *theorem* filter.rtendsto_def
- \+ *theorem* filter.rtendsto_iff_le_comap
- \+ *theorem* filter.tendsto_iff_ptendsto
- \+ *theorem* filter.tendsto_iff_ptendsto_univ
- \+ *theorem* filter.tendsto_iff_rtendsto'
- \+ *theorem* filter.tendsto_iff_rtendsto



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/8db042f)
feat(data/rel): galois_connection (image r) (core r)
#### Estimated changes
Modified src/data/rel.lean
- \+/\- *lemma* rel.core_comp
- \+ *theorem* rel.core_preimage_gc
- \+ *theorem* rel.image_subset_iff
- \+/\- *lemma* rel.preimage_comp
- \+/\- *def* rel.restrict_domain
- \+/\- *lemma* set.preimage_eq



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/b2ba37c)
chore(*): fix errors introduced by rebasing
#### Estimated changes
Deleted analysis/metric_space.lean
- \- *theorem* abs_dist
- \- *theorem* abs_dist_sub_le
- \- *def* ball
- \- *theorem* ball_disjoint
- \- *theorem* ball_disjoint_same
- \- *theorem* ball_eq_empty_iff_nonpos
- \- *theorem* ball_half_subset
- \- *theorem* ball_mem_nhds
- \- *theorem* ball_subset
- \- *theorem* ball_subset_ball
- \- *theorem* ball_subset_closed_ball
- \- *lemma* cauchy_of_metric
- \- *theorem* cauchy_seq_metric'
- \- *theorem* cauchy_seq_metric
- \- *def* closed_ball
- \- *theorem* continuous_dist'
- \- *theorem* continuous_dist
- \- *theorem* continuous_of_metric
- \- *theorem* continuous_topo_metric
- \- *lemma* countable_closure_of_compact
- \- *theorem* dist_comm
- \- *lemma* dist_eq_edist
- \- *lemma* dist_eq_nndist
- \- *theorem* dist_eq_zero
- \- *theorem* dist_le_zero
- \- *theorem* dist_mem_uniformity
- \- *theorem* dist_nonneg
- \- *lemma* dist_pi_def
- \- *theorem* dist_pos
- \- *theorem* dist_self
- \- *theorem* dist_triangle
- \- *theorem* dist_triangle_left
- \- *theorem* dist_triangle_right
- \- *theorem* edist_dist
- \- *lemma* edist_eq_dist
- \- *lemma* edist_eq_nndist
- \- *lemma* edist_ne_top
- \- *theorem* eq_of_dist_eq_zero
- \- *theorem* eq_of_forall_dist_le
- \- *theorem* eq_of_nndist_eq_zero
- \- *theorem* exists_ball_subset_ball
- \- *theorem* exists_delta_of_continuous
- \- *lemma* finite_cover_balls_of_compact
- \- *theorem* is_closed_ball
- \- *theorem* is_open_ball
- \- *theorem* is_open_metric
- \- *lemma* lebesgue_number_lemma_of_metric
- \- *lemma* lebesgue_number_lemma_of_metric_sUnion
- \- *theorem* mem_ball'
- \- *theorem* mem_ball
- \- *theorem* mem_ball_comm
- \- *theorem* mem_ball_self
- \- *theorem* mem_closed_ball
- \- *theorem* mem_closure_iff'
- \- *theorem* mem_nhds_iff_metric
- \- *theorem* mem_uniformity_dist
- \- *lemma* mem_uniformity_dist_edist
- \- *theorem* metric.mem_nhds_within
- \- *theorem* metric.ptendsto_nhds_within
- \- *theorem* metric.rtendsto'_nhds_within
- \- *theorem* metric.rtendsto_nhds_within
- \- *theorem* metric.tendsto_nhds_within
- \- *def* metric_space.induced
- \- *def* metric_space.replace_uniformity
- \- *def* metric_space.uniform_space_of_dist
- \- *lemma* nhds_comap_dist
- \- *theorem* nhds_eq_metric
- \- *def* nndist
- \- *theorem* nndist_comm
- \- *lemma* nndist_eq_dist
- \- *lemma* nndist_eq_edist
- \- *theorem* nndist_eq_zero
- \- *lemma* nndist_self
- \- *theorem* nndist_triangle
- \- *theorem* nndist_triangle_left
- \- *theorem* nndist_triangle_right
- \- *theorem* pos_of_mem_ball
- \- *theorem* real.dist_0_eq_abs
- \- *theorem* real.dist_eq
- \- *lemma* second_countable_of_separable_metric_space
- \- *theorem* subtype.dist_eq
- \- *theorem* swap_dist
- \- *theorem* tendsto_at_top_metric
- \- *theorem* tendsto_dist
- \- *lemma* tendsto_iff_dist_tendsto_zero
- \- *theorem* tendsto_nhds_of_metric
- \- *theorem* tendsto_nhds_topo_metric
- \- *theorem* totally_bounded_of_metric
- \- *theorem* uniform_continuous_dist'
- \- *theorem* uniform_continuous_dist
- \- *theorem* uniform_continuous_of_metric
- \- *theorem* uniform_embedding_of_metric
- \- *theorem* uniformity_dist'
- \- *theorem* uniformity_dist
- \- *theorem* uniformity_edist'
- \- *theorem* uniformity_edist
- \- *theorem* zero_eq_dist
- \- *theorem* zero_eq_nndist

Deleted data/real/cau_seq_filter.lean
- \- *lemma* cau_seq_iff_cauchy_seq
- \- *lemma* cauchy_of_filter_cauchy
- \- *theorem* complete_of_cauchy_seq_tendsto
- \- *lemma* filter_cauchy_of_cauchy
- \- *lemma* sequentially_complete.cauchy_seq_of_dist_tendsto_0
- \- *lemma* sequentially_complete.le_nhds_cau_filter_lim
- \- *lemma* sequentially_complete.mono_of_mono_succ
- \- *lemma* sequentially_complete.seq_of_cau_filter_is_cauchy'
- \- *lemma* sequentially_complete.seq_of_cau_filter_is_cauchy
- \- *lemma* sequentially_complete.seq_of_cau_filter_mem_set_seq
- \- *def* sequentially_complete.set_seq_of_cau_filter
- \- *lemma* sequentially_complete.set_seq_of_cau_filter_inhabited
- \- *lemma* sequentially_complete.set_seq_of_cau_filter_mem_sets
- \- *lemma* sequentially_complete.set_seq_of_cau_filter_monotone'
- \- *lemma* sequentially_complete.set_seq_of_cau_filter_monotone
- \- *lemma* sequentially_complete.set_seq_of_cau_filter_spec
- \- *lemma* sequentially_complete.tendsto_div
- \- *lemma* tendsto_limit

Modified src/analysis/normed_space/basic.lean


Modified src/data/real/cau_seq_filter.lean


Modified src/measure_theory/borel_space.lean


Modified src/topology/continuity.lean
- \+/\- *def* continuous_at_within
- \+/\- *theorem* continuous_at_within_iff_continuous_at_restrict
- \+/\- *theorem* continuous_at_within_univ

Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/sequences.lean




## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/8e4aafa)
feat(analysis/metric): convergence wrt nhds_within
#### Estimated changes
Modified analysis/metric_space.lean
- \+ *theorem* metric.mem_nhds_within
- \+ *theorem* metric.ptendsto_nhds_within
- \+ *theorem* metric.rtendsto'_nhds_within
- \+ *theorem* metric.rtendsto_nhds_within
- \+ *theorem* metric.tendsto_nhds_within



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/f5d73bd)
feat(analysis/topology/continuity): add some variations
#### Estimated changes
Added analysis/metric_space.lean
- \+ *theorem* abs_dist
- \+ *theorem* abs_dist_sub_le
- \+ *def* ball
- \+ *theorem* ball_disjoint
- \+ *theorem* ball_disjoint_same
- \+ *theorem* ball_eq_empty_iff_nonpos
- \+ *theorem* ball_half_subset
- \+ *theorem* ball_mem_nhds
- \+ *theorem* ball_subset
- \+ *theorem* ball_subset_ball
- \+ *theorem* ball_subset_closed_ball
- \+ *lemma* cauchy_of_metric
- \+ *theorem* cauchy_seq_metric'
- \+ *theorem* cauchy_seq_metric
- \+ *def* closed_ball
- \+ *theorem* continuous_dist'
- \+ *theorem* continuous_dist
- \+ *theorem* continuous_of_metric
- \+ *theorem* continuous_topo_metric
- \+ *lemma* countable_closure_of_compact
- \+ *theorem* dist_comm
- \+ *lemma* dist_eq_edist
- \+ *lemma* dist_eq_nndist
- \+ *theorem* dist_eq_zero
- \+ *theorem* dist_le_zero
- \+ *theorem* dist_mem_uniformity
- \+ *theorem* dist_nonneg
- \+ *lemma* dist_pi_def
- \+ *theorem* dist_pos
- \+ *theorem* dist_self
- \+ *theorem* dist_triangle
- \+ *theorem* dist_triangle_left
- \+ *theorem* dist_triangle_right
- \+ *theorem* edist_dist
- \+ *lemma* edist_eq_dist
- \+ *lemma* edist_eq_nndist
- \+ *lemma* edist_ne_top
- \+ *theorem* eq_of_dist_eq_zero
- \+ *theorem* eq_of_forall_dist_le
- \+ *theorem* eq_of_nndist_eq_zero
- \+ *theorem* exists_ball_subset_ball
- \+ *theorem* exists_delta_of_continuous
- \+ *lemma* finite_cover_balls_of_compact
- \+ *theorem* is_closed_ball
- \+ *theorem* is_open_ball
- \+ *theorem* is_open_metric
- \+ *lemma* lebesgue_number_lemma_of_metric
- \+ *lemma* lebesgue_number_lemma_of_metric_sUnion
- \+ *theorem* mem_ball'
- \+ *theorem* mem_ball
- \+ *theorem* mem_ball_comm
- \+ *theorem* mem_ball_self
- \+ *theorem* mem_closed_ball
- \+ *theorem* mem_closure_iff'
- \+ *theorem* mem_nhds_iff_metric
- \+ *theorem* mem_uniformity_dist
- \+ *lemma* mem_uniformity_dist_edist
- \+ *def* metric_space.induced
- \+ *def* metric_space.replace_uniformity
- \+ *def* metric_space.uniform_space_of_dist
- \+ *lemma* nhds_comap_dist
- \+ *theorem* nhds_eq_metric
- \+ *def* nndist
- \+ *theorem* nndist_comm
- \+ *lemma* nndist_eq_dist
- \+ *lemma* nndist_eq_edist
- \+ *theorem* nndist_eq_zero
- \+ *lemma* nndist_self
- \+ *theorem* nndist_triangle
- \+ *theorem* nndist_triangle_left
- \+ *theorem* nndist_triangle_right
- \+ *theorem* pos_of_mem_ball
- \+ *theorem* real.dist_0_eq_abs
- \+ *theorem* real.dist_eq
- \+ *lemma* second_countable_of_separable_metric_space
- \+ *theorem* subtype.dist_eq
- \+ *theorem* swap_dist
- \+ *theorem* tendsto_at_top_metric
- \+ *theorem* tendsto_dist
- \+ *lemma* tendsto_iff_dist_tendsto_zero
- \+ *theorem* tendsto_nhds_of_metric
- \+ *theorem* tendsto_nhds_topo_metric
- \+ *theorem* totally_bounded_of_metric
- \+ *theorem* uniform_continuous_dist'
- \+ *theorem* uniform_continuous_dist
- \+ *theorem* uniform_continuous_of_metric
- \+ *theorem* uniform_embedding_of_metric
- \+ *theorem* uniformity_dist'
- \+ *theorem* uniformity_dist
- \+ *theorem* uniformity_edist'
- \+ *theorem* uniformity_edist
- \+ *theorem* zero_eq_dist
- \+ *theorem* zero_eq_nndist

Added data/real/cau_seq_filter.lean
- \+ *lemma* cau_seq_iff_cauchy_seq
- \+ *lemma* cauchy_of_filter_cauchy
- \+ *theorem* complete_of_cauchy_seq_tendsto
- \+ *lemma* filter_cauchy_of_cauchy
- \+ *lemma* sequentially_complete.cauchy_seq_of_dist_tendsto_0
- \+ *lemma* sequentially_complete.le_nhds_cau_filter_lim
- \+ *lemma* sequentially_complete.mono_of_mono_succ
- \+ *lemma* sequentially_complete.seq_of_cau_filter_is_cauchy'
- \+ *lemma* sequentially_complete.seq_of_cau_filter_is_cauchy
- \+ *lemma* sequentially_complete.seq_of_cau_filter_mem_set_seq
- \+ *def* sequentially_complete.set_seq_of_cau_filter
- \+ *lemma* sequentially_complete.set_seq_of_cau_filter_inhabited
- \+ *lemma* sequentially_complete.set_seq_of_cau_filter_mem_sets
- \+ *lemma* sequentially_complete.set_seq_of_cau_filter_monotone'
- \+ *lemma* sequentially_complete.set_seq_of_cau_filter_monotone
- \+ *lemma* sequentially_complete.set_seq_of_cau_filter_spec
- \+ *lemma* sequentially_complete.tendsto_div
- \+ *lemma* tendsto_limit

Modified src/analysis/exponential.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/data/padics/hensel.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/topological_structures.lean


Modified src/topology/compact_open.lean


Modified src/topology/continuity.lean
- \+ *def* continuous_at
- \+/\- *lemma* continuous_at_iff_ultrafilter
- \+ *lemma* continuous_at_subtype_val
- \+ *def* continuous_at_within
- \+ *theorem* continuous_at_within_iff_continuous_at_restrict
- \+ *theorem* continuous_at_within_iff_ptendsto_res
- \+ *theorem* continuous_at_within_univ
- \+ *lemma* continuous_iff_continuous_at
- \- *lemma* continuous_iff_tendsto
- \+ *def* continuous_on
- \+ *theorem* continuous_on_iff'
- \+ *theorem* continuous_on_iff
- \+ *theorem* continuous_on_iff_continuous_restrict
- \+ *lemma* list.continuous_at_length
- \- *lemma* list.tendsto_length
- \+ *lemma* open_dom_of_pcontinuous
- \+ *def* pcontinuous
- \+ *lemma* pcontinuous_iff'
- \- *lemma* tendsto_subtype_val
- \+ *lemma* vector.continuous_at_remove_nth
- \- *lemma* vector.tendsto_remove_nth

Modified src/topology/instances/complex.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/completion.lean




## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/e0b8253)
feat (analysis/topology/topological_space): properties of nhds, nhds_within
#### Estimated changes
Modified src/topology/basic.lean
- \+ *theorem* all_mem_nhds
- \+ *theorem* all_mem_nhds_filter
- \+ *theorem* map_nhds_induced_of_surjective
- \+ *lemma* map_nhds_within
- \+ *theorem* mem_nhds_induced
- \+ *theorem* mem_nhds_subtype
- \+ *theorem* mem_nhds_within
- \+ *theorem* mem_nhds_within_subtype
- \+ *theorem* nhds_induced
- \+ *theorem* nhds_subtype
- \+ *def* nhds_within
- \+ *theorem* nhds_within_empty
- \+ *theorem* nhds_within_eq
- \+ *theorem* nhds_within_eq_map_subtype_val
- \+ *theorem* nhds_within_eq_nhds_within
- \+ *theorem* nhds_within_inter'
- \+ *theorem* nhds_within_inter
- \+ *theorem* nhds_within_mono
- \+ *theorem* nhds_within_restrict
- \+ *theorem* nhds_within_subtype
- \+ *theorem* nhds_within_union
- \+ *theorem* nhds_within_univ
- \+ *theorem* nhs_within_eq_of_open
- \+ *theorem* principal_subtype
- \+ *theorem* ptendsto'_nhds
- \+ *theorem* ptendsto_nhds
- \+ *theorem* rtendsto'_nhds
- \+ *theorem* rtendsto_nhds
- \+ *theorem* tendsto_at_within_iff_subtype
- \+ *theorem* tendsto_if_nhds_within
- \+ *theorem* tendsto_nhds
- \- *lemma* tendsto_nhds



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/a96fa3b)
feat(order/filter): convergence for relations and partial functions
#### Estimated changes
Modified src/data/pfun.lean
- \+/\- *def* pfun.core
- \+/\- *def* pfun.graph'
- \+/\- *lemma* pfun.mem_core
- \+/\- *lemma* pfun.mem_core_res
- \+/\- *lemma* pfun.preimage_as_subtype
- \+/\- *theorem* roption.mem_restrict

Renamed data/rel.lean to src/data/rel.lean


Modified src/order/filter.lean
- \+ *theorem* filter.le_map_comap_of_surjective'
- \+ *theorem* filter.le_map_comap_of_surjective
- \+ *theorem* filter.map_comap_of_surjective'
- \+ *theorem* filter.map_comap_of_surjective
- \+ *theorem* filter.mem_inf_principal
- \+ *def* filter.mem_pmap
- \+ *def* filter.mem_rcomap'
- \+ *theorem* filter.mem_rmap
- \+ *def* filter.pcomap'
- \+ *def* filter.pmap
- \+ *theorem* filter.pmap_res
- \+ *def* filter.ptendsto'
- \+ *theorem* filter.ptendsto'_def
- \+ *theorem* filter.ptendsto'_of_ptendsto
- \+ *def* filter.ptendsto
- \+ *theorem* filter.ptendsto_def
- \+ *theorem* filter.ptendsto_iff_rtendsto
- \+ *theorem* filter.ptendsto_of_ptendsto'
- \+ *def* filter.rcomap'
- \+ *lemma* filter.rcomap'_compose
- \+ *theorem* filter.rcomap'_rcomap'
- \+ *theorem* filter.rcomap'_sets
- \+ *def* filter.rcomap
- \+ *lemma* filter.rcomap_compose
- \+ *theorem* filter.rcomap_rcomap
- \+ *theorem* filter.rcomap_sets
- \+ *def* filter.rmap
- \+ *lemma* filter.rmap_compose
- \+ *theorem* filter.rmap_rmap
- \+ *theorem* filter.rmap_sets
- \+ *def* filter.rtendsto'
- \+ *theorem* filter.rtendsto'_def
- \+ *def* filter.rtendsto
- \+ *theorem* filter.rtendsto_def
- \+ *theorem* filter.rtendsto_iff_le_comap
- \+ *lemma* filter.tendsto_if
- \+ *theorem* filter.tendsto_iff_ptendsto
- \+ *theorem* filter.tendsto_iff_ptendsto_univ
- \+ *theorem* filter.tendsto_iff_rtendsto'
- \+ *theorem* filter.tendsto_iff_rtendsto



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/4444464)
feat(data/pfun): add restrict, preimage, core, etc.
#### Estimated changes
Modified src/data/pfun.lean
- \+ *theorem* pfun.as_subtype_eq_of_mem
- \+ *lemma* pfun.compl_dom_subset_core
- \+ *def* pfun.core
- \+ *lemma* pfun.core_def
- \+ *lemma* pfun.core_eq
- \+ *lemma* pfun.core_inter
- \+ *lemma* pfun.core_mono
- \+ *lemma* pfun.core_res
- \+ *lemma* pfun.core_restrict
- \+ *theorem* pfun.dom_eq
- \+ *def* pfun.graph'
- \+ *def* pfun.image
- \+ *lemma* pfun.image_def
- \+ *lemma* pfun.image_inter
- \+ *lemma* pfun.image_mono
- \+ *lemma* pfun.image_union
- \+ *lemma* pfun.mem_core
- \+ *lemma* pfun.mem_core_res
- \+ *theorem* pfun.mem_dom
- \+ *lemma* pfun.mem_image
- \+ *def* pfun.mem_preimage
- \+ *theorem* pfun.mem_res
- \+ *theorem* pfun.mem_restrict
- \+ *def* pfun.preimage
- \+ *lemma* pfun.preimage_as_subtype
- \+ *lemma* pfun.preimage_def
- \+ *lemma* pfun.preimage_eq
- \+ *lemma* pfun.preimage_inter
- \+ *lemma* pfun.preimage_mono
- \+ *lemma* pfun.preimage_subset_core
- \+ *lemma* pfun.preimage_subset_dom
- \+ *lemma* pfun.preimage_union
- \+ *lemma* pfun.preimage_univ
- \+ *def* pfun.res
- \+ *theorem* pfun.res_univ
- \+ *theorem* roption.mem_eq
- \+ *theorem* roption.mem_restrict



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/cae5c8b)
fix(data/rel): make composition local notation
#### Estimated changes
Modified data/rel.lean




## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/4779af7)
feat(data/rel): a type for binary relations
#### Estimated changes
Added data/rel.lean
- \+ *def* function.graph
- \+ *def* rel.codom
- \+ *lemma* rel.codom_inv
- \+ *def* rel.comp
- \+ *lemma* rel.comp_assoc
- \+ *lemma* rel.comp_left_id
- \+ *lemma* rel.comp_right_id
- \+ *def* rel.core
- \+ *lemma* rel.core_comp
- \+ *lemma* rel.core_id
- \+ *lemma* rel.core_inter
- \+ *lemma* rel.core_mono
- \+ *lemma* rel.core_union
- \+ *lemma* rel.core_univ
- \+ *def* rel.dom
- \+ *lemma* rel.dom_inv
- \+ *def* rel.image
- \+ *lemma* rel.image_comp
- \+ *lemma* rel.image_id
- \+ *lemma* rel.image_inter
- \+ *lemma* rel.image_mono
- \+ *lemma* rel.image_union
- \+ *lemma* rel.image_univ
- \+ *def* rel.inv
- \+ *lemma* rel.inv_comp
- \+ *lemma* rel.inv_def
- \+ *lemma* rel.inv_id
- \+ *lemma* rel.inv_inv
- \+ *lemma* rel.mem_core
- \+ *lemma* rel.mem_image
- \+ *lemma* rel.mem_preimage
- \+ *def* rel.preimage
- \+ *lemma* rel.preimage_comp
- \+ *lemma* rel.preimage_def
- \+ *lemma* rel.preimage_id
- \+ *lemma* rel.preimage_inter
- \+ *lemma* rel.preimage_mono
- \+ *lemma* rel.preimage_union
- \+ *lemma* rel.preimage_univ
- \+ *def* rel.restrict_domain
- \+ *def* rel
- \+ *lemma* set.image_eq
- \+ *lemma* set.preimage_eq
- \+ *lemma* set.preimage_eq_core



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/126d573)
feat(data/set/basic,logic/function): small additions and renamings
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *theorem* set.inter_subset
- \+ *lemma* set.subtype.val_range
- \- *lemma* set.subtype_val_image
- \- *lemma* set.subtype_val_range
- \+ *theorem* subtype.image_preimage_val
- \+ *theorem* subtype.preimage_val_eq_preimage_val_iff
- \+ *lemma* subtype.val_image
- \+ *theorem* subtype.val_image_subset
- \+ *theorem* subtype.val_image_univ
- \+ *lemma* subtype.val_range

Modified src/logic/function.lean
- \+ *def* function.restrict
- \+ *theorem* function.restrict_eq

Modified src/order/filter.lean


Modified src/topology/continuity.lean




## [2019-02-07 22:32:47](https://github.com/leanprover-community/mathlib/commit/1ed7ad1)
feat(algebra/archimedean): abs_sub_lt_one_of_floor_eq_floor ([#693](https://github.com/leanprover-community/mathlib/pull/693))
* abs_diff_lt_one_of_floor_eq_floor
* better name
#### Estimated changes
Modified src/algebra/archimedean.lean
- \+ *lemma* abs_sub_lt_one_of_floor_eq_floor



## [2019-02-07 19:37:17+01:00](https://github.com/leanprover-community/mathlib/commit/177b5eb)
feat(linear_algebra): dimension of the base field is 1
#### Estimated changes
Modified src/algebra/module.lean


Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis_singleton_one

Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_of_field



## [2019-02-07 19:36:51+01:00](https://github.com/leanprover-community/mathlib/commit/0f24030)
refactor(src/data/finset): supr/infi as a directed supr/infi of finite inf/sup
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.inf_congr
- \+ *theorem* finset.sup_congr
- \+ *lemma* lattice.infi_eq_infi_finset
- \+ *lemma* lattice.supr_eq_supr_finset
- \+ *lemma* set.Inter_eq_Inter_finset
- \+ *lemma* set.Union_eq_Union_finset

Modified src/data/set/lattice.lean
- \+ *theorem* set.monotone_inter
- \+ *theorem* set.monotone_set_of
- \+ *theorem* set.monotone_union

Modified src/order/filter.lean
- \- *lemma* filter.Inf_sets_eq_finite
- \- *lemma* filter.binfi_sup_eq
- \+/\- *lemma* filter.infi_sets_eq'
- \+ *lemma* filter.infi_sets_eq_finite
- \+/\- *lemma* filter.infi_sup_eq
- \+/\- *lemma* filter.supr_join
- \- *lemma* lattice.Inf_eq_finite_sets
- \- *lemma* lattice.inf_left_comm
- \- *lemma* lattice.infi_empty_finset
- \- *lemma* lattice.infi_insert_finset
- \- *theorem* set.monotone_inter
- \- *theorem* set.monotone_set_of

Modified src/order/lattice.lean
- \+ *lemma* lattice.directed_of_inf
- \+ *lemma* lattice.directed_of_sup
- \+ *lemma* lattice.inf_left_comm
- \+ *lemma* lattice.sup_left_comm



## [2019-02-07 15:56:26+01:00](https://github.com/leanprover-community/mathlib/commit/eeed321)
chore(linear_algebra/basic): relate map/comap/ker/range/comp with 0 and smul; use map/comap Galois connection
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *theorem* linear_map.comp_assoc
- \+/\- *theorem* linear_map.comp_id
- \+ *theorem* linear_map.comp_smul
- \+ *theorem* linear_map.comp_zero
- \+/\- *theorem* linear_map.id_comp
- \+ *lemma* linear_map.ker_smul'
- \+ *lemma* linear_map.ker_smul
- \+ *lemma* linear_map.range_le_bot_iff
- \+ *lemma* linear_map.range_smul'
- \+ *lemma* linear_map.range_smul
- \+ *theorem* linear_map.range_zero
- \+ *theorem* linear_map.smul_comp
- \+ *theorem* linear_map.zero_comp
- \+ *lemma* submodule.comap_inf
- \+ *lemma* submodule.comap_infi
- \+ *lemma* submodule.comap_smul'
- \+ *lemma* submodule.comap_smul
- \+ *lemma* submodule.comap_zero
- \+ *lemma* submodule.gc_map_comap
- \+ *lemma* submodule.map_smul'
- \+ *lemma* submodule.map_smul
- \+ *lemma* submodule.map_sup
- \+ *lemma* submodule.map_supr
- \+ *lemma* submodule.map_zero



## [2019-02-07 14:58:25+01:00](https://github.com/leanprover-community/mathlib/commit/e98999e)
chore(algebra/pi_instances): generalize pi.list/multiset/finset_prod/sum_apply to dependent types
#### Estimated changes
Modified src/algebra/pi_instances.lean
- \+/\- *lemma* pi.finset_prod_apply
- \+/\- *lemma* pi.list_prod_apply
- \+/\- *lemma* pi.multiset_prod_apply



## [2019-02-07 14:58:25+01:00](https://github.com/leanprover-community/mathlib/commit/ad7ef86)
refactor(set_theory/cardinal): split up mk_Union_le_mk_sigma, add mk_Union_eq_mk_sigma; add equiv congruence for subtype
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.set_congr
- \+ *def* equiv.subtype_congr

Modified src/data/set/lattice.lean
- \+ *lemma* set.bijective_sigma_to_Union
- \+ *lemma* set.injective_sigma_to_Union
- \+ *def* set.sigma_to_Union
- \+ *lemma* set.surjective_sigma_to_Union

Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.mk_Union_eq_sum_mk
- \+/\- *theorem* cardinal.mk_eq_of_injective



## [2019-02-07 13:13:39+01:00](https://github.com/leanprover-community/mathlib/commit/8a1de24)
feat(data/{list/alist,finmap}): implicit key type ([#662](https://github.com/leanprover-community/mathlib/pull/662))
* feat(data/{list/alist,finmap}): implicit key type
Make the key type α implicit in both alist and finmap. This brings these
types into line with the underlying sigma and simplifies usage since α
is inferred from the value function type β : α → Type v.
* doc(data/list/alist): alist is stored as a linked list
#### Estimated changes
Modified src/data/finmap.lean
- \+/\- *def* alist.to_finmap
- \+/\- *theorem* alist.to_finmap_entries
- \+/\- *theorem* alist.to_finmap_eq
- \+/\- *theorem* finmap.empty_to_finmap
- \+/\- *def* finmap.erase
- \+/\- *theorem* finmap.erase_to_finmap
- \+/\- *theorem* finmap.ext
- \+/\- *def* finmap.extract
- \+/\- *theorem* finmap.extract_eq_lookup_erase
- \+/\- *def* finmap.insert
- \+/\- *theorem* finmap.insert_entries_of_neg
- \+/\- *theorem* finmap.insert_of_pos
- \+/\- *theorem* finmap.insert_to_finmap
- \+/\- *def* finmap.keys
- \+/\- *theorem* finmap.keys_empty
- \+/\- *theorem* finmap.keys_erase
- \+/\- *theorem* finmap.keys_erase_to_finset
- \+/\- *theorem* finmap.keys_ext
- \+/\- *theorem* finmap.keys_replace
- \+/\- *theorem* finmap.keys_val
- \+/\- *theorem* finmap.lift_on_to_finmap
- \+/\- *def* finmap.lookup
- \+/\- *theorem* finmap.lookup_is_some
- \+/\- *theorem* finmap.lookup_to_finmap
- \+/\- *theorem* finmap.mem_def
- \+/\- *theorem* finmap.mem_erase
- \+/\- *theorem* finmap.mem_insert
- \+/\- *theorem* finmap.mem_keys
- \+/\- *theorem* finmap.mem_replace
- \+/\- *theorem* finmap.mem_to_finmap
- \+/\- *theorem* finmap.not_mem_empty
- \+/\- *theorem* finmap.not_mem_empty_entries
- \+/\- *def* finmap.replace
- \+/\- *theorem* finmap.replace_to_finmap
- \+/\- *def* finmap.singleton
- \+/\- *structure* finmap

Modified src/data/list/alist.lean
- \+/\- *def* alist.erase
- \+/\- *theorem* alist.ext
- \+/\- *def* alist.extract
- \+/\- *theorem* alist.extract_eq_lookup_erase
- \+/\- *def* alist.foldl
- \+/\- *def* alist.insert
- \+/\- *theorem* alist.insert_entries_of_neg
- \+/\- *theorem* alist.insert_of_pos
- \+/\- *def* alist.keys
- \+/\- *theorem* alist.keys_empty
- \+/\- *theorem* alist.keys_erase
- \+/\- *theorem* alist.keys_insert
- \+/\- *theorem* alist.keys_nodup
- \+/\- *theorem* alist.keys_replace
- \+/\- *def* alist.lookup
- \+/\- *theorem* alist.lookup_is_some
- \+/\- *theorem* alist.mem_def
- \+/\- *theorem* alist.mem_erase
- \+/\- *theorem* alist.mem_insert
- \+/\- *theorem* alist.mem_keys
- \+/\- *theorem* alist.mem_of_perm
- \+/\- *theorem* alist.mem_replace
- \+/\- *theorem* alist.not_mem_empty
- \+/\- *theorem* alist.not_mem_empty_entries
- \+/\- *theorem* alist.perm_erase
- \+/\- *theorem* alist.perm_insert
- \+/\- *theorem* alist.perm_lookup
- \+/\- *theorem* alist.perm_replace
- \+/\- *def* alist.replace
- \+/\- *def* alist.singleton
- \+/\- *structure* alist



## [2019-02-07 13:02:53+01:00](https://github.com/leanprover-community/mathlib/commit/46d1009)
feat(analysis/metric_space): Isometries ([#657](https://github.com/leanprover-community/mathlib/pull/657))
#### Estimated changes
Added src/topology/metric_space/isometry.lean
- \+ *lemma* emetric.isometry.diam_image
- \+ *lemma* isometric.coe_eq_to_equiv
- \+ *lemma* isometric.coe_eq_to_homeomorph
- \+ *lemma* isometric.image_symm
- \+ *lemma* isometric.preimage_symm
- \+ *lemma* isometric.range_coe
- \+ *lemma* isometric.self_comp_symm
- \+ *lemma* isometric.symm_comp_self
- \+ *lemma* isometric.to_homeomorph_to_equiv
- \+ *structure* isometric
- \+ *theorem* isometry.comp
- \+ *lemma* isometry.continuous
- \+ *theorem* isometry.dist_eq
- \+ *theorem* isometry.edist_eq
- \+ *lemma* isometry.injective
- \+ *lemma* isometry.inv
- \+ *lemma* isometry.isometric_on_range
- \+ *lemma* isometry.isometric_on_range_apply
- \+ *theorem* isometry.uniform_embedding
- \+ *def* isometry
- \+ *lemma* isometry_emetric_iff_metric
- \+ *lemma* isometry_id
- \+ *theorem* isometry_subsingleton
- \+ *lemma* isometry_subtype_val
- \+ *lemma* metric.isometry.diam_image



## [2019-02-07 10:22:13](https://github.com/leanprover-community/mathlib/commit/8911b8c)
feat(algebra/order_functions): max_lt_max and min_lt_min ([#692](https://github.com/leanprover-community/mathlib/pull/692))
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* max_lt_max
- \+ *lemma* min_lt_min



## [2019-02-06 20:15:47](https://github.com/leanprover-community/mathlib/commit/51f80a3)
feat(data/quot): quotient.ind' ([#691](https://github.com/leanprover-community/mathlib/pull/691))
* feat(data/quot): quotient.ind'
* correct elaborator tag; theorems not definitions
#### Estimated changes
Modified src/data/quot.lean




## [2019-02-06 10:58:04+01:00](https://github.com/leanprover-community/mathlib/commit/9615b38)
feat(data/real): completeness criterion for Cauchy sequences (closes [#654](https://github.com/leanprover-community/mathlib/pull/654))
#### Estimated changes
Modified src/data/real/cau_seq_filter.lean
- \+/\- *theorem* complete_of_cauchy_seq_tendsto
- \+ *theorem* emetric.complete_of_convergent_controlled_sequences
- \+ *theorem* metric.complete_of_convergent_controlled_sequences
- \+ *lemma* sequentially_complete.FB_lim
- \+ *lemma* sequentially_complete.FB_pos
- \+ *lemma* sequentially_complete.F_lim
- \+ *lemma* sequentially_complete.F_pos
- \- *lemma* sequentially_complete.cauchy_seq_of_dist_tendsto_0
- \+/\- *lemma* sequentially_complete.le_nhds_cau_filter_lim
- \+ *lemma* sequentially_complete.seq_of_cau_filter_bound
- \- *lemma* sequentially_complete.seq_of_cau_filter_is_cauchy'
- \+/\- *lemma* sequentially_complete.seq_of_cau_filter_mem_set_seq
- \+/\- *lemma* sequentially_complete.set_seq_of_cau_filter_inhabited
- \+/\- *lemma* sequentially_complete.set_seq_of_cau_filter_mem_sets



## [2019-02-06 10:36:56+01:00](https://github.com/leanprover-community/mathlib/commit/3ac7967)
feat(analysis/metric_space): add premetric spaces (closes [#652](https://github.com/leanprover-community/mathlib/pull/652))
#### Estimated changes
Added src/topology/metric_space/premetric_space.lean
- \+ *def* premetric.dist_setoid
- \+ *lemma* premetric.metric_quot_dist_eq



## [2019-02-06 10:29:32+01:00](https://github.com/leanprover-community/mathlib/commit/e93fa30)
feat(category/fold): `foldl` and `foldr` for `traversable` structures ([#376](https://github.com/leanprover-community/mathlib/pull/376))
#### Estimated changes
Added src/category/fold.lean
- \+ *def* monoid.foldl.mk
- \+ *def* monoid.foldl.of_free_monoid
- \+ *def* monoid.foldl
- \+ *def* monoid.foldr.get
- \+ *def* monoid.foldr.mk
- \+ *def* monoid.foldr.of_free_monoid
- \+ *def* monoid.foldr
- \+ *def* monoid.mfoldl.mk
- \+ *def* monoid.mfoldl.of_free_monoid
- \+ *def* monoid.mfoldl
- \+ *def* monoid.mfoldr.get
- \+ *def* monoid.mfoldr.mk
- \+ *def* monoid.mfoldr.of_free_monoid
- \+ *def* monoid.mfoldr
- \+ *def* traversable.fold_map
- \+ *lemma* traversable.fold_map_hom
- \+ *lemma* traversable.fold_map_hom_free
- \+ *lemma* traversable.fold_map_map
- \+ *lemma* traversable.fold_mfoldl_cons
- \+ *lemma* traversable.fold_mfoldr_cons
- \+ *lemma* traversable.foldl.of_free_monoid_comp_free_mk
- \+ *def* traversable.foldl
- \+ *theorem* traversable.foldl_map
- \+ *lemma* traversable.foldl_to_list
- \+ *lemma* traversable.foldr.of_free_monoid_comp_free_mk
- \+ *lemma* traversable.foldr.unop_of_free_monoid
- \+ *def* traversable.foldr
- \+ *theorem* traversable.foldr_map
- \+ *lemma* traversable.foldr_to_list
- \+ *def* traversable.free.map
- \+ *lemma* traversable.free.map_eq_map
- \+ *def* traversable.free.mk
- \+ *def* traversable.length
- \+ *theorem* traversable.length_to_list
- \+ *def* traversable.map_fold
- \+ *lemma* traversable.mfoldl.of_free_monoid_comp_free_mk
- \+ *def* traversable.mfoldl
- \+ *theorem* traversable.mfoldl_map
- \+ *lemma* traversable.mfoldl_to_list
- \+ *lemma* traversable.mfoldr.of_free_monoid_comp_free_mk
- \+ *lemma* traversable.mfoldr.unop_of_free_monoid
- \+ *def* traversable.mfoldr
- \+ *theorem* traversable.mfoldr_map
- \+ *lemma* traversable.mfoldr_to_list
- \+ *def* traversable.to_list
- \+ *theorem* traversable.to_list_eq_self
- \+ *lemma* traversable.to_list_map
- \+ *lemma* traversable.to_list_spec



## [2019-02-06 09:59:29+01:00](https://github.com/leanprover-community/mathlib/commit/c82243a)
feat(analysis/normed_space): bounded linear maps with the operator norm form a normed space (closes [#680](https://github.com/leanprover-community/mathlib/pull/680))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *structure* normed_space.core

Added src/analysis/normed_space/operator_norm.lean
- \+ *theorem* bounded_by_operator_norm
- \+ *lemma* bounded_by_operator_norm_on_unit_ball
- \+ *lemma* bounded_by_operator_norm_on_unit_vector
- \+ *def* bounded_linear_maps
- \+ *lemma* exists_bound'
- \+ *lemma* exists_bound
- \+ *theorem* ext
- \+ *lemma* norm_of_unit_ball_bdd_above
- \+ *lemma* operator_norm_bounded_by
- \+ *theorem* operator_norm_homogeneous
- \+ *lemma* operator_norm_nonneg
- \+ *theorem* operator_norm_triangle
- \+ *theorem* operator_norm_zero_iff
- \+ *lemma* zero_in_im_ball

Modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* lattice.cSup_intro'



## [2019-02-05 19:47:08](https://github.com/leanprover-community/mathlib/commit/d5a1b46)
to_nat_le_to_nat ([#685](https://github.com/leanprover-community/mathlib/pull/685))
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *theorem* int.to_nat_le_to_nat



## [2019-02-05 14:26:19-05:00](https://github.com/leanprover-community/mathlib/commit/9f79d2e)
fix(tactic/h_generalize): fix name resolution in h_generalize ([#688](https://github.com/leanprover-community/mathlib/pull/688))
#### Estimated changes
Modified src/tactic/interactive.lean




## [2019-02-05 14:13:55-05:00](https://github.com/leanprover-community/mathlib/commit/a0d8ae1)
feat(tactic/replaceable): supplement `def_replacer` with attribute `replaceable`
#### Estimated changes
Modified src/data/string.lean
- \- *def* string.map_tokens

Added src/data/string/defs.lean
- \+ *def* string.map_tokens
- \+ *def* string.over_list

Modified src/meta/expr.lean
- \+ *def* name.append_suffix

Modified src/tactic/replacer.lean




## [2019-02-04 19:35:17-05:00](https://github.com/leanprover-community/mathlib/commit/178c09d)
feat(natural_isomorphism): componentwise isos are isos ([#671](https://github.com/leanprover-community/mathlib/pull/671))
#### Estimated changes
Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.is_iso.hom_inv_id
- \- *def* category_theory.is_iso.hom_inv_id
- \+ *lemma* category_theory.is_iso.hom_inv_id_assoc
- \+ *lemma* category_theory.is_iso.inv_hom_id
- \- *def* category_theory.is_iso.inv_hom_id
- \+ *lemma* category_theory.is_iso.inv_hom_id_assoc

Modified src/category_theory/natural_isomorphism.lean




## [2019-02-04 20:49:37](https://github.com/leanprover-community/mathlib/commit/9a8f1b0)
feat(algebra/group_power): gpow_add_one ([#683](https://github.com/leanprover-community/mathlib/pull/683))
* feat(algebra/group_power): gpow_add_one
* feat(data/nat//basic): int.coe_nat_abs
#### Estimated changes
Modified src/algebra/group_power.lean
- \+ *theorem* add_one_gsmul
- \+ *theorem* gpow_add_one
- \+ *theorem* gpow_one_add
- \+ *theorem* one_add_gsmul

Modified src/data/int/basic.lean
- \+ *theorem* int.coe_nat_abs



## [2019-02-04 19:00:17](https://github.com/leanprover-community/mathlib/commit/5395232)
remove simp on set_coe_eq_subtype ([#682](https://github.com/leanprover-community/mathlib/pull/682))
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* set.set_coe_eq_subtype

Modified src/group_theory/sylow.lean


Modified src/tactic/subtype_instance.lean




## [2019-02-04 10:43:58+01:00](https://github.com/leanprover-community/mathlib/commit/5e5f1e2)
fix(data/*/Ico): succ_top is too aggressive as a simp lemma ([#678](https://github.com/leanprover-community/mathlib/pull/678))
#### Estimated changes
Modified src/data/finset.lean
- \+/\- *theorem* finset.Ico.succ_top

Modified src/data/list/basic.lean
- \+/\- *theorem* list.Ico.succ_top

Modified src/data/multiset.lean
- \+/\- *theorem* multiset.Ico.succ_top



## [2019-02-03 22:31:10](https://github.com/leanprover-community/mathlib/commit/2539251)
feat(data/nat/cast): abs_cast
#### Estimated changes
Modified src/data/nat/cast.lean
- \+ *theorem* nat.abs_cast



## [2019-02-03 17:00:41-05:00](https://github.com/leanprover-community/mathlib/commit/d01e523)
feat(category_theory/kleisli): monoids, const applicative functor and kleisli categories ([#660](https://github.com/leanprover-community/mathlib/pull/660))
* feat(category_theory/kleisli): monoids, const applicative functor and
kleisli categories
#### Estimated changes
Modified src/algebra/group.lean
- \+ *lemma* free_add_monoid.add_def
- \+ *lemma* free_add_monoid.zero_def
- \+ *def* free_add_monoid
- \+ *lemma* free_monoid.mul_def
- \+ *lemma* free_monoid.one_def
- \+ *def* free_monoid

Modified src/category/applicative.lean


Modified src/category/basic.lean
- \+ *def* fish
- \+ *lemma* fish_assoc
- \+ *lemma* fish_pipe
- \+ *lemma* fish_pure

Modified src/category/functor.lean
- \+ *def* functor.add_const.mk
- \+ *def* functor.add_const.run
- \+ *def* functor.const.mk'

Modified src/category/traversable/basic.lean


Modified src/category_theory/category.lean
- \+ *lemma* category_theory.End.mul_def
- \+ *lemma* category_theory.End.one_def
- \+/\- *def* category_theory.End

Added src/category_theory/instances/kleisli.lean
- \+ *lemma* category_theory.Kleisli.comp_def
- \+ *lemma* category_theory.Kleisli.id_def
- \+ *def* category_theory.Kleisli.mk
- \+ *def* category_theory.Kleisli

Modified src/category_theory/instances/rings.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.op_inj
- \+ *lemma* category_theory.opposite.op_mul
- \+ *lemma* category_theory.opposite.op_one
- \+ *lemma* category_theory.opposite.unop_mul
- \+ *lemma* category_theory.opposite.unop_one
- \+ *lemma* category_theory.unop_inj

Modified src/data/fintype.lean




## [2019-02-03 17:01:45+01:00](https://github.com/leanprover-community/mathlib/commit/f5bd340)
cleanup(*): removing uses of bare `have` ([#676](https://github.com/leanprover-community/mathlib/pull/676))
#### Estimated changes
Modified src/data/int/basic.lean


Modified src/linear_algebra/basic.lean




## [2019-02-03 02:14:48-05:00](https://github.com/leanprover-community/mathlib/commit/544f35c)
Update README.md
#### Estimated changes
Modified README.md




## [2019-02-03 02:06:28](https://github.com/leanprover-community/mathlib/commit/b3e1e6f)
fix(README): update URL for build status icon ([#681](https://github.com/leanprover-community/mathlib/pull/681))
#### Estimated changes
Modified README.md




## [2019-02-03 01:08:36](https://github.com/leanprover-community/mathlib/commit/044b6fa)
feat(algebra/euclidean_domain): discrete field to euclidean domain ([#674](https://github.com/leanprover-community/mathlib/pull/674))
#### Estimated changes
Modified src/algebra/euclidean_domain.lean




## [2019-02-02 19:04:50-05:00](https://github.com/leanprover-community/mathlib/commit/3109c4b)
chore(purge_olean.sh): a few small improvements ([#661](https://github.com/leanprover-community/mathlib/pull/661))
* purge empty directories
* Only print if an .olean is rm'd. This reduces the noise and reduces the
script run time.
* use git top-level dir to make the script relocatable
* only affect src and test dirs
* use bash instead of sed
#### Estimated changes
Modified purge_olean.sh




## [2019-02-02 18:43:29-05:00](https://github.com/leanprover-community/mathlib/commit/8590ff2)
fix(functor_category): remove superfluous coercions ([#670](https://github.com/leanprover-community/mathlib/pull/670))
#### Estimated changes
Modified src/category_theory/functor_category.lean




## [2019-02-02 18:42:36-05:00](https://github.com/leanprover-community/mathlib/commit/a09dc9f)
cleanup(category_theory/cones): tidying up, after making opposites work better ([#675](https://github.com/leanprover-community/mathlib/pull/675))
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+/\- *def* category_theory.functor.cones
- \+/\- *lemma* category_theory.functor.cones_obj



## [2019-02-02 18:41:09-05:00](https://github.com/leanprover-community/mathlib/commit/b084cfc)
fix(category_theory/equivalence): duplicated namespace prefix ([#669](https://github.com/leanprover-community/mathlib/pull/669))
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \- *def* category_theory.category_theory.equivalence.equivalence_of_fully_faithfully_ess_surj
- \- *def* category_theory.category_theory.equivalence.ess_surj_of_equivalence
- \+ *def* category_theory.equivalence.equivalence_of_fully_faithfully_ess_surj
- \+ *def* category_theory.equivalence.ess_surj_of_equivalence



## [2019-02-02 17:59:12-05:00](https://github.com/leanprover-community/mathlib/commit/e501d02)
fix(replacer): better flow control in replacer when tactic fails ([#673](https://github.com/leanprover-community/mathlib/pull/673))
The main consequence is better error reporting.
#### Estimated changes
Modified src/tactic/replacer.lean




## [2019-02-02 18:42:12](https://github.com/leanprover-community/mathlib/commit/0393ccb)
feat(ring_theory/algebra): subalgebra_of_subring ([#664](https://github.com/leanprover-community/mathlib/pull/664))
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *def* alg_hom_int
- \- *def* is_ring_hom.to_ℤ_alg_hom
- \+ *lemma* mem_subalgebra_of_subring
- \- *def* ring.to_ℤ_algebra
- \+ *def* subalgebra_of_subring



## [2019-02-01 23:00:55-05:00](https://github.com/leanprover-community/mathlib/commit/f529870)
feat(data/nat/gcd/coprime): some easy simp lemmas ([#677](https://github.com/leanprover-community/mathlib/pull/677))
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *theorem* nat.coprime_one_left_iff
- \+ *theorem* nat.coprime_one_right_iff
- \+ *theorem* nat.coprime_self
- \+ *theorem* nat.coprime_zero_left
- \+ *theorem* nat.coprime_zero_right



## [2019-02-02 01:41:01](https://github.com/leanprover-community/mathlib/commit/6925e4d)
feat(algebra/euclidean_domain): lcm ([#665](https://github.com/leanprover-community/mathlib/pull/665))
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+ *theorem* euclidean_domain.dvd_lcm_left
- \+ *theorem* euclidean_domain.dvd_lcm_right
- \+ *lemma* euclidean_domain.gcd_mul_lcm
- \+ *def* euclidean_domain.lcm
- \+ *theorem* euclidean_domain.lcm_dvd
- \+ *lemma* euclidean_domain.lcm_dvd_iff
- \+ *lemma* euclidean_domain.lcm_eq_zero_iff
- \+ *lemma* euclidean_domain.lcm_zero_left
- \+ *lemma* euclidean_domain.lcm_zero_right



## [2019-02-01 20:07:31-05:00](https://github.com/leanprover-community/mathlib/commit/fb60145)
cleanup: replace `begin intros ...` with lambdas ([#672](https://github.com/leanprover-community/mathlib/pull/672))
#### Estimated changes
Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean


Modified src/data/set/basic.lean




## [2019-02-01 22:48:10](https://github.com/leanprover-community/mathlib/commit/ed0d24a)
feat(algebra/euclidean_domain): add quotient_zero axiom to euclidean_domain ([#666](https://github.com/leanprover-community/mathlib/pull/666))
#### Estimated changes
Modified src/algebra/euclidean_domain.lean
- \+ *lemma* euclidean_domain.div_zero
- \+ *theorem* euclidean_domain.mul_div_assoc
- \+/\- *lemma* euclidean_domain.zero_div

Modified src/data/polynomial.lean
- \- *lemma* polynomial.div_zero



## [2019-02-01 12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/d8f6dc4)
feat(src/tactic/explode): improve printing of references
#### Estimated changes
Modified src/tactic/explode.lean




## [2019-02-01 12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/a32de36)
feat(src/tactic/explode): add printing for conclusions of sintros
#### Estimated changes
Modified src/tactic/explode.lean




## [2019-02-01 12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/a08c9a7)
add printing for conclusions of sintros
#### Estimated changes
Modified src/tactic/explode.lean




## [2019-02-01 12:13:59+01:00](https://github.com/leanprover-community/mathlib/commit/c9e4f8e)
fix(tactic/inarith): fix denominator normalization of products
#### Estimated changes
Modified src/tactic/linarith.lean


Modified test/linarith.lean




## [2019-02-01 12:13:31+01:00](https://github.com/leanprover-community/mathlib/commit/52adfd7)
feat(tactic,tactic/interactive): add set tactic, a variant of let
#### Estimated changes
Modified docs/tactics.md


Modified src/tactic/basic.lean


Modified src/tactic/interactive.lean




## [2019-02-01 09:53:51+01:00](https://github.com/leanprover-community/mathlib/commit/89bc63c)
feat(ring_theory/noetherian): is_noetherian_ring_range
#### Estimated changes
Modified src/ring_theory/noetherian.lean
- \+ *theorem* is_noetherian_ring_range



## [2019-02-01 00:30:09](https://github.com/leanprover-community/mathlib/commit/8e381f6)
feat(ring_theory/algebra_operations): multiplication of submodules of an algebra ([#658](https://github.com/leanprover-community/mathlib/pull/658))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.add_eq_sup
- \+ *lemma* submodule.zero_eq_bot

Added src/ring_theory/algebra_operations.lean
- \+ *theorem* algebra.bot_mul
- \+ *theorem* algebra.fg_mul
- \+ *theorem* algebra.mul_bot
- \+ *theorem* algebra.mul_le
- \+ *theorem* algebra.mul_le_mul
- \+ *theorem* algebra.mul_le_mul_left
- \+ *theorem* algebra.mul_le_mul_right
- \+ *theorem* algebra.mul_mem_mul
- \+ *theorem* algebra.mul_mem_mul_rev
- \+ *theorem* algebra.mul_sup
- \+ *theorem* algebra.span_mul_span
- \+ *theorem* algebra.sup_mul

Modified src/ring_theory/ideal_operations.lean
- \- *lemma* submodule.add_eq_sup
- \- *lemma* submodule.zero_eq_bot

