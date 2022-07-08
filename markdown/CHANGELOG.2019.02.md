## [2019-02-28 20:55:23](https://github.com/leanprover-community/mathlib/commit/05449a0)
refactor(ring_theory/localization): rename of to mk, and define of ([#765](https://github.com/leanprover-community/mathlib/pull/765))
* refactor(ring_theory/localization): rename of to mk, and define of
* Make submonoid implicit variable of 'of'
#### Estimated changes
modified src/ring_theory/localization.lean
- \+/\- *lemma* of_zero
- \+/\- *lemma* of_one
- \+/\- *lemma* of_add
- \+/\- *lemma* of_sub
- \+/\- *lemma* of_mul
- \+/\- *lemma* of_neg
- \+/\- *lemma* of_pow
- \+ *lemma* mk_self
- \+ *lemma* mk_self'
- \+ *lemma* mk_self''
- \+ *lemma* coe_mul_mk
- \+ *lemma* mk_eq_mul_mk_one
- \+ *lemma* mk_mul_mk
- \+ *lemma* mk_mul_cancel_left
- \+ *lemma* mk_mul_cancel_right
- \+ *lemma* mk_eq_div
- \+ *lemma* eq_zero_of
- \+ *lemma* of.injective
- \+/\- *lemma* of_one
- \+/\- *lemma* of_add
- \+/\- *lemma* of_sub
- \+/\- *lemma* of_mul
- \+/\- *lemma* of_neg
- \+/\- *lemma* of_pow
- \+/\- *lemma* of_zero
- \- *lemma* of_self
- \- *lemma* of_self'
- \- *lemma* of_self''
- \- *lemma* coe_mul_of
- \- *lemma* of_eq_mul_of_one
- \- *lemma* of_mul_of
- \- *lemma* of_mul_cancel_left
- \- *lemma* of_mul_cancel_right
- \- *lemma* of_eq_div
- \+ *def* mk
- \+/\- *def* of
- \+/\- *def* of



## [2019-02-28 19:14:55](https://github.com/leanprover-community/mathlib/commit/eb033cf)
feat(ring_theory/ideals): make ideal.quotient.field a discrete_field ([#777](https://github.com/leanprover-community/mathlib/pull/777))
#### Estimated changes
modified src/ring_theory/adjoin_root.lean

modified src/ring_theory/ideals.lean



## [2019-02-28 17:20:01](https://github.com/leanprover-community/mathlib/commit/e6a3ca8)
refactor(algebra/group): generalise and extend the API for with_zero ([#762](https://github.com/leanprover-community/mathlib/pull/762))
* refactor(algebra/group): generalise and extend the API for with_zero
* Shorter proof. Thanks Chris
* Travis, try your best
#### Estimated changes
modified src/algebra/group.lean
- \+ *lemma* with_one.one_ne_coe
- \+ *lemma* with_one.coe_ne_one
- \+ *lemma* with_one.ne_one_iff_exists
- \+ *lemma* with_one.coe_inj
- \+ *lemma* with_one.mul_coe
- \+ *lemma* coe_one
- \+ *lemma* mul_coe
- \+ *lemma* inv_coe
- \+ *lemma* inv_zero
- \+ *lemma* inv_one
- \+ *lemma* zero_div
- \+ *lemma* div_zero
- \+ *lemma* div_coe
- \+ *lemma* one_div
- \+ *lemma* div_one
- \+ *lemma* mul_right_inv
- \+ *lemma* mul_left_inv
- \+ *lemma* mul_inv_rev
- \+ *lemma* mul_div_cancel
- \+ *lemma* div_mul_cancel
- \+ *lemma* div_eq_iff_mul_eq
- \+ *lemma* div_eq_div
- \+/\- *def* with_one
- \+/\- *def* with_one



## [2019-02-28 16:55:44](https://github.com/leanprover-community/mathlib/commit/781d187)
feat(group_theory/quotient_group): define ker_lift and prove simp-lemmas ([#764](https://github.com/leanprover-community/mathlib/pull/764))
* feat(group_theory/quotient_group): define ker_lift and prove simp-lemmas
* Add docstring
#### Estimated changes
modified src/group_theory/quotient_group.lean
- \+ *lemma* ker_lift_mk
- \+ *lemma* ker_lift_mk'
- \+/\- *lemma* injective_ker_lift
- \+/\- *lemma* injective_ker_lift
- \+ *def* ker_lift



## [2019-02-28 11:09:35+01:00](https://github.com/leanprover-community/mathlib/commit/81f8530)
fix(tactic/linarith): typo
#### Estimated changes
modified src/tactic/linarith.lean



## [2019-02-28 10:33:40+01:00](https://github.com/leanprover-community/mathlib/commit/08d4d17)
feat(topology/basic): Add instances for subset/inter/union for opens(X) ([#763](https://github.com/leanprover-community/mathlib/pull/763))
* feat(topology/basic): Add instances for subset/inter/union for opens(X)
#### Estimated changes
modified src/topology/basic.lean
- \+ *lemma* inter_eq
- \+ *lemma* union_eq
- \+ *lemma* empty_eq



## [2019-02-27 23:53:37+01:00](https://github.com/leanprover-community/mathlib/commit/477338d)
refactor(data/subtype): organise in namespaces, use variables, add two simp-lemmas ([#760](https://github.com/leanprover-community/mathlib/pull/760))
#### Estimated changes
modified src/data/subtype.lean
- \+ *lemma* ext
- \+ *lemma* coe_ext
- \+ *lemma* val_prop
- \+ *lemma* val_prop'
- \- *lemma* subtype.ext
- \- *lemma* subtype.coe_ext
- \+/\- *theorem* subtype.forall
- \+/\- *theorem* subtype.exists
- \+ *theorem* val_injective
- \+ *theorem* coe_eta
- \+ *theorem* coe_mk
- \+ *theorem* mk_eq_mk
- \- *theorem* subtype.val_injective
- \- *theorem* subtype.coe_eta
- \- *theorem* subtype.coe_mk
- \- *theorem* subtype.mk_eq_mk
- \+/\- *theorem* subtype.forall
- \+/\- *theorem* subtype.exists



## [2019-02-27 22:46:52](https://github.com/leanprover-community/mathlib/commit/af2cf74)
feat(group_theory/quotient_group): map is a group hom ([#761](https://github.com/leanprover-community/mathlib/pull/761))
#### Estimated changes
modified src/group_theory/quotient_group.lean



## [2019-02-27 22:37:11](https://github.com/leanprover-community/mathlib/commit/dfa855c)
feat(data/finset) remove unnecessary assumption from card_eq_succ ([#772](https://github.com/leanprover-community/mathlib/pull/772))
#### Estimated changes
modified src/data/finset.lean
- \+/\- *lemma* card_eq_succ
- \+/\- *lemma* card_eq_succ



## [2019-02-27 23:14:03+01:00](https://github.com/leanprover-community/mathlib/commit/cfde449)
fix(doc/tactics): linarith doc is outdated [ci-skip]
#### Estimated changes
modified docs/tactics.md



## [2019-02-27 21:33:02+01:00](https://github.com/leanprover-community/mathlib/commit/6c71ac0)
fix(tactic/linarith): fix bug in strengthening of strict nat/int inequalities
#### Estimated changes
modified src/tactic/linarith.lean

modified test/linarith.lean



## [2019-02-27 15:25:19](https://github.com/leanprover-community/mathlib/commit/4667d2c)
feat(ring_theory/ideal_operations): ideals form a commutative semiring ([#771](https://github.com/leanprover-community/mathlib/pull/771))
#### Estimated changes
modified src/ring_theory/ideal_operations.lean



## [2019-02-27 14:06:24](https://github.com/leanprover-community/mathlib/commit/05d1d33)
fix(algebra/archimedean): swap names of floor_add_fract and fract_add_floor ([#770](https://github.com/leanprover-community/mathlib/pull/770))
#### Estimated changes
modified src/algebra/archimedean.lean
- \+/\- *lemma* floor_add_fract
- \+/\- *lemma* fract_add_floor
- \+/\- *lemma* fract_add_floor
- \+/\- *lemma* floor_add_fract



## [2019-02-27 12:02:24+01:00](https://github.com/leanprover-community/mathlib/commit/42d1ed7)
feat(linarith): improve handling of strict inequalities in nat and int ([#769](https://github.com/leanprover-community/mathlib/pull/769))
* feat(linarith): perform slightly better on ℕ and ℤ by strengthening t < 0 hyps to t + 1 ≤ 0
* remove already completed TODO item
#### Estimated changes
modified src/tactic/linarith.lean

modified test/linarith.lean



## [2019-02-26 22:04:45+01:00](https://github.com/leanprover-community/mathlib/commit/3f47739)
fix(docs/howto-contribute): main repository has moved
#### Estimated changes
modified docs/howto-contribute.md



## [2019-02-26 12:57:23-05:00](https://github.com/leanprover-community/mathlib/commit/7450cc5)
fix(scripts/update_mathlib): improve python style and error handling ([#759](https://github.com/leanprover-community/mathlib/pull/759))
#### Estimated changes
modified scripts/update-mathlib.py



## [2019-02-25 16:20:56-05:00](https://github.com/leanprover-community/mathlib/commit/71a7e1c)
fix(scripts/update-mathlib): cached archived were never expanded
#### Estimated changes
modified scripts/update-mathlib.py



## [2019-02-25 16:01:35-05:00](https://github.com/leanprover-community/mathlib/commit/4222483)
fix(scripts/update-mathlib): fix the commit check
#### Estimated changes
modified scripts/update-mathlib.py



## [2019-02-24 23:52:02-05:00](https://github.com/leanprover-community/mathlib/commit/e23553a)
doc(nat/decidable_prime): add docstrings explaining the two decidable_prime instances ([#757](https://github.com/leanprover-community/mathlib/pull/757))
#### Estimated changes
modified docs/theories/naturals.md

modified src/data/nat/prime.lean



## [2019-02-24 15:36:34](https://github.com/leanprover-community/mathlib/commit/f922086)
feat(ring_theory/polynomial): more operations on polynomials ([#679](https://github.com/leanprover-community/mathlib/pull/679))
#### Estimated changes
modified src/ring_theory/polynomial.lean
- \+ *theorem* coeff_restriction
- \+ *theorem* coeff_restriction'
- \+ *theorem* degree_restriction
- \+ *theorem* nat_degree_restriction
- \+ *theorem* monic_restriction
- \+ *theorem* restriction_zero
- \+ *theorem* restriction_one
- \+ *theorem* eval₂_restriction
- \+ *theorem* coeff_to_subring
- \+ *theorem* coeff_to_subring'
- \+ *theorem* degree_to_subring
- \+ *theorem* nat_degree_to_subring
- \+ *theorem* monic_to_subring
- \+ *theorem* to_subring_zero
- \+ *theorem* to_subring_one
- \+ *theorem* frange_of_subring
- \+ *theorem* is_noetherian_ring_mv_polynomial_fin
- \+ *theorem* is_noetherian_ring_mv_polynomial_of_fintype
- \+ *def* restriction
- \+ *def* to_subring
- \+ *def* of_subring



## [2019-02-24 11:59:27](https://github.com/leanprover-community/mathlib/commit/c9b2d0e)
chore(linear_algebra/multivariate_polynomial): remove unnecessary decidable_eq assumption ([#755](https://github.com/leanprover-community/mathlib/pull/755))
#### Estimated changes
modified src/linear_algebra/multivariate_polynomial.lean



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
modified src/algebra/group_power.lean
- \+ *theorem* pow_lt_pow_of_lt_left
- \+ *theorem* pow_right_inj

modified src/analysis/exponential.lean
- \+ *lemma* coe_zero
- \+ *lemma* coe_add
- \+ *lemma* coe_neg
- \+ *lemma* coe_sub
- \+ *lemma* coe_gsmul
- \+ *lemma* coe_two_pi
- \+ *lemma* angle_eq_iff_two_pi_dvd_sub
- \+ *theorem* sin_sub_sin
- \+ *theorem* cos_eq_zero_iff
- \+ *theorem* cos_sub_cos
- \+ *theorem* cos_eq_iff_eq_or_eq_neg
- \+ *theorem* sin_eq_iff_eq_or_add_eq_pi
- \+ *theorem* cos_sin_inj
- \+ *def* angle

modified src/data/complex/exponential.lean
- \+ *lemma* exp_nat_mul
- \+ *lemma* exp_nat_mul
- \+ *theorem* cos_add_sin_mul_I_pow



## [2019-02-23 00:41:40](https://github.com/leanprover-community/mathlib/commit/63fa61d)
fix(analysis/specific_limits): remove useless assumption ([#751](https://github.com/leanprover-community/mathlib/pull/751))
#### Estimated changes
modified src/analysis/specific_limits.lean
- \+/\- *lemma* has_sum_of_absolute_convergence_real
- \+/\- *lemma* has_sum_of_absolute_convergence_real



## [2019-02-21 21:35:05](https://github.com/leanprover-community/mathlib/commit/e739cf5)
feat(order_dual): instances for order_dual and shortening proofs ([#746](https://github.com/leanprover-community/mathlib/pull/746))
* feat(order_bot): instances for order_bot and shortening proofs
* fix(topological_structure); remove unused import
#### Estimated changes
modified src/order/basic.lean

modified src/order/conditionally_complete_lattice.lean

modified src/topology/algebra/topological_structures.lean
- \+/\- *lemma* nhds_principal_ne_bot_of_is_glb
- \+/\- *lemma* is_glb_of_mem_nhds
- \+/\- *lemma* is_glb_of_is_lub_of_tendsto
- \+ *lemma* is_lub_of_is_glb_of_tendsto
- \+/\- *lemma* exists_forall_ge_of_compact_of_continuous
- \+/\- *lemma* nhds_principal_ne_bot_of_is_glb
- \+/\- *lemma* is_glb_of_mem_nhds
- \+/\- *lemma* is_glb_of_is_lub_of_tendsto
- \+/\- *lemma* exists_forall_ge_of_compact_of_continuous
- \+/\- *theorem* gt_mem_sets_of_Liminf_gt
- \+/\- *theorem* Liminf_nhds
- \+/\- *theorem* Limsup_eq_of_le_nhds
- \+/\- *theorem* gt_mem_sets_of_Liminf_gt
- \+/\- *theorem* Liminf_nhds
- \+/\- *theorem* Limsup_eq_of_le_nhds



## [2019-02-21 16:24:47](https://github.com/leanprover-community/mathlib/commit/3c3a052)
feat(field_theory/subfield): closure of subset in field ([#742](https://github.com/leanprover-community/mathlib/pull/742))
#### Estimated changes
modified src/field_theory/subfield.lean
- \+ *theorem* ring_closure_subset
- \+ *theorem* mem_closure
- \+ *theorem* subset_closure
- \+ *theorem* closure_subset
- \+ *theorem* closure_subset_iff
- \+ *theorem* closure_mono
- \+ *def* closure



## [2019-02-20 18:08:04-05:00](https://github.com/leanprover-community/mathlib/commit/9656485)
feat(data/finmap): lift_on₂ ([#716](https://github.com/leanprover-community/mathlib/pull/716))
* feat(data/finmap): define lift_on₂ with lift_on
#### Estimated changes
modified src/data/finmap.lean
- \+ *theorem* lift_on₂_to_finmap
- \+ *def* lift_on₂



## [2019-02-20 17:32:07](https://github.com/leanprover-community/mathlib/commit/8b8ae32)
fix(order/basic): give order_dual the correct lt ([#741](https://github.com/leanprover-community/mathlib/pull/741))
#### Estimated changes
modified src/order/basic.lean



## [2019-02-20 12:33:02](https://github.com/leanprover-community/mathlib/commit/c7202e5)
feat(analysis/exponential): pow_nat_rpow_nat_inv ([#740](https://github.com/leanprover-community/mathlib/pull/740))
#### Estimated changes
modified src/analysis/exponential.lean
- \+ *lemma* abs_cpow_inv_nat
- \+ *lemma* pow_nat_rpow_nat_inv



## [2019-02-18 18:07:10](https://github.com/leanprover-community/mathlib/commit/78ce6e4)
feat(data/fintype): fintype.of_injective
#### Estimated changes
modified src/data/fintype.lean



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
modified src/data/finmap.lean
- \+ *theorem* coe_keys
- \+ *theorem* lookup_eq_none
- \+ *theorem* lookup_erase
- \+ *theorem* lookup_erase_ne
- \+/\- *theorem* insert_to_finmap
- \+/\- *theorem* insert_entries_of_neg
- \+/\- *theorem* mem_insert
- \+ *theorem* lookup_insert
- \- *theorem* not_mem_empty_entries
- \+/\- *theorem* insert_to_finmap
- \- *theorem* insert_of_pos
- \+/\- *theorem* insert_entries_of_neg
- \+/\- *theorem* mem_insert
- \+ *def* keys
- \+/\- *def* insert
- \+/\- *def* insert

modified src/data/list/alist.lean
- \+/\- *theorem* keys_nodup
- \+/\- *theorem* mem_keys
- \+/\- *theorem* mem_of_perm
- \+/\- *theorem* not_mem_empty
- \+ *theorem* lookup_eq_none
- \+ *theorem* lookup_erase
- \+ *theorem* lookup_erase_ne
- \+ *theorem* insert_entries
- \+/\- *theorem* insert_entries_of_neg
- \+/\- *theorem* mem_insert
- \+/\- *theorem* keys_insert
- \+/\- *theorem* perm_insert
- \+ *theorem* lookup_insert
- \+ *theorem* lookup_insert_ne
- \- *theorem* mem_def
- \+/\- *theorem* mem_of_perm
- \+/\- *theorem* mem_keys
- \+/\- *theorem* keys_nodup
- \- *theorem* not_mem_empty_entries
- \+/\- *theorem* not_mem_empty
- \- *theorem* insert_of_pos
- \+/\- *theorem* insert_entries_of_neg
- \+/\- *theorem* keys_insert
- \+/\- *theorem* mem_insert
- \+/\- *theorem* perm_insert
- \+/\- *def* keys
- \+/\- *def* insert
- \+/\- *def* keys
- \+/\- *def* insert

modified src/data/list/sigma.lean
- \+ *theorem* keys_nil
- \+ *theorem* keys_cons
- \+ *theorem* mem_keys_of_mem
- \+ *theorem* exists_of_mem_keys
- \+ *theorem* mem_keys
- \+ *theorem* not_mem_keys
- \+ *theorem* not_eq_key
- \+/\- *theorem* nodupkeys_cons
- \+ *theorem* mem_lookup
- \+ *theorem* keys_kreplace
- \+ *theorem* kerase_nil
- \+ *theorem* kerase_cons_eq
- \+ *theorem* kerase_cons_ne
- \+ *theorem* kerase_of_not_mem_keys
- \+ *theorem* kerase_keys_subset
- \+ *theorem* mem_keys_of_mem_keys_kerase
- \+ *theorem* exists_of_kerase
- \+ *theorem* mem_keys_kerase_of_ne
- \+ *theorem* keys_kerase
- \+ *theorem* not_mem_keys_kerase
- \+ *theorem* lookup_kerase
- \+ *theorem* lookup_kerase_ne
- \+ *theorem* kinsert_def
- \+ *theorem* mem_keys_kinsert
- \+ *theorem* kinsert_nodupkeys
- \+ *theorem* perm_kinsert
- \+ *theorem* lookup_kinsert
- \+ *theorem* lookup_kinsert_ne
- \+/\- *theorem* nodupkeys_cons
- \- *theorem* kreplace_map_fst
- \- *theorem* kerase_map_fst
- \+ *def* keys
- \+ *def* kinsert



## [2019-02-18 09:45:57](https://github.com/leanprover-community/mathlib/commit/6b4435b)
feat(data/polynomial): create nonzero_comm_semiring and generalize nonzero_comm_ring lemmas ([#736](https://github.com/leanprover-community/mathlib/pull/736))
#### Estimated changes
modified src/algebra/ring.lean
- \+/\- *lemma* units.coe_ne_zero
- \+/\- *lemma* units.coe_ne_zero
- \+ *def* nonzero_comm_semiring.of_ne

modified src/data/polynomial.lean
- \+/\- *lemma* degree_one
- \+/\- *lemma* degree_X
- \+/\- *lemma* X_ne_zero
- \+/\- *lemma* degree_X_pow
- \+/\- *lemma* not_monic_zero
- \+/\- *lemma* ne_zero_of_monic
- \+/\- *lemma* degree_one
- \+/\- *lemma* degree_X
- \+/\- *lemma* X_ne_zero
- \+/\- *lemma* degree_X_pow
- \+/\- *lemma* not_monic_zero
- \+/\- *lemma* ne_zero_of_monic



## [2019-02-16 21:24:09](https://github.com/leanprover-community/mathlib/commit/c64b67e)
feat(ring_theory/localization): revamp, ideal embedding ([#481](https://github.com/leanprover-community/mathlib/pull/481))
#### Estimated changes
modified src/ring_theory/localization.lean
- \+ *lemma* of_one
- \+ *lemma* of_add
- \+ *lemma* of_sub
- \+ *lemma* of_mul
- \+ *lemma* of_neg
- \+ *lemma* of_pow
- \+ *lemma* coe_zero
- \+ *lemma* coe_one
- \+ *lemma* coe_add
- \+ *lemma* coe_sub
- \+ *lemma* coe_mul
- \+ *lemma* coe_neg
- \+ *lemma* coe_pow
- \+ *lemma* of_zero
- \+ *lemma* of_self
- \+ *lemma* of_self'
- \+ *lemma* of_self''
- \+ *lemma* coe_mul_of
- \+ *lemma* of_eq_mul_of_one
- \+ *lemma* of_mul_of
- \+ *lemma* of_mul_cancel_left
- \+ *lemma* of_mul_cancel_right
- \+ *lemma* of_eq_div
- \+/\- *theorem* r_of_eq
- \+/\- *theorem* symm
- \+ *theorem* map_comap
- \+/\- *theorem* r_of_eq
- \+/\- *theorem* symm
- \+/\- *def* r
- \+ *def* of
- \+/\- *def* away
- \+ *def* away.inv_self
- \+/\- *def* at_prime
- \+ *def* fraction_ring
- \+/\- *def* inv_aux
- \+ *def* le_order_embedding
- \+/\- *def* r
- \- *def* of_comm_ring
- \+/\- *def* away
- \+/\- *def* at_prime
- \- *def* quotient_ring
- \+/\- *def* inv_aux
- \- *def* quotient_ring.field.of_integral_domain



## [2019-02-15 17:29:36-05:00](https://github.com/leanprover-community/mathlib/commit/17f9bef)
feat(category/monad/cont): continuation passing monad ([#728](https://github.com/leanprover-community/mathlib/pull/728))
#### Estimated changes
created src/category/monad/cont.lean
- \+ *lemma* run_cont_t_map_cont_t
- \+ *lemma* run_with_cont_t
- \+ *lemma* monad_lift_bind
- \+ *def* monad_cont.goto
- \+ *def* cont_t
- \+ *def* run
- \+ *def* map
- \+ *def* with_cont_t



## [2019-02-15 19:37:56](https://github.com/leanprover-community/mathlib/commit/0a6e705)
refactor(data/equiv/algebra): move polynomial lemmas from equiv/algebra to mv_polynomial ([#731](https://github.com/leanprover-community/mathlib/pull/731))
* refactor(data/equiv/algebra): move polynomial lemma from equiv/algebra to mv_polynomial
* remove update-mathlib.py
#### Estimated changes
modified src/category_theory/instances/rings.lean

modified src/data/equiv/algebra.lean
- \- *lemma* sum_to_iter_C
- \- *lemma* sum_to_iter_Xl
- \- *lemma* sum_to_iter_Xr
- \- *lemma* iter_to_sum_C_C
- \- *lemma* iter_to_sum_X
- \- *lemma* iter_to_sum_C_X
- \- *def* pempty_ring_equiv
- \- *def* punit_ring_equiv
- \- *def* ring_equiv_of_equiv
- \- *def* ring_equiv_congr
- \- *def* sum_to_iter
- \- *def* iter_to_sum
- \- *def* mv_polynomial_equiv_mv_polynomial
- \- *def* sum_ring_equiv
- \- *def* option_equiv_left
- \- *def* option_equiv_right

modified src/linear_algebra/multivariate_polynomial.lean
- \+ *lemma* sum_to_iter_C
- \+ *lemma* sum_to_iter_Xl
- \+ *lemma* sum_to_iter_Xr
- \+ *lemma* iter_to_sum_C_C
- \+ *lemma* iter_to_sum_X
- \+ *lemma* iter_to_sum_C_X
- \+ *def* pempty_ring_equiv
- \+ *def* punit_ring_equiv
- \+ *def* ring_equiv_of_equiv
- \+ *def* ring_equiv_congr
- \+ *def* sum_to_iter
- \+ *def* iter_to_sum
- \+ *def* mv_polynomial_equiv_mv_polynomial
- \+ *def* sum_ring_equiv
- \+ *def* option_equiv_left
- \+ *def* option_equiv_right

modified src/ring_theory/noetherian.lean



## [2019-02-15 14:26:25+01:00](https://github.com/leanprover-community/mathlib/commit/d80b03e)
chore(order/filter/basic): update documentation of filter_upwards
#### Estimated changes
modified src/order/filter/basic.lean



## [2019-02-15 07:40:09](https://github.com/leanprover-community/mathlib/commit/8730619)
chore(topology/algebra/topological_structures): remove unused import ([#729](https://github.com/leanprover-community/mathlib/pull/729))
#### Estimated changes
modified src/topology/algebra/topological_structures.lean



## [2019-02-14 18:26:14+01:00](https://github.com/leanprover-community/mathlib/commit/ce580d7)
refactor(data/equiv): rename subtype_equiv_of_subtype to subtype_congr and subtype_congr to subtype_congr_prop
#### Estimated changes
modified src/data/equiv/basic.lean
- \+/\- *def* subtype_congr
- \+ *def* subtype_congr_prop
- \+/\- *def* set_congr
- \- *def* subtype_equiv_of_subtype
- \+/\- *def* subtype_congr
- \+/\- *def* set_congr



## [2019-02-14 18:04:51+01:00](https://github.com/leanprover-community/mathlib/commit/683519f)
feat(data/equiv/basic): generalise subtype_equiv_of_subtype ([#724](https://github.com/leanprover-community/mathlib/pull/724))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+/\- *def* subtype_equiv_of_subtype
- \+ *def* subtype_equiv_of_subtype'
- \+/\- *def* subtype_equiv_of_subtype



## [2019-02-14 18:04:24+01:00](https://github.com/leanprover-community/mathlib/commit/d4568a4)
fix(data/subtype): don't use pattern matching in subtype.map ([#725](https://github.com/leanprover-community/mathlib/pull/725))
#### Estimated changes
modified src/data/subtype.lean



## [2019-02-13 19:51:35-05:00](https://github.com/leanprover-community/mathlib/commit/5da8605)
chore(deploy): clean up deploy_nightly.sh ([#720](https://github.com/leanprover-community/mathlib/pull/720))
#### Estimated changes
modified scripts/deploy_nightly.sh



## [2019-02-13 23:30:38+01:00](https://github.com/leanprover-community/mathlib/commit/a6150a3)
refactor(data/real): move cau_seq_filter to analysis/metric_space ([#723](https://github.com/leanprover-community/mathlib/pull/723))
#### Estimated changes
modified src/data/padics/hensel.lean

modified src/data/padics/padic_numbers.lean

modified src/topology/bounded_continuous_function.lean

renamed src/data/real/cau_seq_filter.lean to src/topology/metric_space/cau_seq_filter.lean



## [2019-02-13 17:01:08+01:00](https://github.com/leanprover-community/mathlib/commit/3fd0e60)
refactor(topology/algebra/infinite_sum): Cauchy condition for infinite sums generalized to complete topological groups
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* ball_0_eq
- \+ *lemma* has_sum_iff_vanishing_norm
- \+ *lemma* has_sum_of_norm_bounded
- \+ *lemma* has_sum_of_has_sum_norm
- \+ *lemma* norm_tsum_le_tsum_norm

modified src/analysis/specific_limits.lean
- \- *lemma* has_sum_iff_cauchy
- \- *lemma* has_sum_of_has_sum_norm

modified src/measure_theory/probability_mass_function.lean
- \+/\- *def* pure
- \+/\- *def* pure

modified src/order/filter/basic.lean
- \+/\- *lemma* tendsto_at_top
- \+ *lemma* tendsto_at_top'
- \+/\- *lemma* tendsto_at_top

modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* is_sum_ite_eq
- \+ *lemma* is_sum_iff_is_sum_of_ne_zero_bij
- \+ *lemma* has_sum_iff_has_sum_ne_zero_bij
- \+ *lemma* tsum_ite_eq
- \+ *lemma* is_sum_le_inj
- \+ *lemma* has_sum_iff_cauchy
- \+ *lemma* has_sum_iff_vanishing
- \+/\- *lemma* has_sum_of_has_sum_of_sub
- \+ *lemma* has_sum_comp_of_has_sum_of_injective
- \- *lemma* is_sum_ite
- \- *lemma* tsum_ite
- \+/\- *lemma* has_sum_of_has_sum_of_sub
- \+ *def* option.cases_on'

modified src/topology/algebra/topological_structures.lean
- \+ *lemma* exists_nhds_split_inv



## [2019-02-12 22:44:40+01:00](https://github.com/leanprover-community/mathlib/commit/246c280)
feat(tactic/basic,tactic/interactive): improvements to set tactic ([#712](https://github.com/leanprover-community/mathlib/pull/712))
* feat(tactic/basic,tactic/interactive): improvements to set tactic
* feat(tactic/interactive): take optional explicit type in set tactic
#### Estimated changes
modified docs/tactics.md

modified src/tactic/basic.lean

modified src/tactic/interactive.lean

modified src/tactic/linarith.lean



## [2019-02-12 15:50:35-05:00](https://github.com/leanprover-community/mathlib/commit/f6ca16e)
fix(nightly): improve conditional ([#719](https://github.com/leanprover-community/mathlib/pull/719))
#### Estimated changes
modified scripts/deploy_nightly.sh



## [2019-02-12 20:15:49+01:00](https://github.com/leanprover-community/mathlib/commit/a4afa90)
refactor(analysis/specific_limits): generalize has_sum_of_absolute_convergence to normed_groups
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_triangle_sub
- \+ *lemma* norm_triangle_sum

modified src/analysis/specific_limits.lean
- \+ *lemma* has_sum_iff_cauchy
- \+ *lemma* has_sum_of_has_sum_norm
- \+ *lemma* has_sum_of_absolute_convergence_real
- \- *lemma* has_sum_of_absolute_convergence
- \- *lemma* is_sum_iff_tendsto_nat_of_nonneg

modified src/data/finset.lean
- \+ *lemma* disjoint_sdiff

modified src/measure_theory/decomposition.lean

modified src/measure_theory/measure_space.lean
- \- *lemma* tendsto_at_top_supr_nat
- \- *lemma* tendsto_at_top_infi_nat

modified src/order/filter/basic.lean
- \+/\- *lemma* tendsto_at_top_at_top
- \+/\- *lemma* tendsto_at_top_at_top
- \+ *theorem* tendsto_at_top_principal

modified src/topology/algebra/topological_structures.lean
- \+ *lemma* tendsto_at_top_supr_nat
- \+ *lemma* tendsto_at_top_infi_nat
- \+ *lemma* infi_eq_of_tendsto

modified src/topology/instances/ennreal.lean
- \+ *lemma* is_sum_iff_tendsto_nat
- \+/\- *lemma* exists_le_is_sum_of_le
- \+ *lemma* is_sum_iff_tendsto_nat
- \+/\- *lemma* has_sum_of_nonneg_of_le
- \+ *lemma* is_sum_iff_tendsto_nat_of_nonneg
- \+/\- *lemma* exists_le_is_sum_of_le
- \+/\- *lemma* has_sum_of_nonneg_of_le

modified src/topology/metric_space/basic.lean
- \+/\- *theorem* tendsto_at_top
- \+/\- *theorem* tendsto_at_top

modified src/topology/uniform_space/basic.lean
- \+ *lemma* cauchy_map_iff
- \+ *lemma* cauchy_iff_exists_le_nhds
- \+ *lemma* cauchy_map_iff_exists_tendsto



## [2019-02-12 09:33:43-05:00](https://github.com/leanprover-community/mathlib/commit/503a423)
feat(update-mathlib): improve setup and error messages
#### Estimated changes
modified scripts/remote-install-update-mathlib.sh

modified scripts/setup-update-mathlib.sh

modified scripts/update-mathlib.py



## [2019-02-12 15:28:42+01:00](https://github.com/leanprover-community/mathlib/commit/b6a4763)
refactor(order/filter): replace tendsto_comp_succ_at_top_iff by tendsto_add_at_top_iff_nat
#### Estimated changes
modified src/analysis/specific_limits.lean
- \+/\- *lemma* tendsto_pow_at_top_at_top_of_gt_1_nat
- \+/\- *lemma* tendsto_one_div_add_at_top_nhds_0_nat
- \- *lemma* tendsto_comp_succ_at_top_iff
- \+/\- *lemma* tendsto_pow_at_top_at_top_of_gt_1_nat
- \+/\- *lemma* tendsto_one_div_add_at_top_nhds_0_nat

modified src/order/filter/basic.lean
- \+ *lemma* tendsto_add_at_top_iff_nat

modified src/topology/metric_space/lipschitz.lean



## [2019-02-12 08:46:53-05:00](https://github.com/leanprover-community/mathlib/commit/c4e8414)
fix(update-mathlib): install from anywhere in your directory structure
#### Estimated changes
modified scripts/remote-install-update-mathlib.sh



## [2019-02-12 14:09:42+01:00](https://github.com/leanprover-community/mathlib/commit/f5a85f1)
refactor(order/filter): move lift and lift' to separate file
#### Estimated changes
modified src/data/set/basic.lean
- \+ *theorem* prod_eq_empty_iff

modified src/order/filter/basic.lean
- \+ *lemma* prod_bot
- \+ *lemma* bot_prod
- \+ *lemma* prod_eq_bot
- \- *lemma* lift_sets_eq
- \- *lemma* mem_lift
- \- *lemma* mem_lift_sets
- \- *lemma* lift_le
- \- *lemma* le_lift
- \- *lemma* lift_mono
- \- *lemma* lift_mono'
- \- *lemma* map_lift_eq
- \- *lemma* comap_lift_eq
- \- *lemma* map_lift_eq2
- \- *lemma* lift_comm
- \- *lemma* lift_assoc
- \- *lemma* lift_lift_same_le_lift
- \- *lemma* lift_lift_same_eq_lift
- \- *lemma* lift_principal
- \- *lemma* lift_neq_bot_iff
- \- *lemma* lift_const
- \- *lemma* lift_inf
- \- *lemma* lift_principal2
- \- *lemma* lift_infi
- \- *lemma* mem_lift'
- \- *lemma* mem_lift'_sets
- \- *lemma* lift'_le
- \- *lemma* lift'_mono
- \- *lemma* lift'_mono'
- \- *lemma* lift'_cong
- \- *lemma* map_lift'_eq
- \- *lemma* map_lift'_eq2
- \- *lemma* lift'_principal
- \- *lemma* principal_le_lift'
- \- *lemma* lift_lift'_assoc
- \- *lemma* lift'_lift'_assoc
- \- *lemma* lift'_lift_assoc
- \- *lemma* lift_lift'_same_le_lift'
- \- *lemma* lift_lift'_same_eq_lift'
- \- *lemma* lift'_inf_principal_eq
- \- *lemma* lift'_neq_bot_iff
- \- *lemma* lift'_id
- \- *lemma* le_lift'
- \- *lemma* lift_infi'
- \- *lemma* lift'_infi
- \- *lemma* prod_bot1
- \- *lemma* prod_bot2
- \- *lemma* prod_def
- \- *lemma* prod_same_eq
- \- *lemma* mem_prod_same_iff
- \- *lemma* prod_lift_lift
- \- *lemma* prod_lift'_lift'
- \- *lemma* tendsto_prod_self_iff
- \- *theorem* comap_lift_eq2
- \- *theorem* monotone_lift
- \- *theorem* comap_lift'_eq
- \- *theorem* comap_lift'_eq2
- \- *theorem* monotone_lift'
- \- *theorem* comap_eq_lift'

created src/order/filter/lift.lean
- \+ *lemma* lift_sets_eq
- \+ *lemma* mem_lift
- \+ *lemma* mem_lift_sets
- \+ *lemma* lift_le
- \+ *lemma* le_lift
- \+ *lemma* lift_mono
- \+ *lemma* lift_mono'
- \+ *lemma* map_lift_eq
- \+ *lemma* comap_lift_eq
- \+ *lemma* map_lift_eq2
- \+ *lemma* lift_comm
- \+ *lemma* lift_assoc
- \+ *lemma* lift_lift_same_le_lift
- \+ *lemma* lift_lift_same_eq_lift
- \+ *lemma* lift_principal
- \+ *lemma* lift_neq_bot_iff
- \+ *lemma* lift_const
- \+ *lemma* lift_inf
- \+ *lemma* lift_principal2
- \+ *lemma* lift_infi
- \+ *lemma* mem_lift'
- \+ *lemma* mem_lift'_sets
- \+ *lemma* lift'_le
- \+ *lemma* lift'_mono
- \+ *lemma* lift'_mono'
- \+ *lemma* lift'_cong
- \+ *lemma* map_lift'_eq
- \+ *lemma* map_lift'_eq2
- \+ *lemma* lift'_principal
- \+ *lemma* principal_le_lift'
- \+ *lemma* lift_lift'_assoc
- \+ *lemma* lift'_lift'_assoc
- \+ *lemma* lift'_lift_assoc
- \+ *lemma* lift_lift'_same_le_lift'
- \+ *lemma* lift_lift'_same_eq_lift'
- \+ *lemma* lift'_inf_principal_eq
- \+ *lemma* lift'_neq_bot_iff
- \+ *lemma* lift'_id
- \+ *lemma* le_lift'
- \+ *lemma* lift_infi'
- \+ *lemma* lift'_infi
- \+ *lemma* prod_def
- \+ *lemma* prod_same_eq
- \+ *lemma* mem_prod_same_iff
- \+ *lemma* tendsto_prod_self_iff
- \+ *lemma* prod_lift_lift
- \+ *lemma* prod_lift'_lift'
- \+ *theorem* comap_lift_eq2
- \+ *theorem* monotone_lift
- \+ *theorem* comap_lift'_eq
- \+ *theorem* comap_lift'_eq2
- \+ *theorem* monotone_lift'
- \+ *theorem* comap_eq_lift'

modified src/topology/uniform_space/basic.lean



## [2019-02-12 11:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/253fe33)
refactor(order/filter): generalize map_succ_at_top_eq to arbitrary Galois insertions; generalize tendsto_coe_iff to arbitary order-preserving embeddings
#### Estimated changes
modified src/analysis/specific_limits.lean
- \+/\- *lemma* tendsto_comp_succ_at_top_iff
- \- *lemma* map_succ_at_top_eq
- \+/\- *lemma* tendsto_comp_succ_at_top_iff
- \- *lemma* tendsto_coe_iff

modified src/order/filter/basic.lean
- \+/\- *lemma* at_top_ne_bot
- \+/\- *lemma* mem_at_top_sets
- \+/\- *lemma* map_at_top_eq
- \+ *lemma* tendsto_at_top_embedding
- \+ *lemma* map_at_top_eq_of_gc
- \+ *lemma* map_add_at_top_eq_nat
- \+ *lemma* map_sub_at_top_eq_nat
- \+ *lemma* tendso_add_at_top_nat
- \+ *lemma* tendso_sub_at_top_nat
- \+ *lemma* map_div_at_top_eq_nat
- \+/\- *lemma* at_top_ne_bot
- \+/\- *lemma* mem_at_top_sets
- \+/\- *lemma* map_at_top_eq

modified src/topology/instances/real.lean
- \+ *lemma* tendsto_coe_nat_real_at_top_iff
- \+ *lemma* tendsto_coe_nat_real_at_top_at_top
- \+ *lemma* tendsto_coe_int_real_at_top_iff
- \+ *lemma* tendsto_coe_int_real_at_top_at_top
- \- *lemma* tendsto_of_nat_at_top_at_top



## [2019-02-12 11:17:26+01:00](https://github.com/leanprover-community/mathlib/commit/c853c33)
chore(analysis/specific_limits): replace mul_add_one_le_pow by pow_ge_one_add_mul
#### Estimated changes
modified src/analysis/specific_limits.lean
- \- *lemma* mul_add_one_le_pow



## [2019-02-12 09:12:26](https://github.com/leanprover-community/mathlib/commit/41e3b6f)
refactor(data/list): add prop arg for easier usage ([#715](https://github.com/leanprover-community/mathlib/pull/715))
#### Estimated changes
modified src/data/list/basic.lean
- \+/\- *theorem* exists_or_eq_self_of_erasep
- \+/\- *theorem* exists_or_eq_self_of_erasep



## [2019-02-11 20:48:17-05:00](https://github.com/leanprover-community/mathlib/commit/d1ef181)
feat(topology/metric_space/gluing): Gluing metric spaces ([#695](https://github.com/leanprover-community/mathlib/pull/695))
#### Estimated changes
modified src/topology/metric_space/basic.lean
- \- *lemma* sum.one_dist_le
- \- *lemma* sum.one_dist_le'
- \- *lemma* sum.dist_eq
- \- *def* metric_space_sum

created src/topology/metric_space/gluing.lean
- \+ *lemma* glue_dist_glued_points
- \+ *lemma* sum.dist_eq_glue_dist
- \+ *lemma* sum.one_dist_le
- \+ *lemma* sum.one_dist_le'
- \+ *lemma* sum.dist_eq
- \+ *lemma* isometry_on_inl
- \+ *lemma* isometry_on_inr
- \+ *lemma* to_glue_commute
- \+ *lemma* to_glue_l_isometry
- \+ *lemma* to_glue_r_isometry
- \+ *def* glue_dist
- \+ *def* glue_metric_approx
- \+ *def* sum.dist
- \+ *def* metric_space_sum
- \+ *def* glue_premetric
- \+ *def* glue_space
- \+ *def* to_glue_l
- \+ *def* to_glue_r



## [2019-02-11 15:43:36-05:00](https://github.com/leanprover-community/mathlib/commit/8243300)
build(nightly): fix nightly
#### Estimated changes
modified .travis.yml

modified scripts/deploy_nightly.sh

modified scripts/lean_version.py



## [2019-02-11 16:50:18](https://github.com/leanprover-community/mathlib/commit/fb7e42d)
fix(group_theory/quotient_group): remove duplicate group_hom instance ([#713](https://github.com/leanprover-community/mathlib/pull/713))
#### Estimated changes
modified src/group_theory/quotient_group.lean



## [2019-02-11 10:13:54+01:00](https://github.com/leanprover-community/mathlib/commit/4b84aac)
fix(data/finsupp): duplicated instance
#### Estimated changes
modified src/data/finsupp.lean
- \+/\- *lemma* mul_sum
- \+/\- *lemma* mul_sum



## [2019-02-10 21:50:00](https://github.com/leanprover-community/mathlib/commit/091cad7)
feat(algebra/gcd_domain): normalize ([#668](https://github.com/leanprover-community/mathlib/pull/668))
#### Estimated changes
modified src/algebra/gcd_domain.lean
- \+ *lemma* normalize_zero
- \+ *lemma* normalize_one
- \+ *lemma* normalize_coe_units
- \+ *lemma* normalize_eq_zero
- \+ *lemma* normalize_eq_one
- \+ *lemma* normalize_eq_normalize_iff
- \+ *lemma* dvd_normalize_iff
- \+ *lemma* normalize_dvd_iff
- \+/\- *lemma* out_mk
- \+ *lemma* normalize_out
- \+ *lemma* normalize_lcm
- \+ *lemma* lcm_eq_normalize
- \+ *lemma* normalize_of_nonneg
- \+ *lemma* normalize_of_neg
- \+ *lemma* normalize_coe_nat
- \+/\- *lemma* out_mk
- \- *lemma* norm_unit_out
- \- *lemma* norm_unit_lcm
- \- *lemma* lcm_eq_mul_norm_unit
- \- *lemma* norm_unit_of_nonneg
- \- *lemma* norm_unit_of_neg
- \- *lemma* norm_unit_nat_coe
- \+ *theorem* associated_normalize
- \+ *theorem* normalize_associated
- \+ *theorem* normalize_mul
- \+ *theorem* normalize_idem
- \+ *theorem* normalize_eq_normalize
- \+ *theorem* dvd_antisymm_of_normalize_eq
- \+ *theorem* normalize_gcd
- \+/\- *theorem* gcd_mul_lcm
- \+ *theorem* gcd_eq_normalize
- \+/\- *theorem* gcd_zero_left
- \+/\- *theorem* gcd_zero_right
- \+/\- *theorem* gcd_same
- \+/\- *theorem* gcd_mul_left
- \+/\- *theorem* gcd_mul_right
- \+/\- *theorem* gcd_eq_left_iff
- \+/\- *theorem* gcd_eq_right_iff
- \+/\- *theorem* lcm_units_coe_left
- \+/\- *theorem* lcm_units_coe_right
- \+/\- *theorem* lcm_one_left
- \+/\- *theorem* lcm_one_right
- \+/\- *theorem* lcm_same
- \+/\- *theorem* lcm_mul_left
- \+/\- *theorem* lcm_mul_right
- \+/\- *theorem* lcm_eq_left_iff
- \+/\- *theorem* lcm_eq_right_iff
- \+ *theorem* coe_nat_abs_eq_normalize
- \- *theorem* associated_of_dvd_of_dvd
- \- *theorem* mul_norm_unit_eq_mul_norm_unit
- \- *theorem* dvd_antisymm_of_norm
- \- *theorem* norm_unit_gcd
- \+/\- *theorem* gcd_mul_lcm
- \- *theorem* gcd_eq_mul_norm_unit
- \+/\- *theorem* gcd_zero_left
- \+/\- *theorem* gcd_zero_right
- \+/\- *theorem* gcd_same
- \+/\- *theorem* gcd_mul_left
- \+/\- *theorem* gcd_mul_right
- \+/\- *theorem* gcd_eq_left_iff
- \+/\- *theorem* gcd_eq_right_iff
- \+/\- *theorem* lcm_units_coe_left
- \+/\- *theorem* lcm_units_coe_right
- \+/\- *theorem* lcm_one_left
- \+/\- *theorem* lcm_one_right
- \+/\- *theorem* lcm_same
- \+/\- *theorem* lcm_mul_left
- \+/\- *theorem* lcm_mul_right
- \+/\- *theorem* lcm_eq_left_iff
- \+/\- *theorem* lcm_eq_right_iff
- \- *theorem* coe_nat_abs_eq_mul_norm_unit
- \+ *def* normalize

modified src/data/polynomial.lean
- \+ *lemma* monic_normalize
- \- *lemma* monic_mul_norm_unit

modified src/ring_theory/unique_factorization_domain.lean



## [2019-02-10 12:36:00-05:00](https://github.com/leanprover-community/mathlib/commit/cfe582f)
Automate the deployment of nightly builds ([#707](https://github.com/leanprover-community/mathlib/pull/707))
* build(nightly): automate nightly releases of mathlib
#### Estimated changes
modified .travis.yml

created scripts/deploy_nightly.sh

created scripts/lean_version.py

modified scripts/update-mathlib.py



## [2019-02-10 16:44:30](https://github.com/leanprover-community/mathlib/commit/9b28db0)
refactor(*): refactor associates ([#710](https://github.com/leanprover-community/mathlib/pull/710))
#### Estimated changes
renamed src/ring_theory/associated.lean to src/algebra/associated.lean
- \- *lemma* nat.prime_iff_prime
- \- *lemma* nat.prime_iff_prime_int
- \- *lemma* out_mk
- \- *lemma* out_one
- \- *lemma* out_mul
- \- *lemma* dvd_out_iff
- \- *lemma* out_dvd_iff
- \- *lemma* out_top
- \- *lemma* norm_unit_out
- \- *theorem* irreducible_iff_nat_prime
- \- *def* associates_int_equiv_nat

modified src/algebra/gcd_domain.lean
- \+ *lemma* out_mk
- \+ *lemma* out_one
- \+ *lemma* out_mul
- \+ *lemma* dvd_out_iff
- \+ *lemma* out_dvd_iff
- \+ *lemma* out_top
- \+ *lemma* norm_unit_out
- \+ *lemma* norm_unit_of_nonneg
- \+ *lemma* norm_unit_of_neg
- \+ *lemma* norm_unit_nat_coe
- \+ *lemma* coe_gcd
- \+ *lemma* coe_lcm
- \+ *lemma* nat_abs_gcd
- \+ *lemma* nat_abs_lcm
- \+ *lemma* nat.prime_iff_prime
- \+ *lemma* nat.prime_iff_prime_int
- \+ *theorem* coe_nat_abs_eq_mul_norm_unit
- \+ *theorem* lcm_def
- \+ *theorem* gcd_dvd_left
- \+ *theorem* gcd_dvd_right
- \+ *theorem* dvd_gcd
- \+ *theorem* gcd_mul_lcm
- \+ *theorem* gcd_comm
- \+ *theorem* gcd_assoc
- \+ *theorem* gcd_self
- \+ *theorem* gcd_zero_left
- \+ *theorem* gcd_zero_right
- \+ *theorem* gcd_one_left
- \+ *theorem* gcd_one_right
- \+ *theorem* gcd_mul_left
- \+ *theorem* gcd_mul_right
- \+ *theorem* gcd_pos_of_non_zero_left
- \+ *theorem* gcd_pos_of_non_zero_right
- \+ *theorem* gcd_eq_zero_iff
- \+ *theorem* gcd_div
- \+ *theorem* gcd_dvd_gcd_of_dvd_left
- \+ *theorem* gcd_dvd_gcd_of_dvd_right
- \+ *theorem* gcd_dvd_gcd_mul_left
- \+ *theorem* gcd_dvd_gcd_mul_right
- \+ *theorem* gcd_dvd_gcd_mul_left_right
- \+ *theorem* gcd_dvd_gcd_mul_right_right
- \+ *theorem* gcd_eq_left
- \+ *theorem* gcd_eq_right
- \+ *theorem* lcm_comm
- \+ *theorem* lcm_assoc
- \+ *theorem* lcm_zero_left
- \+ *theorem* lcm_zero_right
- \+ *theorem* lcm_one_left
- \+ *theorem* lcm_one_right
- \+ *theorem* lcm_self
- \+ *theorem* dvd_lcm_left
- \+ *theorem* dvd_lcm_right
- \+ *theorem* lcm_dvd
- \+ *theorem* irreducible_iff_nat_prime
- \+ *def* lcm
- \+ *def* associates_int_equiv_nat

modified src/data/int/gcd.lean
- \- *lemma* norm_unit_of_nonneg
- \- *lemma* norm_unit_of_neg
- \- *lemma* norm_unit_nat_coe
- \- *lemma* coe_gcd
- \- *lemma* coe_lcm
- \- *lemma* nat_abs_gcd
- \- *lemma* nat_abs_lcm
- \- *theorem* coe_nat_abs_eq_mul_norm_unit
- \- *theorem* lcm_def
- \- *theorem* gcd_dvd_left
- \- *theorem* gcd_dvd_right
- \- *theorem* dvd_gcd
- \- *theorem* gcd_mul_lcm
- \- *theorem* gcd_comm
- \- *theorem* gcd_assoc
- \- *theorem* gcd_self
- \- *theorem* gcd_zero_left
- \- *theorem* gcd_zero_right
- \- *theorem* gcd_one_left
- \- *theorem* gcd_one_right
- \- *theorem* gcd_mul_left
- \- *theorem* gcd_mul_right
- \- *theorem* gcd_pos_of_non_zero_left
- \- *theorem* gcd_pos_of_non_zero_right
- \- *theorem* gcd_eq_zero_iff
- \- *theorem* gcd_div
- \- *theorem* gcd_dvd_gcd_of_dvd_left
- \- *theorem* gcd_dvd_gcd_of_dvd_right
- \- *theorem* gcd_dvd_gcd_mul_left
- \- *theorem* gcd_dvd_gcd_mul_right
- \- *theorem* gcd_dvd_gcd_mul_left_right
- \- *theorem* gcd_dvd_gcd_mul_right_right
- \- *theorem* gcd_eq_left
- \- *theorem* gcd_eq_right
- \- *theorem* lcm_comm
- \- *theorem* lcm_assoc
- \- *theorem* lcm_zero_left
- \- *theorem* lcm_zero_right
- \- *theorem* lcm_one_left
- \- *theorem* lcm_one_right
- \- *theorem* lcm_self
- \- *theorem* dvd_lcm_left
- \- *theorem* dvd_lcm_right
- \- *theorem* lcm_dvd
- \- *def* lcm

modified src/data/padics/padic_norm.lean

modified src/data/polynomial.lean

modified src/ring_theory/euclidean_domain.lean

modified src/ring_theory/ideals.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/unique_factorization_domain.lean



## [2019-02-10 14:25:05](https://github.com/leanprover-community/mathlib/commit/c25122b)
feat(algebra/archimedean): add fractional parts of floor_rings ([#709](https://github.com/leanprover-community/mathlib/pull/709))
#### Estimated changes
modified src/algebra/archimedean.lean
- \+ *lemma* floor_eq_iff
- \+ *lemma* fract_add_floor
- \+ *lemma* floor_add_fract
- \+ *lemma* fract_zero
- \+ *lemma* fract_coe
- \+ *lemma* fract_floor
- \+ *lemma* floor_fract
- \+ *lemma* fract_fract
- \+ *theorem* fract_nonneg
- \+ *theorem* fract_lt_one
- \+ *theorem* fract_eq_iff
- \+ *theorem* fract_eq_fract
- \+ *theorem* fract_add
- \+ *theorem* fract_mul_nat
- \+ *def* fract

modified src/algebra/group.lean



## [2019-02-10 14:01:02+01:00](https://github.com/leanprover-community/mathlib/commit/d6f84da)
feat(tactic/tidy): add `tidy?` syntax for reporting a tactic script ([#704](https://github.com/leanprover-community/mathlib/pull/704))
#### Estimated changes
modified docs/tactics.md

modified src/tactic/tidy.lean

modified test/tidy.lean
- \+/\- *def* tidy_test_0
- \+/\- *def* tidy_test_1
- \+/\- *def* d
- \+/\- *def* tidy_test_0
- \+/\- *def* tidy_test_1
- \+/\- *def* d



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
modified src/algebra/ring.lean
- \+ *def* nonzero_comm_ring.of_ne

modified src/data/polynomial.lean
- \+ *lemma* monic_mul
- \+ *lemma* monic_pow
- \+ *lemma* multiplicity_finite_of_degree_pos_of_monic
- \+ *lemma* multiplicity_X_sub_C_finite
- \+ *lemma* root_multiplicity_eq_multiplicity
- \+ *lemma* pow_root_multiplicity_dvd
- \+ *lemma* div_by_monic_mul_pow_root_multiplicity_eq
- \+ *lemma* eval_div_by_monic_pow_root_multiplicity_ne_zero
- \+ *def* nonzero_comm_ring.of_polynomial_ne
- \+ *def* decidable_dvd_monic
- \+ *def* root_multiplicity



## [2019-02-09 15:41:40](https://github.com/leanprover-community/mathlib/commit/088f753)
refactor(geo_sum): remove duplicate proofs about geometric sums ([#706](https://github.com/leanprover-community/mathlib/pull/706))
* feat(data/finset): add range_add_one
* feat(algebra/big_operators): geometric sum for semiring, ring and division ring
* refactor(geo_sum): remove duplicate proofs about geometric sums
#### Estimated changes
modified src/algebra/big_operators.lean
- \+ *lemma* geom_sum_inv
- \+/\- *theorem* geom_sum
- \+/\- *theorem* geom_sum

modified src/analysis/specific_limits.lean
- \- *lemma* sum_geometric'
- \- *lemma* sum_geometric

modified src/data/complex/basic.lean
- \- *lemma* inv_zero
- \- *theorem* mul_inv_cancel

modified src/data/complex/exponential.lean
- \- *lemma* geo_sum_eq
- \- *lemma* geo_sum_inv_eq



## [2019-02-09 15:38:37](https://github.com/leanprover-community/mathlib/commit/484d864)
add geometric sum ([#701](https://github.com/leanprover-community/mathlib/pull/701))
* feat(data/finset): add range_add_one
* feat(algebra/big_operators): geometric sum for semiring, ring and division ring
#### Estimated changes
modified src/algebra/big_operators.lean
- \+ *theorem* geom_sum_mul_add
- \+ *theorem* geom_sum_mul
- \+ *theorem* geom_sum

modified src/data/finset.lean
- \+ *theorem* range_add_one



## [2019-02-08 20:56:33-05:00](https://github.com/leanprover-community/mathlib/commit/22c7179)
build(update-mathlib): adjust the header of python script
#### Estimated changes
modified scripts/update-mathlib.py



## [2019-02-08 18:41:17-05:00](https://github.com/leanprover-community/mathlib/commit/8b51017)
build(update-mathlib): fix installation and documentation
#### Estimated changes
modified scripts/remote-install-update-mathlib.sh

modified scripts/setup-update-mathlib.sh

modified scripts/update-mathlib.py



## [2019-02-08 17:13:15-05:00](https://github.com/leanprover-community/mathlib/commit/650237b)
build(update-mathlib): install update-mathlib into `~/.mathlib/bin`
#### Estimated changes
modified scripts/remote-install-update-mathlib.sh

modified scripts/setup-update-mathlib.sh



## [2019-02-08 17:01:46-05:00](https://github.com/leanprover-community/mathlib/commit/814cb03)
build(update-mathlib): fix installation and documentation
#### Estimated changes
modified README.md

created scripts/remote-install-update-mathlib.sh



## [2019-02-08 16:55:19-05:00](https://github.com/leanprover-community/mathlib/commit/64065f4)
build(update-mathlib): improve installation and documentation
#### Estimated changes
modified .travis.yml

modified README.md

modified scripts/update-mathlib.py



## [2019-02-08 16:11:45-05:00](https://github.com/leanprover-community/mathlib/commit/4227f5c)
Deploy olean ([#697](https://github.com/leanprover-community/mathlib/pull/697))
* deploy(olean): deploy the olean files for every successful builds
#### Estimated changes
modified .travis.yml

modified README.md

created scripts/setup-update-mathlib.sh

created scripts/update-mathlib.py



## [2019-02-08 19:05:45](https://github.com/leanprover-community/mathlib/commit/11e19d8)
refactor(ring_theory/noetherian): make is_noetherian and is_noetherian_ring classes ([#689](https://github.com/leanprover-community/mathlib/pull/689))
* refactor(ring_theory/noetherian): make is_noetherian and is_noetherian_ring classes
* correct spelling mistake.
* add well_founded_submodule_gt
#### Estimated changes
modified src/field_theory/splitting_field.lean

modified src/ring_theory/noetherian.lean
- \+ *lemma* well_founded_submodule_gt
- \- *theorem* is_noetherian_prod
- \- *theorem* is_noetherian_pi
- \- *theorem* ring.is_noetherian_of_fintype
- \- *theorem* is_noetherian_ring_range
- \+/\- *def* is_noetherian_ring
- \- *def* is_noetherian
- \+/\- *def* is_noetherian_ring

modified src/ring_theory/polynomial.lean
- \+/\- *theorem* is_fg_degree_le
- \+/\- *theorem* is_noetherian_ring_polynomial
- \+/\- *theorem* is_fg_degree_le
- \+/\- *theorem* is_noetherian_ring_polynomial

modified src/ring_theory/principal_ideal_domain.lean
- \- *lemma* is_noetherian_ring



## [2019-02-08 13:11:06-05:00](https://github.com/leanprover-community/mathlib/commit/1f50e0d)
fix(build): fix the output keeping travis builds alive ([#702](https://github.com/leanprover-community/mathlib/pull/702))
#### Estimated changes
modified .travis.yml



## [2019-02-08 09:43:02-05:00](https://github.com/leanprover-community/mathlib/commit/0f2562e)
fix(build): fix the output keeping travis builds alive ([#700](https://github.com/leanprover-community/mathlib/pull/700))
#### Estimated changes
modified .travis.yml



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/cfd2b75)
feat(order/filter): break filter into smaller files
#### Estimated changes
renamed src/order/filter.lean to src/order/filter/basic.lean
- \- *lemma* rmap_compose
- \- *lemma* rcomap_compose
- \- *lemma* rcomap'_compose
- \- *theorem* rmap_sets
- \- *theorem* mem_rmap
- \- *theorem* rmap_rmap
- \- *theorem* rtendsto_def
- \- *theorem* rcomap_sets
- \- *theorem* rcomap_rcomap
- \- *theorem* rtendsto_iff_le_comap
- \- *theorem* rcomap'_sets
- \- *theorem* rcomap'_rcomap'
- \- *theorem* rtendsto'_def
- \- *theorem* tendsto_iff_rtendsto
- \- *theorem* tendsto_iff_rtendsto'
- \- *theorem* ptendsto_def
- \- *theorem* ptendsto_iff_rtendsto
- \- *theorem* pmap_res
- \- *theorem* tendsto_iff_ptendsto
- \- *theorem* tendsto_iff_ptendsto_univ
- \- *theorem* ptendsto'_def
- \- *theorem* ptendsto_of_ptendsto'
- \- *theorem* ptendsto'_of_ptendsto
- \- *def* rmap
- \- *def* rtendsto
- \- *def* rcomap
- \- *def* rcomap'
- \- *def* mem_rcomap'
- \- *def* rtendsto'
- \- *def* pmap
- \- *def* mem_pmap
- \- *def* ptendsto
- \- *def* pcomap'
- \- *def* ptendsto'

created src/order/filter/default.lean

created src/order/filter/partial.lean
- \+ *lemma* rmap_compose
- \+ *lemma* rcomap_compose
- \+ *lemma* rcomap'_compose
- \+ *theorem* rmap_sets
- \+ *theorem* mem_rmap
- \+ *theorem* rmap_rmap
- \+ *theorem* rtendsto_def
- \+ *theorem* rcomap_sets
- \+ *theorem* rcomap_rcomap
- \+ *theorem* rtendsto_iff_le_comap
- \+ *theorem* rcomap'_sets
- \+ *theorem* rcomap'_rcomap'
- \+ *theorem* rtendsto'_def
- \+ *theorem* tendsto_iff_rtendsto
- \+ *theorem* tendsto_iff_rtendsto'
- \+ *theorem* ptendsto_def
- \+ *theorem* ptendsto_iff_rtendsto
- \+ *theorem* pmap_res
- \+ *theorem* tendsto_iff_ptendsto
- \+ *theorem* tendsto_iff_ptendsto_univ
- \+ *theorem* ptendsto'_def
- \+ *theorem* ptendsto_of_ptendsto'
- \+ *theorem* ptendsto'_of_ptendsto
- \+ *def* rmap
- \+ *def* rtendsto
- \+ *def* rcomap
- \+ *def* rcomap'
- \+ *def* mem_rcomap'
- \+ *def* rtendsto'
- \+ *def* pmap
- \+ *def* mem_pmap
- \+ *def* ptendsto
- \+ *def* pcomap'
- \+ *def* ptendsto'



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/8db042f)
feat(data/rel): galois_connection (image r) (core r)
#### Estimated changes
modified src/data/rel.lean
- \+/\- *lemma* preimage_comp
- \+/\- *lemma* core_comp
- \+/\- *lemma* preimage_eq
- \+/\- *lemma* preimage_comp
- \+/\- *lemma* core_comp
- \+/\- *lemma* preimage_eq
- \+ *theorem* image_subset_iff
- \+ *theorem* core_preimage_gc
- \+/\- *def* restrict_domain
- \+/\- *def* restrict_domain



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/b2ba37c)
chore(*): fix errors introduced by rebasing
#### Estimated changes
deleted analysis/metric_space.lean
- \- *lemma* edist_eq_nndist
- \- *lemma* nndist_eq_edist
- \- *lemma* edist_ne_top
- \- *lemma* nndist_self
- \- *lemma* nndist_eq_dist
- \- *lemma* dist_eq_nndist
- \- *lemma* dist_eq_edist
- \- *lemma* edist_eq_dist
- \- *lemma* cauchy_of_metric
- \- *lemma* mem_uniformity_dist_edist
- \- *lemma* nhds_comap_dist
- \- *lemma* tendsto_iff_dist_tendsto_zero
- \- *lemma* dist_pi_def
- \- *lemma* second_countable_of_separable_metric_space
- \- *lemma* finite_cover_balls_of_compact
- \- *lemma* countable_closure_of_compact
- \- *lemma* lebesgue_number_lemma_of_metric
- \- *lemma* lebesgue_number_lemma_of_metric_sUnion
- \- *theorem* dist_self
- \- *theorem* eq_of_dist_eq_zero
- \- *theorem* dist_comm
- \- *theorem* edist_dist
- \- *theorem* dist_eq_zero
- \- *theorem* zero_eq_dist
- \- *theorem* dist_triangle
- \- *theorem* dist_triangle_left
- \- *theorem* dist_triangle_right
- \- *theorem* swap_dist
- \- *theorem* abs_dist_sub_le
- \- *theorem* dist_nonneg
- \- *theorem* dist_le_zero
- \- *theorem* dist_pos
- \- *theorem* eq_of_nndist_eq_zero
- \- *theorem* nndist_comm
- \- *theorem* nndist_eq_zero
- \- *theorem* zero_eq_nndist
- \- *theorem* nndist_triangle
- \- *theorem* nndist_triangle_left
- \- *theorem* nndist_triangle_right
- \- *theorem* mem_ball
- \- *theorem* mem_ball'
- \- *theorem* mem_closed_ball
- \- *theorem* ball_subset_closed_ball
- \- *theorem* pos_of_mem_ball
- \- *theorem* mem_ball_self
- \- *theorem* mem_ball_comm
- \- *theorem* ball_subset_ball
- \- *theorem* ball_disjoint
- \- *theorem* ball_disjoint_same
- \- *theorem* ball_subset
- \- *theorem* ball_half_subset
- \- *theorem* exists_ball_subset_ball
- \- *theorem* ball_eq_empty_iff_nonpos
- \- *theorem* uniformity_dist
- \- *theorem* uniformity_dist'
- \- *theorem* mem_uniformity_dist
- \- *theorem* dist_mem_uniformity
- \- *theorem* uniform_continuous_of_metric
- \- *theorem* uniform_embedding_of_metric
- \- *theorem* totally_bounded_of_metric
- \- *theorem* nhds_eq_metric
- \- *theorem* mem_nhds_iff_metric
- \- *theorem* is_open_metric
- \- *theorem* is_open_ball
- \- *theorem* ball_mem_nhds
- \- *theorem* tendsto_nhds_of_metric
- \- *theorem* continuous_of_metric
- \- *theorem* exists_delta_of_continuous
- \- *theorem* tendsto_nhds_topo_metric
- \- *theorem* continuous_topo_metric
- \- *theorem* tendsto_at_top_metric
- \- *theorem* mem_nhds_within
- \- *theorem* rtendsto_nhds_within
- \- *theorem* rtendsto'_nhds_within
- \- *theorem* ptendsto_nhds_within
- \- *theorem* tendsto_nhds_within
- \- *theorem* cauchy_seq_metric
- \- *theorem* cauchy_seq_metric'
- \- *theorem* eq_of_forall_dist_le
- \- *theorem* uniformity_edist'
- \- *theorem* uniformity_edist
- \- *theorem* real.dist_eq
- \- *theorem* real.dist_0_eq_abs
- \- *theorem* abs_dist
- \- *theorem* subtype.dist_eq
- \- *theorem* uniform_continuous_dist'
- \- *theorem* uniform_continuous_dist
- \- *theorem* continuous_dist'
- \- *theorem* continuous_dist
- \- *theorem* tendsto_dist
- \- *theorem* is_closed_ball
- \- *theorem* mem_closure_iff'
- \- *def* metric_space.uniform_space_of_dist
- \- *def* nndist
- \- *def* ball
- \- *def* closed_ball
- \- *def* metric_space.replace_uniformity
- \- *def* metric_space.induced

deleted data/real/cau_seq_filter.lean
- \- *lemma* set_seq_of_cau_filter_mem_sets
- \- *lemma* set_seq_of_cau_filter_inhabited
- \- *lemma* set_seq_of_cau_filter_spec
- \- *lemma* mono_of_mono_succ
- \- *lemma* set_seq_of_cau_filter_monotone'
- \- *lemma* set_seq_of_cau_filter_monotone
- \- *lemma* seq_of_cau_filter_mem_set_seq
- \- *lemma* seq_of_cau_filter_is_cauchy'
- \- *lemma* cauchy_seq_of_dist_tendsto_0
- \- *lemma* tendsto_div
- \- *lemma* seq_of_cau_filter_is_cauchy
- \- *lemma* le_nhds_cau_filter_lim
- \- *lemma* tendsto_limit
- \- *lemma* cauchy_of_filter_cauchy
- \- *lemma* filter_cauchy_of_cauchy
- \- *lemma* cau_seq_iff_cauchy_seq
- \- *theorem* complete_of_cauchy_seq_tendsto
- \- *def* set_seq_of_cau_filter

modified src/analysis/normed_space/basic.lean

modified src/data/real/cau_seq_filter.lean

modified src/measure_theory/borel_space.lean

modified src/topology/continuity.lean
- \+/\- *theorem* continuous_at_within_univ
- \+/\- *theorem* continuous_at_within_iff_continuous_at_restrict
- \+/\- *theorem* continuous_at_within_univ
- \+/\- *theorem* continuous_at_within_iff_continuous_at_restrict
- \+/\- *def* continuous_at_within
- \+/\- *def* continuous_at_within

modified src/topology/instances/ennreal.lean

modified src/topology/metric_space/basic.lean

modified src/topology/sequences.lean



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/8e4aafa)
feat(analysis/metric): convergence wrt nhds_within
#### Estimated changes
modified analysis/metric_space.lean
- \+ *theorem* mem_nhds_within
- \+ *theorem* rtendsto_nhds_within
- \+ *theorem* rtendsto'_nhds_within
- \+ *theorem* ptendsto_nhds_within
- \+ *theorem* tendsto_nhds_within



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/f5d73bd)
feat(analysis/topology/continuity): add some variations
#### Estimated changes
created analysis/metric_space.lean
- \+ *lemma* edist_eq_nndist
- \+ *lemma* nndist_eq_edist
- \+ *lemma* edist_ne_top
- \+ *lemma* nndist_self
- \+ *lemma* nndist_eq_dist
- \+ *lemma* dist_eq_nndist
- \+ *lemma* dist_eq_edist
- \+ *lemma* edist_eq_dist
- \+ *lemma* cauchy_of_metric
- \+ *lemma* mem_uniformity_dist_edist
- \+ *lemma* nhds_comap_dist
- \+ *lemma* tendsto_iff_dist_tendsto_zero
- \+ *lemma* dist_pi_def
- \+ *lemma* second_countable_of_separable_metric_space
- \+ *lemma* finite_cover_balls_of_compact
- \+ *lemma* countable_closure_of_compact
- \+ *lemma* lebesgue_number_lemma_of_metric
- \+ *lemma* lebesgue_number_lemma_of_metric_sUnion
- \+ *theorem* dist_self
- \+ *theorem* eq_of_dist_eq_zero
- \+ *theorem* dist_comm
- \+ *theorem* edist_dist
- \+ *theorem* dist_eq_zero
- \+ *theorem* zero_eq_dist
- \+ *theorem* dist_triangle
- \+ *theorem* dist_triangle_left
- \+ *theorem* dist_triangle_right
- \+ *theorem* swap_dist
- \+ *theorem* abs_dist_sub_le
- \+ *theorem* dist_nonneg
- \+ *theorem* dist_le_zero
- \+ *theorem* dist_pos
- \+ *theorem* eq_of_nndist_eq_zero
- \+ *theorem* nndist_comm
- \+ *theorem* nndist_eq_zero
- \+ *theorem* zero_eq_nndist
- \+ *theorem* nndist_triangle
- \+ *theorem* nndist_triangle_left
- \+ *theorem* nndist_triangle_right
- \+ *theorem* mem_ball
- \+ *theorem* mem_ball'
- \+ *theorem* mem_closed_ball
- \+ *theorem* ball_subset_closed_ball
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
- \+ *theorem* uniformity_dist
- \+ *theorem* uniformity_dist'
- \+ *theorem* mem_uniformity_dist
- \+ *theorem* dist_mem_uniformity
- \+ *theorem* uniform_continuous_of_metric
- \+ *theorem* uniform_embedding_of_metric
- \+ *theorem* totally_bounded_of_metric
- \+ *theorem* nhds_eq_metric
- \+ *theorem* mem_nhds_iff_metric
- \+ *theorem* is_open_metric
- \+ *theorem* is_open_ball
- \+ *theorem* ball_mem_nhds
- \+ *theorem* tendsto_nhds_of_metric
- \+ *theorem* continuous_of_metric
- \+ *theorem* exists_delta_of_continuous
- \+ *theorem* tendsto_nhds_topo_metric
- \+ *theorem* continuous_topo_metric
- \+ *theorem* tendsto_at_top_metric
- \+ *theorem* cauchy_seq_metric
- \+ *theorem* cauchy_seq_metric'
- \+ *theorem* eq_of_forall_dist_le
- \+ *theorem* uniformity_edist'
- \+ *theorem* uniformity_edist
- \+ *theorem* real.dist_eq
- \+ *theorem* real.dist_0_eq_abs
- \+ *theorem* abs_dist
- \+ *theorem* subtype.dist_eq
- \+ *theorem* uniform_continuous_dist'
- \+ *theorem* uniform_continuous_dist
- \+ *theorem* continuous_dist'
- \+ *theorem* continuous_dist
- \+ *theorem* tendsto_dist
- \+ *theorem* is_closed_ball
- \+ *theorem* mem_closure_iff'
- \+ *def* metric_space.uniform_space_of_dist
- \+ *def* nndist
- \+ *def* ball
- \+ *def* closed_ball
- \+ *def* metric_space.replace_uniformity
- \+ *def* metric_space.induced

created data/real/cau_seq_filter.lean
- \+ *lemma* set_seq_of_cau_filter_mem_sets
- \+ *lemma* set_seq_of_cau_filter_inhabited
- \+ *lemma* set_seq_of_cau_filter_spec
- \+ *lemma* mono_of_mono_succ
- \+ *lemma* set_seq_of_cau_filter_monotone'
- \+ *lemma* set_seq_of_cau_filter_monotone
- \+ *lemma* seq_of_cau_filter_mem_set_seq
- \+ *lemma* seq_of_cau_filter_is_cauchy'
- \+ *lemma* cauchy_seq_of_dist_tendsto_0
- \+ *lemma* tendsto_div
- \+ *lemma* seq_of_cau_filter_is_cauchy
- \+ *lemma* le_nhds_cau_filter_lim
- \+ *lemma* tendsto_limit
- \+ *lemma* cauchy_of_filter_cauchy
- \+ *lemma* filter_cauchy_of_cauchy
- \+ *lemma* cau_seq_iff_cauchy_seq
- \+ *theorem* complete_of_cauchy_seq_tendsto
- \+ *def* set_seq_of_cau_filter

modified src/analysis/exponential.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/data/padics/hensel.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/topological_structures.lean

modified src/topology/compact_open.lean

modified src/topology/continuity.lean
- \+ *lemma* continuous_iff_continuous_at
- \+/\- *lemma* continuous_at_iff_ultrafilter
- \+ *lemma* open_dom_of_pcontinuous
- \+ *lemma* pcontinuous_iff'
- \+ *lemma* continuous_at_subtype_val
- \+ *lemma* continuous_at_length
- \+ *lemma* continuous_at_remove_nth
- \- *lemma* continuous_iff_tendsto
- \+/\- *lemma* continuous_at_iff_ultrafilter
- \- *lemma* tendsto_subtype_val
- \- *lemma* tendsto_length
- \- *lemma* tendsto_remove_nth
- \+ *theorem* continuous_at_within_univ
- \+ *theorem* continuous_at_within_iff_continuous_at_restrict
- \+ *theorem* continuous_on_iff
- \+ *theorem* continuous_on_iff_continuous_restrict
- \+ *theorem* continuous_on_iff'
- \+ *theorem* continuous_at_within_iff_ptendsto_res
- \+ *def* continuous_at
- \+ *def* continuous_at_within
- \+ *def* continuous_on
- \+ *def* pcontinuous

modified src/topology/instances/complex.lean

modified src/topology/instances/ennreal.lean

modified src/topology/instances/nnreal.lean

modified src/topology/instances/real.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/completion.lean



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/e0b8253)
feat (analysis/topology/topological_space): properties of nhds, nhds_within
#### Estimated changes
modified src/topology/basic.lean
- \+/\- *lemma* tendsto_const_nhds
- \+ *lemma* map_nhds_within
- \- *lemma* tendsto_nhds
- \+/\- *lemma* tendsto_const_nhds
- \+ *theorem* all_mem_nhds
- \+ *theorem* all_mem_nhds_filter
- \+ *theorem* rtendsto_nhds
- \+ *theorem* rtendsto'_nhds
- \+ *theorem* ptendsto_nhds
- \+ *theorem* ptendsto'_nhds
- \+ *theorem* tendsto_nhds
- \+ *theorem* nhds_within_eq
- \+ *theorem* nhds_within_univ
- \+ *theorem* mem_nhds_within
- \+ *theorem* nhds_within_mono
- \+ *theorem* nhds_within_restrict
- \+ *theorem* nhds_within_eq_nhds_within
- \+ *theorem* nhs_within_eq_of_open
- \+ *theorem* nhds_within_empty
- \+ *theorem* nhds_within_union
- \+ *theorem* nhds_within_inter
- \+ *theorem* nhds_within_inter'
- \+ *theorem* tendsto_if_nhds_within
- \+ *theorem* mem_nhds_induced
- \+ *theorem* nhds_induced
- \+ *theorem* map_nhds_induced_of_surjective
- \+ *theorem* mem_nhds_subtype
- \+ *theorem* nhds_subtype
- \+ *theorem* principal_subtype
- \+ *theorem* mem_nhds_within_subtype
- \+ *theorem* nhds_within_subtype
- \+ *theorem* nhds_within_eq_map_subtype_val
- \+ *theorem* tendsto_at_within_iff_subtype
- \+ *def* nhds_within



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/a96fa3b)
feat(order/filter): convergence for relations and partial functions
#### Estimated changes
modified src/data/pfun.lean
- \+/\- *lemma* mem_core
- \+/\- *lemma* mem_core_res
- \+/\- *lemma* preimage_as_subtype
- \+/\- *lemma* mem_core
- \+/\- *lemma* mem_core_res
- \+/\- *lemma* preimage_as_subtype
- \+/\- *theorem* mem_restrict
- \+/\- *theorem* mem_restrict
- \+/\- *def* graph'
- \+/\- *def* core
- \+/\- *def* graph'
- \+/\- *def* core

renamed data/rel.lean to src/data/rel.lean

modified src/order/filter.lean
- \+ *lemma* tendsto_if
- \+ *lemma* rmap_compose
- \+ *lemma* rcomap_compose
- \+ *lemma* rcomap'_compose
- \+ *theorem* mem_inf_principal
- \+ *theorem* le_map_comap_of_surjective'
- \+ *theorem* map_comap_of_surjective'
- \+ *theorem* le_map_comap_of_surjective
- \+ *theorem* map_comap_of_surjective
- \+ *theorem* rmap_sets
- \+ *theorem* mem_rmap
- \+ *theorem* rmap_rmap
- \+ *theorem* rtendsto_def
- \+ *theorem* rcomap_sets
- \+ *theorem* rcomap_rcomap
- \+ *theorem* rtendsto_iff_le_comap
- \+ *theorem* rcomap'_sets
- \+ *theorem* rcomap'_rcomap'
- \+ *theorem* rtendsto'_def
- \+ *theorem* tendsto_iff_rtendsto
- \+ *theorem* tendsto_iff_rtendsto'
- \+ *theorem* ptendsto_def
- \+ *theorem* ptendsto_iff_rtendsto
- \+ *theorem* pmap_res
- \+ *theorem* tendsto_iff_ptendsto
- \+ *theorem* tendsto_iff_ptendsto_univ
- \+ *theorem* ptendsto'_def
- \+ *theorem* ptendsto_of_ptendsto'
- \+ *theorem* ptendsto'_of_ptendsto
- \+ *def* rmap
- \+ *def* rtendsto
- \+ *def* rcomap
- \+ *def* rcomap'
- \+ *def* mem_rcomap'
- \+ *def* rtendsto'
- \+ *def* pmap
- \+ *def* mem_pmap
- \+ *def* ptendsto
- \+ *def* pcomap'
- \+ *def* ptendsto'



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/4444464)
feat(data/pfun): add restrict, preimage, core, etc.
#### Estimated changes
modified src/data/pfun.lean
- \+ *lemma* image_def
- \+ *lemma* mem_image
- \+ *lemma* image_mono
- \+ *lemma* image_inter
- \+ *lemma* image_union
- \+ *lemma* preimage_def
- \+ *lemma* preimage_subset_dom
- \+ *lemma* preimage_mono
- \+ *lemma* preimage_inter
- \+ *lemma* preimage_union
- \+ *lemma* preimage_univ
- \+ *lemma* core_def
- \+ *lemma* mem_core
- \+ *lemma* compl_dom_subset_core
- \+ *lemma* core_mono
- \+ *lemma* core_inter
- \+ *lemma* mem_core_res
- \+ *lemma* core_res
- \+ *lemma* core_restrict
- \+ *lemma* preimage_subset_core
- \+ *lemma* preimage_eq
- \+ *lemma* core_eq
- \+ *lemma* preimage_as_subtype
- \+ *theorem* mem_eq
- \+ *theorem* mem_restrict
- \+ *theorem* mem_dom
- \+ *theorem* dom_eq
- \+ *theorem* as_subtype_eq_of_mem
- \+ *theorem* mem_restrict
- \+ *theorem* mem_res
- \+ *theorem* res_univ
- \+ *def* graph'
- \+ *def* res
- \+ *def* image
- \+ *def* preimage
- \+ *def* mem_preimage
- \+ *def* core



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/cae5c8b)
fix(data/rel): make composition local notation
#### Estimated changes
modified data/rel.lean



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/4779af7)
feat(data/rel): a type for binary relations
#### Estimated changes
created data/rel.lean
- \+ *lemma* inv_def
- \+ *lemma* inv_inv
- \+ *lemma* codom_inv
- \+ *lemma* dom_inv
- \+ *lemma* comp_assoc
- \+ *lemma* comp_right_id
- \+ *lemma* comp_left_id
- \+ *lemma* inv_id
- \+ *lemma* inv_comp
- \+ *lemma* mem_image
- \+ *lemma* image_mono
- \+ *lemma* image_inter
- \+ *lemma* image_union
- \+ *lemma* image_id
- \+ *lemma* image_comp
- \+ *lemma* image_univ
- \+ *lemma* mem_preimage
- \+ *lemma* preimage_def
- \+ *lemma* preimage_mono
- \+ *lemma* preimage_inter
- \+ *lemma* preimage_union
- \+ *lemma* preimage_id
- \+ *lemma* preimage_comp
- \+ *lemma* preimage_univ
- \+ *lemma* mem_core
- \+ *lemma* core_mono
- \+ *lemma* core_inter
- \+ *lemma* core_union
- \+ *lemma* core_univ
- \+ *lemma* core_id
- \+ *lemma* core_comp
- \+ *lemma* image_eq
- \+ *lemma* preimage_eq
- \+ *lemma* preimage_eq_core
- \+ *def* rel
- \+ *def* inv
- \+ *def* dom
- \+ *def* codom
- \+ *def* comp
- \+ *def* image
- \+ *def* preimage
- \+ *def* core
- \+ *def* restrict_domain
- \+ *def* graph



## [2019-02-08 09:28:04-05:00](https://github.com/leanprover-community/mathlib/commit/126d573)
feat(data/set/basic,logic/function): small additions and renamings
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* val_image
- \+ *lemma* val_range
- \+ *lemma* subtype.val_range
- \+/\- *lemma* range_coe_subtype
- \- *lemma* subtype_val_image
- \- *lemma* subtype_val_range
- \+/\- *lemma* range_coe_subtype
- \+ *theorem* inter_subset
- \+ *theorem* val_image_subset
- \+ *theorem* val_image_univ
- \+ *theorem* image_preimage_val
- \+ *theorem* preimage_val_eq_preimage_val_iff

modified src/logic/function.lean
- \+ *theorem* restrict_eq
- \+ *def* restrict

modified src/order/filter.lean

modified src/topology/continuity.lean



## [2019-02-07 22:32:47](https://github.com/leanprover-community/mathlib/commit/1ed7ad1)
feat(algebra/archimedean): abs_sub_lt_one_of_floor_eq_floor ([#693](https://github.com/leanprover-community/mathlib/pull/693))
* abs_diff_lt_one_of_floor_eq_floor
* better name
#### Estimated changes
modified src/algebra/archimedean.lean
- \+ *lemma* abs_sub_lt_one_of_floor_eq_floor



## [2019-02-07 19:37:17+01:00](https://github.com/leanprover-community/mathlib/commit/177b5eb)
feat(linear_algebra): dimension of the base field is 1
#### Estimated changes
modified src/algebra/module.lean

modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis_singleton_one

modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_of_field



## [2019-02-07 19:36:51+01:00](https://github.com/leanprover-community/mathlib/commit/0f24030)
refactor(src/data/finset): supr/infi as a directed supr/infi of finite inf/sup
#### Estimated changes
modified src/data/finset.lean
- \+ *lemma* supr_eq_supr_finset
- \+ *lemma* infi_eq_infi_finset
- \+ *lemma* Union_eq_Union_finset
- \+ *lemma* Inter_eq_Inter_finset
- \+ *theorem* sup_congr
- \+ *theorem* inf_congr

modified src/data/set/lattice.lean
- \+ *theorem* monotone_inter
- \+ *theorem* monotone_union
- \+ *theorem* monotone_set_of

modified src/order/filter.lean
- \+/\- *lemma* infi_sets_eq'
- \+ *lemma* infi_sets_eq_finite
- \+/\- *lemma* supr_join
- \+/\- *lemma* infi_sup_eq
- \- *lemma* Inf_eq_finite_sets
- \- *lemma* infi_insert_finset
- \- *lemma* infi_empty_finset
- \- *lemma* inf_left_comm
- \+/\- *lemma* infi_sets_eq'
- \- *lemma* Inf_sets_eq_finite
- \+/\- *lemma* supr_join
- \- *lemma* binfi_sup_eq
- \+/\- *lemma* infi_sup_eq
- \- *theorem* monotone_inter
- \- *theorem* monotone_set_of

modified src/order/lattice.lean
- \+ *lemma* sup_left_comm
- \+ *lemma* directed_of_sup
- \+ *lemma* inf_left_comm
- \+ *lemma* directed_of_inf



## [2019-02-07 15:56:26+01:00](https://github.com/leanprover-community/mathlib/commit/eeed321)
chore(linear_algebra/basic): relate map/comap/ker/range/comp with 0 and smul; use map/comap Galois connection
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *lemma* map_zero
- \+ *lemma* gc_map_comap
- \+/\- *lemma* map_bot
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+/\- *lemma* comap_top
- \+ *lemma* comap_inf
- \+ *lemma* comap_infi
- \+ *lemma* comap_zero
- \+ *lemma* comap_smul
- \+ *lemma* map_smul
- \+ *lemma* comap_smul'
- \+ *lemma* map_smul'
- \+ *lemma* range_le_bot_iff
- \+ *lemma* ker_smul
- \+ *lemma* ker_smul'
- \+ *lemma* range_smul
- \+ *lemma* range_smul'
- \+/\- *lemma* comap_top
- \+/\- *lemma* map_bot
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp
- \+ *theorem* comp_assoc
- \+ *theorem* comp_zero
- \+ *theorem* zero_comp
- \+ *theorem* smul_comp
- \+ *theorem* comp_smul
- \+ *theorem* range_zero
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp



## [2019-02-07 14:58:25+01:00](https://github.com/leanprover-community/mathlib/commit/e98999e)
chore(algebra/pi_instances): generalize pi.list/multiset/finset_prod/sum_apply to dependent types
#### Estimated changes
modified src/algebra/pi_instances.lean
- \+/\- *lemma* list_prod_apply
- \+/\- *lemma* multiset_prod_apply
- \+/\- *lemma* finset_prod_apply
- \+/\- *lemma* list_prod_apply
- \+/\- *lemma* multiset_prod_apply
- \+/\- *lemma* finset_prod_apply



## [2019-02-07 14:58:25+01:00](https://github.com/leanprover-community/mathlib/commit/ad7ef86)
refactor(set_theory/cardinal): split up mk_Union_le_mk_sigma, add mk_Union_eq_mk_sigma; add equiv congruence for subtype
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* subtype_congr
- \+ *def* set_congr

modified src/data/set/lattice.lean
- \+ *lemma* surjective_sigma_to_Union
- \+ *lemma* injective_sigma_to_Union
- \+ *lemma* bijective_sigma_to_Union
- \+ *def* sigma_to_Union

modified src/set_theory/cardinal.lean
- \+/\- *theorem* mk_eq_of_injective
- \+ *theorem* mk_Union_eq_sum_mk
- \+/\- *theorem* mk_eq_of_injective



## [2019-02-07 13:13:39+01:00](https://github.com/leanprover-community/mathlib/commit/8a1de24)
feat(data/{list/alist,finmap}): implicit key type ([#662](https://github.com/leanprover-community/mathlib/pull/662))
* feat(data/{list/alist,finmap}): implicit key type
Make the key type α implicit in both alist and finmap. This brings these
types into line with the underlying sigma and simplifies usage since α
is inferred from the value function type β : α → Type v.
* doc(data/list/alist): alist is stored as a linked list
#### Estimated changes
modified src/data/finmap.lean
- \+/\- *theorem* alist.to_finmap_eq
- \+/\- *theorem* alist.to_finmap_entries
- \+/\- *theorem* lift_on_to_finmap
- \+/\- *theorem* ext
- \+/\- *theorem* mem_def
- \+/\- *theorem* mem_to_finmap
- \+/\- *theorem* keys_val
- \+/\- *theorem* keys_ext
- \+/\- *theorem* mem_keys
- \+/\- *theorem* empty_to_finmap
- \+/\- *theorem* not_mem_empty_entries
- \+/\- *theorem* not_mem_empty
- \+/\- *theorem* keys_empty
- \+/\- *theorem* lookup_to_finmap
- \+/\- *theorem* lookup_is_some
- \+/\- *theorem* insert_to_finmap
- \+/\- *theorem* insert_of_pos
- \+/\- *theorem* insert_entries_of_neg
- \+/\- *theorem* mem_insert
- \+/\- *theorem* replace_to_finmap
- \+/\- *theorem* keys_replace
- \+/\- *theorem* mem_replace
- \+/\- *theorem* erase_to_finmap
- \+/\- *theorem* keys_erase_to_finset
- \+/\- *theorem* keys_erase
- \+/\- *theorem* mem_erase
- \+/\- *theorem* extract_eq_lookup_erase
- \+/\- *theorem* alist.to_finmap_eq
- \+/\- *theorem* alist.to_finmap_entries
- \+/\- *theorem* lift_on_to_finmap
- \+/\- *theorem* ext
- \+/\- *theorem* mem_def
- \+/\- *theorem* mem_to_finmap
- \+/\- *theorem* keys_val
- \+/\- *theorem* keys_ext
- \+/\- *theorem* mem_keys
- \+/\- *theorem* empty_to_finmap
- \+/\- *theorem* not_mem_empty_entries
- \+/\- *theorem* not_mem_empty
- \+/\- *theorem* keys_empty
- \+/\- *theorem* lookup_to_finmap
- \+/\- *theorem* lookup_is_some
- \+/\- *theorem* insert_to_finmap
- \+/\- *theorem* insert_of_pos
- \+/\- *theorem* insert_entries_of_neg
- \+/\- *theorem* mem_insert
- \+/\- *theorem* replace_to_finmap
- \+/\- *theorem* keys_replace
- \+/\- *theorem* mem_replace
- \+/\- *theorem* erase_to_finmap
- \+/\- *theorem* keys_erase_to_finset
- \+/\- *theorem* keys_erase
- \+/\- *theorem* mem_erase
- \+/\- *theorem* extract_eq_lookup_erase
- \+/\- *def* alist.to_finmap
- \+/\- *def* keys
- \+/\- *def* singleton
- \+/\- *def* lookup
- \+/\- *def* insert
- \+/\- *def* replace
- \+/\- *def* erase
- \+/\- *def* extract
- \+/\- *def* alist.to_finmap
- \+/\- *def* keys
- \+/\- *def* singleton
- \+/\- *def* lookup
- \+/\- *def* insert
- \+/\- *def* replace
- \+/\- *def* erase
- \+/\- *def* extract

modified src/data/list/alist.lean
- \+/\- *theorem* ext
- \+/\- *theorem* mem_def
- \+/\- *theorem* mem_of_perm
- \+/\- *theorem* mem_keys
- \+/\- *theorem* keys_nodup
- \+/\- *theorem* not_mem_empty_entries
- \+/\- *theorem* not_mem_empty
- \+/\- *theorem* keys_empty
- \+/\- *theorem* lookup_is_some
- \+/\- *theorem* perm_lookup
- \+/\- *theorem* insert_of_pos
- \+/\- *theorem* insert_entries_of_neg
- \+/\- *theorem* keys_insert
- \+/\- *theorem* mem_insert
- \+/\- *theorem* perm_insert
- \+/\- *theorem* keys_replace
- \+/\- *theorem* mem_replace
- \+/\- *theorem* perm_replace
- \+/\- *theorem* keys_erase
- \+/\- *theorem* mem_erase
- \+/\- *theorem* perm_erase
- \+/\- *theorem* extract_eq_lookup_erase
- \+/\- *theorem* ext
- \+/\- *theorem* mem_def
- \+/\- *theorem* mem_of_perm
- \+/\- *theorem* mem_keys
- \+/\- *theorem* keys_nodup
- \+/\- *theorem* not_mem_empty_entries
- \+/\- *theorem* not_mem_empty
- \+/\- *theorem* keys_empty
- \+/\- *theorem* lookup_is_some
- \+/\- *theorem* perm_lookup
- \+/\- *theorem* insert_of_pos
- \+/\- *theorem* insert_entries_of_neg
- \+/\- *theorem* keys_insert
- \+/\- *theorem* mem_insert
- \+/\- *theorem* perm_insert
- \+/\- *theorem* keys_replace
- \+/\- *theorem* mem_replace
- \+/\- *theorem* perm_replace
- \+/\- *theorem* keys_erase
- \+/\- *theorem* mem_erase
- \+/\- *theorem* perm_erase
- \+/\- *theorem* extract_eq_lookup_erase
- \+/\- *def* keys
- \+/\- *def* singleton
- \+/\- *def* lookup
- \+/\- *def* insert
- \+/\- *def* replace
- \+/\- *def* foldl
- \+/\- *def* erase
- \+/\- *def* extract
- \+/\- *def* keys
- \+/\- *def* singleton
- \+/\- *def* lookup
- \+/\- *def* insert
- \+/\- *def* replace
- \+/\- *def* foldl
- \+/\- *def* erase
- \+/\- *def* extract



## [2019-02-07 13:02:53+01:00](https://github.com/leanprover-community/mathlib/commit/46d1009)
feat(analysis/metric_space): Isometries ([#657](https://github.com/leanprover-community/mathlib/pull/657))
#### Estimated changes
created src/topology/metric_space/isometry.lean
- \+ *lemma* isometry_emetric_iff_metric
- \+ *lemma* isometry.injective
- \+ *lemma* isometry_id
- \+ *lemma* isometry.continuous
- \+ *lemma* isometry.inv
- \+ *lemma* emetric.isometry.diam_image
- \+ *lemma* isometry_subtype_val
- \+ *lemma* metric.isometry.diam_image
- \+ *lemma* coe_eq_to_equiv
- \+ *lemma* coe_eq_to_homeomorph
- \+ *lemma* to_homeomorph_to_equiv
- \+ *lemma* symm_comp_self
- \+ *lemma* self_comp_symm
- \+ *lemma* range_coe
- \+ *lemma* image_symm
- \+ *lemma* preimage_symm
- \+ *lemma* isometry.isometric_on_range
- \+ *lemma* isometry.isometric_on_range_apply
- \+ *theorem* isometry.edist_eq
- \+ *theorem* isometry.dist_eq
- \+ *theorem* isometry_subsingleton
- \+ *theorem* isometry.comp
- \+ *theorem* isometry.uniform_embedding
- \+ *def* isometry



## [2019-02-07 10:22:13](https://github.com/leanprover-community/mathlib/commit/8911b8c)
feat(algebra/order_functions): max_lt_max and min_lt_min ([#692](https://github.com/leanprover-community/mathlib/pull/692))
#### Estimated changes
modified src/algebra/order_functions.lean
- \+ *lemma* max_lt_max
- \+ *lemma* min_lt_min



## [2019-02-06 20:15:47](https://github.com/leanprover-community/mathlib/commit/51f80a3)
feat(data/quot): quotient.ind' ([#691](https://github.com/leanprover-community/mathlib/pull/691))
* feat(data/quot): quotient.ind'
* correct elaborator tag; theorems not definitions
#### Estimated changes
modified src/data/quot.lean



## [2019-02-06 10:58:04+01:00](https://github.com/leanprover-community/mathlib/commit/9615b38)
feat(data/real): completeness criterion for Cauchy sequences (closes [#654](https://github.com/leanprover-community/mathlib/pull/654))
#### Estimated changes
modified src/data/real/cau_seq_filter.lean
- \+ *lemma* F_pos
- \+ *lemma* F_lim
- \+ *lemma* FB_pos
- \+ *lemma* FB_lim
- \+/\- *lemma* set_seq_of_cau_filter_mem_sets
- \+/\- *lemma* set_seq_of_cau_filter_inhabited
- \+/\- *lemma* seq_of_cau_filter_mem_set_seq
- \+ *lemma* seq_of_cau_filter_bound
- \+/\- *lemma* le_nhds_cau_filter_lim
- \+/\- *lemma* set_seq_of_cau_filter_mem_sets
- \+/\- *lemma* set_seq_of_cau_filter_inhabited
- \+/\- *lemma* seq_of_cau_filter_mem_set_seq
- \- *lemma* seq_of_cau_filter_is_cauchy'
- \- *lemma* cauchy_seq_of_dist_tendsto_0
- \+/\- *lemma* le_nhds_cau_filter_lim
- \+/\- *theorem* complete_of_cauchy_seq_tendsto
- \+ *theorem* emetric.complete_of_convergent_controlled_sequences
- \+ *theorem* metric.complete_of_convergent_controlled_sequences
- \+/\- *theorem* complete_of_cauchy_seq_tendsto



## [2019-02-06 10:36:56+01:00](https://github.com/leanprover-community/mathlib/commit/3ac7967)
feat(analysis/metric_space): add premetric spaces (closes [#652](https://github.com/leanprover-community/mathlib/pull/652))
#### Estimated changes
created src/topology/metric_space/premetric_space.lean
- \+ *lemma* metric_quot_dist_eq
- \+ *def* dist_setoid



## [2019-02-06 10:29:32+01:00](https://github.com/leanprover-community/mathlib/commit/e93fa30)
feat(category/fold): `foldl` and `foldr` for `traversable` structures ([#376](https://github.com/leanprover-community/mathlib/pull/376))
#### Estimated changes
created src/category/fold.lean
- \+ *lemma* fold_map_hom
- \+ *lemma* free.map_eq_map
- \+ *lemma* foldr.unop_of_free_monoid
- \+ *lemma* mfoldr.unop_of_free_monoid
- \+ *lemma* fold_map_hom
- \+ *lemma* fold_map_hom_free
- \+ *lemma* fold_mfoldl_cons
- \+ *lemma* fold_mfoldr_cons
- \+ *lemma* foldl.of_free_monoid_comp_free_mk
- \+ *lemma* foldr.of_free_monoid_comp_free_mk
- \+ *lemma* mfoldl.of_free_monoid_comp_free_mk
- \+ *lemma* mfoldr.of_free_monoid_comp_free_mk
- \+ *lemma* to_list_spec
- \+ *lemma* fold_map_map
- \+ *lemma* foldl_to_list
- \+ *lemma* foldr_to_list
- \+ *lemma* to_list_map
- \+ *lemma* mfoldl_to_list
- \+ *lemma* mfoldr_to_list
- \+ *theorem* foldl_map
- \+ *theorem* foldr_map
- \+ *theorem* to_list_eq_self
- \+ *theorem* length_to_list
- \+ *theorem* mfoldl_map
- \+ *theorem* mfoldr_map
- \+ *def* fold_map
- \+ *def* foldl
- \+ *def* foldl.mk
- \+ *def* foldl.of_free_monoid
- \+ *def* foldr
- \+ *def* foldr.mk
- \+ *def* foldr.get
- \+ *def* foldr.of_free_monoid
- \+ *def* mfoldl
- \+ *def* mfoldl.mk
- \+ *def* mfoldl.of_free_monoid
- \+ *def* mfoldr
- \+ *def* mfoldr.mk
- \+ *def* mfoldr.get
- \+ *def* mfoldr.of_free_monoid
- \+ *def* fold_map
- \+ *def* foldl
- \+ *def* foldr
- \+ *def* to_list
- \+ *def* length
- \+ *def* mfoldl
- \+ *def* mfoldr
- \+ *def* map_fold
- \+ *def* free.mk
- \+ *def* free.map



## [2019-02-06 09:59:29+01:00](https://github.com/leanprover-community/mathlib/commit/c82243a)
feat(analysis/normed_space): bounded linear maps with the operator norm form a normed space (closes [#680](https://github.com/leanprover-community/mathlib/pull/680))
#### Estimated changes
modified src/analysis/normed_space/basic.lean

created src/analysis/normed_space/operator_norm.lean
- \+ *lemma* exists_bound
- \+ *lemma* exists_bound'
- \+ *lemma* norm_of_unit_ball_bdd_above
- \+ *lemma* zero_in_im_ball
- \+ *lemma* operator_norm_nonneg
- \+ *lemma* bounded_by_operator_norm_on_unit_vector
- \+ *lemma* bounded_by_operator_norm_on_unit_ball
- \+ *lemma* operator_norm_bounded_by
- \+ *theorem* ext
- \+ *theorem* bounded_by_operator_norm
- \+ *theorem* operator_norm_triangle
- \+ *theorem* operator_norm_zero_iff
- \+ *theorem* operator_norm_homogeneous
- \+ *def* bounded_linear_maps

modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* cSup_intro'



## [2019-02-05 19:47:08](https://github.com/leanprover-community/mathlib/commit/d5a1b46)
to_nat_le_to_nat ([#685](https://github.com/leanprover-community/mathlib/pull/685))
#### Estimated changes
modified src/data/int/basic.lean
- \+ *theorem* to_nat_le_to_nat



## [2019-02-05 14:26:19-05:00](https://github.com/leanprover-community/mathlib/commit/9f79d2e)
fix(tactic/h_generalize): fix name resolution in h_generalize ([#688](https://github.com/leanprover-community/mathlib/pull/688))
#### Estimated changes
modified src/tactic/interactive.lean



## [2019-02-05 14:13:55-05:00](https://github.com/leanprover-community/mathlib/commit/a0d8ae1)
feat(tactic/replaceable): supplement `def_replacer` with attribute `replaceable`
#### Estimated changes
modified src/data/string.lean
- \- *def* map_tokens

created src/data/string/defs.lean
- \+ *def* map_tokens
- \+ *def* over_list

modified src/meta/expr.lean
- \+ *def* append_suffix

modified src/tactic/replacer.lean



## [2019-02-04 19:35:17-05:00](https://github.com/leanprover-community/mathlib/commit/178c09d)
feat(natural_isomorphism): componentwise isos are isos ([#671](https://github.com/leanprover-community/mathlib/pull/671))
#### Estimated changes
modified src/category_theory/isomorphism.lean
- \+ *lemma* hom_inv_id
- \+ *lemma* inv_hom_id
- \+ *lemma* hom_inv_id_assoc
- \+ *lemma* inv_hom_id_assoc
- \- *def* hom_inv_id
- \- *def* inv_hom_id

modified src/category_theory/natural_isomorphism.lean



## [2019-02-04 20:49:37](https://github.com/leanprover-community/mathlib/commit/9a8f1b0)
feat(algebra/group_power): gpow_add_one ([#683](https://github.com/leanprover-community/mathlib/pull/683))
* feat(algebra/group_power): gpow_add_one
* feat(data/nat//basic): int.coe_nat_abs
#### Estimated changes
modified src/algebra/group_power.lean
- \+ *theorem* gpow_add_one
- \+ *theorem* add_one_gsmul
- \+ *theorem* gpow_one_add
- \+ *theorem* one_add_gsmul

modified src/data/int/basic.lean
- \+ *theorem* coe_nat_abs



## [2019-02-04 19:00:17](https://github.com/leanprover-community/mathlib/commit/5395232)
remove simp on set_coe_eq_subtype ([#682](https://github.com/leanprover-community/mathlib/pull/682))
#### Estimated changes
modified src/data/set/basic.lean
- \+/\- *theorem* set.set_coe_eq_subtype
- \+/\- *theorem* set.set_coe_eq_subtype

modified src/group_theory/sylow.lean

modified src/tactic/subtype_instance.lean



## [2019-02-04 10:43:58+01:00](https://github.com/leanprover-community/mathlib/commit/5e5f1e2)
fix(data/*/Ico): succ_top is too aggressive as a simp lemma ([#678](https://github.com/leanprover-community/mathlib/pull/678))
#### Estimated changes
modified src/data/finset.lean
- \+/\- *theorem* succ_top
- \+/\- *theorem* succ_top

modified src/data/list/basic.lean
- \+/\- *theorem* succ_top
- \+/\- *theorem* succ_top

modified src/data/multiset.lean
- \+/\- *theorem* succ_top
- \+/\- *theorem* succ_top



## [2019-02-03 22:31:10](https://github.com/leanprover-community/mathlib/commit/2539251)
feat(data/nat/cast): abs_cast
#### Estimated changes
modified src/data/nat/cast.lean
- \+ *theorem* abs_cast



## [2019-02-03 17:00:41-05:00](https://github.com/leanprover-community/mathlib/commit/d01e523)
feat(category_theory/kleisli): monoids, const applicative functor and kleisli categories ([#660](https://github.com/leanprover-community/mathlib/pull/660))
* feat(category_theory/kleisli): monoids, const applicative functor and
kleisli categories
#### Estimated changes
modified src/algebra/group.lean
- \+ *lemma* free_monoid.one_def
- \+ *lemma* free_monoid.mul_def
- \+ *lemma* free_add_monoid.zero_def
- \+ *lemma* free_add_monoid.add_def
- \+ *def* free_monoid
- \+ *def* free_add_monoid

modified src/category/applicative.lean

modified src/category/basic.lean
- \+ *lemma* fish_pure
- \+ *lemma* fish_pipe
- \+ *lemma* fish_assoc
- \+ *def* fish

modified src/category/functor.lean
- \+ *def* const.mk'
- \+/\- *def* add_const
- \+ *def* add_const.mk
- \+ *def* add_const.run
- \+/\- *def* add_const

modified src/category/traversable/basic.lean

modified src/category_theory/category.lean
- \+ *lemma* End.one_def
- \+ *lemma* End.mul_def
- \+/\- *def* End
- \+/\- *def* End

created src/category_theory/instances/kleisli.lean
- \+ *lemma* Kleisli.id_def
- \+ *lemma* Kleisli.comp_def
- \+ *def* Kleisli
- \+ *def* Kleisli.mk

modified src/category_theory/instances/rings.lean

modified src/category_theory/natural_isomorphism.lean

modified src/category_theory/opposites.lean
- \+ *lemma* op_inj
- \+ *lemma* unop_inj
- \+ *lemma* opposite.unop_one
- \+ *lemma* opposite.unop_mul
- \+ *lemma* opposite.op_one
- \+ *lemma* opposite.op_mul

modified src/data/fintype.lean



## [2019-02-03 17:01:45+01:00](https://github.com/leanprover-community/mathlib/commit/f5bd340)
cleanup(*): removing uses of bare `have` ([#676](https://github.com/leanprover-community/mathlib/pull/676))
#### Estimated changes
modified src/data/int/basic.lean

modified src/linear_algebra/basic.lean



## [2019-02-03 02:14:48-05:00](https://github.com/leanprover-community/mathlib/commit/544f35c)
Update README.md
#### Estimated changes
modified README.md



## [2019-02-03 02:06:28](https://github.com/leanprover-community/mathlib/commit/b3e1e6f)
fix(README): update URL for build status icon ([#681](https://github.com/leanprover-community/mathlib/pull/681))
#### Estimated changes
modified README.md



## [2019-02-03 01:08:36](https://github.com/leanprover-community/mathlib/commit/044b6fa)
feat(algebra/euclidean_domain): discrete field to euclidean domain ([#674](https://github.com/leanprover-community/mathlib/pull/674))
#### Estimated changes
modified src/algebra/euclidean_domain.lean



## [2019-02-02 19:04:50-05:00](https://github.com/leanprover-community/mathlib/commit/3109c4b)
chore(purge_olean.sh): a few small improvements ([#661](https://github.com/leanprover-community/mathlib/pull/661))
* purge empty directories
* Only print if an .olean is rm'd. This reduces the noise and reduces the
script run time.
* use git top-level dir to make the script relocatable
* only affect src and test dirs
* use bash instead of sed
#### Estimated changes
modified purge_olean.sh



## [2019-02-02 18:43:29-05:00](https://github.com/leanprover-community/mathlib/commit/8590ff2)
fix(functor_category): remove superfluous coercions ([#670](https://github.com/leanprover-community/mathlib/pull/670))
#### Estimated changes
modified src/category_theory/functor_category.lean



## [2019-02-02 18:42:36-05:00](https://github.com/leanprover-community/mathlib/commit/a09dc9f)
cleanup(category_theory/cones): tidying up, after making opposites work better ([#675](https://github.com/leanprover-community/mathlib/pull/675))
#### Estimated changes
modified src/category_theory/limits/cones.lean
- \+/\- *lemma* cones_obj
- \+/\- *lemma* cones_obj
- \+/\- *def* cones
- \+/\- *def* cones



## [2019-02-02 18:41:09-05:00](https://github.com/leanprover-community/mathlib/commit/b084cfc)
fix(category_theory/equivalence): duplicated namespace prefix ([#669](https://github.com/leanprover-community/mathlib/pull/669))
#### Estimated changes
modified src/category_theory/equivalence.lean



## [2019-02-02 17:59:12-05:00](https://github.com/leanprover-community/mathlib/commit/e501d02)
fix(replacer): better flow control in replacer when tactic fails ([#673](https://github.com/leanprover-community/mathlib/pull/673))
The main consequence is better error reporting.
#### Estimated changes
modified src/tactic/replacer.lean



## [2019-02-02 18:42:12](https://github.com/leanprover-community/mathlib/commit/0393ccb)
feat(ring_theory/algebra): subalgebra_of_subring ([#664](https://github.com/leanprover-community/mathlib/pull/664))
#### Estimated changes
modified src/ring_theory/algebra.lean
- \+ *lemma* mem_subalgebra_of_subring
- \+ *def* alg_hom_int
- \+ *def* subalgebra_of_subring
- \- *def* ring.to_ℤ_algebra
- \- *def* is_ring_hom.to_ℤ_alg_hom



## [2019-02-01 23:00:55-05:00](https://github.com/leanprover-community/mathlib/commit/f529870)
feat(data/nat/gcd/coprime): some easy simp lemmas ([#677](https://github.com/leanprover-community/mathlib/pull/677))
#### Estimated changes
modified src/data/nat/gcd.lean
- \+ *theorem* coprime_zero_left
- \+ *theorem* coprime_zero_right
- \+ *theorem* coprime_one_left_iff
- \+ *theorem* coprime_one_right_iff
- \+ *theorem* coprime_self



## [2019-02-02 01:41:01](https://github.com/leanprover-community/mathlib/commit/6925e4d)
feat(algebra/euclidean_domain): lcm ([#665](https://github.com/leanprover-community/mathlib/pull/665))
#### Estimated changes
modified src/algebra/euclidean_domain.lean
- \+ *lemma* lcm_dvd_iff
- \+ *lemma* lcm_zero_left
- \+ *lemma* lcm_zero_right
- \+ *lemma* lcm_eq_zero_iff
- \+ *lemma* gcd_mul_lcm
- \+ *theorem* dvd_lcm_left
- \+ *theorem* dvd_lcm_right
- \+ *theorem* lcm_dvd
- \+ *def* lcm



## [2019-02-01 20:07:31-05:00](https://github.com/leanprover-community/mathlib/commit/fb60145)
cleanup: replace `begin intros ...` with lambdas ([#672](https://github.com/leanprover-community/mathlib/pull/672))
#### Estimated changes
modified src/category_theory/whiskering.lean

modified src/category_theory/yoneda.lean

modified src/data/set/basic.lean



## [2019-02-01 22:48:10](https://github.com/leanprover-community/mathlib/commit/ed0d24a)
feat(algebra/euclidean_domain): add quotient_zero axiom to euclidean_domain ([#666](https://github.com/leanprover-community/mathlib/pull/666))
#### Estimated changes
modified src/algebra/euclidean_domain.lean
- \+ *lemma* div_zero
- \+/\- *lemma* zero_div
- \+/\- *lemma* zero_div
- \+ *theorem* mul_div_assoc

modified src/data/polynomial.lean
- \- *lemma* div_zero



## [2019-02-01 12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/d8f6dc4)
feat(src/tactic/explode): improve printing of references
#### Estimated changes
modified src/tactic/explode.lean



## [2019-02-01 12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/a32de36)
feat(src/tactic/explode): add printing for conclusions of sintros
#### Estimated changes
modified src/tactic/explode.lean



## [2019-02-01 12:26:22+01:00](https://github.com/leanprover-community/mathlib/commit/a08c9a7)
add printing for conclusions of sintros
#### Estimated changes
modified src/tactic/explode.lean



## [2019-02-01 12:13:59+01:00](https://github.com/leanprover-community/mathlib/commit/c9e4f8e)
fix(tactic/inarith): fix denominator normalization of products
#### Estimated changes
modified src/tactic/linarith.lean

modified test/linarith.lean



## [2019-02-01 12:13:31+01:00](https://github.com/leanprover-community/mathlib/commit/52adfd7)
feat(tactic,tactic/interactive): add set tactic, a variant of let
#### Estimated changes
modified docs/tactics.md

modified src/tactic/basic.lean

modified src/tactic/interactive.lean



## [2019-02-01 09:53:51+01:00](https://github.com/leanprover-community/mathlib/commit/89bc63c)
feat(ring_theory/noetherian): is_noetherian_ring_range
#### Estimated changes
modified src/ring_theory/noetherian.lean
- \+ *theorem* is_noetherian_ring_range



## [2019-02-01 00:30:09](https://github.com/leanprover-community/mathlib/commit/8e381f6)
feat(ring_theory/algebra_operations): multiplication of submodules of an algebra ([#658](https://github.com/leanprover-community/mathlib/pull/658))
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *lemma* add_eq_sup
- \+ *lemma* zero_eq_bot

created src/ring_theory/algebra_operations.lean
- \+ *theorem* mul_mem_mul
- \+ *theorem* mul_le
- \+ *theorem* span_mul_span
- \+ *theorem* fg_mul
- \+ *theorem* mul_bot
- \+ *theorem* bot_mul
- \+ *theorem* mul_le_mul
- \+ *theorem* mul_le_mul_left
- \+ *theorem* mul_le_mul_right
- \+ *theorem* mul_sup
- \+ *theorem* sup_mul
- \+ *theorem* mul_mem_mul_rev

modified src/ring_theory/ideal_operations.lean
- \- *lemma* add_eq_sup
- \- *lemma* zero_eq_bot

