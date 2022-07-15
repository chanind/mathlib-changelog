## [2020-10-31 22:44:12](https://github.com/leanprover-community/mathlib/commit/6f7c539)
docs(order/complete_lattice): make two docstrings more detailed ([#4859](https://github.com/leanprover-community/mathlib/pull/4859))
Following [discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Constructing.20a.20complete.20lattice), clarify information about how to construct a complete lattice while preserving good definitional equalities.
#### Estimated changes
Modified src/order/complete_lattice.lean




## [2020-10-31 20:22:31](https://github.com/leanprover-community/mathlib/commit/51cbb83)
refactor(tactic/norm_num): move norm_num extensions ([#4822](https://github.com/leanprover-community/mathlib/pull/4822))
[#4820](https://github.com/leanprover-community/mathlib/pull/4820) adds the long awaited ability for `norm_num` to be extended in other files. There are two norm_num extensions currently in mathlib: `norm_digits`, which was previously exposed as a standalone tactic, and `eval_prime`, which was a part of `norm_num` and so caused `tactic.norm_num` to depend on `data.nat.prime`. This PR turns both of these into norm_num extensions, and changes the dependencies so that `data.nat.prime` can import `norm_num` rather than the other way around (which required splitting `pnat` primality and gcd facts to their own file).
#### Estimated changes
Modified archive/imo/imo1959_q1.lean


Modified archive/imo/imo1960_q1.lean


Modified archive/imo/imo1969_q1.lean


Modified archive/imo/imo1988_q6.lean


Modified src/data/nat/digits.lean


Modified src/data/nat/prime.lean
- \+ *lemma* tactic.norm_num.is_prime_helper
- \+ *lemma* tactic.norm_num.min_fac_bit0
- \+ *theorem* tactic.norm_num.min_fac_helper.n_pos
- \+ *def* tactic.norm_num.min_fac_helper
- \+ *lemma* tactic.norm_num.min_fac_helper_0
- \+ *lemma* tactic.norm_num.min_fac_helper_1
- \+ *lemma* tactic.norm_num.min_fac_helper_2
- \+ *lemma* tactic.norm_num.min_fac_helper_3
- \+ *lemma* tactic.norm_num.min_fac_helper_4
- \+ *lemma* tactic.norm_num.min_fac_helper_5
- \+ *lemma* tactic.norm_num.min_fac_ne_bit0
- \+ *lemma* tactic.norm_num.not_prime_helper

Modified src/number_theory/divisors.lean


Modified src/tactic/norm_num.lean
- \- *lemma* norm_num.is_prime_helper
- \- *lemma* norm_num.min_fac_bit0
- \- *theorem* norm_num.min_fac_helper.n_pos
- \- *def* norm_num.min_fac_helper
- \- *lemma* norm_num.min_fac_helper_0
- \- *lemma* norm_num.min_fac_helper_1
- \- *lemma* norm_num.min_fac_helper_2
- \- *lemma* norm_num.min_fac_helper_3
- \- *lemma* norm_num.min_fac_helper_4
- \- *lemma* norm_num.min_fac_helper_5
- \- *lemma* norm_num.min_fac_ne_bit0
- \- *lemma* norm_num.not_prime_helper

Modified test/linarith.lean


Modified test/norm_digits.lean


Modified test/norm_num.lean


Modified test/omega.lean




## [2020-10-31 17:41:26](https://github.com/leanprover-community/mathlib/commit/be161d1)
feat(category_theory/sites): functor inclusion constructions ([#4845](https://github.com/leanprover-community/mathlib/pull/4845))
#### Estimated changes
Modified src/category_theory/sites/sieves.lean
- \+ *def* category_theory.sieve.sieve_of_subfunctor
- \+ *lemma* category_theory.sieve.sieve_of_subfunctor_apply
- \+ *lemma* category_theory.sieve.sieve_of_subfunctor_functor_inclusion



## [2020-10-31 17:41:24](https://github.com/leanprover-community/mathlib/commit/d91c878)
chore(group_theory/group_action): introduce `smul_comm_class` ([#4770](https://github.com/leanprover-community/mathlib/pull/4770))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* linear_map.algebra_module.smul_apply
- \- *def* linear_map.restrict_scalars
- \- *lemma* linear_map.smul_apply'
- \- *lemma* map_smul_eq_smul_map

Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_map.map_smul_of_tower
- \+ *def* linear_map.restrict_scalars

Modified src/analysis/convex/basic.lean


Modified src/data/complex/module.lean


Modified src/group_theory/group_action.lean
- \- *theorem* mul_smul
- \+/\- *lemma* smul_assoc
- \- *lemma* smul_comm
- \+ *lemma* smul_comm_class.symm
- \+ *lemma* smul_one_smul

Modified src/linear_algebra/basic.lean
- \+ *def* linear_map.applyₗ'
- \+/\- *lemma* linear_map.smul_apply
- \+/\- *theorem* linear_map.smul_comp

Modified src/linear_algebra/matrix.lean


Modified src/representation_theory/maschke.lean


Modified src/ring_theory/derivation.lean


Modified src/topology/algebra/module.lean




## [2020-10-31 15:07:49](https://github.com/leanprover-community/mathlib/commit/9a03bdf)
chore(algebra/ordered_group): use implicit args, add `add_eq_coe` ([#4853](https://github.com/leanprover-community/mathlib/pull/4853))
* Use implicit arguments in various `iff` lemmas about `with_top`.
* Add `add_eq_coe`.
* Rewrite `with_top.ordered_add_comm_monoid` moving `begin .. end` blocks inside the structure.
This way we don't depend on the fact that `refine` doesn't introduce any `id`s and it's easier to see right away which block proves which statement.
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* with_top.add_eq_coe
- \+/\- *lemma* with_top.add_eq_top
- \+/\- *lemma* with_top.add_lt_top
- \+/\- *lemma* with_top.add_top
- \+/\- *lemma* with_top.top_add

Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.add_eq_top
- \+/\- *lemma* ennreal.add_lt_top
- \+ *lemma* ennreal.coe_finset_sup
- \+/\- *lemma* ennreal.coe_le_iff
- \+/\- *lemma* ennreal.le_coe_iff
- \+/\- *lemma* ennreal.lt_iff_exists_coe

Modified src/order/bounded_lattice.lean
- \+/\- *theorem* with_top.coe_le_iff
- \+ *theorem* with_top.coe_lt_iff
- \+/\- *theorem* with_top.le_coe_iff
- \+/\- *theorem* with_top.lt_iff_exists_coe

Modified src/order/conditionally_complete_lattice.lean


Modified src/topology/metric_space/basic.lean




## [2020-10-31 13:30:44](https://github.com/leanprover-community/mathlib/commit/e14c378)
refactor(order/filter): move some proofs to `bases` ([#3478](https://github.com/leanprover-community/mathlib/pull/3478))
Move some proofs to `order/filter/bases` and add `filter.has_basis` versions.
Non-bc API changes:
* `filter.inf_ne_bot_iff`; change `∀ {U V}, U ∈ f → V ∈ g → ...` to `∀ ⦃U⦄, U ∈ f → ∀ ⦃V⦄, V ∈ g → ...`
  so that `simp` lemmas about `∀ U ∈ f` can further simplify the result;
* `filter.inf_eq_bot_iff`: similarly, change `∃ U V, ...` to `∃ (U ∈ f) (V ∈ g), ...`
* `cluster_pt_iff`: similarly, change `∀ {U V : set α}, U ∈ 𝓝 x → V ∈ F → ...` to
  `∀ ⦃U : set α⦄ (hU : U ∈ 𝓝 x) ⦃V⦄ (hV : V ∈ F), ...`
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.inf_basis_ne_bot_iff
- \+ *lemma* filter.has_basis.inf_ne_bot_iff
- \+ *lemma* filter.has_basis.inf_principal_ne_bot_iff
- \+ *lemma* filter.inf_eq_bot_iff
- \+ *lemma* filter.inf_ne_bot_iff
- \+ *lemma* filter.inf_ne_bot_iff_frequently_left
- \+ *lemma* filter.inf_ne_bot_iff_frequently_right
- \+ *lemma* filter.inf_principal_ne_bot_iff
- \+ *lemma* filter.le_iff_forall_disjoint_principal_compl
- \+ *lemma* filter.le_iff_forall_inf_principal_compl
- \+ *lemma* filter.mem_iff_disjoint_principal_compl
- \+ *lemma* filter.mem_iff_inf_principal_compl

Modified src/order/filter/basic.lean
- \- *lemma* filter.inf_eq_bot_iff
- \- *lemma* filter.inf_ne_bot_iff
- \- *lemma* filter.inf_ne_bot_iff_frequently_left
- \- *lemma* filter.inf_ne_bot_iff_frequently_right
- \- *lemma* filter.inf_principal_ne_bot_iff
- \- *lemma* filter.le_iff_forall_inf_principal_compl
- \- *lemma* filter.mem_iff_inf_principal_compl

Modified src/topology/algebra/ordered.lean


Modified src/topology/basic.lean


Modified src/topology/uniform_space/separation.lean




## [2020-10-31 08:44:02](https://github.com/leanprover-community/mathlib/commit/f9c8abe)
chore(data/finset/basic): a few lemmas about `finset.piecewise` ([#4852](https://github.com/leanprover-community/mathlib/pull/4852))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.le_piecewise_of_le_of_le
- \+ *lemma* finset.piecewise_cases
- \+ *lemma* finset.piecewise_congr
- \+ *lemma* finset.piecewise_le_of_le_of_le
- \+ *lemma* finset.piecewise_mem_set_pi
- \+ *lemma* finset.piecewise_singleton
- \+ *lemma* finset.update_piecewise
- \+ *lemma* finset.update_piecewise_of_mem
- \+ *lemma* finset.update_piecewise_of_not_mem

Modified src/data/set/function.lean
- \+ *lemma* set.piecewise_mem_pi



## [2020-10-31 08:44:00](https://github.com/leanprover-community/mathlib/commit/7756265)
chore(linear_algebra/affine_space/ordered): compare endpoints to midpoint ([#4851](https://github.com/leanprover-community/mathlib/pull/4851))
#### Estimated changes
Modified src/linear_algebra/affine_space/ordered.lean
- \+ *lemma* left_le_midpoint
- \+ *lemma* midpoint_le_left
- \+ *lemma* midpoint_le_right
- \+ *lemma* right_le_midpoint



## [2020-10-31 08:43:59](https://github.com/leanprover-community/mathlib/commit/1f61621)
feat(linear_algebra/affine_space/affine_map): add `affine_map.proj` ([#4850](https://github.com/leanprover-community/mathlib/pull/4850))
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.pi_line_map_apply
- \+ *def* affine_map.proj
- \+ *lemma* affine_map.proj_apply
- \+ *lemma* affine_map.proj_linear

Modified src/linear_algebra/affine_space/midpoint.lean
- \+ *lemma* pi_midpoint_apply



## [2020-10-31 08:43:57](https://github.com/leanprover-community/mathlib/commit/6a44930)
refactor(data/pnat): move data.pnat.prime ([#4839](https://github.com/leanprover-community/mathlib/pull/4839))
Remove the dependency `data.pnat.basic -> data.nat.prime`. Needed for [#4822](https://github.com/leanprover-community/mathlib/pull/4822).
#### Estimated changes
Modified src/data/pnat/basic.lean
- \- *theorem* nat.primes.coe_pnat_inj
- \- *theorem* nat.primes.coe_pnat_nat
- \- *lemma* pnat.coprime.coprime_dvd_left
- \- *lemma* pnat.coprime.factor_eq_gcd_left
- \- *lemma* pnat.coprime.factor_eq_gcd_left_right
- \- *lemma* pnat.coprime.factor_eq_gcd_right
- \- *lemma* pnat.coprime.factor_eq_gcd_right_right
- \- *lemma* pnat.coprime.gcd_mul
- \- *lemma* pnat.coprime.gcd_mul_left_cancel
- \- *lemma* pnat.coprime.gcd_mul_left_cancel_right
- \- *lemma* pnat.coprime.gcd_mul_right_cancel
- \- *lemma* pnat.coprime.gcd_mul_right_cancel_right
- \- *lemma* pnat.coprime.mul
- \- *lemma* pnat.coprime.mul_right
- \- *lemma* pnat.coprime.pow
- \- *lemma* pnat.coprime.symm
- \- *def* pnat.coprime
- \- *lemma* pnat.coprime_coe
- \- *lemma* pnat.coprime_one
- \- *theorem* pnat.dvd_gcd
- \- *theorem* pnat.dvd_lcm_left
- \- *theorem* pnat.dvd_lcm_right
- \- *lemma* pnat.dvd_prime
- \- *lemma* pnat.eq_one_of_lt_two
- \- *lemma* pnat.exists_prime_and_dvd
- \- *def* pnat.gcd
- \- *theorem* pnat.gcd_coe
- \- *lemma* pnat.gcd_comm
- \- *theorem* pnat.gcd_dvd_left
- \- *theorem* pnat.gcd_dvd_right
- \- *lemma* pnat.gcd_eq_left
- \- *lemma* pnat.gcd_eq_left_iff_dvd
- \- *lemma* pnat.gcd_eq_right_iff_dvd
- \- *theorem* pnat.gcd_mul_lcm
- \- *lemma* pnat.gcd_one
- \- *def* pnat.lcm
- \- *theorem* pnat.lcm_coe
- \- *theorem* pnat.lcm_dvd
- \- *lemma* pnat.not_prime_one
- \- *lemma* pnat.one_coprime
- \- *lemma* pnat.one_gcd
- \- *lemma* pnat.prime.ne_one
- \- *lemma* pnat.prime.not_dvd_one
- \- *lemma* pnat.prime.one_lt
- \- *def* pnat.prime
- \- *lemma* pnat.prime_two

Modified src/data/pnat/factors.lean


Added src/data/pnat/prime.lean
- \+ *theorem* nat.primes.coe_pnat_inj
- \+ *theorem* nat.primes.coe_pnat_nat
- \+ *lemma* pnat.coprime.coprime_dvd_left
- \+ *lemma* pnat.coprime.factor_eq_gcd_left
- \+ *lemma* pnat.coprime.factor_eq_gcd_left_right
- \+ *lemma* pnat.coprime.factor_eq_gcd_right
- \+ *lemma* pnat.coprime.factor_eq_gcd_right_right
- \+ *lemma* pnat.coprime.gcd_mul
- \+ *lemma* pnat.coprime.gcd_mul_left_cancel
- \+ *lemma* pnat.coprime.gcd_mul_left_cancel_right
- \+ *lemma* pnat.coprime.gcd_mul_right_cancel
- \+ *lemma* pnat.coprime.gcd_mul_right_cancel_right
- \+ *lemma* pnat.coprime.mul
- \+ *lemma* pnat.coprime.mul_right
- \+ *lemma* pnat.coprime.pow
- \+ *lemma* pnat.coprime.symm
- \+ *def* pnat.coprime
- \+ *lemma* pnat.coprime_coe
- \+ *lemma* pnat.coprime_one
- \+ *theorem* pnat.dvd_gcd
- \+ *theorem* pnat.dvd_lcm_left
- \+ *theorem* pnat.dvd_lcm_right
- \+ *lemma* pnat.dvd_prime
- \+ *lemma* pnat.eq_one_of_lt_two
- \+ *lemma* pnat.exists_prime_and_dvd
- \+ *def* pnat.gcd
- \+ *theorem* pnat.gcd_coe
- \+ *lemma* pnat.gcd_comm
- \+ *theorem* pnat.gcd_dvd_left
- \+ *theorem* pnat.gcd_dvd_right
- \+ *lemma* pnat.gcd_eq_left
- \+ *lemma* pnat.gcd_eq_left_iff_dvd
- \+ *lemma* pnat.gcd_eq_right_iff_dvd
- \+ *theorem* pnat.gcd_mul_lcm
- \+ *lemma* pnat.gcd_one
- \+ *def* pnat.lcm
- \+ *theorem* pnat.lcm_coe
- \+ *theorem* pnat.lcm_dvd
- \+ *lemma* pnat.not_prime_one
- \+ *lemma* pnat.one_coprime
- \+ *lemma* pnat.one_gcd
- \+ *lemma* pnat.prime.ne_one
- \+ *lemma* pnat.prime.not_dvd_one
- \+ *lemma* pnat.prime.one_lt
- \+ *def* pnat.prime
- \+ *lemma* pnat.prime_two

Modified src/data/pnat/xgcd.lean


Modified src/data/rat/basic.lean


Modified src/tactic/norm_num.lean




## [2020-10-31 08:43:55](https://github.com/leanprover-community/mathlib/commit/3b2c97f)
feat(data/dfinsupp): Port `finsupp.lsum` and lemmas about `lift_add_hom` ([#4833](https://github.com/leanprover-community/mathlib/pull/4833))
This then removes the proofs of any `direct_sum` lemmas which become equivalent to the `lift_add_hom` lemmas
#### Estimated changes
Modified src/algebra/direct_sum.lean


Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.comp_lift_add_hom
- \+ *lemma* dfinsupp.lhom_ext'
- \+ *lemma* dfinsupp.lhom_ext
- \+ *lemma* dfinsupp.lift_add_hom_apply_single
- \+ *lemma* dfinsupp.lift_add_hom_comp_single
- \+ *lemma* dfinsupp.lift_add_hom_single_add_hom
- \+ *def* dfinsupp.lsum
- \+ *lemma* dfinsupp.sum_add_hom_comp_single

Modified src/linear_algebra/direct_sum_module.lean




## [2020-10-31 08:43:53](https://github.com/leanprover-community/mathlib/commit/17697a6)
feat(data/dfinsupp): Add dfinsupp.single_eq_single_iff, and subtype.heq_iff_coe_eq ([#4810](https://github.com/leanprover-community/mathlib/pull/4810))
This ought to make working with dfinsupps over subtypes easier
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.single_eq_single_iff

Modified src/data/subtype.lean
- \+ *lemma* subtype.heq_iff_coe_eq



## [2020-10-31 06:18:28](https://github.com/leanprover-community/mathlib/commit/67c2b5a)
feat(analysis/normed_space/add_torsor): distance to midpoint ([#4849](https://github.com/leanprover-community/mathlib/pull/4849))
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* dist_center_homothety
- \+ *lemma* dist_homothety_center
- \+ *lemma* dist_homothety_self
- \+ *lemma* dist_left_midpoint
- \+ *lemma* dist_midpoint_left
- \+ *lemma* dist_midpoint_right
- \+ *lemma* dist_right_midpoint
- \+ *lemma* dist_self_homothety
- \+ *lemma* dist_vadd_left
- \+ *lemma* dist_vadd_right



## [2020-10-31 06:18:25](https://github.com/leanprover-community/mathlib/commit/1521da6)
feat(order/conditionally_complete_lattice): nested intervals lemma ([#4848](https://github.com/leanprover-community/mathlib/pull/4848))
* Add a few versions of the nested intervals lemma.
* Add `pi`-instance for `conditionally_complete_lattice`.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* csupr_mem_Inter_Icc_of_mono_decr_Icc
- \+ *lemma* csupr_mem_Inter_Icc_of_mono_decr_Icc_nat
- \+ *lemma* csupr_mem_Inter_Icc_of_mono_incr_of_mono_decr

Modified src/order/lattice.lean
- \+ *theorem* forall_le_of_monotone_of_mono_decr



## [2020-10-31 06:18:24](https://github.com/leanprover-community/mathlib/commit/f5fd218)
feat(algebra/module/ordered): add pi instance ([#4847](https://github.com/leanprover-community/mathlib/pull/4847))
#### Estimated changes
Modified src/algebra/module/ordered.lean




## [2020-10-31 06:18:21](https://github.com/leanprover-community/mathlib/commit/6fc3517)
feat(category_theory/sites): generate lemmas ([#4840](https://github.com/leanprover-community/mathlib/pull/4840))
A couple of simple lemmas about the sieve generated by certain presieves.
#### Estimated changes
Modified src/category_theory/sites/pretopology.lean


Modified src/category_theory/sites/sieves.lean
- \+ *lemma* category_theory.sieve.generate_of_contains_split_epi
- \+ *lemma* category_theory.sieve.generate_of_singleton_split_epi
- \+ *lemma* category_theory.sieve.generate_top
- \+ *lemma* category_theory.sieve.le_generate



## [2020-10-31 06:18:19](https://github.com/leanprover-community/mathlib/commit/517f0b5)
feat(ring_theory/polynomial/basic): prerequisites for galois_definition ([#4829](https://github.com/leanprover-community/mathlib/pull/4829))
#### Estimated changes
Modified src/data/polynomial/degree/basic.lean
- \+ *lemma* polynomial.as_sum_range'

Modified src/ring_theory/polynomial/basic.lean
- \+ *def* polynomial.degree_lt_equiv



## [2020-10-31 06:18:16](https://github.com/leanprover-community/mathlib/commit/0f39d7a)
feat(data/prod): comp_map ([#4826](https://github.com/leanprover-community/mathlib/pull/4826))
#### Estimated changes
Modified src/data/prod.lean
- \+ *lemma* prod.map_comp_map
- \+ *lemma* prod.map_map



## [2020-10-31 04:53:40](https://github.com/leanprover-community/mathlib/commit/2283cf0)
chore(order/filter/bases): golf a proof ([#4834](https://github.com/leanprover-community/mathlib/pull/4834))
* rename `filter.has_basis.forall_nonempty_iff_ne_bot` to
  `filter.has_basis.ne_bot_iff`, swap LHS with RHS;
* add `filter.has_basis.eq_bot_iff`;
* golf the proof of `filter.has_basis.ne_bot` using `filter.has_basis.forall_iff`.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.eq_bot_iff
- \- *lemma* filter.has_basis.forall_nonempty_iff_ne_bot
- \+ *lemma* filter.has_basis.ne_bot_iff



## [2020-10-31 02:07:09](https://github.com/leanprover-community/mathlib/commit/94fa905)
feat(analysis/calculus/times_cont_diff): differentiability of field inverse ([#4795](https://github.com/leanprover-community/mathlib/pull/4795))
#### Estimated changes
Modified src/algebra/field.lean
- \+ *lemma* inverse_eq_has_inv

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff.div
- \+ *lemma* times_cont_diff.pow
- \+/\- *lemma* times_cont_diff_at.comp
- \+ *lemma* times_cont_diff_at.comp_times_cont_diff_within_at
- \+ *lemma* times_cont_diff_at.congr_of_eventually_eq
- \+ *lemma* times_cont_diff_at.div
- \+ *lemma* times_cont_diff_at.inv
- \+ *lemma* times_cont_diff_at_id
- \+ *lemma* times_cont_diff_at_inv
- \+ *lemma* times_cont_diff_on_id
- \+ *lemma* times_cont_diff_within_at.congr_nhds
- \- *lemma* times_cont_diff_within_at.continuous_within_at'
- \+ *lemma* times_cont_diff_within_at.div
- \+ *lemma* times_cont_diff_within_at.inv
- \+ *lemma* times_cont_diff_within_at.mono_of_mem
- \+ *lemma* times_cont_diff_within_at_congr_nhds
- \+ *lemma* times_cont_diff_within_at_id

Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.one_def

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_within_at.mono_of_mem
- \+ *lemma* continuous_within_at_insert_self
- \+/\- *lemma* continuous_within_at_singleton
- \+ *lemma* continuous_within_at_union
- \+ *lemma* insert_mem_nhds_within_insert
- \+/\- *lemma* mem_nhds_within_insert
- \+ *theorem* nhds_within_insert
- \+ *theorem* nhds_within_singleton



## [2020-10-31 00:58:01](https://github.com/leanprover-community/mathlib/commit/d5650a7)
chore(scripts): update nolints.txt ([#4844](https://github.com/leanprover-community/mathlib/pull/4844))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


Modified scripts/nolints.txt




## [2020-10-30 18:58:08](https://github.com/leanprover-community/mathlib/commit/cc7f06b)
feat(data/polynomial/lifts): polynomials that lift ([#4796](https://github.com/leanprover-community/mathlib/pull/4796))
Given semirings `R` and `S` with a morphism `f : R →+* S`, a polynomial with coefficients in `S` lifts if there exist `q : polynomial R` such that `map f p = q`. I proved some basic results about polynomials that lifts, for example concerning the sum etc.
Almost all the proof are trivial (and essentially identical), fell free to comment just the first ones, I will do the changes in all the relevant lemmas.
The proofs of `lifts_iff_lifts_deg` (a polynomial that lifts can be lifted to a polynomial of the same degree) and of `lifts_iff_lifts_deg_monic` (the same for monic polynomials) are quite painful, but this are the shortest proofs I found... I think that at least these two results deserve to be in mathlib (I'm using them to prove that the cyclotomic polynomial lift to `\Z`).
#### Estimated changes
Added src/data/polynomial/lifts.lean
- \+ *lemma* polynomial.C'_mem_lifts
- \+ *lemma* polynomial.C_mem_lifts
- \+ *lemma* polynomial.X_mem_lifts
- \+ *lemma* polynomial.X_pow_mem_lifts
- \+ *lemma* polynomial.base_mul_mem_lifts
- \+ *lemma* polynomial.erase_mem_lifts
- \+ *def* polynomial.lifts
- \+ *lemma* polynomial.lifts_and_degree_eq_and_monic
- \+ *lemma* polynomial.lifts_iff_coeff_lifts
- \+ *lemma* polynomial.lifts_iff_lifts_ring
- \+ *lemma* polynomial.lifts_iff_set_range
- \+ *def* polynomial.lifts_ring
- \+ *def* polynomial.map_alg
- \+ *lemma* polynomial.map_alg_eq_map
- \+ *lemma* polynomial.mem_lifts
- \+ *lemma* polynomial.mem_lifts_and_degree_eq
- \+ *lemma* polynomial.mem_lifts_iff_mem_alg
- \+ *lemma* polynomial.monomial_mem_lifts
- \+ *lemma* polynomial.monomial_mem_lifts_and_degree_eq
- \+ *lemma* polynomial.smul_mem_lifts



## [2020-10-30 14:20:39](https://github.com/leanprover-community/mathlib/commit/bfadf05)
feat(algebra, logic): Pi instances for nontrivial and monoid_with_zero ([#4766](https://github.com/leanprover-community/mathlib/pull/4766))
#### Estimated changes
Modified src/algebra/group/pi.lean
- \- *def* pi.single
- \- *lemma* pi.single_eq_of_ne
- \- *lemma* pi.single_eq_same

Modified src/algebra/ring/pi.lean


Added src/data/pi.lean
- \+ *def* pi.single
- \+ *lemma* pi.single_eq_of_ne
- \+ *lemma* pi.single_eq_same
- \+ *lemma* pi.single_injective

Modified src/logic/function/basic.lean
- \+ *lemma* function.update_injective

Modified src/logic/nontrivial.lean
- \+ *lemma* pi.nontrivial_at



## [2020-10-30 11:09:12](https://github.com/leanprover-community/mathlib/commit/58f8817)
feat(number_theory/fermat4): The n=4 case of fermat ([#4720](https://github.com/leanprover-community/mathlib/pull/4720))
Fermat's last theorem for n=4.
#### Estimated changes
Modified src/algebra/gcd_monoid.lean
- \+/\- *theorem* exists_associated_pow_of_mul_eq_pow

Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* int.abs_le_self_pow_two
- \+ *lemma* int.le_self_pow_two

Modified src/algebra/group_with_zero_power.lean
- \+ *lemma* ne_zero_pow
- \+/\- *theorem* pow_eq_zero'
- \+/\- *theorem* pow_ne_zero'
- \+/\- *lemma* zero_pow'
- \+/\- *lemma* zero_pow_eq_zero

Modified src/data/int/basic.lean
- \+ *lemma* int.neg_mod_two

Added src/number_theory/fermat4.lean
- \+ *lemma* fermat_42.comm
- \+ *lemma* fermat_42.coprime_of_minimal
- \+ *lemma* fermat_42.exists_minimal
- \+ *lemma* fermat_42.exists_odd_minimal
- \+ *lemma* fermat_42.exists_pos_odd_minimal
- \+ *def* fermat_42.minimal
- \+ *lemma* fermat_42.minimal_comm
- \+ *lemma* fermat_42.mul
- \+ *lemma* fermat_42.ne_zero
- \+ *lemma* fermat_42.neg_of_minimal
- \+ *lemma* fermat_42.not_minimal
- \+ *def* fermat_42
- \+ *lemma* int.coprime_of_sqr_sum'
- \+ *lemma* int.coprime_of_sqr_sum
- \+ *lemma* not_fermat_42
- \+ *theorem* not_fermat_4

Modified src/number_theory/pythagorean_triples.lean
- \+ *theorem* pythagorean_triple.coprime_classification'

Modified src/ring_theory/int/basic.lean
- \+ *lemma* int.exists_unit_of_abs
- \+ *lemma* int.gcd_eq_one_iff_coprime
- \+ *lemma* int.prime.dvd_pow'
- \+ *lemma* int.prime.dvd_pow
- \+ *lemma* int.sqr_of_coprime
- \+ *lemma* int.sqr_of_gcd_eq_one



## [2020-10-30 11:09:05](https://github.com/leanprover-community/mathlib/commit/d28e3d1)
feat(ring_theory/witt_vector/is_poly): supporting ghost calculations ([#4691](https://github.com/leanprover-community/mathlib/pull/4691))
Most operations on Witt vectors can be described/defined
by evaluating integral polynomials on the coefficients of Witt vectors.
One can prove identities between combinations of such operations
by applying the non-injective ghost map,
and continuing to prove the resulting identity of ghost components.
Such a calculation is called a ghost calculation.
This file provides the theoretical justification for why
applying the non-injective ghost map is a legal move,
and it provides tactics that aid in applying this step
to the point that it is almost transparent.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Added src/ring_theory/witt_vector/is_poly.lean
- \+ *lemma* witt_vector.add_is_poly₂
- \+ *lemma* witt_vector.bind₁_one_poly_witt_polynomial
- \+ *lemma* witt_vector.bind₁_zero_witt_polynomial
- \+ *lemma* witt_vector.is_poly.comp
- \+ *lemma* witt_vector.is_poly.comp₂
- \+ *lemma* witt_vector.is_poly.ext
- \+ *lemma* witt_vector.is_poly.map
- \+ *def* witt_vector.is_poly
- \+ *lemma* witt_vector.is_poly₂.comp
- \+ *lemma* witt_vector.is_poly₂.comp_left
- \+ *lemma* witt_vector.is_poly₂.comp_right
- \+ *lemma* witt_vector.is_poly₂.diag
- \+ *lemma* witt_vector.is_poly₂.ext
- \+ *lemma* witt_vector.is_poly₂.map
- \+ *def* witt_vector.is_poly₂
- \+ *lemma* witt_vector.mul_is_poly₂
- \+ *lemma* witt_vector.neg_is_poly
- \+ *def* witt_vector.one_poly
- \+ *lemma* witt_vector.poly_eq_of_witt_polynomial_bind_eq'
- \+ *lemma* witt_vector.poly_eq_of_witt_polynomial_bind_eq



## [2020-10-30 08:20:23](https://github.com/leanprover-community/mathlib/commit/3aac028)
feat(field_theory/intermediate_field): equalities from inclusions and dimension bounds ([#4828](https://github.com/leanprover-community/mathlib/pull/4828))
#### Estimated changes
Modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field.eq_of_le_of_findim_eq'
- \+ *lemma* intermediate_field.eq_of_le_of_findim_eq
- \+ *lemma* intermediate_field.eq_of_le_of_findim_le'
- \+ *lemma* intermediate_field.eq_of_le_of_findim_le

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.eq_of_le_of_findim_le



## [2020-10-30 08:20:21](https://github.com/leanprover-community/mathlib/commit/6ec7aec)
feat(data/polynomial): ext lemmas for homomorphisms from `polynomial R` ([#4823](https://github.com/leanprover-community/mathlib/pull/4823))
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \+ *lemma* polynomial.alg_hom_ext

Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.add_hom_ext'
- \+ *lemma* polynomial.add_hom_ext
- \+ *lemma* polynomial.lhom_ext'

Modified src/data/polynomial/monomial.lean
- \+ *lemma* polynomial.ring_hom_ext'
- \+ *lemma* polynomial.ring_hom_ext



## [2020-10-30 08:20:19](https://github.com/leanprover-community/mathlib/commit/03a477c)
feat(data/dfinsupp): Port over the `finsupp.lift_add_hom` API ([#4821](https://github.com/leanprover-community/mathlib/pull/4821))
These lemmas are mostly copied with minimal translation from `finsupp`.
A few proofs are taken from `direct_sum`.
The API of `direct_sum` is deliberately unchanged in this PR.
#### Estimated changes
Modified src/algebra/direct_sum.lean


Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.add_closure_Union_range_single
- \+ *lemma* dfinsupp.add_hom_ext'
- \+ *lemma* dfinsupp.add_hom_ext
- \+ *def* dfinsupp.lift_add_hom
- \+ *def* dfinsupp.single_add_hom
- \+ *def* dfinsupp.sum_add_hom
- \+ *lemma* dfinsupp.sum_add_hom_apply
- \+ *lemma* dfinsupp.sum_add_hom_single



## [2020-10-30 08:20:18](https://github.com/leanprover-community/mathlib/commit/5ae192e)
feat(data/equiv, algebra/*): Add simps projections to many equivs and homs ([#4818](https://github.com/leanprover-community/mathlib/pull/4818))
This doesn't actually change any existing lemmas to use these projections.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* alg_equiv.simps.inv_fun

Modified src/algebra/group/hom.lean


Modified src/algebra/module/linear_map.lean
- \+ *def* linear_equiv.simps.inv_fun

Modified src/algebra/ring/basic.lean


Modified src/data/equiv/mul_add.lean
- \+ *def* mul_equiv.simps.inv_fun

Modified src/data/equiv/ring.lean
- \+ *def* ring_equiv.simps.inv_fun



## [2020-10-30 08:20:16](https://github.com/leanprover-community/mathlib/commit/d46d0c2)
chore(topology/basic): the set of cluster pts of a filter is a closed set ([#4815](https://github.com/leanprover-community/mathlib/pull/4815))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* interior_eq_nhds'
- \+ *lemma* interior_set_of_eq
- \+ *lemma* is_closed_set_of_cluster_pt
- \+ *lemma* is_open_set_of_eventually_nhds

Modified src/topology/subset_properties.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2020-10-30 08:20:14](https://github.com/leanprover-community/mathlib/commit/072cfc5)
chore(data/dfinsupp): Provide dfinsupp with a semimodule instance ([#4801](https://github.com/leanprover-community/mathlib/pull/4801))
finsupp already has one, it seems pointless to hide the one for dfinsupp behind a def.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \- *def* dfinsupp.to_has_scalar
- \- *def* dfinsupp.to_semimodule

Modified src/linear_algebra/direct_sum_module.lean




## [2020-10-30 08:20:09](https://github.com/leanprover-community/mathlib/commit/63c0dac)
refactor(module/ordered): make ordered_semimodule a mixin ([#4719](https://github.com/leanprover-community/mathlib/pull/4719))
Per @urkud's suggestion at [#4683](https://github.com/leanprover-community/mathlib/pull/4683). This should avoid having to introduce a separate `ordered_algebra` class.
#### Estimated changes
Modified src/algebra/module/ordered.lean
- \+ *lemma* ordered_semimodule.mk''
- \- *def* ordered_semimodule.mk''
- \+ *lemma* ordered_semimodule.mk'
- \- *def* ordered_semimodule.mk'

Modified src/analysis/convex/basic.lean
- \+/\- *lemma* concave_on.concave_le
- \+/\- *lemma* concave_on.convex_hypograph
- \+/\- *lemma* concave_on.convex_lt
- \+/\- *lemma* concave_on.smul
- \+/\- *lemma* concave_on_iff_convex_hypograph
- \+/\- *lemma* convex_on.convex_epigraph
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* convex_on.convex_lt
- \+/\- *lemma* convex_on.smul
- \+/\- *lemma* convex_on_iff_convex_epigraph
- \+/\- *lemma* neg_concave_on_iff
- \+/\- *lemma* neg_convex_on_iff

Modified src/analysis/convex/cone.lean
- \+ *lemma* convex_cone.to_ordered_semimodule
- \- *def* convex_cone.to_ordered_semimodule

Modified src/analysis/convex/extrema.lean


Modified src/linear_algebra/affine_space/ordered.lean




## [2020-10-30 05:28:30](https://github.com/leanprover-community/mathlib/commit/4003b3e)
feat(*): a, switch to lean 3.23 ([#4802](https://github.com/leanprover-community/mathlib/pull/4802))
There are three changes affecting mathlib:
1. `ℕ → ℕ` is now elaborated as `∀ ᾰ : ℕ, ℕ`.  This means that `intro` introduces assumptions with names like `ᾰ_1`, etc.  These names should not be used, and instead provided explicitly to `intro` (and other tactics).
2. The heuristic to determine the definition name for `instance : foo bar` has been changed.
3. `by_contra` now uses classical logic, and defaults to the hypothesis name `h`.
4. adds a few new simp-lemmas in `data/typevec`
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified leanpkg.toml


Modified scripts/lint-copy-mod-doc.py


Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/free_algebra.lean


Modified src/algebra/group/ulift.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/category_theory/is_connected.lean


Modified src/category_theory/limits/cofinal.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/reflects_isomorphisms.lean


Modified src/combinatorics/simple_graph.lean


Modified src/computability/tm_to_partrec.lean


Modified src/control/functor/multivariate.lean


Modified src/control/lawful_fix.lean


Modified src/data/dfinsupp.lean


Modified src/data/finsupp/lattice.lean


Modified src/data/int/basic.lean


Modified src/data/list/basic.lean


Modified src/data/list/sigma.lean


Modified src/data/matrix/basic.lean


Modified src/data/mv_polynomial/monad.lean


Modified src/data/nat/factorial.lean


Modified src/data/nat/prime.lean


Modified src/data/nat/sqrt.lean


Modified src/data/num/lemmas.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/pfunctor/univariate/M.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/degree/basic.lean


Modified src/data/real/basic.lean
- \+/\- *def* real.comm_ring_aux

Modified src/data/real/cau_seq_completion.lean


Modified src/data/sym2.lean


Modified src/data/typevec.lean
- \+ *lemma* typevec.prod_fst_mk
- \+ *lemma* typevec.prod_snd_mk
- \+ *lemma* typevec.subtype_val_to_subtype'
- \+ *lemma* typevec.subtype_val_to_subtype
- \+ *lemma* typevec.to_subtype'_of_subtype'

Modified src/geometry/manifold/algebra/smooth_functions.lean


Modified src/group_theory/abelianization.lean


Modified src/group_theory/group_action.lean


Modified src/group_theory/presented_group.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/sylow.lean


Modified src/logic/basic.lean


Modified src/number_theory/lucas_lehmer.lean


Modified src/order/omega_complete_partial_order.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean


Modified src/testing/slim_check/sampleable.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/category/Compactum.lean


Modified src/topology/category/UniformSpace.lean


Modified src/topology/omega_complete_partial_order.lean


Modified test/finish3.lean


Modified test/norm_cast.lean


Modified test/pretty_cases.lean


Modified test/qpf.lean




## [2020-10-30 02:02:16](https://github.com/leanprover-community/mathlib/commit/581b2af)
feat(analysis/asymptotics): Equivalent definitions for `is_[oO] u v l` looking like `u = φ * v` for some `φ` ([#4646](https://github.com/leanprover-community/mathlib/pull/4646))
The advantage of these statements over `u/v` tendsto 0 / is bounded is they do not require any nonvanishing assumptions about `v`
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *lemma* asymptotics.is_O.eventually_mul_div_cancel
- \+ *lemma* asymptotics.is_O_iff_exists_eq_mul
- \+ *lemma* asymptotics.is_O_with.eventually_mul_div_cancel
- \+ *lemma* asymptotics.is_O_with.exists_eq_mul
- \+ *lemma* asymptotics.is_O_with_iff_exists_eq_mul
- \+ *lemma* asymptotics.is_O_with_of_eq_mul
- \+ *lemma* asymptotics.is_o.eventually_mul_div_cancel
- \+ *lemma* asymptotics.is_o_iff_exists_eq_mul



## [2020-10-30 01:08:49](https://github.com/leanprover-community/mathlib/commit/f510728)
chore(scripts): update nolints.txt ([#4825](https://github.com/leanprover-community/mathlib/pull/4825))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-29 22:37:58](https://github.com/leanprover-community/mathlib/commit/fc307f9)
feat(tactic/norm_num): make norm_num extensible ([#4820](https://github.com/leanprover-community/mathlib/pull/4820))
This allows you to extend `norm_num` by defining additional tactics of type `expr → tactic (expr × expr)` with the `@[norm_num]` attribute. It still requires some tactic proficiency to use correctly, but it at least allows us to move all the possible norm_num extensions to their own files instead of the current dependency cycle problem.
This could potentially become a performance problem if too many things are marked `@[norm_num]`, as they are simply looked through in linear order. It could be improved by having extensions register a finite set of constants that they wish to evaluate, and dispatch to the right extension tactic using a `name_map`.
```lean
def foo : ℕ := 1
@[norm_num] meta def eval_foo : expr → tactic (expr × expr)
| `(foo) := pure (`(1:ℕ), `(eq.refl 1))
| _ := tactic.failed
example : foo = 1 := by norm_num
```
#### Estimated changes
Modified src/tactic/abel.lean


Modified src/tactic/norm_num.lean


Modified src/tactic/ring_exp.lean


Modified test/norm_num.lean
- \+ *def* foo



## [2020-10-29 19:28:13](https://github.com/leanprover-community/mathlib/commit/2c7efdf)
feat(category_theory/sites): Grothendieck topology on a space ([#4819](https://github.com/leanprover-community/mathlib/pull/4819))
The grothendieck topology associated to a topological space.
I also changed a definition I meant to change in [#4816](https://github.com/leanprover-community/mathlib/pull/4816), and updated the TODOs of some docstrings; I can split these into separate PRs if needed but I think all the changes are quite minor
#### Estimated changes
Modified src/category_theory/sites/grothendieck.lean


Modified src/category_theory/sites/pretopology.lean


Modified src/category_theory/sites/sieves.lean
- \- *lemma* category_theory.presieve.singleton_arrow_self
- \+ *lemma* category_theory.presieve.singleton_self

Added src/category_theory/sites/spaces.lean
- \+ *def* opens.grothendieck_topology
- \+ *def* opens.pretopology
- \+ *lemma* opens.pretopology_to_grothendieck



## [2020-10-29 19:28:10](https://github.com/leanprover-community/mathlib/commit/92af9fa)
feat(category_theory/limits/pullbacks): pullback self is id iff mono ([#4813](https://github.com/leanprover-community/mathlib/pull/4813))
#### Estimated changes
Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.pullback_cone.is_limit_mk_id_id
- \+ *lemma* category_theory.limits.pullback_cone.mono_of_is_limit_mk_id_id



## [2020-10-29 19:28:07](https://github.com/leanprover-community/mathlib/commit/78811e0)
feat(ring_theory/unique_factorization_domain): `unique_factorization_monoid` structure on polynomials over ufd ([#4774](https://github.com/leanprover-community/mathlib/pull/4774))
Provides the `unique_factorization_monoid` structure on polynomials over a UFD
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/ring_theory/polynomial/basic.lean
- \+/\- *theorem* polynomial.exists_irreducible_of_degree_pos
- \+/\- *theorem* polynomial.exists_irreducible_of_nat_degree_ne_zero
- \+/\- *theorem* polynomial.exists_irreducible_of_nat_degree_pos

Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2020-10-29 19:28:03](https://github.com/leanprover-community/mathlib/commit/856381c)
chore(data/equiv/basic): arrow_congr preserves properties of binary operators ([#4759](https://github.com/leanprover-community/mathlib/pull/4759))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.semiconj_conj
- \+ *lemma* equiv.semiconj₂_conj

Modified src/logic/function/conjugate.lean
- \+ *lemma* function.semiconj₂.is_associative_left
- \+ *lemma* function.semiconj₂.is_associative_right
- \+ *lemma* function.semiconj₂.is_idempotent_left
- \+ *lemma* function.semiconj₂.is_idempotent_right



## [2020-10-29 19:28:00](https://github.com/leanprover-community/mathlib/commit/ccc98d0)
refactor(*): `midpoint`, `point_reflection`, and Mazur-Ulam in affine spaces ([#4752](https://github.com/leanprover-community/mathlib/pull/4752))
* redefine `midpoint` for points in an affine space;
* redefine `point_reflection` for affine spaces (as `equiv`,
  `affine_equiv`, and `isometric`);
* define `const_vsub` as `equiv`, `affine_equiv`, and `isometric`;
* define `affine_map.of_map_midpoint`;
* fully migrate the proof of Mazur-Ulam theorem to affine spaces;
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* equiv.coe_const_vsub
- \+ *lemma* equiv.coe_const_vsub_symm
- \+ *def* equiv.const_vsub
- \+ *lemma* equiv.injective_point_reflection_left_of_injective_bit0
- \+ *def* equiv.point_reflection
- \+ *lemma* equiv.point_reflection_apply
- \+ *lemma* equiv.point_reflection_fixed_iff_of_injective_bit0
- \+ *lemma* equiv.point_reflection_involutive
- \+ *lemma* equiv.point_reflection_self
- \+ *lemma* equiv.point_reflection_symm

Modified src/algebra/invertible.lean
- \+ *lemma* one_sub_inv_of_two

Deleted src/algebra/midpoint.lean
- \- *lemma* add_monoid_hom.coe_of_map_midpoint
- \- *def* add_monoid_hom.of_map_midpoint
- \- *lemma* equiv.point_reflection_midpoint_left
- \- *lemma* equiv.point_reflection_midpoint_right
- \- *def* midpoint
- \- *lemma* midpoint_add_add
- \- *lemma* midpoint_add_left
- \- *lemma* midpoint_add_right
- \- *lemma* midpoint_add_self
- \- *lemma* midpoint_comm
- \- *lemma* midpoint_def
- \- *lemma* midpoint_eq_iff
- \- *lemma* midpoint_neg_neg
- \- *lemma* midpoint_self
- \- *lemma* midpoint_smul_smul
- \- *lemma* midpoint_sub_left
- \- *lemma* midpoint_sub_right
- \- *lemma* midpoint_sub_sub
- \- *lemma* midpoint_unique
- \- *lemma* midpoint_zero_add

Modified src/algebra/module/basic.lean
- \+ *theorem* two_smul'

Modified src/analysis/normed_space/add_torsor.lean
- \+ *def* affine_map.of_map_midpoint
- \+ *lemma* isometric.coe_const_vsub
- \+ *lemma* isometric.coe_const_vsub_symm
- \+ *def* isometric.const_vsub
- \+ *lemma* isometric.dist_point_reflection_fixed
- \+ *lemma* isometric.dist_point_reflection_self'
- \+ *lemma* isometric.dist_point_reflection_self
- \+ *lemma* isometric.dist_point_reflection_self_real
- \+ *def* isometric.point_reflection
- \+ *lemma* isometric.point_reflection_apply
- \+ *lemma* isometric.point_reflection_fixed_iff
- \+ *lemma* isometric.point_reflection_involutive
- \+ *lemma* isometric.point_reflection_midpoint_left
- \+ *lemma* isometric.point_reflection_midpoint_right
- \+ *lemma* isometric.point_reflection_self
- \+ *lemma* isometric.point_reflection_symm
- \+ *lemma* isometric.point_reflection_to_equiv

Modified src/analysis/normed_space/mazur_ulam.lean
- \+ *lemma* isometric.coe_to_affine_equiv
- \- *lemma* isometric.coe_to_affine_map
- \+/\- *lemma* isometric.map_midpoint
- \+/\- *lemma* isometric.midpoint_fixed
- \+ *def* isometric.to_affine_equiv
- \- *def* isometric.to_affine_map

Deleted src/analysis/normed_space/point_reflection.lean
- \- *lemma* equiv.point_reflection_fixed_iff_of_module
- \- *def* isometric.point_reflection
- \- *lemma* isometric.point_reflection_apply
- \- *lemma* isometric.point_reflection_dist_fixed
- \- *lemma* isometric.point_reflection_dist_self'
- \- *lemma* isometric.point_reflection_dist_self
- \- *lemma* isometric.point_reflection_dist_self_real
- \- *lemma* isometric.point_reflection_fixed_iff
- \- *lemma* isometric.point_reflection_involutive
- \- *lemma* isometric.point_reflection_midpoint_left
- \- *lemma* isometric.point_reflection_midpoint_right
- \- *lemma* isometric.point_reflection_self
- \- *lemma* isometric.point_reflection_symm
- \- *lemma* isometric.point_reflection_to_equiv

Modified src/data/equiv/mul_add.lean
- \- *def* equiv.point_reflection
- \- *lemma* equiv.point_reflection_apply
- \- *lemma* equiv.point_reflection_fixed_iff_of_bit0_injective
- \- *lemma* equiv.point_reflection_involutive
- \- *lemma* equiv.point_reflection_self
- \- *lemma* equiv.point_reflection_symm

Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* affine_equiv.apply_line_map
- \+ *lemma* affine_equiv.coe_const_vsub
- \+ *lemma* affine_equiv.coe_const_vsub_symm
- \+ *def* affine_equiv.const_vsub
- \+ *lemma* affine_equiv.injective_point_reflection_left_of_injective_bit0
- \+ *lemma* affine_equiv.injective_point_reflection_left_of_module
- \+ *def* affine_equiv.point_reflection
- \+ *lemma* affine_equiv.point_reflection_apply
- \+ *lemma* affine_equiv.point_reflection_fixed_iff_of_injective_bit0
- \+ *lemma* affine_equiv.point_reflection_fixed_iff_of_module
- \+ *lemma* affine_equiv.point_reflection_involutive
- \+ *lemma* affine_equiv.point_reflection_self
- \+ *lemma* affine_equiv.point_reflection_symm
- \+ *lemma* affine_equiv.to_equiv_point_reflection
- \+ *lemma* affine_map.homothety_neg_one_apply
- \+ *lemma* affine_map.line_map_vadd
- \+ *lemma* affine_map.line_map_vsub
- \+ *lemma* affine_map.vadd_line_map
- \+ *lemma* affine_map.vsub_line_map

Modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.homothety_eq_line_map
- \+ *lemma* affine_map.left_vsub_line_map
- \+ *lemma* affine_map.line_map_vadd_line_map
- \+ *lemma* affine_map.line_map_vsub_left
- \+ *lemma* affine_map.line_map_vsub_line_map
- \+ *lemma* affine_map.line_map_vsub_right
- \+ *lemma* affine_map.right_vsub_line_map

Added src/linear_algebra/affine_space/midpoint.lean
- \+ *lemma* add_monoid_hom.coe_of_map_midpoint
- \+ *def* add_monoid_hom.of_map_midpoint
- \+ *lemma* affine_equiv.map_midpoint
- \+ *lemma* affine_equiv.point_reflection_midpoint_left
- \+ *lemma* affine_equiv.point_reflection_midpoint_right
- \+ *lemma* affine_map.map_midpoint
- \+ *lemma* homothety_inv_of_two
- \+ *lemma* homothety_inv_two
- \+ *lemma* homothety_one_half
- \+ *lemma* line_map_inv_two
- \+ *lemma* line_map_one_half
- \+ *def* midpoint
- \+ *lemma* midpoint_add_self
- \+ *lemma* midpoint_comm
- \+ *lemma* midpoint_eq_iff'
- \+ *lemma* midpoint_eq_iff
- \+ *lemma* midpoint_eq_midpoint_iff_vsub_eq_vsub
- \+ *lemma* midpoint_self
- \+ *lemma* midpoint_unique
- \+ *lemma* midpoint_vadd_midpoint
- \+ *lemma* midpoint_vsub_midpoint
- \+ *lemma* midpoint_zero_add



## [2020-10-29 19:27:56](https://github.com/leanprover-community/mathlib/commit/4d19191)
feat(algebra/monoid_algebra): Add an equivalence between `add_monoid_algebra` and `monoid_algebra` in terms of `multiplicative` ([#4402](https://github.com/leanprover-community/mathlib/pull/4402))
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.map_domain_mul
- \+ *lemma* monoid_algebra.map_domain_mul



## [2020-10-29 18:26:22](https://github.com/leanprover-community/mathlib/commit/d709ed6)
feat(algebra/direct_sum*): relax a lot of constraints to add_comm_monoid ([#3537](https://github.com/leanprover-community/mathlib/pull/3537))
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/algebra/direct_sum.lean
- \+ *lemma* direct_sum.sub_apply
- \+ *theorem* direct_sum.to_add_monoid.unique
- \+ *def* direct_sum.to_add_monoid
- \+ *lemma* direct_sum.to_add_monoid_of
- \- *theorem* direct_sum.to_group.unique
- \- *def* direct_sum.to_group
- \- *lemma* direct_sum.to_group_of
- \+/\- *def* direct_sum

Modified src/linear_algebra/direct_sum_module.lean
- \+/\- *lemma* direct_sum.smul_apply



## [2020-10-29 15:42:46](https://github.com/leanprover-community/mathlib/commit/f83468d)
feat(category_theory/functor_category): monos in the functor category ([#4811](https://github.com/leanprover-community/mathlib/pull/4811))
#### Estimated changes
Modified src/category_theory/functor_category.lean
- \+ *lemma* category_theory.nat_trans.epi_app_of_epi
- \+ *lemma* category_theory.nat_trans.mono_app_of_mono



## [2020-10-29 14:18:55](https://github.com/leanprover-community/mathlib/commit/7d7e850)
chore(category_theory/sites): nicer names ([#4816](https://github.com/leanprover-community/mathlib/pull/4816))
Changes the name `arrows_with_codomain` to `presieve` which is more suggestive and shorter, and changes `singleton_arrow` to `singleton`, since it's in the presieve namespace anyway.
#### Estimated changes
Modified src/category_theory/sites/pretopology.lean
- \+/\- *def* category_theory.pullback_arrows

Modified src/category_theory/sites/sieves.lean
- \- *def* category_theory.arrows_with_codomain.bind
- \- *lemma* category_theory.arrows_with_codomain.bind_comp
- \- *def* category_theory.arrows_with_codomain.singleton_arrow
- \- *lemma* category_theory.arrows_with_codomain.singleton_arrow_eq_iff_domain
- \- *lemma* category_theory.arrows_with_codomain.singleton_arrow_self
- \- *def* category_theory.arrows_with_codomain
- \+ *def* category_theory.presieve.bind
- \+ *lemma* category_theory.presieve.bind_comp
- \+ *def* category_theory.presieve.singleton
- \+ *lemma* category_theory.presieve.singleton_arrow_self
- \+ *lemma* category_theory.presieve.singleton_eq_iff_domain
- \+ *def* category_theory.presieve
- \+/\- *def* category_theory.sieve.bind
- \+/\- *def* category_theory.sieve.generate
- \+/\- *def* category_theory.sieve.gi_generate
- \+/\- *lemma* category_theory.sieve.le_pullback_bind
- \+/\- *lemma* category_theory.sieve.mem_generate
- \+/\- *lemma* category_theory.sieve.pushforward_le_bind_of_mem
- \+/\- *lemma* category_theory.sieve.sets_iff_generate



## [2020-10-29 13:24:15](https://github.com/leanprover-community/mathlib/commit/8b858d0)
feat(data/dfinsupp): Relax requirements of semimodule conversion to add_comm_monoid ([#3490](https://github.com/leanprover-community/mathlib/pull/3490))
The extra `_`s required to make this still build are unfortunate, but hopefully someone else can work out how to remove them in a later PR.
#### Estimated changes
Modified src/algebra/direct_limit.lean


Modified src/algebra/direct_sum.lean
- \+ *lemma* direct_sum.add_apply
- \+ *lemma* direct_sum.zero_apply

Modified src/algebra/lie/basic.lean
- \+/\- *lemma* lie_algebra.of_associative_algebra_hom_id

Modified src/data/dfinsupp.lean
- \+/\- *lemma* dfinsupp.ext
- \+/\- *lemma* dfinsupp.smul_apply
- \+/\- *lemma* dfinsupp.support_smul
- \+/\- *def* dfinsupp.to_has_scalar
- \+/\- *def* dfinsupp.to_semimodule

Modified src/linear_algebra/direct_sum_module.lean
- \+ *lemma* direct_sum.smul_apply
- \+ *lemma* direct_sum.support_smul



## [2020-10-29 09:49:53](https://github.com/leanprover-community/mathlib/commit/d510a63)
feat(linear_algebra/finite_dimensional): finite dimensional algebra_hom of fields is bijective ([#4793](https://github.com/leanprover-community/mathlib/pull/4793))
Changes to finite_dimensional.lean from [#4786](https://github.com/leanprover-community/mathlib/pull/4786)
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* alg_hom.bijective



## [2020-10-29 07:30:22](https://github.com/leanprover-community/mathlib/commit/1baf701)
feat(category_theory/Fintype): Adds the category of finite types and its "standard" skeleton. ([#4809](https://github.com/leanprover-community/mathlib/pull/4809))
This PR adds the category `Fintype` of finite types, as well as its "standard" skeleton whose objects are `fin n`.
#### Estimated changes
Added src/category_theory/Fintype.lean
- \+ *def* Fintype.incl
- \+ *def* Fintype.of
- \+ *def* Fintype.skeleton.incl
- \+ *lemma* Fintype.skeleton.incl_mk_nat_card
- \+ *lemma* Fintype.skeleton.is_skeletal
- \+ *def* Fintype.skeleton.mk
- \+ *def* Fintype.skeleton.to_nat
- \+ *def* Fintype.skeleton
- \+ *def* Fintype

Modified src/data/fintype/basic.lean
- \+ *lemma* fin.equiv_iff_eq



## [2020-10-29 01:05:47](https://github.com/leanprover-community/mathlib/commit/d9c8215)
chore(scripts): update nolints.txt ([#4814](https://github.com/leanprover-community/mathlib/pull/4814))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-28 20:49:21](https://github.com/leanprover-community/mathlib/commit/69d41da)
feat(tactic/dependencies): add tactics to compute (reverse) dependencies ([#4602](https://github.com/leanprover-community/mathlib/pull/4602))
These are the beginnings of an API about dependencies between expressions. For
now, we only deal with dependencies and reverse dependencies of hypotheses,
which are easy to compute.
Breaking change: `tactic.revert_deps` is renamed to
`tactic.revert_reverse_dependencies_of_hyp` for consistency. Its implementation
is completely new, but should be equivalent to the old one except for the order
in which hypotheses are reverted. (But the old implementation made no particular
guarantees about this order anyway.)
#### Estimated changes
Modified src/meta/expr.lean


Modified src/meta/rb_map.lean


Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Added src/tactic/dependencies.lean


Modified src/tactic/interactive.lean


Modified src/tactic/wlog.lean


Added test/dependencies.lean


Modified test/tactics.lean




## [2020-10-28 18:09:43](https://github.com/leanprover-community/mathlib/commit/d75da1a)
feat(topology/algebra/group_with_zero): introduce `has_continuous_inv'` ([#4804](https://github.com/leanprover-community/mathlib/pull/4804))
Move lemmas about continuity of division from `normed_field`, add a few new lemmas, and introduce a new typeclass. Also use it for `nnreal`s.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \- *lemma* continuous.div
- \- *lemma* continuous.inv'
- \- *lemma* continuous_at.div
- \- *lemma* continuous_at.inv'
- \- *lemma* continuous_on.div
- \- *lemma* continuous_on.inv'
- \- *lemma* continuous_within_at.div
- \- *lemma* continuous_within_at.inv'
- \- *lemma* filter.tendsto.div
- \- *lemma* filter.tendsto.div_const
- \- *lemma* filter.tendsto.inv'
- \- *lemma* normed_field.continuous_on_inv
- \- *lemma* normed_field.tendsto_inv

Modified src/measure_theory/borel_space.lean


Added src/topology/algebra/group_with_zero.lean
- \+ *lemma* continuous.div
- \+ *lemma* continuous.div_const
- \+ *lemma* continuous.inv'
- \+ *lemma* continuous_at.div
- \+ *lemma* continuous_at.div_const
- \+ *lemma* continuous_at.inv'
- \+ *lemma* continuous_on.div
- \+ *lemma* continuous_on.div_const
- \+ *lemma* continuous_on.inv'
- \+ *lemma* continuous_on_div
- \+ *lemma* continuous_on_inv'
- \+ *lemma* continuous_within_at.div
- \+ *lemma* continuous_within_at.div_const
- \+ *lemma* continuous_within_at.inv'
- \+ *lemma* filter.tendsto.div
- \+ *lemma* filter.tendsto.div_const
- \+ *lemma* filter.tendsto.inv'
- \+ *lemma* tendsto_inv'

Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \- *lemma* nnreal.tendsto.sub
- \+/\- *lemma* nnreal.tendsto_coe



## [2020-10-28 18:09:41](https://github.com/leanprover-community/mathlib/commit/80ffad0)
chore(data/dfinsupp): Make some lemma arguments explicit ([#4803](https://github.com/leanprover-community/mathlib/pull/4803))
This file is long and this is not exhaustive, but this hits most of the simpler ones
#### Estimated changes
Modified src/algebra/lie/basic.lean


Modified src/data/dfinsupp.lean
- \+/\- *lemma* dfinsupp.add_apply
- \+/\- *lemma* dfinsupp.filter_pos_add_filter_neg
- \+/\- *lemma* dfinsupp.neg_apply
- \+/\- *lemma* dfinsupp.sub_apply
- \+/\- *lemma* dfinsupp.zero_apply

Modified src/linear_algebra/direct_sum_module.lean




## [2020-10-28 18:09:39](https://github.com/leanprover-community/mathlib/commit/7a37dd4)
feat(algebra/monoid_algebra): Bundle lift_nc_mul and lift_nc_one into a ring_hom and alg_hom ([#4789](https://github.com/leanprover-community/mathlib/pull/4789))
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+ *def* add_monoid_algebra.lift_nc_alg_hom
- \+ *def* add_monoid_algebra.lift_nc_ring_hom
- \+ *def* monoid_algebra.lift_nc_alg_hom
- \+ *def* monoid_algebra.lift_nc_ring_hom



## [2020-10-28 18:09:37](https://github.com/leanprover-community/mathlib/commit/28cc74f)
feat(ring_theory/unique_factorization_domain): a `normalization_monoid` structure for ufms ([#4772](https://github.com/leanprover-community/mathlib/pull/4772))
Provides a default `normalization_monoid` structure on a `unique_factorization_monoid`
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* associates.associated_map_mk
- \+ *lemma* associates.mk_monoid_hom_apply

Modified src/algebra/gcd_monoid.lean
- \+ *def* normalization_monoid_of_monoid_hom_right_inverse

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_monoid.factors_mul
- \+ *lemma* unique_factorization_monoid.factors_one



## [2020-10-28 18:09:35](https://github.com/leanprover-community/mathlib/commit/25df267)
feat(category_theory/limits/presheaf): free cocompletion ([#4740](https://github.com/leanprover-community/mathlib/pull/4740))
Fill in the missing part of [#4401](https://github.com/leanprover-community/mathlib/pull/4401), showing that the yoneda extension is unique. Also adds some basic API around [#4401](https://github.com/leanprover-community/mathlib/pull/4401).
#### Estimated changes
Modified docs/references.bib


Modified src/category_theory/elements.lean
- \+ *def* category_theory.category_of_elements.map
- \+ *lemma* category_theory.category_of_elements.map_π

Modified src/category_theory/limits/preserves/basic.lean
- \+ *def* category_theory.limits.is_colimit_of_preserves
- \+ *def* category_theory.limits.is_limit_of_preserves

Modified src/category_theory/limits/presheaf.lean
- \+ *lemma* category_theory.cocone_of_representable_naturality
- \+ *lemma* category_theory.cocone_of_representable_ι_app
- \+ *def* category_theory.nat_iso_of_nat_iso_on_representables
- \+ *def* category_theory.unique_extension_along_yoneda



## [2020-10-28 18:09:33](https://github.com/leanprover-community/mathlib/commit/dfa85b5)
feat(archive/imo): formalize IMO 1981 problem Q3 ([#4599](https://github.com/leanprover-community/mathlib/pull/4599))
Determine the maximum value of `m ^ 2 + n ^ 2`, where `m` and `n` are integers in
`{1, 2, ..., 1981}` and `(n ^ 2 - m * n - m ^ 2) ^ 2 = 1`.
#### Estimated changes
Added archive/imo/imo1981_q3.lean
- \+ *theorem* imo1981_q3
- \+ *lemma* k_bound
- \+ *lemma* m_n_bounds
- \+ *lemma* nat_predicate.eq_imp_1
- \+ *lemma* nat_predicate.imp_fib
- \+ *lemma* nat_predicate.m_le_n
- \+ *lemma* nat_predicate.m_pos
- \+ *lemma* nat_predicate.n_le_N
- \+ *lemma* nat_predicate.n_pos
- \+ *lemma* nat_predicate.reduction
- \+ *def* nat_predicate
- \+ *lemma* problem_predicate.eq_imp_1
- \+ *lemma* problem_predicate.m_le_n
- \+ *lemma* problem_predicate.reduction
- \+ *structure* problem_predicate
- \+ *lemma* solution_bound
- \+ *theorem* solution_greatest
- \+ *def* specified_set

Modified src/algebra/ordered_ring.lean
- \+ *lemma* abs_eq_iff_mul_self_eq
- \+ *lemma* abs_le_iff_mul_self_le
- \+ *lemma* abs_lt_iff_mul_self_lt
- \+ *lemma* mul_self_inj
- \+ *lemma* zero_lt_three

Modified src/data/int/basic.lean
- \+ *lemma* int.nat_abs_eq_iff_mul_self_eq
- \+ *lemma* int.nat_abs_eq_iff_sq_eq
- \+ *lemma* int.nat_abs_le_iff_mul_self_le
- \+ *lemma* int.nat_abs_le_iff_sq_le
- \+ *lemma* int.nat_abs_lt_iff_mul_self_lt
- \+ *lemma* int.nat_abs_lt_iff_sq_lt

Modified src/data/nat/basic.lean
- \+ *theorem* nat.eq_one_of_mul_eq_one_left
- \+ *theorem* nat.eq_one_of_mul_eq_one_right
- \+/\- *lemma* nat.zero_max

Modified src/data/nat/fib.lean
- \+ *lemma* nat.fib_two



## [2020-10-28 15:21:10](https://github.com/leanprover-community/mathlib/commit/40da087)
feat(equiv/basic): use @[simps] ([#4652](https://github.com/leanprover-community/mathlib/pull/4652))
Use the `@[simps]` attribute to automatically generate equation lemmas for equivalences.
The names `foo_apply` and `foo_symm_apply` are used for the projection lemmas of `foo`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.Pi_congr_left'
- \- *lemma* equiv.Pi_congr_left'_apply
- \- *lemma* equiv.Pi_congr_left'_symm_apply
- \- *lemma* equiv.arrow_congr'_apply
- \+/\- *def* equiv.arrow_congr
- \- *lemma* equiv.arrow_congr_apply
- \- *theorem* equiv.coe_of_bijective
- \- *lemma* equiv.coe_plift
- \- *lemma* equiv.coe_plift_symm
- \- *lemma* equiv.coe_prod_comm
- \- *theorem* equiv.coe_prod_congr
- \- *lemma* equiv.coe_ulift
- \- *lemma* equiv.coe_ulift_symm
- \- *lemma* equiv.conj_apply
- \+/\- *def* equiv.fun_unique
- \- *lemma* equiv.fun_unique_apply
- \- *lemma* equiv.fun_unique_symm_apply
- \- *lemma* equiv.of_injective_apply
- \+/\- *def* equiv.prod_assoc
- \- *theorem* equiv.prod_assoc_apply
- \- *theorem* equiv.prod_assoc_sym_apply
- \+/\- *def* equiv.prod_comm
- \+/\- *def* equiv.prod_congr
- \+/\- *def* equiv.prod_punit
- \- *theorem* equiv.prod_punit_apply
- \+/\- *def* equiv.psigma_equiv_sigma
- \- *lemma* equiv.psigma_equiv_sigma_apply
- \- *lemma* equiv.psigma_equiv_sigma_symm_apply
- \- *theorem* equiv.punit_prod_apply
- \- *theorem* equiv.set.image_apply
- \- *lemma* equiv.set.of_eq_apply
- \- *lemma* equiv.set.of_eq_symm_apply
- \- *theorem* equiv.set.range_apply
- \- *lemma* equiv.set.univ_apply
- \- *lemma* equiv.set.univ_symm_apply
- \- *lemma* equiv.sigma_congr_left_apply
- \- *lemma* equiv.sigma_congr_right_apply
- \- *lemma* equiv.sigma_congr_right_symm_apply
- \+/\- *def* equiv.sigma_equiv_prod
- \- *lemma* equiv.sigma_equiv_prod_apply
- \- *lemma* equiv.sigma_equiv_prod_symm_apply
- \- *lemma* equiv.sigma_preimage_equiv_apply
- \- *lemma* equiv.sigma_preimage_equiv_symm_apply_fst
- \- *lemma* equiv.sigma_preimage_equiv_symm_apply_snd_fst
- \+ *def* equiv.simps.inv_fun
- \- *lemma* equiv.subtype_congr_right_mk
- \- *lemma* equiv.subtype_preimage_apply
- \- *lemma* equiv.subtype_preimage_symm_apply_coe
- \- *lemma* equiv.sum_comm_apply
- \- *theorem* equiv.sum_congr_apply

Modified src/data/subtype.lean
- \+/\- *def* subtype.coind
- \+/\- *def* subtype.map
- \+ *def* subtype.simps.val

Modified src/tactic/simps.lean


Modified test/simps.lean




## [2020-10-28 10:34:25](https://github.com/leanprover-community/mathlib/commit/e8f8de6)
feat(ring_theory/valuation): ring of integers ([#4729](https://github.com/leanprover-community/mathlib/pull/4729))
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \+ *lemma* pow_lt_pow'
- \+ *lemma* pow_lt_pow_succ
- \+ *lemma* zero_lt_one''

Modified src/ring_theory/valuation/basic.lean
- \+ *lemma* valuation.map_add_le
- \+ *lemma* valuation.map_add_lt
- \+ *lemma* valuation.map_sum_le
- \+ *lemma* valuation.map_sum_lt'
- \+ *lemma* valuation.map_sum_lt

Added src/ring_theory/valuation/integers.lean
- \+ *theorem* valuation.integer.integers
- \+ *def* valuation.integer
- \+ *lemma* valuation.integers.dvd_iff_le
- \+ *lemma* valuation.integers.dvd_of_le
- \+ *lemma* valuation.integers.is_unit_of_one
- \+ *lemma* valuation.integers.le_iff_dvd
- \+ *lemma* valuation.integers.le_of_dvd
- \+ *lemma* valuation.integers.one_of_is_unit
- \+ *structure* valuation.integers

Added src/ring_theory/valuation/integral.lean
- \+ *lemma* valuation.integers.mem_of_integral



## [2020-10-28 09:18:54](https://github.com/leanprover-community/mathlib/commit/216cbc4)
feat(analysis/special_functions/trigonometric): simp attributes for trig values ([#4806](https://github.com/leanprover-community/mathlib/pull/4806))
simp attributes for the trig values that didn't already have them
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* real.cos_pi_div_eight
- \+/\- *lemma* real.cos_pi_div_four
- \+/\- *lemma* real.cos_pi_div_six
- \+/\- *lemma* real.cos_pi_div_sixteen
- \+/\- *lemma* real.cos_pi_div_thirty_two
- \+/\- *lemma* real.cos_pi_div_three
- \+/\- *lemma* real.sin_pi_div_eight
- \+/\- *lemma* real.sin_pi_div_four
- \+/\- *lemma* real.sin_pi_div_six
- \+/\- *lemma* real.sin_pi_div_sixteen
- \+/\- *lemma* real.sin_pi_div_thirty_two
- \+/\- *lemma* real.sin_pi_div_three



## [2020-10-28 07:49:32](https://github.com/leanprover-community/mathlib/commit/6dfa952)
refactor(order/filter): make `filter.has_mem semireducible ([#4807](https://github.com/leanprover-community/mathlib/pull/4807))
This way `simp only []` does not simplify `s ∈ f` to `s ∈ f.sets`.
* Add protected simp lemmas `filter.mem_mk` and `filter.mem_sets`.
* Use implicit argument in `filter.mem_generate_iff`.
* Use `∃ t, s ∈ ...` instead of `s ∈ ⋃ t, ...` in
  `filter.mem_infi_finite` and `filter.mem_infi_finite'`.
* Use an implicit argument in `(non/ne_)empty_of_mem_ultrafilter`.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/data/analysis/topology.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.mem_generate_iff

Modified src/order/filter/lift.lean


Modified src/order/filter/partial.lean


Modified src/order/filter/pointwise.lean


Modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* filter.ne_empty_of_mem_ultrafilter
- \+/\- *lemma* filter.nonempty_of_mem_ultrafilter

Modified src/topology/category/Compactum.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/order.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2020-10-28 06:06:38](https://github.com/leanprover-community/mathlib/commit/7807f3d)
chore(linear_algebra/affine_space/basic): split ([#4767](https://github.com/leanprover-community/mathlib/pull/4767))
* Split `linear_algebra/affine_space/basic` into two files: `affine_map` and `affine_subspace`.
* Move notation `affine_space` to the bottom of `algebra/add_torsor`.
#### Estimated changes
Modified src/algebra/add_torsor.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/normed_space/mazur_ulam.lean


Modified src/linear_algebra/affine_space/affine_equiv.lean


Added src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* affine_map.add_linear
- \+ *lemma* affine_map.apply_line_map
- \+ *lemma* affine_map.coe_add
- \+ *lemma* affine_map.coe_comp
- \+ *lemma* affine_map.coe_const
- \+ *lemma* affine_map.coe_fst
- \+ *lemma* affine_map.coe_homothety_affine
- \+ *lemma* affine_map.coe_homothety_hom
- \+ *lemma* affine_map.coe_id
- \+ *lemma* affine_map.coe_line_map
- \+ *lemma* affine_map.coe_mk'
- \+ *lemma* affine_map.coe_mk
- \+ *lemma* affine_map.coe_mul
- \+ *lemma* affine_map.coe_one
- \+ *lemma* affine_map.coe_smul
- \+ *lemma* affine_map.coe_snd
- \+ *lemma* affine_map.coe_zero
- \+ *def* affine_map.comp
- \+ *lemma* affine_map.comp_apply
- \+ *lemma* affine_map.comp_assoc
- \+ *lemma* affine_map.comp_id
- \+ *lemma* affine_map.comp_line_map
- \+ *def* affine_map.const
- \+ *lemma* affine_map.const_linear
- \+ *lemma* affine_map.decomp'
- \+ *lemma* affine_map.decomp
- \+ *lemma* affine_map.ext
- \+ *lemma* affine_map.ext_iff
- \+ *def* affine_map.fst
- \+ *lemma* affine_map.fst_line_map
- \+ *lemma* affine_map.fst_linear
- \+ *def* affine_map.homothety
- \+ *lemma* affine_map.homothety_add
- \+ *def* affine_map.homothety_affine
- \+ *lemma* affine_map.homothety_apply
- \+ *lemma* affine_map.homothety_def
- \+ *def* affine_map.homothety_hom
- \+ *lemma* affine_map.homothety_mul
- \+ *lemma* affine_map.homothety_one
- \+ *lemma* affine_map.homothety_zero
- \+ *def* affine_map.id
- \+ *lemma* affine_map.id_apply
- \+ *lemma* affine_map.id_comp
- \+ *lemma* affine_map.id_linear
- \+ *lemma* affine_map.image_interval
- \+ *lemma* affine_map.injective_coe_fn
- \+ *def* affine_map.line_map
- \+ *lemma* affine_map.line_map_apply
- \+ *lemma* affine_map.line_map_apply_module'
- \+ *lemma* affine_map.line_map_apply_module
- \+ *lemma* affine_map.line_map_apply_one
- \+ *lemma* affine_map.line_map_apply_one_sub
- \+ *lemma* affine_map.line_map_apply_ring'
- \+ *lemma* affine_map.line_map_apply_ring
- \+ *lemma* affine_map.line_map_apply_zero
- \+ *lemma* affine_map.line_map_linear
- \+ *lemma* affine_map.line_map_same
- \+ *lemma* affine_map.line_map_same_apply
- \+ *lemma* affine_map.line_map_symm
- \+ *lemma* affine_map.line_map_vadd_apply
- \+ *lemma* affine_map.linear_map_vsub
- \+ *lemma* affine_map.map_vadd
- \+ *def* affine_map.mk'
- \+ *lemma* affine_map.mk'_linear
- \+ *def* affine_map.snd
- \+ *lemma* affine_map.snd_line_map
- \+ *lemma* affine_map.snd_linear
- \+ *lemma* affine_map.to_fun_eq_coe
- \+ *lemma* affine_map.vadd_apply
- \+ *lemma* affine_map.vsub_apply
- \+ *lemma* affine_map.zero_linear
- \+ *structure* affine_map
- \+ *lemma* linear_map.coe_to_affine_map
- \+ *def* linear_map.to_affine_map
- \+ *lemma* linear_map.to_affine_map_linear

Added src/linear_algebra/affine_space/affine_subspace.lean
- \+ *def* affine_span
- \+ *lemma* affine_span_insert_affine_span
- \+ *lemma* affine_span_insert_eq_affine_span
- \+ *lemma* affine_span_mono
- \+ *lemma* affine_span_nonempty
- \+ *lemma* affine_span_singleton_union_vadd_eq_top_of_span_eq_top
- \+ *lemma* affine_subspace.affine_span_coe
- \+ *lemma* affine_subspace.affine_span_eq_Inf
- \+ *lemma* affine_subspace.bot_coe
- \+ *lemma* affine_subspace.coe_affine_span_singleton
- \+ *lemma* affine_subspace.coe_direction_eq_vsub_set
- \+ *lemma* affine_subspace.coe_direction_eq_vsub_set_left
- \+ *lemma* affine_subspace.coe_direction_eq_vsub_set_right
- \+ *def* affine_subspace.direction
- \+ *lemma* affine_subspace.direction_affine_span_insert
- \+ *lemma* affine_subspace.direction_bot
- \+ *lemma* affine_subspace.direction_eq_top_iff_of_nonempty
- \+ *lemma* affine_subspace.direction_eq_vector_span
- \+ *lemma* affine_subspace.direction_inf
- \+ *lemma* affine_subspace.direction_inf_of_mem
- \+ *lemma* affine_subspace.direction_inf_of_mem_inf
- \+ *lemma* affine_subspace.direction_le
- \+ *lemma* affine_subspace.direction_lt_of_nonempty
- \+ *lemma* affine_subspace.direction_mk'
- \+ *def* affine_subspace.direction_of_nonempty
- \+ *lemma* affine_subspace.direction_of_nonempty_eq_direction
- \+ *lemma* affine_subspace.direction_sup
- \+ *lemma* affine_subspace.direction_top
- \+ *lemma* affine_subspace.eq_iff_direction_eq_of_mem
- \+ *lemma* affine_subspace.eq_of_direction_eq_of_nonempty_of_le
- \+ *lemma* affine_subspace.exists_of_lt
- \+ *lemma* affine_subspace.ext
- \+ *lemma* affine_subspace.ext_of_direction_eq
- \+ *lemma* affine_subspace.inf_coe
- \+ *lemma* affine_subspace.inter_eq_singleton_of_nonempty_of_is_compl
- \+ *lemma* affine_subspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
- \+ *lemma* affine_subspace.le_def'
- \+ *lemma* affine_subspace.le_def
- \+ *lemma* affine_subspace.lt_def
- \+ *lemma* affine_subspace.lt_iff_le_and_exists
- \+ *lemma* affine_subspace.mem_affine_span_insert_iff
- \+ *lemma* affine_subspace.mem_affine_span_singleton
- \+ *lemma* affine_subspace.mem_coe
- \+ *lemma* affine_subspace.mem_direction_iff_eq_vsub
- \+ *lemma* affine_subspace.mem_direction_iff_eq_vsub_left
- \+ *lemma* affine_subspace.mem_direction_iff_eq_vsub_right
- \+ *lemma* affine_subspace.mem_inf_iff
- \+ *lemma* affine_subspace.mem_top
- \+ *def* affine_subspace.mk'
- \+ *lemma* affine_subspace.mk'_eq
- \+ *lemma* affine_subspace.mk'_nonempty
- \+ *lemma* affine_subspace.not_le_iff_exists
- \+ *lemma* affine_subspace.not_mem_bot
- \+ *lemma* affine_subspace.self_mem_mk'
- \+ *lemma* affine_subspace.span_Union
- \+ *lemma* affine_subspace.span_empty
- \+ *lemma* affine_subspace.span_points_subset_coe_of_subset_coe
- \+ *lemma* affine_subspace.span_union
- \+ *lemma* affine_subspace.span_univ
- \+ *lemma* affine_subspace.sup_direction_le
- \+ *lemma* affine_subspace.sup_direction_lt_of_nonempty_of_inter_empty
- \+ *lemma* affine_subspace.top_coe
- \+ *lemma* affine_subspace.vadd_mem_iff_mem_direction
- \+ *lemma* affine_subspace.vadd_mem_mk'
- \+ *lemma* affine_subspace.vadd_mem_of_mem_direction
- \+ *lemma* affine_subspace.vsub_left_mem_direction_iff_mem
- \+ *lemma* affine_subspace.vsub_mem_direction
- \+ *lemma* affine_subspace.vsub_right_mem_direction_iff_mem
- \+ *structure* affine_subspace
- \+ *lemma* coe_affine_span
- \+ *lemma* direction_affine_span
- \+ *lemma* mem_affine_span
- \+ *lemma* mem_span_points
- \+ *def* span_points
- \+ *lemma* span_points_nonempty
- \+ *def* submodule.to_affine_subspace
- \+ *lemma* subset_affine_span
- \+ *lemma* subset_span_points
- \+ *lemma* vadd_mem_span_points_of_mem_span_points_of_mem_vector_span
- \+ *def* vector_span
- \+ *lemma* vector_span_def
- \+ *lemma* vector_span_empty
- \+ *lemma* vector_span_eq_span_vsub_set_left
- \+ *lemma* vector_span_eq_span_vsub_set_left_ne
- \+ *lemma* vector_span_eq_span_vsub_set_right
- \+ *lemma* vector_span_eq_span_vsub_set_right_ne
- \+ *lemma* vector_span_image_eq_span_vsub_set_left_ne
- \+ *lemma* vector_span_image_eq_span_vsub_set_right_ne
- \+ *lemma* vector_span_mono
- \+ *lemma* vector_span_range_eq_span_range_vsub_left
- \+ *lemma* vector_span_range_eq_span_range_vsub_left_ne
- \+ *lemma* vector_span_range_eq_span_range_vsub_right
- \+ *lemma* vector_span_range_eq_span_range_vsub_right_ne
- \+ *lemma* vector_span_singleton
- \+ *lemma* vsub_mem_vector_span
- \+ *lemma* vsub_mem_vector_span_of_mem_span_points_of_mem_span_points
- \+ *lemma* vsub_set_subset_vector_span

Modified src/linear_algebra/affine_space/basic.lean
- \- *lemma* affine_map.add_linear
- \- *lemma* affine_map.apply_line_map
- \- *lemma* affine_map.coe_add
- \- *lemma* affine_map.coe_comp
- \- *lemma* affine_map.coe_const
- \- *lemma* affine_map.coe_fst
- \- *lemma* affine_map.coe_homothety_affine
- \- *lemma* affine_map.coe_homothety_hom
- \- *lemma* affine_map.coe_id
- \- *lemma* affine_map.coe_line_map
- \- *lemma* affine_map.coe_mk'
- \- *lemma* affine_map.coe_mk
- \- *lemma* affine_map.coe_mul
- \- *lemma* affine_map.coe_one
- \- *lemma* affine_map.coe_smul
- \- *lemma* affine_map.coe_snd
- \- *lemma* affine_map.coe_zero
- \- *def* affine_map.comp
- \- *lemma* affine_map.comp_apply
- \- *lemma* affine_map.comp_assoc
- \- *lemma* affine_map.comp_id
- \- *lemma* affine_map.comp_line_map
- \- *def* affine_map.const
- \- *lemma* affine_map.const_linear
- \- *lemma* affine_map.decomp'
- \- *lemma* affine_map.decomp
- \- *lemma* affine_map.ext
- \- *lemma* affine_map.ext_iff
- \- *def* affine_map.fst
- \- *lemma* affine_map.fst_line_map
- \- *lemma* affine_map.fst_linear
- \- *def* affine_map.homothety
- \- *lemma* affine_map.homothety_add
- \- *def* affine_map.homothety_affine
- \- *lemma* affine_map.homothety_apply
- \- *lemma* affine_map.homothety_def
- \- *def* affine_map.homothety_hom
- \- *lemma* affine_map.homothety_mul
- \- *lemma* affine_map.homothety_one
- \- *lemma* affine_map.homothety_zero
- \- *def* affine_map.id
- \- *lemma* affine_map.id_apply
- \- *lemma* affine_map.id_comp
- \- *lemma* affine_map.id_linear
- \- *lemma* affine_map.image_interval
- \- *lemma* affine_map.injective_coe_fn
- \- *def* affine_map.line_map
- \- *lemma* affine_map.line_map_apply
- \- *lemma* affine_map.line_map_apply_module'
- \- *lemma* affine_map.line_map_apply_module
- \- *lemma* affine_map.line_map_apply_one
- \- *lemma* affine_map.line_map_apply_one_sub
- \- *lemma* affine_map.line_map_apply_ring'
- \- *lemma* affine_map.line_map_apply_ring
- \- *lemma* affine_map.line_map_apply_zero
- \- *lemma* affine_map.line_map_linear
- \- *lemma* affine_map.line_map_same
- \- *lemma* affine_map.line_map_same_apply
- \- *lemma* affine_map.line_map_symm
- \- *lemma* affine_map.line_map_vadd_apply
- \- *lemma* affine_map.linear_map_vsub
- \- *lemma* affine_map.map_vadd
- \- *def* affine_map.mk'
- \- *lemma* affine_map.mk'_linear
- \- *def* affine_map.snd
- \- *lemma* affine_map.snd_line_map
- \- *lemma* affine_map.snd_linear
- \- *lemma* affine_map.to_fun_eq_coe
- \- *lemma* affine_map.vadd_apply
- \- *lemma* affine_map.vsub_apply
- \- *lemma* affine_map.zero_linear
- \- *structure* affine_map
- \- *def* affine_span
- \- *lemma* affine_span_insert_affine_span
- \- *lemma* affine_span_insert_eq_affine_span
- \- *lemma* affine_span_mono
- \- *lemma* affine_span_nonempty
- \- *lemma* affine_span_singleton_union_vadd_eq_top_of_span_eq_top
- \- *lemma* affine_subspace.affine_span_coe
- \- *lemma* affine_subspace.affine_span_eq_Inf
- \- *lemma* affine_subspace.bot_coe
- \- *lemma* affine_subspace.coe_affine_span_singleton
- \- *lemma* affine_subspace.coe_direction_eq_vsub_set
- \- *lemma* affine_subspace.coe_direction_eq_vsub_set_left
- \- *lemma* affine_subspace.coe_direction_eq_vsub_set_right
- \- *def* affine_subspace.direction
- \- *lemma* affine_subspace.direction_affine_span_insert
- \- *lemma* affine_subspace.direction_bot
- \- *lemma* affine_subspace.direction_eq_top_iff_of_nonempty
- \- *lemma* affine_subspace.direction_eq_vector_span
- \- *lemma* affine_subspace.direction_inf
- \- *lemma* affine_subspace.direction_inf_of_mem
- \- *lemma* affine_subspace.direction_inf_of_mem_inf
- \- *lemma* affine_subspace.direction_le
- \- *lemma* affine_subspace.direction_lt_of_nonempty
- \- *lemma* affine_subspace.direction_mk'
- \- *def* affine_subspace.direction_of_nonempty
- \- *lemma* affine_subspace.direction_of_nonempty_eq_direction
- \- *lemma* affine_subspace.direction_sup
- \- *lemma* affine_subspace.direction_top
- \- *lemma* affine_subspace.eq_iff_direction_eq_of_mem
- \- *lemma* affine_subspace.eq_of_direction_eq_of_nonempty_of_le
- \- *lemma* affine_subspace.exists_of_lt
- \- *lemma* affine_subspace.ext
- \- *lemma* affine_subspace.ext_of_direction_eq
- \- *lemma* affine_subspace.inf_coe
- \- *lemma* affine_subspace.inter_eq_singleton_of_nonempty_of_is_compl
- \- *lemma* affine_subspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
- \- *lemma* affine_subspace.le_def'
- \- *lemma* affine_subspace.le_def
- \- *lemma* affine_subspace.lt_def
- \- *lemma* affine_subspace.lt_iff_le_and_exists
- \- *lemma* affine_subspace.mem_affine_span_insert_iff
- \- *lemma* affine_subspace.mem_affine_span_singleton
- \- *lemma* affine_subspace.mem_coe
- \- *lemma* affine_subspace.mem_direction_iff_eq_vsub
- \- *lemma* affine_subspace.mem_direction_iff_eq_vsub_left
- \- *lemma* affine_subspace.mem_direction_iff_eq_vsub_right
- \- *lemma* affine_subspace.mem_inf_iff
- \- *lemma* affine_subspace.mem_top
- \- *def* affine_subspace.mk'
- \- *lemma* affine_subspace.mk'_eq
- \- *lemma* affine_subspace.mk'_nonempty
- \- *lemma* affine_subspace.not_le_iff_exists
- \- *lemma* affine_subspace.not_mem_bot
- \- *lemma* affine_subspace.self_mem_mk'
- \- *lemma* affine_subspace.span_Union
- \- *lemma* affine_subspace.span_empty
- \- *lemma* affine_subspace.span_points_subset_coe_of_subset_coe
- \- *lemma* affine_subspace.span_union
- \- *lemma* affine_subspace.span_univ
- \- *lemma* affine_subspace.sup_direction_le
- \- *lemma* affine_subspace.sup_direction_lt_of_nonempty_of_inter_empty
- \- *lemma* affine_subspace.top_coe
- \- *lemma* affine_subspace.vadd_mem_iff_mem_direction
- \- *lemma* affine_subspace.vadd_mem_mk'
- \- *lemma* affine_subspace.vadd_mem_of_mem_direction
- \- *lemma* affine_subspace.vsub_left_mem_direction_iff_mem
- \- *lemma* affine_subspace.vsub_mem_direction
- \- *lemma* affine_subspace.vsub_right_mem_direction_iff_mem
- \- *structure* affine_subspace
- \- *lemma* coe_affine_span
- \- *lemma* direction_affine_span
- \- *lemma* linear_map.coe_to_affine_map
- \- *def* linear_map.to_affine_map
- \- *lemma* linear_map.to_affine_map_linear
- \- *lemma* mem_affine_span
- \- *lemma* mem_span_points
- \- *def* span_points
- \- *lemma* span_points_nonempty
- \- *def* submodule.to_affine_subspace
- \- *lemma* subset_affine_span
- \- *lemma* subset_span_points
- \- *lemma* vadd_mem_span_points_of_mem_span_points_of_mem_vector_span
- \- *def* vector_span
- \- *lemma* vector_span_def
- \- *lemma* vector_span_empty
- \- *lemma* vector_span_eq_span_vsub_set_left
- \- *lemma* vector_span_eq_span_vsub_set_left_ne
- \- *lemma* vector_span_eq_span_vsub_set_right
- \- *lemma* vector_span_eq_span_vsub_set_right_ne
- \- *lemma* vector_span_image_eq_span_vsub_set_left_ne
- \- *lemma* vector_span_image_eq_span_vsub_set_right_ne
- \- *lemma* vector_span_mono
- \- *lemma* vector_span_range_eq_span_range_vsub_left
- \- *lemma* vector_span_range_eq_span_range_vsub_left_ne
- \- *lemma* vector_span_range_eq_span_range_vsub_right
- \- *lemma* vector_span_range_eq_span_range_vsub_right_ne
- \- *lemma* vector_span_singleton
- \- *lemma* vsub_mem_vector_span
- \- *lemma* vsub_mem_vector_span_of_mem_span_points_of_mem_span_points
- \- *lemma* vsub_set_subset_vector_span

Modified src/linear_algebra/affine_space/combination.lean


Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/affine_space/independent.lean


Modified src/linear_algebra/affine_space/ordered.lean


Modified src/topology/algebra/affine.lean




## [2020-10-28 01:11:30](https://github.com/leanprover-community/mathlib/commit/4d1da54)
chore(scripts): update nolints.txt ([#4808](https://github.com/leanprover-community/mathlib/pull/4808))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-27 22:22:51](https://github.com/leanprover-community/mathlib/commit/c737996)
feat(algebra/algebra/subalgebra): algebra equalizer ([#4791](https://github.com/leanprover-community/mathlib/pull/4791))
Changes to subalgebra.lean from [#4786](https://github.com/leanprover-community/mathlib/pull/4786)
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *def* alg_hom.equalizer
- \+ *lemma* alg_hom.mem_equalizer



## [2020-10-27 22:22:50](https://github.com/leanprover-community/mathlib/commit/2a7e215)
feat(data/vector2): scanl and associated lemmas ([#4613](https://github.com/leanprover-community/mathlib/pull/4613))
#### Estimated changes
Modified src/data/vector2.lean
- \+/\- *lemma* vector.nth_cons_nil
- \+ *def* vector.scanl
- \+ *lemma* vector.scanl_cons
- \+ *lemma* vector.scanl_head
- \+ *lemma* vector.scanl_nil
- \+ *lemma* vector.scanl_nth
- \+ *lemma* vector.scanl_singleton
- \+ *lemma* vector.scanl_val
- \+ *lemma* vector.to_list_scanl



## [2020-10-27 19:53:05](https://github.com/leanprover-community/mathlib/commit/51e12c0)
chore(ring_theory/fractional_ideal): change exists_eq_span_singleton_mul ([#4800](https://github.com/leanprover-community/mathlib/pull/4800))
Replace assumption `(a : K)` with `(a : R)`
Add result `a \ne 0` 
Change `span_singleton` a to `span singleton (g.to_map a)^-1`
.. in the statement of lemma `exists_eq_span_singleton_mul`
Adapt dependences
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean




## [2020-10-27 19:53:03](https://github.com/leanprover-community/mathlib/commit/97065db)
refactor(data/polynomial): use `linear_map` for `monomial`, review `degree` ([#4784](https://github.com/leanprover-community/mathlib/pull/4784))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_hom.map_int_cast

Modified src/algebra/group/basic.lean
- \+ *theorem* one_eq_inv

Modified src/analysis/calculus/deriv.lean


Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean
- \+/\- *def* polynomial.monomial
- \+ *lemma* polynomial.monomial_def
- \+/\- *lemma* polynomial.monomial_zero_right
- \+ *lemma* polynomial.smul_monomial

Modified src/data/polynomial/degree.lean
- \- *lemma* polynomial.eq_C_of_nat_degree_eq_zero

Modified src/data/polynomial/degree/basic.lean
- \+/\- *lemma* polynomial.C_eq_int_cast
- \+ *lemma* polynomial.as_sum_range_C_mul_X_pow
- \+ *lemma* polynomial.as_sum_support_C_mul_X_pow
- \+ *lemma* polynomial.coeff_nat_degree
- \+ *lemma* polynomial.degree_C_mul_X_pow
- \+ *lemma* polynomial.degree_C_mul_X_pow_le
- \- *theorem* polynomial.degree_C_mul_X_pow_le
- \+/\- *lemma* polynomial.degree_X_pow
- \+/\- *lemma* polynomial.degree_monomial
- \+/\- *lemma* polynomial.degree_monomial_le
- \+ *lemma* polynomial.eq_C_of_nat_degree_eq_zero
- \+ *lemma* polynomial.eq_X_add_C_of_nat_degree_le_one
- \+ *lemma* polynomial.exists_eq_X_add_C_of_nat_degree_le_one
- \+/\- *lemma* polynomial.mem_support_C_mul_X_pow
- \+ *lemma* polynomial.monic.ne_zero_of_ne
- \+ *lemma* polynomial.monic.ne_zero_of_polynomial_ne
- \- *lemma* polynomial.monic.ne_zero_of_zero_ne_one
- \+/\- *lemma* polynomial.nat_degree_C_mul_X_pow_of_nonzero
- \+ *theorem* polynomial.nat_degree_le_iff_degree_le
- \- *theorem* polynomial.nat_degree_le_of_degree_le
- \+ *lemma* polynomial.supp_subset_range
- \+/\- *lemma* polynomial.support_C_mul_X_pow_nonzero

Modified src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* polynomial.le_trailing_degree_C_mul_X_pow
- \- *theorem* polynomial.le_trailing_degree_C_mul_X_pow
- \+ *lemma* polynomial.le_trailing_degree_monomial
- \- *lemma* polynomial.monomial_le_trailing_degree
- \+ *lemma* polynomial.nat_trailing_degree_monomial
- \+ *lemma* polynomial.nat_trailing_degree_monomial_le
- \+ *lemma* polynomial.trailing_degree_C_mul_X_pow
- \+/\- *lemma* polynomial.trailing_degree_monomial

Modified src/data/polynomial/derivative.lean
- \+ *lemma* polynomial.derivative_C_mul_X_pow
- \+/\- *lemma* polynomial.derivative_monomial

Modified src/data/polynomial/div.lean


Modified src/data/polynomial/erase_lead.lean


Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/monic.lean


Modified src/data/polynomial/monomial.lean
- \+ *theorem* polynomial.nontrivial.of_polynomial_ne
- \- *theorem* polynomial.nonzero.of_polynomial_ne

Modified src/data/real/irrational.lean
- \- *lemma* nat_degree_gt_one_of_irrational_root
- \+ *lemma* one_lt_nat_degree_of_irrational_root

Modified src/field_theory/separable.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/scale_roots.lean


Modified src/ring_theory/polynomial_algebra.lean
- \+ *lemma* poly_equiv_tensor.inv_fun_monomial



## [2020-10-27 19:53:01](https://github.com/leanprover-community/mathlib/commit/a1ab984)
feat(data/finset/lattice,order/basic): add lemmas in order_dual, prove dual order exchanges max' and min' ([#4715](https://github.com/leanprover-community/mathlib/pull/4715))
Introduce functionality to work with order duals and monotone decreasing maps.  The pretty part of the code is by Johan Commelin, the ugly part is my own addition!
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.nonempty.map

Modified src/data/finset/lattice.lean
- \+ *lemma* finset.max'_eq_of_dual_min'
- \+ *lemma* finset.min'_eq_of_dual_max'
- \+ *lemma* finset.of_dual_max_eq_min_of_dual
- \+ *lemma* finset.of_dual_min_eq_max_of_dual

Added src/order/order_dual.lean
- \+ *lemma* order_dual.le_to_dual
- \+ *lemma* order_dual.lt_to_dual
- \+ *def* order_dual.of_dual
- \+ *lemma* order_dual.of_dual_inj
- \+ *lemma* order_dual.of_dual_le_of_dual
- \+ *lemma* order_dual.of_dual_lt_of_dual
- \+ *lemma* order_dual.of_dual_symm_eq
- \+ *lemma* order_dual.of_dual_to_dual
- \+ *def* order_dual.to_dual
- \+ *lemma* order_dual.to_dual_inj
- \+ *lemma* order_dual.to_dual_le
- \+ *lemma* order_dual.to_dual_le_to_dual
- \+ *lemma* order_dual.to_dual_lt
- \+ *lemma* order_dual.to_dual_lt_to_dual
- \+ *lemma* order_dual.to_dual_of_dual
- \+ *lemma* order_dual.to_dual_symm_eq



## [2020-10-27 17:20:51](https://github.com/leanprover-community/mathlib/commit/1efbf13)
feat(data/vector2): add lemma map_id ([#4799](https://github.com/leanprover-community/mathlib/pull/4799))
`map_id` proves that a vector is unchanged when mapped under the `id` function. This is similar to `list.map_id`. This lemma was marked with the `simp` attribute to make it available to the simplifier.
#### Estimated changes
Modified src/data/vector2.lean
- \+ *lemma* vector.map_id



## [2020-10-27 17:20:47](https://github.com/leanprover-community/mathlib/commit/40e514c)
feat(algebra/monoid_algebra): formula for `lift_nc f g (c • φ)` ([#4782](https://github.com/leanprover-community/mathlib/pull/4782))
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.lift_nc_smul
- \+ *lemma* monoid_algebra.lift_nc_smul
- \+/\- *lemma* monoid_algebra.single_algebra_map_eq_algebra_map_mul_of



## [2020-10-27 17:20:45](https://github.com/leanprover-community/mathlib/commit/99acfda)
feat(category_theory/sites): pretopology ([#4648](https://github.com/leanprover-community/mathlib/pull/4648))
Adds pretopologies.
#### Estimated changes
Added src/category_theory/sites/pretopology.lean
- \+ *def* category_theory.pretopology.gi
- \+ *lemma* category_theory.pretopology.mem_to_grothendieck
- \+ *def* category_theory.pretopology.of_grothendieck
- \+ *def* category_theory.pretopology.to_grothendieck
- \+ *lemma* category_theory.pretopology.to_grothendieck_bot
- \+ *def* category_theory.pretopology.trivial
- \+ *structure* category_theory.pretopology
- \+ *def* category_theory.pullback_arrows
- \+ *lemma* category_theory.pullback_arrows_comm
- \+ *lemma* category_theory.pullback_singleton



## [2020-10-27 14:39:13](https://github.com/leanprover-community/mathlib/commit/a027a37)
feat(tactic/simps): user-provided names for projections ([#4663](https://github.com/leanprover-community/mathlib/pull/4663))
Adds the functionality to specify custom projection names, like this:
```lean
initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)
```
These names will always be used and cannot (yet) be manually overridden. 
Implement this for embeddings: `initialize_simps_projections embedding (to_fun → apply)`.
Rename `fixed_points.to_alg_hom_apply -> fixed_points.to_alg_hom_apply_apply`, since `@[simps]` now generates the name `to_alg_hom_apply` instead of `to_alg_hom_to_fun`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/field_theory/fixed.lean
- \- *lemma* fixed_points.to_alg_hom_apply
- \+ *lemma* fixed_points.to_alg_hom_apply_apply

Modified src/logic/embedding.lean
- \+/\- *def* function.embedding.sigma_map
- \+/\- *def* function.embedding.sigma_mk
- \+/\- *def* set.embedding_of_subset

Modified src/measure_theory/haar_measure.lean


Modified src/tactic/simps.lean


Modified test/simps.lean
- \+ *def* manual_projection_names.equiv.simps.inv_fun
- \+ *def* manual_projection_names.equiv.symm
- \+ *structure* manual_projection_names.equiv



## [2020-10-27 11:55:33](https://github.com/leanprover-community/mathlib/commit/e0b153b)
refactor(*): drop `decidable_linear_order`, switch to Lean 3.22.0 ([#4762](https://github.com/leanprover-community/mathlib/pull/4762))
The main non-bc change in Lean 3.22.0 is leanprover-community/lean[#484](https://github.com/leanprover-community/mathlib/pull/484) which merges `linear_order`
with `decidable_linear_order`. This is the `mathlib` part of this PR.
## List of API changes
* All `*linear_order*` typeclasses now imply decidability of `(≤)`, `(<)`, and `(=)`.
* Drop `classical.DLO`.
* Drop `discrete_linear_ordered_field`, use `linear_ordered_field` instead.
* Drop `decidable_linear_ordered_semiring`, use `linear_ordered_semiring` instead.
* Drop `decidable_linear_ordered_comm_ring`, use `linear_ordered_comm_ring` instead;
* Rename `decidable_linear_ordered_cancel_add_comm_monoid` to `linear_ordered_cancel_add_comm_monoid`.
* Rename `decidable_linear_ordered_add_comm_group` to `linear_ordered_add_comm_group`.
* Modify some lemmas to use weaker typeclass assumptions.
* Add more lemmas about `ordering.compares`, including `linear_order_of_compares` which
  constructs a `linear_order` instance from `cmp` function.
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean
- \+/\- *lemma* Ico_lemma

Modified leanpkg.toml


Modified src/algebra/archimedean.lean
- \- *lemma* decidable_linear_ordered_add_comm_group.exists_int_smul_near_of_pos'
- \- *lemma* decidable_linear_ordered_add_comm_group.exists_int_smul_near_of_pos
- \+/\- *lemma* exists_int_pow_near'
- \+/\- *lemma* exists_int_pow_near
- \+ *lemma* linear_ordered_add_comm_group.exists_int_smul_near_of_pos'
- \+ *lemma* linear_ordered_add_comm_group.exists_int_smul_near_of_pos

Modified src/algebra/big_operators/order.lean
- \+/\- *lemma* finset.abs_sum_le_sum_abs

Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/continued_fractions/computation/basic.lean


Modified src/algebra/continued_fractions/computation/correctness_terminating.lean


Modified src/algebra/continued_fractions/computation/translations.lean


Modified src/algebra/field_power.lean
- \+/\- *lemma* one_lt_fpow

Modified src/algebra/floor.lean
- \+/\- *lemma* abs_sub_lt_one_of_floor_eq_floor

Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* abs_neg_one_pow
- \+/\- *lemma* pow_abs

Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/order.lean
- \+/\- *theorem* cmp_compares
- \+/\- *lemma* decidable.le_iff_le_iff_lt_iff_lt
- \+/\- *lemma* decidable.le_imp_le_iff_lt_imp_lt
- \+ *def* linear_order_of_compares
- \+/\- *theorem* ordering.compares.eq_gt
- \+ *theorem* ordering.compares.le_antisymm
- \+ *theorem* ordering.compares.le_total
- \+ *theorem* ordering.compares.ne_gt
- \+ *theorem* ordering.compares.ne_lt
- \+ *theorem* ordering.compares_swap
- \+ *theorem* ordering.swap_eq_iff_eq_swap

Modified src/algebra/order_functions.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_group.lean
- \- *lemma* decidable_linear_ordered_add_comm_group.add_lt_add_left
- \+ *lemma* exists_gt_zero
- \+/\- *lemma* fn_min_mul_fn_max
- \+ *lemma* linear_ordered_add_comm_group.add_lt_add_left
- \+/\- *lemma* min_mul_max
- \- *def* nonneg_add_comm_group.to_decidable_linear_ordered_add_comm_group
- \+ *def* nonneg_add_comm_group.to_linear_ordered_add_comm_group
- \+/\- *theorem* units.max_coe
- \+/\- *theorem* units.min_coe

Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* abs_two
- \- *def* linear_nonneg_ring.to_decidable_linear_ordered_comm_ring
- \+/\- *def* linear_nonneg_ring.to_linear_order
- \+ *def* linear_nonneg_ring.to_linear_ordered_comm_ring
- \+/\- *def* linear_nonneg_ring.to_linear_ordered_ring

Modified src/algebra/punit_instances.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/extrema.lean


Modified src/combinatorics/pigeonhole.lean


Modified src/data/bool.lean


Modified src/data/char.lean


Modified src/data/complex/exponential.lean
- \+/\- *lemma* complex.sum_div_factorial_le

Modified src/data/fin.lean


Modified src/data/finset/fold.lean


Modified src/data/finset/lattice.lean


Modified src/data/finset/sort.lean


Modified src/data/fintype/sort.lean


Modified src/data/int/basic.lean


Modified src/data/int/cast.lean
- \+/\- *theorem* int.cast_abs
- \+/\- *theorem* int.cast_max
- \+/\- *theorem* int.cast_min

Modified src/data/list/basic.lean
- \+/\- *lemma* list.exists_le_of_sum_le
- \+/\- *lemma* list.exists_lt_of_sum_lt

Modified src/data/list/min_max.lean


Modified src/data/matrix/pequiv.lean


Modified src/data/multiset/basic.lean
- \+/\- *lemma* multiset.abs_sum_le_sum_abs

Modified src/data/nat/basic.lean


Modified src/data/nat/cast.lean
- \+/\- *theorem* nat.abs_cast
- \+/\- *theorem* nat.cast_max
- \+/\- *theorem* nat.cast_min

Modified src/data/nat/choose/dvd.lean


Modified src/data/nat/enat.lean


Modified src/data/num/lemmas.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/padics/ring_homs.lean


Modified src/data/pnat/basic.lean


Modified src/data/polynomial/degree/trailing_degree.lean
- \+/\- *lemma* polynomial.coeff_eq_zero_of_lt_nat_trailing_degree
- \+/\- *lemma* polynomial.coeff_eq_zero_of_trailing_degree_lt
- \+/\- *lemma* polynomial.coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt
- \+/\- *lemma* polynomial.coeff_nat_trailing_degree_pred_eq_zero
- \+/\- *theorem* polynomial.le_trailing_degree_C_mul_X_pow
- \+/\- *theorem* polynomial.le_trailing_degree_X_pow
- \+/\- *lemma* polynomial.monomial_le_trailing_degree
- \+/\- *lemma* polynomial.nat_trailing_degree_eq_of_trailing_degree_eq
- \+/\- *lemma* polynomial.nat_trailing_degree_le_nat_trailing_degree
- \+/\- *theorem* polynomial.nat_trailing_degree_le_of_trailing_degree_le
- \+/\- *lemma* polynomial.nat_trailing_degree_le_trailing_degree
- \+/\- *lemma* polynomial.nat_trailing_degree_neg
- \+/\- *lemma* polynomial.nat_trailing_degree_one
- \+/\- *lemma* polynomial.trailing_degree_eq_nat_trailing_degree
- \+/\- *lemma* polynomial.trailing_degree_le_trailing_degree

Modified src/data/polynomial/eval.lean


Modified src/data/rat/basic.lean


Modified src/data/rat/cast.lean
- \+/\- *theorem* rat.cast_abs
- \+/\- *theorem* rat.cast_max
- \+/\- *theorem* rat.cast_min

Modified src/data/rat/order.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean
- \+/\- *def* cau_seq
- \+/\- *def* is_cau_seq

Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.coe_abs
- \+/\- *lemma* hyperreal.coe_max
- \+/\- *lemma* hyperreal.coe_min

Modified src/data/real/nnreal.lean


Modified src/data/set/finite.lean
- \+/\- *lemma* set.Union_Inter_of_monotone

Modified src/data/set/intervals/basic.lean


Modified src/data/set/intervals/disjoint.lean


Modified src/data/set/intervals/ord_connected.lean


Modified src/data/set/intervals/unordered_interval.lean


Modified src/data/string/basic.lean


Modified src/data/support.lean
- \+/\- *lemma* function.support_max
- \+/\- *lemma* function.support_min

Modified src/data/zsqrtd/basic.lean


Modified src/group_theory/archimedean.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/perm/cycles.lean
- \+/\- *def* equiv.perm.cycle_factors

Modified src/group_theory/perm/sign.lean
- \+/\- *def* equiv.perm.swap_factors

Modified src/linear_algebra/affine_space/basic.lean
- \+/\- *lemma* affine_map.image_interval

Modified src/linear_algebra/finite_dimensional.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/interval_integral.lean


Modified src/order/basic.lean
- \- *def* decidable_linear_order.lift

Modified src/order/bounded_lattice.lean
- \+/\- *theorem* with_bot.coe_le_coe
- \+/\- *theorem* with_bot.inf_eq_min
- \+/\- *theorem* with_bot.lattice_eq_DLO
- \+/\- *theorem* with_bot.some_le_some
- \+/\- *theorem* with_bot.sup_eq_max
- \+/\- *theorem* with_top.inf_eq_min
- \+/\- *theorem* with_top.lattice_eq_DLO
- \+/\- *theorem* with_top.sup_eq_max

Modified src/order/bounds.lean
- \+/\- *lemma* is_greatest.insert
- \+/\- *lemma* is_greatest.union
- \+/\- *lemma* is_greatest_pair
- \+/\- *lemma* is_least.insert
- \+/\- *lemma* is_least.union
- \+/\- *lemma* is_least_pair

Modified src/order/category/NonemptyFinLinOrd.lean


Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/extr.lean


Modified src/order/filter/filter_product.lean
- \+/\- *lemma* filter.germ.abs_def
- \+/\- *lemma* filter.germ.const_abs
- \+/\- *lemma* filter.germ.const_max
- \+/\- *lemma* filter.germ.const_min
- \+/\- *lemma* filter.germ.max_def
- \+/\- *lemma* filter.germ.min_def

Modified src/order/lattice.lean
- \+/\- *theorem* inf_eq_min
- \+/\- *theorem* sup_eq_max

Modified src/order/lexicographic.lean


Modified src/order/pilex.lean


Modified src/order/rel_classes.lean
- \- *def* decidable_linear_order_of_STO'
- \+/\- *def* linear_order_of_STO'

Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/valuation/basic.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/set_theory/surreal.lean


Modified src/tactic/interval_cases.lean


Modified src/tactic/monotonicity/interactive.lean
- \+/\- *def* tactic.interactive.list.minimum_on

Modified src/testing/slim_check/sampleable.lean


Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* summable_abs_iff

Modified src/topology/algebra/ordered.lean
- \- *lemma* decidable_linear_ordered_add_comm_group.tendsto_nhds
- \+ *lemma* linear_ordered_add_comm_group.tendsto_nhds
- \+/\- *lemma* tendsto_abs_at_top_at_top

Modified src/topology/algebra/polynomial.lean
- \+/\- *lemma* polynomial.tendsto_infinity

Modified src/topology/local_extr.lean


Modified src/topology/uniform_space/absolute_value.lean


Modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* cauchy_seq.mem_entourage

Modified test/linarith.lean


Modified test/monotonicity.lean




## [2020-10-27 01:56:15](https://github.com/leanprover-community/mathlib/commit/69db7a3)
chore(scripts): update nolints.txt ([#4797](https://github.com/leanprover-community/mathlib/pull/4797))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-26 23:04:21](https://github.com/leanprover-community/mathlib/commit/6e2980c)
chore(*): reflow some long lines ([#4794](https://github.com/leanprover-community/mathlib/pull/4794))
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/algebra/algebra/basic.lean
- \+/\- *def* alg_equiv.of_alg_hom

Modified src/algebra/algebra/operations.lean


Modified src/algebra/archimedean.lean


Modified src/algebra/associated.lean
- \+/\- *lemma* irreducible_of_prime
- \+/\- *lemma* prime_of_associated

Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* ring_hom.map_prod

Modified src/algebra/big_operators/intervals.lean


Modified src/algebra/big_operators/ring.lean
- \+/\- *lemma* finset.prod_powerset_insert

Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/category/CommRing/adjunctions.lean


Modified src/algebra/char_p.lean
- \+/\- *lemma* char_p_of_prime_pow_injective

Modified src/algebra/continued_fractions/computation/basic.lean


Modified src/algebra/direct_limit.lean
- \+/\- *lemma* add_comm_group.direct_limit.lift_add
- \+/\- *lemma* add_comm_group.direct_limit.lift_sub
- \+/\- *lemma* add_comm_group.direct_limit.of_add
- \+/\- *lemma* add_comm_group.direct_limit.of_sub
- \+/\- *lemma* module.direct_limit.of.zero_exact_aux
- \+/\- *theorem* ring.direct_limit.induction_on
- \+/\- *lemma* ring.direct_limit.of.zero_exact_aux
- \+/\- *lemma* ring.direct_limit.of_pow

Modified src/algebra/gcd_monoid.lean


Modified src/algebra/geom_sum.lean
- \+/\- *lemma* op_geom_series

Modified src/algebra/monoid_algebra.lean




## [2020-10-26 23:04:19](https://github.com/leanprover-community/mathlib/commit/8746f08)
feat(data/equiv/basic): equiv.set.powerset ([#4790](https://github.com/leanprover-community/mathlib/pull/4790))
#### Estimated changes
Modified src/data/equiv/basic.lean




## [2020-10-26 21:30:45](https://github.com/leanprover-community/mathlib/commit/c76c3c5)
feat(degree/basic.lean): degree_lt_iff_coeff_zero ([#4792](https://github.com/leanprover-community/mathlib/pull/4792))
Changes to degree/basic.lean from [#4786](https://github.com/leanprover-community/mathlib/pull/4786)
#### Estimated changes
Modified src/data/polynomial/degree/basic.lean
- \+ *theorem* polynomial.degree_lt_iff_coeff_zero



## [2020-10-26 18:39:32](https://github.com/leanprover-community/mathlib/commit/95b3add)
fix(tactic/derive_fintype): add support for props ([#4777](https://github.com/leanprover-community/mathlib/pull/4777))
This adds support for propositional arguments in inductive constructors.
It was previously not handled, and while it *almost* works without
change, we have to use `Sigma' (a:A) (b:B) (c:C), unit` to tuple up the
arguments instead of `Sigma' (a:A) (b:B), C` because it would cause problems
in the unary case where there is only one propositional field.
#### Estimated changes
Modified src/tactic/derive_fintype.lean


Modified test/derive_fintype.lean
- \+ *structure* foo4



## [2020-10-26 18:39:30](https://github.com/leanprover-community/mathlib/commit/9428598)
feat(tactic/rcases): add `rintro (x y : t)` support ([#4722](https://github.com/leanprover-community/mathlib/pull/4722))
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/rintros/near/213999254
#### Estimated changes
Modified src/tactic/rcases.lean


Modified test/rcases.lean




## [2020-10-26 18:39:29](https://github.com/leanprover-community/mathlib/commit/877a20e)
feat(ring_theory/finiteness): some finiteness notions in commutative algebra ([#4634](https://github.com/leanprover-community/mathlib/pull/4634))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean


Modified src/ring_theory/adjoin.lean


Added src/ring_theory/finiteness.lean
- \+ *lemma* alg_hom.finite.comp
- \+ *lemma* alg_hom.finite.finite_type
- \+ *lemma* alg_hom.finite.id
- \+ *lemma* alg_hom.finite.of_surjective
- \+ *def* alg_hom.finite
- \+ *lemma* alg_hom.finite_type.comp
- \+ *lemma* alg_hom.finite_type.comp_surjective
- \+ *lemma* alg_hom.finite_type.id
- \+ *lemma* alg_hom.finite_type.of_surjective
- \+ *def* alg_hom.finite_type
- \+ *lemma* algebra.finite_type.equiv
- \+ *lemma* algebra.finite_type.of_surjective
- \+ *lemma* algebra.finite_type.self
- \+ *lemma* algebra.finite_type.trans
- \+ *def* algebra.finite_type
- \+ *lemma* module.finite.equiv
- \+ *lemma* module.finite.of_injective
- \+ *lemma* module.finite.of_surjective
- \+ *lemma* module.finite.trans
- \+ *def* module.finite
- \+ *lemma* module.finite_def
- \+ *lemma* ring_hom.finite.comp
- \+ *lemma* ring_hom.finite.finite_type
- \+ *lemma* ring_hom.finite.id
- \+ *lemma* ring_hom.finite.of_surjective
- \+ *def* ring_hom.finite
- \+ *lemma* ring_hom.finite_type.comp
- \+ *lemma* ring_hom.finite_type.comp_surjective
- \+ *lemma* ring_hom.finite_type.id
- \+ *lemma* ring_hom.finite_type.of_surjective
- \+ *def* ring_hom.finite_type



## [2020-10-26 18:39:27](https://github.com/leanprover-community/mathlib/commit/61c095f)
chore(algebra/module,linear_algebra): split off a `linear_map` file ([#4476](https://github.com/leanprover-community/mathlib/pull/4476))
In order to make `algebra/module/basic.lean` and `linear_algebra/basic.lean` a bit more manageable, move the basic facts about `linear_map`s and `linear_equiv`s into a separate file. `linear_algebra/basic.lean` still needs to be split a bit more.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \- *def* add_monoid_hom.to_int_linear_map
- \- *def* add_monoid_hom.to_rat_linear_map
- \- *lemma* is_linear_map.is_linear_map_neg
- \- *lemma* is_linear_map.is_linear_map_smul'
- \- *lemma* is_linear_map.is_linear_map_smul
- \- *lemma* is_linear_map.map_neg
- \- *lemma* is_linear_map.map_sub
- \- *lemma* is_linear_map.map_zero
- \- *def* is_linear_map.mk'
- \- *theorem* is_linear_map.mk'_apply
- \- *structure* is_linear_map
- \- *theorem* linear_map.coe_injective
- \- *lemma* linear_map.coe_mk
- \- *def* linear_map.comp
- \- *lemma* linear_map.comp_apply
- \- *lemma* linear_map.comp_coe
- \- *theorem* linear_map.ext
- \- *theorem* linear_map.ext_iff
- \- *theorem* linear_map.ext_ring
- \- *def* linear_map.id
- \- *lemma* linear_map.id_apply
- \- *lemma* linear_map.id_coe
- \- *theorem* linear_map.is_linear
- \- *lemma* linear_map.map_add
- \- *lemma* linear_map.map_neg
- \- *lemma* linear_map.map_smul
- \- *lemma* linear_map.map_sub
- \- *lemma* linear_map.map_sum
- \- *lemma* linear_map.map_zero
- \- *def* linear_map.to_add_monoid_hom
- \- *lemma* linear_map.to_add_monoid_hom_coe
- \- *theorem* linear_map.to_add_monoid_hom_injective
- \- *lemma* linear_map.to_fun_eq_coe
- \- *structure* linear_map
- \- *abbreviation* module.End

Added src/algebra/module/linear_map.lean
- \+ *def* add_monoid_hom.to_int_linear_map
- \+ *def* add_monoid_hom.to_rat_linear_map
- \+ *lemma* is_linear_map.is_linear_map_neg
- \+ *lemma* is_linear_map.is_linear_map_smul'
- \+ *lemma* is_linear_map.is_linear_map_smul
- \+ *lemma* is_linear_map.map_neg
- \+ *lemma* is_linear_map.map_sub
- \+ *lemma* is_linear_map.map_zero
- \+ *def* is_linear_map.mk'
- \+ *theorem* is_linear_map.mk'_apply
- \+ *structure* is_linear_map
- \+ *theorem* linear_equiv.apply_symm_apply
- \+ *theorem* linear_equiv.coe_coe
- \+ *lemma* linear_equiv.coe_to_add_equiv
- \+ *lemma* linear_equiv.coe_to_equiv
- \+ *lemma* linear_equiv.comp_coe
- \+ *lemma* linear_equiv.eq_symm_apply
- \+ *lemma* linear_equiv.ext
- \+ *lemma* linear_equiv.injective_to_equiv
- \+ *lemma* linear_equiv.injective_to_linear_map
- \+ *lemma* linear_equiv.inv_fun_apply
- \+ *theorem* linear_equiv.map_add
- \+ *theorem* linear_equiv.map_eq_zero_iff
- \+ *theorem* linear_equiv.map_ne_zero_iff
- \+ *theorem* linear_equiv.map_smul
- \+ *lemma* linear_equiv.map_sum
- \+ *theorem* linear_equiv.map_zero
- \+ *lemma* linear_equiv.mk_apply
- \+ *def* linear_equiv.refl
- \+ *lemma* linear_equiv.refl_apply
- \+ *lemma* linear_equiv.refl_to_linear_map
- \+ *lemma* linear_equiv.refl_trans
- \+ *def* linear_equiv.symm
- \+ *theorem* linear_equiv.symm_apply_apply
- \+ *lemma* linear_equiv.symm_apply_eq
- \+ *theorem* linear_equiv.symm_symm
- \+ *lemma* linear_equiv.symm_trans
- \+ *lemma* linear_equiv.symm_trans_apply
- \+ *def* linear_equiv.to_equiv
- \+ *lemma* linear_equiv.to_equiv_inj
- \+ *lemma* linear_equiv.to_fun_apply
- \+ *lemma* linear_equiv.to_linear_map_inj
- \+ *def* linear_equiv.trans
- \+ *theorem* linear_equiv.trans_apply
- \+ *lemma* linear_equiv.trans_refl
- \+ *lemma* linear_equiv.trans_symm
- \+ *structure* linear_equiv
- \+ *theorem* linear_map.coe_injective
- \+ *lemma* linear_map.coe_mk
- \+ *def* linear_map.comp
- \+ *lemma* linear_map.comp_apply
- \+ *lemma* linear_map.comp_coe
- \+ *theorem* linear_map.ext
- \+ *theorem* linear_map.ext_iff
- \+ *theorem* linear_map.ext_ring
- \+ *def* linear_map.id
- \+ *lemma* linear_map.id_apply
- \+ *lemma* linear_map.id_coe
- \+ *def* linear_map.inverse
- \+ *theorem* linear_map.is_linear
- \+ *lemma* linear_map.map_add
- \+ *lemma* linear_map.map_neg
- \+ *lemma* linear_map.map_smul
- \+ *lemma* linear_map.map_sub
- \+ *lemma* linear_map.map_sum
- \+ *lemma* linear_map.map_zero
- \+ *def* linear_map.to_add_monoid_hom
- \+ *lemma* linear_map.to_add_monoid_hom_coe
- \+ *theorem* linear_map.to_add_monoid_hom_injective
- \+ *lemma* linear_map.to_fun_eq_coe
- \+ *structure* linear_map
- \+ *abbreviation* module.End

Modified src/algebra/module/submodule.lean


Modified src/data/dfinsupp.lean


Modified src/data/finsupp/basic.lean


Modified src/linear_algebra/basic.lean
- \- *theorem* linear_equiv.apply_symm_apply
- \- *theorem* linear_equiv.coe_coe
- \- *lemma* linear_equiv.coe_to_add_equiv
- \- *lemma* linear_equiv.coe_to_equiv
- \- *lemma* linear_equiv.comp_coe
- \- *lemma* linear_equiv.eq_symm_apply
- \- *lemma* linear_equiv.ext
- \- *lemma* linear_equiv.injective_to_equiv
- \- *lemma* linear_equiv.injective_to_linear_map
- \- *lemma* linear_equiv.inv_fun_apply
- \- *theorem* linear_equiv.map_add
- \- *theorem* linear_equiv.map_eq_zero_iff
- \- *theorem* linear_equiv.map_ne_zero_iff
- \- *theorem* linear_equiv.map_smul
- \- *lemma* linear_equiv.map_sum
- \- *theorem* linear_equiv.map_zero
- \- *lemma* linear_equiv.mk_apply
- \- *def* linear_equiv.refl
- \- *lemma* linear_equiv.refl_apply
- \- *lemma* linear_equiv.refl_to_linear_map
- \- *lemma* linear_equiv.refl_trans
- \- *def* linear_equiv.symm
- \- *theorem* linear_equiv.symm_apply_apply
- \- *lemma* linear_equiv.symm_apply_eq
- \- *theorem* linear_equiv.symm_symm
- \- *lemma* linear_equiv.symm_trans
- \- *lemma* linear_equiv.symm_trans_apply
- \- *def* linear_equiv.to_equiv
- \- *lemma* linear_equiv.to_equiv_inj
- \- *lemma* linear_equiv.to_fun_apply
- \- *lemma* linear_equiv.to_linear_map_inj
- \- *def* linear_equiv.trans
- \- *theorem* linear_equiv.trans_apply
- \- *lemma* linear_equiv.trans_refl
- \- *lemma* linear_equiv.trans_symm
- \- *structure* linear_equiv
- \- *def* linear_map.inverse



## [2020-10-26 16:13:21](https://github.com/leanprover-community/mathlib/commit/83edb50)
feat(simps): improve error messages ([#4653](https://github.com/leanprover-community/mathlib/pull/4653))
If a custom projection has a different type than the expected projection, then it will show a more specific error message.
Also reflow most long lines
Also add some tests
#### Estimated changes
Modified src/tactic/simps.lean


Modified test/simps.lean
- \- *structure* failty_manual_coercion.equiv
- \+ *structure* faulty_manual_coercion.equiv
- \+ *def* faulty_universes.equiv.simps.inv_fun
- \+ *def* faulty_universes.equiv.symm
- \+ *structure* faulty_universes.equiv
- \+ *def* manual_universes.equiv.simps.inv_fun
- \+ *def* manual_universes.equiv.symm
- \+ *structure* manual_universes.equiv



## [2020-10-26 14:18:36](https://github.com/leanprover-community/mathlib/commit/ba5594a)
feat(data/dfinsupp): Add missing to_additive lemmas ([#4788](https://github.com/leanprover-community/mathlib/pull/4788))
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.prod_inv
- \+ *lemma* dfinsupp.prod_mul
- \+ *lemma* dfinsupp.prod_one
- \- *lemma* dfinsupp.sum_add
- \- *lemma* dfinsupp.sum_neg
- \- *lemma* dfinsupp.sum_zero



## [2020-10-26 13:22:48](https://github.com/leanprover-community/mathlib/commit/2e90c60)
feat(ring_theory/witt_vector/basic): verifying the ring axioms ([#4694](https://github.com/leanprover-community/mathlib/pull/4694))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Added src/ring_theory/witt_vector/basic.lean
- \+ *def* witt_vector.ghost_component
- \+ *lemma* witt_vector.ghost_component_apply
- \+ *def* witt_vector.ghost_equiv
- \+ *lemma* witt_vector.ghost_equiv_coe
- \+ *lemma* witt_vector.ghost_map.bijective_of_invertible
- \+ *def* witt_vector.ghost_map
- \+ *lemma* witt_vector.ghost_map_apply
- \+ *def* witt_vector.map
- \+ *lemma* witt_vector.map_coeff
- \+ *lemma* witt_vector.map_fun.add
- \+ *lemma* witt_vector.map_fun.injective
- \+ *lemma* witt_vector.map_fun.mul
- \+ *lemma* witt_vector.map_fun.neg
- \+ *lemma* witt_vector.map_fun.one
- \+ *lemma* witt_vector.map_fun.surjective
- \+ *lemma* witt_vector.map_fun.zero
- \+ *def* witt_vector.map_fun
- \+ *lemma* witt_vector.map_injective
- \+ *lemma* witt_vector.map_surjective



## [2020-10-26 05:21:12](https://github.com/leanprover-community/mathlib/commit/7be82f9)
chore(scripts): update nolints.txt ([#4785](https://github.com/leanprover-community/mathlib/pull/4785))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-26 05:21:10](https://github.com/leanprover-community/mathlib/commit/b2b39ed)
chore(order/galois_connection): define `with_bot.gi_get_or_else_bot` ([#4781](https://github.com/leanprover-community/mathlib/pull/4781))
This Galois insertion can be used to golf proofs about
`polynomial.degree` vs `polynomial.nat_degree`.
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* option.get_or_else_coe

Modified src/order/bounded_lattice.lean
- \+ *lemma* with_bot.get_or_else_bot
- \+ *lemma* with_bot.get_or_else_bot_le_iff

Modified src/order/galois_connection.lean
- \+ *def* with_bot.gi_get_or_else_bot



## [2020-10-26 05:21:08](https://github.com/leanprover-community/mathlib/commit/121c9a4)
chore(algebra/group/hom): use `coe_comp` in `simp` lemmas ([#4780](https://github.com/leanprover-community/mathlib/pull/4780))
This way Lean will simplify `⇑(f.comp g)` even if it is not applied to
an element.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.coe_comp
- \+/\- *lemma* monoid_hom.comp_apply
- \+ *lemma* mul_hom.coe_comp
- \+/\- *lemma* mul_hom.comp_apply
- \+ *lemma* one_hom.coe_comp
- \+/\- *lemma* one_hom.comp_apply

Modified src/algebra/ring/basic.lean
- \+ *lemma* add_monoid_hom.coe_mul_right
- \+/\- *lemma* add_monoid_hom.mul_right_apply



## [2020-10-26 05:21:06](https://github.com/leanprover-community/mathlib/commit/6e4fe98)
chore(data/polynomial/{degree/basic, eval}): Some trivial lemmas about polynomials ([#4768](https://github.com/leanprover-community/mathlib/pull/4768))
I have added the lemma `supp_card_le_succ_nat_degree` about the cardinality of the support of a polynomial and removed the useless commutativity assumptio in `map_sum` and `map_neg`.
#### Estimated changes
Modified src/data/polynomial/degree/basic.lean
- \+ *lemma* polynomial.card_supp_le_succ_nat_degree
- \+ *lemma* polynomial.supp_subset_range_nat_degree_succ

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.map_int_cast
- \+/\- *lemma* polynomial.map_neg
- \+/\- *lemma* polynomial.map_sub



## [2020-10-26 04:25:05](https://github.com/leanprover-community/mathlib/commit/4036212)
feat(algebra/big_operators/nat_antidiagonal): a few more lemmas ([#4783](https://github.com/leanprover-community/mathlib/pull/4783))
#### Estimated changes
Modified src/algebra/big_operators/nat_antidiagonal.lean
- \+ *lemma* finset.nat.prod_antidiagonal_subst
- \+ *lemma* finset.nat.prod_antidiagonal_succ'
- \+ *lemma* finset.nat.prod_antidiagonal_succ
- \+ *lemma* finset.nat.prod_antidiagonal_swap
- \+ *lemma* finset.nat.sum_antidiagonal_succ'
- \+/\- *lemma* finset.nat.sum_antidiagonal_succ



## [2020-10-25 21:53:20](https://github.com/leanprover-community/mathlib/commit/a9d3ce8)
feat(analysis/normed_space/add_torsor): continuity of `vadd`/`vsub` ([#4751](https://github.com/leanprover-community/mathlib/pull/4751))
Prove that `vadd`/`vsub` are Lipschitz continuous, hence uniform
continuous and continuous.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* vadd_eq_vadd_iff_neg_add_eq_vsub
- \+ *lemma* vadd_eq_vadd_iff_sub_eq_vsub
- \+ *lemma* vsub_sub_vsub_comm

Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* continuous.vadd
- \+ *lemma* continuous.vsub
- \+ *lemma* continuous_at.vadd
- \+ *lemma* continuous_at.vsub
- \+ *lemma* continuous_vadd
- \+ *lemma* continuous_vsub
- \+ *lemma* continuous_within_at.vadd
- \+ *lemma* continuous_within_at.vsub
- \+ *lemma* dist_vadd_vadd_le
- \+ *lemma* dist_vsub_cancel_left
- \+ *lemma* dist_vsub_cancel_right
- \+ *lemma* dist_vsub_vsub_le
- \+ *lemma* edist_vadd_vadd_le
- \+ *lemma* edist_vsub_vsub_le
- \+ *lemma* filter.tendsto.vadd
- \+ *lemma* filter.tendsto.vsub
- \+ *lemma* lipschitz_with.vadd
- \+ *lemma* lipschitz_with.vsub
- \+/\- *def* metric_space_of_normed_group_of_add_torsor
- \+ *lemma* nndist_vadd_vadd_le
- \+ *lemma* nndist_vsub_vsub_le
- \+ *lemma* uniform_continuous_vadd
- \+ *lemma* uniform_continuous_vsub

Modified src/analysis/normed_space/basic.lean




## [2020-10-25 18:29:34](https://github.com/leanprover-community/mathlib/commit/e7a4b12)
fix(tactic/core): fix infinite loop in emit_code_here ([#4746](https://github.com/leanprover-community/mathlib/pull/4746))
Previously `emit_code_here "\n"` would go into an infinite loop because the `command_like` parser consumes nothing, but the string is not yet empty. Now we recurse on the length of the string to ensure termination.
#### Estimated changes
Modified src/tactic/core.lean


Modified test/run_parser.lean




## [2020-10-25 16:45:20](https://github.com/leanprover-community/mathlib/commit/151f0dd)
chore(linear_algebra/tensor_product): missing simp lemmas ([#4769](https://github.com/leanprover-community/mathlib/pull/4769))
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+ *theorem* tensor_product.assoc_symm_tmul
- \+ *theorem* tensor_product.comm_symm_tmul
- \+ *theorem* tensor_product.congr_symm_tmul
- \+ *lemma* tensor_product.lid_symm_apply
- \+ *lemma* tensor_product.lift_comp_map
- \+ *lemma* tensor_product.map_comp
- \+ *lemma* tensor_product.rid_symm_apply



## [2020-10-25 16:45:18](https://github.com/leanprover-community/mathlib/commit/69f550c)
chore(ring_theory/unique_factorization_domain): fix some lemma names ([#4765](https://github.com/leanprover-community/mathlib/pull/4765))
Fixes names of some lemmas that were erroneously renamed with find-and-replace
Changes some constructor names to use dot notation
Names replaced:
`exists_prime_of_factor` -> `exists_prime_factors`
`wf_dvd_monoid_of_exists_prime_of_factor` -> `wf_dvd_monoid.of_exists_prime_factors`
`irreducible_iff_prime_of_exists_prime_of_factor` -> `irreducible_iff_prime_of_exists_prime_factors`
`unique_factorization_monoid_of_exists_prime_of_factor` -> `unique_factorization_monoid.of_exists_prime_factors`
`unique_factorization_monoid_iff_exists_prime_of_factor` -> `unique_factorization_monoid.iff_exists_prime_factors`
`irreducible_iff_prime_of_exists_unique_irreducible_of_factor` -> `irreducible_iff_prime_of_exists_unique_irreducible_factors`
`unique_factorization_monoid.of_exists_unique_irreducible_of_factor` -> `unique_factorization_monoid.of_exists_unique_irreducible_factors`
`no_factors_of_no_prime_of_factor` -> `no_factors_of_no_prime_factors`
`dvd_of_dvd_mul_left_of_no_prime_of_factor` -> `dvd_of_dvd_mul_left_of_no_prime_factors`
`dvd_of_dvd_mul_right_of_no_prime_of_factor` -> `dvd_of_dvd_mul_right_of_no_prime_factors`
#### Estimated changes
Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* irreducible_iff_prime_of_exists_prime_factors
- \- *lemma* irreducible_iff_prime_of_exists_prime_of_factor
- \+ *theorem* irreducible_iff_prime_of_exists_unique_irreducible_factors
- \- *theorem* irreducible_iff_prime_of_exists_unique_irreducible_of_factor
- \+ *lemma* unique_factorization_monoid.dvd_of_dvd_mul_left_of_no_prime_factors
- \- *lemma* unique_factorization_monoid.dvd_of_dvd_mul_left_of_no_prime_of_factor
- \+ *lemma* unique_factorization_monoid.dvd_of_dvd_mul_right_of_no_prime_factors
- \- *lemma* unique_factorization_monoid.dvd_of_dvd_mul_right_of_no_prime_of_factor
- \+ *theorem* unique_factorization_monoid.exists_prime_factors
- \- *theorem* unique_factorization_monoid.exists_prime_of_factor
- \+ *theorem* unique_factorization_monoid.iff_exists_prime_factors
- \+ *lemma* unique_factorization_monoid.no_factors_of_no_prime_factors
- \- *lemma* unique_factorization_monoid.no_factors_of_no_prime_of_factor
- \+ *theorem* unique_factorization_monoid.of_exists_prime_factors
- \+ *theorem* unique_factorization_monoid.of_exists_unique_irreducible_factors
- \- *theorem* unique_factorization_monoid.of_exists_unique_irreducible_of_factor
- \- *theorem* unique_factorization_monoid_iff_exists_prime_of_factor
- \- *theorem* unique_factorization_monoid_of_exists_prime_of_factor
- \+ *lemma* wf_dvd_monoid.of_exists_prime_factors
- \- *lemma* wf_dvd_monoid_of_exists_prime_of_factor



## [2020-10-25 14:56:50](https://github.com/leanprover-community/mathlib/commit/14cff9a)
chore(algebra/group/pi): add `pi.has_div` ([#4776](https://github.com/leanprover-community/mathlib/pull/4776))
Motivated by [#4646](https://github.com/leanprover-community/mathlib/pull/4646)
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+ *lemma* pi.div_apply



## [2020-10-24 22:07:59](https://github.com/leanprover-community/mathlib/commit/f056468)
chore(analysis/normed_space): add 2 `@[simp]` attrs ([#4775](https://github.com/leanprover-community/mathlib/pull/4775))
Add `@[simp]` to `norm_pos_iff` and `norm_le_zero_iff`
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* norm_pos_iff

Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/units.lean


Modified src/data/padics/hensel.lean




## [2020-10-24 11:48:11](https://github.com/leanprover-community/mathlib/commit/cae77dc)
feat(algebra/direct_sum): Fix two todos about generalizing over unique types ([#4764](https://github.com/leanprover-community/mathlib/pull/4764))
Also promotes `id` to a `≃+`, and prefers coercion over direct use of `subtype.val`.
#### Estimated changes
Modified src/algebra/direct_sum.lean


Modified src/data/dfinsupp.lean
- \+ *lemma* dfinsupp.single_injective

Modified src/linear_algebra/direct_sum_module.lean




## [2020-10-24 05:36:36](https://github.com/leanprover-community/mathlib/commit/de6a9d4)
feat(ring_theory/polynomial/content): `gcd_monoid` instance on polynomials over gcd domain ([#4760](https://github.com/leanprover-community/mathlib/pull/4760))
Refactors `ring_theory/polynomial/content` a bit to introduce `prim_part`
Provides a `gcd_monoid` instance on polynomials over a gcd domain
#### Estimated changes
Added src/data/polynomial/cancel_leads.lean
- \+ *def* polynomial.cancel_leads
- \+ *lemma* polynomial.dvd_cancel_leads_of_dvd_of_dvd
- \+ *lemma* polynomial.nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree
- \+ *lemma* polynomial.neg_cancel_leads

Modified src/ring_theory/polynomial/content.lean
- \+ *lemma* polynomial.content_prim_part
- \+ *lemma* polynomial.dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part
- \+ *lemma* polynomial.eq_C_content_mul_prim_part
- \- *lemma* polynomial.eq_C_mul_primitive
- \+ *theorem* polynomial.exists_primitive_lcm_of_is_primitive
- \+ *lemma* polynomial.is_primitive.dvd_prim_part_iff_dvd
- \+ *theorem* polynomial.is_primitive.mul
- \+ *lemma* polynomial.is_primitive.prim_part_eq
- \+ *lemma* polynomial.is_primitive_prim_part
- \+ *lemma* polynomial.is_unit_prim_part_C
- \+ *lemma* polynomial.nat_degree_prim_part
- \+ *def* polynomial.prim_part
- \+ *lemma* polynomial.prim_part_dvd
- \+ *theorem* polynomial.prim_part_mul
- \+ *lemma* polynomial.prim_part_ne_zero
- \+ *lemma* polynomial.prim_part_zero



## [2020-10-24 05:36:34](https://github.com/leanprover-community/mathlib/commit/570c293)
feat(data/polynomial/ring_division): Two easy lemmas about polynomials ([#4742](https://github.com/leanprover-community/mathlib/pull/4742))
Two easy lemmas from my previous, now splitted, PR.
#### Estimated changes
Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.monic_X_pow_sub_C

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.leading_coeff_div_by_monic_of_monic



## [2020-10-24 05:36:32](https://github.com/leanprover-community/mathlib/commit/b9a94d6)
feat(linear_algebra/nonsingular_inverse): add stronger form of Cramer's rule ([#4737](https://github.com/leanprover-community/mathlib/pull/4737))
Also renaming `cramer_transpose_eq_adjugate_mul_vec` --> `cramer_eq_adjugate_mul_vec` after the transpose was rendered redundant.
#### Estimated changes
Modified docs/100.yaml


Modified src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* matrix.cramer_eq_adjugate_mul_vec
- \- *lemma* matrix.cramer_transpose_eq_adjugate_mul_vec
- \- *lemma* matrix.cramers_rule
- \+ *lemma* matrix.det_smul_inv_mul_vec_eq_cramer
- \+ *lemma* matrix.mul_vec_cramer



## [2020-10-24 03:10:11](https://github.com/leanprover-community/mathlib/commit/2987a49)
fix(tactic/core): use eval_pexpr in run_parser_cmd ([#4761](https://github.com/leanprover-community/mathlib/pull/4761))
Continuation of [#4745](https://github.com/leanprover-community/mathlib/pull/4745), see https://github.com/leanprover-community/mathlib/pull/4745#discussion_r510771137
#### Estimated changes
Modified src/tactic/core.lean




## [2020-10-24 01:02:28](https://github.com/leanprover-community/mathlib/commit/8255507)
feat(data/pnat/basic): Add strong induction on pnat ([#4736](https://github.com/leanprover-community/mathlib/pull/4736))
I added strong induction on `pnat`. (This was from a previous PR that I am splitting.)
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.case_strong_induction_on
- \+ *lemma* pnat.exists_eq_succ_of_ne_one
- \+ *lemma* pnat.strong_induction_on



## [2020-10-23 22:12:51](https://github.com/leanprover-community/mathlib/commit/c141eed)
feat(data/list/basic): Add prod_reverse_noncomm ([#4757](https://github.com/leanprover-community/mathlib/pull/4757))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.prod_reverse_noncomm



## [2020-10-23 22:12:50](https://github.com/leanprover-community/mathlib/commit/4ec88db)
feat(algebra/direct_sum): Bundle the homomorphisms ([#4754](https://github.com/leanprover-community/mathlib/pull/4754))
#### Estimated changes
Modified src/algebra/direct_sum.lean
- \+/\- *def* direct_sum.mk
- \- *lemma* direct_sum.mk_add
- \- *lemma* direct_sum.mk_neg
- \- *lemma* direct_sum.mk_sub
- \- *lemma* direct_sum.mk_zero
- \+/\- *def* direct_sum.of
- \- *lemma* direct_sum.of_add
- \- *lemma* direct_sum.of_neg
- \- *lemma* direct_sum.of_sub
- \- *lemma* direct_sum.of_zero
- \+/\- *def* direct_sum.to_group
- \- *lemma* direct_sum.to_group_add
- \- *lemma* direct_sum.to_group_neg
- \- *lemma* direct_sum.to_group_sub
- \- *lemma* direct_sum.to_group_zero

Modified src/linear_algebra/direct_sum/finsupp.lean


Modified src/linear_algebra/direct_sum_module.lean




## [2020-10-23 22:12:48](https://github.com/leanprover-community/mathlib/commit/aa59039)
feat(category_theory): presheaf is colimit of representables ([#4401](https://github.com/leanprover-community/mathlib/pull/4401))
Show every presheaf (on a small category) is a colimit of representables, and some related results. 
Suggestions for better names more than welcome.
#### Estimated changes
Modified docs/references.bib


Modified src/category_theory/adjunction/default.lean


Modified src/category_theory/adjunction/opposites.lean
- \+ *def* adjunction.nat_iso_of_left_adjoint_nat_iso
- \+ *def* adjunction.nat_iso_of_right_adjoint_nat_iso

Added src/category_theory/limits/presheaf.lean
- \+ *def* category_theory.cocone_of_representable
- \+ *lemma* category_theory.cocone_of_representable_X
- \+ *def* category_theory.colimit_adj.elements.initial
- \+ *def* category_theory.colimit_adj.extend_along_yoneda
- \+ *lemma* category_theory.colimit_adj.extend_along_yoneda_obj
- \+ *def* category_theory.colimit_adj.is_extension_along_yoneda
- \+ *def* category_theory.colimit_adj.is_initial
- \+ *def* category_theory.colimit_adj.restrict_yoneda_hom_equiv
- \+ *lemma* category_theory.colimit_adj.restrict_yoneda_hom_equiv_natural
- \+ *def* category_theory.colimit_adj.restricted_yoneda
- \+ *def* category_theory.colimit_adj.restricted_yoneda_yoneda
- \+ *def* category_theory.colimit_adj.yoneda_adjunction
- \+ *def* category_theory.colimit_of_representable
- \+ *def* category_theory.extend_along_yoneda_yoneda
- \+ *def* category_theory.functor_to_representables

Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* category_theory.limits.initial_op_of_terminal
- \+ *def* category_theory.limits.initial_unop_of_terminal
- \+ *def* category_theory.limits.terminal_op_of_initial
- \+ *def* category_theory.limits.terminal_unop_of_initial



## [2020-10-23 20:04:40](https://github.com/leanprover-community/mathlib/commit/5afeb9b)
chore(*): a few more type-specific ext lemmas ([#4741](https://github.com/leanprover-community/mathlib/pull/4741))
* mark lemmas about homs from `multiplicative nat` and `multiplicative int` as `@[ext]`;
* add a special case lemma about linear maps from the base semiring;
* ext lemmas for ring homs from `(add_)monoid_algebra`;
* ext lemmas for multiplicative homs from `multiplicative (α →₀ M)`;
* make sure that Lean can chain ext lemmas by using hom equalities in lemmas about `finsupp`/`(add_)monoid_algebra`.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* monoid_hom.ext_mint
- \+/\- *lemma* monoid_hom.ext_mnat

Modified src/algebra/module/basic.lean
- \+ *theorem* linear_map.ext_ring

Modified src/algebra/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.alg_hom_ext'
- \+/\- *lemma* add_monoid_algebra.alg_hom_ext
- \+ *lemma* add_monoid_algebra.ring_hom_ext'
- \+ *lemma* add_monoid_algebra.ring_hom_ext
- \+ *lemma* monoid_algebra.alg_hom_ext'
- \+/\- *lemma* monoid_algebra.alg_hom_ext
- \+ *lemma* monoid_algebra.ring_hom_ext'
- \+ *lemma* monoid_algebra.ring_hom_ext

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.add_hom_ext'
- \+/\- *lemma* finsupp.add_hom_ext
- \- *lemma* finsupp.lhom_ext'
- \- *lemma* finsupp.lhom_ext
- \+ *lemma* finsupp.mul_hom_ext'
- \+ *lemma* finsupp.mul_hom_ext

Modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* mv_polynomial.ring_hom_ext

Modified src/linear_algebra/finsupp.lean
- \+ *lemma* finsupp.lhom_ext'
- \+ *lemma* finsupp.lhom_ext

Modified src/linear_algebra/matrix.lean




## [2020-10-23 17:42:40](https://github.com/leanprover-community/mathlib/commit/0bbf3e2)
fix(deprecated/group): Correct the name of `is_add_group_hom has_neg.neg` ([#4755](https://github.com/leanprover-community/mathlib/pull/4755))
Rename `inv.is_add_group_hom` to `neg.is_add_group_hom`.
#### Estimated changes
Modified src/deprecated/group.lean




## [2020-10-23 13:03:43](https://github.com/leanprover-community/mathlib/commit/5886961)
feat(data/{nat,list}/basic): Add some trivial lemmas ([#4738](https://github.com/leanprover-community/mathlib/pull/4738))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.prod_inv
- \+ *lemma* list.prod_inv_reverse

Modified src/data/nat/basic.lean




## [2020-10-23 10:15:32](https://github.com/leanprover-community/mathlib/commit/b651c6f)
feat(tactic/core): add `run_parser` user command ([#4745](https://github.com/leanprover-community/mathlib/pull/4745))
Allows for writing things like:
```lean
import tactic.core
run_parser emit_code_here "def foo := 1"
```
Relevant Zulip conversation: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/universes/near/214229509
#### Estimated changes
Modified src/tactic/core.lean


Added test/run_parser.lean




## [2020-10-23 10:15:30](https://github.com/leanprover-community/mathlib/commit/fb4aee0)
fix(deprecated/*): remove instances ([#4735](https://github.com/leanprover-community/mathlib/pull/4735))
Remove all instances constructing structures from `is_*` predicates, like for example:
```lean
instance subset.ring {S : set R} [is_subring S] : ring S :=
...
```
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* algebra.of_is_subring

Modified src/algebra/group_action_hom.lean


Modified src/algebra/group_ring_action.lean


Modified src/deprecated/subfield.lean


Modified src/deprecated/subgroup.lean
- \+ *def* subtype.comm_group
- \+ *def* subtype.group

Modified src/deprecated/submonoid.lean
- \+ *def* subtype.comm_monoid
- \+ *def* subtype.monoid

Modified src/deprecated/subring.lean
- \+ *def* subring.domain
- \+ *def* subset.comm_ring
- \+ *def* subset.ring
- \+ *def* subtype.comm_ring
- \+ *def* subtype.ring

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial/basic.lean


Added test/import_order_timeout.lean
- \+ *lemma* foo
- \+ *lemma* injective_iff



## [2020-10-23 10:15:28](https://github.com/leanprover-community/mathlib/commit/70b14ce)
refactor(*): use is_scalar_tower instead of restrict_scalars ([#4733](https://github.com/leanprover-community/mathlib/pull/4733))
- rename `semimodule.restrict_scalars` to `restrict_scalars`
- rename `restrict_scalars` to `subspace.restrict_scalars`
- use `is_scalar_tower` wherever possible
- add warnings to docstrings about `restrict_scalars` to encourage `is_scalar_tower` instead
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *def* algebra.restrict_scalars_equiv
- \- *lemma* algebra.restrict_scalars_equiv_apply
- \- *lemma* algebra.restrict_scalars_equiv_symm_apply
- \+ *lemma* algebra_map_smul
- \+ *lemma* linear_map.algebra_module.smul_apply
- \+ *lemma* linear_map.coe_coe_is_scalar_tower
- \+/\- *lemma* linear_map.coe_restrict_scalars_eq_coe
- \+ *lemma* linear_map.ker_restrict_scalars
- \+/\- *def* linear_map.lto_fun
- \+/\- *def* linear_map.restrict_scalars
- \+ *def* linear_map.smul_algebra_right
- \+ *theorem* linear_map.smul_algebra_right_apply
- \+ *lemma* linear_map.smul_apply'
- \- *def* linear_map_algebra_has_scalar
- \- *lemma* linear_map_algebra_module.smul_apply
- \- *def* linear_map_algebra_module
- \+ *def* restrict_scalars
- \- *lemma* restrict_scalars_ker
- \+ *lemma* restrict_scalars_smul_def
- \- *def* semimodule.restrict_scalars'
- \- *def* semimodule.restrict_scalars
- \- *lemma* semimodule.restrict_scalars_smul_def
- \- *def* smul_algebra_right
- \- *theorem* smul_algebra_right_apply
- \+/\- *def* submodule.restrict_scalars
- \+/\- *lemma* submodule.restrict_scalars_bot
- \+ *lemma* submodule.restrict_scalars_inj
- \+ *lemma* submodule.restrict_scalars_injective
- \+/\- *lemma* submodule.restrict_scalars_mem
- \+/\- *lemma* submodule.restrict_scalars_top

Modified src/algebra/monoid_algebra.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/basic.lean


Modified src/analysis/normed_space/basic.lean
- \- *def* normed_space.restrict_scalars'
- \+ *def* normed_space.restrict_scalars

Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/inner_product.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *def* continuous_linear_map.smul_algebra_right
- \+/\- *theorem* continuous_linear_map.smul_algebra_right_apply

Modified src/data/complex/is_R_or_C.lean


Modified src/data/complex/module.lean


Modified src/field_theory/tower.lean


Modified src/representation_theory/maschke.lean
- \- *def* conjugate
- \- *lemma* conjugate_i
- \- *def* equivariant_projection
- \- *lemma* equivariant_projection_condition
- \+ *def* linear_map.conjugate
- \+ *lemma* linear_map.conjugate_i
- \+ *def* linear_map.equivariant_projection
- \+ *lemma* linear_map.equivariant_projection_condition
- \+ *def* linear_map.sum_of_conjugates
- \+ *def* linear_map.sum_of_conjugates_equivariant
- \- *def* sum_of_conjugates
- \- *def* sum_of_conjugates_equivariant

Modified src/ring_theory/algebra_tower.lean
- \- *def* submodule.restrict_scalars'
- \- *theorem* submodule.restrict_scalars'_inj
- \- *theorem* submodule.restrict_scalars'_injective
- \- *theorem* submodule.restrict_scalars'_top



## [2020-10-23 10:15:26](https://github.com/leanprover-community/mathlib/commit/82b4843)
feat(ring_theory/roots_of_unity): Roots of unity as union of primitive roots ([#4644](https://github.com/leanprover-community/mathlib/pull/4644))
I have added some lemmas about roots of unity, especially `root_of_unity_eq_uniun_prim` that says that, if there is a primitive `n`-th root of unity in `R`, then the set of `n`-th roots of unity is equal to the union of `primitive_roots i R` for `i | n`.
I will use this lemma in to develop the theory of cyclotomic polynomials.
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+ *lemma* pnat.pos_of_div_pos

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.mem_nth_roots_finset
- \+ *def* polynomial.nth_roots_finset

Modified src/number_theory/divisors.lean
- \+ *lemma* nat.filter_dvd_eq_divisors

Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* is_primitive_root.card_nth_roots
- \+ *lemma* is_primitive_root.card_nth_roots_finset
- \+ *lemma* is_primitive_root.disjoint
- \+ *lemma* is_primitive_root.nth_roots_nodup
- \+ *lemma* is_primitive_root.nth_roots_one_eq_bind_primitive_roots
- \+ *lemma* is_primitive_root.pow



## [2020-10-23 10:15:24](https://github.com/leanprover-community/mathlib/commit/278a14b)
feat(analysis/p_series): prove the p-series convergence test ([#4360](https://github.com/leanprover-community/mathlib/pull/4360))
#### Estimated changes
Modified docs/100.yaml


Added src/analysis/p_series.lean
- \+ *lemma* ennreal.le_tsum_condensed
- \+ *lemma* ennreal.tsum_condensed_le
- \+ *lemma* finset.le_sum_condensed'
- \+ *lemma* finset.le_sum_condensed
- \+ *lemma* finset.sum_condensed_le'
- \+ *lemma* finset.sum_condensed_le
- \+ *lemma* nnreal.summable_condensed_iff
- \+ *lemma* nnreal.summable_one_div_rpow
- \+ *lemma* nnreal.summable_one_rpow_inv
- \+ *lemma* real.not_summable_nat_cast_inv
- \+ *lemma* real.not_summable_one_div_nat_cast
- \+ *lemma* real.summable_nat_pow_inv
- \+ *lemma* real.summable_nat_rpow_inv
- \+ *lemma* real.summable_one_div_nat_pow
- \+ *lemma* real.summable_one_div_nat_rpow
- \+ *lemma* real.tendsto_sum_range_one_div_nat_succ_at_top
- \+ *lemma* summable_condensed_iff_of_nonneg

Modified src/analysis/specific_limits.lean
- \- *lemma* half_le_harmonic_double_sub_harmonic
- \- *def* harmonic_series
- \- *theorem* harmonic_tendsto_at_top
- \- *lemma* mono_harmonic
- \- *lemma* self_div_two_le_harmonic_two_pow

Modified src/order/filter/cofinite.lean
- \+ *lemma* filter.eventually_cofinite_ne



## [2020-10-23 10:15:21](https://github.com/leanprover-community/mathlib/commit/04b5572)
feat(ring_theory/witt_vector/defs): type of witt vectors + ring operations ([#4332](https://github.com/leanprover-community/mathlib/pull/4332))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/ring_theory/witt_vector/defs.lean
- \+ *lemma* witt_vector.add_coeff
- \+ *def* witt_vector.coeff
- \+ *lemma* witt_vector.coeff_mk
- \+ *def* witt_vector.eval
- \+ *lemma* witt_vector.ext
- \+ *lemma* witt_vector.ext_iff
- \+ *def* witt_vector.mk
- \+ *lemma* witt_vector.mul_coeff
- \+ *lemma* witt_vector.neg_coeff
- \+ *lemma* witt_vector.one_coeff_eq_of_pos
- \+ *lemma* witt_vector.one_coeff_zero
- \+ *def* witt_vector.peval
- \+ *lemma* witt_vector.zero_coeff
- \+ *def* witt_vector



## [2020-10-23 07:42:45](https://github.com/leanprover-community/mathlib/commit/9e4ef85)
feat(linear_algebra/affine_space): define `affine_equiv.mk'` ([#4750](https://github.com/leanprover-community/mathlib/pull/4750))
Similarly to `affine_map.mk'`, this constructor checks that the map
agrees with its linear part only for one base point.
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* affine_equiv.coe_mk'
- \+ *lemma* affine_equiv.linear_mk'
- \+ *def* affine_equiv.mk'
- \+ *lemma* affine_equiv.to_equiv_mk'



## [2020-10-23 07:42:43](https://github.com/leanprover-community/mathlib/commit/468c01c)
chore(topology/*): add two missing simp coe lemmas ([#4748](https://github.com/leanprover-community/mathlib/pull/4748))
#### Estimated changes
Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_equiv.coe_to_linear_equiv

Modified src/topology/metric_space/isometry.lean
- \+ *lemma* isometric.coe_to_equiv



## [2020-10-23 07:42:40](https://github.com/leanprover-community/mathlib/commit/458c833)
chore(algebra/group/basic): Mark inv_involutive simp ([#4744](https://github.com/leanprover-community/mathlib/pull/4744))
This means expressions like `has_inv.inv ∘ has_inv.inv` can be simplified
#### Estimated changes
Modified src/algebra/group/basic.lean




## [2020-10-23 05:47:36](https://github.com/leanprover-community/mathlib/commit/bb52355)
feat(linear_algebra/basic): define `linear_equiv.neg` ([#4749](https://github.com/leanprover-community/mathlib/pull/4749))
Also weaken requirements for `has_neg (M →ₗ[R] M₂)` from
`[add_comm_group M]` `[add_comm_group M₂]` to `[add_comm_monoid M]`
`[add_comm_group M₂]`.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_equiv.coe_neg
- \+ *def* linear_equiv.neg
- \+ *lemma* linear_equiv.neg_apply
- \+ *lemma* linear_equiv.symm_neg



## [2020-10-23 05:47:34](https://github.com/leanprover-community/mathlib/commit/dc4ad81)
refactor(*): lmul is an algebra hom ([#4724](https://github.com/leanprover-community/mathlib/pull/4724))
also, make some arguments implicit, and add simp lemmas
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* algebra.lmul'_apply
- \+/\- *def* algebra.lmul
- \+/\- *lemma* algebra.lmul_left_apply
- \+ *lemma* algebra.lmul_left_mul
- \+ *lemma* algebra.lmul_left_one
- \+/\- *lemma* algebra.lmul_right_apply
- \+ *lemma* algebra.lmul_right_mul
- \+ *lemma* algebra.lmul_right_one
- \+/\- *lemma* module.algebra_map_End_apply
- \+/\- *lemma* module.algebra_map_End_eq_smul_id
- \+/\- *lemma* module.ker_algebra_map_End

Modified src/algebra/algebra/operations.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_map.mul_apply

Modified src/linear_algebra/finite_dimensional.lean




## [2020-10-23 05:47:32](https://github.com/leanprover-community/mathlib/commit/ff711a3)
feat(measure_theory/measure_space): Added lemmas for commuting restrict for outer measures and measures ([#4673](https://github.com/leanprover-community/mathlib/pull/4673))
This also adds `of_function_apply` and `Inf_apply` (for `outer_measure`). I had some difficulty getting
these functions to expand (as represented by the length of `Inf_apply`) in a clean way.
I also think `Inf_apply` is instructive in terms of making it clear what the definition of `Inf` is. Once `Inf` is rewritten,
then the large set of operations available for `infi_le` and `le_infi` (and `ennreal.tsum_le_tsum`) can be used.
`measure.restrict_Inf_eq_Inf_restrict` will be helpful in getting more results about the subtraction of measures,
specifically writing down the result of `(a - b)` when `a` is not less than or equal to `b` and `b` is not less than
or equal to `a`.
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.measure.le_of_add_le_add_left
- \+ *lemma* measure_theory.measure.restrict_Inf_eq_Inf_restrict
- \+ *lemma* measure_theory.measure.restrict_to_outer_measure_eq_to_outer_measure_restrict

Modified src/measure_theory/outer_measure.lean
- \+ *lemma* measure_theory.outer_measure.Inf_apply
- \+/\- *lemma* measure_theory.outer_measure.Inf_gen_nonempty2
- \+ *lemma* measure_theory.outer_measure.of_function_apply
- \+ *lemma* measure_theory.outer_measure.restrict_Inf_eq_Inf_restrict
- \+ *lemma* measure_theory.outer_measure.restrict_trim



## [2020-10-23 04:31:09](https://github.com/leanprover-community/mathlib/commit/f279313)
feat(category_theory/yoneda): better simp lemmas for small yoneda ([#4743](https://github.com/leanprover-community/mathlib/pull/4743))
Gives nicer (d)simp lemmas for yoneda_sections_small.
#### Estimated changes
Modified src/category_theory/yoneda.lean
- \+/\- *def* category_theory.yoneda_sections_small
- \+ *lemma* category_theory.yoneda_sections_small_hom
- \+ *lemma* category_theory.yoneda_sections_small_inv_app_apply



## [2020-10-23 01:10:33](https://github.com/leanprover-community/mathlib/commit/8bd1df5)
chore(scripts): update nolints.txt ([#4747](https://github.com/leanprover-community/mathlib/pull/4747))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-22 17:33:36](https://github.com/leanprover-community/mathlib/commit/de12036)
chore(data/polynomial): remove monomial_one_eq_X_pow ([#4734](https://github.com/leanprover-community/mathlib/pull/4734))
monomial_one_eq_X_pow was a duplicate of X_pow_eq_monomial
#### Estimated changes
Modified src/data/polynomial/coeff.lean


Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/monomial.lean
- \- *lemma* polynomial.monomial_one_eq_X_pow

Modified src/ring_theory/polynomial_algebra.lean




## [2020-10-22 14:57:55](https://github.com/leanprover-community/mathlib/commit/6eb5564)
chore(data/equiv/basic): Add a simp lemma perm.coe_mul ([#4723](https://github.com/leanprover-community/mathlib/pull/4723))
This mirrors `equiv.coe_trans`
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.perm.coe_mul
- \+/\- *theorem* equiv.perm.mul_apply



## [2020-10-22 07:48:25](https://github.com/leanprover-community/mathlib/commit/add5096)
chore(*): 3 unrelated small changes ([#4732](https://github.com/leanprover-community/mathlib/pull/4732))
* fix universe levels in `equiv.set.compl`: by default Lean uses some
`max` universes both for `α` and `β`, and it backfires when one tries
to apply it.
* add `nat.mul_factorial_pred`;
* add instance `fixed_points.decidable`.
Part of [#4731](https://github.com/leanprover-community/mathlib/pull/4731)
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/data/nat/factorial.lean
- \+ *theorem* nat.mul_factorial_pred

Modified src/dynamics/fixed_points/basic.lean




## [2020-10-22 07:48:23](https://github.com/leanprover-community/mathlib/commit/aba31c9)
feat(algebra/monoid_algebra): define a non-commutative version of `lift` ([#4725](https://github.com/leanprover-community/mathlib/pull/4725))
* [X] define `monoid_algebra.lift_c` and `add_monoid_algebra.lift_nc` to be generalizations of `(mv_)polynomial.eval₂` to `(add_)monoid_algebra`s.
* [X] use `to_additive` in many proofs about `add_monoid_algebra`;
* [X] define `finsupp.nontrivial`, use it for `(add_)monoid_algebra.nontrivial`;
* [X] copy more lemmas about `lift` from `monoid_algebra` to `add_monoid_algebra`;
* [X] use `@[ext]` on more powerful type-specific lemmas;
* [x] fix docstrings of `(add_)monoid_algebra.lift₂`;
* [x] fix compile failures.
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/category/CommRing/adjunctions.lean


Modified src/algebra/monoid_algebra.lean
- \+/\- *lemma* add_monoid_algebra.alg_hom_ext
- \+/\- *lemma* add_monoid_algebra.alg_hom_ext_iff
- \+/\- *def* add_monoid_algebra.lift
- \+ *lemma* add_monoid_algebra.lift_apply'
- \+ *lemma* add_monoid_algebra.lift_apply
- \+ *lemma* add_monoid_algebra.lift_def
- \+ *def* add_monoid_algebra.lift_nc
- \+ *lemma* add_monoid_algebra.lift_nc_mul
- \+ *lemma* add_monoid_algebra.lift_nc_one
- \+ *lemma* add_monoid_algebra.lift_nc_single
- \+ *lemma* add_monoid_algebra.lift_of
- \+ *lemma* add_monoid_algebra.lift_single
- \+ *lemma* add_monoid_algebra.lift_symm_apply
- \+ *lemma* add_monoid_algebra.lift_unique'
- \+ *lemma* add_monoid_algebra.lift_unique
- \+/\- *lemma* add_monoid_algebra.of_apply
- \+/\- *lemma* monoid_algebra.alg_hom_ext
- \+ *lemma* monoid_algebra.lift_apply'
- \+ *lemma* monoid_algebra.lift_def
- \+ *def* monoid_algebra.lift_nc
- \+ *lemma* monoid_algebra.lift_nc_mul
- \+ *lemma* monoid_algebra.lift_nc_one
- \+ *lemma* monoid_algebra.lift_nc_single

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.comp_lift_add_hom
- \+ *lemma* finsupp.lift_add_hom_apply_single
- \+ *lemma* finsupp.lift_add_hom_comp_single
- \+ *lemma* finsupp.prod_add_index'
- \+ *lemma* finsupp.sum_add_index'

Modified src/data/mv_polynomial/basic.lean
- \+ *theorem* mv_polynomial.aeval_unique
- \+/\- *lemma* mv_polynomial.alg_hom_ext
- \- *theorem* mv_polynomial.eval_unique
- \+/\- *lemma* mv_polynomial.ring_hom_ext
- \+ *lemma* mv_polynomial.single_eq_monomial

Modified src/data/mv_polynomial/comap.lean


Modified src/data/mv_polynomial/monad.lean
- \+ *lemma* mv_polynomial.bind₁_comp_rename
- \+ *lemma* mv_polynomial.rename_comp_bind₁



## [2020-10-22 07:48:21](https://github.com/leanprover-community/mathlib/commit/fb5ef2b)
feat(linear_algebra/nonsingular_inverse): state Cramer's rule explicitly ([#4700](https://github.com/leanprover-community/mathlib/pull/4700))
Mostly so that we can add an entry to the Freek 100.
#### Estimated changes
Modified docs/100.yaml


Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.smul_mul_vec_assoc

Modified src/linear_algebra/determinant.lean
- \+/\- *lemma* matrix.det_eq_zero_of_column_eq_zero
- \+ *lemma* matrix.det_eq_zero_of_row_eq_zero
- \- *theorem* matrix.det_zero_of_column_eq
- \+ *theorem* matrix.det_zero_of_row_eq

Modified src/linear_algebra/nonsingular_inverse.lean
- \+/\- *def* matrix.adjugate
- \+/\- *def* matrix.cramer
- \+/\- *lemma* matrix.cramer_apply
- \- *lemma* matrix.cramer_column_self
- \+/\- *def* matrix.cramer_map
- \+ *lemma* matrix.cramer_transpose_eq_adjugate_mul_vec
- \+ *lemma* matrix.cramer_transpose_row_self
- \+ *lemma* matrix.cramers_rule



## [2020-10-22 06:38:42](https://github.com/leanprover-community/mathlib/commit/03f0285)
refactor(algebra/add_torsor): define pointwise `-ᵥ` and `+ᵥ` on sets ([#4710](https://github.com/leanprover-community/mathlib/pull/4710))
This seems more natural than `vsub_set` to me.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+ *lemma* set.empty_vsub
- \+ *lemma* set.finite.vadd
- \+ *lemma* set.finite.vsub
- \+ *lemma* set.singleton_vadd
- \+ *lemma* set.singleton_vsub
- \+ *lemma* set.singleton_vsub_self
- \+ *lemma* set.vadd_singleton
- \+ *lemma* set.vadd_subset_vadd
- \+ *lemma* set.vsub_empty
- \+ *lemma* set.vsub_mem_vsub
- \+ *lemma* set.vsub_self_mono
- \+ *lemma* set.vsub_singleton
- \+ *lemma* set.vsub_subset_iff
- \+ *lemma* set.vsub_subset_vsub
- \- *lemma* vsub_mem_vsub_set
- \- *def* vsub_set
- \- *lemma* vsub_set_empty
- \- *lemma* vsub_set_finite_of_finite
- \- *lemma* vsub_set_mono
- \- *lemma* vsub_set_singleton

Modified src/geometry/euclidean/monge_point.lean


Modified src/linear_algebra/affine_space/basic.lean
- \+/\- *def* vector_span
- \+/\- *lemma* vector_span_def
- \+/\- *lemma* vsub_set_subset_vector_span

Modified src/linear_algebra/affine_space/finite_dimensional.lean




## [2020-10-22 05:15:46](https://github.com/leanprover-community/mathlib/commit/4c4d47c)
feat(algebra/gcd_monoid): noncomputably defines `gcd_monoid` structures from partial information ([#4664](https://github.com/leanprover-community/mathlib/pull/4664))
Adds the following 4 noncomputable functions which define `gcd_monoid` instances.
`gcd_monoid_of_gcd` takes as input a `gcd` function and a few of its properties
`gcd_monoid_of_lcm` takes as input a `lcm` function and a few of its properties
`gcd_monoid_of_exists_gcd` takes as input the prop that every two elements have a `gcd`
`gcd_monoid_of_exists_lcm` takes as input the prop that every two elements have an `lcm`
#### Estimated changes
Modified src/algebra/gcd_monoid.lean




## [2020-10-22 01:14:08](https://github.com/leanprover-community/mathlib/commit/fca876e)
chore(scripts): update nolints.txt ([#4730](https://github.com/leanprover-community/mathlib/pull/4730))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-21 15:31:43](https://github.com/leanprover-community/mathlib/commit/df45002)
feat(archive): formalize compiler correctness by McCarthy and Painter ([#4702](https://github.com/leanprover-community/mathlib/pull/4702))
Add a formalization of the correctness of a compiler from arithmetic expressions to machine language described by McCarthy and Painter, which is considered the first proof of compiler correctness.
#### Estimated changes
Added archive/arithcc.lean
- \+ *def* arithcc.compile
- \+ *theorem* arithcc.compiler_correctness
- \+ *inductive* arithcc.expr
- \+ *def* arithcc.identifier
- \+ *inductive* arithcc.instruction
- \+ *def* arithcc.loc
- \+ *def* arithcc.outcome
- \+ *lemma* arithcc.outcome_append
- \+ *def* arithcc.read
- \+ *lemma* arithcc.register.le_of_lt_succ
- \+ *lemma* arithcc.register.lt_succ_self
- \+ *def* arithcc.register
- \+ *structure* arithcc.state
- \+ *def* arithcc.state_eq
- \+ *lemma* arithcc.state_eq_implies_write_eq
- \+ *def* arithcc.state_eq_rs
- \+ *lemma* arithcc.state_eq_rs_implies_write_eq_rs
- \+ *def* arithcc.step
- \+ *def* arithcc.value
- \+ *def* arithcc.word
- \+ *def* arithcc.write
- \+ *lemma* arithcc.write_eq_implies_state_eq



## [2020-10-21 15:31:40](https://github.com/leanprover-community/mathlib/commit/1b4e769)
feat(linear_algebra/affine_space): define `affine_equiv` ([#2909](https://github.com/leanprover-community/mathlib/pull/2909))
Define
* [X] `affine_equiv` to be an invertible affine map (e.g., extend both `affine_map` and `equiv`);
* [X] conversion to `linear_equiv`;
* [X] `group` structure on affine automorphisms;
* [X] prove standard lemmas for equivalences (`apply_symm_apply`, `symm_apply_eq` etc).
API changes
* make `G` implicit in `equiv.vadd_const`.
#### Estimated changes
Modified src/algebra/add_torsor.lean
- \+/\- *lemma* equiv.coe_vadd_const
- \+/\- *lemma* equiv.coe_vadd_const_symm

Modified src/analysis/normed_space/add_torsor.lean
- \+/\- *lemma* isometric.vadd_const_to_equiv

Added src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* affine_equiv.apply_eq_iff_eq
- \+ *lemma* affine_equiv.apply_eq_iff_eq_symm_apply
- \+ *lemma* affine_equiv.apply_symm_apply
- \+ *lemma* affine_equiv.coe_fn_inj
- \+ *lemma* affine_equiv.coe_mul
- \+ *lemma* affine_equiv.coe_one
- \+ *lemma* affine_equiv.coe_refl
- \+ *lemma* affine_equiv.coe_to_affine_map
- \+ *lemma* affine_equiv.coe_to_equiv
- \+ *lemma* affine_equiv.coe_trans
- \+ *def* affine_equiv.const_vadd
- \+ *lemma* affine_equiv.const_vadd_apply
- \+ *lemma* affine_equiv.const_vadd_symm_apply
- \+ *lemma* affine_equiv.ext
- \+ *lemma* affine_equiv.injective_coe_fn
- \+ *lemma* affine_equiv.injective_to_affine_map
- \+ *lemma* affine_equiv.injective_to_equiv
- \+ *lemma* affine_equiv.inv_def
- \+ *lemma* affine_equiv.linear_const_vadd
- \+ *lemma* affine_equiv.linear_refl
- \+ *lemma* affine_equiv.linear_to_affine_map
- \+ *lemma* affine_equiv.linear_vadd_const
- \+ *lemma* affine_equiv.map_vadd
- \+ *lemma* affine_equiv.mul_def
- \+ *lemma* affine_equiv.one_def
- \+ *lemma* affine_equiv.range_eq
- \+ *def* affine_equiv.refl
- \+ *lemma* affine_equiv.refl_apply
- \+ *lemma* affine_equiv.refl_trans
- \+ *def* affine_equiv.symm
- \+ *lemma* affine_equiv.symm_apply_apply
- \+ *lemma* affine_equiv.symm_linear
- \+ *lemma* affine_equiv.symm_refl
- \+ *lemma* affine_equiv.symm_to_equiv
- \+ *lemma* affine_equiv.symm_trans
- \+ *def* affine_equiv.to_affine_map
- \+ *lemma* affine_equiv.to_affine_map_inj
- \+ *lemma* affine_equiv.to_affine_map_mk
- \+ *lemma* affine_equiv.to_equiv_inj
- \+ *lemma* affine_equiv.to_equiv_refl
- \+ *def* affine_equiv.trans
- \+ *lemma* affine_equiv.trans_apply
- \+ *lemma* affine_equiv.trans_assoc
- \+ *lemma* affine_equiv.trans_refl
- \+ *lemma* affine_equiv.trans_symm
- \+ *def* affine_equiv.vadd_const
- \+ *lemma* affine_equiv.vadd_const_apply
- \+ *lemma* affine_equiv.vadd_const_symm_apply
- \+ *structure* affine_equiv
- \+ *lemma* linear_equiv.coe_to_affine_equiv
- \+ *def* linear_equiv.to_affine_equiv



## [2020-10-21 13:35:00](https://github.com/leanprover-community/mathlib/commit/75316ca)
chore(linear_algebra/basic): a few simp lemmas ([#4727](https://github.com/leanprover-community/mathlib/pull/4727))
* add `submodule.nonempty`;
* add `@[simp]` to `submodule.map_id`;
* add `submodule.neg_coe`, `protected submodule.map_neg`, and `submodule.span_neg`.
#### Estimated changes
Modified src/algebra/module/submodule.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* submodule.map_id
- \+ *lemma* submodule.neg_coe
- \+ *lemma* submodule.span_neg



## [2020-10-21 01:39:35](https://github.com/leanprover-community/mathlib/commit/01c1e6f)
chore(scripts): update nolints.txt ([#4721](https://github.com/leanprover-community/mathlib/pull/4721))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-21 01:39:33](https://github.com/leanprover-community/mathlib/commit/3a860cc)
fixup(category_theory/sites): add arrow sets that aren't sieves  ([#4703](https://github.com/leanprover-community/mathlib/pull/4703))
Broken off from [#4648](https://github.com/leanprover-community/mathlib/pull/4648).
- I realised that by creating a type `arrows_with_codomain` I can avoid using `set (over X)` entirely (the bit I was missing was that `derive complete_lattice` works on the new type even though it wasn't inferred on the pi-type), so I changed sieves to use that instead. 
- I added constructors for special arrow sets. The definitions of `singleton_arrow` and `pullback_arrows` look a bit dubious because of the equality and `eq_to_hom` stuff; I don't love that either so if there's a suggestion on how to achieve the same things (in particular stating (1) and (3) from: https://stacks.math.columbia.edu/tag/00VH, as well as a complete lattice structure) I'd be happy to consider.
- I added a coercion so we can write `S f` instead of `S.arrows f` for sieves.
#### Estimated changes
Modified src/category_theory/sites/grothendieck.lean
- \+/\- *lemma* category_theory.grothendieck_topology.arrow_max
- \+ *lemma* category_theory.grothendieck_topology.bind_covering
- \+/\- *lemma* category_theory.grothendieck_topology.dense_covering
- \+ *lemma* category_theory.grothendieck_topology.ext

Modified src/category_theory/sites/sieves.lean
- \+ *def* category_theory.arrows_with_codomain.bind
- \+ *lemma* category_theory.arrows_with_codomain.bind_comp
- \+ *def* category_theory.arrows_with_codomain.singleton_arrow
- \+ *lemma* category_theory.arrows_with_codomain.singleton_arrow_eq_iff_domain
- \+ *lemma* category_theory.arrows_with_codomain.singleton_arrow_self
- \+ *def* category_theory.arrows_with_codomain
- \+ *def* category_theory.sieve.bind
- \+ *lemma* category_theory.sieve.downward_closed
- \+/\- *def* category_theory.sieve.generate
- \- *inductive* category_theory.sieve.generate_sets
- \+/\- *def* category_theory.sieve.gi_generate
- \+/\- *lemma* category_theory.sieve.id_mem_iff_eq_top
- \+ *lemma* category_theory.sieve.le_pullback_bind
- \+ *lemma* category_theory.sieve.mem_generate
- \+/\- *lemma* category_theory.sieve.mem_pushforward_of_comp
- \+/\- *lemma* category_theory.sieve.mem_top
- \+/\- *lemma* category_theory.sieve.pullback_eq_top_iff_mem
- \+/\- *lemma* category_theory.sieve.pullback_eq_top_of_mem
- \+ *lemma* category_theory.sieve.pushforward_le_bind_of_mem
- \- *def* category_theory.sieve.set_over
- \+/\- *lemma* category_theory.sieve.sets_iff_generate



## [2020-10-21 00:42:57](https://github.com/leanprover-community/mathlib/commit/857cbd5)
chore(category_theory/limits/preserves): split up files and remove redundant defs ([#4717](https://github.com/leanprover-community/mathlib/pull/4717))
Broken off from [#4163](https://github.com/leanprover-community/mathlib/pull/4163) and [#4716](https://github.com/leanprover-community/mathlib/pull/4716).
While the diff of this PR is quite big, it actually doesn't do very much: 
- I removed the definitions of `preserves_(co)limits_iso` from `preserves/basic`, since there's already a version in `preserves/shapes` which has lemmas about it. (I didn't keep them in `preserves/basic` since that file is already getting quite big, so I chose to instead put them into the smaller file.
- I split up `preserves/shapes` into two files: `preserves/limits` and `preserves/shapes`. From my other PRs my plan is for `shapes` to contain isomorphisms and constructions for special shapes, eg `fan.mk` and `fork`s, some of which aren't already present, and `limits` to have things for the general case. In this PR I don't change the situation for special shapes (other than simplifying some proofs), other than moving it into a separate file for clarity.
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space/has_colimits.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/preserves/basic.lean
- \- *def* category_theory.limits.preserves_colimit_iso
- \- *def* category_theory.limits.preserves_limit_iso

Added src/category_theory/limits/preserves/limits.lean
- \+ *lemma* lift_comp_preserves_limits_iso_hom
- \+ *def* preserves_colimit_iso
- \+ *lemma* preserves_colimits_iso_inv_comp_desc
- \+ *lemma* preserves_desc_map_cocone
- \+ *lemma* preserves_lift_map_cone
- \+ *def* preserves_limit_iso
- \+ *lemma* preserves_limits_iso_hom_π
- \+ *lemma* preserves_limits_iso_inv_π
- \+ *lemma* ι_preserves_colimits_iso_hom
- \+ *lemma* ι_preserves_colimits_iso_inv

Modified src/category_theory/limits/preserves/shapes.lean
- \- *def* preserves_limits_iso
- \- *lemma* preserves_limits_iso_hom_π



## [2020-10-20 13:15:11](https://github.com/leanprover-community/mathlib/commit/8489972)
feat(data/complex/module): ![1, I] is a basis of C over R ([#4713](https://github.com/leanprover-community/mathlib/pull/4713))
#### Estimated changes
Modified src/data/complex/module.lean
- \+ *lemma* complex.coe_algebra_map
- \+ *lemma* complex.dim_real_complex
- \+ *lemma* complex.findim_real_complex
- \+ *lemma* complex.im_smul
- \+ *lemma* complex.is_basis_one_I
- \+ *lemma* complex.re_smul
- \+ *lemma* complex.{u}
- \+ *lemma* dim_real_of_complex
- \+ *lemma* findim_real_of_complex

Modified src/data/matrix/notation.lean
- \+ *lemma* matrix.range_cons
- \+ *lemma* matrix.range_empty



## [2020-10-20 10:23:27](https://github.com/leanprover-community/mathlib/commit/cf551ee)
chore(*): review some lemmas about injectivity of coercions ([#4711](https://github.com/leanprover-community/mathlib/pull/4711))
API changes:
* rename `linear_map.coe_fn_congr` to `protected
  linear_map.congr_arg`;
* rename `linear_map.lcongr_fun` to `protected linear_map.congr_fun`;
* rename `enorm.coe_fn_injective` to `enorm.injective_coe_fn`, add
  `enorm.coe_inj`;
* rename `equiv.coe_fn_injective` to `equiv.injective_coe_fn`,
  reformulate in terms of `function.injective`;
* add `equiv.coe_inj`;
* add `affine_map.injective_coe_fn`, `protected affine_map.congr_arg`,
  and `protected affine_map.congr_fun`;
* rename `linear_equiv.to_equiv_injective` to
  `linear_equiv.injective_to_equiv`, add `linear_equiv.to_equiv_inj`;
* rename `linear_equiv.eq_of_linear_map_eq` to
  `linear_equiv.injective_to_linear_map`, formulate as `injective
  coe`;
* add `linear_equiv.to_linear_map_inj`;
* rename `outer_measure.coe_fn_injective` to
  `outer_measure.injective_coe_fn`;
* rename `rel_iso.to_equiv_injective` to `rel_iso.injective_to_equiv`;
* rename `rel_iso.coe_fn_injective` to `rel_iso.injective_coe_fn`;
* rename `continuous_linear_map.coe_fn_injective` to
  `injective_coe_fn`.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \- *lemma* linear_map.coe_fn_congr
- \- *lemma* linear_map.lcongr_fun

Modified src/analysis/normed_space/enorm.lean
- \- *lemma* enorm.coe_fn_injective
- \+ *lemma* enorm.coe_inj
- \+ *lemma* enorm.injective_coe_fn

Modified src/analysis/normed_space/operator_norm.lean


Modified src/category_theory/monoidal/internal/Module.lean


Modified src/data/equiv/basic.lean
- \- *theorem* equiv.coe_fn_injective
- \+ *theorem* equiv.injective_coe_fn

Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* affine_map.injective_coe_fn

Modified src/linear_algebra/basic.lean
- \- *lemma* linear_equiv.eq_of_linear_map_eq
- \+ *lemma* linear_equiv.injective_to_equiv
- \+ *lemma* linear_equiv.injective_to_linear_map
- \+/\- *lemma* linear_equiv.refl_trans
- \+ *lemma* linear_equiv.to_equiv_inj
- \- *lemma* linear_equiv.to_equiv_injective
- \+ *lemma* linear_equiv.to_linear_map_inj
- \+/\- *lemma* linear_equiv.trans_refl

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/determinant.lean


Modified src/measure_theory/outer_measure.lean
- \- *lemma* measure_theory.outer_measure.coe_fn_injective
- \+ *lemma* measure_theory.outer_measure.injective_coe_fn

Modified src/order/rel_iso.lean
- \- *theorem* rel_iso.coe_fn_injective
- \+ *theorem* rel_iso.injective_coe_fn
- \+ *theorem* rel_iso.injective_to_equiv
- \- *theorem* rel_iso.to_equiv_injective

Modified src/set_theory/ordinal.lean


Modified src/topology/algebra/module.lean
- \- *theorem* continuous_linear_map.coe_fn_injective
- \+ *theorem* continuous_linear_map.injective_coe_fn



## [2020-10-20 10:23:25](https://github.com/leanprover-community/mathlib/commit/5d52ea4)
chore(.gitignore): gitignore for emacs temp files ([#4699](https://github.com/leanprover-community/mathlib/pull/4699))
Emacs backup files end in `~`, and you don't want them in the repo. Just makes things mildly easier for emacs users if that pattern is in the gitignore.
#### Estimated changes
Modified .gitignore




## [2020-10-20 08:10:53](https://github.com/leanprover-community/mathlib/commit/8131349)
fix(tactic/norm_num): remove one_div from simp set ([#4705](https://github.com/leanprover-community/mathlib/pull/4705))
fixes [#4701](https://github.com/leanprover-community/mathlib/pull/4701)
#### Estimated changes
Modified src/tactic/norm_num.lean


Modified test/norm_num.lean




## [2020-10-20 08:10:51](https://github.com/leanprover-community/mathlib/commit/617e829)
feat(linear_algebra/affine_space/ordered): define `slope` ([#4669](https://github.com/leanprover-community/mathlib/pull/4669))
* Review API of `ordered_semimodule`:
  - replace `lt_of_smul_lt_smul_of_nonneg` with `lt_of_smul_lt_smul_of_pos`;
    it's equivalent but is easier to prove;
  - add more lemmas;
  - add a constructor for the special case of an ordered semimodule over
	a linearly ordered field; in this case it suffices to verify only
	`a < b → 0 < c → c • a ≤ c • b`;
  - use the new constructor in `analysis/convex/cone`;
* Define `units.smul_perm_hom`, reroute `mul_action.to_perm` through it;
* Add a few more lemmas unfolding `affine_map.line_map` in special cases;
* Define `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` and prove a handful
  of monotonicity properties.
#### Estimated changes
Modified src/algebra/module/ordered.lean
- \+ *lemma* eq_of_smul_eq_smul_of_pos_of_le
- \+ *lemma* le_smul_iff_of_pos
- \+ *lemma* lt_of_smul_lt_smul_of_nonneg
- \+ *def* ordered_semimodule.mk''
- \+ *def* ordered_semimodule.mk'
- \+ *lemma* smul_le_iff_of_pos
- \+ *lemma* smul_le_smul_iff_of_neg
- \+ *lemma* smul_le_smul_iff_of_pos
- \+ *lemma* smul_lt_iff_of_pos
- \+ *lemma* smul_lt_smul_iff_of_pos
- \+ *lemma* smul_pos_iff_of_pos

Modified src/analysis/convex/cone.lean


Modified src/group_theory/group_action.lean
- \+ *lemma* is_unit.smul_left_cancel
- \+/\- *def* mul_action.to_perm
- \+ *lemma* units.smul_eq_iff_eq_inv_smul
- \+ *lemma* units.smul_left_cancel
- \+ *def* units.smul_perm_hom

Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* affine_map.fst_line_map
- \+ *lemma* affine_map.line_map_apply_module'
- \+ *lemma* affine_map.line_map_apply_module
- \+ *lemma* affine_map.line_map_apply_one_sub
- \+ *lemma* affine_map.line_map_apply_ring'
- \+ *lemma* affine_map.line_map_apply_ring
- \+ *lemma* affine_map.line_map_same_apply
- \+ *lemma* affine_map.snd_line_map

Added src/linear_algebra/affine_space/ordered.lean
- \+ *lemma* eq_of_slope_eq_zero
- \+ *lemma* left_le_line_map_iff_le
- \+ *lemma* left_lt_line_map_iff_lt
- \+ *lemma* line_map_le_left_iff_le
- \+ *lemma* line_map_le_line_map_iff_of_lt
- \+ *lemma* line_map_le_map_iff_slope_le_slope
- \+ *lemma* line_map_le_map_iff_slope_le_slope_left
- \+ *lemma* line_map_le_map_iff_slope_le_slope_right
- \+ *lemma* line_map_le_right_iff_le
- \+ *lemma* line_map_lt_left_iff_lt
- \+ *lemma* line_map_lt_line_map_iff_of_lt
- \+ *lemma* line_map_lt_map_iff_slope_lt_slope
- \+ *lemma* line_map_lt_map_iff_slope_lt_slope_left
- \+ *lemma* line_map_lt_map_iff_slope_lt_slope_right
- \+ *lemma* line_map_lt_right_iff_lt
- \+ *lemma* line_map_mono_endpoints
- \+ *lemma* line_map_mono_left
- \+ *lemma* line_map_mono_right
- \+ *lemma* line_map_slope_line_map_slope_line_map
- \+ *lemma* line_map_slope_slope_sub_div_sub
- \+ *lemma* line_map_strict_mono_endpoints
- \+ *lemma* line_map_strict_mono_left
- \+ *lemma* line_map_strict_mono_right
- \+ *lemma* map_le_line_map_iff_slope_le_slope
- \+ *lemma* map_le_line_map_iff_slope_le_slope_left
- \+ *lemma* map_le_line_map_iff_slope_le_slope_right
- \+ *lemma* map_lt_line_map_iff_slope_lt_slope
- \+ *lemma* map_lt_line_map_iff_slope_lt_slope_left
- \+ *lemma* map_lt_line_map_iff_slope_lt_slope_right
- \+ *lemma* right_le_line_map_iff_le
- \+ *lemma* right_lt_line_map_iff_lt
- \+ *def* slope
- \+ *lemma* slope_comm
- \+ *lemma* slope_def_field
- \+ *lemma* slope_same
- \+ *lemma* sub_div_sub_smul_slope_add_sub_div_sub_smul_slope



## [2020-10-20 05:38:10](https://github.com/leanprover-community/mathlib/commit/b46190f)
chore(data/finsupp): minor review ([#4712](https://github.com/leanprover-community/mathlib/pull/4712))
* add a few lemmas about injectivity of `coe_fn` etc;
* simplify definition of `finsupp.on_finset`;
* replace the proof of `support_on_finset` by `rfl`;
* make `finsupp.mem_support_on_finset` a `simp` lemma.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.coe_mk
- \+ *lemma* finsupp.coe_zero
- \+/\- *lemma* finsupp.ext
- \+ *lemma* finsupp.ext_iff'
- \+ *lemma* finsupp.injective_coe_fn
- \+/\- *lemma* finsupp.mem_support_on_finset
- \+/\- *lemma* finsupp.zero_apply

Modified src/linear_algebra/basis.lean




## [2020-10-20 05:38:08](https://github.com/leanprover-community/mathlib/commit/288802b)
chore(data/polynomial): slightly generalize `map_eq_zero` and `map_ne_zero` ([#4708](https://github.com/leanprover-community/mathlib/pull/4708))
We don't need the codomain to be a field.
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* polynomial.map_eq_zero
- \+/\- *lemma* polynomial.map_ne_zero



## [2020-10-20 05:38:07](https://github.com/leanprover-community/mathlib/commit/21415c8)
chore(topology/algebra/ordered): drop section vars, golf 2 proofs ([#4706](https://github.com/leanprover-community/mathlib/pull/4706))
* Explicitly specify explicit arguments instead of using section
  variables;
* Add `continuous_min` and `continuous_max`;
* Use them for `tendsto.min` and `tendsto.max`
#### Estimated changes
Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* continuous.max
- \+/\- *lemma* continuous.min
- \+ *lemma* continuous_max
- \+ *lemma* continuous_min
- \+/\- *lemma* frontier_le_subset_eq
- \+/\- *lemma* frontier_lt_subset_eq



## [2020-10-20 05:38:04](https://github.com/leanprover-community/mathlib/commit/0cf8a98)
chore(data/set): a few more lemmas about `image2` ([#4695](https://github.com/leanprover-community/mathlib/pull/4695))
Also add `@[simp]` to `set.image2_singleton_left` and `set.image2_singleton_rigt`.
#### Estimated changes
Modified src/algebra/pointwise.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.exists_prod_set
- \+ *lemma* set.forall_image2_iff
- \+ *lemma* set.image2_assoc
- \+/\- *lemma* set.image2_singleton
- \+/\- *lemma* set.image2_singleton_left
- \+/\- *lemma* set.image2_singleton_right
- \+ *lemma* set.image2_subset_iff



## [2020-10-20 05:38:01](https://github.com/leanprover-community/mathlib/commit/050b5a1)
feat(data/real/pi): Leibniz's series for pi ([#4228](https://github.com/leanprover-community/mathlib/pull/4228))
Freek No. 26 
<!-- put comments you want to keep out of the PR commit here -->
#### Estimated changes
Modified docs/100.yaml


Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.tendsto_div_pow_mul_exp_add_at_top
- \+ *lemma* real.tendsto_exp_nhds_0_nhds_1
- \+ *lemma* real.tendsto_mul_exp_add_div_pow_at_top

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* real.log_rpow
- \+ *lemma* tendsto_rpow_at_top
- \+ *lemma* tendsto_rpow_div
- \+ *lemma* tendsto_rpow_div_mul_add
- \+ *lemma* tendsto_rpow_neg_at_top
- \+ *lemma* tendsto_rpow_neg_div

Modified src/data/real/pi.lean
- \+ *theorem* real.tendsto_sum_pi_div_four

Modified src/topology/algebra/monoid.lean
- \+ *lemma* tendsto.const_mul
- \+ *lemma* tendsto.mul_const

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_pow_at_top
- \+ *lemma* tendsto_pow_neg_at_top



## [2020-10-20 03:17:38](https://github.com/leanprover-community/mathlib/commit/cd884eb)
feat(measure_theory): finite_spanning_sets_in ([#4668](https://github.com/leanprover-community/mathlib/pull/4668))
* We define a new Type-valued structure `finite_spanning_sets_in` which consists of a countable sequence of sets that span the type, have finite measure, and live in a specified collection of sets, 
* `sigma_finite` is redefined in terms of `finite_spanning_sets_in`
* One of the ext lemmas is now conveniently formulated in terms of `finite_spanning_sets_in`
* `finite_spanning_sets_in` is also used to remove a little bit of code duplication in `prod` (which occurred because `sigma_finite` was a `Prop`, and forgot the actual construction)
* Define a predicate `is_countably_spanning` which states that a collection of sets has a countable spanning subset. This is useful for one particular lemma in `prod`.
* Generalize some lemmas about products in the case that the σ-algebras are generated by a collection of sets. This can be used to reason about iterated products.
* Prove `prod_assoc_prod`.
* Cleanup in `measurable_space` and somewhat in `measure_space`.
* Rename `measurable.sum_rec -> measurable.sum_elim` (and give a different but definitionally equal statement)
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.prod_assoc_preimage

Modified src/data/nat/pairing.lean
- \+ *lemma* set.Union_unpair_prod

Modified src/data/set/lattice.lean
- \+ *lemma* set.Union_prod
- \+ *lemma* set.bUnion_prod
- \+ *lemma* set.prod_Union
- \+ *lemma* set.prod_bUnion
- \+ *lemma* set.prod_sUnion
- \+ *lemma* set.sUnion_prod

Modified src/measure_theory/measurable_space.lean
- \+ *def* is_countably_spanning
- \+ *lemma* is_countably_spanning_is_measurable
- \+/\- *lemma* is_measurable.Inter
- \+/\- *lemma* is_measurable.Inter_Prop
- \+/\- *lemma* is_measurable.Union
- \+/\- *lemma* is_measurable.Union_Prop
- \+/\- *lemma* is_measurable.disjointed
- \+/\- *lemma* is_measurable.sInter
- \+/\- *lemma* is_measurable.sUnion
- \+/\- *lemma* is_measurable.subtype_image
- \+/\- *lemma* measurable.comp
- \+/\- *lemma* measurable.fst
- \+/\- *lemma* measurable.indicator
- \+/\- *lemma* measurable.piecewise
- \+/\- *lemma* measurable.snd
- \+/\- *lemma* measurable.subtype_coe
- \+/\- *lemma* measurable.subtype_mk
- \+ *lemma* measurable.sum_elim
- \- *lemma* measurable.sum_rec
- \+/\- *lemma* measurable_const
- \+/\- *lemma* measurable_equiv.coe_eq
- \+ *def* measurable_equiv.prod_assoc
- \+/\- *def* measurable_equiv.prod_comm
- \+/\- *def* measurable_equiv.prod_congr
- \+/\- *def* measurable_equiv.set.prod
- \+/\- *def* measurable_equiv.set.range_inl
- \+/\- *def* measurable_equiv.set.range_inr
- \+/\- *def* measurable_equiv.set.singleton
- \+/\- *def* measurable_equiv.sum_congr
- \+/\- *def* measurable_equiv.symm
- \- *lemma* measurable_equiv.symm_to_equiv
- \+/\- *def* measurable_equiv.trans
- \- *lemma* measurable_equiv.trans_to_equiv
- \+/\- *lemma* measurable_find
- \+/\- *lemma* measurable_find_greatest'
- \+/\- *lemma* measurable_find_greatest
- \+/\- *lemma* measurable_from_nat
- \+/\- *lemma* measurable_from_top
- \+/\- *lemma* measurable_id
- \+/\- *lemma* measurable_of_measurable_on_compl_singleton
- \+/\- *lemma* measurable_one
- \+/\- *lemma* measurable_pi_apply
- \+/\- *lemma* measurable_pi_lambda
- \+/\- *lemma* measurable_space.comap_bot
- \+/\- *lemma* measurable_space.comap_supr
- \+/\- *lemma* measurable_space.dynkin_system.ext
- \+/\- *lemma* measurable_space.dynkin_system.generate_le
- \+/\- *def* measurable_space.dynkin_system.to_measurable_space
- \+/\- *lemma* measurable_space.ext
- \+ *lemma* measurable_space.generate_from_is_measurable
- \+/\- *lemma* measurable_space.generate_from_le
- \+/\- *def* measurable_space.gi_generate_from
- \+ *lemma* measurable_space.is_pi_system_is_measurable
- \+/\- *lemma* measurable_space.map_top
- \+/\- *structure* measurable_space
- \+/\- *lemma* measurable_subtype_coe
- \+/\- *lemma* measurable_to_encodable
- \+/\- *lemma* measurable_to_nat
- \+/\- *lemma* measurable_unit
- \+/\- *lemma* subsingleton.measurable

Modified src/measure_theory/measure_space.lean
- \+/\- *def* completion
- \- *lemma* measure_theory.exists_finite_spanning_sets
- \- *lemma* measure_theory.finite_at_filter_of_finite
- \+ *lemma* measure_theory.is_countably_spanning_spanning_sets
- \+/\- *lemma* measure_theory.measure.ext_of_generate_from_of_Union
- \+/\- *lemma* measure_theory.measure.finite_at_bot
- \+/\- *def* measure_theory.measure.finite_at_filter
- \+ *lemma* measure_theory.measure.finite_at_filter_of_finite
- \+ *structure* measure_theory.measure.finite_spanning_sets_in
- \+ *def* measure_theory.measure.to_finite_spanning_sets_in
- \+ *def* measure_theory.sigma_finite
- \+/\- *def* null_measurable

Modified src/measure_theory/prod.lean
- \+ *lemma* generate_from_eq_prod
- \+ *lemma* generate_from_prod_eq
- \+ *lemma* is_countably_spanning.prod
- \+ *lemma* is_pi_system.prod
- \+ *def* measure_theory.measure.finite_spanning_sets_in.prod
- \+ *lemma* measure_theory.measure.prod_assoc_prod
- \+ *lemma* measure_theory.measure.prod_eq_generate_from
- \- *lemma* measure_theory.measure.prod_unique



## [2020-10-20 01:14:13](https://github.com/leanprover-community/mathlib/commit/9755ae3)
chore(scripts): update nolints.txt ([#4704](https://github.com/leanprover-community/mathlib/pull/4704))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-19 22:45:26](https://github.com/leanprover-community/mathlib/commit/accc50e)
chore(data/finsupp): `to_additive` on `on_finset_sum` ([#4698](https://github.com/leanprover-community/mathlib/pull/4698))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.on_finset_prod
- \- *lemma* finsupp.on_finset_sum



## [2020-10-19 22:45:23](https://github.com/leanprover-community/mathlib/commit/706b484)
chore(data/multiset): add a few lemmas ([#4697](https://github.com/leanprover-community/mathlib/pull/4697))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.count_cons
- \+ *theorem* multiset.map_nsmul
- \+ *theorem* multiset.sum_map_singleton



## [2020-10-19 22:45:21](https://github.com/leanprover-community/mathlib/commit/b707e98)
refactor(ring_theory/witt_vector): move lemmas to separate file ([#4693](https://github.com/leanprover-community/mathlib/pull/4693))
This new file has almost no module docstring.
This is on purpose, it is a refactor PR.
A follow-up PR will add a module docstring and more definitions.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Added src/ring_theory/witt_vector/defs.lean
- \+ *lemma* witt_vector.constant_coeff_witt_add
- \+ *lemma* witt_vector.constant_coeff_witt_mul
- \+ *lemma* witt_vector.constant_coeff_witt_neg
- \+ *lemma* witt_vector.constant_coeff_witt_sub
- \+ *def* witt_vector.witt_add
- \+ *lemma* witt_vector.witt_add_vars
- \+ *lemma* witt_vector.witt_add_zero
- \+ *def* witt_vector.witt_mul
- \+ *lemma* witt_vector.witt_mul_vars
- \+ *lemma* witt_vector.witt_mul_zero
- \+ *def* witt_vector.witt_neg
- \+ *lemma* witt_vector.witt_neg_vars
- \+ *lemma* witt_vector.witt_neg_zero
- \+ *def* witt_vector.witt_one
- \+ *lemma* witt_vector.witt_one_pos_eq_zero
- \+ *lemma* witt_vector.witt_one_zero_eq_one
- \+ *def* witt_vector.witt_sub
- \+ *lemma* witt_vector.witt_sub_zero
- \+ *def* witt_vector.witt_zero
- \+ *lemma* witt_vector.witt_zero_eq_zero

Modified src/ring_theory/witt_vector/structure_polynomial.lean
- \+ *lemma* witt_structure_int_vars
- \+ *lemma* witt_structure_rat_vars
- \- *lemma* witt_vector.constant_coeff_witt_add
- \- *lemma* witt_vector.constant_coeff_witt_mul
- \- *lemma* witt_vector.constant_coeff_witt_neg
- \- *lemma* witt_vector.constant_coeff_witt_sub
- \- *lemma* witt_vector.witt_add_vars
- \- *lemma* witt_vector.witt_add_zero
- \- *lemma* witt_vector.witt_mul_vars
- \- *lemma* witt_vector.witt_mul_zero
- \- *lemma* witt_vector.witt_neg_vars
- \- *lemma* witt_vector.witt_neg_zero
- \- *lemma* witt_vector.witt_one_pos_eq_zero
- \- *lemma* witt_vector.witt_one_zero_eq_one
- \- *lemma* witt_vector.witt_structure_int_vars
- \- *lemma* witt_vector.witt_structure_rat_vars
- \- *lemma* witt_vector.witt_sub_zero
- \- *lemma* witt_vector.witt_zero_eq_zero



## [2020-10-19 22:45:19](https://github.com/leanprover-community/mathlib/commit/b300302)
feat(algebra/free_algebra): Add a ring instance ([#4692](https://github.com/leanprover-community/mathlib/pull/4692))
This also adds a ring instance to `tensor_algebra`.
The approach here does not work for `exterior_algebra` and `clifford_algebra`, and produces weird errors.
Those will be easier to investigate when their foundations are in mathlib.
#### Estimated changes
Modified src/algebra/free_algebra.lean


Modified src/linear_algebra/tensor_algebra.lean




## [2020-10-19 22:45:17](https://github.com/leanprover-community/mathlib/commit/cc6594a)
doc(algebra/algebra/basic): Fixes some documentation about `R`-algebras ([#4689](https://github.com/leanprover-community/mathlib/pull/4689))
See the associated zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/The.20Type.20of.20R-algebras/near/213722713
#### Estimated changes
Modified src/algebra/algebra/basic.lean




## [2020-10-19 22:45:15](https://github.com/leanprover-community/mathlib/commit/86d65f8)
chore(topology/instances/ennreal): prove `nnreal.not_summable_iff_tendsto_nat_at_top` ([#4670](https://github.com/leanprover-community/mathlib/pull/4670))
* use `ℝ≥0` notation in `data/real/ennreal`;
* add `ennreal.forall_ne_top`, `ennreal.exists_ne_top`,
  `ennreal.ne_top_equiv_nnreal`, `ennreal.cinfi_ne_top`,
  `ennreal.infi_ne_top`, `ennreal.csupr_ne_top`, `ennreal.sup_ne_top`,
  `ennreal.supr_ennreal`;
* add `nnreal.injective_coe`, add `@[simp, norm_cast]` to
  `nnreal.tendsto_coe`, and add `nnreal.tendsto_coe_at_top`; move
  `nnreal.infi_real_pos_eq_infi_nnreal_pos` from `ennreal` to `nnreal`;
* use `function.injective` instead of an unfolded definition in `filter.comap_map`;
* add `ennreal.nhds_top'`, `ennreal.tendsto_nhds_top_iff_nnreal`,
  `ennreal.tendsto_nhds_top_iff_nat`;
  
* upgrade `ennreal.tendsto_coe_nnreal_nhds_top` to an `iff`, rename to
  `ennreal.tendsto_coe_nhds_top`;
* `nnreal.has_sum_iff_tendsto_nat` now takes  `r` as an implicit argument;
* add `nnreal.not_summable_iff_tendsto_nat_at_top` and
  `not_summable_iff_tendsto_nat_at_top_of_nonneg`.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.cinfi_ne_top
- \+/\- *lemma* ennreal.coe_Inf
- \+/\- *lemma* ennreal.coe_Sup
- \+/\- *lemma* ennreal.coe_finset_prod
- \+/\- *lemma* ennreal.coe_finset_sum
- \+/\- *lemma* ennreal.coe_indicator
- \+/\- *lemma* ennreal.coe_inv_two
- \+/\- *lemma* ennreal.coe_le_iff
- \+/\- *lemma* ennreal.coe_max
- \+/\- *lemma* ennreal.coe_mem_upper_bounds
- \+/\- *lemma* ennreal.coe_min
- \+/\- *lemma* ennreal.coe_mono
- \+/\- *lemma* ennreal.coe_nat
- \+/\- *lemma* ennreal.coe_nnreal_eq
- \+/\- *lemma* ennreal.coe_one
- \+/\- *lemma* ennreal.coe_to_real
- \+/\- *lemma* ennreal.coe_two
- \+/\- *lemma* ennreal.coe_zero
- \+ *lemma* ennreal.csupr_ne_top
- \+ *lemma* ennreal.exists_ne_top
- \+/\- *lemma* ennreal.forall_ennreal
- \+ *lemma* ennreal.forall_ne_top
- \+ *lemma* ennreal.infi_ne_top
- \+/\- *lemma* ennreal.le_coe_iff
- \+/\- *lemma* ennreal.le_of_forall_epsilon_le
- \+/\- *lemma* ennreal.lt_iff_exists_add_pos_lt
- \+/\- *lemma* ennreal.lt_iff_exists_coe
- \+ *def* ennreal.ne_top_equiv_nnreal
- \+/\- *def* ennreal.of_nnreal_hom
- \+/\- *lemma* ennreal.some_eq_coe
- \+ *lemma* ennreal.supr_ennreal
- \+ *lemma* ennreal.supr_ne_top
- \+/\- *def* ennreal

Modified src/data/real/nnreal.lean


Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.comap_map

Modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_nhds_bot_mono'
- \+ *lemma* tendsto_nhds_bot_mono
- \+ *lemma* tendsto_nhds_top_mono'
- \+ *lemma* tendsto_nhds_top_mono

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.nhds_top'
- \+/\- *lemma* ennreal.nhds_top
- \+ *lemma* ennreal.tendsto_coe_nhds_top
- \- *lemma* ennreal.tendsto_coe_nnreal_nhds_top
- \+ *lemma* ennreal.tendsto_nhds_top_iff_nat
- \+ *lemma* ennreal.tendsto_nhds_top_iff_nnreal
- \+/\- *lemma* ennreal.tsum_coe_ne_top_iff_summable
- \- *lemma* infi_real_pos_eq_infi_nnreal_pos
- \+/\- *lemma* nnreal.has_sum_iff_tendsto_nat
- \+ *lemma* nnreal.not_summable_iff_tendsto_nat_at_top
- \+ *lemma* not_summable_iff_tendsto_nat_at_top_of_nonneg

Modified src/topology/instances/nnreal.lean
- \+ *lemma* nnreal.comap_coe_at_top
- \+ *lemma* nnreal.infi_real_pos_eq_infi_nnreal_pos
- \+ *lemma* nnreal.map_coe_at_top
- \+ *lemma* nnreal.tendsto_coe'
- \+/\- *lemma* nnreal.tendsto_coe
- \+ *lemma* nnreal.tendsto_coe_at_top



## [2020-10-19 22:45:12](https://github.com/leanprover-community/mathlib/commit/3019581)
feat({field,ring}_theory/adjoin): generalize `induction_on_adjoin` ([#4647](https://github.com/leanprover-community/mathlib/pull/4647))
We can prove `induction_on_adjoin` for both `algebra.adjoin` and `intermediate_field.adjoin` in a very similar way, if we add a couple of small lemmas. The extra lemmas I introduced for `algebra.adjoin` shorten the proof of `intermediate_field.adjoin` noticeably.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* intermediate_field.adjoin_empty
- \+ *lemma* intermediate_field.adjoin_eq_algebra_adjoin
- \+ *lemma* intermediate_field.adjoin_insert_adjoin
- \- *lemma* intermediate_field.adjoin_le_algebra_adjoin
- \+ *lemma* intermediate_field.eq_adjoin_of_eq_algebra_adjoin
- \+ *def* intermediate_field.fg
- \+ *lemma* intermediate_field.fg_adjoin_finset
- \+ *theorem* intermediate_field.fg_bot
- \+ *theorem* intermediate_field.fg_def
- \+ *lemma* intermediate_field.fg_of_fg_to_subalgebra
- \+ *lemma* intermediate_field.fg_of_noetherian

Modified src/field_theory/intermediate_field.lean
- \+ *lemma* intermediate_field.to_subalgebra_le_to_subalgebra
- \+ *lemma* intermediate_field.to_subalgebra_lt_to_subalgebra

Modified src/ring_theory/adjoin.lean
- \+ *lemma* algebra.adjoin_insert_adjoin
- \+ *theorem* subalgebra.fg_of_fg_to_submodule
- \+ *theorem* subalgebra.fg_of_noetherian
- \+ *lemma* subalgebra.induction_on_adjoin



## [2020-10-19 22:45:10](https://github.com/leanprover-community/mathlib/commit/006b2e7)
feat(data/polynomial/reverse): define `reverse f`, prove that `reverse` is a multiplicative monoid homomorphism ([#4598](https://github.com/leanprover-community/mathlib/pull/4598))
#### Estimated changes
Added src/data/polynomial/reverse.lean
- \+ *lemma* polynomial.coeff_reflect
- \+ *lemma* polynomial.reflect_C_mul
- \+ *lemma* polynomial.reflect_C_mul_X_pow
- \+ *lemma* polynomial.reflect_add
- \+ *lemma* polynomial.reflect_eq_zero_iff
- \+ *lemma* polynomial.reflect_monomial
- \+ *theorem* polynomial.reflect_mul
- \+ *lemma* polynomial.reflect_mul_induction
- \+ *lemma* polynomial.reflect_support
- \+ *lemma* polynomial.reflect_zero
- \+ *def* polynomial.rev_at
- \+ *lemma* polynomial.rev_at_add
- \+ *def* polynomial.rev_at_fun
- \+ *lemma* polynomial.rev_at_fun_eq
- \+ *lemma* polynomial.rev_at_fun_inj
- \+ *lemma* polynomial.rev_at_fun_invol
- \+ *lemma* polynomial.rev_at_invol
- \+ *lemma* polynomial.rev_at_le
- \+ *theorem* polynomial.reverse_mul
- \+ *lemma* polynomial.reverse_mul_of_domain
- \+ *lemma* polynomial.reverse_zero



## [2020-10-19 22:45:07](https://github.com/leanprover-community/mathlib/commit/0c70cf3)
feat(tactic/unify_equations): add unify_equations tactic ([#4515](https://github.com/leanprover-community/mathlib/pull/4515))
`unify_equations` is a first-order unification tactic for propositional
equalities. It implements the algorithm that `cases` uses to simplify
indices of inductive types, with one extension: `unify_equations` can
derive a contradiction from 'cyclic' equations like `n = n + 1`.
`unify_equations` is unlikely to be particularly useful on its own, but
I'll use it as part of my new `induction` tactic.
#### Estimated changes
Modified docs/references.bib


Modified src/tactic/basic.lean


Modified src/tactic/core.lean


Added src/tactic/unify_equations.lean
- \+ *lemma* tactic.unify_equations.add_add_one_ne

Added test/unify_equations.lean
- \+ *inductive* rose



## [2020-10-19 22:45:05](https://github.com/leanprover-community/mathlib/commit/a249c9a)
feat(archive/imo): formalize IMO 1998 problem 2 ([#4502](https://github.com/leanprover-community/mathlib/pull/4502))
#### Estimated changes
Added archive/imo/imo1998_q2.lean
- \+ *def* A
- \+ *lemma* A_card_lower_bound
- \+ *lemma* A_card_upper_bound
- \+ *lemma* A_fibre_over_contestant
- \+ *lemma* A_fibre_over_contestant_card
- \+ *lemma* A_fibre_over_judge_pair
- \+ *lemma* A_fibre_over_judge_pair_card
- \+ *lemma* A_maps_to_off_diag_judge_pair
- \+ *lemma* add_sq_add_sq_sub
- \+ *def* agreed_contestants
- \+ *abbreviation* agreed_triple.contestant
- \+ *abbreviation* agreed_triple.judge_pair
- \+ *abbreviation* agreed_triple
- \+ *lemma* clear_denominators
- \+ *lemma* distinct_judge_pairs_card_lower_bound
- \+ *theorem* imo1998_q2
- \+ *abbreviation* judge_pair.agree
- \+ *lemma* judge_pair.agree_iff_same_rating
- \+ *abbreviation* judge_pair.distinct
- \+ *abbreviation* judge_pair.judge₁
- \+ *abbreviation* judge_pair.judge₂
- \+ *abbreviation* judge_pair
- \+ *lemma* judge_pairs_card_lower_bound
- \+ *lemma* norm_bound_of_odd_sum

Modified src/data/finset/basic.lean
- \+ *def* finset.diag
- \+ *lemma* finset.diag_card
- \+ *lemma* finset.filter_card_add_filter_neg_card_eq_card
- \+ *theorem* finset.filter_product
- \+ *lemma* finset.filter_product_card
- \+ *lemma* finset.mem_diag
- \+ *lemma* finset.mem_off_diag
- \+ *def* finset.off_diag
- \+ *lemma* finset.off_diag_card

Modified src/data/int/parity.lean
- \+ *lemma* int.ne_of_odd_sum

Modified src/data/nat/parity.lean
- \+ *lemma* nat.odd_gt_zero



## [2020-10-19 22:45:03](https://github.com/leanprover-community/mathlib/commit/5065471)
feat(data/monoid_algebra): add missing has_coe_to_fun ([#4315](https://github.com/leanprover-community/mathlib/pull/4315))
Also does the same for the additive version `semimodule k (add_monoid_algebra k G)`.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean




## [2020-10-19 20:01:36](https://github.com/leanprover-community/mathlib/commit/0523b61)
chore(logic/function): `simp`lify applications of `(un)curry` ([#4696](https://github.com/leanprover-community/mathlib/pull/4696))
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* function.curry_apply
- \+ *lemma* function.uncurry_apply_pair



## [2020-10-19 15:37:07-04:00](https://github.com/leanprover-community/mathlib/commit/a1f1770)
Revert "chore(data/multiset): add a few lemmas"
This reverts commit 45caa4f392fe4f7622fef576cf3811b9ff6fd307.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \- *theorem* multiset.count_cons
- \- *theorem* multiset.map_nsmul
- \- *theorem* multiset.sum_map_singleton



## [2020-10-19 15:30:42-04:00](https://github.com/leanprover-community/mathlib/commit/45caa4f)
chore(data/multiset): add a few lemmas
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.count_cons
- \+ *theorem* multiset.map_nsmul
- \+ *theorem* multiset.sum_map_singleton



## [2020-10-19 15:11:45](https://github.com/leanprover-community/mathlib/commit/cacc297)
fix(tactic/norm_num): remove unnecessary argument to rat.cast_zero ([#4682](https://github.com/leanprover-community/mathlib/pull/4682))
See [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60norm_num.60.20error.20message).
#### Estimated changes
Modified src/tactic/norm_num.lean
- \+/\- *theorem* norm_num.adc_bit0_bit1
- \+/\- *theorem* norm_num.adc_bit1_bit0
- \+/\- *theorem* norm_num.adc_bit1_bit1
- \+/\- *lemma* norm_num.int_div
- \+/\- *lemma* norm_num.int_mod
- \+/\- *theorem* norm_num.le_bit0_bit0
- \+/\- *theorem* norm_num.le_bit1_bit1
- \+/\- *theorem* norm_num.lt_bit0_bit0
- \+/\- *theorem* norm_num.lt_bit1_bit1
- \+/\- *theorem* norm_num.rat_cast_bit0
- \+/\- *theorem* norm_num.rat_cast_bit1
- \+/\- *theorem* norm_num.sle_bit0_bit0
- \+/\- *theorem* norm_num.sle_bit0_bit1
- \+/\- *theorem* norm_num.sle_bit1_bit0
- \+/\- *theorem* norm_num.sle_bit1_bit1
- \+/\- *theorem* norm_num.sle_one_bit0
- \+/\- *theorem* norm_num.sle_one_bit1

Modified test/norm_num.lean




## [2020-10-19 11:39:07](https://github.com/leanprover-community/mathlib/commit/0f1bc68)
feat(ring_theory/witt_vector/structure_polynomial): examples and basic properties ([#4467](https://github.com/leanprover-community/mathlib/pull/4467))
This is the 4th and final PR in a series on a fundamental theorem about Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.eval₂_hom_zero'
- \+ *lemma* mv_polynomial.eval₂_hom_zero

Modified src/data/mv_polynomial/variables.lean
- \+ *lemma* mv_polynomial.mem_vars_bind₁
- \+ *lemma* mv_polynomial.mem_vars_rename

Modified src/ring_theory/witt_vector/structure_polynomial.lean
- \+ *lemma* constant_coeff_witt_structure_int
- \+ *lemma* constant_coeff_witt_structure_int_zero
- \+ *lemma* constant_coeff_witt_structure_rat
- \+ *lemma* constant_coeff_witt_structure_rat_zero
- \+ *lemma* witt_vector.constant_coeff_witt_add
- \+ *lemma* witt_vector.constant_coeff_witt_mul
- \+ *lemma* witt_vector.constant_coeff_witt_neg
- \+ *lemma* witt_vector.constant_coeff_witt_sub
- \+ *lemma* witt_vector.witt_add_vars
- \+ *lemma* witt_vector.witt_add_zero
- \+ *lemma* witt_vector.witt_mul_vars
- \+ *lemma* witt_vector.witt_mul_zero
- \+ *lemma* witt_vector.witt_neg_vars
- \+ *lemma* witt_vector.witt_neg_zero
- \+ *lemma* witt_vector.witt_one_pos_eq_zero
- \+ *lemma* witt_vector.witt_one_zero_eq_one
- \+ *lemma* witt_vector.witt_structure_int_vars
- \+ *lemma* witt_vector.witt_structure_rat_vars
- \+ *lemma* witt_vector.witt_sub_zero
- \+ *lemma* witt_vector.witt_zero_eq_zero



## [2020-10-19 11:39:05](https://github.com/leanprover-community/mathlib/commit/4140f78)
feat(algebra/ordered_semiring): relax 0 < 1 to 0 ≤ 1 ([#4363](https://github.com/leanprover-community/mathlib/pull/4363))
Per [discussion](https://github.com/leanprover-community/mathlib/pull/4296#issuecomment-701953077) in [#4296](https://github.com/leanprover-community/mathlib/pull/4296).
#### Estimated changes
Modified archive/imo/imo1972_b2.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \- *lemma* zero_lt_one'

Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_ring.lean
- \+/\- *lemma* canonically_ordered_semiring.zero_lt_one
- \+/\- *lemma* le_of_mul_le_of_one_le
- \+/\- *def* nonneg_ring.to_linear_nonneg_ring
- \- *def* nonneg_ring.to_ordered_ring
- \+ *lemma* zero_le_two
- \+ *lemma* zero_lt_one'
- \+/\- *lemma* zero_lt_one

Modified src/algebra/punit_instances.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* real.norm_two

Modified src/analysis/normed_space/mazur_ulam.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/int/basic.lean


Modified src/data/nat/basic.lean


Modified src/data/num/lemmas.lean


Modified src/data/polynomial/div.lean


Modified src/data/rat/order.lean


Modified src/data/real/basic.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.one_lt_two

Modified src/data/real/nnreal.lean


Modified src/data/zsqrtd/basic.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/order/filter/filter_product.lean
- \+ *lemma* filter.germ.le_def

Modified src/ring_theory/subsemiring.lean


Modified src/tactic/linarith/verification.lean


Modified src/tactic/norm_num.lean


Modified src/tactic/omega/coeffs.lean


Modified src/topology/algebra/floor_ring.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/path_connected.lean




## [2020-10-19 10:38:52](https://github.com/leanprover-community/mathlib/commit/ef9d00f)
feat(linear_algebra/matrix): multiplying `is_basis.to_matrix` and `linear_map.to_matrix` ([#4650](https://github.com/leanprover-community/mathlib/pull/4650))
This basically tells us that `is_basis.to_matrix` is indeed a basis change matrix.
#### Estimated changes
Modified src/linear_algebra/matrix.lean
- \+ *lemma* is_basis.sum_to_matrix_smul_self
- \+ *lemma* is_basis.to_lin_to_matrix
- \+/\- *def* is_basis.to_matrix
- \+ *lemma* is_basis.to_matrix_eq_to_matrix_constr
- \+/\- *lemma* is_basis.to_matrix_self
- \+/\- *lemma* is_basis.to_matrix_update
- \+ *lemma* is_basis_to_matrix_mul_linear_map_to_matrix
- \+ *lemma* linear_map_to_matrix_mul_is_basis_to_matrix
- \+ *lemma* matrix.to_lin_self



## [2020-10-19 10:38:50](https://github.com/leanprover-community/mathlib/commit/47dcecd)
feat(data/complex/exponential): bounds on exp ([#4432](https://github.com/leanprover-community/mathlib/pull/4432))
Define `real.exp_bound` using `complex.exp_bound`.  Deduce numerical
bounds on `exp 1` analogous to those we have for pi.
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+ *lemma* real.exp_1_approx_succ_eq
- \+ *lemma* real.exp_approx_end'
- \+ *lemma* real.exp_approx_end
- \+ *lemma* real.exp_approx_start
- \+ *lemma* real.exp_approx_succ
- \+ *lemma* real.exp_bound
- \+ *def* real.exp_near
- \+ *theorem* real.exp_near_sub
- \+ *theorem* real.exp_near_succ
- \+ *theorem* real.exp_near_zero

Added src/data/complex/exponential_bounds.lean
- \+ *lemma* real.exp_neg_one_gt_0367879441
- \+ *lemma* real.exp_neg_one_lt_0367879442
- \+ *lemma* real.exp_one_gt_271828182
- \+ *lemma* real.exp_one_lt_271828183
- \+ *lemma* real.exp_one_near_10
- \+ *lemma* real.exp_one_near_20



## [2020-10-19 10:38:48](https://github.com/leanprover-community/mathlib/commit/c38d128)
feat(ring_theory/polynomial/chebyshev): chebyshev polynomials of the first kind ([#4267](https://github.com/leanprover-community/mathlib/pull/4267))
If T_n denotes the n-th Chebyshev polynomial of the first kind, then the
polynomials 2*T_n(X/2) form a Lambda structure on Z[X].
I call these polynomials the lambdashev polynomials, because, as far as I
am aware they don't have a name in the literature.
We show that they commute, and that the p-th polynomial is congruent to X^p
mod p. In other words: a Lambda structure.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* chebyshev₁_complex_cos
- \+ *lemma* cos_nat_mul

Added src/ring_theory/polynomial/chebyshev/basic.lean
- \+ *lemma* polynomial.chebyshev₁_eq_lambdashev
- \+ *lemma* polynomial.chebyshev₁_mul
- \+ *lemma* polynomial.lambdashev_char_p
- \+ *lemma* polynomial.lambdashev_comp_comm
- \+ *lemma* polynomial.lambdashev_eq_chebyshev₁
- \+ *lemma* polynomial.lambdashev_eval_add_inv
- \+ *lemma* polynomial.lambdashev_mul
- \+ *lemma* polynomial.lambdashev_zmod_p

Added src/ring_theory/polynomial/chebyshev/default.lean


Added src/ring_theory/polynomial/chebyshev/defs.lean
- \+ *lemma* polynomial.chebyshev₁_add_two
- \+ *lemma* polynomial.chebyshev₁_of_two_le
- \+ *lemma* polynomial.chebyshev₁_one
- \+ *lemma* polynomial.chebyshev₁_two
- \+ *lemma* polynomial.chebyshev₁_zero
- \+ *lemma* polynomial.lambdashev_add_two
- \+ *lemma* polynomial.lambdashev_eq_two_le
- \+ *lemma* polynomial.lambdashev_one
- \+ *lemma* polynomial.lambdashev_two
- \+ *lemma* polynomial.lambdashev_zero
- \+ *lemma* polynomial.map_chebyshev₁
- \+ *lemma* polynomial.map_lambdashev



## [2020-10-19 07:13:04](https://github.com/leanprover-community/mathlib/commit/f75dbd3)
feat(algebra/*): some simp lemmas, and changing binders ([#4681](https://github.com/leanprover-community/mathlib/pull/4681))
#### Estimated changes
Modified src/algebra/algebra/basic.lean


Modified src/algebra/invertible.lean
- \+ *lemma* inv_of_mul_self_assoc
- \+ *lemma* mul_inv_of_self_assoc

Modified src/group_theory/group_action.lean




## [2020-10-19 07:13:01](https://github.com/leanprover-community/mathlib/commit/41c227a)
feat(algebra/infinite_sum): make tsum irreducible ([#4679](https://github.com/leanprover-community/mathlib/pull/4679))
See https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/congr'.20is.20slow
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+/\- *def* tsum



## [2020-10-19 07:12:58](https://github.com/leanprover-community/mathlib/commit/7601a7a)
feat(ring_theory/adjoin): adjoin_singleton_one ([#4633](https://github.com/leanprover-community/mathlib/pull/4633))
#### Estimated changes
Modified src/ring_theory/adjoin.lean
- \+ *lemma* algebra.adjoin_singleton_one



## [2020-10-19 04:45:06](https://github.com/leanprover-community/mathlib/commit/4b890a2)
feat(*): make int.nonneg irreducible ([#4601](https://github.com/leanprover-community/mathlib/pull/4601))
In [#4474](https://github.com/leanprover-community/mathlib/pull/4474), `int.lt` was made irreducible. We make `int.nonneg` irreducible, which is stronger as `int.lt` is expressed in terms of `int.nonneg`.
#### Estimated changes
Modified src/algebra/field_power.lean


Modified src/data/int/basic.lean


Modified src/data/int/range.lean


Modified src/data/int/sqrt.lean
- \+/\- *theorem* int.sqrt_nonneg

Modified src/data/nat/modeq.lean


Modified src/data/rat/sqrt.lean


Modified src/data/zmod/basic.lean


Modified src/data/zsqrtd/gaussian_int.lean
- \+/\- *lemma* gaussian_int.norm_nonneg

Modified src/number_theory/lucas_lehmer.lean


Modified src/tactic/omega/eq_elim.lean


Modified src/tactic/omega/nat/dnf.lean


Modified test/monotonicity.lean


Modified test/tactics.lean




## [2020-10-19 01:25:23](https://github.com/leanprover-community/mathlib/commit/d174295)
chore(scripts): update nolints.txt ([#4680](https://github.com/leanprover-community/mathlib/pull/4680))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-19 01:25:21](https://github.com/leanprover-community/mathlib/commit/9d1bbd1)
fix(data/equiv): nolint typo ([#4677](https://github.com/leanprover-community/mathlib/pull/4677))
#### Estimated changes
Modified src/data/equiv/basic.lean




## [2020-10-19 01:25:19](https://github.com/leanprover-community/mathlib/commit/49bb5dd)
refactor(tactic/norm_num): define prove_ne_zero using prove_ne ([#4626](https://github.com/leanprover-community/mathlib/pull/4626))
This is trickier than it sounds because of a cyclic dependency. As a result we
now have two versions of `prove_ne_zero` and `prove_clear_denom` is
generic over them. One version proves ne using an order relation on the
target, while the other uses `uncast` lemmas to reduce to `rat` and
then uses the first `prove_ne_zero`. (This is why we actually want two versions -
we can't solve this with a large mutual def, because it would
result in an infinite recursion.)
#### Estimated changes
Modified src/tactic/norm_num.lean


Modified test/ring.lean




## [2020-10-18 23:06:55](https://github.com/leanprover-community/mathlib/commit/1ac5d82)
fix(logic/nontrivial): change tactic doc entry tag to more common "type class" ([#4676](https://github.com/leanprover-community/mathlib/pull/4676))
#### Estimated changes
Modified src/logic/nontrivial.lean




## [2020-10-18 21:34:51](https://github.com/leanprover-community/mathlib/commit/61e1111)
chore(linear_algebra/affine_space): introduce notation for `affine_map` ([#4675](https://github.com/leanprover-community/mathlib/pull/4675))
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* concave_on.comp_affine_map
- \+/\- *lemma* convex.affine_image
- \+/\- *lemma* convex.affine_preimage
- \+/\- *lemma* convex.combo_affine_apply
- \+/\- *lemma* convex_on.comp_affine_map

Modified src/analysis/convex/extrema.lean


Modified src/analysis/normed_space/mazur_ulam.lean
- \+/\- *def* isometric.to_affine_map

Modified src/geometry/euclidean/basic.lean
- \+/\- *def* euclidean_geometry.orthogonal_projection

Modified src/linear_algebra/affine_space/basic.lean
- \+/\- *lemma* affine_map.add_linear
- \+/\- *lemma* affine_map.apply_line_map
- \+/\- *lemma* affine_map.coe_add
- \+/\- *lemma* affine_map.coe_comp
- \+/\- *lemma* affine_map.coe_fst
- \+/\- *lemma* affine_map.coe_mul
- \+/\- *lemma* affine_map.coe_one
- \+/\- *lemma* affine_map.coe_smul
- \+/\- *lemma* affine_map.coe_snd
- \+/\- *lemma* affine_map.coe_zero
- \+/\- *def* affine_map.comp
- \+/\- *lemma* affine_map.comp_apply
- \+/\- *lemma* affine_map.comp_assoc
- \+/\- *lemma* affine_map.comp_id
- \+/\- *lemma* affine_map.comp_line_map
- \+/\- *def* affine_map.const
- \+/\- *lemma* affine_map.decomp'
- \+/\- *lemma* affine_map.decomp
- \+/\- *lemma* affine_map.ext
- \+/\- *lemma* affine_map.ext_iff
- \+/\- *def* affine_map.fst
- \+/\- *lemma* affine_map.fst_linear
- \+/\- *def* affine_map.homothety
- \+/\- *def* affine_map.homothety_affine
- \+/\- *def* affine_map.homothety_hom
- \+/\- *def* affine_map.id
- \+/\- *lemma* affine_map.id_comp
- \+/\- *lemma* affine_map.image_interval
- \+/\- *def* affine_map.line_map
- \+/\- *lemma* affine_map.linear_map_vsub
- \+/\- *lemma* affine_map.map_vadd
- \+/\- *def* affine_map.snd
- \+/\- *lemma* affine_map.snd_linear
- \+/\- *lemma* affine_map.to_fun_eq_coe
- \+/\- *lemma* affine_map.vadd_apply
- \+/\- *lemma* affine_map.vsub_apply
- \+/\- *lemma* affine_map.zero_linear
- \+/\- *def* linear_map.to_affine_map

Modified src/linear_algebra/affine_space/combination.lean
- \+/\- *def* affine_map.weighted_vsub_of_point
- \+/\- *def* finset.affine_combination

Modified src/topology/algebra/affine.lean
- \+/\- *lemma* affine_map.continuous_iff



## [2020-10-18 21:34:49](https://github.com/leanprover-community/mathlib/commit/4faf2e2)
chore(order/filter): use implicit arguments in `tendsto_at_top` etc ([#4672](https://github.com/leanprover-community/mathlib/pull/4672))
Also weaken some assumptions from a decidable linear order to a linear order.
#### Estimated changes
Modified src/data/real/hyperreal.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.tendsto_at_bot'
- \+/\- *lemma* filter.tendsto_at_bot
- \+/\- *lemma* filter.tendsto_at_bot_at_bot
- \+/\- *lemma* filter.tendsto_at_bot_at_top
- \+/\- *lemma* filter.tendsto_at_top'
- \+/\- *lemma* filter.tendsto_at_top
- \+/\- *lemma* filter.tendsto_at_top_at_bot
- \+/\- *lemma* filter.tendsto_at_top_at_top
- \+ *lemma* filter.tendsto_at_top_mul_at_top

Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* emetric.tendsto_at_top

Modified src/topology/sequences.lean


Modified src/topology/uniform_space/cauchy.lean




## [2020-10-18 21:34:47](https://github.com/leanprover-community/mathlib/commit/392d52c)
chore(order/filter): run `dsimp only [set.mem_set_of_eq]` in `filter_upwards` ([#4671](https://github.com/leanprover-community/mathlib/pull/4671))
#### Estimated changes
Modified src/analysis/asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/special_functions/exp_log.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/prod.lean


Modified src/order/filter/basic.lean




## [2020-10-18 19:21:09](https://github.com/leanprover-community/mathlib/commit/93b7e63)
feat(analysis/special_functions/trigonometric): range_{exp,cos,sin} ([#4595](https://github.com/leanprover-community/mathlib/pull/4595))
#### Estimated changes
Modified src/algebra/ordered_ring.lean


Modified src/algebra/quadratic_discriminant.lean


Modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* real.log_surjective
- \+ *lemma* real.range_exp
- \+ *lemma* real.range_log

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.cos_surjective
- \+ *lemma* complex.exists_eq_mul_self
- \+ *lemma* complex.exists_pow_nat_eq
- \+ *lemma* complex.range_cos
- \+ *lemma* complex.range_exp
- \+ *lemma* complex.range_sin
- \+ *lemma* complex.sin_surjective
- \+ *lemma* real.range_cos_infinite
- \+ *lemma* real.range_sin_infinite

Modified src/data/set/finite.lean
- \+ *theorem* set.infinite_of_infinite_image



## [2020-10-18 16:02:22](https://github.com/leanprover-community/mathlib/commit/fee2dfa)
chore(analysis/calculus/fderiv): golf a lemma using new `nontriviality` ([#4584](https://github.com/leanprover-community/mathlib/pull/4584))
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/topology/algebra/module.lean




## [2020-10-18 09:59:52](https://github.com/leanprover-community/mathlib/commit/e21dc7a)
feat(topology/subset_properties): define `filter.cocompact` ([#4666](https://github.com/leanprover-community/mathlib/pull/4666))
The filter of complements to compact subsets.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* continuous.norm
- \+ *lemma* tendsto_norm_cocompact_at_top

Modified src/data/set/basic.lean
- \+ *lemma* set.nonempty_insert

Modified src/topology/algebra/ordered.lean
- \+ *lemma* continuous.exists_forall_ge
- \+ *lemma* continuous.exists_forall_le

Modified src/topology/metric_space/basic.lean
- \+ *lemma* tendsto_dist_left_cocompact_at_top
- \+ *lemma* tendsto_dist_right_cocompact_at_top

Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean
- \+ *def* filter.cocompact
- \+ *lemma* filter.has_basis_cocompact
- \+ *lemma* filter.mem_cocompact'
- \+ *lemma* filter.mem_cocompact
- \+ *lemma* is_compact.compl_mem_cocompact
- \+ *lemma* is_compact.insert



## [2020-10-18 05:51:33](https://github.com/leanprover-community/mathlib/commit/cc32876)
chore(analysis/normed_space/basic): add `continuous_at.inv'`, `continuous.div` etc ([#4667](https://github.com/leanprover-community/mathlib/pull/4667))
Also add `continuous_on_(cos/sin)`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* continuous.div
- \+ *lemma* continuous.inv'
- \+ *lemma* continuous_at.inv'
- \+ *lemma* continuous_on.div
- \+ *lemma* continuous_on.inv'
- \+ *lemma* continuous_within_at.div
- \+ *lemma* continuous_within_at.inv'

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.continuous_on_cos
- \+ *lemma* complex.continuous_on_sin
- \+ *lemma* real.continuous_on_cos



## [2020-10-18 04:29:30](https://github.com/leanprover-community/mathlib/commit/db06b67)
feat(measure_theory/prod): product measures and Fubini's theorem ([#4590](https://github.com/leanprover-community/mathlib/pull/4590))
* Define the product measure of two σ-finite measures.
* Prove Tonelli's theorem.
* Prove Fubini's theorem.
#### Estimated changes
Modified docs/overview.yaml


Modified docs/references.bib


Modified docs/undergrad.yaml


Modified src/data/indicator_function.lean
- \+ *lemma* set.indicator_mul_left
- \+ *lemma* set.indicator_mul_right

Modified src/measure_theory/measure_space.lean


Added src/measure_theory/prod.lean
- \+ *lemma* generate_from_prod
- \+ *lemma* is_measurable_integrable
- \+ *lemma* is_pi_system_prod
- \+ *lemma* measurable.integral_prod_left'
- \+ *lemma* measurable.integral_prod_left
- \+ *lemma* measurable.integral_prod_right'
- \+ *lemma* measurable.integral_prod_right
- \+ *lemma* measurable.lintegral_prod_left'
- \+ *lemma* measurable.lintegral_prod_left
- \+ *lemma* measurable.lintegral_prod_right'
- \+ *lemma* measurable.lintegral_prod_right
- \+ *lemma* measurable.map_prod_mk_left
- \+ *lemma* measurable.map_prod_mk_right
- \+ *lemma* measurable_measure_prod_mk_left
- \+ *lemma* measurable_measure_prod_mk_left_finite
- \+ *lemma* measurable_measure_prod_mk_right
- \+ *lemma* measure_theory.continuous_integral_integral
- \+ *lemma* measure_theory.has_finite_integral_prod_iff
- \+ *lemma* measure_theory.integrable.integral_norm_prod_left
- \+ *lemma* measure_theory.integrable.integral_norm_prod_right
- \+ *lemma* measure_theory.integrable.integral_prod_left
- \+ *lemma* measure_theory.integrable.integral_prod_right
- \+ *lemma* measure_theory.integrable.prod_left_ae
- \+ *lemma* measure_theory.integrable.prod_right_ae
- \+ *lemma* measure_theory.integrable.swap
- \+ *lemma* measure_theory.integrable_prod_iff'
- \+ *lemma* measure_theory.integrable_prod_iff
- \+ *lemma* measure_theory.integrable_swap_iff
- \+ *lemma* measure_theory.integral_fn_integral_add
- \+ *lemma* measure_theory.integral_fn_integral_sub
- \+ *lemma* measure_theory.integral_integral
- \+ *lemma* measure_theory.integral_integral_add'
- \+ *lemma* measure_theory.integral_integral_add
- \+ *lemma* measure_theory.integral_integral_sub'
- \+ *lemma* measure_theory.integral_integral_sub
- \+ *lemma* measure_theory.integral_integral_swap
- \+ *lemma* measure_theory.integral_integral_symm
- \+ *lemma* measure_theory.integral_prod
- \+ *lemma* measure_theory.integral_prod_swap
- \+ *lemma* measure_theory.integral_prod_symm
- \+ *lemma* measure_theory.lintegral_fn_integral_sub
- \+ *lemma* measure_theory.lintegral_lintegral
- \+ *lemma* measure_theory.lintegral_lintegral_swap
- \+ *lemma* measure_theory.lintegral_lintegral_symm
- \+ *lemma* measure_theory.lintegral_prod
- \+ *lemma* measure_theory.lintegral_prod_swap
- \+ *lemma* measure_theory.lintegral_prod_symm
- \+ *lemma* measure_theory.measure.add_prod
- \+ *lemma* measure_theory.measure.ae_ae_of_ae_prod
- \+ *lemma* measure_theory.measure.ae_measure_lt_top
- \+ *lemma* measure_theory.measure.dirac_prod
- \+ *lemma* measure_theory.measure.dirac_prod_dirac
- \+ *lemma* measure_theory.measure.integrable_measure_prod_mk_left
- \+ *lemma* measure_theory.measure.measure_ae_null_of_prod_null
- \+ *lemma* measure_theory.measure.measure_prod_null
- \+ *lemma* measure_theory.measure.prod_add
- \+ *lemma* measure_theory.measure.prod_apply
- \+ *lemma* measure_theory.measure.prod_apply_symm
- \+ *lemma* measure_theory.measure.prod_dirac
- \+ *lemma* measure_theory.measure.prod_eq
- \+ *lemma* measure_theory.measure.prod_prod
- \+ *lemma* measure_theory.measure.prod_restrict
- \+ *lemma* measure_theory.measure.prod_sum
- \+ *lemma* measure_theory.measure.prod_swap
- \+ *lemma* measure_theory.measure.prod_unique
- \+ *lemma* measure_theory.measure.sum_prod



## [2020-10-18 01:46:58](https://github.com/leanprover-community/mathlib/commit/c7782bb)
chore(scripts): update nolints.txt ([#4665](https://github.com/leanprover-community/mathlib/pull/4665))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-18 01:46:56](https://github.com/leanprover-community/mathlib/commit/77dc679)
chore(data/set/intervals): more lemmas ([#4662](https://github.com/leanprover-community/mathlib/pull/4662))
#### Estimated changes
Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Icc_bot
- \+ *lemma* set.Icc_top
- \+/\- *lemma* set.Ici_bot
- \+/\- *lemma* set.Ici_top
- \+ *lemma* set.Ico_bot
- \+ *lemma* set.Ico_subset_Ici_self
- \+ *lemma* set.Ico_union_right
- \+ *lemma* set.Iic_bot
- \+ *lemma* set.Iic_top
- \+ *lemma* set.Ioc_subset_Iic_self
- \+ *lemma* set.Ioc_top
- \+ *lemma* set.Ioc_union_left
- \+ *lemma* set.Ioo_union_left
- \+ *lemma* set.Ioo_union_right



## [2020-10-18 01:46:53](https://github.com/leanprover-community/mathlib/commit/9585210)
chore(order/filter): add a few lemmas ([#4661](https://github.com/leanprover-community/mathlib/pull/4661))
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.at_top_basis_Ioi
- \+ *lemma* filter.eventually_gt_at_top
- \+ *lemma* filter.eventually_lt_at_bot

Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.frequently_iff

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.eventually_sup
- \+ *lemma* filter.tendsto_top



## [2020-10-18 01:46:51](https://github.com/leanprover-community/mathlib/commit/f990838)
chore(data/finsupp/basic): rename type variables ([#4624](https://github.com/leanprover-community/mathlib/pull/4624))
Use `M`, `N`, `P` for types with `has_zero`, `add_monoid`, or
`add_comm_monoid` structure, and `R`, `S` for types with at least
a `semiring` instance.
API change: `single_add_erase` and `erase_add_single` now use explicit arguments.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.add_apply
- \+/\- *lemma* finsupp.add_eq_zero_iff
- \+/\- *lemma* finsupp.add_hom_ext
- \+/\- *def* finsupp.antidiagonal
- \+/\- *lemma* finsupp.antidiagonal_zero
- \+/\- *lemma* finsupp.card_support_eq_one'
- \+/\- *lemma* finsupp.card_support_eq_one
- \+/\- *lemma* finsupp.card_support_eq_zero
- \+/\- *lemma* finsupp.coe_leval'
- \+/\- *lemma* finsupp.coe_leval
- \+/\- *def* finsupp.comap_domain
- \+/\- *lemma* finsupp.comap_domain_apply
- \+/\- *def* finsupp.comap_has_scalar
- \+/\- *def* finsupp.comap_mul_action
- \+/\- *lemma* finsupp.comap_smul_apply
- \+/\- *lemma* finsupp.comap_smul_single
- \+/\- *def* finsupp.emb_domain
- \+/\- *lemma* finsupp.emb_domain_apply
- \+/\- *lemma* finsupp.emb_domain_eq_map_domain
- \+/\- *lemma* finsupp.emb_domain_eq_zero
- \+/\- *lemma* finsupp.emb_domain_inj
- \+/\- *lemma* finsupp.emb_domain_injective
- \+/\- *lemma* finsupp.emb_domain_notin_range
- \+/\- *lemma* finsupp.emb_domain_zero
- \+/\- *lemma* finsupp.eq_single_iff
- \+/\- *lemma* finsupp.eq_zero_of_comap_domain_eq_zero
- \+/\- *def* finsupp.equiv_fun_on_fintype
- \+/\- *def* finsupp.erase
- \+/\- *lemma* finsupp.erase_add
- \+/\- *lemma* finsupp.erase_add_single
- \+/\- *lemma* finsupp.erase_ne
- \+/\- *lemma* finsupp.erase_same
- \+/\- *lemma* finsupp.erase_single
- \+/\- *lemma* finsupp.erase_single_ne
- \+/\- *lemma* finsupp.erase_zero
- \+/\- *def* finsupp.eval_add_hom
- \+/\- *lemma* finsupp.eval_add_hom_apply
- \+/\- *lemma* finsupp.ext
- \+/\- *lemma* finsupp.ext_iff
- \+/\- *def* finsupp.filter
- \+/\- *lemma* finsupp.filter_add
- \+/\- *lemma* finsupp.filter_curry
- \+/\- *lemma* finsupp.filter_pos_add_filter_neg
- \+/\- *lemma* finsupp.filter_smul
- \+/\- *lemma* finsupp.filter_sum
- \+/\- *lemma* finsupp.filter_zero
- \+/\- *lemma* finsupp.finite_le_nat
- \+/\- *lemma* finsupp.finite_lt_nat
- \+/\- *lemma* finsupp.finite_supp
- \+/\- *def* finsupp.finsupp_prod_equiv
- \+/\- *def* finsupp.frange
- \+/\- *theorem* finsupp.frange_single
- \+/\- *lemma* finsupp.induction₂
- \+/\- *lemma* finsupp.le_iff
- \+/\- *def* finsupp.leval'
- \+/\- *def* finsupp.leval
- \+/\- *lemma* finsupp.lhom_ext'
- \+/\- *lemma* finsupp.lhom_ext
- \+/\- *def* finsupp.lift_add_hom
- \+/\- *lemma* finsupp.lift_add_hom_apply
- \+/\- *lemma* finsupp.lift_add_hom_single_add_hom
- \+/\- *lemma* finsupp.lift_add_hom_symm_apply
- \+/\- *lemma* finsupp.lift_add_hom_symm_apply_apply
- \+/\- *lemma* finsupp.lt_wf
- \+/\- *def* finsupp.map_domain
- \+/\- *lemma* finsupp.map_domain_add
- \+/\- *lemma* finsupp.map_domain_apply
- \+/\- *lemma* finsupp.map_domain_comap_domain
- \+/\- *lemma* finsupp.map_domain_comp
- \+/\- *lemma* finsupp.map_domain_congr
- \+/\- *lemma* finsupp.map_domain_finset_sum
- \+/\- *lemma* finsupp.map_domain_injective
- \+/\- *lemma* finsupp.map_domain_notin_range
- \+/\- *lemma* finsupp.map_domain_single
- \+/\- *lemma* finsupp.map_domain_smul
- \+/\- *lemma* finsupp.map_domain_sum
- \+/\- *lemma* finsupp.map_domain_support
- \+/\- *lemma* finsupp.map_domain_zero
- \+/\- *def* finsupp.map_range.add_monoid_hom
- \+/\- *def* finsupp.map_range
- \+/\- *lemma* finsupp.map_range_add
- \+/\- *lemma* finsupp.map_range_apply
- \+/\- *lemma* finsupp.map_range_finset_sum
- \+/\- *lemma* finsupp.map_range_multiset_sum
- \+/\- *lemma* finsupp.map_range_single
- \+/\- *lemma* finsupp.map_range_zero
- \+/\- *lemma* finsupp.mem_antidiagonal_support
- \+/\- *theorem* finsupp.mem_frange
- \+/\- *lemma* finsupp.mem_support_finset_sum
- \+/\- *lemma* finsupp.mem_support_iff
- \+/\- *lemma* finsupp.mem_support_multiset_sum
- \+/\- *lemma* finsupp.mem_support_single
- \+/\- *lemma* finsupp.mul_sum
- \+/\- *lemma* finsupp.multiset_map_sum
- \+/\- *lemma* finsupp.multiset_sum_sum
- \+/\- *lemma* finsupp.neg_apply
- \+/\- *lemma* finsupp.not_mem_support_iff
- \+/\- *def* finsupp.on_finset
- \+/\- *lemma* finsupp.on_finset_apply
- \+/\- *lemma* finsupp.on_finset_sum
- \+/\- *def* finsupp.prod
- \+/\- *lemma* finsupp.prod_add_index
- \+/\- *lemma* finsupp.prod_comm
- \+/\- *lemma* finsupp.prod_emb_domain
- \+/\- *lemma* finsupp.prod_finset_sum_index
- \+/\- *lemma* finsupp.prod_fintype
- \+ *lemma* finsupp.prod_inv
- \+/\- *lemma* finsupp.prod_ite_eq'
- \+/\- *lemma* finsupp.prod_ite_eq
- \+/\- *lemma* finsupp.prod_map_domain_index
- \+/\- *lemma* finsupp.prod_map_domain_index_inj
- \+/\- *lemma* finsupp.prod_map_range_index
- \+ *lemma* finsupp.prod_mul
- \+/\- *lemma* finsupp.prod_neg_index
- \+/\- *lemma* finsupp.prod_of_support_subset
- \+/\- *lemma* finsupp.prod_pow
- \+/\- *lemma* finsupp.prod_single_index
- \+/\- *lemma* finsupp.prod_subtype_domain_index
- \+/\- *lemma* finsupp.prod_to_multiset
- \+/\- *lemma* finsupp.prod_zero_index
- \+/\- *def* finsupp.restrict_support_equiv
- \+/\- *lemma* finsupp.sigma_sum
- \+/\- *def* finsupp.single
- \+/\- *lemma* finsupp.single_add
- \+/\- *lemma* finsupp.single_add_erase
- \+/\- *def* finsupp.single_add_hom
- \+/\- *lemma* finsupp.single_apply
- \+/\- *lemma* finsupp.single_eq_of_ne
- \+/\- *lemma* finsupp.single_eq_same
- \+/\- *lemma* finsupp.single_eq_single_iff
- \+/\- *lemma* finsupp.single_finset_sum
- \+/\- *lemma* finsupp.single_injective
- \+/\- *lemma* finsupp.single_multiset_sum
- \+/\- *lemma* finsupp.single_sum
- \+/\- *lemma* finsupp.single_swap
- \+/\- *lemma* finsupp.single_zero
- \+/\- *lemma* finsupp.smul_apply'
- \+/\- *lemma* finsupp.smul_apply
- \+/\- *lemma* finsupp.smul_single'
- \+/\- *lemma* finsupp.smul_single
- \+/\- *lemma* finsupp.smul_single_one
- \+/\- *def* finsupp.split
- \+/\- *def* finsupp.split_comp
- \+/\- *lemma* finsupp.sub_apply
- \+/\- *def* finsupp.subtype_domain
- \+/\- *lemma* finsupp.subtype_domain_add
- \+/\- *lemma* finsupp.subtype_domain_apply
- \+/\- *lemma* finsupp.subtype_domain_eq_zero_iff'
- \+/\- *lemma* finsupp.subtype_domain_eq_zero_iff
- \+/\- *lemma* finsupp.subtype_domain_finsupp_sum
- \+/\- *lemma* finsupp.subtype_domain_neg
- \+/\- *lemma* finsupp.subtype_domain_sub
- \+/\- *lemma* finsupp.subtype_domain_sum
- \+/\- *lemma* finsupp.subtype_domain_zero
- \+/\- *def* finsupp.sum
- \- *lemma* finsupp.sum_add
- \+/\- *lemma* finsupp.sum_apply
- \+/\- *lemma* finsupp.sum_comap_domain
- \+/\- *lemma* finsupp.sum_curry_index
- \+/\- *lemma* finsupp.sum_id_lt_of_lt
- \+/\- *lemma* finsupp.sum_mul
- \- *lemma* finsupp.sum_neg
- \+/\- *lemma* finsupp.sum_single
- \+/\- *lemma* finsupp.sum_smul_index'
- \+/\- *lemma* finsupp.sum_smul_index
- \+/\- *lemma* finsupp.sum_sub
- \+/\- *lemma* finsupp.sum_zero
- \+/\- *lemma* finsupp.support_add
- \+/\- *lemma* finsupp.support_add_eq
- \+/\- *lemma* finsupp.support_curry
- \+/\- *lemma* finsupp.support_emb_domain
- \+/\- *lemma* finsupp.support_eq_empty
- \+/\- *lemma* finsupp.support_eq_singleton'
- \+/\- *lemma* finsupp.support_eq_singleton
- \+/\- *lemma* finsupp.support_erase
- \+/\- *lemma* finsupp.support_map_range
- \+/\- *lemma* finsupp.support_neg
- \+/\- *lemma* finsupp.support_on_finset_subset
- \+/\- *lemma* finsupp.support_smul
- \+/\- *lemma* finsupp.support_subset_iff
- \+/\- *lemma* finsupp.support_subtype_domain
- \+/\- *lemma* finsupp.support_sum
- \+/\- *lemma* finsupp.support_zero
- \+/\- *lemma* finsupp.support_zip_with
- \+/\- *lemma* finsupp.swap_mem_antidiagonal_support
- \+/\- *lemma* finsupp.to_multiset_strict_mono
- \+/\- *lemma* finsupp.to_multiset_to_finsupp
- \+/\- *lemma* finsupp.unique_ext
- \+/\- *lemma* finsupp.unique_ext_iff
- \+/\- *lemma* finsupp.unique_single
- \+/\- *lemma* finsupp.unique_single_eq_iff
- \+/\- *lemma* finsupp.zero_apply
- \+/\- *theorem* finsupp.zero_not_mem_frange
- \+/\- *def* finsupp.zip_with
- \+/\- *structure* finsupp
- \+/\- *lemma* monoid_hom.map_finsupp_prod
- \+/\- *lemma* mul_equiv.map_finsupp_prod
- \+/\- *lemma* ring_hom.map_finsupp_prod
- \+/\- *lemma* ring_hom.map_finsupp_sum

Modified src/data/polynomial/degree/basic.lean


Modified src/linear_algebra/finsupp.lean




## [2020-10-18 01:46:49](https://github.com/leanprover-community/mathlib/commit/ebd2b7f)
feat(logic/nontrivial): make `nontriviality` work for more goals ([#4574](https://github.com/leanprover-community/mathlib/pull/4574))
The goal is to make `nontriviality` work for the following goals:
* [x] `nontriviality α` if the goal is `is_open s`, `s : set α`;
* [x] `nontriviality E` if the goal is `is_O f g` or `is_o f g`, where `f : α → E`;
* [x] `nontriviality R` if the goal is `linear_independent R _`;
* [ ] `nontriviality R` if the goal is `is_O f g` or `is_o f g`, where `f : α → E`, `[semimodule R E]`;
  in this case `nontriviality` should add a local instance `semimodule.subsingleton R`.
The last case was never needed in `mathlib`, and there is a workaround: run `nontriviality E`, then deduce `nontrivial R` from `nontrivial E`.
Misc feature:
* [x] make `nontriviality` accept an optional list of additional `simp` lemmas.
#### Estimated changes
Modified src/algebra/group/units.lean
- \+/\- *lemma* is_unit_of_subsingleton

Modified src/analysis/asymptotics.lean
- \+ *lemma* asymptotics.is_O_of_subsingleton
- \+ *lemma* asymptotics.is_o_of_subsingleton

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_at_of_subsingleton
- \+ *lemma* times_cont_diff_of_subsingleton
- \+ *lemma* times_cont_diff_on_of_subsingleton
- \+ *lemma* times_cont_diff_within_at_of_subsingleton

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_of_subsingleton

Modified src/analysis/normed_space/units.lean


Modified src/data/polynomial/degree/basic.lean
- \+ *lemma* polynomial.monic_of_subsingleton

Modified src/linear_algebra/char_poly/coeff.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/logic/nontrivial.lean


Modified test/nontriviality.lean
- \+ *def* empty_or_univ
- \+ *lemma* subsingleton.set_empty_or_univ'
- \+ *lemma* subsingleton.set_empty_or_univ



## [2020-10-18 01:46:47](https://github.com/leanprover-community/mathlib/commit/b977dba)
fix(solve_by_elim): handle multiple goals with different hypotheses ([#4519](https://github.com/leanprover-community/mathlib/pull/4519))
Previously `solve_by_elim*` would operate on multiple goals (only succeeding if it could close all of them, and performing backtracking across goals), however it would incorrectly only use the local context from the main goal. If other goals had different sets of hypotheses, ... various bad things could happen!
This PR arranges so that `solve_by_elim*` inspects the local context later, so it picks up the correct hypotheses.
#### Estimated changes
Modified src/tactic/equiv_rw.lean


Modified src/tactic/solve_by_elim.lean


Modified src/tactic/suggest.lean


Modified test/solve_by_elim.lean




## [2020-10-17 23:24:37](https://github.com/leanprover-community/mathlib/commit/13cd192)
feat(measure_theory/measure_space): added sub for measure_theory.measure ([#4639](https://github.com/leanprover-community/mathlib/pull/4639))
This definition is useful for proving the Lebesgue-Radon-Nikodym theorem for non-negative measures.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.le_of_add_le_add_left

Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.measure.le_of_add_le_add_left
- \+ *lemma* measure_theory.measure.le_zero_iff_eq'
- \+ *lemma* measure_theory.measure.sub_add_cancel_of_le
- \+ *lemma* measure_theory.measure.sub_apply
- \+ *lemma* measure_theory.measure.sub_def
- \+ *lemma* measure_theory.measure.sub_eq_zero_of_le

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.tsum_sub



## [2020-10-17 23:24:35](https://github.com/leanprover-community/mathlib/commit/e83458c)
feat(algebra/group_power): Add mul/add variants of powers_hom and friends ([#4636](https://github.com/leanprover-community/mathlib/pull/4636))
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *def* gmultiples_add_hom
- \+ *lemma* gmultiples_add_hom_apply
- \+ *lemma* gmultiples_add_hom_symm_apply
- \+ *def* gpowers_mul_hom
- \+ *lemma* gpowers_mul_hom_apply
- \+ *lemma* gpowers_mul_hom_symm_apply
- \+ *def* multiples_add_hom
- \+ *lemma* multiples_add_hom_apply
- \+ *lemma* multiples_add_hom_symm_apply
- \+ *def* powers_mul_hom
- \+ *lemma* powers_mul_hom_apply
- \+ *lemma* powers_mul_hom_symm_apply



## [2020-10-17 23:24:33](https://github.com/leanprover-community/mathlib/commit/c83c28a)
feat(archive/imo): add IMO 2019 problem 4 ([#4482](https://github.com/leanprover-community/mathlib/pull/4482))
#### Estimated changes
Added archive/imo/imo2019_q4.lean
- \+ *theorem* imo2019_q4
- \+ *theorem* imo2019_q4_upper_bound

Modified src/algebra/big_operators/default.lean


Added src/algebra/big_operators/enat.lean
- \+ *lemma* finset.sum_nat_coe_enat

Modified src/data/int/basic.lean
- \+ *lemma* int.exists_lt_and_lt_iff_not_dvd

Modified src/data/nat/basic.lean
- \+ *lemma* nat.exists_lt_and_lt_iff_not_dvd

Modified src/data/nat/bitwise.lean
- \+ *lemma* nat.bit_eq_zero

Modified src/data/nat/enat.lean
- \+ *def* enat.coe_hom

Modified src/data/nat/multiplicity.lean
- \+ *lemma* nat.multiplicity_two_factorial_lt
- \+ *lemma* nat.prime.multiplicity_factorial_mul
- \+ *lemma* nat.prime.multiplicity_factorial_mul_succ
- \+/\- *lemma* nat.prime.multiplicity_one

Modified src/order/basic.lean
- \+ *lemma* monotone.ne_of_lt_of_lt_int
- \+ *lemma* monotone.ne_of_lt_of_lt_nat



## [2020-10-17 20:50:45](https://github.com/leanprover-community/mathlib/commit/95d33ee)
refactor(algebra/quadratic_discriminant): drop linearity condition; cleanup ([#4656](https://github.com/leanprover-community/mathlib/pull/4656))
Renames:
- `discriminant_le_zero` to `discrim_le_zero`
- `discriminant_lt_zero` to `discrim_lt_zero`
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* exists_le_mul_self
- \+ *lemma* exists_lt_mul_self

Modified src/algebra/quadratic_discriminant.lean
- \+/\- *def* discrim
- \+ *lemma* discrim_le_zero
- \+ *lemma* discrim_lt_zero
- \- *lemma* discriminant_le_zero
- \- *lemma* discriminant_lt_zero
- \- *lemma* exist_quadratic_eq_zero
- \- *lemma* exists_le_mul_self
- \- *lemma* exists_lt_mul_self
- \+ *lemma* exists_quadratic_eq_zero
- \+/\- *lemma* quadratic_eq_zero_iff
- \+/\- *lemma* quadratic_eq_zero_iff_discrim_eq_square
- \+/\- *lemma* quadratic_eq_zero_iff_of_discrim_eq_zero
- \+/\- *lemma* quadratic_ne_zero_of_discrim_ne_square



## [2020-10-17 20:50:43](https://github.com/leanprover-community/mathlib/commit/0367467)
chore(group/type_tags): Add missing simp lemmas ([#4651](https://github.com/leanprover-community/mathlib/pull/4651))
#### Estimated changes
Modified src/algebra/group/type_tags.lean
- \+/\- *def* additive.of_mul
- \+ *lemma* additive.of_mul_symm_eq
- \+/\- *def* additive.to_mul
- \+ *lemma* additive.to_mul_symm_eq
- \+/\- *def* multiplicative.of_add
- \+ *lemma* multiplicative.of_add_symm_eq
- \+/\- *def* multiplicative.to_add
- \+ *lemma* multiplicative.to_add_symm_eq



## [2020-10-17 20:50:41](https://github.com/leanprover-community/mathlib/commit/0b9afe1)
chore(linear_algebra/affine_space): redefine `line_map`, add `to_affine_subspace` ([#4643](https://github.com/leanprover-community/mathlib/pull/4643))
* now `line_map` takes two points on the line, not a point and a
  direction, update/review lemmas;
* add `submodule.to_affine_subspace`;
* add `affine_map.fst` and `affine_map.snd`;
* prove that an affine map `ℝ → ℝ` sends an unordered interval to an unordered interval.
#### Estimated changes
Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/extrema.lean


Modified src/data/set/function.lean
- \+ *theorem* set.maps_to_inter
- \+ *theorem* set.maps_to_union

Modified src/linear_algebra/affine_space/basic.lean
- \- *lemma* affine_map.affine_apply_line_map
- \- *lemma* affine_map.affine_comp_line_map
- \+ *lemma* affine_map.apply_line_map
- \+ *lemma* affine_map.coe_fst
- \+ *lemma* affine_map.coe_line_map
- \+ *lemma* affine_map.coe_snd
- \+ *lemma* affine_map.comp_line_map
- \+ *def* affine_map.fst
- \+ *lemma* affine_map.fst_linear
- \+ *lemma* affine_map.image_interval
- \+/\- *def* affine_map.line_map
- \+/\- *lemma* affine_map.line_map_apply
- \+ *lemma* affine_map.line_map_apply_one
- \+/\- *lemma* affine_map.line_map_apply_zero
- \+/\- *lemma* affine_map.line_map_linear
- \+ *lemma* affine_map.line_map_same
- \+ *lemma* affine_map.line_map_symm
- \+ *lemma* affine_map.line_map_vadd_apply
- \- *lemma* affine_map.line_map_vadd_neg
- \- *lemma* affine_map.line_map_zero
- \+ *def* affine_map.snd
- \+ *lemma* affine_map.snd_linear
- \+ *def* submodule.to_affine_subspace

Modified src/order/basic.lean
- \+ *lemma* monotone.reflect_lt
- \- *lemma* reflect_lt

Modified src/topology/algebra/affine.lean




## [2020-10-17 18:26:05](https://github.com/leanprover-community/mathlib/commit/589ebf5)
chore(algebra/*): add a few `prod.*` instances ([#4659](https://github.com/leanprover-community/mathlib/pull/4659))
* `prod.left_cancel_semigroup`;
* `prod_right_cancel_semigroup`;
* `prod.ordered_cancel_comm_monoid`;
* `ordered_comm_group`.
#### Estimated changes
Modified src/algebra/group/prod.lean


Modified src/algebra/ordered_group.lean




## [2020-10-17 18:26:02](https://github.com/leanprover-community/mathlib/commit/6e5b6cc)
feat(algebra/gcd_monoid, polynomial/field_division): generalizing `normalization_monoid` on polynomials ([#4655](https://github.com/leanprover-community/mathlib/pull/4655))
Defines a `normalization_monoid` instance on any `comm_group_with_zero`, including fields
Defines a `normalization_monoid` instance on `polynomial R` when `R` has a `normalization_monoid` instance
#### Estimated changes
Modified src/algebra/gcd_monoid.lean
- \+ *lemma* comm_group_with_zero.coe_norm_unit

Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* polynomial.coe_norm_unit
- \+ *lemma* polynomial.coe_norm_unit_of_ne_zero
- \+ *lemma* polynomial.leading_coeff_normalize
- \+ *lemma* polynomial.normalize_monic

Modified src/field_theory/algebraic_closure.lean


Modified src/field_theory/splitting_field.lean




## [2020-10-17 18:26:00](https://github.com/leanprover-community/mathlib/commit/edddb3b)
feat(finsupp/basic): Add a variant of `prod_map_domain_index` for when f is injective ([#4645](https://github.com/leanprover-community/mathlib/pull/4645))
This puts much weaker restrictions on `h`, making this easier to apply in some situations
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.prod_emb_domain
- \+ *lemma* finsupp.prod_map_domain_index_inj



## [2020-10-17 18:25:58](https://github.com/leanprover-community/mathlib/commit/85eb12d)
feat(algebra/algebra/basic): product of two algebras ([#4632](https://github.com/leanprover-community/mathlib/pull/4632))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra.algebra_map_prod_apply



## [2020-10-17 18:25:57](https://github.com/leanprover-community/mathlib/commit/82ff1e5)
feat(algebra/algebra/subalgebra): subalgebra.subsingleton ([#4631](https://github.com/leanprover-community/mathlib/pull/4631))
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean


Modified src/order/bounded_lattice.lean
- \+ *lemma* subsingleton_of_top_le_bot



## [2020-10-17 18:25:55](https://github.com/leanprover-community/mathlib/commit/688157f)
feat(ring_theory/polynomial/content): definition of content + proof that it is multiplicative ([#4393](https://github.com/leanprover-community/mathlib/pull/4393))
Defines `polynomial.content` to be the `gcd` of the coefficients of a polynomial
Says a polynomial `is_primitive` if its content is 1
Proves that `(p * q).content = p.content * q.content
#### Estimated changes
Modified src/algebra/ordered_group.lean
- \+ *lemma* with_bot.add_lt_add_iff_left
- \+ *lemma* with_bot.add_lt_add_iff_right

Modified src/data/polynomial/erase_lead.lean
- \+ *lemma* polynomial.erase_lead_nat_degree_lt_or_erase_lead_eq_zero

Added src/ring_theory/polynomial/content.lean
- \+ *lemma* polynomial.C_content_dvd
- \+ *def* polynomial.content
- \+ *lemma* polynomial.content_C
- \+ *lemma* polynomial.content_C_mul
- \+ *lemma* polynomial.content_X
- \+ *lemma* polynomial.content_X_mul
- \+ *lemma* polynomial.content_X_pow
- \+ *lemma* polynomial.content_dvd_coeff
- \+ *lemma* polynomial.content_eq_gcd_leading_coeff_content_erase_lead
- \+ *lemma* polynomial.content_eq_gcd_range_of_lt
- \+ *lemma* polynomial.content_eq_gcd_range_succ
- \+ *lemma* polynomial.content_eq_zero_iff
- \+ *lemma* polynomial.content_monomial
- \+ *theorem* polynomial.content_mul
- \+ *lemma* polynomial.content_mul_aux
- \+ *lemma* polynomial.content_one
- \+ *lemma* polynomial.content_zero
- \+ *lemma* polynomial.dvd_content_iff_C_dvd
- \+ *lemma* polynomial.eq_C_mul_primitive
- \+ *lemma* polynomial.gcd_content_eq_of_dvd_sub
- \+ *lemma* polynomial.is_primitive.content_eq_one
- \+ *lemma* polynomial.is_primitive.ne_zero
- \+ *def* polynomial.is_primitive
- \+ *lemma* polynomial.is_primitive_iff_is_unit_of_C_dvd
- \+ *lemma* polynomial.is_primitive_one
- \+ *lemma* polynomial.normalize_content



## [2020-10-17 16:08:01](https://github.com/leanprover-community/mathlib/commit/b145c36)
feat(archive/imo): variant solution to IMO 1962 problem 4 ([#4640](https://github.com/leanprover-community/mathlib/pull/4640))
Continuation of a discussion at [#4518](https://github.com/leanprover-community/mathlib/pull/4518)
#### Estimated changes
Modified archive/imo/imo1962_q4.lean
- \+ *lemma* formula
- \+ *theorem* imo1962_q4'
- \+ *lemma* solve_cos2x_0

Modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_eq_zero_iff



## [2020-10-17 13:41:26](https://github.com/leanprover-community/mathlib/commit/25d8343)
feat(topology/sheaves): an equivalent sheaf condition ([#4538](https://github.com/leanprover-community/mathlib/pull/4538))
Another condition equivalent to the sheaf condition: for every open cover `U`, `F.obj (supr U)` is the limit point of the diagram consisting of all the `F.obj V`, where `V ≤ U i` for some `i`.
This condition is particularly straightforward to state, and makes some proofs easier (however we don't do this here: just prove the equivalence with the "official" definition). It's particularly nice because there is no case splitting (depending on whether you're looking at single or double intersections) when checking the sheaf condition.
This is the statement Lurie uses in Spectral Algebraic Geometry.
Later I may propose that we make this the official definition, but I'll wait to see how it pans out in actual use, first. For now it's just provided as yet another equivalent version of the sheaf condition.
#### Estimated changes
Modified docs/references.bib


Modified src/topology/sheaves/sheaf.lean


Added src/topology/sheaves/sheaf_condition/opens_le_cover.lean
- \+ *def* Top.presheaf.sheaf_condition.opens_le_cover.hom_to_index
- \+ *def* Top.presheaf.sheaf_condition.opens_le_cover.index
- \+ *def* Top.presheaf.sheaf_condition.opens_le_cover
- \+ *def* Top.presheaf.sheaf_condition.opens_le_cover_cocone
- \+ *def* Top.presheaf.sheaf_condition.pairwise_cocone_iso
- \+ *def* Top.presheaf.sheaf_condition.pairwise_diagram_iso
- \+ *def* Top.presheaf.sheaf_condition.pairwise_to_opens_le_cover
- \+ *def* Top.presheaf.sheaf_condition.pairwise_to_opens_le_cover_map
- \+ *def* Top.presheaf.sheaf_condition.pairwise_to_opens_le_cover_obj
- \+ *def* Top.presheaf.sheaf_condition_equiv_sheaf_condition_opens_le_cover
- \+ *def* Top.presheaf.sheaf_condition_opens_le_cover
- \+ *def* Top.presheaf.sheaf_condition_opens_le_cover_equiv_sheaf_condition_pairwise_intersections



## [2020-10-17 01:11:20](https://github.com/leanprover-community/mathlib/commit/ca2e6f4)
chore(scripts): update nolints.txt ([#4654](https://github.com/leanprover-community/mathlib/pull/4654))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-16 21:43:46](https://github.com/leanprover-community/mathlib/commit/7b9acd9)
chore(measure_theory/*): reflow long lines ([#4642](https://github.com/leanprover-community/mathlib/pull/4642))
Also do some minor golfing.
#### Estimated changes
Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.integral_add_measure'
- \+/\- *lemma* measure_theory.l1.simple_func.coe_add
- \+/\- *lemma* measure_theory.l1.simple_func.coe_neg
- \+/\- *lemma* measure_theory.l1.simple_func.coe_neg_part
- \+/\- *lemma* measure_theory.l1.simple_func.coe_pos_part
- \+/\- *lemma* measure_theory.l1.simple_func.coe_sub
- \+/\- *lemma* measure_theory.l1.simple_func.coe_zero

Modified src/measure_theory/content.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.simple_func.supr_approx_apply

Modified src/measure_theory/interval_integral.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/set_integral.lean




## [2020-10-16 19:41:32](https://github.com/leanprover-community/mathlib/commit/189e538)
feat(geometry/manifold): stab at diffeomorphisms ([#4351](https://github.com/leanprover-community/mathlib/pull/4351))
#### Estimated changes
Added src/geometry/manifold/diffeomorph.lean
- \+ *def* diffeomorph
- \+ *lemma* times_diffeomorph.coe_eq_to_equiv
- \+ *structure* times_diffeomorph

Modified src/topology/homeomorph.lean




## [2020-10-16 18:01:28](https://github.com/leanprover-community/mathlib/commit/86b298f)
feat(category_theory/sites): grothendieck topologies ([#4577](https://github.com/leanprover-community/mathlib/pull/4577))
#### Estimated changes
Added src/category_theory/sites/grothendieck.lean
- \+ *lemma* category_theory.grothendieck_topology.arrow_intersect
- \+ *lemma* category_theory.grothendieck_topology.arrow_max
- \+ *lemma* category_theory.grothendieck_topology.arrow_stable
- \+ *lemma* category_theory.grothendieck_topology.arrow_trans
- \+ *def* category_theory.grothendieck_topology.atomic
- \+ *lemma* category_theory.grothendieck_topology.bot_covering
- \+ *lemma* category_theory.grothendieck_topology.bot_covers
- \+ *lemma* category_theory.grothendieck_topology.covering_iff_covers_id
- \+ *lemma* category_theory.grothendieck_topology.covering_of_eq_top
- \+ *def* category_theory.grothendieck_topology.covers
- \+ *lemma* category_theory.grothendieck_topology.covers_iff
- \+ *def* category_theory.grothendieck_topology.dense
- \+ *lemma* category_theory.grothendieck_topology.dense_covering
- \+ *def* category_theory.grothendieck_topology.discrete
- \+ *lemma* category_theory.grothendieck_topology.discrete_eq_top
- \+ *lemma* category_theory.grothendieck_topology.intersection_covering
- \+ *lemma* category_theory.grothendieck_topology.intersection_covering_iff
- \+ *lemma* category_theory.grothendieck_topology.is_glb_Inf
- \+ *lemma* category_theory.grothendieck_topology.mem_sieves_iff_coe
- \+ *lemma* category_theory.grothendieck_topology.pullback_stable
- \+ *def* category_theory.grothendieck_topology.right_ore_condition
- \+ *lemma* category_theory.grothendieck_topology.right_ore_of_pullbacks
- \+ *lemma* category_theory.grothendieck_topology.superset_covering
- \+ *lemma* category_theory.grothendieck_topology.top_covering
- \+ *lemma* category_theory.grothendieck_topology.top_covers
- \+ *lemma* category_theory.grothendieck_topology.top_mem
- \+ *lemma* category_theory.grothendieck_topology.transitive
- \+ *def* category_theory.grothendieck_topology.trivial
- \+ *lemma* category_theory.grothendieck_topology.trivial_covering
- \+ *lemma* category_theory.grothendieck_topology.trivial_eq_bot
- \+ *structure* category_theory.grothendieck_topology

Modified src/category_theory/sites/sieves.lean
- \+ *lemma* category_theory.sieve.pullback_eq_top_of_mem
- \+ *lemma* category_theory.sieve.pullback_id



## [2020-10-16 16:28:29](https://github.com/leanprover-community/mathlib/commit/0d9227f)
feat(category_theory/monad/kleisli): add Kleisli category of a monad ([#4542](https://github.com/leanprover-community/mathlib/pull/4542))
Adds the Kleisli category of a monad, and shows the Kleisli category for a lawful control monad is equivalent to the Kleisli category of its category-theoretic version.
Following discussion at https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/kleisli.20vs.20kleisli.
I'd appreciate suggestions for names more sensible than the ones already there.
#### Estimated changes
Added src/category_theory/monad/kleisli.lean
- \+ *def* category_theory.kleisli.adjunction.adj
- \+ *def* category_theory.kleisli.adjunction.from_kleisli
- \+ *def* category_theory.kleisli.adjunction.to_kleisli
- \+ *def* category_theory.kleisli.adjunction.to_kleisli_comp_from_kleisli_iso_self
- \+ *def* category_theory.kleisli

Modified src/category_theory/monad/types.lean
- \+ *def* category_theory.eq



## [2020-10-16 07:43:42](https://github.com/leanprover-community/mathlib/commit/f675a00)
chore(set_theory/zfc): split long lines ([#4641](https://github.com/leanprover-community/mathlib/pull/4641))
Also add `Set.subset_def` and rewrite `Set.mem_pair_sep` in tactic mode
#### Estimated changes
Modified src/set_theory/zfc.lean
- \+/\- *theorem* Class.sep_hom
- \+/\- *theorem* Set.image.mk
- \+/\- *theorem* Set.map_fval
- \+/\- *theorem* Set.map_is_func
- \+/\- *theorem* Set.map_unique
- \+/\- *theorem* Set.mem_image
- \+/\- *theorem* Set.mem_map
- \+/\- *theorem* Set.mem_pair_sep
- \+ *lemma* Set.subset_def
- \+/\- *theorem* pSet.definable.eq
- \+/\- *def* pSet.resp.eval_aux



## [2020-10-16 05:34:17](https://github.com/leanprover-community/mathlib/commit/1cce606)
feat(analysis/special_functions/trigonometric): some lemmas ([#4638](https://github.com/leanprover-community/mathlib/pull/4638))
The following changes:
- `sin_sub_sin` and friends (sum-to-product lemmas) moved from `trigonometric` to the earlier file `exponential`.  (I think the distinction between the files is that `trigonometric` collects the facts that require either differentiation or the definition `pi`, whereas purely algebraic facts about trigonometry go in `exponential`?  For example the double-angle formula is in `exponential`).
- rewrite proof of `cos_lt_cos_of_nonneg_of_le_pi_div_two` to avoid dependence on `cos_eq_one_iff_of_lt_of_lt` (but not sure if the result is actually simpler, feel free to propose this be reverted)
- some new explicit values of trig functions, `cos (π / 3)` and similar
- correct a series of lemmas in the `complex` namespace that were stated for real arguments (presumably the author copy-pasted but forgot to rewrite)
- lemmas `sin_eq_zero_iff`, `cos_eq_cos_iff`, `sin_eq_sin_iff`
#### Estimated changes
Modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* complex.cos_add_pi
- \+/\- *lemma* complex.cos_add_pi_div_two
- \+/\- *lemma* complex.cos_add_two_pi
- \+ *lemma* complex.cos_eq_cos_iff
- \+/\- *lemma* complex.cos_pi_div_two_sub
- \+/\- *lemma* complex.cos_pi_sub
- \+/\- *lemma* complex.cos_sub_pi_div_two
- \+/\- *lemma* complex.sin_add_pi
- \+/\- *lemma* complex.sin_add_pi_div_two
- \+/\- *lemma* complex.sin_add_two_pi
- \+ *lemma* complex.sin_eq_sin_iff
- \+ *theorem* complex.sin_eq_zero_iff
- \+ *theorem* complex.sin_ne_zero_iff
- \+/\- *lemma* complex.sin_pi_div_two_sub
- \+/\- *lemma* complex.sin_pi_sub
- \+/\- *lemma* complex.sin_sub_pi_div_two
- \+ *lemma* real.cos_eq_cos_iff
- \+ *lemma* real.cos_pi_div_six
- \+ *lemma* real.cos_pi_div_three
- \- *theorem* real.cos_sub_cos
- \+ *lemma* real.sin_eq_sin_iff
- \+ *lemma* real.sin_pi_div_six
- \+ *lemma* real.sin_pi_div_three
- \- *theorem* real.sin_sub_sin
- \+ *lemma* real.square_cos_pi_div_six
- \+ *lemma* real.square_sin_pi_div_three

Modified src/data/complex/exponential.lean
- \+ *lemma* complex.cos_add_cos
- \+ *theorem* complex.cos_sub_cos
- \+ *theorem* complex.sin_sub_sin
- \+ *lemma* real.cos_add_cos
- \+ *theorem* real.cos_sub_cos
- \+ *lemma* real.sin_sub_sin



## [2020-10-16 05:34:15](https://github.com/leanprover-community/mathlib/commit/e7b8421)
chore(linear_algebra/finsupp): turn `finsupp.lsum` into `add_equiv` ([#4597](https://github.com/leanprover-community/mathlib/pull/4597))
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \- *lemma* finsupp.hom_ext
- \+ *lemma* finsupp.lhom_ext'
- \+ *lemma* finsupp.lhom_ext
- \+ *lemma* finsupp.lift_add_hom_symm_apply_apply

Modified src/linear_algebra/direct_sum/finsupp.lean
- \+/\- *def* finsupp_lequiv_direct_sum

Modified src/linear_algebra/finsupp.lean
- \+/\- *def* finsupp.lsum
- \+ *theorem* finsupp.lsum_symm_apply



## [2020-10-16 03:25:42](https://github.com/leanprover-community/mathlib/commit/8280190)
chore(scripts): update nolints.txt ([#4637](https://github.com/leanprover-community/mathlib/pull/4637))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


Modified scripts/nolints.txt




## [2020-10-16 03:25:39](https://github.com/leanprover-community/mathlib/commit/cc14658)
chore(algebra/group_powers): Add missing lemmas ([#4635](https://github.com/leanprover-community/mathlib/pull/4635))
This part of the file defines four equivalences, but goes on to state lemmas about only one of them.
This provides the lemmas for the other three.
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* add_monoid_hom.apply_int
- \+ *lemma* add_monoid_hom.apply_nat
- \+ *lemma* gmultiples_hom_apply
- \+ *lemma* gmultiples_hom_symm_apply
- \+ *lemma* gpowers_hom_apply
- \+ *lemma* gpowers_hom_symm_apply
- \- *lemma* mnat_monoid_hom_eq
- \- *lemma* mnat_monoid_hom_ext
- \+ *lemma* monoid_hom.apply_mint
- \+ *lemma* monoid_hom.apply_mnat
- \+ *lemma* monoid_hom.ext_mint
- \+ *lemma* monoid_hom.ext_mnat
- \+ *lemma* multiples_hom_apply
- \+ *lemma* multiples_hom_symm_apply



## [2020-10-16 00:56:13](https://github.com/leanprover-community/mathlib/commit/dca1393)
feat(data/equiv/basic): add `equiv.set.compl` ([#4630](https://github.com/leanprover-community/mathlib/pull/4630))
Given an equivalence between two sets `e₀ : s ≃ t`, the set of
`e : α ≃ β` that agree with `e₀` on `s` is equivalent to `sᶜ ≃ tᶜ`.
Also add a bunch of lemmas to `data/set/function`; some of them are
used in the definition of `equiv.set.compl`.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.set.sum_compl_symm_apply
- \+ *lemma* equiv.set.sum_compl_symm_apply_compl
- \+ *lemma* equiv.set.union_symm_apply_left
- \+ *lemma* equiv.set.union_symm_apply_right
- \+ *def* equiv.set_prod_equiv_sigma
- \+ *lemma* equiv.subtype_congr_apply
- \+ *lemma* equiv.subtype_congr_symm_apply

Modified src/data/set/function.lean
- \- *lemma* function.injective.inj_on
- \+ *lemma* set.bij_on.compl
- \+ *lemma* set.inj_on_of_injective
- \+ *lemma* set.inv_on.mono
- \+ *theorem* set.left_inv_on.maps_to
- \+ *theorem* set.left_inv_on.mono
- \+/\- *theorem* set.left_inv_on.surj_on
- \+ *theorem* set.maps_to.mem_iff
- \+ *lemma* set.maps_to.surj_on_compl
- \+ *lemma* set.maps_to_iff_exists_map_subtype
- \+/\- *theorem* set.maps_to_range
- \+ *theorem* set.right_inv_on.maps_to
- \+ *theorem* set.right_inv_on.mono
- \+ *lemma* set.surj_on.maps_to_compl
- \+ *lemma* set.surj_on_iff_exists_map_subtype
- \+ *theorem* set.surjective_maps_to_image_restrict



## [2020-10-16 00:56:11](https://github.com/leanprover-community/mathlib/commit/b0b61e6)
feat(order/category/omega-complete): omega-complete partial orders form a complete category ([#4397](https://github.com/leanprover-community/mathlib/pull/4397))
as discussed in [#4348](https://github.com/leanprover-community/mathlib/pull/4348).
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \- *lemma* category_theory.limits.cofork.of_π_app_one
- \- *lemma* category_theory.limits.cofork.of_π_app_zero
- \- *lemma* category_theory.limits.fork.of_ι_app_one
- \- *lemma* category_theory.limits.fork.of_ι_app_zero

Modified src/category_theory/limits/shapes/products.lean
- \+/\- *def* category_theory.limits.cofan.mk
- \- *lemma* category_theory.limits.cofan.mk_π_app
- \+/\- *def* category_theory.limits.fan.mk
- \- *lemma* category_theory.limits.fan.mk_π_app

Modified src/category_theory/limits/shapes/types.lean


Modified src/order/category/omega_complete_partial_order.lean
- \+ *def* ωCPO.has_equalizers.equalizer
- \+ *def* ωCPO.has_equalizers.equalizer_ι
- \+ *def* ωCPO.has_equalizers.is_equalizer
- \+ *def* ωCPO.has_products.is_product
- \+ *def* ωCPO.has_products.product
- \+/\- *def* ωCPO

Modified src/order/omega_complete_partial_order.lean
- \+ *theorem* omega_complete_partial_order.continuous_hom.congr_arg
- \+ *theorem* omega_complete_partial_order.continuous_hom.congr_fun
- \+ *def* omega_complete_partial_order.subtype

Modified src/order/preorder_hom.lean
- \+ *def* preorder_hom.subtype.val



## [2020-10-15 23:48:19](https://github.com/leanprover-community/mathlib/commit/3e12a7b)
chore(category_theory/limits/binary_products): fixup binary product lemmas ([#4376](https://github.com/leanprover-community/mathlib/pull/4376))
The main changes in here are:
- `prod.map` is now a def, not an abbreviation. I think this is an important change because oftentimes `simp` will reduce it to `lim.map` and then get stuck, which is tough to debug and usually the wrong step to take. Instead, the `prod.map_fst` and `snd` lemmas are proved directly rather than with simp, and these are used to get everything else.
- I added a couple of new simp lemmas and rewrote a few others: the overall guide here is that more things can be proved by `rw` or `simp` *without using ext*. The idea of this is that when you're dealing with a chain of compositions containing product morphisms, it's much nicer to be able to rewrite (or simp) the parts you want rather than needing to do an auxiliary `have` and use `ext` in there, then rewrite using this lemma inside your big chain. In this file at least I managed to get rid of a bunch of uses of `ext` (and also convert `tidy` to `simp`) so I'm pretty sure these changes were positive.
- Moved around some definitions and lemmas. No big changes here, mostly just putting things which work similarly closer.
- Weakened typeclass assumptions: in particular for `prod_comparison`.
- Renamed some `prod_` lemmas to `prod.`, since there used to be a mix between the two; so I've made the usage consistent.
+ dual versions of all the above.
#### Estimated changes
Modified src/category_theory/abelian/non_preadditive.lean
- \+ *lemma* category_theory.non_preadditive_abelian.diag_σ
- \+/\- *def* category_theory.non_preadditive_abelian.is_colimit_σ
- \+/\- *abbreviation* category_theory.non_preadditive_abelian.r
- \- *abbreviation* category_theory.non_preadditive_abelian.Δ
- \- *lemma* category_theory.non_preadditive_abelian.Δ_map
- \- *lemma* category_theory.non_preadditive_abelian.Δ_σ
- \+/\- *abbreviation* category_theory.non_preadditive_abelian.σ

Modified src/category_theory/closed/cartesian.lean
- \+/\- *def* category_theory.coev
- \+ *lemma* category_theory.coev_naturality
- \+/\- *def* category_theory.ev
- \+ *lemma* category_theory.ev_naturality
- \+/\- *def* category_theory.exp.adjunction

Modified src/category_theory/limits/connected.lean
- \+/\- *def* category_theory.prod_preserves_connected_limits.forget_cone
- \+/\- *def* category_theory.prod_preserves_connected_limits.γ₁
- \+/\- *def* category_theory.prod_preserves_connected_limits.γ₂

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.coprod.desc_comp
- \- *lemma* category_theory.limits.coprod.desc_comp_comp
- \+ *lemma* category_theory.limits.coprod.desc_comp_inl_comp_inr
- \+ *lemma* category_theory.limits.coprod.desc_inl_inr
- \+ *lemma* category_theory.limits.coprod.diag_comp
- \+/\- *lemma* category_theory.limits.coprod.inl_map
- \+/\- *lemma* category_theory.limits.coprod.inr_map
- \+ *def* category_theory.limits.coprod.map
- \- *abbreviation* category_theory.limits.coprod.map
- \+/\- *lemma* category_theory.limits.coprod.map_codiag
- \- *lemma* category_theory.limits.coprod.map_comp_codiag
- \+ *lemma* category_theory.limits.coprod.map_comp_id
- \+/\- *lemma* category_theory.limits.coprod.map_comp_inl_inr_codiag
- \+/\- *lemma* category_theory.limits.coprod.map_desc
- \+ *lemma* category_theory.limits.coprod.map_id_comp
- \+ *lemma* category_theory.limits.coprod.map_id_id
- \+/\- *lemma* category_theory.limits.coprod.map_inl_inr_codiag
- \+ *def* category_theory.limits.coprod.map_iso
- \- *abbreviation* category_theory.limits.coprod.map_iso
- \- *lemma* category_theory.limits.coprod.map_iso_hom
- \- *lemma* category_theory.limits.coprod.map_iso_inv
- \+ *lemma* category_theory.limits.coprod.map_map
- \+ *lemma* category_theory.limits.coprod.map_swap
- \- *lemma* category_theory.limits.coprod_desc_inl_inr
- \- *lemma* category_theory.limits.coprod_map_comp_id
- \- *lemma* category_theory.limits.coprod_map_id_comp
- \- *lemma* category_theory.limits.coprod_map_id_id
- \- *lemma* category_theory.limits.coprod_map_map
- \+/\- *lemma* category_theory.limits.inv_prod_comparison_map_fst
- \+/\- *lemma* category_theory.limits.inv_prod_comparison_map_snd
- \+ *lemma* category_theory.limits.prod.comp_diag
- \+ *lemma* category_theory.limits.prod.comp_lift
- \+/\- *lemma* category_theory.limits.prod.diag_map
- \- *lemma* category_theory.limits.prod.diag_map_comp
- \+/\- *lemma* category_theory.limits.prod.diag_map_fst_snd
- \+ *def* category_theory.limits.prod.functor
- \- *lemma* category_theory.limits.prod.lift_comp_comp
- \+ *lemma* category_theory.limits.prod.lift_fst_comp_snd_comp
- \+ *lemma* category_theory.limits.prod.lift_fst_snd
- \+/\- *lemma* category_theory.limits.prod.lift_map
- \+ *def* category_theory.limits.prod.map
- \- *abbreviation* category_theory.limits.prod.map
- \+ *lemma* category_theory.limits.prod.map_comp_id
- \+/\- *lemma* category_theory.limits.prod.map_fst
- \+ *lemma* category_theory.limits.prod.map_id_comp
- \+ *lemma* category_theory.limits.prod.map_id_id
- \+ *def* category_theory.limits.prod.map_iso
- \- *abbreviation* category_theory.limits.prod.map_iso
- \- *lemma* category_theory.limits.prod.map_iso_hom
- \- *lemma* category_theory.limits.prod.map_iso_inv
- \+ *lemma* category_theory.limits.prod.map_map
- \+/\- *lemma* category_theory.limits.prod.map_snd
- \+ *lemma* category_theory.limits.prod.map_swap
- \+/\- *def* category_theory.limits.prod_comparison
- \+/\- *lemma* category_theory.limits.prod_comparison_inv_natural
- \+/\- *lemma* category_theory.limits.prod_comparison_natural
- \- *def* category_theory.limits.prod_functor
- \- *lemma* category_theory.limits.prod_lift_fst_snd
- \- *lemma* category_theory.limits.prod_map_comp_id
- \- *lemma* category_theory.limits.prod_map_id_comp
- \- *lemma* category_theory.limits.prod_map_id_id
- \- *lemma* category_theory.limits.prod_map_map

Modified src/category_theory/monoidal/of_has_finite_products.lean
- \+ *def* category_theory.limits.prod.functor_left_comp
- \+ *lemma* category_theory.limits.prod.left_unitor_hom_naturality
- \+ *lemma* category_theory.limits.prod.left_unitor_inv_naturality
- \+ *lemma* category_theory.limits.prod.right_unitor_hom_naturality
- \- *def* category_theory.limits.prod_functor_left_comp
- \- *lemma* category_theory.limits.prod_left_unitor_hom_naturality
- \- *lemma* category_theory.limits.prod_left_unitor_inv_naturality
- \- *lemma* category_theory.limits.prod_right_unitor_hom_naturality



## [2020-10-15 22:31:38](https://github.com/leanprover-community/mathlib/commit/b7d176e)
feat(category_theory/cones): some isomorphisms relating operations ([#4536](https://github.com/leanprover-community/mathlib/pull/4536))
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+ *def* category_theory.functor.map_cocone_precompose
- \+ *def* category_theory.functor.map_cocone_precompose_equivalence_functor
- \+ *def* category_theory.functor.map_cocone_whisker
- \+ *def* category_theory.functor.map_cone_postcompose
- \+ *def* category_theory.functor.map_cone_postcompose_equivalence_functor
- \+ *def* category_theory.functor.map_cone_whisker



## [2020-10-15 20:34:24](https://github.com/leanprover-community/mathlib/commit/8985e39)
feat(archive/100-theorems-list/70_perfect_numbers): Perfect Number Theorem, Direction 2 ([#4621](https://github.com/leanprover-community/mathlib/pull/4621))
Adds a few extra lemmas about `divisors`, `proper_divisors` and sums of proper divisors
Proves Euler's direction of the Perfect Number theorem, finishing Freek 70
#### Estimated changes
Modified archive/100-theorems-list/70_perfect_numbers.lean
- \+ *lemma* nat.eq_pow_two_mul_odd
- \+ *theorem* nat.eq_two_pow_mul_prime_mersenne_of_even_perfect
- \+ *theorem* nat.even_and_perfect_iff

Modified docs/100.yaml


Modified src/number_theory/divisors.lean
- \+ *lemma* nat.divisors_one
- \- *lemma* nat.divisors_prime
- \+ *lemma* nat.eq_proper_divisors_of_subset_of_sum_eq_sum
- \+/\- *lemma* nat.fst_mem_divisors_of_mem_antidiagonal
- \+/\- *lemma* nat.map_swap_divisors_antidiagonal
- \+ *lemma* nat.one_mem_proper_divisors_iff_one_lt
- \+/\- *theorem* nat.perfect_iff_sum_divisors_eq_two_mul
- \+/\- *theorem* nat.perfect_iff_sum_proper_divisors
- \+ *lemma* nat.pos_of_mem_divisors
- \+ *lemma* nat.pos_of_mem_proper_divisors
- \+ *lemma* nat.prime.divisors
- \+ *lemma* nat.prime.proper_divisors
- \+ *lemma* nat.prime.sum_divisors
- \+ *lemma* nat.prime.sum_proper_divisors
- \+ *lemma* nat.proper_divisors_eq_singleton_one_iff_prime
- \+ *lemma* nat.proper_divisors_one
- \+ *lemma* nat.proper_divisors_subset_divisors
- \+/\- *lemma* nat.snd_mem_divisors_of_mem_antidiagonal
- \- *lemma* nat.sum_divisors_prime
- \+ *lemma* nat.sum_proper_divisors_dvd
- \+ *lemma* nat.sum_proper_divisors_eq_one_iff_prime
- \+/\- *lemma* nat.swap_mem_divisors_antidiagonal



## [2020-10-15 16:29:11](https://github.com/leanprover-community/mathlib/commit/d473517)
chore(algebra/group/hom): add `monoid_hom.eval` ([#4629](https://github.com/leanprover-community/mathlib/pull/4629))
#### Estimated changes
Modified src/algebra/big_operators/pi.lean
- \+ *lemma* monoid_hom.finset_prod_apply
- \+/\- *lemma* pi.list_prod_apply

Modified src/algebra/group/hom.lean
- \+ *def* monoid_hom.eval
- \+ *lemma* monoid_hom.eval_apply



## [2020-10-15 16:29:09](https://github.com/leanprover-community/mathlib/commit/38a5f5d)
chore(data/equiv/mul_add): add `monoid_hom.to_mul_equiv` ([#4628](https://github.com/leanprover-community/mathlib/pull/4628))
#### Estimated changes
Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/data/equiv/mul_add.lean
- \+ *def* add_monoid_hom.to_add_equiv
- \+ *lemma* monoid_hom.coe_to_mul_equiv
- \+ *def* monoid_hom.to_mul_equiv
- \+ *lemma* mul_equiv.coe_to_monoid_hom



## [2020-10-15 16:29:07](https://github.com/leanprover-community/mathlib/commit/46b0528)
refactor(data/polynomial): Move some lemmas to `monoid_algebra` ([#4627](https://github.com/leanprover-community/mathlib/pull/4627))
The `add_monoid_algebra.mul_apply_antidiagonal` lemma is copied verbatim from `monoid_algebra.mul_apply_antidiagonal`.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.mul_apply_antidiagonal

Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/basic.lean
- \+/\- *def* polynomial.coeff
- \- *lemma* polynomial.coeff_single

Modified src/data/polynomial/coeff.lean




## [2020-10-15 16:29:05](https://github.com/leanprover-community/mathlib/commit/abaf3c2)
feat(algebra/category/Algebra/basic): Add free/forget adjunction. ([#4620](https://github.com/leanprover-community/mathlib/pull/4620))
This PR adds the usual free/forget adjunction for the category of `R`-algebras.
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean
- \+ *def* Algebra.adj
- \+ *def* Algebra.free



## [2020-10-15 16:29:03](https://github.com/leanprover-community/mathlib/commit/07ee11e)
feat(algebra/algebra/basic): Add `map_finsupp_(sum|prod)` to `alg_(hom|equiv)` ([#4603](https://github.com/leanprover-community/mathlib/pull/4603))
Also copies some lemmas from `alg_hom` to `alg_equiv` that were missing
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* alg_equiv.map_div
- \+ *lemma* alg_equiv.map_finsupp_prod
- \+ *lemma* alg_equiv.map_finsupp_sum
- \+ *lemma* alg_equiv.map_inv
- \+/\- *lemma* alg_equiv.map_neg
- \+ *lemma* alg_equiv.map_prod
- \+/\- *lemma* alg_equiv.map_sub
- \+ *lemma* alg_hom.map_finsupp_prod
- \+ *lemma* alg_hom.map_finsupp_sum



## [2020-10-15 16:29:00](https://github.com/leanprover-community/mathlib/commit/bb1f549)
feat(algebra/gcd_monoid): in a gcd_domain a coprime factor of a power is a power ([#4589](https://github.com/leanprover-community/mathlib/pull/4589))
The main result is:
```
theorem associated_pow_of_mul_eq_pow {a b c : α} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : gcd a b = 1) {k : ℕ} (h : a * b = c ^ k) :
  ∃ (d : α), associated (d ^ k) a
```
#### Estimated changes
Modified src/algebra/gcd_monoid.lean
- \+ *lemma* dvd_gcd_mul_of_dvd_mul
- \+ *lemma* dvd_mul_gcd_of_dvd_mul
- \+ *theorem* exists_associated_pow_of_mul_eq_pow
- \+ *theorem* gcd_pow_left_dvd_pow_gcd
- \+ *theorem* gcd_pow_right_dvd_pow_gcd
- \+ *theorem* pow_dvd_of_mul_eq_pow



## [2020-10-15 16:28:58](https://github.com/leanprover-community/mathlib/commit/b01ca81)
feat(data/matrix/notation): simp lemmas for constant-indexed elements ([#4491](https://github.com/leanprover-community/mathlib/pull/4491))
If you use the `![]` vector notation to define a vector, then `simp`
can extract elements `0` and `1` from that vector, but not element `2`
or subsequent elements.  (This shows up in particular in geometry if
defining a triangle with a concrete vector of vertices and then
subsequently doing things that need to extract a particular vertex.)
Add `bit0` and `bit1` `simp` lemmas to allow any element indexed by a
numeral to be extracted (even when the numeral is larger than the
length of the list, such numerals in `fin n` being interpreted mod
`n`).
This ends up quite long; `bit0` and `bit1` semantics mean extracting
alternate elements of the vector in a way that can wrap around to the
start of the vector when the numeral is `n` or larger, so the lemmas
need to deal with constructing such a vector of alternate elements.
As I've implemented it, some definitions also need an extra hypothesis
as an argument to control definitional equalities for the vector
lengths, to avoid problems with non-defeq types when stating
subsequent lemmas.  However, even the example added to
`test/matrix.lean` of extracting element `123456789` of a 5-element
vector is processed quite quickly, so this seems efficient enough.
Note also that there are two `@[simp]` lemmas whose proofs are just
`by simp`, but that are in fact needed for `simp` to complete
extracting some elements and that the `simp` linter does not (at least
when used with `#lint` for this single file) complain about.  I'm not
sure what's going on there, since I didn't think a lemma that `simp`
can prove should normally need to be marked as `@[simp]`.
#### Estimated changes
Modified src/data/fin.lean
- \+ *def* fin.append

Modified src/data/matrix/notation.lean
- \+ *lemma* matrix.cons_append
- \+ *lemma* matrix.cons_vec_alt0
- \+ *lemma* matrix.cons_vec_alt1
- \+ *lemma* matrix.cons_vec_bit0_eq_alt0
- \+ *lemma* matrix.cons_vec_bit1_eq_alt1
- \+ *lemma* matrix.empty_append
- \+ *lemma* matrix.empty_vec_alt0
- \+ *lemma* matrix.empty_vec_alt1
- \+ *def* matrix.vec_alt0
- \+ *lemma* matrix.vec_alt0_append
- \+ *def* matrix.vec_alt1
- \+ *lemma* matrix.vec_alt1_append

Modified test/matrix.lean




## [2020-10-15 15:01:02](https://github.com/leanprover-community/mathlib/commit/85d4b57)
feat(data/polynomial/eval): bit0_comp, bit1_comp ([#4617](https://github.com/leanprover-community/mathlib/pull/4617))
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.bit0_comp
- \+ *lemma* polynomial.bit1_comp



## [2020-10-15 14:04:18](https://github.com/leanprover-community/mathlib/commit/1444fa5)
fix(haar_measure): minor changes ([#4623](https://github.com/leanprover-community/mathlib/pull/4623))
There were some mistakes in the doc, which made it sound like `chaar` and `haar_outer_measure` coincide on compact sets, which is not generally true. 
Also cleanup various proofs.
#### Estimated changes
Modified src/measure_theory/content.lean
- \+ *lemma* measure_theory.outer_measure.of_content_le

Modified src/measure_theory/haar_measure.lean
- \- *lemma* measure_theory.measure.chaar_le_haar_outer_measure
- \+ *lemma* measure_theory.measure.echaar_le_haar_outer_measure
- \+ *lemma* measure_theory.measure.haar.echaar_self
- \+/\- *lemma* measure_theory.measure.haar.is_left_invariant_chaar
- \+ *lemma* measure_theory.measure.haar.is_left_invariant_echaar
- \+/\- *lemma* measure_theory.measure.haar.is_left_invariant_index
- \- *lemma* measure_theory.measure.haar_outer_measure_le_chaar
- \+ *lemma* measure_theory.measure.haar_outer_measure_le_echaar



## [2020-10-15 08:51:18](https://github.com/leanprover-community/mathlib/commit/7559d1c)
lint(data/num/*): add docs and remove some [has_zero] requirements ([#4604](https://github.com/leanprover-community/mathlib/pull/4604))
#### Estimated changes
Modified src/data/num/basic.lean
- \+/\- *def* cast_num
- \- *def* pos_num.sqrt_aux1
- \- *def* pos_num.sqrt_aux

Modified src/data/num/bitwise.lean


Modified src/data/num/lemmas.lean
- \+/\- *theorem* pos_num.cast_bit0
- \+/\- *theorem* pos_num.cast_bit1
- \+/\- *theorem* pos_num.cast_one'
- \+/\- *theorem* pos_num.cast_one



## [2020-10-15 07:30:22](https://github.com/leanprover-community/mathlib/commit/fa65282)
chore(category_theory/monoidal): fix typo in docstrings ([#4625](https://github.com/leanprover-community/mathlib/pull/4625))
#### Estimated changes
Modified src/category_theory/monoidal/category.lean
- \+/\- *lemma* category_theory.monoidal_category.left_unitor_conjugation
- \+/\- *lemma* category_theory.monoidal_category.right_unitor_conjugation
- \+/\- *def* category_theory.tensor_iso



## [2020-10-15 01:11:53](https://github.com/leanprover-community/mathlib/commit/2e1129e)
chore(scripts): update nolints.txt ([#4622](https://github.com/leanprover-community/mathlib/pull/4622))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-14 18:39:39](https://github.com/leanprover-community/mathlib/commit/084b7e7)
chore(algebra/order,data/set/intervals): a few more trivial lemmas ([#4611](https://github.com/leanprover-community/mathlib/pull/4611))
* a few more lemmas for `has_le.le` and `has_lt.lt` namespaces;
* a few lemmas about intersections of intervals;
* fix section header in `topology/algebra/module`.
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* has_le.le.le_or_le
- \+/\- *lemma* has_le.le.le_or_lt
- \+/\- *lemma* has_le.le.lt_or_le
- \+ *lemma* has_lt.lt.lt_or_lt
- \+ *lemma* has_lt.lt.ne'

Modified src/data/set/intervals/basic.lean
- \+ *lemma* set.Ioc_inter_Ioo_of_left_lt
- \+ *lemma* set.Ioc_inter_Ioo_of_right_le
- \+ *lemma* set.Ioo_inter_Ioc_of_left_le
- \+ *lemma* set.Ioo_inter_Ioc_of_right_lt

Modified src/topology/algebra/module.lean




## [2020-10-14 18:39:37](https://github.com/leanprover-community/mathlib/commit/d11eb84)
fix(tactic/suggest): properly remove "Try this: exact " prefix from library_search hole command ([#4609](https://github.com/leanprover-community/mathlib/pull/4609))
[See Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/mechanisms.20to.20search.20through.20mathlilb/near/213223321)
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/suggest.lean




## [2020-10-14 17:31:01](https://github.com/leanprover-community/mathlib/commit/40844f0)
doc(category_theory/comma): Fix markdown rendering in docs ([#4618](https://github.com/leanprover-community/mathlib/pull/4618))
#### Estimated changes
Modified src/category_theory/comma.lean




## [2020-10-14 14:46:32](https://github.com/leanprover-community/mathlib/commit/de46349)
feat(data/set/intervals): more lemmas about `unordered_interval` ([#4607](https://github.com/leanprover-community/mathlib/pull/4607))
Add images/preimages of unordered intervals under common arithmetic operations.
#### Estimated changes
Modified src/data/set/basic.lean
- \+/\- *theorem* set.nonempty.image_const

Modified src/data/set/intervals/unordered_interval.lean
- \+ *lemma* set.image_add_const_interval
- \+ *lemma* set.image_const_add_interval
- \+ *lemma* set.image_const_mul_interval
- \+ *lemma* set.image_const_sub_interval
- \+ *lemma* set.image_div_const_interval
- \+ *lemma* set.image_mul_const_interval
- \+ *lemma* set.image_neg_interval
- \+ *lemma* set.image_sub_const_interval
- \+ *lemma* set.preimage_add_const_interval
- \+ *lemma* set.preimage_const_add_interval
- \+ *lemma* set.preimage_const_mul_interval
- \+ *lemma* set.preimage_const_sub_interval
- \+ *lemma* set.preimage_div_const_interval
- \+ *lemma* set.preimage_mul_const_interval
- \+ *lemma* set.preimage_neg_interval
- \+ *lemma* set.preimage_sub_const_interval



## [2020-10-14 14:46:30](https://github.com/leanprover-community/mathlib/commit/442ef22)
feat(linear_algebra/clifford_algebra): Add a definition derived from exterior_algebra.lean ([#4430](https://github.com/leanprover-community/mathlib/pull/4430))
#### Estimated changes
Added src/linear_algebra/clifford_algebra.lean
- \+ *def* clifford_algebra.as_exterior
- \+ *theorem* clifford_algebra.comp_ι_square_scalar
- \+ *theorem* clifford_algebra.hom_ext
- \+ *def* clifford_algebra.lift
- \+ *theorem* clifford_algebra.lift_comp_ι
- \+ *theorem* clifford_algebra.lift_unique
- \+ *theorem* clifford_algebra.lift_ι_apply
- \+ *inductive* clifford_algebra.rel
- \+ *def* clifford_algebra.ι
- \+ *theorem* clifford_algebra.ι_comp_lift
- \+ *theorem* clifford_algebra.ι_square_scalar
- \+ *def* clifford_algebra

Modified src/linear_algebra/exterior_algebra.lean




## [2020-10-14 15:36:40+02:00](https://github.com/leanprover-community/mathlib/commit/1a1655c)
doc(docs/100): link to actual triangle inequality ([#4614](https://github.com/leanprover-community/mathlib/pull/4614))
#### Estimated changes
Modified docs/100.yaml




## [2020-10-14 09:45:28](https://github.com/leanprover-community/mathlib/commit/f7edbca)
feat(algebra/char_zero): char_zero.infinite ([#4593](https://github.com/leanprover-community/mathlib/pull/4593))
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+/\- *lemma* two_ne_zero'

Modified src/data/fintype/basic.lean
- \+ *lemma* infinite.nonempty



## [2020-10-14 09:45:26](https://github.com/leanprover-community/mathlib/commit/6f5ccc1)
chore(linear_algebra/linear_independent): review API ([#4567](https://github.com/leanprover-community/mathlib/pull/4567))
### API changes
#### New definitions and lemmas
* `subalgebra.to_submodule_equiv`: a linear equivalence between a subalgebra and its coercion
  to a submodule;
* `algebra.to_submodule_bot`: coercion of `⊥ : subalgebra R A` to `submodule R A` is
  `submodule.span {1}`;
* `submodule.disjoint_def'`: one more expansion of `disjoint` for submodules;
* `submodule.is_compl_range_inl_inr`: ranges of `inl` and `inr` are complement submodules;
* `finsupp.supported_inter`, `finsupp.disjojint_supported_supported`,
  `finsupp.disjoint_supported_supported_iff` : more lemmas about `finsupp.supported`;
* `finsupp.total_unique`: formula for `finsupp.total` on a `unique` type;
* `linear_independent_iff_injective_total`, `linear_independent.injective_total` :
  relate `linear_independent R v` to `injective (finsupp.total ι M R v)`;
* `fintype.linear_independent_iff`: a simplified test for
  `linear_independent R v` if the domain of `v` is a `fintype`;
* `linear_independent.map'`: an injective linear map sends linearly
  independent families of vectors to linearly independent families of
  vectors;
* `linear_map.linear_independent_iff`: if `f` is an injective linear
  map, then `f ∘ v` is linearly independent iff `v` is linearly
  independent;
* `linear_independent.disjoint_span_image`: if `v` is a linearly
  independent family of vectors, then the submodules spanned by
  disjoint subfamilies of `v` are disjoint;
* `linear_independent_sum`: a test for linear independence of a
  disjoint union of two families of vectors;
* `linear_independent.sum_type`: `iff.mpr` from `linear_independent_sum`;
* `linear_independent_unique_iff`, `linear_independent_unique`: a test
  for linear independence of a single-vector family;
* `linear_independent_option'`, `linear_independent_option`, `linear_independent.option`:
  test for linear independence of a family indexed by `option ι`;
* `linear_independent_pair`: test for independence of `{v₁, v₂}`;
* `linear_independent_fin_cons`, `linear_independent.fin_cons`,
  `linear_independent_fin_succ`, `linear_independent_fin2`: tests for
  linear independence of families indexed by `i : fin n`.
#### Rename
* `_root_.disjoint_span_singleton` → `submodule.disjoint_span_singleton'`;
* `linear_independent.image` → `linear_independent.map`
* `linear_independent_of_comp` → `linear_independent.of_comp`;
#### Changes in type signature
* `is_basis.to_dual`, `is_basis.to_dual_flip`, `is_basis.to_dual_equiv`: take `B` as an explicit
  argument to improve readability of the pretty-printed output;
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *theorem* algebra.to_submodule_bot
- \+ *def* subalgebra.to_submodule_equiv

Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.option_equiv_sum_punit_coe
- \+/\- *lemma* equiv.option_equiv_sum_punit_none
- \+ *lemma* equiv.set.insert_apply_left
- \+ *lemma* equiv.set.insert_apply_right
- \+ *lemma* equiv.set.insert_symm_apply_inl
- \+ *lemma* equiv.set.insert_symm_apply_inr

Modified src/field_theory/fixed.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.is_compl_range_inl_inr
- \+/\- *lemma* linear_map.sup_range_inl_inr
- \+ *theorem* submodule.disjoint_def'
- \+ *lemma* submodule.disjoint_span_singleton'

Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dual.lean
- \+/\- *def* is_basis.dual_basis
- \+/\- *lemma* is_basis.to_dual_apply_left
- \+/\- *lemma* is_basis.to_dual_apply_right
- \+/\- *lemma* is_basis.to_dual_eq_equiv_fun
- \+/\- *lemma* is_basis.to_dual_eq_repr
- \+/\- *def* is_basis.to_dual_flip
- \+/\- *lemma* is_basis.to_dual_inj
- \+/\- *theorem* is_basis.to_dual_ker
- \+/\- *theorem* is_basis.to_dual_range
- \+/\- *lemma* is_basis.to_dual_swap_eq_to_dual
- \+/\- *lemma* module.dual.eval_apply

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean
- \+ *theorem* finsupp.disjoint_supported_supported
- \+ *theorem* finsupp.disjoint_supported_supported_iff
- \+ *theorem* finsupp.supported_inter
- \+ *theorem* finsupp.total_unique

Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/linear_independent.lean
- \- *lemma* disjoint_span_singleton
- \+ *theorem* fintype.linear_independent_iff
- \+ *lemma* linear_independent.disjoint_span_image
- \+ *lemma* linear_independent.fin_cons
- \- *theorem* linear_independent.image'
- \+ *theorem* linear_independent.image
- \- *lemma* linear_independent.image
- \+ *lemma* linear_independent.map'
- \+ *lemma* linear_independent.map
- \+ *lemma* linear_independent.of_comp
- \- *lemma* linear_independent.of_subtype_range
- \+ *lemma* linear_independent.option
- \+ *lemma* linear_independent.sum_type
- \+ *theorem* linear_independent.to_subtype_range'
- \+ *theorem* linear_independent.to_subtype_range
- \- *lemma* linear_independent.to_subtype_range
- \- *lemma* linear_independent.unique
- \+ *lemma* linear_independent_fin2
- \+ *lemma* linear_independent_fin_cons
- \+ *lemma* linear_independent_fin_succ
- \+ *theorem* linear_independent_iff_injective_total
- \- *lemma* linear_independent_of_comp
- \+ *lemma* linear_independent_option'
- \+ *lemma* linear_independent_option
- \+ *lemma* linear_independent_pair
- \+ *theorem* linear_independent_subtype_range
- \+ *lemma* linear_independent_sum
- \- *lemma* linear_independent_unique
- \+ *lemma* linear_independent_unique_iff



## [2020-10-14 08:24:05](https://github.com/leanprover-community/mathlib/commit/8511729)
refactor(data/int/gcd,ring_theory/int/basic): collect integer divisibility results from various files ([#4572](https://github.com/leanprover-community/mathlib/pull/4572))
Applying comments from PR [#4384](https://github.com/leanprover-community/mathlib/pull/4384). In particular:
1) Move the gcd and lcm results from gcd_monoid to `data/int/gcd.lean` with new proofs (for a few lcm results) that do not need ring theory.
2) Try to collect applications of ring theory to ℕ and ℤ into a new file `ring_theory/int/basic.lean`.
#### Estimated changes
Modified src/algebra/gcd_monoid.lean
- \- *def* associates_int_equiv_nat
- \- *lemma* int.coe_gcd
- \- *lemma* int.coe_lcm
- \- *theorem* int.coe_nat_abs_eq_normalize
- \- *theorem* int.dvd_gcd
- \- *theorem* int.dvd_lcm_left
- \- *theorem* int.dvd_lcm_right
- \- *theorem* int.exists_gcd_one'
- \- *theorem* int.exists_gcd_one
- \- *theorem* int.gcd_assoc
- \- *theorem* int.gcd_comm
- \- *theorem* int.gcd_div
- \- *theorem* int.gcd_div_gcd_div_gcd
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
- \- *theorem* int.ne_zero_of_gcd
- \- *lemma* int.normalize_coe_nat
- \- *lemma* int.normalize_of_neg
- \- *lemma* int.normalize_of_nonneg
- \- *theorem* int.pow_dvd_pow_iff
- \- *lemma* int.prime.dvd_mul'
- \- *lemma* int.prime.dvd_mul
- \- *theorem* irreducible_iff_nat_prime
- \- *lemma* nat.prime_iff_prime
- \- *lemma* nat.prime_iff_prime_int
- \- *lemma* prime_two_or_dvd_of_dvd_two_mul_pow_self_two

Modified src/data/int/gcd.lean
- \+ *theorem* int.dvd_gcd
- \+ *theorem* int.dvd_lcm_left
- \+ *theorem* int.dvd_lcm_right
- \+ *theorem* int.exists_gcd_one'
- \+ *theorem* int.exists_gcd_one
- \+ *theorem* int.gcd_assoc
- \+ *theorem* int.gcd_comm
- \+ *theorem* int.gcd_div
- \+ *theorem* int.gcd_div_gcd_div_gcd
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
- \+ *theorem* int.ne_zero_of_gcd
- \+ *theorem* int.pow_dvd_pow_iff

Deleted src/data/nat/associated.lean
- \- *theorem* nat.irreducible_iff_prime
- \- *theorem* nat.prime_iff

Modified src/data/nat/multiplicity.lean


Deleted src/data/nat/unique_factorization.lean
- \- *theorem* nat.factors_eq

Modified src/data/padics/padic_norm.lean


Modified src/data/real/irrational.lean


Modified src/number_theory/pythagorean_triples.lean


Added src/ring_theory/int/basic.lean
- \+ *def* associates_int_equiv_nat
- \+ *lemma* int.coe_gcd
- \+ *lemma* int.coe_lcm
- \+ *theorem* int.coe_nat_abs_eq_normalize
- \+ *lemma* int.nat_abs_gcd
- \+ *lemma* int.nat_abs_lcm
- \+ *lemma* int.normalize_coe_nat
- \+ *lemma* int.normalize_of_neg
- \+ *lemma* int.normalize_of_nonneg
- \+ *lemma* int.prime.dvd_mul'
- \+ *lemma* int.prime.dvd_mul
- \+ *theorem* irreducible_iff_nat_prime
- \+ *lemma* multiplicity.finite_int_iff
- \+ *lemma* multiplicity.finite_int_iff_nat_abs_finite
- \+ *theorem* nat.factors_eq
- \+ *theorem* nat.irreducible_iff_prime
- \+ *theorem* nat.prime_iff
- \+ *lemma* nat.prime_iff_prime
- \+ *lemma* nat.prime_iff_prime_int
- \+ *lemma* prime_two_or_dvd_of_dvd_two_mul_pow_self_two

Modified src/ring_theory/multiplicity.lean
- \- *lemma* multiplicity.finite_int_iff
- \- *lemma* multiplicity.finite_int_iff_nat_abs_finite



## [2020-10-14 08:24:03](https://github.com/leanprover-community/mathlib/commit/20006f1)
feat(data/polynomial/field_division, field_theory/splitting_field): Splits if enough roots ([#4557](https://github.com/leanprover-community/mathlib/pull/4557))
I have added some lemmas about polynomials that split. In particular the fact that if `p` has as many roots as its degree than it can be written as a product of `(X - a)` and so it splits.
The proof of this for monic polynomial, in `eq_prod_of_card_roots_monic`, is rather messy and can probably be improved a lot.
#### Estimated changes
Modified src/data/polynomial/field_division.lean
- \+ *lemma* polynomial.prod_multiset_X_sub_C_dvd
- \+ *lemma* polynomial.prod_multiset_root_eq_finset_root
- \+ *lemma* polynomial.roots_C_mul

Modified src/data/polynomial/monomial.lean
- \+ *lemma* polynomial.C_eq_zero
- \+/\- *lemma* polynomial.C_inj

Modified src/field_theory/splitting_field.lean
- \+ *lemma* polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C
- \+ *lemma* polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
- \+ *lemma* polynomial.splits_iff_card_roots



## [2020-10-14 01:06:37](https://github.com/leanprover-community/mathlib/commit/1c12bd9)
chore(scripts): update nolints.txt ([#4610](https://github.com/leanprover-community/mathlib/pull/4610))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-13 23:51:13](https://github.com/leanprover-community/mathlib/commit/e2dd1c6)
feat(analysis/normed_space): unconditionally convergent series in `R^n` is absolutely convergent ([#4551](https://github.com/leanprover-community/mathlib/pull/4551))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \- *lemma* has_sum_of_bounded_monoid_hom_of_has_sum
- \- *lemma* has_sum_of_bounded_monoid_hom_of_summable

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* summable_norm_iff

Modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* continuous_linear_map.has_sum_of_summable

Modified src/analysis/specific_limits.lean


Modified src/data/indicator_function.lean
- \+ *lemma* set.indicator_eq_zero_or_self

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable.of_neg
- \+ *lemma* summable_abs_iff
- \+ *lemma* summable_neg_iff
- \+ *lemma* summable_subtype_and_compl



## [2020-10-13 21:59:53](https://github.com/leanprover-community/mathlib/commit/2543b68)
refactor(*): migrate to `dense` API ([#4447](https://github.com/leanprover-community/mathlib/pull/4447))
@PatrickMassot introduced `dense` in [#4399](https://github.com/leanprover-community/mathlib/pull/4399). In this PR I review the API and migrate many definitions and lemmas
to use `dense s` instead of `closure s = univ`. I also generalize `second_countable_of_separable` to a `uniform_space`
with a countably generated uniformity filter.
## API changes
### Use `dense` or `dense_range` instead of `closure _ = univ`
#### Lemmas
- `has_fderiv_within_at.unique_diff_within_at`;
- `exists_dense_seq`;
- `dense_Inter_of_open_nat`;
- `dense_sInter_of_open`;
- `dense_bInter_of_open`;
- `dense_Inter_of_open`;
- `dense_sInter_of_Gδ`;
- `dense_bInter_of_Gδ`;
- `eventually_residual`;
- `mem_residual`;
- `dense_bUnion_interior_of_closed`;
- `dense_sUnion_interior_of_closed`;
- `dense_Union_interior_of_closed`;
- `Kuratowski_embeddinng.embedding_of_subset_isometry`;
- `continuous_extend_from`;
#### Definitions
- `unique_diff_within_at`;
- `residual`;
### Rename
- `submodule.linear_eq_on` → `linear_map.eq_on_span`, `linear_map.eq_on_span'`;
- `submodule.linear_map.ext_on` → `linear_map.ext_on_range`;
- `filter.is_countably_generated.has_antimono_basis` →
  `filter.is_countably_generated.exists_antimono_basis`;
- `exists_countable_closure_eq_univ` → `exists_countable_dense`, use `dense`;
- `dense_seq_dense` → `dense_range_dense_seq`, use `dense`;
- `dense_range.separable_space` is now `protected`;
- `dense_of_subset_dense` → `dense.mono`;
- `dense_inter_of_open_left` → `dense.inter_of_open_left`;
- `dense_inter_of_open_right` → `dense.inter_of_open_right`;
- `continuous.dense_image_of_dense_range` → `dense_range.dense_image`;
- `dense_range.inhabited`, `dense_range.nonempty`: changed API, TODO;
- `quotient_dense_of_dense` → `dense.quotient`, use `dense`;
- `dense_inducing.separable` → `dense_inducing.separable_space`, add `protected`;
- `dense_embedding.separable` → `dense_embedding.separable_space`, add `protected`;
- `dense_inter_of_Gδ` → `dense.inter_of_Gδ`;
- `stone_cech_unit_dense` → `dense_range_stone_cech_unit`;
- `abstract_completion.dense'` → `abstract_completion.closure_range`;
- `Cauchy.pure_cauchy_dense` → `Cauchy.dense_range_pure_cauchy`;
- `completion.dense` → `completion.dense_range_coe`;
- `completion.dense₂` → `completion.dense_range_coe₂`;
- `completion.dense₃` → `completion.dense_range_coe₃`;
### New
- `has_fderiv_within_at.unique_on` : if `f'` and `f₁'` are two derivatives of `f`
  within `s` at `x`, then they are equal on the tangent cone to `s` at `x`;
- `local_homeomorph.mdifferentiable.mfderiv_bijective`,
  `local_homeomorph.mdifferentiable.mfderiv_surjective`
- `continuous_linear_map.eq_on_closure_span`: if two continuous linear maps are equal on `s`,
  then they are equal on `closure (submodule.span s)`;
- `continuous_linear_map.ext_on`: if two continuous linear maps are equal on a set `s` such that
  `submodule.span s` is dense, then they are equal;
- `dense_closure`: `closure s` is dense iff `s` is dense;
- `dense.of_closure`, `dense.closure`: aliases for `dense_closure.mp` and `dense_closure.mpr`;
- `dense_univ`: `univ` is dense;
- `dense.inter_open_nonempty`: alias for `dense_iff_inter_open.mp`;
- `dense.nonempty_iff`: if `s : set α` is a dense set, then `s` is nonempty iff `α` is nonempty;
- `dense.nonempty`: a dense set in a nonempty type is nonempty;
- `dense_range.some`: given a function with `dense_range` and a point in the codomain, returns a point in the domain;
- `function.surjective.dense_range`: a surjective function has dense range;
- `continuous.range_subset_closure_image_dense`: closure of the image of a dense set under
  a continuous function includes the range of this function;
- `dense_range.dense_of_maps_to`: if a function with dense range maps a dense set `s` to `t`, then
  `t` is dense in the codomain;
- `dense_range.quotient`;
- `dense.prod`: product of two dense sets is dense in the product;
- `set.eq_on.closure`;
- `continuous.ext_on`;
- `linear_map.ext_on`
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *theorem* has_fderiv_within_at.unique_on

Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/geometry/manifold/mfderiv.lean
- \+ *lemma* local_homeomorph.mdifferentiable.mfderiv_bijective
- \+ *lemma* local_homeomorph.mdifferentiable.mfderiv_surjective

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.eq_on_span'
- \+ *lemma* linear_map.eq_on_span
- \+ *lemma* linear_map.ext_on
- \+ *lemma* linear_map.ext_on_range
- \- *lemma* submodule.linear_eq_on
- \- *lemma* submodule.linear_map.ext_on

Modified src/linear_algebra/basis.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.eq_on_closure_span
- \+ *lemma* continuous_linear_map.ext_on

Modified src/topology/bases.lean
- \- *lemma* dense_range.separable_space
- \+ *lemma* topological_space.dense_range_dense_seq
- \- *lemma* topological_space.dense_seq_dense
- \- *lemma* topological_space.exists_countable_closure_eq_univ
- \+/\- *lemma* topological_space.exists_dense_seq

Modified src/topology/basic.lean
- \- *lemma* continuous.dense_image_of_dense_range
- \+ *lemma* continuous.range_subset_closure_image_dense
- \+ *lemma* dense.inter_of_open_left
- \+ *lemma* dense.inter_of_open_right
- \+ *lemma* dense.mono
- \+ *lemma* dense.nonempty
- \+ *lemma* dense.nonempty_iff
- \+ *lemma* dense_closure
- \- *lemma* dense_inter_of_open_left
- \- *lemma* dense_inter_of_open_right
- \- *lemma* dense_of_subset_dense
- \+/\- *lemma* dense_range.comp
- \+ *lemma* dense_range.dense_image
- \+ *lemma* dense_range.dense_of_maps_to
- \- *def* dense_range.inhabited
- \+/\- *lemma* dense_range.nonempty
- \+ *lemma* dense_range.nonempty_iff
- \+ *def* dense_range.some
- \+ *lemma* dense_univ
- \+ *lemma* function.surjective.dense_range

Modified src/topology/constructions.lean
- \+ *lemma* dense.prod
- \+ *lemma* dense.quotient
- \- *lemma* dense_range.prod
- \+ *lemma* dense_range.prod_map
- \+ *lemma* dense_range.quotient
- \- *lemma* quotient_dense_of_dense

Modified src/topology/dense_embedding.lean
- \- *lemma* dense_embedding.separable
- \- *lemma* dense_inducing.separable

Modified src/topology/extend_from_subset.lean
- \+/\- *lemma* continuous_extend_from

Modified src/topology/instances/real.lean


Modified src/topology/metric_space/baire.lean
- \+ *theorem* dense.inter_of_Gδ
- \- *theorem* dense_inter_of_Gδ
- \+/\- *lemma* mem_residual

Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/isometry.lean
- \+/\- *lemma* Kuratowski_embedding.embedding_of_subset_isometry

Modified src/topology/separation.lean
- \+ *lemma* continuous.ext_on
- \+ *lemma* set.eq_on.closure

Modified src/topology/stone_cech.lean
- \+ *lemma* dense_range_pure
- \+ *lemma* dense_range_stone_cech_unit
- \+ *lemma* induced_topology_pure
- \- *lemma* stone_cech_unit_dense

Modified src/topology/uniform_space/abstract_completion.lean
- \+ *lemma* abstract_completion.closure_range
- \- *lemma* abstract_completion.dense'

Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/completion.lean
- \+ *lemma* Cauchy.dense_range_pure_cauchy
- \- *lemma* Cauchy.pure_cauchy_dense
- \- *lemma* uniform_space.completion.dense
- \+ *lemma* uniform_space.completion.dense_range_coe
- \+ *lemma* uniform_space.completion.dense_range_coe₂
- \+ *lemma* uniform_space.completion.dense_range_coe₃
- \- *lemma* uniform_space.completion.dense₂
- \- *lemma* uniform_space.completion.dense₃



## [2020-10-13 19:48:34](https://github.com/leanprover-community/mathlib/commit/fde3d78)
chore(multiset): dedicated notation for multiset.cons ([#4600](https://github.com/leanprover-community/mathlib/pull/4600))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/data/dfinsupp.lean


Modified src/data/finmap.lean


Modified src/data/finset/basic.lean
- \+/\- *theorem* finset.cons_val
- \+/\- *theorem* finset.insert_val'
- \+/\- *theorem* finset.insert_val_of_not_mem
- \+/\- *theorem* finset.mk_cons
- \+/\- *theorem* finset.singleton_val

Modified src/data/finset/pi.lean


Modified src/data/finsupp/basic.lean


Modified src/data/fintype/basic.lean


Modified src/data/multiset/antidiagonal.lean
- \+/\- *theorem* multiset.antidiagonal_cons
- \+/\- *theorem* multiset.antidiagonal_zero

Modified src/data/multiset/basic.lean
- \+/\- *theorem* multiset.add_cons
- \+/\- *theorem* multiset.card_cons
- \+/\- *theorem* multiset.card_eq_one
- \+/\- *theorem* multiset.card_singleton
- \+/\- *theorem* multiset.cons_add
- \+/\- *theorem* multiset.cons_bind
- \+/\- *theorem* multiset.cons_erase
- \+/\- *theorem* multiset.cons_inj_right
- \+/\- *theorem* multiset.cons_inter_distrib
- \+/\- *theorem* multiset.cons_le_cons
- \+/\- *theorem* multiset.cons_le_cons_iff
- \+/\- *lemma* multiset.cons_ne_zero
- \+/\- *theorem* multiset.cons_subset
- \+/\- *theorem* multiset.cons_swap
- \+/\- *theorem* multiset.cons_union_distrib
- \+/\- *theorem* multiset.count_cons_of_ne
- \+/\- *theorem* multiset.count_cons_self
- \+/\- *theorem* multiset.count_le_count_cons
- \+/\- *theorem* multiset.count_singleton
- \+/\- *theorem* multiset.countp_cons_of_neg
- \+/\- *theorem* multiset.countp_cons_of_pos
- \+/\- *theorem* multiset.disjoint_singleton
- \+/\- *theorem* multiset.erase_cons_head
- \+/\- *theorem* multiset.erase_cons_tail
- \+/\- *theorem* multiset.erase_le_iff_le_cons
- \+/\- *theorem* multiset.exists_cons_of_mem
- \+/\- *theorem* multiset.filter_cons_of_neg
- \+/\- *theorem* multiset.filter_cons_of_pos
- \+/\- *theorem* multiset.foldl_cons
- \+/\- *theorem* multiset.foldr_cons
- \+/\- *theorem* multiset.join_cons
- \+/\- *theorem* multiset.le_cons_erase
- \+/\- *theorem* multiset.le_cons_of_not_mem
- \+/\- *theorem* multiset.le_cons_self
- \+/\- *theorem* multiset.lt_cons_self
- \+/\- *theorem* multiset.lt_iff_cons_le
- \+/\- *theorem* multiset.map_cons
- \+/\- *theorem* multiset.mem_cons
- \+/\- *lemma* multiset.mem_cons_of_mem
- \+/\- *theorem* multiset.mem_cons_self
- \+/\- *theorem* multiset.mem_singleton
- \+/\- *theorem* multiset.mem_singleton_self
- \+/\- *theorem* multiset.prod_cons
- \+/\- *theorem* multiset.prod_singleton
- \+/\- *theorem* multiset.product_singleton
- \+/\- *lemma* multiset.repeat_one
- \+/\- *theorem* multiset.repeat_subset_singleton
- \+/\- *lemma* multiset.repeat_succ
- \+/\- *theorem* multiset.singleton_add
- \+/\- *theorem* multiset.singleton_coe
- \+/\- *theorem* multiset.singleton_disjoint
- \+/\- *theorem* multiset.singleton_eq_singleton
- \+/\- *theorem* multiset.singleton_inj
- \+/\- *theorem* multiset.singleton_le
- \+/\- *theorem* multiset.singleton_ne_zero
- \+/\- *theorem* multiset.sub_cons
- \+/\- *lemma* multiset.zero_ne_cons

Modified src/data/multiset/erase_dup.lean
- \+/\- *theorem* multiset.erase_dup_singleton

Modified src/data/multiset/finset_ops.lean
- \+/\- *theorem* multiset.ndinsert_of_not_mem
- \+/\- *theorem* multiset.ndinsert_zero

Modified src/data/multiset/fold.lean
- \+/\- *theorem* multiset.fold_cons'_left
- \+/\- *theorem* multiset.fold_cons'_right
- \+/\- *theorem* multiset.fold_cons_right
- \+/\- *theorem* multiset.fold_singleton

Modified src/data/multiset/functor.lean
- \+/\- *lemma* multiset.pure_def

Modified src/data/multiset/gcd.lean
- \+/\- *lemma* multiset.gcd_singleton
- \+/\- *lemma* multiset.lcm_singleton

Modified src/data/multiset/intervals.lean
- \+/\- *theorem* multiset.Ico.eq_cons
- \+/\- *theorem* multiset.Ico.succ_top

Modified src/data/multiset/lattice.lean
- \+/\- *lemma* multiset.inf_singleton
- \+/\- *lemma* multiset.sup_singleton

Modified src/data/multiset/nat_antidiagonal.lean


Modified src/data/multiset/nodup.lean
- \+/\- *theorem* multiset.nodup_cons
- \+/\- *theorem* multiset.nodup_cons_of_nodup
- \+/\- *theorem* multiset.nodup_iff_le
- \+/\- *lemma* multiset.nodup_iff_ne_cons_cons
- \+/\- *theorem* multiset.nodup_of_nodup_cons
- \+/\- *theorem* multiset.nodup_singleton
- \+/\- *theorem* multiset.not_mem_of_nodup_cons
- \+/\- *theorem* multiset.not_nodup_pair

Modified src/data/multiset/pi.lean
- \+/\- *def* multiset.pi.cons
- \+/\- *lemma* multiset.pi.cons_same
- \+/\- *lemma* multiset.pi_zero

Modified src/data/multiset/powerset.lean
- \+/\- *theorem* multiset.powerset_zero

Modified src/data/multiset/range.lean
- \+/\- *theorem* multiset.range_succ

Modified src/data/multiset/sections.lean
- \+/\- *lemma* multiset.sections_zero

Modified src/data/pnat/factors.lean
- \+/\- *def* prime_multiset.of_prime

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* polynomial.roots_X_sub_C

Modified src/data/set/finite.lean


Modified src/data/sym.lean


Modified src/field_theory/splitting_field.lean


Modified src/group_theory/perm/sign.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2020-10-13 18:44:25](https://github.com/leanprover-community/mathlib/commit/7368d71)
chore(number_theory/arithmetic_function): Define in terms of zero_hom ([#4606](https://github.com/leanprover-community/mathlib/pull/4606))
No need to write these proofs in two places
#### Estimated changes
Modified src/number_theory/arithmetic_function.lean
- \+/\- *lemma* nat.arithmetic_function.map_zero
- \+/\- *lemma* nat.arithmetic_function.zero_apply
- \+ *def* nat.arithmetic_function
- \- *structure* nat.arithmetic_function



## [2020-10-13 16:46:02](https://github.com/leanprover-community/mathlib/commit/b1c1033)
feat(analysis/normed_space/operator_norm): construct a continuous_linear_equiv from a linear_equiv and bounds in both directions ([#4583](https://github.com/leanprover-community/mathlib/pull/4583))
#### Estimated changes
Modified src/analysis/normed_space/operator_norm.lean
- \+ *def* linear_equiv.to_continuous_linear_equiv_of_bounds



## [2020-10-13 16:46:00](https://github.com/leanprover-community/mathlib/commit/7cff825)
feat(data/vector2): induction principle, define last, and some lemmas (blocked by [#4578](https://github.com/leanprover-community/mathlib/pull/4578)) ([#4554](https://github.com/leanprover-community/mathlib/pull/4554))
#### Estimated changes
Modified src/data/vector2.lean
- \+ *def* vector.induction_on
- \+ *def* vector.last
- \+ *lemma* vector.last_def
- \+ *lemma* vector.nth_cons_nil
- \+ *lemma* vector.reverse_nth_zero
- \+ *lemma* vector.singleton_tail
- \+ *lemma* vector.tail_nil
- \+ *lemma* vector.to_list_reverse
- \+ *lemma* vector.to_list_singleton



## [2020-10-13 15:24:50](https://github.com/leanprover-community/mathlib/commit/71bb9f2)
chore(linear_algebra/finsupp): Implement lsingle in terms of single_add_hom ([#4605](https://github.com/leanprover-community/mathlib/pull/4605))
While not shorter, this makes it easier to relate the two definitions
#### Estimated changes
Modified src/linear_algebra/finsupp.lean
- \+/\- *def* finsupp.lapply



## [2020-10-13 14:02:34](https://github.com/leanprover-community/mathlib/commit/ca6af1c)
chore(algebra/monoid_algebra): Replace `algebra_map'` with `single_(zero|one)_ring_hom` ([#4582](https://github.com/leanprover-community/mathlib/pull/4582))
`algebra_map'` is now trivially equal to `single_(zero|one)_ring_hom.comp`, so is no longer needed.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \- *def* add_monoid_algebra.algebra_map'
- \+ *def* add_monoid_algebra.single_zero_alg_hom
- \+ *def* add_monoid_algebra.single_zero_ring_hom
- \- *def* monoid_algebra.algebra_map'
- \+ *def* monoid_algebra.single_one_alg_hom
- \+ *def* monoid_algebra.single_one_ring_hom

Modified src/data/polynomial/monomial.lean
- \+/\- *def* polynomial.C



## [2020-10-13 11:12:28](https://github.com/leanprover-community/mathlib/commit/9f9344d)
feat(algebra/char_p): fields with a hom between them have same char ([#4594](https://github.com/leanprover-community/mathlib/pull/4594))
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *lemma* ring_hom.char_p_iff_char_p



## [2020-10-13 09:47:17](https://github.com/leanprover-community/mathlib/commit/dd8bf2c)
feat(data/polynomial/eval): easy lemmas + speedup ([#4596](https://github.com/leanprover-community/mathlib/pull/4596))
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean
- \- *lemma* polynomial.mul_comp

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.comp_assoc
- \+ *lemma* polynomial.eval₂_congr
- \+ *lemma* polynomial.mul_comp
- \+ *lemma* polynomial.neg_comp
- \+ *lemma* polynomial.sub_comp



## [2020-10-13 06:30:22](https://github.com/leanprover-community/mathlib/commit/7fff35f)
chore(algebra/pointwise): remove `@[simp]` from `singleton_one`/`singleton_zero` ([#4592](https://github.com/leanprover-community/mathlib/pull/4592))
This lemma simplified `{1}` and `{0}` to `1` and `0` making them unusable for other `singleton` lemmas.
#### Estimated changes
Modified src/algebra/pointwise.lean
- \+ *lemma* set.preimage_mul_left_singleton
- \+ *lemma* set.preimage_mul_right_singleton

Modified src/ring_theory/fractional_ideal.lean


Modified src/topology/metric_space/gromov_hausdorff.lean




## [2020-10-13 06:30:20](https://github.com/leanprover-community/mathlib/commit/c9ae9e6)
chore(linear_algebra/dimension): more same-universe versions of `is_basis.mk_eq_dim` ([#4591](https://github.com/leanprover-community/mathlib/pull/4591))
While all the `lift` magic is good for general theory, it is not that convenient for the case when everything is in `Type`.
* add `mk_eq_mk_of_basis'`: same-universe version of `mk_eq_mk_of_basis`;
* generalize `is_basis.mk_eq_dim''` to any index type in the same universe as `V`, not necessarily `s : set V`;
* reorder lemmas to optimize the total length of the proofs;
* drop one `finite_dimensional` assumption in `findim_of_infinite_dimensional`.
#### Estimated changes
Modified src/field_theory/tower.lean
- \+/\- *theorem* finite_dimensional.findim_mul_findim

Modified src/linear_algebra/dimension.lean
- \+/\- *theorem* is_basis.mk_eq_dim''
- \+ *theorem* mk_eq_mk_of_basis'

Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.findim_of_infinite_dimensional



## [2020-10-13 04:39:56](https://github.com/leanprover-community/mathlib/commit/766d860)
fix(big_operators): fix imports ([#4588](https://github.com/leanprover-community/mathlib/pull/4588))
Previously `algebra.big_operators.pi` imported `algebra.big_operators.default`. That import direction is now reversed.
#### Estimated changes
Modified src/algebra/big_operators/default.lean


Modified src/algebra/big_operators/pi.lean


Modified src/data/polynomial/iterated_deriv.lean


Modified src/deprecated/submonoid.lean




## [2020-10-13 03:48:58](https://github.com/leanprover-community/mathlib/commit/505b969)
feat(archive/imo): formalize IMO 1962 problem Q1 ([#4450](https://github.com/leanprover-community/mathlib/pull/4450))
The problem statement:
Find the smallest natural number $n$ which has the following properties:
(a) Its decimal representation has 6 as the last digit.
(b) If the last digit 6 is erased and placed in front of the remaining digits,
the resulting number is four times as large as the original number $n$.
This is a proof that 153846 is the smallest member of the set satisfying these conditions.
#### Estimated changes
Added archive/imo/imo1962_q1.lean
- \+ *lemma* case_0_digit
- \+ *lemma* case_1_digit
- \+ *lemma* case_2_digit
- \+ *lemma* case_3_digit
- \+ *lemma* case_4_digit
- \+ *lemma* case_5_digit
- \+ *lemma* case_more_digits
- \+ *lemma* helper_5_digit
- \+ *theorem* imo1962_q1
- \+ *lemma* no_smaller_solutions
- \+ *abbreviation* problem_predicate'
- \+ *def* problem_predicate
- \+ *lemma* satisfied_by_153846
- \+ *lemma* without_digits



## [2020-10-13 02:01:14](https://github.com/leanprover-community/mathlib/commit/e957269)
chore(scripts): update nolints.txt ([#4587](https://github.com/leanprover-community/mathlib/pull/4587))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


Modified scripts/nolints.txt




## [2020-10-13 02:01:12](https://github.com/leanprover-community/mathlib/commit/9eb341a)
feat(mv_polynomial): minor simplification in coeff_mul ([#4586](https://github.com/leanprover-community/mathlib/pull/4586))
The proof was already golfed in [#4472](https://github.com/leanprover-community/mathlib/pull/4472).
Use `×` instead of `sigma`.
Shorten one line over 100 chars.
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean




## [2020-10-13 02:01:09](https://github.com/leanprover-community/mathlib/commit/7dcaee1)
feat(archive/imo): formalize IMO 1962 problem 4 ([#4518](https://github.com/leanprover-community/mathlib/pull/4518))
The problem statement: Solve the equation `cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1`.
There are a bunch of trig formulas I proved along the way; there are sort of an infinite number of trig formulas so I'm open to feedback on whether some should go in the core libraries. Also possibly some of them have a shorter proof that would render the lemma unnecessary.
For what it's worth, the actual method of solution is not how a human would do it; a more intuitive human method is to simplify in terms of `cos x` and then solve, but I think this is simpler in Lean because it doesn't rely on solving `cos x = y` for several different `y`.
#### Estimated changes
Added archive/imo/imo1962_q4.lean
- \+ *lemma* alt_equiv
- \+ *def* alt_formula
- \+ *lemma* cos_sum_equiv
- \+ *lemma* finding_zeros
- \+ *theorem* imo1962_q4
- \+ *def* problem_equation
- \+ *def* solution_set
- \+ *lemma* solve_cos2_half
- \+ *lemma* solve_cos3x_0

Modified src/data/complex/exponential.lean
- \+ *lemma* complex.cos_square'
- \+ *lemma* complex.cos_three_mul
- \+ *lemma* complex.cosh_square
- \+ *lemma* complex.cosh_three_mul
- \+ *lemma* complex.cosh_two_mul
- \+ *lemma* complex.sin_three_mul
- \+ *lemma* complex.sinh_square
- \+ *lemma* complex.sinh_three_mul
- \+ *lemma* complex.sinh_two_mul
- \+ *lemma* real.cos_square'
- \+ *lemma* real.cos_three_mul
- \+ *lemma* real.cos_two_mul'
- \+ *lemma* real.cosh_add_sinh
- \+ *lemma* real.cosh_square
- \+ *lemma* real.cosh_three_mul
- \+ *lemma* real.cosh_two_mul
- \+ *lemma* real.sin_three_mul
- \+ *lemma* real.sinh_add_cosh
- \+ *lemma* real.sinh_square
- \+ *lemma* real.sinh_three_mul
- \+ *lemma* real.sinh_two_mul



## [2020-10-13 02:01:07](https://github.com/leanprover-community/mathlib/commit/b231d8e)
feat(archive/imo): formalize IMO 1960 problem 1 ([#4366](https://github.com/leanprover-community/mathlib/pull/4366))
The problem:
Determine all three-digit numbers $N$ having the property that $N$ is divisible by 11, and
$\dfrac{N}{11}$ is equal to the sum of the squares of the digits of $N$.
Art of Problem Solving offers three solutions to this problem - https://artofproblemsolving.com/wiki/index.php/1960_IMO_Problems/Problem_1 - but they all involve a fairly large amount of bashing through cases and solving basic algebra. This proof is also essentially bashing through cases, using the `iterate` tactic and calls to `norm_num`.
#### Estimated changes
Added archive/imo/imo1960_q1.lean
- \+ *lemma* ge_100
- \+ *theorem* imo1960_q1
- \+ *lemma* left_direction
- \+ *lemma* lt_1000
- \+ *lemma* not_zero
- \+ *def* problem_predicate
- \+ *lemma* right_direction
- \+ *def* search_up_to
- \+ *lemma* search_up_to_end
- \+ *lemma* search_up_to_start
- \+ *lemma* search_up_to_step
- \+ *def* solution_predicate
- \+ *def* sum_of_squares



## [2020-10-12 23:17:41](https://github.com/leanprover-community/mathlib/commit/a6d445d)
feat(data/finsupp): Add `map_finsupp_prod` to homs ([#4585](https://github.com/leanprover-community/mathlib/pull/4585))
This is a convenience alias for `map_prod`, which is awkward to use.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *lemma* monoid_hom.map_finsupp_prod
- \+ *lemma* mul_equiv.map_finsupp_prod
- \+ *lemma* ring_hom.map_finsupp_prod
- \+ *lemma* ring_hom.map_finsupp_sum



## [2020-10-12 23:17:40](https://github.com/leanprover-community/mathlib/commit/d1bb5ea)
feat(topology/category/Compactum): Compact Hausdorff spaces ([#4555](https://github.com/leanprover-community/mathlib/pull/4555))
This PR provides the equivalence between the category of compact Hausdorff topological spaces and the category of algebras for the ultrafilter monad.
## Notation
1. `Compactum` is the category of algebras for the ultrafilter monad. It's a wrapper around `monad.algebra (of_type_functor $ ultrafilter)`.
2. `CompHaus` is the full subcategory of `Top` consisting of topological spaces which are compact and Hausdorff.
#### Estimated changes
Added src/data/set/constructions.lean
- \+ *inductive* has_finite_inter.finite_inter_closure
- \+ *def* has_finite_inter.finite_inter_closure_has_finite_inter
- \+ *lemma* has_finite_inter.finite_inter_closure_insert
- \+ *lemma* has_finite_inter.finite_inter_mem
- \+ *structure* has_finite_inter

Modified src/order/filter/ultrafilter.lean
- \+ *lemma* filter.ne_empty_of_mem_ultrafilter
- \+ *lemma* filter.nonempty_of_mem_ultrafilter
- \+ *lemma* filter.ultrafilter_iff_compl_mem_iff_not_mem'

Modified src/topology/basic.lean
- \+ *def* Lim'
- \+ *def* filter.ultrafilter.Lim

Added src/topology/category/CompHaus.lean
- \+ *structure* CompHaus
- \+ *def* CompHaus_to_Top

Added src/topology/category/Compactum.lean
- \+ *lemma* Compactum.Lim_eq_str
- \+ *def* Compactum.adj
- \+ *lemma* Compactum.cl_eq_closure
- \+ *lemma* Compactum.continuous_of_hom
- \+ *def* Compactum.forget
- \+ *def* Compactum.free
- \+ *def* Compactum.hom_of_continuous
- \+ *def* Compactum.incl
- \+ *lemma* Compactum.is_closed_cl
- \+ *theorem* Compactum.is_closed_iff
- \+ *def* Compactum.join
- \+ *lemma* Compactum.join_distrib
- \+ *lemma* Compactum.le_nhds_of_str_eq
- \+ *def* Compactum.str
- \+ *lemma* Compactum.str_eq_of_le_nhds
- \+ *lemma* Compactum.str_hom_commute
- \+ *lemma* Compactum.str_incl
- \+ *def* Compactum
- \+ *lemma* Compactum_to_CompHaus.faithful
- \+ *def* Compactum_to_CompHaus.full
- \+ *def* Compactum_to_CompHaus

Modified src/topology/separation.lean
- \+ *lemma* is_open_iff_ultrafilter'



## [2020-10-12 23:17:37](https://github.com/leanprover-community/mathlib/commit/bc77a23)
feat(data/list/*): add left- and right-biased versions of map₂ and zip ([#4512](https://github.com/leanprover-community/mathlib/pull/4512))
When given lists of different lengths, `map₂` and `zip` truncate the output to
the length of the shorter input list. This commit adds variations on `map₂` and
`zip` whose output is always as long as the left/right input.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.map₂_flip
- \+ *theorem* list.map₂_left'_nil_right
- \+ *theorem* list.map₂_left_eq_map₂
- \+ *theorem* list.map₂_left_eq_map₂_left'
- \+ *theorem* list.map₂_left_nil_right
- \+ *theorem* list.map₂_right'_cons_cons
- \+ *theorem* list.map₂_right'_nil_cons
- \+ *theorem* list.map₂_right'_nil_left
- \+ *theorem* list.map₂_right'_nil_right
- \+ *theorem* list.map₂_right_cons_cons
- \+ *theorem* list.map₂_right_eq_map₂
- \+ *theorem* list.map₂_right_eq_map₂_right'
- \+ *theorem* list.map₂_right_nil_cons
- \+ *theorem* list.map₂_right_nil_left
- \+ *theorem* list.map₂_right_nil_right
- \+ *theorem* list.zip_left'_cons_cons
- \+ *theorem* list.zip_left'_cons_nil
- \+ *theorem* list.zip_left'_nil_left
- \+ *theorem* list.zip_left'_nil_right
- \+ *theorem* list.zip_left_cons_cons
- \+ *theorem* list.zip_left_cons_nil
- \+ *theorem* list.zip_left_eq_zip_left'
- \+ *theorem* list.zip_left_nil_left
- \+ *theorem* list.zip_left_nil_right
- \+ *theorem* list.zip_right'_cons_cons
- \+ *theorem* list.zip_right'_nil_cons
- \+ *theorem* list.zip_right'_nil_left
- \+ *theorem* list.zip_right'_nil_right
- \+ *theorem* list.zip_right_cons_cons
- \+ *theorem* list.zip_right_eq_zip_right'
- \+ *theorem* list.zip_right_nil_cons
- \+ *theorem* list.zip_right_nil_left
- \+ *theorem* list.zip_right_nil_right

Modified src/data/list/defs.lean
- \+ *def* list.map₂_left'
- \+ *def* list.map₂_left
- \+ *def* list.map₂_right'
- \+ *def* list.map₂_right
- \+ *def* list.zip_left'
- \+ *def* list.zip_left
- \+ *def* list.zip_right'
- \+ *def* list.zip_right



## [2020-10-12 20:50:13](https://github.com/leanprover-community/mathlib/commit/d3d70f1)
chore(algebra/order*): move `abs`/`min`/`max`, review ([#4581](https://github.com/leanprover-community/mathlib/pull/4581))
* make `algebra.ordered_group` import `algebra.order_functions`, not vice versa;
* move some proofs from `algebra.ordered_functions` to `algebra.ordered_group` and `algebra.ordered_ring`;
* deduplicate API;
* golf some proofs.
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/order_functions.lean
- \- *lemma* abs_abs_sub_le_abs_sub
- \- *lemma* abs_add
- \- *lemma* abs_eq
- \- *lemma* abs_eq_zero
- \- *theorem* abs_le
- \- *theorem* abs_le_abs
- \- *lemma* abs_le_max_abs_abs
- \- *lemma* abs_lt
- \- *lemma* abs_max_sub_max_le_abs
- \- *lemma* abs_nonpos_iff
- \- *lemma* abs_one
- \- *lemma* abs_pos_iff
- \- *lemma* abs_sub_le_iff
- \- *lemma* abs_sub_lt_iff
- \- *lemma* fn_min_mul_fn_max
- \- *lemma* lt_abs
- \- *lemma* max_le_add_of_nonneg
- \- *lemma* max_mul_mul_le_max_mul_max
- \- *lemma* max_mul_of_nonneg
- \- *lemma* max_sub_min_eq_abs'
- \- *lemma* max_sub_min_eq_abs
- \- *lemma* max_zero_sub_eq_self
- \- *lemma* min_le_add_of_nonneg_left
- \- *lemma* min_le_add_of_nonneg_right
- \- *lemma* min_mul_max
- \- *lemma* min_mul_of_nonneg
- \- *lemma* min_sub
- \- *lemma* mul_max_of_nonneg
- \- *lemma* mul_min_of_nonneg
- \- *lemma* sub_abs_le_abs_sub

Modified src/algebra/ordered_field.lean
- \+ *lemma* max_div_div_right
- \+ *lemma* max_div_div_right_of_nonpos
- \+ *lemma* min_div_div_right
- \+ *lemma* min_div_div_right_of_nonpos

Modified src/algebra/ordered_group.lean
- \+/\- *lemma* abs_abs
- \+ *lemma* abs_abs_sub_abs_le_abs_sub
- \+ *lemma* abs_add
- \- *lemma* abs_add_le_abs_add_abs
- \+ *lemma* abs_eq
- \+ *lemma* abs_eq_zero
- \+ *theorem* abs_le'
- \+ *theorem* abs_le
- \+ *theorem* abs_le_abs
- \+ *lemma* abs_le_max_abs_abs
- \- *lemma* abs_le_of_le_of_neg_le
- \+ *lemma* abs_lt
- \- *lemma* abs_lt_of_lt_of_neg_lt
- \+ *lemma* abs_max_sub_max_le_abs
- \+/\- *lemma* abs_neg
- \+ *lemma* abs_nonpos_iff
- \+/\- *lemma* abs_of_neg
- \+/\- *lemma* abs_of_nonneg
- \+/\- *lemma* abs_of_nonpos
- \+/\- *lemma* abs_of_pos
- \+ *lemma* abs_pos
- \- *lemma* abs_pos_of_ne_zero
- \+/\- *lemma* abs_pos_of_neg
- \+/\- *lemma* abs_pos_of_pos
- \+ *lemma* abs_sub_le_iff
- \+ *lemma* abs_sub_lt_iff
- \+/\- *lemma* abs_zero
- \- *lemma* decidable_linear_ordered_add_comm_group.eq_of_abs_sub_nonpos
- \+ *lemma* eq_of_abs_sub_nonpos
- \- *lemma* eq_zero_of_abs_eq_zero
- \+ *lemma* fn_min_mul_fn_max
- \+/\- *lemma* le_abs_self
- \+ *lemma* lt_abs
- \- *lemma* max_eq_neg_min_neg_neg
- \+ *lemma* max_le_add_of_nonneg
- \+/\- *lemma* max_neg_neg
- \+ *lemma* max_sub_min_eq_abs'
- \+ *lemma* max_sub_min_eq_abs
- \+ *lemma* max_sub_sub_left
- \+ *lemma* max_sub_sub_right
- \+ *lemma* max_zero_sub_eq_self
- \- *lemma* min_eq_neg_max_neg_neg
- \+ *lemma* min_le_add_of_nonneg_left
- \+ *lemma* min_le_add_of_nonneg_right
- \+ *lemma* min_mul_max
- \+/\- *lemma* min_neg_neg
- \+ *lemma* min_sub_sub_left
- \+ *lemma* min_sub_sub_right
- \- *lemma* ne_zero_of_abs_ne_zero
- \+/\- *lemma* neg_le_abs_self

Modified src/algebra/ordered_ring.lean
- \- *lemma* abs_abs_sub_abs_le_abs_sub
- \+ *def* abs_hom
- \+ *lemma* abs_one
- \+ *def* linear_nonneg_ring.to_linear_order
- \+ *def* linear_nonneg_ring.to_linear_ordered_ring
- \+ *lemma* max_mul_mul_le_max_mul_max
- \+ *lemma* max_mul_of_nonneg
- \+ *lemma* min_mul_of_nonneg
- \+ *lemma* mul_max_of_nonneg
- \+ *lemma* mul_min_of_nonneg
- \+ *def* nonneg_ring.to_ordered_ring

Modified src/analysis/special_functions/exp_log.lean


Modified src/analysis/special_functions/pow.lean


Modified src/data/int/basic.lean


Modified src/data/real/hyperreal.lean


Modified src/data/set/intervals/basic.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/tactic/monotonicity/basic.lean


Modified src/topology/instances/real.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean




## [2020-10-12 20:50:11](https://github.com/leanprover-community/mathlib/commit/6ea6200)
feat(tactic/rcases): rcases_many ([#4569](https://github.com/leanprover-community/mathlib/pull/4569))
This allows you to pattern match many variables at once, using the
syntax `obtain ⟨a|b, c|d⟩ := ⟨x, y⟩`. This doesn't require any change
to the front end documentation, as it is in some sense the obvious thing,
but this doesn't break any existing uses because this could never work
before (since the expected type of the tuple expression is not known).
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/rcases.lean


Modified test/rcases.lean




## [2020-10-12 20:50:09](https://github.com/leanprover-community/mathlib/commit/9bed456)
feta(data/fin): induction principle on fin (n + 1) ([#4546](https://github.com/leanprover-community/mathlib/pull/4546))
#### Estimated changes
Modified src/data/fin.lean
- \+ *theorem* fin.cases_succ'
- \+ *def* fin.induction
- \+ *def* fin.induction_on

Modified src/data/matrix/notation.lean




## [2020-10-12 20:50:06](https://github.com/leanprover-community/mathlib/commit/8ccfb0a)
chore(control/functor): linting ([#4496](https://github.com/leanprover-community/mathlib/pull/4496))
#### Estimated changes
Modified src/control/functor.lean




## [2020-10-12 18:08:56](https://github.com/leanprover-community/mathlib/commit/9713e96)
chore(*): update to Lean 3.21.0c ([#4578](https://github.com/leanprover-community/mathlib/pull/4578))
The only real change is the removal of notation for `vector.cons`.
#### Estimated changes
Modified leanpkg.toml


Modified src/computability/halting.lean


Modified src/computability/primrec.lean


Modified src/computability/tm_to_partrec.lean


Modified src/computability/turing_machine.lean


Modified src/data/bitvec/core.lean


Modified src/data/num/bitwise.lean


Modified src/data/sym.lean
- \+/\- *lemma* sym.cons_of_coe_eq

Modified src/data/vector2.lean
- \+/\- *theorem* vector.cons_head
- \+/\- *theorem* vector.cons_tail
- \+/\- *theorem* vector.cons_val

Modified src/group_theory/sylow.lean
- \+/\- *lemma* sylow.mem_fixed_points_mul_left_cosets_iff_mem_normalizer

Modified src/number_theory/sum_four_squares.lean


Modified src/topology/list.lean




## [2020-10-12 18:08:53](https://github.com/leanprover-community/mathlib/commit/6816b83)
feat(archive/100-theorems-list/70_perfect_numbers): Direction 1 of the Perfect Number Theorem ([#4544](https://github.com/leanprover-community/mathlib/pull/4544))
Proves Euclid's half of the Euclid-Euler Theorem that if `2 ^ (k + 1) - 1` is prime, then `2 ^ k * (2 ^ (k + 1) - 1)` is an (even) perfect number.
#### Estimated changes
Added archive/100-theorems-list/70_perfect_numbers.lean
- \+ *theorem* nat.even_two_pow_mul_mersenne_of_prime
- \+ *lemma* nat.ne_zero_of_prime_mersenne
- \+ *theorem* nat.perfect_two_pow_mul_mersenne_of_prime
- \+ *lemma* nat.sigma_two_pow_eq_mersenne_succ
- \+ *lemma* odd_mersenne_succ

Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* nat.arithmetic_function.sigma_one_apply

Modified src/number_theory/divisors.lean
- \+ *lemma* nat.divisors_prime
- \+ *lemma* nat.divisors_prime_pow
- \+ *lemma* nat.mem_divisors_prime_pow
- \+/\- *def* nat.perfect
- \+/\- *theorem* nat.perfect_iff_sum_divisors_eq_two_mul
- \+/\- *theorem* nat.perfect_iff_sum_proper_divisors
- \+ *lemma* nat.prod_divisors_prime
- \+ *lemma* nat.prod_divisors_prime_pow
- \+ *lemma* nat.sum_divisors_prime
- \+ *lemma* nat.sum_divisors_prime_pow

Modified src/number_theory/lucas_lehmer.lean
- \+ *lemma* succ_mersenne



## [2020-10-12 17:14:21](https://github.com/leanprover-community/mathlib/commit/9379050)
chore(data/hash_map): linting ([#4498](https://github.com/leanprover-community/mathlib/pull/4498))
#### Estimated changes
Modified src/data/hash_map.lean




## [2020-10-12 14:57:35](https://github.com/leanprover-community/mathlib/commit/266895f)
fix(algebra/ordered_group): use `add_neg` in autogenerated lemma name ([#4580](https://github.com/leanprover-community/mathlib/pull/4580))
Explicitly add `sub_le_sub_iff` with `a - b`.
#### Estimated changes
Modified src/algebra/linear_ordered_comm_group_with_zero.lean


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* div_le_div_iff'
- \+ *lemma* sub_le_sub_iff



## [2020-10-12 14:57:33](https://github.com/leanprover-community/mathlib/commit/b3ce883)
feat(algebra/*_power): simplify `(-a)^(bit0 _)` and `(-a)^(bit1 _)` ([#4573](https://github.com/leanprover-community/mathlib/pull/4573))
Works for `pow` and `fpow`. Also simplify powers of `I : ℂ`.
#### Estimated changes
Modified src/algebra/field_power.lean
- \+ *lemma* neg_fpow_bit0
- \+ *lemma* neg_fpow_bit1

Modified src/algebra/group_power/basic.lean
- \+ *theorem* bit0_nsmul'
- \+ *theorem* bit1_nsmul'
- \+ *theorem* neg_pow_bit0
- \+ *theorem* neg_pow_bit1
- \+ *theorem* pow_bit0'
- \+ *theorem* pow_bit1'

Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/group_with_zero_power.lean
- \+ *lemma* fpow_add'
- \+ *theorem* fpow_bit0'
- \+ *theorem* fpow_bit0
- \+ *theorem* fpow_bit1'
- \+ *theorem* fpow_bit1

Modified src/data/complex/basic.lean
- \+ *lemma* complex.I_fpow_bit0
- \+ *lemma* complex.I_fpow_bit1
- \+ *lemma* complex.I_pow_bit0
- \+ *lemma* complex.I_pow_bit1

Modified src/data/int/basic.lean
- \+ *lemma* int.bit0_ne_bit1
- \+ *lemma* int.bit1_ne_bit0
- \+ *lemma* int.bit1_ne_zero
- \+ *lemma* int.bodd_bit0
- \+ *lemma* int.bodd_bit1
- \+/\- *lemma* int.bodd_two



## [2020-10-12 14:57:31](https://github.com/leanprover-community/mathlib/commit/38e9ed3)
feat(archive/imo): IMO 2020 Q2 ([#4565](https://github.com/leanprover-community/mathlib/pull/4565))
Add a proof of IMO 2020 Q2 (directly following one of the official
solutions; there are many very similar approaches possible).
In support of this solution, add `geom_mean_le_arith_mean4_weighted`
to `analysis.mean_inequalities`, for both `real` and `nnreal`,
analogous to the versions for two and three numbers (and also add
`geom_mean_le_arith_mean3_weighted` for `real` as it was only present
for `nnreal`).
#### Estimated changes
Added archive/imo/imo2020_q2.lean
- \+ *theorem* imo2020_q2

Modified src/analysis/mean_inequalities.lean
- \+ *theorem* nnreal.geom_mean_le_arith_mean4_weighted
- \+ *theorem* real.geom_mean_le_arith_mean3_weighted
- \+ *theorem* real.geom_mean_le_arith_mean4_weighted



## [2020-10-12 14:57:28](https://github.com/leanprover-community/mathlib/commit/5022425)
feat(algebra/free_algebra): Add an inductive principle ([#4335](https://github.com/leanprover-community/mathlib/pull/4335))
#### Estimated changes
Modified src/algebra/free_algebra.lean
- \+ *lemma* free_algebra.induction



## [2020-10-12 14:57:26](https://github.com/leanprover-community/mathlib/commit/3d1f16a)
feat(analysis/normed_space/multilinear): define `mk_pi_algebra` ([#4316](https://github.com/leanprover-community/mathlib/pull/4316))
I'm going to use this definition for converting `(mv_)power_series` to `formal_multilinear_series`.
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* continuous_multilinear_map.mk_pi_algebra_apply
- \+ *lemma* continuous_multilinear_map.mk_pi_algebra_fin_apply
- \+ *lemma* continuous_multilinear_map.mk_pi_field_apply_one_eq_self
- \- *lemma* continuous_multilinear_map.mk_pi_ring_apply_one_eq_self
- \+ *lemma* continuous_multilinear_map.norm_mk_pi_algebra
- \+ *lemma* continuous_multilinear_map.norm_mk_pi_algebra_fin
- \+ *lemma* continuous_multilinear_map.norm_mk_pi_algebra_fin_le_of_pos
- \+ *lemma* continuous_multilinear_map.norm_mk_pi_algebra_fin_succ_le
- \+ *lemma* continuous_multilinear_map.norm_mk_pi_algebra_fin_zero
- \+ *lemma* continuous_multilinear_map.norm_mk_pi_algebra_le
- \+ *lemma* continuous_multilinear_map.norm_mk_pi_algebra_of_empty

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* linear_map.coe_comp_multilinear_map
- \+/\- *def* linear_map.comp_multilinear_map
- \+ *lemma* linear_map.comp_multilinear_map_apply
- \+ *lemma* multilinear_map.mk_pi_algebra_apply
- \+ *lemma* multilinear_map.mk_pi_algebra_fin_apply
- \+ *lemma* multilinear_map.mk_pi_algebra_fin_apply_const
- \+ *def* multilinear_map.smul_right
- \+ *lemma* multilinear_map.smul_right_apply

Modified src/topology/algebra/multilinear.lean
- \+ *theorem* continuous_multilinear_map.to_multilinear_map_inj



## [2020-10-12 12:21:50](https://github.com/leanprover-community/mathlib/commit/1362701)
refactor(field_theory): Adjoin intermediate field ([#4468](https://github.com/leanprover-community/mathlib/pull/4468))
Refactor adjoin to be an intermediate field rather than a subalgebra.
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \- *lemma* field.adjoin.algebra_map_mem
- \- *lemma* field.adjoin.mono
- \- *lemma* field.adjoin.range_algebra_map_subset
- \- *def* field.adjoin
- \- *lemma* field.adjoin_adjoin_comm
- \- *lemma* field.adjoin_adjoin_left
- \- *lemma* field.adjoin_contains_field_as_subfield
- \- *lemma* field.adjoin_dim_eq_one_iff
- \- *lemma* field.adjoin_dim_eq_one_of_sub_bot
- \- *lemma* field.adjoin_eq_bot
- \- *lemma* field.adjoin_eq_bot_iff
- \- *lemma* field.adjoin_eq_range_algebra_map_adjoin
- \- *lemma* field.adjoin_findim_eq_one_iff
- \- *lemma* field.adjoin_one
- \- *lemma* field.adjoin_simple.algebra_map_gen
- \- *def* field.adjoin_simple.gen
- \- *lemma* field.adjoin_simple_adjoin_simple
- \- *lemma* field.adjoin_simple_comm
- \- *lemma* field.adjoin_simple_dim_eq_one_iff
- \- *lemma* field.adjoin_simple_dim_eq_one_of_mem_bot
- \- *lemma* field.adjoin_simple_eq_bot
- \- *lemma* field.adjoin_simple_eq_bot_iff
- \- *lemma* field.adjoin_simple_findim_eq_one_iff
- \- *lemma* field.adjoin_subset_adjoin_iff
- \- *lemma* field.adjoin_subset_iff
- \- *lemma* field.adjoin_subset_subfield
- \- *lemma* field.adjoin_zero
- \- *lemma* field.bot_eq_top_of_dim_adjoin_eq_one
- \- *lemma* field.bot_eq_top_of_findim_adjoin_eq_one
- \- *lemma* field.bot_eq_top_of_findim_adjoin_le_one
- \- *lemma* field.mem_adjoin_simple_self
- \- *lemma* field.mem_bot_of_adjoin_simple_dim_eq_one
- \- *lemma* field.mem_bot_of_adjoin_simple_sub_bot
- \- *lemma* field.sub_bot_of_adjoin_dim_eq_one
- \- *lemma* field.sub_bot_of_adjoin_sub_bot
- \- *lemma* field.subfield_subset_adjoin_self
- \- *lemma* field.subset_adjoin
- \- *lemma* field.subset_adjoin_of_subset_left
- \- *lemma* field.subset_adjoin_of_subset_right
- \+ *lemma* intermediate_field.adjoin.algebra_map_mem
- \+ *lemma* intermediate_field.adjoin.mono
- \+ *lemma* intermediate_field.adjoin.range_algebra_map_subset
- \+ *def* intermediate_field.adjoin
- \+ *lemma* intermediate_field.adjoin_adjoin_comm
- \+ *lemma* intermediate_field.adjoin_adjoin_left
- \+ *lemma* intermediate_field.adjoin_contains_field_as_subfield
- \+ *lemma* intermediate_field.adjoin_eq_bot_iff
- \+ *lemma* intermediate_field.adjoin_eq_range_algebra_map_adjoin
- \+ *lemma* intermediate_field.adjoin_induction
- \+ *lemma* intermediate_field.adjoin_int
- \+ *lemma* intermediate_field.adjoin_le_algebra_adjoin
- \+ *lemma* intermediate_field.adjoin_le_iff
- \+ *lemma* intermediate_field.adjoin_le_subfield
- \+ *lemma* intermediate_field.adjoin_map
- \+ *lemma* intermediate_field.adjoin_nat
- \+ *lemma* intermediate_field.adjoin_one
- \+ *lemma* intermediate_field.adjoin_simple.algebra_map_gen
- \+ *def* intermediate_field.adjoin_simple.gen
- \+ *lemma* intermediate_field.adjoin_simple_adjoin_simple
- \+ *lemma* intermediate_field.adjoin_simple_comm
- \+ *lemma* intermediate_field.adjoin_simple_eq_bot_iff
- \+ *lemma* intermediate_field.adjoin_subset_adjoin_iff
- \+ *lemma* intermediate_field.adjoin_zero
- \+ *lemma* intermediate_field.algebra_adjoin_le_adjoin
- \+ *lemma* intermediate_field.bot_eq_top_of_dim_adjoin_eq_one
- \+ *lemma* intermediate_field.bot_eq_top_of_findim_adjoin_eq_one
- \+ *lemma* intermediate_field.bot_eq_top_of_findim_adjoin_le_one
- \+ *lemma* intermediate_field.bot_to_subalgebra
- \+ *lemma* intermediate_field.coe_bot_eq_self
- \+ *lemma* intermediate_field.coe_top_eq_top
- \+ *lemma* intermediate_field.dim_adjoin_eq_one_iff
- \+ *lemma* intermediate_field.dim_adjoin_simple_eq_one_iff
- \+ *lemma* intermediate_field.dim_intermediate_field_eq_dim_subalgebra
- \+ *lemma* intermediate_field.findim_adjoin_eq_one_iff
- \+ *lemma* intermediate_field.findim_adjoin_simple_eq_one_iff
- \+ *lemma* intermediate_field.findim_intermediate_field_eq_findim_subalgebra
- \+ *lemma* intermediate_field.gc
- \+ *def* intermediate_field.gi
- \+ *lemma* intermediate_field.induction_on_adjoin
- \+ *lemma* intermediate_field.mem_adjoin_simple_self
- \+ *lemma* intermediate_field.mem_bot
- \+ *lemma* intermediate_field.mem_top
- \+ *lemma* intermediate_field.subset_adjoin
- \+ *lemma* intermediate_field.subset_adjoin_of_subset_left
- \+ *lemma* intermediate_field.subset_adjoin_of_subset_right
- \+ *lemma* intermediate_field.subsingleton_of_dim_adjoin_eq_one
- \+ *lemma* intermediate_field.subsingleton_of_findim_adjoin_eq_one
- \+ *lemma* intermediate_field.subsingleton_of_findim_adjoin_le_one
- \+ *lemma* intermediate_field.to_subalgebra_eq_iff
- \+ *lemma* intermediate_field.top_to_subalgebra

Modified src/field_theory/intermediate_field.lean
- \+ *def* intermediate_field.lift1
- \+ *def* intermediate_field.lift2
- \+ *lemma* intermediate_field.mem_lift2
- \+/\- *lemma* intermediate_field.pow_mem

Modified src/field_theory/primitive_element.lean
- \- *theorem* field.exists_primitive_element_aux
- \- *theorem* field.exists_primitive_element_inf

Modified src/field_theory/subfield.lean


Modified src/order/bounded_lattice.lean
- \+ *lemma* eq_bot_of_bot_eq_top
- \+ *lemma* eq_top_of_bot_eq_top
- \+ *lemma* subsingleton_of_bot_eq_top



## [2020-10-12 10:16:23](https://github.com/leanprover-community/mathlib/commit/8fa9125)
feat(data/polynomial/degree/erase_lead): definition and basic lemmas ([#4527](https://github.com/leanprover-community/mathlib/pull/4527))
erase_lead serves as the reduction step in an induction, breaking off one monomial from a polynomial.  It is used in a later PR to prove that reverse is a multiplicative monoid map on polynomials.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *theorem* finset.pred_card_le_card_erase
- \+ *theorem* finset.subset_of_eq

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.card_support_eq_one'
- \+ *lemma* finsupp.card_support_eq_one
- \+ *lemma* finsupp.card_support_eq_zero
- \+ *lemma* finsupp.eq_single_iff
- \+ *lemma* finsupp.erase_zero
- \+ *lemma* finsupp.support_eq_singleton'
- \+ *lemma* finsupp.support_eq_singleton

Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.X_pow_eq_monomial
- \- *lemma* polynomial.monomial_eq_X_pow

Modified src/data/polynomial/degree.lean
- \+ *lemma* polynomial.C_mul_X_pow_eq_self
- \+ *lemma* polynomial.monomial_nat_degree_leading_coeff_eq_self

Modified src/data/polynomial/degree/basic.lean
- \+ *lemma* polynomial.leading_coeff_monomial'
- \+ *lemma* polynomial.nat_degree_monomial

Added src/data/polynomial/erase_lead.lean
- \+ *def* polynomial.erase_lead
- \+ *lemma* polynomial.erase_lead_C
- \+ *lemma* polynomial.erase_lead_C_mul_X_pow
- \+ *lemma* polynomial.erase_lead_X
- \+ *lemma* polynomial.erase_lead_X_pow
- \+ *lemma* polynomial.erase_lead_add_C_mul_X_pow
- \+ *lemma* polynomial.erase_lead_add_monomial_nat_degree_leading_coeff
- \+ *lemma* polynomial.erase_lead_coeff
- \+ *lemma* polynomial.erase_lead_coeff_nat_degree
- \+ *lemma* polynomial.erase_lead_coeff_of_ne
- \+ *lemma* polynomial.erase_lead_degree_le
- \+ *lemma* polynomial.erase_lead_monomial
- \+ *lemma* polynomial.erase_lead_nat_degree_le
- \+ *lemma* polynomial.erase_lead_nat_degree_lt
- \+ *lemma* polynomial.erase_lead_ne_zero
- \+ *lemma* polynomial.erase_lead_support
- \+ *lemma* polynomial.erase_lead_support_card_lt
- \+ *lemma* polynomial.erase_lead_zero
- \+ *lemma* polynomial.nat_degree_not_mem_erase_lead_support
- \+ *lemma* polynomial.ne_nat_degree_of_mem_erase_lead_support
- \+ *lemma* polynomial.self_sub_C_mul_X_pow
- \+ *lemma* polynomial.self_sub_monomial_nat_degree_leading_coeff



## [2020-10-12 08:30:01](https://github.com/leanprover-community/mathlib/commit/0bfc68f)
feat(ring_theory/witt_vector/structure_polynomial): witt_structure_int_prop ([#4466](https://github.com/leanprover-community/mathlib/pull/4466))
This is the 3rd PR in a series on a fundamental theorem about Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/ring_theory/witt_vector/structure_polynomial.lean
- \+ *lemma* eq_witt_structure_int
- \+ *theorem* witt_structure_int_exists_unique
- \+ *theorem* witt_structure_int_prop
- \+ *lemma* witt_structure_int_rename
- \+ *theorem* witt_structure_prop



## [2020-10-12 06:33:28](https://github.com/leanprover-community/mathlib/commit/b953717)
feat(set_theory/cardinal): cardinality of powerset ([#4576](https://github.com/leanprover-community/mathlib/pull/4576))
adds a lemma for cardinality of powerset
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *theorem* cardinal.mk_set



## [2020-10-12 01:08:24](https://github.com/leanprover-community/mathlib/commit/81b8123)
chore(scripts): update nolints.txt ([#4575](https://github.com/leanprover-community/mathlib/pull/4575))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-11 21:16:36](https://github.com/leanprover-community/mathlib/commit/665cc13)
chore(topology/algebra/group): review ([#4570](https://github.com/leanprover-community/mathlib/pull/4570))
* Ensure that we don't use `[topological_group G]` when it suffices to ask for, e.g., `[has_continuous_mul G]`.
* Introduce `[has_continuous_sub]`, add an instance for `nnreal`.
#### Estimated changes
Modified src/analysis/convex/topology.lean


Modified src/measure_theory/borel_space.lean


Modified src/topology/algebra/group.lean
- \+/\- *lemma* continuous.inv
- \+/\- *lemma* continuous.sub
- \- *lemma* continuous_at.inv
- \+ *lemma* continuous_at_inv
- \- *lemma* continuous_inv
- \+/\- *lemma* continuous_on.inv
- \+/\- *lemma* continuous_on.sub
- \+/\- *lemma* continuous_on_inv
- \- *lemma* continuous_sub
- \+/\- *lemma* continuous_within_at.inv
- \+ *lemma* continuous_within_at.sub
- \+ *lemma* continuous_within_at_inv
- \+/\- *lemma* exists_nhds_split_inv
- \+/\- *lemma* filter.tendsto.inv
- \+/\- *lemma* filter.tendsto.sub
- \+/\- *lemma* is_closed_map_mul_left
- \+/\- *lemma* is_closed_map_mul_right
- \+ *lemma* is_open.mul_left
- \+ *lemma* is_open.mul_right
- \+/\- *lemma* is_open_map_mul_left
- \+/\- *lemma* is_open_map_mul_right
- \- *lemma* is_open_mul_left
- \- *lemma* is_open_mul_right
- \+/\- *lemma* nhds_one_symm
- \+/\- *lemma* nhds_translation
- \+/\- *lemma* nhds_translation_mul_inv
- \+/\- *lemma* tendsto_inv

Modified src/topology/instances/nnreal.lean
- \- *lemma* nnreal.continuous.sub
- \- *lemma* nnreal.continuous_sub



## [2020-10-11 20:09:45](https://github.com/leanprover-community/mathlib/commit/952a407)
feat(data/nat/digits): add norm_digits tactic ([#4452](https://github.com/leanprover-community/mathlib/pull/4452))
This adds a basic tactic for normalizing expressions of the form `nat.digits a b = l`. As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/simplifying.20nat.2Edigits/near/212152395
#### Estimated changes
Modified src/data/nat/digits.lean
- \+ *theorem* nat.digits_def'
- \+ *theorem* nat.digits_zero_succ'
- \+ *theorem* nat.norm_digits.digits_one
- \+ *theorem* nat.norm_digits.digits_succ

Added test/norm_digits.lean




## [2020-10-11 20:09:43](https://github.com/leanprover-community/mathlib/commit/b1ca33e)
feat(analysis/calculus/times_cont_diff, analysis/calculus/inverse): smooth inverse function theorem ([#4407](https://github.com/leanprover-community/mathlib/pull/4407))
The inverse function theorem, in the C^k and smooth categories.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at.of_local_homeomorph

Modified src/analysis/calculus/inverse.lean
- \+ *lemma* times_cont_diff_at.image_mem_to_local_homeomorph_target
- \+ *def* times_cont_diff_at.local_inverse
- \+ *lemma* times_cont_diff_at.local_inverse_apply_image
- \+ *lemma* times_cont_diff_at.mem_to_local_homeomorph_source
- \+ *def* times_cont_diff_at.to_local_homeomorph
- \+ *lemma* times_cont_diff_at.to_local_homeomorph_coe
- \+ *lemma* times_cont_diff_at.to_local_inverse

Modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_at.has_strict_fderiv_at'
- \+ *theorem* times_cont_diff_at.of_local_homeomorph
- \+ *lemma* times_cont_diff_at_zero
- \+ *lemma* times_cont_diff_within_at_zero



## [2020-10-11 18:49:02](https://github.com/leanprover-community/mathlib/commit/b48b4ff)
feat(analysis/normed_space/inner_product): Cauchy-Schwarz equality case and other lemmas ([#4571](https://github.com/leanprover-community/mathlib/pull/4571))
#### Estimated changes
Modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* abs_inner_div_norm_mul_norm_eq_one_iff
- \+ *lemma* abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
- \+ *lemma* abs_inner_eq_norm_iff
- \+/\- *def* euclidean_space
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square_of_inner_eq_zero
- \+ *lemma* submodule.bot_orthogonal_eq_top
- \+ *lemma* submodule.eq_top_iff_orthogonal_eq_bot
- \+ *lemma* submodule.is_compl_orthogonal_of_is_complete
- \- *lemma* submodule.is_compl_orthogonal_of_is_complete_real
- \+ *lemma* submodule.top_orthogonal_eq_bot

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.norm_eq_abs

Modified src/geometry/euclidean/basic.lean




## [2020-10-11 18:49:00](https://github.com/leanprover-community/mathlib/commit/0f085b9)
chore(linear_algebra/finite_dimensional): rename `of_finite_basis` ([#4562](https://github.com/leanprover-community/mathlib/pull/4562))
* rename `of_finite_basis` to `of_fintype_basis`;
* add new `of_finite_basis` assuming that the domain the basis is a
  `finite` set;
* allow `s : finset ι` and any function `s → V` in `of_finset_basis`.
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/field_theory/tower.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* finite_dimensional.of_finite_basis
- \+/\- *lemma* finite_dimensional.of_finset_basis
- \+ *lemma* finite_dimensional.of_fintype_basis



## [2020-10-11 16:27:35](https://github.com/leanprover-community/mathlib/commit/14dcfe0)
chore(*): assorted lemmas ([#4566](https://github.com/leanprover-community/mathlib/pull/4566))
Non-bc changes:
* make some lemmas use `coe` instead of `subtype.val`;
* make the arguments of `range_comp` explicit, reorder them.
#### Estimated changes
Modified src/data/dfinsupp.lean


Modified src/data/equiv/basic.lean
- \+/\- *def* equiv.option_equiv_sum_punit
- \+ *lemma* equiv.option_equiv_sum_punit_symm_inl
- \+ *lemma* equiv.option_equiv_sum_punit_symm_inr

Modified src/data/finset/basic.lean
- \+ *lemma* finset.subtype_eq_empty

Modified src/data/finsupp/basic.lean
- \+/\- *lemma* finsupp.emb_domain_apply
- \+ *lemma* finsupp.emb_domain_eq_zero
- \+/\- *lemma* finsupp.emb_domain_inj
- \+ *lemma* finsupp.emb_domain_injective
- \+/\- *lemma* finsupp.emb_domain_zero
- \+ *lemma* finsupp.subtype_domain_eq_zero_iff'
- \+ *lemma* finsupp.subtype_domain_eq_zero_iff
- \+/\- *lemma* finsupp.support_emb_domain
- \+ *lemma* finsupp.unique_ext
- \+ *lemma* finsupp.unique_ext_iff

Modified src/data/option/basic.lean
- \+ *lemma* option.cases_on'_coe
- \+ *lemma* option.cases_on'_none
- \+ *lemma* option.cases_on'_none_coe
- \+ *lemma* option.cases_on'_some

Modified src/data/set/basic.lean
- \- *lemma* function.surjective.range_eq
- \+ *theorem* set.is_compl_range_inl_range_inr
- \+ *theorem* set.pair_comm
- \+/\- *theorem* set.range_comp

Modified src/data/set/function.lean


Modified src/data/set/lattice.lean
- \+ *theorem* set.subset_Inter_iff

Modified src/data/sum.lean
- \+ *lemma* sum.injective_inl
- \+ *lemma* sum.injective_inr

Modified src/logic/nontrivial.lean
- \+ *lemma* not_subsingleton

Modified src/measure_theory/simple_func_dense.lean


Modified src/topology/metric_space/gromov_hausdorff.lean




## [2020-10-11 16:27:33](https://github.com/leanprover-community/mathlib/commit/918e5d8)
chore(data/finsupp): replace `eq_zero_of_zero_eq_one` with `finsupp.unique_of_right` ([#4563](https://github.com/leanprover-community/mathlib/pull/4563))
Also add a lemma `semimodule.subsingleton`: if `R` is a subsingleton semiring, then any semimodule over `R` is a subsingleton.
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* is_unit_of_subsingleton

Modified src/algebra/group_with_zero.lean
- \+ *theorem* subsingleton_iff_zero_eq_one
- \- *theorem* subsingleton_of_zero_eq_one

Modified src/algebra/module/basic.lean
- \+ *theorem* semimodule.subsingleton

Modified src/data/finsupp/basic.lean


Modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent_of_subsingleton
- \- *lemma* linear_independent_of_zero_eq_one



## [2020-10-11 15:12:38](https://github.com/leanprover-community/mathlib/commit/33f7870)
chore(measure_theory/measurable_space): add `finset.is_measurable_bUnion` etc ([#4553](https://github.com/leanprover-community/mathlib/pull/4553))
I always forget how to convert `finset` or `set.finite` to `set.countable. Also `finset.is_measurable_bUnion` uses `finset`'s `has_mem`, not coercion to `set`.
Also replace `tendsto_at_top_supr_nat` etc with slightly more general versions using a `[semilattice_sup β] [nonempty β]` instead of `nat`.
#### Estimated changes
Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/measurable_space.lean
- \+ *lemma* finset.is_measurable_bInter
- \+ *lemma* finset.is_measurable_bUnion
- \+ *lemma* set.finite.is_measurable_bInter
- \+ *lemma* set.finite.is_measurable_bUnion
- \+ *lemma* set.finite.is_measurable_sInter
- \+ *lemma* set.finite.is_measurable_sUnion

Modified src/measure_theory/measure_space.lean


Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* supr_eq_of_tendsto
- \+ *lemma* tendsto_at_top_cinfi
- \+ *lemma* tendsto_at_top_infi
- \- *lemma* tendsto_at_top_infi_nat
- \- *lemma* tendsto_at_top_supr_nat



## [2020-10-11 12:30:22](https://github.com/leanprover-community/mathlib/commit/99130d8)
chore(algebra/monoid_algebra): Reorder lemmas, name some sections for clarity ([#4535](https://github.com/leanprover-community/mathlib/pull/4535))
This also reduces the scope of `local attribute [reducible] add_monoid_algebra` to the sections which actually need it.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean




## [2020-10-11 10:42:23](https://github.com/leanprover-community/mathlib/commit/0487a1d)
chore(algebra/algebra/basic): fix definition of `ring_hom.to_algebra` ([#4561](https://github.com/leanprover-community/mathlib/pull/4561))
The new definition uses `to_ring_hom := i` instead of `.. i` to get
defeq `algebra_map R S = i`, and adds it as a lemma.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* ring_hom.algebra_map_to_algebra



## [2020-10-11 04:06:05](https://github.com/leanprover-community/mathlib/commit/2c53e5e)
chore(order/well_founded): move to a file ([#4568](https://github.com/leanprover-community/mathlib/pull/4568))
I want to use `order/rel_classes` before `data/set/basic`.
#### Estimated changes
Modified archive/imo/imo1988_q6.lean


Modified src/data/fintype/basic.lean


Modified src/order/lattice.lean
- \+ *lemma* lt_sup_iff

Modified src/order/pilex.lean


Modified src/order/rel_classes.lean
- \- *lemma* well_founded.eq_iff_not_lt_of_le
- \- *theorem* well_founded.has_min
- \- *theorem* well_founded.min_mem
- \- *theorem* well_founded.not_lt_min
- \- *theorem* well_founded.well_founded_iff_has_max'
- \- *theorem* well_founded.well_founded_iff_has_min'
- \- *theorem* well_founded.well_founded_iff_has_min

Added src/order/well_founded.lean
- \+ *lemma* well_founded.eq_iff_not_lt_of_le
- \+ *theorem* well_founded.has_min
- \+ *theorem* well_founded.min_mem
- \+ *theorem* well_founded.not_lt_min
- \+ *theorem* well_founded.well_founded_iff_has_max'
- \+ *theorem* well_founded.well_founded_iff_has_min'
- \+ *theorem* well_founded.well_founded_iff_has_min



## [2020-10-11 03:06:27](https://github.com/leanprover-community/mathlib/commit/4dbebe3)
chore(scripts): update nolints.txt ([#4564](https://github.com/leanprover-community/mathlib/pull/4564))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt




## [2020-10-11 01:02:23](https://github.com/leanprover-community/mathlib/commit/d8d6e18)
feat(data/finset/basic): equivalence of finsets from equivalence of types ([#4560](https://github.com/leanprover-community/mathlib/pull/4560))
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
Given an equivalence `α` to `β`, produce an equivalence between `finset α` and `finset β`, and simp lemmas about it.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* equiv.finset_congr_apply
- \+ *lemma* equiv.finset_congr_symm_apply



## [2020-10-10 23:06:12](https://github.com/leanprover-community/mathlib/commit/df5adc5)
chore(topology/*): golf some proofs ([#4528](https://github.com/leanprover-community/mathlib/pull/4528))
* move `exists_nhds_split` to `topology/algebra/monoid`, rename to `exists_nhds_one_split`;
* add a version `exists_open_nhds_one_split`;
* move `exists_nhds_split4` to `topology/algebra/monoid`, rename to `exists_nhds_one_split4`;
* move `one_open_separated_mul` to `topology/algebra/monoid`, rename to `exists_open_nhds_one_mul_subset`;
* add `mem_prod_nhds_iff`;
* golf some proofs.
#### Estimated changes
Modified src/topology/algebra/group.lean
- \- *lemma* exists_nhds_split4
- \- *lemma* exists_nhds_split
- \- *lemma* one_open_separated_mul

Modified src/topology/algebra/monoid.lean
- \+ *lemma* exists_nhds_one_split4
- \+ *lemma* exists_nhds_one_split
- \+ *lemma* exists_open_nhds_one_mul_subset
- \+ *lemma* exists_open_nhds_one_split

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/constructions.lean
- \+/\- *lemma* exists_nhds_square
- \+ *lemma* filter.has_basis.prod_nhds
- \+ *lemma* mem_nhds_prod_iff



## [2020-10-10 20:25:23](https://github.com/leanprover-community/mathlib/commit/c726898)
feat(data/equiv/basic): equivalence on functions from bool ([#4559](https://github.com/leanprover-community/mathlib/pull/4559))
An equivalence of functions from bool and pairs, together with some simp lemmas about it.
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.bool_to_equiv_prod
- \+ *lemma* equiv.bool_to_equiv_prod_apply
- \+ *lemma* equiv.bool_to_equiv_prod_symm_apply_ff
- \+ *lemma* equiv.bool_to_equiv_prod_symm_apply_tt



## [2020-10-10 18:28:05](https://github.com/leanprover-community/mathlib/commit/f91e0c6)
feat(data/finset/pi): pi singleton lemmas ([#4558](https://github.com/leanprover-community/mathlib/pull/4558))
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259). 
Two lemmas to reduce `finset.pi` on singletons.
#### Estimated changes
Modified src/data/finset/pi.lean
- \+ *lemma* finset.pi_const_singleton
- \+ *lemma* finset.pi_singletons



## [2020-10-10 15:18:44](https://github.com/leanprover-community/mathlib/commit/c8738cb)
feat(topology/uniform_space/cauchy): generalize `second_countable_of_separable` to uniform spaces ([#4530](https://github.com/leanprover-community/mathlib/pull/4530))
Also generalize `is_countably_generated.has_antimono_basis` to `is_countably_generated.exists_antimono_subbasis` and add a few lemmas about bases of the uniformity filter.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.property_index
- \+ *lemma* filter.has_basis.set_index_mem
- \+ *lemma* filter.has_basis.set_index_subset
- \+ *lemma* filter.is_countably_generated.exists_antimono_basis
- \- *lemma* filter.is_countably_generated.exists_antimono_seq
- \+ *lemma* filter.is_countably_generated.exists_antimono_subbasis
- \- *lemma* filter.is_countably_generated.has_antimono_basis
- \+/\- *lemma* filter.is_countably_generated.inf
- \+/\- *lemma* filter.is_countably_generated.inf_principal
- \+/\- *lemma* filter.is_countably_generated_iff_exists_antimono_basis

Modified src/topology/bases.lean
- \+ *lemma* topological_space.exists_countable_dense

Modified src/topology/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/sequences.lean


Modified src/topology/uniform_space/basic.lean
- \+/\- *lemma* nhds_eq_uniformity
- \+ *lemma* uniform_space.is_open_ball
- \+ *lemma* uniform_space.mem_ball_self
- \+ *lemma* uniformity_has_basis_open
- \+ *lemma* uniformity_has_basis_open_symmetric

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* uniform_space.second_countable_of_separable

Modified src/topology/uniform_space/completion.lean




## [2020-10-10 09:40:05](https://github.com/leanprover-community/mathlib/commit/6676917)
feat(analysis/special_functions/*): a few more simp lemmas ([#4550](https://github.com/leanprover-community/mathlib/pull/4550))
Add more lemmas for simplifying inequalities with `exp`, `log`, and
`rpow`. Lemmas that generate more than one inequality are not marked
as `simp`.
#### Estimated changes
Modified src/algebra/ordered_ring.lean


Modified src/analysis/special_functions/exp_log.lean
- \+/\- *lemma* real.log_nonneg
- \+ *lemma* real.log_nonneg_iff
- \+ *lemma* real.log_nonpos_iff'
- \+ *lemma* real.log_nonpos_iff

Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* real.one_le_rpow_of_pos_of_le_one_of_nonpos
- \+ *lemma* real.one_lt_rpow_iff
- \+ *lemma* real.one_lt_rpow_iff_of_pos
- \+/\- *lemma* real.one_lt_rpow_of_pos_of_lt_one_of_neg
- \+ *lemma* real.rpow_le_one_iff_of_pos
- \+ *lemma* real.rpow_lt_one_iff
- \+ *lemma* real.rpow_lt_one_iff_of_pos

Modified src/data/complex/exponential.lean
- \+ *lemma* real.exp_le_one_iff
- \+/\- *lemma* real.exp_lt_one_iff
- \+ *lemma* real.one_le_exp_iff
- \+/\- *lemma* real.one_lt_exp_iff



## [2020-10-10 01:04:50](https://github.com/leanprover-community/mathlib/commit/b084a06)
chore(scripts): update nolints.txt ([#4556](https://github.com/leanprover-community/mathlib/pull/4556))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


Modified scripts/nolints.txt




## [2020-10-09 19:22:53](https://github.com/leanprover-community/mathlib/commit/40b55c0)
feat(measure_theory): additions ([#4324](https://github.com/leanprover-community/mathlib/pull/4324))
Many additional lemmas. 
Notable addition: sequential limits of measurable functions into a metric space are measurable.
Rename `integral_map_measure` -> `integral_map` (to be consistent with the version for `lintegral`)
Fix the precedence of all notations for integrals. From now on `∫ x, abs ∥f x∥ ∂μ` will be parsed
correctly (previously it gave a parse error).
Some cleanup (moving lemmas, and some nicer presentation by opening locales and namespaces).
#### Estimated changes
Modified src/data/indicator_function.lean
- \+ *lemma* set.indicator_comp_right
- \+ *lemma* set.indicator_prod_one

Modified src/data/set/finite.lean
- \+ *lemma* set.Union_Inter_of_monotone

Modified src/data/set/lattice.lean
- \+ *lemma* set.Union_Inter_subset
- \+ *lemma* set.Union_inter_of_monotone
- \+ *lemma* set.Union_inter_subset

Modified src/logic/basic.lean
- \+ *lemma* ite_and

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.ennnorm_integral_le_lintegral_ennnorm
- \+ *lemma* measure_theory.integral_add'
- \+ *lemma* measure_theory.integral_map
- \- *lemma* measure_theory.integral_map_measure
- \+ *lemma* measure_theory.integral_neg'
- \+ *lemma* measure_theory.integral_sub'
- \+ *lemma* measure_theory.integral_to_real
- \+ *lemma* measure_theory.integral_zero'
- \+ *lemma* measure_theory.lintegral_coe_eq_integral
- \+ *lemma* measure_theory.simple_func.integral_eq_sum_of_subset

Modified src/measure_theory/borel_space.lean
- \+/\- *lemma* ennreal.measurable_coe
- \+/\- *lemma* measurable.ennreal_coe
- \+ *lemma* measurable.inf_nndist
- \+/\- *lemma* measurable.nnnorm
- \+/\- *lemma* measurable.nnreal_coe
- \+/\- *lemma* measurable.norm
- \+/\- *lemma* measurable.sub_nnreal
- \+/\- *lemma* measurable_dist
- \+/\- *lemma* measurable_edist
- \+/\- *lemma* measurable_ennreal_coe_iff
- \+/\- *def* measurable_equiv.ennreal_equiv_nnreal
- \+ *lemma* measurable_inf_nndist
- \+ *lemma* measurable_liminf'
- \+ *lemma* measurable_liminf
- \+ *lemma* measurable_limsup'
- \+ *lemma* measurable_limsup
- \+/\- *lemma* measurable_nndist
- \+/\- *lemma* measurable_nnnorm
- \+ *lemma* measurable_of_tendsto_metric'
- \+ *lemma* measurable_of_tendsto_metric
- \+ *lemma* measurable_of_tendsto_nnreal'
- \+ *lemma* measurable_of_tendsto_nnreal
- \+/\- *lemma* nnreal.measurable_coe

Modified src/measure_theory/integration.lean
- \+ *lemma* measure_theory.ae_lt_top
- \+ *lemma* measure_theory.lintegral_comp
- \+ *lemma* measure_theory.lintegral_mul_const'
- \+ *lemma* measure_theory.lintegral_mul_const
- \+ *lemma* measure_theory.lintegral_mul_const_le

Modified src/measure_theory/l1_space.lean
- \+ *lemma* measure_theory.integrable_smul_const
- \+ *lemma* measure_theory.l1.norm_eq_lintegral
- \+ *lemma* measure_theory.l1.norm_sub_eq_lintegral
- \+ *lemma* measure_theory.l1.of_real_norm_eq_lintegral
- \+ *lemma* measure_theory.l1.of_real_norm_sub_eq_lintegral

Modified src/measure_theory/measure_space.lean
- \+/\- *lemma* measure_theory.dirac_ae_eq
- \+/\- *theorem* measure_theory.measure.le_iff'
- \+/\- *theorem* measure_theory.measure.le_iff
- \+/\- *theorem* measure_theory.measure.lt_iff'
- \+/\- *theorem* measure_theory.measure.lt_iff
- \+ *lemma* measure_theory.measure.sum_cond
- \+/\- *theorem* measure_theory.measure.to_outer_measure_le
- \+ *lemma* measure_theory.measure_Union_null_iff
- \+ *lemma* measure_theory.measure_if
- \+ *lemma* measure_theory.measure_union_null_iff

Modified src/measure_theory/set_integral.lean
- \+ *lemma* integral_smul_const

Modified src/measure_theory/simple_func_dense.lean
- \+/\- *lemma* measure_theory.simple_func.integrable_approx_on
- \+/\- *lemma* measure_theory.simple_func.integrable_approx_on_univ
- \+ *lemma* measure_theory.simple_func.norm_approx_on_zero_le
- \+/\- *lemma* measure_theory.simple_func.tendsto_approx_on_l1_edist
- \+/\- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_l1
- \+/\- *lemma* measure_theory.simple_func.tendsto_approx_on_univ_l1_edist



## [2020-10-09 18:15:49](https://github.com/leanprover-community/mathlib/commit/d533e1c)
feat(ring_theory/power_series): inverse lemmas ([#4552](https://github.com/leanprover-community/mathlib/pull/4552))
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
#### Estimated changes
Modified src/ring_theory/power_series.lean
- \+ *lemma* power_series.eq_inv_iff_mul_eq_one
- \+ *lemma* power_series.eq_mul_inv_iff_mul_eq
- \+ *lemma* power_series.inv_eq_iff_mul_eq_one



## [2020-10-09 15:44:20](https://github.com/leanprover-community/mathlib/commit/b167809)
feat(topology/basic): Lim_spec etc. cleanup ([#4545](https://github.com/leanprover-community/mathlib/pull/4545))
Fixes [#4543](https://github.com/leanprover-community/mathlib/pull/4543)
See [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/More.20point.20set.20topology.20questions/near/212757136)
#### Estimated changes
Modified src/order/filter/ultrafilter.lean


Modified src/topology/basic.lean
- \- *lemma* Lim_spec
- \+ *lemma* le_nhds_Lim
- \- *lemma* lim_spec
- \+ *lemma* tendsto_nhds_lim

Modified src/topology/extend_from_subset.lean


Modified src/topology/separation.lean
- \+ *lemma* Lim_eq_iff
- \+ *lemma* filter.lim_eq_iff
- \+/\- *lemma* filter.tendsto.lim_eq
- \+ *lemma* is_ultrafilter.Lim_eq_iff_le_nhds

Modified src/topology/subset_properties.lean
- \+ *lemma* is_ultrafilter.le_nhds_Lim

Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2020-10-09 13:16:06](https://github.com/leanprover-community/mathlib/commit/fcaf6e9)
feat(meta/expr): add parser for generated binder names ([#4540](https://github.com/leanprover-community/mathlib/pull/4540))
During elaboration, Lean generates a name for anonymous Π binders. This commit
adds a parser that recognises such names.
#### Estimated changes
Modified src/data/string/defs.lean
- \+ *def* string.is_nat

Modified src/data/sum.lean


Modified src/meta/expr.lean




## [2020-10-09 13:16:04](https://github.com/leanprover-community/mathlib/commit/306dc8a)
chore(algebra/big_operators/basic): add lemma prod_multiset_count' that generalize prod_multiset_count to consider a function to a monoid ([#4534](https://github.com/leanprover-community/mathlib/pull/4534))
I have added `prod_multiset_count'` that is very similar to `prod_multiset_count` but takes into account a function `f : \a \r M` where `M` is a commutative monoid. The proof is essentially the same (I didn't try to prove it using `prod_multiset_count` because maybe we can remove it and just keep the more general version).
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_multiset_map_count



## [2020-10-09 11:06:01](https://github.com/leanprover-community/mathlib/commit/656ef0a)
chore(topology/instances/nnreal): use notation ([#4548](https://github.com/leanprover-community/mathlib/pull/4548))
#### Estimated changes
Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* nnreal.coe_tsum
- \+/\- *lemma* nnreal.continuous.sub
- \+/\- *lemma* nnreal.continuous_coe
- \+/\- *lemma* nnreal.continuous_sub
- \+/\- *lemma* nnreal.has_sum_coe
- \+/\- *lemma* nnreal.sum_add_tsum_nat_add
- \+/\- *lemma* nnreal.summable_comp_injective
- \+/\- *lemma* nnreal.summable_nat_add
- \+/\- *lemma* nnreal.tendsto.sub
- \+/\- *lemma* nnreal.tendsto_coe



## [2020-10-09 11:05:59](https://github.com/leanprover-community/mathlib/commit/d0f45f5)
lint(various): nolint has_inhabited_instance for injective functions ([#4541](https://github.com/leanprover-community/mathlib/pull/4541))
`function.embedding`, `homeomorph`, `isometric` represent injective/bijective functions, so it's silly to expect them to be inhabited.
#### Estimated changes
Modified src/logic/embedding.lean


Modified src/topology/homeomorph.lean


Modified src/topology/metric_space/isometry.lean




## [2020-10-09 08:54:38](https://github.com/leanprover-community/mathlib/commit/cc75e4e)
chore(data/nat/cast): a few `simp`/`norm_cast` lemmas ([#4549](https://github.com/leanprover-community/mathlib/pull/4549))
#### Estimated changes
Modified src/data/nat/cast.lean
- \+/\- *theorem* nat.cast_le
- \+ *theorem* nat.cast_le_one
- \+ *theorem* nat.cast_lt_one
- \+/\- *lemma* nat.coe_nat_dvd
- \+ *theorem* nat.one_le_cast
- \+ *theorem* nat.one_lt_cast
- \+ *theorem* nat.strict_mono_cast



## [2020-10-09 01:44:31](https://github.com/leanprover-community/mathlib/commit/f6836c1)
chore(scripts): update nolints.txt ([#4547](https://github.com/leanprover-community/mathlib/pull/4547))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/copy-mod-doc-exceptions.txt


Modified scripts/nolints.txt




## [2020-10-08 23:44:06](https://github.com/leanprover-community/mathlib/commit/8004fb6)
chore(topology/algebra/group): move a lemma to `group_theory/coset` ([#4522](https://github.com/leanprover-community/mathlib/pull/4522))
`quotient_group_saturate` didn't use any topology. Move it to
`group_theory/coset` and rename to
`quotient_group.preimage_image_coe`.
Also rename `quotient_group.open_coe` to `quotient_group.is_open_map_coe`
#### Estimated changes
Modified src/group_theory/coset.lean
- \+ *lemma* quotient_group.preimage_image_coe

Modified src/group_theory/quotient_group.lean
- \+/\- *lemma* quotient_group.coe_gpow
- \+/\- *lemma* quotient_group.coe_inv
- \+/\- *lemma* quotient_group.coe_mul
- \+/\- *lemma* quotient_group.coe_one
- \+/\- *lemma* quotient_group.coe_pow

Modified src/topology/algebra/group.lean
- \+ *lemma* quotient_group.is_open_map_coe
- \- *lemma* quotient_group.open_coe
- \- *lemma* quotient_group_saturate



## [2020-10-08 22:15:42](https://github.com/leanprover-community/mathlib/commit/ce999a8)
feat(topology/basic): add `is_open_iff_ultrafilter` ([#4529](https://github.com/leanprover-community/mathlib/pull/4529))
Requested on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F)
by Adam Topaz
#### Estimated changes
Modified src/order/filter/ultrafilter.lean
- \+ *lemma* filter.le_iff_ultrafilter
- \+ *lemma* filter.mem_iff_ultrafilter

Modified src/topology/basic.lean
- \+ *theorem* is_open_iff_ultrafilter



## [2020-10-08 18:04:05](https://github.com/leanprover-community/mathlib/commit/a912455)
fix(bors.toml, build.yml): check for new linter, rename linter to "Lint style" ([#4539](https://github.com/leanprover-community/mathlib/pull/4539))
#### Estimated changes
Modified .github/workflows/build.yml


Modified bors.toml




## [2020-10-08 15:41:18](https://github.com/leanprover-community/mathlib/commit/73f119e)
refactor(category_theory/pairwise): change direction of morphisms in the category of pairwise intersections ([#4537](https://github.com/leanprover-community/mathlib/pull/4537))
Even though this makes some proofs slightly more awkward, this is the more natural definition.
In a subsequent PR about another equivalent sheaf condition, it also makes proofs less awkward, too!
#### Estimated changes
Modified src/category_theory/category/pairwise.lean
- \+ *def* category_theory.pairwise.cocone
- \+ *def* category_theory.pairwise.cocone_is_colimit
- \+ *def* category_theory.pairwise.cocone_ι_app
- \- *def* category_theory.pairwise.cone
- \- *def* category_theory.pairwise.cone_is_limit
- \- *def* category_theory.pairwise.cone_π_app
- \+/\- *def* category_theory.pairwise.diagram
- \+/\- *def* category_theory.pairwise.diagram_obj

Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean




## [2020-10-08 15:41:16](https://github.com/leanprover-community/mathlib/commit/0ae4a3d)
fix(update-copy-mod-doc-exceptions.sh): cleanup, sort properly ([#4533](https://github.com/leanprover-community/mathlib/pull/4533))
Followup to [#4513](https://github.com/leanprover-community/mathlib/pull/4513).
#### Estimated changes
Modified scripts/update-copy-mod-doc-exceptions.sh




## [2020-10-08 15:41:14](https://github.com/leanprover-community/mathlib/commit/427564e)
chore(algebra/monoid_algebra): Fix TODO about unwanted unfolding ([#4532](https://github.com/leanprover-community/mathlib/pull/4532))
For whatever reason, supplying `zero` and `add` explicitly makes the proofs work inline.
This TODO was added by @johoelzl in f09abb1c47a846c33c0e996ffa9bf12951b40b15.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean




## [2020-10-08 15:41:12](https://github.com/leanprover-community/mathlib/commit/0c18d96)
chore(data/padics/*): linting + squeeze_simp speedup ([#4531](https://github.com/leanprover-community/mathlib/pull/4531))
#### Estimated changes
Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean
- \+/\- *def* padic_seq



## [2020-10-08 15:41:08](https://github.com/leanprover-community/mathlib/commit/60be8ed)
feat(data/equiv/*): to_monoid_hom_injective and to_ring_hom_injective ([#4525](https://github.com/leanprover-community/mathlib/pull/4525))
#### Estimated changes
Modified src/data/equiv/mul_add.lean
- \+ *lemma* mul_equiv.to_monoid_hom_injective

Modified src/data/equiv/ring.lean
- \+ *lemma* ring_equiv.to_ring_hom_injective



## [2020-10-08 15:41:06](https://github.com/leanprover-community/mathlib/commit/253f225)
lint(computability/halting): docstrings ([#4524](https://github.com/leanprover-community/mathlib/pull/4524))
Adds docstrings in `computability/halting.lean`
#### Estimated changes
Modified src/computability/halting.lean




## [2020-10-08 15:41:04](https://github.com/leanprover-community/mathlib/commit/e74bd26)
chore(*): add a few more `unique` instances ([#4511](https://github.com/leanprover-community/mathlib/pull/4511))
* `linear_map.unique_of_left`, `linear_map.unique_of_right`,
  `continuous_linear_map.unique_of_left`,
  `continuous_linear_map.unique_of_right`: if either `M` or `M₂` is a
  `subsingleton`, then both `M →ₗ[R] M₂` and `M →L[R] M₂` are
  `unique`;
* `pi.unique`: if each `β a` is `unique`, then `Π a, β a` is `unique`;
* rename `function.injective.comap_subsingleton` to
  `function.injective.subsingleton`;
* add `unique.mk'` and `function.injective.unique`;
* add a few `simp` lemmas for `default`;
* drop `nonempty_unique_or_exists_ne` and `subsingleton_or_exists_ne`;
* rename `linear_map.coe_inj` to `coe_injective` and `continuous_linear_map.coe_inj` to `coe_fn_injective`,
  make them use `function.injective`.
Motivated by [#4407](https://github.com/leanprover-community/mathlib/pull/4407)
#### Estimated changes
Modified src/algebra/category/Module/limits.lean


Modified src/algebra/module/basic.lean
- \- *theorem* linear_map.coe_inj
- \+ *theorem* linear_map.coe_injective
- \+/\- *theorem* linear_map.to_add_monoid_hom_injective

Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/data/equiv/basic.lean


Modified src/geometry/euclidean/basic.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.default_def

Modified src/logic/unique.lean
- \- *lemma* function.injective.comap_subsingleton
- \- *def* function.surjective.unique
- \- *lemma* nonempty_unique_or_exists_ne
- \+ *lemma* pi.default_apply
- \+ *lemma* pi.default_def
- \- *lemma* subsingleton_or_exists_ne
- \+ *def* unique.mk'

Modified src/ring_theory/derivation.lean


Modified src/topology/algebra/module.lean
- \+ *theorem* continuous_linear_map.coe_fn_injective
- \- *theorem* continuous_linear_map.coe_inj
- \+ *lemma* continuous_linear_map.default_def



## [2020-10-08 15:41:02](https://github.com/leanprover-community/mathlib/commit/7b42c71)
feat(archive/imo): revive @kbuzzard's imo2019_q1 ([#4377](https://github.com/leanprover-community/mathlib/pull/4377))
#### Estimated changes
Added archive/imo/imo2019_q1.lean
- \+ *theorem* imo2019Q1



## [2020-10-08 15:40:59](https://github.com/leanprover-community/mathlib/commit/9b0d30c)
feat(number_theory/arithmetic_function): define `is_multiplicative` on `arithmetic_function`s, provides examples ([#4312](https://github.com/leanprover-community/mathlib/pull/4312))
Provides a few basic examples of important arithmetic functions
Defines what it means for an arithmetic function to be multiplicative
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *lemma* nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul

Modified src/number_theory/arithmetic_function.lean
- \+/\- *lemma* nat.arithmetic_function.add_apply
- \+/\- *lemma* nat.arithmetic_function.coe_coe
- \+/\- *theorem* nat.arithmetic_function.coe_inj
- \+/\- *theorem* nat.arithmetic_function.ext
- \+/\- *theorem* nat.arithmetic_function.ext_iff
- \+ *def* nat.arithmetic_function.id
- \+ *lemma* nat.arithmetic_function.id_apply
- \+/\- *lemma* nat.arithmetic_function.int_coe_apply
- \+ *lemma* nat.arithmetic_function.is_multiplicative.int_cast
- \+ *lemma* nat.arithmetic_function.is_multiplicative.map_mul_of_coprime
- \+ *lemma* nat.arithmetic_function.is_multiplicative.map_one
- \+ *lemma* nat.arithmetic_function.is_multiplicative.mul
- \+ *lemma* nat.arithmetic_function.is_multiplicative.nat_cast
- \+ *lemma* nat.arithmetic_function.is_multiplicative.pmul
- \+ *lemma* nat.arithmetic_function.is_multiplicative.ppow
- \+ *def* nat.arithmetic_function.is_multiplicative
- \+ *lemma* nat.arithmetic_function.is_multiplicative_id
- \+ *lemma* nat.arithmetic_function.is_multiplicative_pow
- \+ *lemma* nat.arithmetic_function.is_multiplicative_sigma
- \+ *lemma* nat.arithmetic_function.is_multiplicative_zeta
- \+/\- *lemma* nat.arithmetic_function.map_zero
- \+/\- *lemma* nat.arithmetic_function.mul_apply
- \+ *theorem* nat.arithmetic_function.mul_zeta_apply
- \+/\- *lemma* nat.arithmetic_function.nat_coe_apply
- \+/\- *lemma* nat.arithmetic_function.one_apply_ne
- \+/\- *lemma* nat.arithmetic_function.one_one
- \+ *def* nat.arithmetic_function.pmul
- \+ *lemma* nat.arithmetic_function.pmul_apply
- \+ *lemma* nat.arithmetic_function.pmul_comm
- \+ *lemma* nat.arithmetic_function.pmul_zeta
- \+ *def* nat.arithmetic_function.pow
- \+ *lemma* nat.arithmetic_function.pow_apply
- \+ *def* nat.arithmetic_function.ppow
- \+ *lemma* nat.arithmetic_function.ppow_apply
- \+ *lemma* nat.arithmetic_function.ppow_succ'
- \+ *lemma* nat.arithmetic_function.ppow_succ
- \+ *lemma* nat.arithmetic_function.ppow_zero
- \+ *def* nat.arithmetic_function.sigma
- \+ *lemma* nat.arithmetic_function.sigma_apply
- \+/\- *lemma* nat.arithmetic_function.to_fun_eq
- \+/\- *lemma* nat.arithmetic_function.zero_apply
- \+ *def* nat.arithmetic_function.zeta
- \+ *lemma* nat.arithmetic_function.zeta_apply
- \+ *lemma* nat.arithmetic_function.zeta_apply_ne
- \+ *theorem* nat.arithmetic_function.zeta_mul_apply
- \+ *lemma* nat.arithmetic_function.zeta_mul_pow_eq_sigma
- \+ *lemma* nat.arithmetic_function.zeta_pmul
- \+/\- *structure* nat.arithmetic_function

Modified src/number_theory/divisors.lean
- \+/\- *def* nat.divisors
- \- *lemma* nat.divisors_eq_proper_divisors_insert_self
- \+ *lemma* nat.divisors_eq_proper_divisors_insert_self_of_pos
- \+/\- *lemma* nat.divisors_zero
- \+/\- *def* nat.proper_divisors



## [2020-10-08 13:27:56](https://github.com/leanprover-community/mathlib/commit/5a01549)
lint(multiset/pi): remove unused instance ([#4526](https://github.com/leanprover-community/mathlib/pull/4526))
Removes an unused instance from `multiset/pi`
#### Estimated changes
Modified src/data/finset/pi.lean


Modified src/data/multiset/pi.lean
- \+/\- *lemma* multiset.pi.cons_ne



## [2020-10-08 13:27:54](https://github.com/leanprover-community/mathlib/commit/48a3604)
feat(logic/nontrivial): a tactic to summon nontrivial instances ([#4374](https://github.com/leanprover-community/mathlib/pull/4374))
```
Given a goal `a = b` or `a ≤ b` in a type `α`, generates an additional hypothesis `nontrivial α`
(as otherwise `α` is a subsingleton and the goal is trivial).
Alternatively, given a hypothesis `a ≠ b` or `a < b` in a type `α`, tries to generate a `nontrivial α`
hypothesis from existing hypotheses using `nontrivial_of_ne` and `nontrivial_of_lt`.
```
#### Estimated changes
Modified src/linear_algebra/char_poly/coeff.lean
- \- *lemma* char_poly_monic_of_nontrivial

Modified src/logic/nontrivial.lean
- \+ *lemma* nontrivial_of_lt
- \+/\- *lemma* subsingleton_or_nontrivial

Added test/nontriviality.lean




## [2020-10-08 10:23:23](https://github.com/leanprover-community/mathlib/commit/43f52dd)
chore(algebra/char_zero): rename vars, add `with_top` instance ([#4523](https://github.com/leanprover-community/mathlib/pull/4523))
Motivated by [#3135](https://github.com/leanprover-community/mathlib/pull/3135).
* Use `R` as a `Type*` variable;
* Add `add_monoid_hom.map_nat_cast` and `with_top.coe_add_hom`;
* Drop versions of `char_zero_of_inj_zero`, use `[add_left_cancel_monoid R]` instead.
#### Estimated changes
Modified src/algebra/char_p.lean


Modified src/algebra/char_zero.lean
- \- *theorem* add_group.char_zero_of_inj_zero
- \+/\- *lemma* add_halves'
- \+/\- *lemma* add_self_eq_zero
- \+/\- *lemma* bit0_eq_zero
- \+/\- *theorem* char_zero_of_inj_zero
- \+/\- *lemma* half_add_self
- \+/\- *lemma* half_sub
- \+/\- *lemma* nat.cast_add_one_ne_zero
- \+/\- *theorem* nat.cast_dvd_char_zero
- \+/\- *theorem* nat.cast_eq_zero
- \+/\- *theorem* nat.cast_inj
- \+/\- *theorem* nat.cast_injective
- \+/\- *theorem* nat.cast_ne_zero
- \- *theorem* ordered_cancel_comm_monoid.char_zero_of_inj_zero
- \+/\- *lemma* sub_half
- \+/\- *lemma* two_ne_zero'

Modified src/algebra/ordered_group.lean
- \+ *def* with_top.coe_add_hom
- \+ *lemma* with_top.coe_coe_add_hom

Modified src/data/complex/basic.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/nat/cast.lean
- \+/\- *lemma* add_monoid_hom.eq_nat_cast
- \+ *lemma* add_monoid_hom.map_nat_cast



## [2020-10-08 05:32:06](https://github.com/leanprover-community/mathlib/commit/34a4471)
chore(data/quot): `quot.mk` etc are surjective ([#4517](https://github.com/leanprover-community/mathlib/pull/4517))
#### Estimated changes
Modified src/data/quot.lean
- \+/\- *theorem* quotient.lift_on_beta₂
- \+ *lemma* quotient.surjective_quotient_mk'
- \+ *lemma* surjective_quot_mk
- \+ *lemma* surjective_quotient_mk



## [2020-10-08 05:32:04](https://github.com/leanprover-community/mathlib/commit/4f75760)
chore(*/hom,equiv): Split `monoid_hom` into more fundamental structures, and reuse them elsewhere ([#4423](https://github.com/leanprover-community/mathlib/pull/4423))
Notably this adds `add_hom` and `mul_hom`, which become base classes of `add_equiv`, `mul_equiv`, `linear_map`, and `linear_equiv`.
Primarily to avoid breaking assumptions of field order in `monoid_hom` and `add_monoid_hom`, this also adds `one_hom` and `zero_hom`.
A massive number of lemmas here are totally uninteresting and hold for pretty much all objects that define `coe_to_fun`.
This PR translates all those lemmas, but doesn't bother attempting to generalize later ones.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *structure* add_hom
- \+/\- *structure* add_monoid_hom
- \+/\- *lemma* monoid_hom.cancel_left
- \+/\- *lemma* monoid_hom.cancel_right
- \+/\- *lemma* monoid_hom.coe_inj
- \+/\- *lemma* monoid_hom.coe_mk
- \+/\- *def* monoid_hom.comp
- \+/\- *lemma* monoid_hom.comp_apply
- \+/\- *lemma* monoid_hom.comp_assoc
- \+/\- *lemma* monoid_hom.comp_id
- \+/\- *theorem* monoid_hom.congr_arg
- \+/\- *theorem* monoid_hom.congr_fun
- \+/\- *lemma* monoid_hom.ext
- \+/\- *lemma* monoid_hom.ext_iff
- \+/\- *def* monoid_hom.id
- \+/\- *lemma* monoid_hom.id_apply
- \+/\- *lemma* monoid_hom.id_comp
- \+/\- *lemma* monoid_hom.map_mul
- \+/\- *lemma* monoid_hom.map_one
- \+/\- *lemma* monoid_hom.one_apply
- \+/\- *lemma* monoid_hom.to_fun_eq_coe
- \+/\- *structure* monoid_hom
- \+ *lemma* mul_hom.cancel_left
- \+ *lemma* mul_hom.cancel_right
- \+ *lemma* mul_hom.coe_inj
- \+ *lemma* mul_hom.coe_mk
- \+ *def* mul_hom.comp
- \+ *lemma* mul_hom.comp_apply
- \+ *lemma* mul_hom.comp_assoc
- \+ *lemma* mul_hom.comp_id
- \+ *theorem* mul_hom.congr_arg
- \+ *theorem* mul_hom.congr_fun
- \+ *lemma* mul_hom.ext
- \+ *lemma* mul_hom.ext_iff
- \+ *def* mul_hom.id
- \+ *lemma* mul_hom.id_apply
- \+ *lemma* mul_hom.id_comp
- \+ *lemma* mul_hom.map_mul
- \+ *lemma* mul_hom.to_fun_eq_coe
- \+ *structure* mul_hom
- \+ *lemma* one_hom.cancel_left
- \+ *lemma* one_hom.cancel_right
- \+ *lemma* one_hom.coe_inj
- \+ *lemma* one_hom.coe_mk
- \+ *def* one_hom.comp
- \+ *lemma* one_hom.comp_apply
- \+ *lemma* one_hom.comp_assoc
- \+ *lemma* one_hom.comp_id
- \+ *theorem* one_hom.congr_arg
- \+ *theorem* one_hom.congr_fun
- \+ *lemma* one_hom.ext
- \+ *lemma* one_hom.ext_iff
- \+ *def* one_hom.id
- \+ *lemma* one_hom.id_apply
- \+ *lemma* one_hom.id_comp
- \+ *lemma* one_hom.map_one
- \+ *lemma* one_hom.one_apply
- \+ *lemma* one_hom.to_fun_eq_coe
- \+ *structure* one_hom
- \+ *structure* zero_hom

Modified src/algebra/module/basic.lean


Modified src/data/equiv/mul_add.lean
- \+/\- *structure* add_equiv
- \+/\- *structure* mul_equiv

Modified src/linear_algebra/basic.lean
- \- *def* linear_equiv.to_add_equiv
- \+ *def* linear_equiv.to_equiv



## [2020-10-08 04:37:20](https://github.com/leanprover-community/mathlib/commit/b4dc912)
ci(*): run style lint in parallel job, fix update-copy-mod-doc-exceptions.sh ([#4513](https://github.com/leanprover-community/mathlib/pull/4513))
Followup to [#4486](https://github.com/leanprover-community/mathlib/pull/4486):
- run the linter in a separate parallel job, per request
- the update-*.sh script now correctly generates a full exceptions file
- add some more comments to the shell scripts
#### Estimated changes
Modified .github/workflows/build.yml


Modified scripts/copy-mod-doc-exceptions.txt


Modified scripts/lint-copy-mod-doc.sh


Modified scripts/update-copy-mod-doc-exceptions.sh




## [2020-10-08 04:37:18](https://github.com/leanprover-community/mathlib/commit/3d1d4fb)
feat(data/polynomial/degree/trailing_degree): fixed formatting and streamlined a couple of proofs ([#4509](https://github.com/leanprover-community/mathlib/pull/4509))
#### Estimated changes
Modified src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* polynomial.nat_trailing_degree_eq_support_min'
- \+ *lemma* polynomial.nat_trailing_degree_le_of_mem_supp
- \+ *lemma* polynomial.nat_trailing_degree_mem_support_of_nonzero
- \+ *lemma* polynomial.trailing_coeff_eq_zero
- \+ *lemma* polynomial.trailing_coeff_nonzero_iff_nonzero



## [2020-10-08 03:44:56](https://github.com/leanprover-community/mathlib/commit/7a71554)
doc(tactic/slim_check): improve advice in error message ([#4520](https://github.com/leanprover-community/mathlib/pull/4520))
The error message in `slim_check` suggests to look for `testable` and it now specifies which namespace to find `testable` in.
#### Estimated changes
Modified src/tactic/slim_check.lean




## [2020-10-08 01:08:47](https://github.com/leanprover-community/mathlib/commit/e9d1dc4)
chore(scripts): update nolints.txt ([#4521](https://github.com/leanprover-community/mathlib/pull/4521))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-10-07 23:27:32](https://github.com/leanprover-community/mathlib/commit/a5b0376)
chore(topology/algebra/monoid,group): rename variables ([#4516](https://github.com/leanprover-community/mathlib/pull/4516))
Use `M`, `N` for monoids, `G`, `H` for groups.
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+/\- *lemma* add_group_with_zero_nhd.add_Z
- \+/\- *lemma* add_group_with_zero_nhd.exists_Z_half
- \+/\- *lemma* add_group_with_zero_nhd.neg_Z
- \+/\- *lemma* add_group_with_zero_nhd.nhds_eq
- \+/\- *lemma* add_group_with_zero_nhd.nhds_zero_eq_Z
- \+/\- *lemma* compact_covered_by_mul_left_translates
- \+/\- *lemma* compact_open_separated_mul
- \+/\- *lemma* continuous.inv
- \+/\- *lemma* continuous.sub
- \+/\- *lemma* continuous_at.inv
- \+/\- *lemma* continuous_inv
- \+/\- *lemma* continuous_on.inv
- \+/\- *lemma* continuous_on.sub
- \+/\- *lemma* continuous_on_inv
- \+/\- *lemma* continuous_sub
- \+/\- *lemma* continuous_within_at.inv
- \+/\- *lemma* exists_nhds_split4
- \+/\- *lemma* exists_nhds_split
- \+/\- *lemma* exists_nhds_split_inv
- \+/\- *lemma* filter.tendsto.inv
- \+/\- *lemma* filter.tendsto.sub
- \+/\- *lemma* is_closed_map_mul_left
- \+/\- *lemma* is_closed_map_mul_right
- \+/\- *lemma* is_open_map_mul_left
- \+/\- *lemma* is_open_map_mul_right
- \+/\- *lemma* is_open_mul_left
- \+/\- *lemma* is_open_mul_right
- \+/\- *lemma* nhds_is_mul_hom
- \+/\- *lemma* nhds_mul
- \+/\- *lemma* nhds_one_symm
- \+/\- *lemma* nhds_translation
- \+/\- *lemma* nhds_translation_mul_inv
- \+/\- *lemma* one_open_separated_mul
- \+/\- *lemma* quotient_group.open_coe
- \+/\- *lemma* quotient_group_saturate
- \+/\- *lemma* tendsto_inv
- \+/\- *lemma* topological_group.regular_space
- \+/\- *lemma* topological_group.t1_space
- \+/\- *lemma* topological_group.t2_space

Modified src/topology/algebra/monoid.lean
- \+/\- *lemma* continuous.mul
- \+/\- *lemma* continuous.pow
- \+/\- *lemma* continuous_at.mul
- \+/\- *lemma* continuous_finset_prod
- \+/\- *lemma* continuous_list_prod
- \+/\- *lemma* continuous_mul
- \+/\- *lemma* continuous_mul_left
- \+/\- *lemma* continuous_mul_right
- \+/\- *lemma* continuous_multiset_prod
- \+/\- *lemma* continuous_on.mul
- \+/\- *lemma* continuous_pow
- \+/\- *lemma* continuous_within_at.mul
- \+/\- *lemma* filter.tendsto.mul
- \+/\- *lemma* submonoid.mem_nhds_one
- \+/\- *lemma* tendsto_finset_prod
- \+/\- *lemma* tendsto_list_prod
- \+/\- *lemma* tendsto_mul
- \+/\- *lemma* tendsto_multiset_prod



## [2020-10-07 21:39:17](https://github.com/leanprover-community/mathlib/commit/d67062f)
chore(algebra/pointwise): add `###` here and there ([#4514](https://github.com/leanprover-community/mathlib/pull/4514))
#### Estimated changes
Modified src/algebra/pointwise.lean




## [2020-10-07 21:39:15](https://github.com/leanprover-community/mathlib/commit/fa8b7ba)
chore(topology/*): use dot notation for `is_open.prod` and `is_closed.prod` ([#4510](https://github.com/leanprover-community/mathlib/pull/4510))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/special_functions/pow.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/compact_open.lean


Modified src/topology/constructions.lean
- \+ *lemma* is_closed.prod
- \- *lemma* is_closed_prod
- \+ *lemma* is_open.prod
- \- *lemma* is_open_prod

Modified src/topology/instances/complex.lean


Modified src/topology/instances/real.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/topological_fiber_bundle.lean


Modified src/topology/uniform_space/compact_separated.lean




## [2020-10-07 20:25:40](https://github.com/leanprover-community/mathlib/commit/2b89d59)
chore(ring_theory/coprime): weaken assumptions of finset.prod_dvd_of_coprime ([#4506](https://github.com/leanprover-community/mathlib/pull/4506))
#### Estimated changes
Modified src/ring_theory/coprime.lean
- \+/\- *theorem* finset.prod_dvd_of_coprime



## [2020-10-07 18:09:31](https://github.com/leanprover-community/mathlib/commit/4635aee)
chore(algebra/continuous_functions): `coninuous` -> `continuous` ([#4508](https://github.com/leanprover-community/mathlib/pull/4508))
#### Estimated changes
Modified src/topology/algebra/continuous_functions.lean




## [2020-10-07 18:09:28](https://github.com/leanprover-community/mathlib/commit/4e8427e)
fix(data/list/defs): remove map_head; rename map_last to modify_last ([#4507](https://github.com/leanprover-community/mathlib/pull/4507))
`map_head` is removed in favour of the equivalent `modify_head`.
`map_last` is renamed to `modify_last` for consistency with the other
`modify_*` functions.
#### Estimated changes
Modified src/data/list/defs.lean
- \- *def* list.map_head
- \- *def* list.map_last
- \+ *def* list.modify_last



## [2020-10-07 18:09:25](https://github.com/leanprover-community/mathlib/commit/a4a20ac)
doc(data/num/basic): added doc-strings to most defs ([#4439](https://github.com/leanprover-community/mathlib/pull/4439))
#### Estimated changes
Modified src/data/num/basic.lean




## [2020-10-07 16:08:11](https://github.com/leanprover-community/mathlib/commit/8f9c10f)
feat(data/matrix): add `matrix.mul_sub` and `matrix.sub_mul` ([#4505](https://github.com/leanprover-community/mathlib/pull/4505))
I was quite surprised that we didn't have this yet, but I guess they weren't needed when `sub_eq_add_neg` was still `@[simp]`.
#### Estimated changes
Modified src/data/matrix/basic.lean




## [2020-10-07 16:08:08](https://github.com/leanprover-community/mathlib/commit/2d34e94)
chore(*big_operators*): line length ([#4504](https://github.com/leanprover-community/mathlib/pull/4504))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *theorem* finset.prod_eq_fold
- \+/\- *lemma* finset.prod_subset
- \+/\- *lemma* ring_hom.map_prod

Modified src/algebra/polynomial/big_operators.lean




## [2020-10-07 16:08:05](https://github.com/leanprover-community/mathlib/commit/6b50fb9)
fix(tactic/ring): use int_sub_hack to avoid defeq blowup ([#4503](https://github.com/leanprover-community/mathlib/pull/4503))
#### Estimated changes
Modified src/tactic/ring.lean


Modified test/ring.lean




## [2020-10-07 14:27:03](https://github.com/leanprover-community/mathlib/commit/4db1c72)
ci(scripts/*): linting for copyright, imports, module docstrings, line length ([#4486](https://github.com/leanprover-community/mathlib/pull/4486))
This PR adds some scripts to check the `.lean` files in `src/` and `archive/` for the following issues (which are out of scope for the current linter):
- Malformed or missing copyright header
- More than one file imported per line
- Module docstring missing, or too late
- Lines of length > 100 (unless they contain `http`)
The scripts are run at the end of our "tests" job since the "lint" job usually takes longer to run. (This isn't a big deal though, since they're quick.)
Current problems are saved in the file `scripts/copy-mod-doc-exceptions.txt` and ignored so that we don't have to fix everything up front. Over time, this should get shorter as we fix things!
Separately, this also fixes some warnings in our GitHub actions workflow (see [this blog post](https://github.blog/changelog/2020-10-01-github-actions-deprecating-set-env-and-add-path-commands/)).
#### Estimated changes
Modified .github/workflows/build.yml


Added scripts/copy-mod-doc-exceptions.txt


Added scripts/lint-copy-mod-doc.py


Added scripts/lint-copy-mod-doc.sh


Added scripts/update-copy-mod-doc-exceptions.sh


Modified scripts/update_nolints.sh




## [2020-10-07 14:26:58](https://github.com/leanprover-community/mathlib/commit/c9d4567)
lint(data/matrix/basic): add definition docstrings ([#4478](https://github.com/leanprover-community/mathlib/pull/4478))
#### Estimated changes
Modified src/data/matrix/basic.lean




## [2020-10-07 10:12:05](https://github.com/leanprover-community/mathlib/commit/6a85279)
fix(tactic/doc_commands): do not construct json by hand ([#4501](https://github.com/leanprover-community/mathlib/pull/4501))
Fixes three lines going over the 100 character limit.
The first one was a hand-rolled JSON serializer, I took the liberty to migrate it to the new `json` API.
#### Estimated changes
Modified src/tactic/doc_commands.lean




## [2020-10-07 10:12:04](https://github.com/leanprover-community/mathlib/commit/0386ada)
chore(data/tree): linting ([#4499](https://github.com/leanprover-community/mathlib/pull/4499))
#### Estimated changes
Modified src/data/tree.lean




## [2020-10-07 10:12:02](https://github.com/leanprover-community/mathlib/commit/cbbc123)
lint(category_theory/equivalence): docstring and a module doc ([#4495](https://github.com/leanprover-community/mathlib/pull/4495))
#### Estimated changes
Modified src/category_theory/equivalence.lean




## [2020-10-07 10:12:00](https://github.com/leanprover-community/mathlib/commit/8a4b491)
feat(ring_theory/witt_vector/structure_polynomial): {map_}witt_structure_int ([#4465](https://github.com/leanprover-community/mathlib/pull/4465))
This is the second PR in a series on a fundamental theorem about Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Modified src/ring_theory/witt_vector/structure_polynomial.lean
- \+ *lemma* C_p_pow_dvd_bind₁_rename_witt_polynomial_sub_sum
- \+ *lemma* bind₁_rename_expand_witt_polynomial
- \+ *lemma* map_witt_structure_int
- \+ *lemma* witt_structure_rat_rec
- \+ *lemma* witt_structure_rat_rec_aux



## [2020-10-07 07:56:34](https://github.com/leanprover-community/mathlib/commit/e5ce9d3)
chore(data/quot): linting ([#4500](https://github.com/leanprover-community/mathlib/pull/4500))
#### Estimated changes
Modified src/data/quot.lean




## [2020-10-07 07:56:32](https://github.com/leanprover-community/mathlib/commit/ed9ef1b)
chore(*): normalise copyright headers ([#4497](https://github.com/leanprover-community/mathlib/pull/4497))
This diff makes sure that all files start with a copyright header
of the following shape
```
/-
Copyright ...
... Apache ...
Author...
-/
```
Some files used to have a short description of the contents
in the same comment block.
Such comments have *not* been turned into module docstrings,
but simply moved to a regular comment block below the copyright header.
Turning these comments into good module docstrings is an
effort that should be undertaken in future PRs.
#### Estimated changes
Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/integral_normalization.lean


Modified src/data/set/function.lean


Modified src/measure_theory/category/Meas.lean


Modified src/tactic/derive_fintype.lean


Modified src/tactic/derive_inhabited.lean


Modified src/tactic/interactive.lean


Modified src/tactic/omega/clause.lean


Modified src/tactic/omega/coeffs.lean


Modified src/tactic/omega/eq_elim.lean


Modified src/tactic/omega/find_ees.lean


Modified src/tactic/omega/find_scalars.lean


Modified src/tactic/omega/int/dnf.lean


Modified src/tactic/omega/int/form.lean


Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/int/preterm.lean


Modified src/tactic/omega/lin_comb.lean


Modified src/tactic/omega/main.lean


Modified src/tactic/omega/misc.lean


Modified src/tactic/omega/nat/dnf.lean


Modified src/tactic/omega/nat/form.lean


Modified src/tactic/omega/nat/main.lean


Modified src/tactic/omega/nat/neg_elim.lean


Modified src/tactic/omega/nat/preterm.lean


Modified src/tactic/omega/nat/sub_elim.lean


Modified src/tactic/omega/prove_unsats.lean


Modified src/tactic/omega/term.lean




## [2020-10-07 06:23:11](https://github.com/leanprover-community/mathlib/commit/3c75527)
lint(group_theory/*): docstrings and an inhabited instance ([#4493](https://github.com/leanprover-community/mathlib/pull/4493))
An inhabited instance for `presented_group`
Docstrings in `group_theory/abelianization` and `group_theory/congruence`.
#### Estimated changes
Modified src/group_theory/abelianization.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/presented_group.lean




## [2020-10-07 04:25:17](https://github.com/leanprover-community/mathlib/commit/8c528b9)
lint(group_theory/perm/*): docstrings ([#4492](https://github.com/leanprover-community/mathlib/pull/4492))
Adds missing docstrings in `group_theory/perm/cycles` and `group_theory/perm/sign`.
#### Estimated changes
Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean




## [2020-10-07 01:06:50](https://github.com/leanprover-community/mathlib/commit/cb3118d)
chore(scripts): update nolints.txt ([#4490](https://github.com/leanprover-community/mathlib/pull/4490))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-10-07 01:06:47](https://github.com/leanprover-community/mathlib/commit/2e77ef6)
lint(order/lexographic, pilex): docstrings ([#4489](https://github.com/leanprover-community/mathlib/pull/4489))
Docstrings in `order/lexographic` and `order/pilex`
#### Estimated changes
Modified src/order/lexicographic.lean


Modified src/order/pilex.lean




## [2020-10-07 01:06:45](https://github.com/leanprover-community/mathlib/commit/afffab1)
lint(order/order_iso_nat): docstrings ([#4488](https://github.com/leanprover-community/mathlib/pull/4488))
Adds docstrings to `rel_embedding.nat_lt` and `rel_embedding.nat_gt`
#### Estimated changes
Modified src/order/order_iso_nat.lean




## [2020-10-07 01:06:42](https://github.com/leanprover-community/mathlib/commit/93cdc3a)
feat(control/traversable/basic): composition of applicative transformations ([#4487](https://github.com/leanprover-community/mathlib/pull/4487))
Added composition law for applicative transformations, added rest of interface for coercion of applicative transformations to functions (lifted from `monoid_hom`), and proved composition was associative and has an identity.  Also corrected some documentation.
#### Estimated changes
Modified src/control/traversable/basic.lean
- \+ *lemma* applicative_transformation.app_eq_coe
- \+ *lemma* applicative_transformation.coe_inj
- \+ *lemma* applicative_transformation.coe_mk
- \+ *def* applicative_transformation.comp
- \+ *lemma* applicative_transformation.comp_apply
- \+ *lemma* applicative_transformation.comp_assoc
- \+ *lemma* applicative_transformation.comp_id
- \+ *lemma* applicative_transformation.congr_arg
- \+ *lemma* applicative_transformation.congr_fun
- \+ *lemma* applicative_transformation.ext
- \+ *lemma* applicative_transformation.ext_iff
- \+ *lemma* applicative_transformation.id_comp
- \+ *lemma* applicative_transformation.preserves_map'



## [2020-10-07 01:06:41](https://github.com/leanprover-community/mathlib/commit/fe8b631)
lint(ring_theory/*): docstrings ([#4485](https://github.com/leanprover-community/mathlib/pull/4485))
Docstrings in `ring_theory/ideal/operations`, `ring_theory/multiplicity`, and `ring_theory/ring_invo`.
#### Estimated changes
Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/ring_invo.lean




## [2020-10-06 22:45:54](https://github.com/leanprover-community/mathlib/commit/7488f8e)
lint(order/bounded_lattice): docstring ([#4484](https://github.com/leanprover-community/mathlib/pull/4484))
#### Estimated changes
Modified src/order/bounded_lattice.lean




## [2020-10-06 22:45:52](https://github.com/leanprover-community/mathlib/commit/f4ccbdf)
feat(data/nat/basic): add_succ_lt_add ([#4483](https://github.com/leanprover-community/mathlib/pull/4483))
Add the lemma that, for natural numbers, if `a < b` and `c < d` then
`a + c + 1 < b + d` (i.e. a stronger version of `add_lt_add` for the
natural number case).  `library_search` did not find this in mathlib.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.add_succ_lt_add



## [2020-10-06 22:45:50](https://github.com/leanprover-community/mathlib/commit/f88234d)
feat(measure_theory): integral of a non-negative function is >0 iff μ(support f) > 0 ([#4410](https://github.com/leanprover-community/mathlib/pull/4410))
Also add a few supporting lemmas
#### Estimated changes
Modified src/algebra/order.lean
- \+ *lemma* has_le.le.le_iff_eq
- \+ *lemma* has_le.le.lt_iff_ne

Modified src/data/indicator_function.lean
- \+ *lemma* set.indicator_of_support_subset
- \+ *lemma* set.indicator_support

Modified src/data/support.lean
- \+ *lemma* function.support_eq_empty_iff

Modified src/measure_theory/bochner_integration.lean
- \+ *lemma* measure_theory.integral_eq_zero_iff_of_nonneg
- \+ *lemma* measure_theory.integral_eq_zero_iff_of_nonneg_ae
- \+ *lemma* measure_theory.integral_pos_iff_support_of_nonneg
- \+ *lemma* measure_theory.integral_pos_iff_support_of_nonneg_ae

Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.lintegral_eq_zero_iff
- \+ *lemma* measure_theory.lintegral_pos_iff_support

Modified src/measure_theory/interval_integral.lean
- \+ *lemma* interval_integral.integral_eq_integral_of_support_subset
- \+ *lemma* interval_integral.integral_eq_zero_iff_of_le_of_nonneg_ae
- \+ *lemma* interval_integral.integral_eq_zero_iff_of_nonneg_ae
- \+ *lemma* interval_integral.integral_non_measurable
- \+ *lemma* interval_integral.integral_pos_iff_support_of_nonneg_ae'
- \+ *lemma* interval_integral.integral_pos_iff_support_of_nonneg_ae
- \+ *lemma* interval_integral.integral_zero
- \+ *lemma* measure_theory.integrable.interval_integrable

Modified src/measure_theory/lebesgue_measure.lean
- \+ *lemma* filter.eventually.volume_pos_of_nhds_real

Modified src/measure_theory/set_integral.lean
- \+ *lemma* continuous.integrable_of_compact_closure_support
- \+ *lemma* measure_theory.set_integral_eq_zero_iff_of_nonneg_ae
- \+ *lemma* measure_theory.set_integral_pos_iff_support_of_nonneg_ae

Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_le.le_iff_eq

Modified src/topology/algebra/ordered.lean
- \+ *lemma* filter.eventually.exists_Ioo_subset

Modified src/topology/basic.lean
- \+ *lemma* is_open.eventually_mem



## [2020-10-06 21:23:34](https://github.com/leanprover-community/mathlib/commit/5192fd9)
feat(data/polynomial/degree/basic): add lemmas dealing with monomials, their support and their nat_degrees ([#4475](https://github.com/leanprover-community/mathlib/pull/4475))
#### Estimated changes
Modified src/data/polynomial/degree/basic.lean
- \+ *lemma* polynomial.card_support_C_mul_X_pow_le_one
- \+ *lemma* polynomial.le_degree_of_mem_supp
- \+ *lemma* polynomial.le_nat_degree_of_mem_supp
- \+ *lemma* polynomial.mem_support_C_mul_X_pow
- \+ *lemma* polynomial.nat_degree_C_mul_X_pow
- \+ *lemma* polynomial.nat_degree_C_mul_X_pow_le
- \+ *lemma* polynomial.nat_degree_C_mul_X_pow_of_nonzero
- \+ *lemma* polynomial.nat_degree_eq_support_max'
- \+ *lemma* polynomial.nat_degree_mem_support_of_nonzero
- \+ *lemma* polynomial.nonempty_support_iff
- \+ *lemma* polynomial.support_C_mul_X_pow
- \+ *lemma* polynomial.support_C_mul_X_pow_nonzero



## [2020-10-06 21:23:32](https://github.com/leanprover-community/mathlib/commit/d768e46)
feat(ring_theory/witt_vector/structure_polynomial): witt_structure_rat{_prop} ([#4464](https://github.com/leanprover-community/mathlib/pull/4464))
This is the first PR in a series on a fundamental theorem for Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
Added src/ring_theory/witt_vector/structure_polynomial.lean
- \+ *theorem* witt_structure_rat_exists_unique
- \+ *theorem* witt_structure_rat_prop



## [2020-10-06 19:36:49](https://github.com/leanprover-community/mathlib/commit/7948b5a)
chore(*): fix authorship for split files ([#4480](https://github.com/leanprover-community/mathlib/pull/4480))
A few files with missing copyright headers in [#4477](https://github.com/leanprover-community/mathlib/pull/4477) came from splitting up older files, so the attribution was incorrect:
- `data/setoid/partition.lean` was split from `data/setoid.lean` in [#2853](https://github.com/leanprover-community/mathlib/pull/2853).
- `data/finset/order.lean` was split from `algebra/big_operators.lean` in [#3495](https://github.com/leanprover-community/mathlib/pull/3495).
- `group_theory/submonoid/operations.lean` was split from `group_theory/submonoid.lean` in  [#3058](https://github.com/leanprover-community/mathlib/pull/3058).
#### Estimated changes
Modified src/data/finset/order.lean


Modified src/data/setoid/partition.lean


Modified src/group_theory/submonoid/operations.lean




## [2020-10-06 17:40:04](https://github.com/leanprover-community/mathlib/commit/ac05889)
chore(topology/list): one import per line ([#4479](https://github.com/leanprover-community/mathlib/pull/4479))
This one seems to have slipped through previous efforts
#### Estimated changes
Modified src/topology/list.lean




## [2020-10-06 15:23:11](https://github.com/leanprover-community/mathlib/commit/e559ca9)
chore(*): add copyright headers ([#4477](https://github.com/leanprover-community/mathlib/pull/4477))
#### Estimated changes
Modified src/category_theory/category/pairwise.lean


Modified src/category_theory/limits/punit.lean


Modified src/data/finset/order.lean


Modified src/data/list/indexes.lean


Modified src/data/setoid/partition.lean


Modified src/group_theory/submonoid/operations.lean


Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean




## [2020-10-06 15:23:09](https://github.com/leanprover-community/mathlib/commit/7416127)
feat(data/polynomial/ring_division): add multiplicity of sum of polynomials is at least minimum of multiplicities ([#4442](https://github.com/leanprover-community/mathlib/pull/4442))
I've added the lemma `root_multiplicity_add` inside `data/polynomial/ring_division` that says that the multiplicity of a root in a sum of two polynomials is at least the minimum of the multiplicities.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+ *lemma* min_pow_dvd_add

Modified src/data/polynomial/ring_division.lean
- \+ *lemma* polynomial.root_multiplicity_X_sub_C_pow
- \+ *lemma* polynomial.root_multiplicity_add
- \+ *lemma* polynomial.root_multiplicity_of_dvd



## [2020-10-06 12:41:50](https://github.com/leanprover-community/mathlib/commit/8d19939)
feat(*): make `int.le` irreducible ([#4474](https://github.com/leanprover-community/mathlib/pull/4474))
There's very rarely a reason to unfold `int.le` and it can create trouble: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/deep.20recursion.20was.20detected.20at.20'replace'
#### Estimated changes
Modified src/algebra/field_power.lean


Modified src/algebra/gcd_monoid.lean


Modified src/data/int/basic.lean


Modified src/data/int/range.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/tactic/linarith/preprocessing.lean


Modified src/tactic/omega/eq_elim.lean




## [2020-10-06 12:41:47](https://github.com/leanprover-community/mathlib/commit/99e308d)
chore(parity): even and odd in semiring ([#4473](https://github.com/leanprover-community/mathlib/pull/4473))
Replaces the ad-hoc `nat.even`, `nat.odd`, `int.even` and `int.odd` by definitions that make sense in semirings and get that `odd` can be `rintros`/`rcases`'ed. This requires almost no change except that `even` is not longer usable as a dot notation (which I see as a feature since I find `even n` to be more readable than `n.even`).
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *def* even
- \+ *lemma* even_iff_two_dvd
- \+ *def* odd

Modified src/analysis/convex/specific_functions.lean
- \+/\- *lemma* convex_on_pow_of_even
- \+/\- *lemma* int_prod_range_nonneg

Modified src/analysis/mean_inequalities.lean


Modified src/data/int/parity.lean
- \- *def* int.even
- \+/\- *theorem* int.even_add
- \+/\- *theorem* int.even_bit0
- \+/\- *theorem* int.even_coe_nat
- \+/\- *theorem* int.even_iff
- \+/\- *theorem* int.even_mul
- \+/\- *theorem* int.even_neg
- \+/\- *theorem* int.even_pow
- \+/\- *theorem* int.even_sub
- \+/\- *theorem* int.even_zero
- \+/\- *theorem* int.mod_two_ne_one
- \+/\- *theorem* int.mod_two_ne_zero
- \+/\- *theorem* int.not_even_bit1
- \+/\- *theorem* int.not_even_one
- \- *def* int.odd
- \- *lemma* int.odd_def
- \+ *theorem* int.odd_iff
- \+ *lemma* int.odd_iff_not_even
- \+/\- *theorem* int.two_dvd_ne_zero

Modified src/data/nat/parity.lean
- \+/\- *theorem* nat.even.add
- \+/\- *theorem* nat.even.sub
- \- *def* nat.even
- \+/\- *theorem* nat.even_add
- \+/\- *theorem* nat.even_bit0
- \+/\- *theorem* nat.even_iff
- \+/\- *theorem* nat.even_mul
- \+/\- *theorem* nat.even_pow
- \+/\- *theorem* nat.even_sub
- \+/\- *theorem* nat.even_succ
- \+/\- *theorem* nat.mod_two_ne_one
- \+/\- *theorem* nat.mod_two_ne_zero
- \+/\- *theorem* nat.not_even_bit1
- \- *def* nat.odd
- \- *lemma* nat.odd_def
- \+ *theorem* nat.odd_iff
- \+ *lemma* nat.odd_iff_not_even

Modified src/number_theory/sum_four_squares.lean




## [2020-10-06 12:41:45](https://github.com/leanprover-community/mathlib/commit/1d1a041)
chore(data/mv_polynomial/basic): coeff_mul, more golfing and speedup ([#4472](https://github.com/leanprover-community/mathlib/pull/4472))
#### Estimated changes
Modified src/algebra/group_with_zero.lean
- \+ *lemma* mul_eq_zero_of_ne_zero_imp_eq_zero

Modified src/data/mv_polynomial/basic.lean




## [2020-10-06 12:41:43](https://github.com/leanprover-community/mathlib/commit/8cebd2b)
chore(algebra/algebra): Split subalgebras into their own file ([#4471](https://github.com/leanprover-community/mathlib/pull/4471))
This matches how `subring` and `submonoid` both have their own files.
This also remove `noncomputable theory` which is unnecessary for almost all the definitions
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *def* alg_equiv.of_bijective
- \- *def* alg_hom.cod_restrict
- \- *lemma* alg_hom.coe_range
- \- *theorem* alg_hom.injective_cod_restrict
- \- *lemma* alg_hom.mem_range
- \- *def* algebra.adjoin
- \- *theorem* algebra.bijective_algebra_map_iff
- \- *def* algebra.bot_equiv
- \- *def* algebra.bot_equiv_of_injective
- \- *theorem* algebra.coe_bot
- \- *theorem* algebra.coe_top
- \- *theorem* algebra.comap_top
- \- *theorem* algebra.eq_top_iff
- \- *theorem* algebra.map_bot
- \- *theorem* algebra.map_top
- \- *theorem* algebra.mem_bot
- \- *theorem* algebra.mem_top
- \- *theorem* algebra.surjective_algebra_map_iff
- \- *def* algebra.to_top
- \- *lemma* mem_subalgebra_of_is_subring
- \- *lemma* mem_subalgebra_of_subring
- \- *lemma* mem_subalgebra_of_subsemiring
- \- *theorem* subalgebra.add_mem
- \- *theorem* subalgebra.algebra_map_mem
- \- *theorem* subalgebra.coe_int_mem
- \- *theorem* subalgebra.coe_nat_mem
- \- *lemma* subalgebra.coe_val
- \- *def* subalgebra.comap'
- \- *def* subalgebra.comap
- \- *theorem* subalgebra.ext
- \- *theorem* subalgebra.ext_iff
- \- *theorem* subalgebra.gsmul_mem
- \- *theorem* subalgebra.list_prod_mem
- \- *theorem* subalgebra.list_sum_mem
- \- *def* subalgebra.map
- \- *lemma* subalgebra.map_injective
- \- *theorem* subalgebra.map_le
- \- *lemma* subalgebra.map_mono
- \- *theorem* subalgebra.mem_coe
- \- *lemma* subalgebra.mem_map
- \- *lemma* subalgebra.mem_to_submodule
- \- *theorem* subalgebra.mul_mem
- \- *theorem* subalgebra.multiset_prod_mem
- \- *theorem* subalgebra.multiset_sum_mem
- \- *theorem* subalgebra.neg_mem
- \- *theorem* subalgebra.nsmul_mem
- \- *theorem* subalgebra.one_mem
- \- *theorem* subalgebra.pow_mem
- \- *theorem* subalgebra.prod_mem
- \- *theorem* subalgebra.range_le
- \- *theorem* subalgebra.range_subset
- \- *lemma* subalgebra.range_val
- \- *theorem* subalgebra.smul_mem
- \- *theorem* subalgebra.srange_le
- \- *theorem* subalgebra.sub_mem
- \- *theorem* subalgebra.sum_mem
- \- *def* subalgebra.to_submodule
- \- *theorem* subalgebra.to_submodule_inj
- \- *theorem* subalgebra.to_submodule_injective
- \- *def* subalgebra.to_subring
- \- *def* subalgebra.under
- \- *def* subalgebra.val
- \- *lemma* subalgebra.val_apply
- \- *theorem* subalgebra.zero_mem
- \- *structure* subalgebra
- \- *def* subalgebra_of_is_subring
- \- *def* subalgebra_of_subring
- \- *def* subalgebra_of_subsemiring

Added src/algebra/algebra/subalgebra.lean
- \+ *def* alg_hom.cod_restrict
- \+ *lemma* alg_hom.coe_range
- \+ *theorem* alg_hom.injective_cod_restrict
- \+ *lemma* alg_hom.mem_range
- \+ *def* algebra.adjoin
- \+ *theorem* algebra.bijective_algebra_map_iff
- \+ *theorem* algebra.coe_bot
- \+ *theorem* algebra.coe_top
- \+ *theorem* algebra.comap_top
- \+ *theorem* algebra.eq_top_iff
- \+ *theorem* algebra.map_bot
- \+ *theorem* algebra.map_top
- \+ *theorem* algebra.mem_bot
- \+ *theorem* algebra.mem_top
- \+ *theorem* algebra.surjective_algebra_map_iff
- \+ *def* algebra.to_top
- \+ *lemma* mem_subalgebra_of_is_subring
- \+ *lemma* mem_subalgebra_of_subring
- \+ *lemma* mem_subalgebra_of_subsemiring
- \+ *theorem* subalgebra.add_mem
- \+ *theorem* subalgebra.algebra_map_mem
- \+ *theorem* subalgebra.coe_int_mem
- \+ *theorem* subalgebra.coe_nat_mem
- \+ *lemma* subalgebra.coe_val
- \+ *def* subalgebra.comap'
- \+ *def* subalgebra.comap
- \+ *theorem* subalgebra.ext
- \+ *theorem* subalgebra.ext_iff
- \+ *theorem* subalgebra.gsmul_mem
- \+ *theorem* subalgebra.list_prod_mem
- \+ *theorem* subalgebra.list_sum_mem
- \+ *def* subalgebra.map
- \+ *lemma* subalgebra.map_injective
- \+ *theorem* subalgebra.map_le
- \+ *lemma* subalgebra.map_mono
- \+ *theorem* subalgebra.mem_coe
- \+ *lemma* subalgebra.mem_map
- \+ *lemma* subalgebra.mem_to_submodule
- \+ *theorem* subalgebra.mul_mem
- \+ *theorem* subalgebra.multiset_prod_mem
- \+ *theorem* subalgebra.multiset_sum_mem
- \+ *theorem* subalgebra.neg_mem
- \+ *theorem* subalgebra.nsmul_mem
- \+ *theorem* subalgebra.one_mem
- \+ *theorem* subalgebra.pow_mem
- \+ *theorem* subalgebra.prod_mem
- \+ *theorem* subalgebra.range_le
- \+ *theorem* subalgebra.range_subset
- \+ *lemma* subalgebra.range_val
- \+ *theorem* subalgebra.smul_mem
- \+ *theorem* subalgebra.srange_le
- \+ *theorem* subalgebra.sub_mem
- \+ *theorem* subalgebra.sum_mem
- \+ *def* subalgebra.to_submodule
- \+ *theorem* subalgebra.to_submodule_inj
- \+ *theorem* subalgebra.to_submodule_injective
- \+ *def* subalgebra.to_subring
- \+ *def* subalgebra.under
- \+ *def* subalgebra.val
- \+ *lemma* subalgebra.val_apply
- \+ *theorem* subalgebra.zero_mem
- \+ *structure* subalgebra
- \+ *def* subalgebra_of_is_subring
- \+ *def* subalgebra_of_subring
- \+ *def* subalgebra_of_subsemiring

Modified src/algebra/category/Algebra/basic.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/ring_theory/adjoin.lean




## [2020-10-06 12:41:42](https://github.com/leanprover-community/mathlib/commit/94bc31d)
lint(logic/unique): module doc, docstring ([#4461](https://github.com/leanprover-community/mathlib/pull/4461))
#### Estimated changes
Modified src/logic/unique.lean




## [2020-10-06 12:41:40](https://github.com/leanprover-community/mathlib/commit/2fc6598)
lint(group_theory/eckmann_hilton): docs, module docs, unused argument ([#4459](https://github.com/leanprover-community/mathlib/pull/4459))
#### Estimated changes
Modified src/group_theory/eckmann_hilton.lean
- \+/\- *def* eckmann_hilton.comm_group



## [2020-10-06 12:41:38](https://github.com/leanprover-community/mathlib/commit/f4207aa)
feat(data/*): lemmas about lists and finsets ([#4457](https://github.com/leanprover-community/mathlib/pull/4457))
A part of [#4316](https://github.com/leanprover-community/mathlib/pull/4316)
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.prod_mk

Modified src/data/fintype/basic.lean
- \+ *lemma* fin.univ_def
- \+ *lemma* finset.univ_eq_empty
- \+/\- *lemma* finset.univ_nonempty
- \+ *lemma* finset.univ_nonempty_iff

Modified src/data/fintype/card.lean
- \+ *theorem* fin.prod_of_fn
- \+ *theorem* fin.prod_univ_def

Modified src/data/list/basic.lean
- \+ *lemma* list.attach_eq_nil
- \+ *lemma* list.pmap_eq_nil
- \+ *lemma* list.prod_update_nth

Modified src/data/list/nodup.lean
- \+ *lemma* list.nodup.map_update

Modified src/data/list/of_fn.lean
- \+ *lemma* list.of_fn_const
- \+/\- *theorem* list.of_fn_succ
- \+/\- *theorem* list.of_fn_zero

Modified src/data/list/range.lean
- \+ *lemma* list.fin_range_eq_nil
- \+ *lemma* list.fin_range_zero
- \+ *theorem* list.of_fn_eq_map
- \+ *theorem* list.of_fn_id
- \+ *theorem* list.range'_eq_nil
- \+ *theorem* list.range_eq_nil

Modified src/data/multiset/basic.lean




## [2020-10-06 12:41:36](https://github.com/leanprover-community/mathlib/commit/1fa07c2)
chore(category_theory/monoidal): add module docs ([#4454](https://github.com/leanprover-community/mathlib/pull/4454))
#### Estimated changes
Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functor.lean




## [2020-10-06 12:41:33](https://github.com/leanprover-community/mathlib/commit/4d9406e)
feat(geometry/euclidean/monge_point): orthocentric systems ([#4448](https://github.com/leanprover-community/mathlib/pull/4448))
Define orthocentric systems of points, and prove some basic properties
of them.  In particular, if we say that an orthocentric system
consists of four points, one of which is the orthocenter of the
triangle formed by the other three, then each of the points is the
orthocenter of the triangle formed by the other three, and all four
triangles have the same circumradius.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean
- \+ *lemma* euclidean_geometry.cospherical.affine_independent

Modified src/geometry/euclidean/monge_point.lean
- \+ *lemma* euclidean_geometry.affine_span_of_orthocentric_system
- \+ *lemma* euclidean_geometry.exists_dist_eq_circumradius_of_subset_insert_orthocenter
- \+ *lemma* euclidean_geometry.exists_of_range_subset_orthocentric_system
- \+ *lemma* euclidean_geometry.orthocentric_system.affine_independent
- \+ *lemma* euclidean_geometry.orthocentric_system.eq_insert_orthocenter
- \+ *lemma* euclidean_geometry.orthocentric_system.exists_circumradius_eq
- \+ *def* euclidean_geometry.orthocentric_system



## [2020-10-06 10:22:31](https://github.com/leanprover-community/mathlib/commit/e9b43b6)
lint(data/equiv/ring): docstrings, inhabited ([#4460](https://github.com/leanprover-community/mathlib/pull/4460))
#### Estimated changes
Modified src/data/equiv/ring.lean




## [2020-10-06 10:22:29](https://github.com/leanprover-community/mathlib/commit/58a54d3)
chore(category_theory/*): doc-strings ([#4453](https://github.com/leanprover-community/mathlib/pull/4453))
#### Estimated changes
Modified src/category_theory/endomorphism.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/monoidal/functor.lean




## [2020-10-06 10:22:27](https://github.com/leanprover-community/mathlib/commit/6b59725)
chore(control/traversable/{basic,equiv,instances,lemmas}): linting ([#4444](https://github.com/leanprover-community/mathlib/pull/4444))
The `nolint`s in `instances.lean` are there because all the arguments need to be there for `is_lawful_traversable`.  In the same file, I moved `traverse_map` because it does not need the `is_lawful_applicative` instances.
#### Estimated changes
Modified src/control/traversable/basic.lean
- \+ *def* applicative_transformation.id_transformation

Modified src/control/traversable/equiv.lean


Modified src/control/traversable/instances.lean


Modified src/control/traversable/lemmas.lean




## [2020-10-06 10:22:25](https://github.com/leanprover-community/mathlib/commit/372d294)
feat(data/finsupp): lift a collection of `add_monoid_hom`s to an `add_monoid_hom` on `α →₀ β` ([#4395](https://github.com/leanprover-community/mathlib/pull/4395))
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *theorem* linear_map.to_add_monoid_hom_injective

Modified src/data/finsupp/basic.lean
- \+ *lemma* finsupp.add_closure_Union_range_single
- \+ *lemma* finsupp.add_hom_ext
- \+/\- *lemma* finsupp.hom_ext
- \+ *def* finsupp.lift_add_hom
- \+ *lemma* finsupp.lift_add_hom_apply
- \+ *lemma* finsupp.lift_add_hom_single_add_hom
- \+ *lemma* finsupp.lift_add_hom_symm_apply
- \+ *lemma* finsupp.prod_of_support_subset
- \+/\- *lemma* finsupp.prod_single_index
- \+ *def* finsupp.single_add_hom



## [2020-10-06 09:02:45](https://github.com/leanprover-community/mathlib/commit/b1d3ef9)
chore(data/mv_polynomial/basic): speedup coeff_mul ([#4469](https://github.com/leanprover-community/mathlib/pull/4469))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean




## [2020-10-06 09:02:43](https://github.com/leanprover-community/mathlib/commit/c08a868)
feat(trailing_degree): added two lemmas support_X, support_X_empty computing the support of X, simplified a couple of lemmas ([#4294](https://github.com/leanprover-community/mathlib/pull/4294))
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.monomial_eq_X_pow
- \+ *lemma* polynomial.support_X
- \+ *lemma* polynomial.support_X_empty
- \+ *lemma* polynomial.support_X_pow
- \+ *lemma* polynomial.support_monomial'
- \+ *lemma* polynomial.support_monomial

Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.C_mul_X_pow_eq_monomial
- \- *lemma* polynomial.monomial_eq_smul_X
- \- *lemma* polynomial.monomial_one_eq_X_pow
- \+ *lemma* polynomial.support_C_mul_X_pow'
- \+ *lemma* polynomial.support_mul_X_pow

Modified src/data/polynomial/degree/trailing_degree.lean
- \+/\- *lemma* polynomial.trailing_degree_lt_wf

Modified src/data/polynomial/monomial.lean
- \+ *lemma* polynomial.monomial_eq_smul_X
- \+ *lemma* polynomial.monomial_one_eq_X_pow



## [2020-10-06 09:02:41](https://github.com/leanprover-community/mathlib/commit/fc7e943)
feat(normed_space/basic): remove localized notation ([#4246](https://github.com/leanprover-community/mathlib/pull/4246))
Remove notation for `tendsto` in `nhds`. 
Also make `is_bounded_linear_map.tendsto` protected.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* lim_norm
- \+/\- *lemma* lim_norm_zero

Modified src/analysis/normed_space/bounded_linear_maps.lean
- \- *lemma* is_bounded_linear_map.tendsto



## [2020-10-06 07:07:40](https://github.com/leanprover-community/mathlib/commit/32b5b68)
chore(topology/compacts): inhabit instances ([#4462](https://github.com/leanprover-community/mathlib/pull/4462))
#### Estimated changes
Modified src/topology/compacts.lean




## [2020-10-06 07:07:38](https://github.com/leanprover-community/mathlib/commit/d3b1d65)
lint(measure_theory): docstrings and style ([#4455](https://github.com/leanprover-community/mathlib/pull/4455))
#### Estimated changes
Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/probability_mass_function.lean
- \+/\- *def* pmf.bernoulli
- \+/\- *lemma* pmf.bind_apply
- \+/\- *def* pmf.of_fintype
- \+/\- *def* pmf.pure
- \+/\- *def* pmf.seq
- \+/\- *lemma* pmf.tsum_coe
- \+/\- *def* {u}



## [2020-10-06 02:54:28](https://github.com/leanprover-community/mathlib/commit/523bddb)
doc(data/nat/prime, data/int/basic, data/int/modeq): docstrings ([#4445](https://github.com/leanprover-community/mathlib/pull/4445))
Filling in docstrings on `data/nat/prime`, `data/int/basic`, `data/int/modeq`.
#### Estimated changes
Modified src/data/int/basic.lean


Modified src/data/int/modeq.lean


Modified src/data/nat/prime.lean




## [2020-10-06 02:54:26](https://github.com/leanprover-community/mathlib/commit/cd78599)
lint(category_theory/monad): doc-strings ([#4428](https://github.com/leanprover-community/mathlib/pull/4428))
#### Estimated changes
Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean




## [2020-10-06 02:04:28](https://github.com/leanprover-community/mathlib/commit/a228af6)
chore(scripts): update nolints.txt ([#4456](https://github.com/leanprover-community/mathlib/pull/4456))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-10-06 00:55:20](https://github.com/leanprover-community/mathlib/commit/27b6c23)
lint(category_theory/limits): docstrings and inhabited instances ([#4435](https://github.com/leanprover-community/mathlib/pull/4435))
#### Estimated changes
Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves/basic.lean


Modified src/category_theory/limits/shapes/products.lean




## [2020-10-06 00:09:52](https://github.com/leanprover-community/mathlib/commit/37879aa)
feat(undergrad): minimal polynomial ([#4308](https://github.com/leanprover-community/mathlib/pull/4308))
Adds minimal polynomial of endomorphisms to the undergrad list, although its use will be hard to guess for undergrads.
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/field_theory/minimal_polynomial.lean


Modified src/linear_algebra/eigenspace.lean




## [2020-10-05 23:18:37](https://github.com/leanprover-community/mathlib/commit/432da5f)
feat(measure_theory/integration): add lintegral_with_density_eq_lintegral_mul ([#4350](https://github.com/leanprover-community/mathlib/pull/4350))
This is Exercise 1.2.1 from Terence Tao's "An Epsilon of Room"
#### Estimated changes
Modified docs/references.bib


Modified src/measure_theory/integration.lean
- \+/\- *lemma* measure_theory.lintegral_add
- \+/\- *lemma* measure_theory.lintegral_add_measure
- \+/\- *lemma* measure_theory.lintegral_const_mul
- \+/\- *lemma* measure_theory.lintegral_smul_measure
- \+/\- *lemma* measure_theory.lintegral_sum_measure
- \+ *lemma* measure_theory.lintegral_with_density_eq_lintegral_mul
- \+/\- *lemma* measure_theory.with_density_apply



## [2020-10-05 22:01:48](https://github.com/leanprover-community/mathlib/commit/97c444e)
lint(topology/algebra): docstrings ([#4446](https://github.com/leanprover-community/mathlib/pull/4446))
#### Estimated changes
Modified src/topology/algebra/group.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/uniform_ring.lean




## [2020-10-05 19:45:24](https://github.com/leanprover-community/mathlib/commit/21158c4)
lint(data/pnat): Docstrings and an unused argument in `pnat.basic`, `pnat.factors` ([#4443](https://github.com/leanprover-community/mathlib/pull/4443))
Adds docstrings
Changes `div_exact` from having one unused input of type `k | m` to `div_exact m k`.
#### Estimated changes
Modified src/data/pnat/basic.lean
- \+/\- *def* pnat.div_exact
- \+/\- *theorem* pnat.mul_div_exact

Modified src/data/pnat/factors.lean




## [2020-10-05 19:45:21](https://github.com/leanprover-community/mathlib/commit/45347f9)
lint(src/order/rel_iso): docstrings and inhabited ([#4441](https://github.com/leanprover-community/mathlib/pull/4441))
#### Estimated changes
Modified src/order/rel_iso.lean




## [2020-10-05 19:45:19](https://github.com/leanprover-community/mathlib/commit/2127165)
chore(linear_algebra/basis): split off `linear_independent.lean` ([#4440](https://github.com/leanprover-community/mathlib/pull/4440))
The file `basis.lean` was getting rather long (1500 lines), so I decided to split it into two not as long files at a natural point: everything using `linear_independent` but not `basis` can go into a new file `linear_independent.lean`. As a result, we can import `basis.lean` a bit later in the `ring_theory` hierarchy.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \- *lemma* disjoint_span_singleton
- \- *lemma* eq_of_linear_independent_of_span_subtype
- \- *lemma* exists_finite_card_le_of_finite_of_linear_independent_of_span
- \- *lemma* exists_linear_independent
- \- *lemma* exists_of_linear_independent_of_finite_span
- \- *lemma* le_of_span_le_span
- \- *theorem* linear_dependent_iff
- \- *lemma* linear_independent.comp
- \- *theorem* linear_independent.image'
- \- *lemma* linear_independent.image
- \- *lemma* linear_independent.image_subtype
- \- *lemma* linear_independent.injective
- \- *lemma* linear_independent.inl_union_inr
- \- *lemma* linear_independent.insert
- \- *lemma* linear_independent.mono
- \- *lemma* linear_independent.ne_zero
- \- *lemma* linear_independent.of_subtype_range
- \- *def* linear_independent.repr
- \- *lemma* linear_independent.repr_eq
- \- *lemma* linear_independent.repr_eq_single
- \- *lemma* linear_independent.repr_ker
- \- *lemma* linear_independent.repr_range
- \- *lemma* linear_independent.restrict_of_comp_subtype
- \- *lemma* linear_independent.to_subtype_range
- \- *lemma* linear_independent.total_comp_repr
- \- *def* linear_independent.total_equiv
- \- *lemma* linear_independent.total_repr
- \- *lemma* linear_independent.union
- \- *lemma* linear_independent.unique
- \- *def* linear_independent
- \- *lemma* linear_independent_Union_finite
- \- *lemma* linear_independent_Union_finite_subtype
- \- *lemma* linear_independent_Union_of_directed
- \- *lemma* linear_independent_bUnion_of_directed
- \- *theorem* linear_independent_comp_subtype
- \- *theorem* linear_independent_comp_subtype_disjoint
- \- *lemma* linear_independent_empty
- \- *lemma* linear_independent_empty_type
- \- *theorem* linear_independent_equiv'
- \- *theorem* linear_independent_equiv
- \- *theorem* linear_independent_iff''
- \- *theorem* linear_independent_iff'
- \- *theorem* linear_independent_iff
- \- *lemma* linear_independent_iff_not_mem_span
- \- *lemma* linear_independent_iff_not_smul_mem_span
- \- *theorem* linear_independent_iff_total_on
- \- *theorem* linear_independent_image
- \- *lemma* linear_independent_inl_union_inr'
- \- *theorem* linear_independent_insert'
- \- *theorem* linear_independent_insert
- \- *theorem* linear_independent_monoid_hom
- \- *lemma* linear_independent_of_comp
- \- *lemma* linear_independent_of_finite
- \- *lemma* linear_independent_of_zero_eq_one
- \- *lemma* linear_independent_sUnion_of_directed
- \- *lemma* linear_independent_singleton
- \- *lemma* linear_independent_span
- \- *theorem* linear_independent_subtype
- \- *theorem* linear_independent_subtype_disjoint
- \- *lemma* linear_independent_unique
- \- *lemma* mem_span_insert_exchange
- \- *lemma* span_le_span_iff
- \- *lemma* surjective_of_linear_independent_of_span

Added src/linear_algebra/linear_independent.lean
- \+ *lemma* disjoint_span_singleton
- \+ *lemma* eq_of_linear_independent_of_span_subtype
- \+ *lemma* exists_finite_card_le_of_finite_of_linear_independent_of_span
- \+ *lemma* exists_linear_independent
- \+ *lemma* exists_of_linear_independent_of_finite_span
- \+ *lemma* le_of_span_le_span
- \+ *theorem* linear_dependent_iff
- \+ *lemma* linear_independent.comp
- \+ *theorem* linear_independent.image'
- \+ *lemma* linear_independent.image
- \+ *lemma* linear_independent.image_subtype
- \+ *lemma* linear_independent.injective
- \+ *lemma* linear_independent.inl_union_inr
- \+ *lemma* linear_independent.insert
- \+ *lemma* linear_independent.mono
- \+ *lemma* linear_independent.ne_zero
- \+ *lemma* linear_independent.of_subtype_range
- \+ *def* linear_independent.repr
- \+ *lemma* linear_independent.repr_eq
- \+ *lemma* linear_independent.repr_eq_single
- \+ *lemma* linear_independent.repr_ker
- \+ *lemma* linear_independent.repr_range
- \+ *lemma* linear_independent.restrict_of_comp_subtype
- \+ *lemma* linear_independent.to_subtype_range
- \+ *lemma* linear_independent.total_comp_repr
- \+ *def* linear_independent.total_equiv
- \+ *lemma* linear_independent.total_repr
- \+ *lemma* linear_independent.union
- \+ *lemma* linear_independent.unique
- \+ *def* linear_independent
- \+ *lemma* linear_independent_Union_finite
- \+ *lemma* linear_independent_Union_finite_subtype
- \+ *lemma* linear_independent_Union_of_directed
- \+ *lemma* linear_independent_bUnion_of_directed
- \+ *theorem* linear_independent_comp_subtype
- \+ *theorem* linear_independent_comp_subtype_disjoint
- \+ *lemma* linear_independent_empty
- \+ *lemma* linear_independent_empty_type
- \+ *theorem* linear_independent_equiv'
- \+ *theorem* linear_independent_equiv
- \+ *theorem* linear_independent_iff''
- \+ *theorem* linear_independent_iff'
- \+ *theorem* linear_independent_iff
- \+ *lemma* linear_independent_iff_not_mem_span
- \+ *lemma* linear_independent_iff_not_smul_mem_span
- \+ *theorem* linear_independent_iff_total_on
- \+ *theorem* linear_independent_image
- \+ *lemma* linear_independent_inl_union_inr'
- \+ *theorem* linear_independent_insert'
- \+ *theorem* linear_independent_insert
- \+ *theorem* linear_independent_monoid_hom
- \+ *lemma* linear_independent_of_comp
- \+ *lemma* linear_independent_of_finite
- \+ *lemma* linear_independent_of_zero_eq_one
- \+ *lemma* linear_independent_sUnion_of_directed
- \+ *lemma* linear_independent_singleton
- \+ *lemma* linear_independent_span
- \+ *theorem* linear_independent_subtype
- \+ *theorem* linear_independent_subtype_disjoint
- \+ *lemma* linear_independent_unique
- \+ *lemma* mem_span_insert_exchange
- \+ *lemma* span_le_span_iff
- \+ *lemma* surjective_of_linear_independent_of_span

Modified src/ring_theory/algebra_tower.lean


Modified src/ring_theory/noetherian.lean




## [2020-10-05 19:45:18](https://github.com/leanprover-community/mathlib/commit/88c76ab)
feat(order/filter/ultrafilter): Add variant of `exists_ultrafilter`. ([#4436](https://github.com/leanprover-community/mathlib/pull/4436))
The lemma `exists_ultrafilter` tells us that any proper filter can be extended to an ultrafilter (using Zorn's lemma). This PR adds a variant, called `exists_ultrafilter_of_finite_inter_nonempty` which says that any collection of sets `S` can be extended to an ultrafilter whenever it satisfies the property that the intersection of any finite subcollection `T` is nonempty.
#### Estimated changes
Modified src/order/filter/ultrafilter.lean
- \+ *lemma* filter.exists_ultrafilter_of_finite_inter_nonempty



## [2020-10-05 19:45:15](https://github.com/leanprover-community/mathlib/commit/9151532)
lint(order/conditionally_complete_lattice): docstrings ([#4434](https://github.com/leanprover-community/mathlib/pull/4434))
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean




## [2020-10-05 19:45:13](https://github.com/leanprover-community/mathlib/commit/221ec60)
feat(ring_theory/ideal): ideals in product rings ([#4431](https://github.com/leanprover-community/mathlib/pull/4431))
#### Estimated changes
Modified src/algebra/group/prod.lean
- \+ *lemma* mul_equiv.coe_prod_comm
- \+ *lemma* mul_equiv.coe_prod_comm_symm
- \+ *def* mul_equiv.prod_comm

Modified src/algebra/ring/prod.lean
- \+ *lemma* ring_equiv.coe_coe_prod_comm
- \+ *lemma* ring_equiv.coe_coe_prod_comm_symm
- \+ *lemma* ring_equiv.coe_prod_comm
- \+ *lemma* ring_equiv.coe_prod_comm_symm
- \+ *lemma* ring_equiv.fst_comp_coe_prod_comm
- \+ *def* ring_equiv.prod_comm
- \+ *lemma* ring_equiv.snd_comp_coe_prod_comm

Modified src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* prime_spectrum.prime_spectrum_prod_symm_inl_as_ideal
- \+ *lemma* prime_spectrum.prime_spectrum_prod_symm_inr_as_ideal

Modified src/ring_theory/ideal/operations.lean
- \+ *theorem* ideal.map_is_prime_of_equiv
- \+ *lemma* ring_hom.ker_coe_equiv

Added src/ring_theory/ideal/prod.lean
- \+ *theorem* ideal.ideal_prod_eq
- \+ *def* ideal.ideal_prod_equiv
- \+ *lemma* ideal.ideal_prod_equiv_symm_apply
- \+ *theorem* ideal.ideal_prod_prime
- \+ *lemma* ideal.ideal_prod_prime_aux
- \+ *lemma* ideal.is_prime_ideal_prod_top'
- \+ *lemma* ideal.is_prime_ideal_prod_top
- \+ *lemma* ideal.is_prime_of_is_prime_prod_top'
- \+ *lemma* ideal.is_prime_of_is_prime_prod_top
- \+ *lemma* ideal.map_fst_prod
- \+ *lemma* ideal.map_prod_comm_prod
- \+ *lemma* ideal.map_snd_prod
- \+ *lemma* ideal.mem_prod
- \+ *lemma* ideal.prime_ideals_equiv_symm_inl
- \+ *lemma* ideal.prime_ideals_equiv_symm_inr
- \+ *lemma* ideal.prod.ext_iff
- \+ *def* ideal.prod
- \+ *lemma* ideal.prod_top_top



## [2020-10-05 19:45:10](https://github.com/leanprover-community/mathlib/commit/f9e3779)
lint(category_theory/whiskering): add doc-strings ([#4417](https://github.com/leanprover-community/mathlib/pull/4417))
#### Estimated changes
Modified src/category_theory/whiskering.lean
- \+/\- *def* category_theory.functor.left_unitor
- \+/\- *def* category_theory.functor.right_unitor



## [2020-10-05 19:45:08](https://github.com/leanprover-community/mathlib/commit/d2140ef)
feat(algebra/gcd_monoid): `gcd_mul_dvd_mul_gcd` ([#4386](https://github.com/leanprover-community/mathlib/pull/4386))
Adds a `gcd_monoid` version of `nat.gcd_mul_dvd_mul_gcd`
#### Estimated changes
Modified src/algebra/gcd_monoid.lean
- \+ *lemma* exists_dvd_and_dvd_of_dvd_mul
- \+ *theorem* gcd_mul_dvd_mul_gcd



## [2020-10-05 17:20:44](https://github.com/leanprover-community/mathlib/commit/c58c4e6)
docs(tactic/{fin_cases,lift}): lint ([#4421](https://github.com/leanprover-community/mathlib/pull/4421))
#### Estimated changes
Modified src/tactic/fin_cases.lean


Modified src/tactic/lift.lean




## [2020-10-05 17:20:42](https://github.com/leanprover-community/mathlib/commit/e89d0ed)
chore(*/multilinear): generalize `comp_linear_map` to a family of linear maps ([#4408](https://github.com/leanprover-community/mathlib/pull/4408))
Together with [#4316](https://github.com/leanprover-community/mathlib/pull/4316) this will give us multilinear maps corresponding to monomials.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/linear_algebra/multilinear.lean
- \+/\- *def* multilinear_map.comp_linear_map
- \+ *lemma* multilinear_map.comp_linear_map_apply

Modified src/logic/function/basic.lean
- \+ *lemma* function.apply_update

Modified src/topology/algebra/multilinear.lean
- \+ *lemma* continuous_multilinear_map.comp_continuous_linear_map_apply



## [2020-10-05 15:18:22](https://github.com/leanprover-community/mathlib/commit/7f74e6b)
feat(data/mv_polynomial/basic): map_map_range_eq_iff ([#4438](https://github.com/leanprover-community/mathlib/pull/4438))
Split off from [#4268](https://github.com/leanprover-community/mathlib/pull/4268)
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.map_map_range_eq_iff



## [2020-10-05 15:18:20](https://github.com/leanprover-community/mathlib/commit/39f5d6b)
feat(data/rat/basic): denom_eq_one_iff ([#4437](https://github.com/leanprover-community/mathlib/pull/4437))
Split off from [#4268](https://github.com/leanprover-community/mathlib/pull/4268)
#### Estimated changes
Modified src/data/rat/basic.lean
- \+ *lemma* rat.denom_eq_one_iff



## [2020-10-05 15:18:18](https://github.com/leanprover-community/mathlib/commit/22398f3)
chore(src/linear_algebra): linting ([#4427](https://github.com/leanprover-community/mathlib/pull/4427))
#### Estimated changes
Modified src/linear_algebra/dual.lean




## [2020-10-05 11:39:07](https://github.com/leanprover-community/mathlib/commit/ca269b4)
feat(linear_algebra/affine_space/finite_dimensional): collinearity ([#4433](https://github.com/leanprover-community/mathlib/pull/4433))
Define collinearity of a set of points in an affine space for a vector
space (as meaning the `vector_span` has dimension at most 1), and
prove some basic lemmas about it, leading to three points being
collinear if and only if they are not affinely independent.
#### Estimated changes
Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* affine_independent_iff_not_collinear
- \+ *def* collinear
- \+ *lemma* collinear_empty
- \+ *lemma* collinear_iff_dim_le_one
- \+ *lemma* collinear_iff_exists_forall_eq_smul_vadd
- \+ *lemma* collinear_iff_findim_le_one
- \+ *lemma* collinear_iff_not_affine_independent
- \+ *lemma* collinear_iff_of_mem
- \+ *lemma* collinear_insert_singleton
- \+ *lemma* collinear_singleton



## [2020-10-05 11:39:05](https://github.com/leanprover-community/mathlib/commit/b0fe280)
chore(category_theory/yoneda): doc-strings ([#4429](https://github.com/leanprover-community/mathlib/pull/4429))
#### Estimated changes
Modified src/category_theory/products/basic.lean


Modified src/category_theory/yoneda.lean




## [2020-10-05 11:39:03](https://github.com/leanprover-community/mathlib/commit/1501bf6)
chore(data/fin2): linting ([#4426](https://github.com/leanprover-community/mathlib/pull/4426))
#### Estimated changes
Modified src/data/fin2.lean




## [2020-10-05 11:39:01](https://github.com/leanprover-community/mathlib/commit/dd73dd2)
chore(linear_algebra/finsupp*): linting ([#4425](https://github.com/leanprover-community/mathlib/pull/4425))
#### Estimated changes
Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean




## [2020-10-05 11:38:58](https://github.com/leanprover-community/mathlib/commit/c058524)
chore(data/fintype/basic): linting ([#4424](https://github.com/leanprover-community/mathlib/pull/4424))
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2020-10-05 11:38:56](https://github.com/leanprover-community/mathlib/commit/70b8e82)
data(data/dlist/{basic,instances}): linting ([#4422](https://github.com/leanprover-community/mathlib/pull/4422))
#### Estimated changes
Modified src/data/dlist/basic.lean


Modified src/data/dlist/instances.lean




## [2020-10-05 11:38:54](https://github.com/leanprover-community/mathlib/commit/da1265c)
chore(data/buffer/basic): linting ([#4420](https://github.com/leanprover-community/mathlib/pull/4420))
#### Estimated changes
Modified src/data/buffer/basic.lean




## [2020-10-05 11:38:52](https://github.com/leanprover-community/mathlib/commit/768ff76)
chore(data/array/lemmas): linting ([#4419](https://github.com/leanprover-community/mathlib/pull/4419))
#### Estimated changes
Modified src/data/array/lemmas.lean
- \+/\- *def* equiv.d_array_equiv_fin



## [2020-10-05 11:38:50](https://github.com/leanprover-community/mathlib/commit/c370bd0)
chore(data/W): linting ([#4418](https://github.com/leanprover-community/mathlib/pull/4418))
#### Estimated changes
Modified src/data/W.lean




## [2020-10-05 11:38:48](https://github.com/leanprover-community/mathlib/commit/6a4fd24)
lint(category_theory/adjunction): add doc-strings ([#4415](https://github.com/leanprover-community/mathlib/pull/4415))
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/limits.lean




## [2020-10-05 11:38:46](https://github.com/leanprover-community/mathlib/commit/17b607f)
chore(algebra/direct_sum): linting ([#4412](https://github.com/leanprover-community/mathlib/pull/4412))
#### Estimated changes
Modified src/algebra/direct_sum.lean


Modified src/algebra/lie/basic.lean


Modified src/linear_algebra/direct_sum_module.lean




## [2020-10-05 11:38:43](https://github.com/leanprover-community/mathlib/commit/b44e927)
feat(data/finsupp): Make `finsupp.dom_congr` a `≃+` ([#4398](https://github.com/leanprover-community/mathlib/pull/4398))
Since this has additional structure, it may as well be part of the type
#### Estimated changes
Modified src/data/finsupp/basic.lean


Modified src/linear_algebra/basic.lean
- \+ *lemma* add_equiv.coe_to_linear_equiv
- \+ *lemma* add_equiv.coe_to_linear_equiv_symm
- \+ *def* add_equiv.to_linear_equiv

Modified src/linear_algebra/finsupp.lean




## [2020-10-05 11:38:41](https://github.com/leanprover-community/mathlib/commit/54a2c6b)
chore(algebra/group/with_one): prove `group_with_zero` earlier, drop custom lemmas ([#4385](https://github.com/leanprover-community/mathlib/pull/4385))
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximations.lean


Modified src/algebra/group/with_one.lean
- \+/\- *lemma* with_zero.coe_one
- \- *lemma* with_zero.div_eq_div
- \- *lemma* with_zero.div_eq_iff_mul_eq
- \- *lemma* with_zero.div_mul_cancel
- \- *lemma* with_zero.div_one
- \- *lemma* with_zero.div_zero
- \- *theorem* with_zero.mul_comm
- \- *lemma* with_zero.mul_div_cancel
- \- *lemma* with_zero.mul_inv_cancel
- \- *lemma* with_zero.mul_inv_rev
- \- *lemma* with_zero.mul_left_inv
- \- *lemma* with_zero.mul_right_inv
- \- *lemma* with_zero.one_div
- \- *lemma* with_zero.zero_div

Modified src/data/option/basic.lean
- \+ *lemma* option.coe_def



## [2020-10-05 11:38:39](https://github.com/leanprover-community/mathlib/commit/7236084)
refactor(linear_algebra/matrix): consistent naming ([#4345](https://github.com/leanprover-community/mathlib/pull/4345))
The naming of the maps between `linear_map` and `matrix` was a mess. This PR proposes to clean it up by standardising on two forms:
 * `linear_map.to_matrix` and `matrix.to_linear_map` are the equivalences (in the respective direction) between `M₁ →ₗ[R] M₂` and `matrix m n R`, given bases for `M₁` and `M₂`.
 * `linear_map.to_matrix'` and `matrix.to_lin'` are the equivalences between `((n → R) →ₗ[R] (m → R))` and `matrix m n R` in the respective directions
The following declarations are renamed:
 * `comp_to_matrix_mul` -> `linear_map.to_matrix'_comp`
 * `linear_equiv_matrix` -> `linear_map.to_matrix`
 * `linear_equiv_matrix_{apply,comp,id,mul,range}` -> `linear_map.to_matrix_{apply,comp,id,mul,range}`
 * `linear_equiv_matrix_symm_{apply,mul,one}` -> `matrix.to_lin_{apply,mul,one}`
 * `linear_equiv_matrix'` -> `linear_map.to_matrix'`
 * `linear_map.to_matrix_id` ->`linear_map.to_matrix'_id`
 * `matrix.mul_to_lin` -> `matrix.to_lin'_mul`
 * `matrix.to_lin` -> `matrix.mul_vec_lin` (which should get simplified to `matrix.to_lin'`)
 * `matrix.to_lin_apply` -> `matrix.to_lin'_apply`
 * `matrix.to_lin_one` -> `matrix.to_lin'_one`
 * `to_lin_to_matrix` -> `matrix.to_lin'_to_matrix'`
 * `to_matrix_to_lin` -> `linear_map.to_matrix'_to_lin'`
The following declarations are deleted as unnecessary:
 * `linear_equiv_matrix_apply'` (use `linear_map.to_matrix_apply` instead)
 * `linear_equiv_matrix'_apply` (the original `linear_map.to_matrix` doesn't exist any more)
 * `linear_equiv_matrix'_symm_apply` (the original `matrix.to_lin` doesn't exist any more)
 * `linear_map.to_matrixₗ` (use `linear_map.to_matrix'` instead)
 * `linear_map.to_matrix` (use `linear_map.to_matrix'` instead)
 * `linear_map.to_matrix_of_equiv` (use `linear_map.to_matrix'_apply` instead)
 * `matrix.eval` (use `matrix.to_lin'` instead)
 * `matrix.to_lin.is_add_monoid_hom` (use `linear_equiv.to_add_monoid_hom` instead)
 * `matrix.to_lin_{add,zero,neg}` (use `linear_equiv.map_{add,zero,neg} matrix.to_lin'` instead)
 * `matrix.to_lin_of_equiv` (use `matrix.to_lin'_apply` instead)
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Refactoring.20.60linear_map.20.3C-.3E.20matrix.60
#### Estimated changes
Modified src/algebra/lie/basic.lean


Modified src/field_theory/tower.lean


Modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis.range_repr
- \+ *lemma* is_basis.range_repr_self

Modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* matrix.to_bilin_form_comp
- \+/\- *lemma* matrix_is_adjoint_pair_bilin_form

Modified src/linear_algebra/matrix.lean
- \+/\- *def* alg_equiv_matrix'
- \+/\- *def* alg_equiv_matrix
- \- *def* linear_equiv_matrix'
- \- *lemma* linear_equiv_matrix'_apply
- \- *lemma* linear_equiv_matrix'_symm_apply
- \- *def* linear_equiv_matrix
- \- *lemma* linear_equiv_matrix_apply'
- \- *lemma* linear_equiv_matrix_apply
- \- *lemma* linear_equiv_matrix_id
- \- *theorem* linear_equiv_matrix_range
- \- *lemma* linear_equiv_matrix_symm_apply
- \- *lemma* linear_equiv_matrix_symm_one
- \- *lemma* linear_equiv_matrix_symm_transpose
- \- *lemma* linear_equiv_matrix_transpose
- \+ *def* linear_map.to_matrix'
- \+ *lemma* linear_map.to_matrix'_apply
- \+ *lemma* linear_map.to_matrix'_comp
- \+ *lemma* linear_map.to_matrix'_id
- \+ *lemma* linear_map.to_matrix'_mul
- \+ *lemma* linear_map.to_matrix'_symm
- \+ *lemma* linear_map.to_matrix'_to_lin'
- \+/\- *def* linear_map.to_matrix
- \+ *lemma* linear_map.to_matrix_apply'
- \+ *lemma* linear_map.to_matrix_apply
- \+ *lemma* linear_map.to_matrix_comp
- \+/\- *lemma* linear_map.to_matrix_id
- \+ *lemma* linear_map.to_matrix_mul
- \- *theorem* linear_map.to_matrix_of_equiv
- \+ *theorem* linear_map.to_matrix_range
- \+ *lemma* linear_map.to_matrix_symm
- \+ *lemma* linear_map.to_matrix_symm_transpose
- \+ *lemma* linear_map.to_matrix_to_lin
- \+ *lemma* linear_map.to_matrix_transpose
- \- *def* linear_map.to_matrixₗ
- \- *lemma* matrix.comp_to_matrix_mul
- \+ *lemma* matrix.diagonal_to_lin'
- \- *lemma* matrix.diagonal_to_lin
- \- *def* matrix.eval
- \+ *lemma* matrix.ker_diagonal_to_lin'
- \- *lemma* matrix.ker_diagonal_to_lin
- \- *lemma* matrix.linear_equiv_matrix_comp
- \- *lemma* matrix.linear_equiv_matrix_mul
- \- *lemma* matrix.linear_equiv_matrix_symm_mul
- \- *lemma* matrix.mul_to_lin
- \+ *def* matrix.mul_vec_lin
- \+ *lemma* matrix.mul_vec_lin_apply
- \+ *lemma* matrix.mul_vec_std_basis
- \+/\- *lemma* matrix.rank_vec_mul_vec
- \+ *def* matrix.to_lin'
- \+ *lemma* matrix.to_lin'_apply
- \+ *lemma* matrix.to_lin'_mul
- \+ *lemma* matrix.to_lin'_one
- \+ *lemma* matrix.to_lin'_symm
- \+ *lemma* matrix.to_lin'_to_matrix'
- \+/\- *def* matrix.to_lin
- \- *lemma* matrix.to_lin_add
- \+/\- *lemma* matrix.to_lin_apply
- \+ *lemma* matrix.to_lin_mul
- \- *lemma* matrix.to_lin_neg
- \- *theorem* matrix.to_lin_of_equiv
- \+/\- *lemma* matrix.to_lin_one
- \+ *lemma* matrix.to_lin_symm
- \+ *lemma* matrix.to_lin_to_matrix
- \- *lemma* matrix.to_lin_zero
- \- *lemma* to_lin_to_matrix
- \- *lemma* to_matrix_to_lin

Modified src/linear_algebra/quadratic_form.lean


Modified src/linear_algebra/special_linear_group.lean
- \+ *def* matrix.special_linear_group.to_lin'
- \+ *lemma* matrix.special_linear_group.to_lin'_mul
- \+ *lemma* matrix.special_linear_group.to_lin'_one
- \- *def* matrix.special_linear_group.to_lin
- \- *lemma* matrix.special_linear_group.to_lin_mul
- \- *lemma* matrix.special_linear_group.to_lin_one



## [2020-10-05 08:49:57](https://github.com/leanprover-community/mathlib/commit/67b312c)
chore(logic/relation): linting ([#4414](https://github.com/leanprover-community/mathlib/pull/4414))
#### Estimated changes
Modified src/logic/relation.lean




## [2020-10-05 08:49:55](https://github.com/leanprover-community/mathlib/commit/186660c)
feat(*): assorted `simp` lemmas for IMO 2019 q1 ([#4383](https://github.com/leanprover-community/mathlib/pull/4383))
* mark some lemmas about cancelling in expressions with `(-)` as `simp`;
* simplify `a * b = a * c` to `b = c ∨ a = 0`, and similarly for
  `a * c = b * c;
* change `priority` of `monoid.has_pow` and `group.has_pow` to the
  default priority.
* simplify `monoid.pow` and `group.gpow` to `has_pow.pow`.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+/\- *lemma* add_add_neg_cancel'_right
- \+/\- *lemma* add_add_sub_cancel
- \+/\- *lemma* add_sub_sub_cancel
- \+/\- *lemma* sub_add_add_cancel
- \+/\- *lemma* sub_add_sub_cancel'
- \+/\- *lemma* sub_sub_cancel
- \+/\- *lemma* sub_sub_sub_cancel_left

Modified src/algebra/group/commute.lean
- \+ *theorem* commute.inv_mul_cancel_assoc
- \+ *theorem* commute.mul_inv_cancel_assoc
- \+ *lemma* inv_mul_cancel_comm
- \+ *lemma* inv_mul_cancel_comm_assoc
- \+ *lemma* mul_inv_cancel_comm
- \+ *lemma* mul_inv_cancel_comm_assoc

Modified src/algebra/group_power/basic.lean
- \+ *lemma* group.gpow_eq_has_pow
- \+ *lemma* monoid.pow_eq_has_pow

Modified src/algebra/group_with_zero.lean
- \+ *lemma* mul_eq_mul_left_iff
- \+ *lemma* mul_eq_mul_right_iff

Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/special_functions/trigonometric.lean


Modified src/data/int/basic.lean


Modified src/data/padics/padic_integers.lean
- \- *lemma* padic_int.cast_pow
- \+ *lemma* padic_int.coet_pow

Modified src/set_theory/ordinal_notation.lean




## [2020-10-05 08:49:53](https://github.com/leanprover-community/mathlib/commit/8f4475b)
feat(combinatorics/partitions): Add partitions ([#4303](https://github.com/leanprover-community/mathlib/pull/4303))
#### Estimated changes
Modified src/combinatorics/composition.lean


Added src/combinatorics/partition.lean
- \+ *lemma* partition.count_of_sums_of_ne_zero
- \+ *lemma* partition.count_of_sums_zero
- \+ *def* partition.distincts
- \+ *def* partition.indiscrete_partition
- \+ *def* partition.odd_distincts
- \+ *def* partition.odds
- \+ *def* partition.of_composition
- \+ *lemma* partition.of_composition_surj
- \+ *def* partition.of_multiset
- \+ *def* partition.of_sums
- \+ *structure* partition



## [2020-10-05 07:39:36](https://github.com/leanprover-community/mathlib/commit/ca679ac)
chore(algebra/direct_limit): linting ([#4411](https://github.com/leanprover-community/mathlib/pull/4411))
#### Estimated changes
Modified src/algebra/direct_limit.lean
- \- *lemma* add_comm_group.direct_limit.directed_system
- \+/\- *lemma* add_comm_group.direct_limit.lift_unique
- \+/\- *theorem* add_comm_group.direct_limit.of.zero_exact
- \+/\- *def* add_comm_group.direct_limit
- \+/\- *theorem* module.direct_limit.exists_of
- \+/\- *theorem* module.direct_limit.lift_unique
- \+/\- *lemma* module.direct_limit.of.zero_exact_aux
- \+/\- *theorem* ring.direct_limit.exists_of
- \+/\- *theorem* ring.direct_limit.induction_on
- \+/\- *theorem* ring.direct_limit.lift_unique
- \+/\- *lemma* ring.direct_limit.of.zero_exact_aux
- \+/\- *theorem* ring.direct_limit.of_injective
- \+/\- *theorem* ring.direct_limit.polynomial.exists_of



## [2020-10-05 07:39:32](https://github.com/leanprover-community/mathlib/commit/581b141)
feat(data/complex): norm_cast lemmas ([#4405](https://github.com/leanprover-community/mathlib/pull/4405))
Mark various existing lemmas such as `abs_of_real` and `of_real_exp`
as `norm_cast` lemmas so that `norm_cast` and related tactics can
handle expressions involving those functions, and add lemmas
`of_real_prod` and `of_real_sum` to allow those tactics to work with
sums and products involving coercions from real to complex.
#### Estimated changes
Modified src/data/complex/basic.lean
- \+/\- *lemma* complex.abs_of_real
- \+ *lemma* complex.of_real_prod
- \+ *lemma* complex.of_real_sum

Modified src/data/complex/exponential.lean
- \+/\- *lemma* complex.of_real_cos
- \+/\- *lemma* complex.of_real_cosh
- \+/\- *lemma* complex.of_real_exp
- \+/\- *lemma* complex.of_real_sin
- \+/\- *lemma* complex.of_real_sinh
- \+/\- *lemma* complex.of_real_tan
- \+/\- *lemma* complex.of_real_tanh



## [2020-10-05 07:39:30](https://github.com/leanprover-community/mathlib/commit/1c8bb42)
feat(linear_algebra/affine_space/finite_dimensional): more lemmas ([#4389](https://github.com/leanprover-community/mathlib/pull/4389))
Add more lemmas concerning dimensions of affine spans of finite
families of points.  In particular, various forms of the lemma that `n + 1`
points are affinely independent if and only if their `vector_span` has
dimension `n` (or equivalently, at least `n`).  With suitable
definitions, this is equivalent to saying that three points are
affinely independent or collinear, four are affinely independent or
coplanar, etc., thus preparing for giving a definition of `collinear`
(for any set of points in an affine space for a vector space) in terms
of dimension and proving some basic properties of it including
relating it to affine independence.
#### Estimated changes
Modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* vector_span_range_eq_span_range_vsub_left_ne
- \+ *lemma* vector_span_range_eq_span_range_vsub_right_ne

Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* affine_independent_iff_findim_vector_span_eq
- \+ *lemma* affine_independent_iff_le_findim_vector_span
- \+ *lemma* affine_independent_iff_not_findim_vector_span_le
- \+ *lemma* findim_vector_span_image_finset_le
- \+ *lemma* findim_vector_span_le_iff_not_affine_independent
- \+ *lemma* findim_vector_span_range_le



## [2020-10-05 07:39:28](https://github.com/leanprover-community/mathlib/commit/565e961)
feat(number_theory/arithmetic_function): Define arithmetic functions/the Dirichlet ring ([#4352](https://github.com/leanprover-community/mathlib/pull/4352))
Defines a type `arithmetic_function A` of functions from `nat` to `A` sending 0 to 0
Defines the Dirichlet ring structure on `arithmetic_function A`
#### Estimated changes
Added src/number_theory/arithmetic_function.lean
- \+ *lemma* nat.arithmetic_function.add_apply
- \+ *lemma* nat.arithmetic_function.coe_coe
- \+ *theorem* nat.arithmetic_function.coe_inj
- \+ *theorem* nat.arithmetic_function.ext
- \+ *theorem* nat.arithmetic_function.ext_iff
- \+ *lemma* nat.arithmetic_function.int_coe_apply
- \+ *lemma* nat.arithmetic_function.map_zero
- \+ *lemma* nat.arithmetic_function.mul_apply
- \+ *lemma* nat.arithmetic_function.nat_coe_apply
- \+ *lemma* nat.arithmetic_function.one_apply_ne
- \+ *lemma* nat.arithmetic_function.one_one
- \+ *lemma* nat.arithmetic_function.to_fun_eq
- \+ *lemma* nat.arithmetic_function.zero_apply
- \+ *structure* nat.arithmetic_function

Modified src/number_theory/divisors.lean
- \+ *lemma* nat.dvd_of_mem_divisors



## [2020-10-05 05:24:10](https://github.com/leanprover-community/mathlib/commit/9ab7f05)
feat(category_theory/limits/terminal): limit of a diagram with initial object ([#4404](https://github.com/leanprover-community/mathlib/pull/4404))
If the index category for a functor has an initial object, the image of the functor is a limit.
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+/\- *def* category_theory.limits.as_empty_cocone
- \+/\- *def* category_theory.limits.as_empty_cone
- \+ *def* category_theory.limits.cocone_of_diagram_terminal
- \+ *def* category_theory.limits.colimit_of_diagram_terminal
- \+ *def* category_theory.limits.colimit_of_terminal
- \+ *def* category_theory.limits.cone_of_diagram_initial
- \+ *def* category_theory.limits.limit_of_diagram_initial
- \+ *def* category_theory.limits.limit_of_initial



## [2020-10-05 05:24:08](https://github.com/leanprover-community/mathlib/commit/91d9e96)
chore(algebra/ring/basic): docs, simps ([#4375](https://github.com/leanprover-community/mathlib/pull/4375))
* add docstrings to all typeclasses in `algebra/ring/basic`;
* add `ring_hom.inhabited := ⟨id α⟩` to make linter happy;
* given `f : α →+* β`, simplify `f.to_monoid_hom` and
`f.to_add_monoid_hom` to coercions;
* add `simp` lemmas for coercions of `ring_hom.mk f _ _ _ _` to
`monoid_hom` and `add_monoid_hom`.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \- *lemma* coe_add_monoid_hom
- \- *lemma* coe_monoid_hom
- \+ *lemma* ring_hom.coe_add_monoid_hom
- \+ *lemma* ring_hom.coe_add_monoid_hom_mk
- \+ *lemma* ring_hom.coe_monoid_hom
- \+ *lemma* ring_hom.coe_monoid_hom_mk
- \+ *lemma* ring_hom.to_add_monoid_hom_eq_coe
- \+/\- *lemma* ring_hom.to_fun_eq_coe
- \+ *lemma* ring_hom.to_monoid_hom_eq_coe

Modified src/ring_theory/algebra_tower.lean




## [2020-10-05 05:24:06](https://github.com/leanprover-community/mathlib/commit/08cdf37)
feat(analysis/complex/roots_of_unity): complex (primitive) roots of unity ([#4330](https://github.com/leanprover-community/mathlib/pull/4330))
#### Estimated changes
Modified docs/undergrad.yaml


Added src/analysis/complex/roots_of_unity.lean
- \+ *lemma* complex.card_primitive_roots
- \+ *lemma* complex.card_roots_of_unity
- \+ *lemma* complex.is_primitive_root_exp
- \+ *lemma* complex.is_primitive_root_exp_of_coprime
- \+ *lemma* complex.is_primitive_root_iff
- \+ *lemma* complex.mem_roots_of_unity

Modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* complex.two_pi_I_ne_zero
- \+ *lemma* real.pi_ne_zero



## [2020-10-05 04:08:17](https://github.com/leanprover-community/mathlib/commit/bf99889)
feat(category_theory/limits): lift self limit ([#4403](https://github.com/leanprover-community/mathlib/pull/4403))
A couple of little lemmas to simplify lift of a limit cone.
#### Estimated changes
Modified src/category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.is_colimit.desc_self
- \+ *lemma* category_theory.limits.is_limit.lift_self



## [2020-10-05 02:16:27](https://github.com/leanprover-community/mathlib/commit/916b5d3)
feat(topology): completion of separable space is separable ([#4399](https://github.com/leanprover-community/mathlib/pull/4399))
API change:
* `dense` renamed to `exists_between`;
* new `dense (s : set α)` means `∀ x, x ∈ closure s`.
#### Estimated changes
Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/specific_limits.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/nnreal.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/set/intervals/infinite.lean


Modified src/data/set/intervals/ord_connected.lean


Modified src/order/basic.lean
- \- *lemma* dense
- \+ *lemma* exists_between

Modified src/order/bounded_lattice.lean


Modified src/order/bounds.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/bases.lean
- \+ *lemma* dense_range.separable_space
- \+ *lemma* topological_space.exists_countable_closure_eq_univ

Modified src/topology/basic.lean
- \+ *lemma* continuous.dense_image_of_dense_range
- \+ *lemma* dense.closure_eq
- \+ *def* dense
- \+ *lemma* dense_iff_closure_eq
- \+/\- *lemma* dense_of_subset_dense
- \+ *lemma* dense_range.closure_range
- \+ *lemma* dense_range.comp
- \+ *def* dense_range.inhabited
- \+ *lemma* dense_range.nonempty
- \+ *def* dense_range
- \+ *lemma* dense_range_iff_closure_range

Modified src/topology/bounded_continuous_function.lean


Modified src/topology/constructions.lean
- \+ *lemma* dense_range.prod

Modified src/topology/continuous_on.lean
- \+ *lemma* dense_range.nhds_within_ne_bot

Modified src/topology/dense_embedding.lean
- \+ *lemma* dense_embedding.separable
- \+ *lemma* dense_inducing.separable
- \- *lemma* dense_range.closure_range
- \- *lemma* dense_range.comp
- \- *def* dense_range.inhabited
- \- *lemma* dense_range.nhds_within_ne_bot
- \- *lemma* dense_range.nonempty
- \- *lemma* dense_range.prod
- \- *def* dense_range
- \- *lemma* dense_range_iff_closure_range

Modified src/topology/instances/ennreal.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/uniform_space/completion.lean




## [2020-10-05 01:18:46](https://github.com/leanprover-community/mathlib/commit/fc09dba)
feat(analysis/special_functions/pow): exp_mul ([#4409](https://github.com/leanprover-community/mathlib/pull/4409))
Add the lemma that `exp (x * y) = (exp x) ^ y`, for real `x` and `y`.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+ *lemma* real.exp_mul



## [2020-10-04 20:49:23](https://github.com/leanprover-community/mathlib/commit/d13d21b)
feat(algebra/big_operators/order): bounding finite fibration cardinalities from below ([#4396](https://github.com/leanprover-community/mathlib/pull/4396))
Also including unrelated change `finset.inter_eq_sdiff_sdiff`.
#### Estimated changes
Modified src/algebra/big_operators/order.lean
- \+ *theorem* finset.mul_card_image_le_card
- \+ *theorem* finset.mul_card_image_le_card_of_maps_to

Modified src/data/finset/basic.lean
- \+ *lemma* finset.inter_eq_sdiff_sdiff



## [2020-10-04 19:18:31](https://github.com/leanprover-community/mathlib/commit/f437365)
feat(linear_algebra/dimension): one-dimensional spaces ([#4400](https://github.com/leanprover-community/mathlib/pull/4400))
Add some lemmas about the vectors in spaces and subspaces of dimension
at most 1.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.le_span_singleton_iff

Modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_le_one_iff
- \+ *lemma* dim_submodule_le_one_iff'
- \+ *lemma* dim_submodule_le_one_iff



## [2020-10-04 15:27:55](https://github.com/leanprover-community/mathlib/commit/8f53676)
feat(data/nat): Slightly strengthen nat.coprime_of_dvd/nat.coprime_of_dvd' ([#4368](https://github.com/leanprover-community/mathlib/pull/4368))
It is sufficient to consider prime factors.
The theorems now depend on nat.prime (data/nat/prime.lean), which depends on
data/nat/gcd.lean, so I moved them to prime.lean.
#### Estimated changes
Modified archive/imo/imo1959_q1.lean


Modified src/data/nat/gcd.lean
- \- *theorem* nat.coprime_of_dvd'
- \- *theorem* nat.coprime_of_dvd

Modified src/data/nat/modeq.lean


Modified src/data/nat/prime.lean
- \+ *theorem* nat.coprime_of_dvd'
- \+ *theorem* nat.coprime_of_dvd

Modified src/number_theory/pell.lean




## [2020-10-04 11:10:48](https://github.com/leanprover-community/mathlib/commit/729b60a)
feat(data/set/basic): subsingleton_coe ([#4388](https://github.com/leanprover-community/mathlib/pull/4388))
Add a lemma relating a set being a subsingleton set to its coercion to
a type being a subsingleton type.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.subsingleton_coe



## [2020-10-04 11:10:45](https://github.com/leanprover-community/mathlib/commit/e8b65e6)
feat(data/set/basic): eq_singleton_iff_unique_mem ([#4387](https://github.com/leanprover-community/mathlib/pull/4387))
We have this lemma for `finset`.  Add a version for `set` (with the
same name).
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.eq_singleton_iff_unique_mem



## [2020-10-04 11:10:43](https://github.com/leanprover-community/mathlib/commit/e1b1d17)
feat(algebra/group): construct `add_monoid_hom` from `map_sub` ([#4382](https://github.com/leanprover-community/mathlib/pull/4382))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* add_monoid_hom.coe_of_map_sub
- \+/\- *theorem* add_monoid_hom.map_sub
- \+ *def* add_monoid_hom.of_map_sub
- \+ *lemma* monoid_hom.coe_of_map_mul_inv
- \+ *def* monoid_hom.of_map_mul_inv



## [2020-10-04 11:10:41](https://github.com/leanprover-community/mathlib/commit/231271d)
chore(data/equiv/mul_add): add more `equiv` lemmas to `mul_equiv` namespace ([#4380](https://github.com/leanprover-community/mathlib/pull/4380))
Also make `apply_eq_iff_eq` and `apply_eq_iff_eq_symm_apply` use
implicit arguments.
#### Estimated changes
Modified src/category_theory/limits/types.lean


Modified src/data/equiv/basic.lean
- \+/\- *theorem* equiv.apply_eq_iff_eq
- \+/\- *theorem* equiv.apply_eq_iff_eq_symm_apply

Modified src/data/equiv/encodable/basic.lean


Modified src/data/equiv/mul_add.lean
- \+ *theorem* mul_equiv.apply_eq_iff_eq
- \+ *lemma* mul_equiv.apply_eq_iff_symm_apply
- \+ *lemma* mul_equiv.eq_symm_apply
- \+ *lemma* mul_equiv.symm_apply_eq

Modified src/data/opposite.lean


Modified src/group_theory/monoid_localization.lean




## [2020-10-04 11:10:39](https://github.com/leanprover-community/mathlib/commit/5d35b9a)
feat(algebra/gcd_monoid, data/*set/gcd): a few lemmas about gcds ([#4354](https://github.com/leanprover-community/mathlib/pull/4354))
Adds lemmas about gcds useful for proving Gauss's Lemma
#### Estimated changes
Modified src/algebra/gcd_monoid.lean
- \+ *lemma* gcd_eq_of_dvd_sub_left
- \+ *lemma* gcd_eq_of_dvd_sub_right

Modified src/data/finset/gcd.lean
- \+ *lemma* finset.gcd_eq_gcd_filter_ne_zero
- \+ *lemma* finset.gcd_eq_of_dvd_sub
- \+ *theorem* finset.gcd_eq_zero_iff
- \+ *lemma* finset.gcd_mul_left
- \+ *lemma* finset.gcd_mul_right

Modified src/data/multiset/gcd.lean
- \+ *theorem* multiset.gcd_eq_zero_iff



## [2020-10-04 09:48:24](https://github.com/leanprover-community/mathlib/commit/509dd9e)
feat(linear_algebra/basic): span_singleton smul lemmas ([#4394](https://github.com/leanprover-community/mathlib/pull/4394))
Add two submodule lemmas relating `span R ({r • x})` and `span R {x}`.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.span_singleton_smul_eq
- \+ *lemma* submodule.span_singleton_smul_le



## [2020-10-04 06:59:45](https://github.com/leanprover-community/mathlib/commit/c3d0835)
chore(data/mv_polynomial): rename `pderivative` to `pderiv` ([#4381](https://github.com/leanprover-community/mathlib/pull/4381))
This name matches `fderiv` and `deriv` we have in `analysis/`.
#### Estimated changes
Renamed src/data/mv_polynomial/pderivative.lean to src/data/mv_polynomial/pderiv.lean
- \+ *def* mv_polynomial.pderiv
- \+ *lemma* mv_polynomial.pderiv_C
- \+ *lemma* mv_polynomial.pderiv_C_mul
- \+ *lemma* mv_polynomial.pderiv_eq_zero_of_not_mem_vars
- \+ *lemma* mv_polynomial.pderiv_monomial
- \+ *lemma* mv_polynomial.pderiv_monomial_mul
- \+ *lemma* mv_polynomial.pderiv_monomial_single
- \+ *lemma* mv_polynomial.pderiv_mul
- \- *def* mv_polynomial.pderivative
- \- *lemma* mv_polynomial.pderivative_C
- \- *lemma* mv_polynomial.pderivative_C_mul
- \- *lemma* mv_polynomial.pderivative_eq_zero_of_not_mem_vars
- \- *lemma* mv_polynomial.pderivative_monomial
- \- *lemma* mv_polynomial.pderivative_monomial_mul
- \- *lemma* mv_polynomial.pderivative_monomial_single
- \- *lemma* mv_polynomial.pderivative_mul



## [2020-10-04 05:39:03](https://github.com/leanprover-community/mathlib/commit/e902cae)
feat(category_theory/limits/cofinal): better API for cofinal functors ([#4276](https://github.com/leanprover-community/mathlib/pull/4276))
This PR
1. Proves that `F : C ⥤ D` being cofinal is equivalent to `colimit (F ⋙ G) ≅ colimit G` for all `G : D ⥤ E`. (Previously we just had the implication.)
2. Proves that if `F` is cofinal then `limit (F.op ⋙ H) ≅ limit H` for all `H: Dᵒᵖ ⥤ E`.
#### Estimated changes
Modified src/category_theory/is_connected.lean
- \+ *lemma* category_theory.zag_symmetric
- \+ *lemma* category_theory.zigzag_symmetric

Modified src/category_theory/limits/cofinal.lean
- \+ *lemma* category_theory.cofinal.cofinal_of_colimit_comp_coyoneda_iso_punit
- \+ *def* category_theory.cofinal.colimit_comp_coyoneda_iso
- \+ *def* category_theory.cofinal.cones_equiv
- \+ *def* category_theory.cofinal.extend_cone
- \+ *def* category_theory.cofinal.extend_cone_cocone_to_cone
- \+ *def* category_theory.cofinal.extend_cone_cone_to_cocone
- \+ *lemma* category_theory.cofinal.has_limit_of_comp
- \+ *def* category_theory.cofinal.is_limit_extend_cone_equiv
- \+ *def* category_theory.cofinal.is_limit_whisker_equiv
- \+ *def* category_theory.cofinal.limit_cone_comp
- \+ *lemma* category_theory.cofinal.limit_cone_comp_aux
- \+ *def* category_theory.cofinal.limit_cone_of_comp
- \+ *def* category_theory.cofinal.limit_iso'
- \+ *def* category_theory.cofinal.limit_iso
- \+ *lemma* category_theory.cofinal.limit_pre_is_iso_aux
- \+ *lemma* category_theory.cofinal.zigzag_of_eqv_gen_quot_rel

Modified src/category_theory/limits/limits.lean
- \+ *lemma* category_theory.limits.is_limit.of_cone_equiv_apply_desc
- \+ *lemma* category_theory.limits.is_limit.of_cone_equiv_symm_apply_desc

Modified src/category_theory/limits/types.lean
- \+ *lemma* category_theory.limits.types.colimit_eq
- \+ *lemma* category_theory.limits.types.colimit_equiv_quot_apply
- \+ *def* category_theory.limits.types.quot.rel

Added src/category_theory/limits/yoneda.lean
- \+ *def* category_theory.coyoneda.colimit_cocone
- \+ *def* category_theory.coyoneda.colimit_cocone_is_colimit
- \+ *def* category_theory.coyoneda.colimit_coyoneda_iso

Modified src/category_theory/opposites.lean




## [2020-10-04 03:45:24](https://github.com/leanprover-community/mathlib/commit/e738e90)
feat(algebra/group_power/identities): named ring identities ([#4390](https://github.com/leanprover-community/mathlib/pull/4390))
This PR adds a new file containing some "named" ring identities provable by `ring`.
#### Estimated changes
Added src/algebra/group_power/identities.lean
- \+ *theorem* pow_four_add_four_mul_pow_four'
- \+ *theorem* pow_four_add_four_mul_pow_four
- \+ *theorem* pow_two_add_mul_pow_two_mul_pow_two_add_mul_pow_two
- \+ *theorem* pow_two_add_pow_two_mul_pow_two_add_pow_two
- \+ *theorem* sum_eight_sq_mul_sum_eight_sq
- \+ *theorem* sum_four_sq_mul_sum_four_sq

Modified src/number_theory/sum_four_squares.lean




## [2020-10-04 01:55:07](https://github.com/leanprover-community/mathlib/commit/f2044a5)
chore(scripts): update nolints.txt ([#4392](https://github.com/leanprover-community/mathlib/pull/4392))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-10-03 23:52:40](https://github.com/leanprover-community/mathlib/commit/333c216)
chore(algebra/group/type_tags): Use ≃ instead of → ([#4346](https://github.com/leanprover-community/mathlib/pull/4346))
These functions are all equivalences, so we may as well expose that in their type
This also fills in some conversions that were missing.
Unfortunately this requires some type ascriptions in a handful of places.
It might be possible to remove these somehow.
This zulip thread contains a mwe: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Type.20inference.20on.20.60.E2.86.92.60.20vs.20.60.E2.89.83.60/near/211922501.
#### Estimated changes
Modified src/algebra/group/type_tags.lean
- \+ *def* add_monoid_hom.to_multiplicative''
- \+/\- *def* add_monoid_hom.to_multiplicative'
- \+/\- *def* add_monoid_hom.to_multiplicative
- \+/\- *def* additive.of_mul
- \+/\- *def* additive.to_mul
- \+ *def* monoid_hom.to_additive''
- \+/\- *def* monoid_hom.to_additive'
- \+/\- *def* monoid_hom.to_additive
- \+/\- *def* multiplicative.of_add
- \+/\- *def* multiplicative.to_add
- \- *lemma* of_add_injective
- \- *lemma* of_mul_injective
- \- *lemma* to_add_injective
- \- *lemma* to_mul_injective

Modified src/data/equiv/mul_add.lean
- \+ *def* add_equiv.to_multiplicative''
- \+ *def* add_equiv.to_multiplicative'
- \+/\- *def* add_equiv.to_multiplicative
- \+ *def* mul_equiv.to_additive''
- \+ *def* mul_equiv.to_additive'
- \+/\- *def* mul_equiv.to_additive

Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/ring_theory/roots_of_unity.lean




## [2020-10-03 20:51:17](https://github.com/leanprover-community/mathlib/commit/a0ba5e7)
doc(data/real/*): add a few docstrings, `ereal.has_zero`, and `ereal.inhabited` ([#4378](https://github.com/leanprover-community/mathlib/pull/4378))
#### Estimated changes
Modified src/data/real/basic.lean


Modified src/data/real/ereal.lean


Modified src/data/real/nnreal.lean




## [2020-10-03 20:51:15](https://github.com/leanprover-community/mathlib/commit/e593ffa)
feat(algebra/ordered*): more simp lemmas ([#4359](https://github.com/leanprover-community/mathlib/pull/4359))
Simplify expressions like `0 < a * b`, `0 < a / b`, `a / b < 1` etc. to FOL formulas of inequalities on `a`, `b`.
#### Estimated changes
Modified src/algebra/gcd_monoid.lean


Modified src/algebra/group_power/basic.lean
- \+/\- *theorem* pow_nonneg
- \+/\- *theorem* pow_pos

Modified src/algebra/group_with_zero.lean
- \+ *lemma* inv_eq_one'

Modified src/algebra/order.lean
- \+ *lemma* ne.le_iff_lt
- \+ *lemma* ne.lt_or_lt

Modified src/algebra/ordered_field.lean
- \+ *lemma* div_le_one_iff
- \+ *lemma* div_lt_one_iff
- \+ *lemma* div_neg_iff
- \+ *lemma* div_nonneg_iff
- \+ *lemma* div_nonpos_iff
- \+ *lemma* div_pos_iff
- \+ *lemma* inv_le_one_iff
- \+ *lemma* inv_lt_one_iff
- \+ *lemma* inv_lt_one_iff_of_pos
- \+ *lemma* one_le_div_iff
- \+ *lemma* one_le_inv_iff
- \+ *lemma* one_lt_div_iff
- \+ *lemma* one_lt_inv_iff

Modified src/algebra/ordered_ring.lean
- \- *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero
- \+ *lemma* mul_neg_iff
- \+ *lemma* mul_nonneg_iff
- \+ *lemma* mul_nonpos_iff
- \+ *lemma* mul_pos_iff
- \+ *lemma* nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg
- \+/\- *lemma* pos_of_mul_pos_left
- \+/\- *lemma* pos_of_mul_pos_right

Modified src/analysis/hofer.lean


Modified src/data/int/basic.lean
- \+/\- *lemma* int.coe_nat_nonneg

Modified src/data/padics/hensel.lean


Modified src/data/rat/order.lean


Modified src/data/real/nnreal.lean


Modified src/number_theory/lucas_lehmer.lean




## [2020-10-03 18:56:38](https://github.com/leanprover-community/mathlib/commit/b790b27)
feat(slim_check): sampleable instance for generating functions and injective functions ([#3967](https://github.com/leanprover-community/mathlib/pull/3967))
This also adds `printable_prop` to trace why propositions hold or don't hold and `sampleable_ext` to allow the data structure generated and shrunken by `slim_check` to have a different type from the type we are looking for.
#### Estimated changes
Modified src/control/uliftable.lean
- \+/\- *def* uliftable.adapt_up

Modified src/data/list/perm.lean


Modified src/system/random/basic.lean


Modified src/tactic/slim_check.lean


Added src/testing/slim_check/functions.lean
- \+ *def* slim_check.injective_function.apply
- \+ *lemma* slim_check.injective_function.apply_id_injective
- \+ *lemma* slim_check.injective_function.apply_id_mem_iff
- \+ *def* slim_check.injective_function.list.apply_id
- \+ *lemma* slim_check.injective_function.list.apply_id_cons
- \+ *lemma* slim_check.injective_function.list.apply_id_eq_self
- \+ *lemma* slim_check.injective_function.list.apply_id_zip_eq
- \+ *def* slim_check.injective_function.perm.slice
- \+ *def* slim_check.injective_function.slice_sizes
- \+ *inductive* slim_check.injective_function
- \+ *def* slim_check.total_function.apply
- \+ *def* slim_check.total_function.list.to_finmap'
- \+ *def* slim_check.total_function.repr_aux
- \+ *def* slim_check.total_function.total.sizeof
- \+ *inductive* slim_check.total_function

Modified src/testing/slim_check/gen.lean
- \+ *def* slim_check.gen.choose_nat'
- \+ *def* slim_check.gen.elements
- \+ *def* slim_check.gen.freq
- \+ *def* slim_check.gen.freq_aux
- \- *def* slim_check.gen.one_of_aux
- \+ *def* slim_check.gen.resize

Modified src/testing/slim_check/sampleable.lean
- \+ *def* slim_check.int.has_sizeof
- \+ *def* slim_check.large.mk
- \+ *def* slim_check.large
- \+/\- *def* slim_check.print_samples
- \+ *def* slim_check.rec_shrink_with
- \+ *lemma* slim_check.rec_shrink_with_eq
- \+ *def* slim_check.small.mk
- \+ *def* slim_check.small
- \+/\- *def* slim_check.sum.shrink

Modified src/testing/slim_check/testable.lean
- \+ *def* slim_check.add_shrinks
- \+/\- *def* slim_check.add_var_to_counter_example
- \+ *def* slim_check.format_failure'
- \+ *def* slim_check.format_failure
- \+/\- *def* slim_check.minimize
- \+/\- *def* slim_check.minimize_aux
- \- *def* slim_check.test_result.to_string
- \+/\- *def* slim_check.trace_if_giveup
- \+ *def* slim_check.use_has_to_string.mk
- \+ *def* slim_check.use_has_to_string

Added test/mk_slim_check_test.lean


Modified test/slim_check.lean




## [2020-10-03 15:26:49](https://github.com/leanprover-community/mathlib/commit/c39170e)
doc(*): add a few short module docstrings ([#4370](https://github.com/leanprover-community/mathlib/pull/4370))
#### Estimated changes
Modified src/algebra/opposites.lean


Modified src/data/equiv/basic.lean


Modified src/data/opposite.lean




## [2020-10-03 10:25:54](https://github.com/leanprover-community/mathlib/commit/946ab02)
chore(.github/workflows): github action for crossing off PR dependencies ([#4367](https://github.com/leanprover-community/mathlib/pull/4367))
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md


Added .github/workflows/sync_closed_tasks.yaml




## [2020-10-03 05:00:16](https://github.com/leanprover-community/mathlib/commit/069952b)
chore(category_theory/limits/binary_products): weaken assumptions ([#4373](https://github.com/leanprover-community/mathlib/pull/4373))
weakens the assumptions on which limits need to exist for these constructions
not much of a change but the assumptions I used were too strong so just a small fix
#### Estimated changes
Modified src/category_theory/limits/shapes/constructions/preserve_binary_products.lean
- \+/\- *def* category_theory.limits.alternative_cone
- \+/\- *def* category_theory.limits.alternative_cone_is_limit



## [2020-10-03 05:00:15](https://github.com/leanprover-community/mathlib/commit/9e455c1)
feat(data/monoid_algebra): Allow R ≠ k in semimodule R (monoid_algebra k G) ([#4365](https://github.com/leanprover-community/mathlib/pull/4365))
Also does the same for the additive version `semimodule R (add_monoid_algebra k G)`.
#### Estimated changes
Modified src/algebra/monoid_algebra.lean
- \+/\- *lemma* add_monoid_algebra.alg_hom_ext
- \+/\- *lemma* add_monoid_algebra.alg_hom_ext_iff
- \+/\- *def* add_monoid_algebra.algebra_map'
- \+/\- *lemma* add_monoid_algebra.coe_algebra_map
- \+/\- *def* add_monoid_algebra.lift
- \+/\- *lemma* monoid_algebra.alg_hom_ext
- \+/\- *lemma* monoid_algebra.coe_algebra_map
- \+/\- *def* monoid_algebra.lift
- \+/\- *lemma* monoid_algebra.lift_apply
- \+/\- *lemma* monoid_algebra.lift_of
- \+/\- *lemma* monoid_algebra.lift_single
- \+/\- *lemma* monoid_algebra.lift_symm_apply
- \+/\- *lemma* monoid_algebra.lift_unique'
- \+/\- *lemma* monoid_algebra.lift_unique
- \+ *lemma* monoid_algebra.single_algebra_map_eq_algebra_map_mul_of



## [2020-10-03 04:08:49](https://github.com/leanprover-community/mathlib/commit/6ab3eb7)
chore(category_theory/limits/equalizers): some equalizer fixups ([#4372](https://github.com/leanprover-community/mathlib/pull/4372))
A couple of minor changes for equalizers:
- Add some `simps` attributes
- Removes some redundant brackets
- Simplify the construction of an iso between cones (+dual)
- Show the equalizer fork is a limit (+dual)
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *def* category_theory.limits.coequalizer_is_coequalizer
- \+/\- *lemma* category_theory.limits.cofork.condition
- \+/\- *def* category_theory.limits.cofork.ext
- \+ *def* category_theory.limits.equalizer_is_equalizer
- \+/\- *lemma* category_theory.limits.fork.condition
- \+/\- *def* category_theory.limits.fork.ext



## [2020-10-03 01:06:52](https://github.com/leanprover-community/mathlib/commit/6a52400)
chore(scripts): update nolints.txt ([#4371](https://github.com/leanprover-community/mathlib/pull/4371))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-10-02 20:49:45](https://github.com/leanprover-community/mathlib/commit/da24add)
feat(data/multiset): ordered sum lemmas ([#4305](https://github.com/leanprover-community/mathlib/pull/4305))
Add some lemmas about products in ordered monoids and sums in ordered add monoids, and a multiset count filter lemma (and a rename of a count filter lemma)
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.all_one_of_le_one_le_of_prod_eq_one
- \+ *lemma* list.one_le_prod_of_one_le
- \+ *lemma* list.single_le_prod
- \+ *lemma* list.sum_eq_zero_iff

Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.all_one_of_le_one_le_of_prod_eq_one
- \- *theorem* multiset.count_filter
- \+ *theorem* multiset.count_filter_of_neg
- \+ *theorem* multiset.count_filter_of_pos
- \+ *lemma* multiset.one_le_prod_of_one_le
- \+ *lemma* multiset.single_le_prod
- \+ *lemma* multiset.sum_eq_zero_iff



## [2020-10-02 18:01:52](https://github.com/leanprover-community/mathlib/commit/2634c1b)
feat(category_theory/cones): map_cone_inv as an equivalence ([#4253](https://github.com/leanprover-community/mathlib/pull/4253))
When `G` is an equivalence, we have `G.map_cone_inv : cone (F ⋙ G) → cone F`, and that this is an inverse to `G.map_cone`, but not quite that these constitute an equivalence of categories. This PR fixes that.
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+ *lemma* category_theory.equivalence.counit_app_functor
- \- *lemma* category_theory.equivalence.counit_functor
- \+ *lemma* category_theory.equivalence.counit_inv_app_functor
- \- *lemma* category_theory.equivalence.functor_unit
- \- *lemma* category_theory.equivalence.inverse_counit
- \+ *lemma* category_theory.equivalence.unit_app_inverse
- \+ *lemma* category_theory.equivalence.unit_inv_app_inverse
- \- *lemma* category_theory.equivalence.unit_inverse

Modified src/category_theory/limits/cones.lean
- \+ *def* category_theory.functor.map_cocone_inv
- \+ *def* category_theory.functor.map_cocone_inv_map_cocone
- \+ *def* category_theory.functor.map_cocone_map_cocone_inv
- \+ *def* category_theory.limits.cocones.functoriality_equivalence
- \+ *def* category_theory.limits.cones.functoriality_equivalence

Modified src/category_theory/limits/limits.lean


Modified src/category_theory/monoidal/transport.lean




## [2020-10-02 13:06:24](https://github.com/leanprover-community/mathlib/commit/2ce359b)
feat(data/nat/parity,data/int/parity): odd numbers ([#4357](https://github.com/leanprover-community/mathlib/pull/4357))
As discussed at
<https://leanprover.zulipchat.com/#narrow/stream/208328-IMO-grand-challenge/topic/formalizing.20IMO.20problems>,
define `nat.odd` and `int.odd` to allow a more literal expression
(outside of mathlib; for example, in formal olympiad problem
statements) of results whose informal statement refers to odd numbers.
These definitions are not expected to be used in mathlib beyond the
`simp` lemmas added here that translate them back to `¬ even`.  This
is similar to how `>` is defined but almost all mathlib results are
expected to use `<` instead.
It's likely that expressing olympiad problem statements literally in
Lean will end up using some other such definitions, where avoiding API
duplication means almost everything relevant in mathlib is developed
in terms of the expansion of the definition.
#### Estimated changes
Modified src/data/int/parity.lean
- \+ *def* int.odd
- \+ *lemma* int.odd_def

Modified src/data/nat/parity.lean
- \+ *def* nat.odd
- \+ *lemma* nat.odd_def



## [2020-10-02 12:12:21](https://github.com/leanprover-community/mathlib/commit/53570c0)
chore(README): add zulip badge ([#4362](https://github.com/leanprover-community/mathlib/pull/4362))
#### Estimated changes
Modified README.md




## [2020-10-02 10:14:33](https://github.com/leanprover-community/mathlib/commit/eeb9bb6)
feat(data/polynomial/coeff): single-variate `C_dvd_iff_dvd_coeff` ([#4355](https://github.com/leanprover-community/mathlib/pull/4355))
Adds a single-variate version of the lemma `mv_polynomial.C_dvd_iff_dvd_coeff`
(Useful for Gauss's Lemma)
#### Estimated changes
Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.C_dvd_iff_dvd_coeff



## [2020-10-02 10:14:31](https://github.com/leanprover-community/mathlib/commit/8876ba2)
feat(ring_theory/roots_of_unity): (primitive) roots of unity ([#4260](https://github.com/leanprover-community/mathlib/pull/4260))
#### Estimated changes
Added src/ring_theory/roots_of_unity.lean
- \+ *lemma* card_roots_of_unity
- \+ *lemma* is_primitive_root.card_primitive_roots
- \+ *lemma* is_primitive_root.card_roots_of_unity'
- \+ *lemma* is_primitive_root.card_roots_of_unity
- \+ *lemma* is_primitive_root.coe_subgroup_iff
- \+ *lemma* is_primitive_root.coe_units_iff
- \+ *lemma* is_primitive_root.eq_neg_one_of_two_right
- \+ *lemma* is_primitive_root.eq_pow_of_mem_roots_of_unity
- \+ *lemma* is_primitive_root.eq_pow_of_pow_eq_one
- \+ *lemma* is_primitive_root.fpow_eq_one
- \+ *lemma* is_primitive_root.fpow_eq_one_iff_dvd
- \+ *lemma* is_primitive_root.fpow_of_gcd_eq_one
- \+ *lemma* is_primitive_root.gpow_eq_one
- \+ *lemma* is_primitive_root.gpow_eq_one_iff_dvd
- \+ *lemma* is_primitive_root.gpow_of_gcd_eq_one
- \+ *lemma* is_primitive_root.gpowers_eq
- \+ *lemma* is_primitive_root.iff_def
- \+ *lemma* is_primitive_root.inv'
- \+ *lemma* is_primitive_root.inv
- \+ *lemma* is_primitive_root.inv_iff'
- \+ *lemma* is_primitive_root.inv_iff
- \+ *lemma* is_primitive_root.is_primitive_root_iff'
- \+ *lemma* is_primitive_root.is_primitive_root_iff
- \+ *lemma* is_primitive_root.is_unit
- \+ *lemma* is_primitive_root.mem_roots_of_unity
- \+ *lemma* is_primitive_root.mk_of_lt
- \+ *lemma* is_primitive_root.neg_one
- \+ *lemma* is_primitive_root.one
- \+ *lemma* is_primitive_root.one_right_iff
- \+ *lemma* is_primitive_root.pow_eq_one_iff_dvd
- \+ *lemma* is_primitive_root.pow_iff_coprime
- \+ *lemma* is_primitive_root.pow_inj
- \+ *lemma* is_primitive_root.pow_ne_one_of_pos_of_lt
- \+ *lemma* is_primitive_root.pow_of_coprime
- \+ *def* is_primitive_root.zmod_equiv_gpowers
- \+ *lemma* is_primitive_root.zmod_equiv_gpowers_apply_coe_int
- \+ *lemma* is_primitive_root.zmod_equiv_gpowers_apply_coe_nat
- \+ *lemma* is_primitive_root.zmod_equiv_gpowers_symm_apply_gpow'
- \+ *lemma* is_primitive_root.zmod_equiv_gpowers_symm_apply_gpow
- \+ *lemma* is_primitive_root.zmod_equiv_gpowers_symm_apply_pow'
- \+ *lemma* is_primitive_root.zmod_equiv_gpowers_symm_apply_pow
- \+ *structure* is_primitive_root
- \+ *lemma* map_roots_of_unity
- \+ *lemma* mem_primitive_roots
- \+ *lemma* mem_roots_of_unity
- \+ *lemma* mem_roots_of_unity_iff_mem_nth_roots
- \+ *def* primitive_roots
- \+ *def* roots_of_unity
- \+ *def* roots_of_unity_equiv_nth_roots
- \+ *lemma* roots_of_unity_equiv_nth_roots_apply
- \+ *lemma* roots_of_unity_equiv_nth_roots_symm_apply
- \+ *lemma* roots_of_unity_le_of_dvd



## [2020-10-02 08:35:04](https://github.com/leanprover-community/mathlib/commit/d631126)
chore(algebra): move algebra and monoid algebra to algebra/ ([#4298](https://github.com/leanprover-community/mathlib/pull/4298))
On the basis that all the basic definitions of algebraic gadgets are otherwise in `src/algebra/`, I'd like to move `ring_theory/algebra.lean`, `ring_theory/algebra_operations.lean`, and `data/monoid_algebra.lean` there too.
#### Estimated changes
Renamed src/ring_theory/algebra.lean to src/algebra/algebra/basic.lean


Renamed src/ring_theory/algebra_operations.lean to src/algebra/algebra/operations.lean


Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/free_algebra.lean


Modified src/algebra/lie/basic.lean


Renamed src/data/monoid_algebra.lean to src/algebra/monoid_algebra.lean


Modified src/algebra/ring_quot.lean


Modified src/data/complex/module.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/polynomial/basic.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/finsupp.lean


Modified src/representation_theory/maschke.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/tensor_product.lean


Modified src/topology/algebra/module.lean




## [2020-10-02 07:19:29](https://github.com/leanprover-community/mathlib/commit/1f91d93)
chore(ring_theory/power_series): rename variables ([#4361](https://github.com/leanprover-community/mathlib/pull/4361))
Use `R`, `S`, `T` for (semi)rings and `k` for a field.
#### Estimated changes
Modified src/ring_theory/power_series.lean
- \+/\- *lemma* mv_polynomial.coe_C
- \+/\- *lemma* mv_polynomial.coe_add
- \+/\- *lemma* mv_polynomial.coe_monomial
- \+/\- *lemma* mv_polynomial.coe_mul
- \+/\- *lemma* mv_polynomial.coe_one
- \+/\- *def* mv_polynomial.coe_to_mv_power_series.ring_hom
- \+/\- *lemma* mv_polynomial.coe_zero
- \+/\- *lemma* mv_polynomial.coeff_coe
- \+/\- *def* mv_power_series.C
- \+/\- *def* mv_power_series.X
- \+/\- *lemma* mv_power_series.X_def
- \+/\- *lemma* mv_power_series.X_dvd_iff
- \+/\- *lemma* mv_power_series.X_inj
- \+/\- *lemma* mv_power_series.X_pow_dvd_iff
- \+/\- *def* mv_power_series.coeff
- \+/\- *lemma* mv_power_series.coeff_C
- \+/\- *lemma* mv_power_series.coeff_C_mul
- \+/\- *lemma* mv_power_series.coeff_inv
- \+/\- *lemma* mv_power_series.coeff_inv_aux
- \+/\- *lemma* mv_power_series.coeff_inv_of_unit
- \+/\- *lemma* mv_power_series.coeff_map
- \+/\- *lemma* mv_power_series.coeff_monomial'
- \+/\- *lemma* mv_power_series.coeff_monomial
- \+/\- *lemma* mv_power_series.coeff_mul
- \+/\- *lemma* mv_power_series.coeff_mul_C
- \+/\- *lemma* mv_power_series.coeff_smul
- \+/\- *lemma* mv_power_series.coeff_trunc
- \+/\- *lemma* mv_power_series.coeff_zero
- \+/\- *lemma* mv_power_series.coeff_zero_C
- \+/\- *lemma* mv_power_series.coeff_zero_X
- \+/\- *lemma* mv_power_series.coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* mv_power_series.coeff_zero_mul_X
- \+/\- *lemma* mv_power_series.coeff_zero_one
- \+/\- *def* mv_power_series.constant_coeff
- \+/\- *lemma* mv_power_series.constant_coeff_C
- \+/\- *lemma* mv_power_series.constant_coeff_X
- \+/\- *lemma* mv_power_series.constant_coeff_inv
- \+/\- *lemma* mv_power_series.constant_coeff_inv_of_unit
- \+/\- *lemma* mv_power_series.constant_coeff_map
- \+/\- *lemma* mv_power_series.constant_coeff_one
- \+/\- *lemma* mv_power_series.constant_coeff_zero
- \+/\- *lemma* mv_power_series.ext
- \+/\- *lemma* mv_power_series.ext_iff
- \+/\- *lemma* mv_power_series.inv_eq_zero
- \+/\- *def* mv_power_series.inv_of_unit
- \+/\- *lemma* mv_power_series.inv_of_unit_eq'
- \+/\- *lemma* mv_power_series.inv_of_unit_eq
- \+/\- *lemma* mv_power_series.is_unit_constant_coeff
- \+/\- *def* mv_power_series.map
- \+/\- *lemma* mv_power_series.map_id
- \+/\- *def* mv_power_series.monomial
- \+/\- *lemma* mv_power_series.monomial_mul_monomial
- \+/\- *lemma* mv_power_series.monomial_zero_eq_C
- \+/\- *lemma* mv_power_series.monomial_zero_eq_C_apply
- \+/\- *lemma* mv_power_series.mul_inv_of_unit
- \+/\- *def* mv_power_series.trunc
- \+/\- *lemma* mv_power_series.trunc_C
- \+/\- *def* mv_power_series.trunc_fun
- \+/\- *lemma* mv_power_series.trunc_one
- \+/\- *def* mv_power_series
- \+/\- *lemma* polynomial.coe_C
- \+/\- *lemma* polynomial.coe_add
- \+/\- *lemma* polynomial.coe_monomial
- \+/\- *lemma* polynomial.coe_mul
- \+/\- *lemma* polynomial.coe_one
- \+/\- *def* polynomial.coe_to_power_series.ring_hom
- \+/\- *lemma* polynomial.coe_zero
- \+/\- *lemma* polynomial.coeff_coe
- \+/\- *def* power_series.C
- \+/\- *def* power_series.X
- \+/\- *lemma* power_series.X_dvd_iff
- \+/\- *lemma* power_series.X_eq
- \+/\- *lemma* power_series.X_pow_dvd_iff
- \+/\- *lemma* power_series.X_pow_eq
- \+/\- *lemma* power_series.X_prime
- \+/\- *def* power_series.coeff
- \+/\- *lemma* power_series.coeff_C
- \+/\- *lemma* power_series.coeff_C_mul
- \+/\- *lemma* power_series.coeff_inv
- \+/\- *lemma* power_series.coeff_inv_aux
- \+/\- *lemma* power_series.coeff_inv_of_unit
- \+/\- *lemma* power_series.coeff_map
- \+/\- *lemma* power_series.coeff_mk
- \+/\- *lemma* power_series.coeff_monomial'
- \+/\- *lemma* power_series.coeff_monomial
- \+/\- *lemma* power_series.coeff_mul
- \+/\- *lemma* power_series.coeff_mul_C
- \+/\- *lemma* power_series.coeff_of_lt_order
- \+/\- *lemma* power_series.coeff_one_X
- \+/\- *lemma* power_series.coeff_order
- \+/\- *lemma* power_series.coeff_smul
- \+/\- *lemma* power_series.coeff_succ_mul_X
- \+/\- *lemma* power_series.coeff_trunc
- \+/\- *lemma* power_series.coeff_zero_C
- \+/\- *lemma* power_series.coeff_zero_X
- \+/\- *lemma* power_series.coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* power_series.coeff_zero_mul_X
- \+/\- *lemma* power_series.coeff_zero_one
- \+/\- *def* power_series.constant_coeff
- \+/\- *lemma* power_series.constant_coeff_C
- \+/\- *lemma* power_series.constant_coeff_X
- \+/\- *lemma* power_series.constant_coeff_inv
- \+/\- *lemma* power_series.constant_coeff_inv_of_unit
- \+/\- *lemma* power_series.constant_coeff_one
- \+/\- *lemma* power_series.constant_coeff_zero
- \+/\- *lemma* power_series.eq_zero_or_eq_zero_of_mul_eq_zero
- \+/\- *lemma* power_series.ext
- \+/\- *lemma* power_series.ext_iff
- \+/\- *lemma* power_series.inv_eq_inv_aux
- \+/\- *lemma* power_series.inv_eq_zero
- \+/\- *def* power_series.inv_of_unit
- \+/\- *lemma* power_series.inv_of_unit_eq'
- \+/\- *lemma* power_series.inv_of_unit_eq
- \+/\- *lemma* power_series.is_unit_constant_coeff
- \+/\- *lemma* power_series.le_order
- \+/\- *lemma* power_series.le_order_add
- \+/\- *def* power_series.map
- \+/\- *lemma* power_series.map_id
- \+/\- *def* power_series.mk
- \+/\- *def* power_series.monomial
- \+/\- *lemma* power_series.monomial_eq_mk
- \+/\- *lemma* power_series.monomial_zero_eq_C
- \+/\- *lemma* power_series.monomial_zero_eq_C_apply
- \+/\- *lemma* power_series.mul_inv_of_unit
- \+/\- *lemma* power_series.nat_le_order
- \+/\- *def* power_series.order
- \+/\- *lemma* power_series.order_X
- \+/\- *lemma* power_series.order_X_pow
- \+/\- *lemma* power_series.order_add_of_order_eq
- \+/\- *lemma* power_series.order_eq
- \+/\- *lemma* power_series.order_eq_nat
- \+/\- *lemma* power_series.order_eq_top
- \+/\- *lemma* power_series.order_finite_of_coeff_ne_zero
- \+/\- *lemma* power_series.order_le
- \+/\- *lemma* power_series.order_monomial
- \+/\- *lemma* power_series.order_monomial_of_ne_zero
- \+/\- *lemma* power_series.order_mul
- \+/\- *lemma* power_series.order_mul_ge
- \+/\- *lemma* power_series.order_one
- \+/\- *lemma* power_series.order_zero
- \+/\- *lemma* power_series.span_X_is_prime
- \+/\- *def* power_series.trunc
- \+/\- *lemma* power_series.trunc_C
- \+/\- *lemma* power_series.trunc_add
- \+/\- *lemma* power_series.trunc_one
- \+/\- *lemma* power_series.trunc_zero
- \+/\- *def* power_series



## [2020-10-02 05:57:43](https://github.com/leanprover-community/mathlib/commit/140db10)
chore(data/monoid_algebra): Make the style in `lift` consistent ([#4347](https://github.com/leanprover-community/mathlib/pull/4347))
This continues from a06c87ed28989d062aa3d5324e880e62edf4a2f8, which changed add_monoid_algebra.lift but not monoid_algebra.lift.
Note only the additive proof needs `erw` (to unfold `multiplicative`).
#### Estimated changes
Modified src/data/monoid_algebra.lean




## [2020-10-02 01:04:21](https://github.com/leanprover-community/mathlib/commit/d41f386)
chore(scripts): update nolints.txt ([#4358](https://github.com/leanprover-community/mathlib/pull/4358))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-10-01 20:40:02](https://github.com/leanprover-community/mathlib/commit/4ef680b)
feat(group_theory): subgroups of real numbers ([#4334](https://github.com/leanprover-community/mathlib/pull/4334))
This fills the last hole in the "Topology of R" section of our undergrad curriculum: additive subgroups of real numbers are either dense or cyclic. Most of this PR is supporting material about ordered abelian groups. 
Co-Authored-By: Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/algebra/archimedean.lean
- \+ *lemma* decidable_linear_ordered_add_comm_group.exists_int_smul_near_of_pos'
- \+ *lemma* decidable_linear_ordered_add_comm_group.exists_int_smul_near_of_pos

Modified src/algebra/group_power/basic.lean
- \+ *theorem* gsmul_nonneg
- \+ *theorem* nsmul_lt_nsmul
- \+/\- *theorem* nsmul_nonneg
- \+ *lemma* nsmul_pos

Modified src/algebra/group_power/lemmas.lean
- \+ *theorem* gsmul_le_gsmul
- \+ *theorem* gsmul_le_gsmul_iff
- \+ *theorem* gsmul_lt_gsmul
- \+ *theorem* gsmul_lt_gsmul_iff
- \+ *lemma* gsmul_pos
- \+ *theorem* nsmul_le_nsmul_iff
- \+ *theorem* nsmul_lt_nsmul_iff

Added src/group_theory/archimedean.lean
- \+ *lemma* add_subgroup.cyclic_of_min
- \+ *lemma* int.subgroup_cyclic

Modified src/group_theory/subgroup.lean
- \+ *lemma* add_subgroup.closure_singleton_zero
- \+ *lemma* subgroup.bot_or_exists_ne_one
- \+ *lemma* subgroup.bot_or_nontrivial
- \+ *lemma* subgroup.closure_singleton_one
- \+ *lemma* subgroup.eq_bot_iff_forall
- \+ *lemma* subgroup.nontrivial_iff_exists_ne_one

Modified src/group_theory/submonoid/membership.lean
- \+ *lemma* add_submonoid.closure_singleton_zero
- \+ *lemma* submonoid.closure_singleton_one

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* submonoid.bot_or_exists_ne_one
- \+ *lemma* submonoid.bot_or_nontrivial
- \+ *lemma* submonoid.eq_bot_iff_forall
- \+ *lemma* submonoid.nontrivial_iff_exists_ne_one

Modified src/order/bounds.lean
- \+ *lemma* is_glb.exists_between_self_add'
- \+ *lemma* is_glb.exists_between_self_add
- \+ *lemma* is_lub.exists_between_sub_self'
- \+ *lemma* is_lub.exists_between_sub_self

Modified src/ring_theory/subring.lean
- \+ *lemma* add_subgroup.int_mul_mem

Modified src/topology/instances/real.lean
- \+ *lemma* real.mem_closure_iff
- \+ *lemma* real.subgroup_dense_of_no_min
- \+ *lemma* real.subgroup_dense_or_cyclic



## [2020-10-01 18:43:08](https://github.com/leanprover-community/mathlib/commit/4851857)
chore(analysis/normed_space): define `norm_one_class` ([#4323](https://github.com/leanprover-community/mathlib/pull/4323))
Many normed rings have `∥1⊫1`. Add a typeclass mixin for this property.
API changes:
* drop `normed_field.norm_one`, use `norm_one` instead;
* same with `normed_field.nnnorm_one`;
* new typeclass `norm_one_class` for `∥1∥ = 1`;
* add `list.norm_prod_le`, `list.norm_prod_le`, `finset.norm_prod_le`, `finset.norm_prod_le'`:
  norm of the product of finitely many elements is less than or equal to the product of their norms;
  versions with prime assume that a `list` or a `finset` is nonempty, while the other versions
  assume `[norm_one_class]`;
* rename `norm_pow_le` to `norm_pow_le'`, new `norm_pow_le` assumes `[norm_one_class]` instead
  of `0 < n`;
* add a few supporting lemmas about `list`s and `finset`s.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_mk

Modified src/analysis/asymptotics.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* eventually_norm_pow_le
- \+ *lemma* finset.norm_prod_le'
- \+ *lemma* finset.norm_prod_le
- \+ *lemma* list.norm_prod_le'
- \+ *lemma* list.norm_prod_le
- \+/\- *lemma* mul_left_bound
- \+/\- *lemma* mul_right_bound
- \+ *lemma* nnnorm_one
- \+/\- *lemma* norm_mul_le
- \+ *lemma* norm_pow_le'
- \+/\- *lemma* norm_pow_le
- \+ *lemma* normed_algebra.nontrivial
- \+ *lemma* normed_algebra.norm_one_class
- \- *lemma* normed_algebra.to_nonzero
- \- *lemma* normed_field.nnnorm_one
- \- *lemma* normed_field.norm_one
- \+/\- *lemma* units.norm_pos

Modified src/analysis/normed_space/units.lean


Modified src/analysis/specific_limits.lean


Modified src/data/finset/basic.lean
- \+ *theorem* finset.mk_cons
- \+ *theorem* finset.mk_zero
- \+ *theorem* finset.nonempty_cons
- \+ *lemma* finset.nonempty_mk_coe
- \+ *theorem* finset.not_nonempty_empty

Modified src/data/padics/padic_integers.lean
- \- *lemma* padic_int.norm_one



## [2020-10-01 17:37:36](https://github.com/leanprover-community/mathlib/commit/d5834ee)
feat(data/real/irrational): add a lemma to deduce nat_degree from irrational root ([#4349](https://github.com/leanprover-community/mathlib/pull/4349))
This PR is splitted from [#4301](https://github.com/leanprover-community/mathlib/pull/4301) .
#### Estimated changes
Modified src/data/real/irrational.lean
- \+ *lemma* nat_degree_gt_one_of_irrational_root



## [2020-10-01 17:37:34](https://github.com/leanprover-community/mathlib/commit/ddaa325)
feat(archive/imo): formalize IMO 1969 problem 1 ([#4261](https://github.com/leanprover-community/mathlib/pull/4261))
This is a formalization of the problem and solution for the first problem on the 1969 IMO:
Prove that there are infinitely many natural numbers $a$ with the following property: the number $z = n^4 + a$ is not prime for any natural number $n$
#### Estimated changes
Added archive/imo/imo1969_q1.lean
- \+ *lemma* factorization
- \+ *theorem* imo1969_q1
- \+ *lemma* int_large
- \+ *lemma* int_not_prime
- \+ *lemma* left_factor_large
- \+ *lemma* polynomial_not_prime
- \+ *lemma* right_factor_large



## [2020-10-01 16:43:25](https://github.com/leanprover-community/mathlib/commit/7767ef8)
feat(number_theory/divisors): defines the finsets of divisors/proper divisors, perfect numbers, etc. ([#4310](https://github.com/leanprover-community/mathlib/pull/4310))
Defines `nat.divisors n` to be the set of divisors of `n`, and `nat.proper_divisors` to be the set of divisors of `n` other than `n`.
Defines `nat.divisors_antidiagonal` in analogy to other `antidiagonal`s used to define convolutions
Defines `nat.perfect`, the predicate for perfect numbers
#### Estimated changes
Added src/number_theory/divisors.lean
- \+ *lemma* nat.divisor_le
- \+ *def* nat.divisors
- \+ *def* nat.divisors_antidiagonal
- \+ *lemma* nat.divisors_antidiagonal_one
- \+ *lemma* nat.divisors_antidiagonal_zero
- \+ *lemma* nat.divisors_eq_proper_divisors_insert_self
- \+ *lemma* nat.divisors_zero
- \+ *lemma* nat.fst_mem_divisors_of_mem_antidiagonal
- \+ *lemma* nat.map_swap_divisors_antidiagonal
- \+ *lemma* nat.mem_divisors
- \+ *lemma* nat.mem_divisors_antidiagonal
- \+ *lemma* nat.mem_proper_divisors
- \+ *def* nat.perfect
- \+ *theorem* nat.perfect_iff_sum_divisors_eq_two_mul
- \+ *theorem* nat.perfect_iff_sum_proper_divisors
- \+ *lemma* nat.proper_divisors.not_self_mem
- \+ *def* nat.proper_divisors
- \+ *lemma* nat.proper_divisors_zero
- \+ *lemma* nat.snd_mem_divisors_of_mem_antidiagonal
- \+ *lemma* nat.sum_divisors_eq_sum_proper_divisors_add_self
- \+ *lemma* nat.swap_mem_divisors_antidiagonal



## [2020-10-01 14:28:11](https://github.com/leanprover-community/mathlib/commit/f10dda0)
feat(data/nat/basic): simp-lemmas for bit0 and bit1 mod two ([#4343](https://github.com/leanprover-community/mathlib/pull/4343))
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.bit0_mod_two
- \+ *lemma* nat.bit1_mod_two



## [2020-10-01 14:28:07](https://github.com/leanprover-community/mathlib/commit/0fc7b29)
feat(data/mv_polynomial): stub on invertible elements ([#4320](https://github.com/leanprover-community/mathlib/pull/4320))
More from the Witt vector branch.
#### Estimated changes
Added src/data/mv_polynomial/invertible.lean


Modified src/ring_theory/algebra_tower.lean
- \+ *def* is_scalar_tower.invertible.algebra_tower
- \+ *def* is_scalar_tower.invertible_algebra_coe_nat



## [2020-10-01 14:28:01](https://github.com/leanprover-community/mathlib/commit/3d58fce)
feat(linear_algebra): determinant of `matrix.block_diagonal` ([#4300](https://github.com/leanprover-community/mathlib/pull/4300))
This PR shows the determinant of `matrix.block_diagonal` is the product of the determinant of each subblock.
The only contributing permutations in the expansion of the determinant are those which map each block to the same block. Each of those permutations has the form `equiv.prod_congr_left σ`. Using `equiv.perm.extend` and `equiv.prod_congr_right`, we can compute the sign of `equiv.prod_congr_left σ`, and with a bit of algebraic manipulation we reach the conclusion.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* int.coe_prod
- \+ *lemma* list.prod_to_finset
- \+ *lemma* nat.coe_prod
- \+ *lemma* units.coe_prod

Modified src/data/equiv/basic.lean
- \+ *lemma* equiv.perm.eq_of_prod_extend_right_ne
- \+ *lemma* equiv.perm.fst_prod_extend_right
- \+ *def* equiv.perm.prod_extend_right
- \+ *lemma* equiv.perm.prod_extend_right_apply_eq
- \+ *lemma* equiv.perm.prod_extend_right_apply_ne
- \+ *def* equiv.prod_congr_left
- \+ *lemma* equiv.prod_congr_left_apply
- \+ *lemma* equiv.prod_congr_left_trans_prod_comm
- \+ *lemma* equiv.prod_congr_refl_left
- \+ *lemma* equiv.prod_congr_refl_right
- \+ *def* equiv.prod_congr_right
- \+ *lemma* equiv.prod_congr_right_apply
- \+ *lemma* equiv.prod_congr_right_trans_prod_comm
- \+ *lemma* equiv.sigma_congr_right_sigma_equiv_prod
- \+ *lemma* equiv.sigma_equiv_prod_sigma_congr_right

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_pi_univ

Modified src/group_theory/perm/sign.lean
- \+/\- *lemma* equiv.perm.card_support_swap
- \+/\- *lemma* equiv.perm.eq_swap_of_is_cycle_of_apply_apply_eq_self
- \+/\- *lemma* equiv.perm.is_cycle_swap
- \+/\- *lemma* equiv.perm.is_cycle_swap_mul
- \+/\- *lemma* equiv.perm.is_cycle_swap_mul_aux₁
- \+/\- *lemma* equiv.perm.is_cycle_swap_mul_aux₂
- \+ *lemma* equiv.perm.prod_prod_extend_right
- \+/\- *lemma* equiv.perm.sign_cycle
- \+ *lemma* equiv.perm.sign_prod_congr_left
- \+ *lemma* equiv.perm.sign_prod_congr_right
- \+ *lemma* equiv.perm.sign_prod_extend_right
- \+/\- *lemma* equiv.perm.support_swap

Modified src/linear_algebra/determinant.lean
- \+ *lemma* matrix.det_block_diagonal



## [2020-10-01 14:27:59](https://github.com/leanprover-community/mathlib/commit/13e9cc4)
feat(linear_algebra/exterior_algebra): Add an exterior algebra ([#4297](https://github.com/leanprover-community/mathlib/pull/4297))
This adds the basic exterior algebra definitions using a very similar approach to `universal_enveloping_algebra`.
It's based off the `exterior_algebra` branch, dropping the `wedge` stuff for now as development in multilinear maps is happening elsewhere.
#### Estimated changes
Added src/linear_algebra/exterior_algebra.lean
- \+ *theorem* exterior_algebra.comp_ι_square_zero
- \+ *theorem* exterior_algebra.hom_ext
- \+ *def* exterior_algebra.lift
- \+ *theorem* exterior_algebra.lift_comp_ι
- \+ *theorem* exterior_algebra.lift_unique
- \+ *theorem* exterior_algebra.lift_ι_apply
- \+ *inductive* exterior_algebra.rel
- \+ *def* exterior_algebra.ι
- \+ *theorem* exterior_algebra.ι_comp_lift
- \+ *theorem* exterior_algebra.ι_square_zero
- \+ *def* exterior_algebra



## [2020-10-01 14:27:57](https://github.com/leanprover-community/mathlib/commit/268073a)
feat(geometry/manifold): derivative of the zero section of the tangent bundle ([#4292](https://github.com/leanprover-community/mathlib/pull/4292))
We show that the zero section of the tangent bundle to a smooth manifold is smooth, and compute its derivative.
Along the way, some streamlining of supporting material.
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* fderiv_const
- \+/\- *lemma* fderiv_id'
- \+ *lemma* fderiv_within_eq_fderiv

Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* basic_smooth_bundle_core.smooth_const_section
- \+ *lemma* smooth.mdifferentiable
- \+ *lemma* smooth.mdifferentiable_at
- \+ *lemma* smooth.mdifferentiable_within_at
- \+ *lemma* tangent_bundle.smooth_zero_section
- \+ *lemma* tangent_bundle.tangent_map_tangent_bundle_pure
- \+ *def* tangent_bundle.zero_section

Modified src/topology/topological_fiber_bundle.lean
- \+ *lemma* topological_fiber_bundle_core.continuous_const_section
- \+ *lemma* topological_fiber_bundle_core.local_triv'_apply
- \- *lemma* topological_fiber_bundle_core.local_triv'_fst
- \- *lemma* topological_fiber_bundle_core.local_triv'_inv_fst
- \+ *lemma* topological_fiber_bundle_core.local_triv'_symm_apply
- \+ *lemma* topological_fiber_bundle_core.local_triv_apply
- \- *lemma* topological_fiber_bundle_core.local_triv_fst
- \+/\- *lemma* topological_fiber_bundle_core.mem_local_triv_at_source



## [2020-10-01 14:27:55](https://github.com/leanprover-community/mathlib/commit/11cdc8c)
feat(data/polynomial/*) : as_sum_support  ([#4286](https://github.com/leanprover-community/mathlib/pull/4286))
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean


Modified src/data/polynomial/degree/basic.lean
- \- *lemma* polynomial.as_sum
- \+ *lemma* polynomial.as_sum_range
- \+ *lemma* polynomial.as_sum_support

Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval_finset_sum

Modified src/data/polynomial/monic.lean




## [2020-10-01 12:28:37](https://github.com/leanprover-community/mathlib/commit/0ccc157)
feat(data/nat/fact, analysis/specific_limits): rename nat.fact, add few lemmas about its behaviour along at_top ([#4309](https://github.com/leanprover-community/mathlib/pull/4309))
Main content : 
- Rename `nat.fact` to `nat.factorial`, and add notation `n!` in locale `factorial`. This fixes [#2786](https://github.com/leanprover-community/mathlib/pull/2786)
- Generalize `prod_inv_distrib` to `comm_group_with_zero` *without any nonzero assumptions*
- `factorial_tendsto_at_top` : n! --> infinity as n--> infinity
- `tendsto_factorial_div_pow_self_at_top` : n!/(n^n) --> 0 as n --> infinity
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.pow_eq_prod_const
- \+ *lemma* finset.prod_inv_distrib'

Modified src/algebra/big_operators/intervals.lean
- \- *lemma* finset.prod_Ico_id_eq_fact
- \+ *lemma* finset.prod_Ico_id_eq_factorial
- \+ *lemma* finset.prod_range_add_one_eq_factorial

Modified src/algebra/big_operators/order.lean
- \+ *lemma* finset.prod_le_one

Modified src/analysis/specific_limits.lean
- \+ *lemma* factorial_tendsto_at_top
- \+ *lemma* tendsto_factorial_div_pow_self_at_top

Modified src/data/complex/exponential.lean
- \- *lemma* complex.sum_div_fact_le
- \+ *lemma* complex.sum_div_factorial_le

Modified src/data/fintype/basic.lean
- \+/\- *lemma* fintype.card_perm
- \+/\- *lemma* length_perms_of_list

Modified src/data/list/perm.lean
- \+/\- *theorem* list.length_permutations

Modified src/data/nat/choose/basic.lean
- \- *theorem* nat.choose_eq_fact_div_fact
- \+ *theorem* nat.choose_eq_factorial_div_factorial
- \- *lemma* nat.choose_mul_fact_mul_fact
- \+ *lemma* nat.choose_mul_factorial_mul_factorial
- \- *theorem* nat.fact_mul_fact_dvd_fact
- \+ *theorem* nat.factorial_mul_factorial_dvd_factorial

Modified src/data/nat/choose/dvd.lean


Deleted src/data/nat/fact.lean
- \- *theorem* nat.dvd_fact
- \- *def* nat.fact
- \- *theorem* nat.fact_dvd_fact
- \- *lemma* nat.fact_eq_one
- \- *lemma* nat.fact_inj
- \- *theorem* nat.fact_le
- \- *lemma* nat.fact_lt
- \- *lemma* nat.fact_mul_pow_le_fact
- \- *theorem* nat.fact_ne_zero
- \- *theorem* nat.fact_one
- \- *theorem* nat.fact_pos
- \- *theorem* nat.fact_succ
- \- *theorem* nat.fact_zero
- \- *lemma* nat.monotone_fact
- \- *lemma* nat.one_lt_fact

Added src/data/nat/factorial.lean
- \+ *theorem* nat.dvd_factorial
- \+ *def* nat.factorial
- \+ *theorem* nat.factorial_dvd_factorial
- \+ *lemma* nat.factorial_eq_one
- \+ *lemma* nat.factorial_inj
- \+ *theorem* nat.factorial_le
- \+ *lemma* nat.factorial_lt
- \+ *lemma* nat.factorial_mul_pow_le_factorial
- \+ *theorem* nat.factorial_ne_zero
- \+ *theorem* nat.factorial_one
- \+ *theorem* nat.factorial_pos
- \+ *theorem* nat.factorial_succ
- \+ *theorem* nat.factorial_zero
- \+ *lemma* nat.monotone_factorial
- \+ *lemma* nat.one_lt_factorial
- \+ *lemma* nat.self_le_factorial

Modified src/data/nat/multiplicity.lean
- \- *lemma* nat.prime.multiplicity_fact
- \+ *lemma* nat.prime.multiplicity_factorial
- \- *lemma* nat.prime.pow_dvd_fact_iff
- \+ *lemma* nat.prime.pow_dvd_factorial_iff

Modified src/data/nat/prime.lean
- \- *lemma* nat.prime.dvd_fact
- \+ *lemma* nat.prime.dvd_factorial

Modified src/number_theory/primorial.lean


Modified src/number_theory/quadratic_reciprocity.lean
- \+/\- *lemma* zmod.wilsons_lemma



## [2020-10-01 09:16:51](https://github.com/leanprover-community/mathlib/commit/9c241b0)
feat(*): a few more tests for `summable`, docstrings ([#4325](https://github.com/leanprover-community/mathlib/pull/4325))
### Important new theorems:
* `summable_geometric_iff_norm_lt_1`: a geometric series in a normed field is summable iff the norm of the common ratio is less than 1;
* `summable.tendsto_cofinite_zero`: divergence test: if `f` is a `summable` function, then `f x` tends to zero along `cofinite`;
### API change
* rename `cauchy_seq_of_tendsto_nhds` to `filter.tendsto.cauchy_seq` to enable dot syntax.
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *lemma* summable_geometric_iff_norm_lt_1

Modified src/order/filter/cofinite.lean
- \+ *lemma* finset.eventually_cofinite_nmem
- \+ *lemma* set.finite.compl_mem_cofinite
- \+ *lemma* set.finite.eventually_cofinite_nmem
- \+/\- *lemma* set.infinite_iff_frequently_cofinite

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable.tendsto_cofinite_zero
- \+ *lemma* summable.vanishing
- \+/\- *lemma* summable_iff_cauchy_seq_finset

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* nnreal.exists_le_has_sum_of_le
- \+/\- *lemma* nnreal.has_sum_iff_tendsto_nat
- \+/\- *lemma* nnreal.summable_of_le
- \+/\- *lemma* nnreal.tendsto_sum_nat_add
- \+/\- *lemma* nnreal.tsum_comp_le_tsum_of_inj

Modified src/topology/sequences.lean


Modified src/topology/uniform_space/cauchy.lean
- \- *lemma* cauchy_seq_of_tendsto_nhds
- \+ *lemma* filter.tendsto.cauchy_map
- \+ *lemma* filter.tendsto.cauchy_seq



## [2020-10-01 09:16:49](https://github.com/leanprover-community/mathlib/commit/fb2b1de)
feat(algebra/ordered_ring): ask for 0 < 1 earlier. ([#4296](https://github.com/leanprover-community/mathlib/pull/4296))
It used to be that `linear_ordered_semiring` asked for `0 < 1`, while `ordered_semiring` didn't.
I'd prefer that `ordered_semiring` asks for this already:
1. because lots of interesting examples (e.g. rings of operators) satisfy this property
2. because the rest of mathlib doesn't care
#### Estimated changes
Modified src/algebra/ordered_ring.lean


Modified src/order/filter/filter_product.lean




## [2020-10-01 07:41:14](https://github.com/leanprover-community/mathlib/commit/9ceb114)
feat(analysis/normed_space/inner_product): Define the inner product based on `is_R_or_C` ([#4057](https://github.com/leanprover-community/mathlib/pull/4057))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* abs_norm_eq_norm

Modified src/analysis/normed_space/hahn_banach.lean


Added src/analysis/normed_space/inner_product.lean
- \+ *lemma* abs_inner_le_norm
- \+ *lemma* abs_real_inner_div_norm_mul_norm_eq_one_iff
- \+ *lemma* abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
- \+ *lemma* abs_real_inner_div_norm_mul_norm_le_one
- \+ *lemma* abs_real_inner_le_norm
- \+ *def* bilin_form_of_real_inner
- \+ *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \+ *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \+ *def* euclidean_space
- \+ *theorem* exists_norm_eq_infi_of_complete_convex
- \+ *theorem* exists_norm_eq_infi_of_complete_subspace
- \+ *lemma* findim_euclidean_space
- \+ *lemma* findim_euclidean_space_fin
- \+ *def* has_inner.is_R_or_C_to_real
- \+ *lemma* inner_abs_conj_sym
- \+ *lemma* inner_add_add_self
- \+ *lemma* inner_add_left
- \+ *lemma* inner_add_right
- \+ *lemma* inner_conj_sym
- \+ *lemma* inner_eq_zero_sym
- \+ *lemma* inner_im_symm
- \+ *lemma* inner_mul_conj_re_abs
- \+ *lemma* inner_mul_inner_self_le
- \+ *lemma* inner_neg_left
- \+ *lemma* inner_neg_neg
- \+ *lemma* inner_neg_right
- \+ *structure* inner_product_space.core
- \+ *def* inner_product_space.is_R_or_C_to_real
- \+ *lemma* inner_product_space.of_core.abs_inner_le_norm
- \+ *lemma* inner_product_space.of_core.inner_abs_conj_sym
- \+ *lemma* inner_product_space.of_core.inner_add_add_self
- \+ *lemma* inner_product_space.of_core.inner_add_left
- \+ *lemma* inner_product_space.of_core.inner_add_right
- \+ *lemma* inner_product_space.of_core.inner_conj_sym
- \+ *lemma* inner_product_space.of_core.inner_im_symm
- \+ *lemma* inner_product_space.of_core.inner_mul_conj_re_abs
- \+ *lemma* inner_product_space.of_core.inner_mul_inner_self_le
- \+ *lemma* inner_product_space.of_core.inner_neg_left
- \+ *lemma* inner_product_space.of_core.inner_neg_right
- \+ *lemma* inner_product_space.of_core.inner_norm_sq_eq_inner_self
- \+ *lemma* inner_product_space.of_core.inner_re_symm
- \+ *lemma* inner_product_space.of_core.inner_self_eq_norm_square
- \+ *lemma* inner_product_space.of_core.inner_self_eq_zero
- \+ *lemma* inner_product_space.of_core.inner_self_im_zero
- \+ *lemma* inner_product_space.of_core.inner_self_nonneg
- \+ *lemma* inner_product_space.of_core.inner_self_nonneg_im
- \+ *lemma* inner_product_space.of_core.inner_self_re_to_K
- \+ *lemma* inner_product_space.of_core.inner_smul_left
- \+ *lemma* inner_product_space.of_core.inner_smul_right
- \+ *lemma* inner_product_space.of_core.inner_sub_left
- \+ *lemma* inner_product_space.of_core.inner_sub_right
- \+ *lemma* inner_product_space.of_core.inner_sub_sub_self
- \+ *lemma* inner_product_space.of_core.inner_zero_left
- \+ *lemma* inner_product_space.of_core.inner_zero_right
- \+ *lemma* inner_product_space.of_core.norm_eq_sqrt_inner
- \+ *def* inner_product_space.of_core.norm_sq
- \+ *lemma* inner_product_space.of_core.sqrt_norm_sq_eq_norm
- \+ *def* inner_product_space.of_core.to_has_inner
- \+ *def* inner_product_space.of_core.to_has_norm
- \+ *def* inner_product_space.of_core.to_normed_group
- \+ *def* inner_product_space.of_core.to_normed_space
- \+ *def* inner_product_space.of_core
- \+ *lemma* inner_re_symm
- \+ *lemma* inner_re_zero_left
- \+ *lemma* inner_re_zero_right
- \+ *lemma* inner_self_abs_to_K
- \+ *lemma* inner_self_conj
- \+ *lemma* inner_self_eq_norm_square
- \+ *lemma* inner_self_eq_zero
- \+ *lemma* inner_self_im_zero
- \+ *lemma* inner_self_nonneg
- \+ *lemma* inner_self_nonneg_im
- \+ *lemma* inner_self_nonpos
- \+ *lemma* inner_self_re_abs
- \+ *lemma* inner_self_re_to_K
- \+ *lemma* inner_smul_left
- \+ *lemma* inner_smul_right
- \+ *lemma* inner_sub_left
- \+ *lemma* inner_sub_right
- \+ *lemma* inner_sub_sub_self
- \+ *lemma* inner_sum
- \+ *lemma* inner_sum_smul_sum_smul_of_sum_eq_zero
- \+ *lemma* inner_zero_left
- \+ *lemma* inner_zero_right
- \+ *lemma* linear_independent_of_ne_zero_of_inner_eq_zero
- \+ *lemma* norm_add_mul_self
- \+ *lemma* norm_add_mul_self_real
- \+ *lemma* norm_add_pow_two
- \+ *lemma* norm_add_pow_two_real
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square_real
- \+ *theorem* norm_eq_infi_iff_inner_eq_zero
- \+ *theorem* norm_eq_infi_iff_real_inner_eq_zero
- \+ *theorem* norm_eq_infi_iff_real_inner_le_zero
- \+ *lemma* norm_eq_sqrt_inner
- \+ *lemma* norm_eq_sqrt_real_inner
- \+ *lemma* norm_sub_mul_self
- \+ *lemma* norm_sub_mul_self_real
- \+ *lemma* norm_sub_pow_two
- \+ *lemma* norm_sub_pow_two_real
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square_real
- \+ *def* orthogonal_projection
- \+ *lemma* orthogonal_projection_def
- \+ *def* orthogonal_projection_fn
- \+ *lemma* orthogonal_projection_fn_eq
- \+ *lemma* orthogonal_projection_fn_inner_eq_zero
- \+ *lemma* orthogonal_projection_fn_mem
- \+ *lemma* orthogonal_projection_inner_eq_zero
- \+ *lemma* orthogonal_projection_mem
- \+ *def* orthogonal_projection_of_complete
- \+ *lemma* parallelogram_law
- \+ *lemma* parallelogram_law_with_norm
- \+ *lemma* parallelogram_law_with_norm_real
- \+ *lemma* real_inner_add_add_self
- \+ *lemma* real_inner_add_sub_eq_zero_iff
- \+ *lemma* real_inner_comm
- \+ *lemma* real_inner_div_norm_mul_norm_eq_neg_one_iff
- \+ *lemma* real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
- \+ *lemma* real_inner_div_norm_mul_norm_eq_one_iff
- \+ *lemma* real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
- \+ *lemma* real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
- \+ *lemma* real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
- \+ *lemma* real_inner_eq_re_inner
- \+ *lemma* real_inner_mul_inner_self_le
- \+ *lemma* real_inner_self_abs
- \+ *lemma* real_inner_self_eq_norm_square
- \+ *lemma* real_inner_self_nonneg
- \+ *lemma* real_inner_self_nonpos
- \+ *lemma* real_inner_smul_left
- \+ *lemma* real_inner_smul_right
- \+ *lemma* real_inner_smul_self_left
- \+ *lemma* real_inner_smul_self_right
- \+ *lemma* real_inner_sub_sub_self
- \+ *def* sesq_form_of_inner
- \+ *lemma* submodule.Inf_orthogonal
- \+ *lemma* submodule.findim_add_inf_findim_orthogonal
- \+ *lemma* submodule.inf_orthogonal
- \+ *lemma* submodule.infi_orthogonal
- \+ *lemma* submodule.inner_left_of_mem_orthogonal
- \+ *lemma* submodule.inner_right_of_mem_orthogonal
- \+ *lemma* submodule.is_compl_orthogonal_of_is_complete_real
- \+ *lemma* submodule.le_orthogonal_orthogonal
- \+ *lemma* submodule.mem_orthogonal'
- \+ *lemma* submodule.mem_orthogonal
- \+ *def* submodule.orthogonal
- \+ *lemma* submodule.orthogonal_disjoint
- \+ *lemma* submodule.orthogonal_gc
- \+ *lemma* submodule.orthogonal_le
- \+ *lemma* submodule.sup_orthogonal_inf_of_is_complete
- \+ *lemma* submodule.sup_orthogonal_of_is_complete
- \+ *lemma* sum_inner

Deleted src/analysis/normed_space/real_inner_product.lean
- \- *lemma* abs_inner_div_norm_mul_norm_eq_one_iff
- \- *lemma* abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
- \- *lemma* abs_inner_div_norm_mul_norm_le_one
- \- *lemma* abs_inner_le_norm
- \- *def* bilin_form_of_inner
- \- *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \- *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \- *def* euclidean_space
- \- *theorem* exists_norm_eq_infi_of_complete_convex
- \- *theorem* exists_norm_eq_infi_of_complete_subspace
- \- *lemma* findim_euclidean_space
- \- *lemma* findim_euclidean_space_fin
- \- *lemma* inner_add_add_self
- \- *lemma* inner_add_left
- \- *lemma* inner_add_right
- \- *lemma* inner_add_sub_eq_zero_iff
- \- *lemma* inner_comm
- \- *lemma* inner_div_norm_mul_norm_eq_neg_one_iff
- \- *lemma* inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
- \- *lemma* inner_div_norm_mul_norm_eq_one_iff
- \- *lemma* inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
- \- *lemma* inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
- \- *lemma* inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
- \- *lemma* inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
- \- *lemma* inner_mul_inner_self_le
- \- *lemma* inner_neg_left
- \- *lemma* inner_neg_neg
- \- *lemma* inner_neg_right
- \- *structure* inner_product_space.core
- \- *lemma* inner_product_space.of_core.abs_inner_le_norm
- \- *lemma* inner_product_space.of_core.inner_add_add_self
- \- *lemma* inner_product_space.of_core.inner_add_left
- \- *lemma* inner_product_space.of_core.inner_add_right
- \- *lemma* inner_product_space.of_core.inner_comm
- \- *lemma* inner_product_space.of_core.inner_mul_inner_self_le
- \- *lemma* inner_product_space.of_core.inner_self_eq_norm_square
- \- *lemma* inner_product_space.of_core.inner_smul_left
- \- *lemma* inner_product_space.of_core.inner_smul_right
- \- *lemma* inner_product_space.of_core.norm_eq_sqrt_inner
- \- *def* inner_product_space.of_core.to_has_inner
- \- *def* inner_product_space.of_core.to_has_norm
- \- *def* inner_product_space.of_core.to_normed_group
- \- *def* inner_product_space.of_core.to_normed_space
- \- *def* inner_product_space.of_core
- \- *lemma* inner_self_eq_norm_square
- \- *lemma* inner_self_eq_zero
- \- *lemma* inner_self_nonneg
- \- *lemma* inner_self_nonpos
- \- *lemma* inner_smul_left
- \- *lemma* inner_smul_right
- \- *lemma* inner_smul_self_left
- \- *lemma* inner_smul_self_right
- \- *lemma* inner_sub_left
- \- *lemma* inner_sub_right
- \- *lemma* inner_sub_sub_self
- \- *lemma* inner_sum
- \- *lemma* inner_sum_smul_sum_smul_of_sum_eq_zero
- \- *lemma* inner_zero_left
- \- *lemma* inner_zero_right
- \- *lemma* linear_independent_of_ne_zero_of_inner_eq_zero
- \- *lemma* norm_add_mul_self
- \- *lemma* norm_add_pow_two
- \- *lemma* norm_add_square_eq_norm_square_add_norm_square
- \- *lemma* norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero
- \- *theorem* norm_eq_infi_iff_inner_eq_zero
- \- *theorem* norm_eq_infi_iff_inner_le_zero
- \- *lemma* norm_sub_mul_self
- \- *lemma* norm_sub_pow_two
- \- *lemma* norm_sub_square_eq_norm_square_add_norm_square
- \- *lemma* norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero
- \- *def* orthogonal_projection
- \- *lemma* orthogonal_projection_def
- \- *def* orthogonal_projection_fn
- \- *lemma* orthogonal_projection_fn_eq
- \- *lemma* orthogonal_projection_fn_inner_eq_zero
- \- *lemma* orthogonal_projection_fn_mem
- \- *lemma* orthogonal_projection_inner_eq_zero
- \- *lemma* orthogonal_projection_mem
- \- *def* orthogonal_projection_of_complete
- \- *lemma* parallelogram_law
- \- *lemma* parallelogram_law_with_norm
- \- *lemma* submodule.Inf_orthogonal
- \- *lemma* submodule.findim_add_inf_findim_orthogonal
- \- *lemma* submodule.inf_orthogonal
- \- *lemma* submodule.infi_orthogonal
- \- *lemma* submodule.inner_left_of_mem_orthogonal
- \- *lemma* submodule.inner_right_of_mem_orthogonal
- \- *lemma* submodule.is_compl_orthogonal_of_is_complete
- \- *lemma* submodule.le_orthogonal_orthogonal
- \- *lemma* submodule.mem_orthogonal'
- \- *lemma* submodule.mem_orthogonal
- \- *def* submodule.orthogonal
- \- *lemma* submodule.orthogonal_disjoint
- \- *lemma* submodule.orthogonal_gc
- \- *lemma* submodule.orthogonal_le
- \- *lemma* submodule.sup_orthogonal_inf_of_is_complete
- \- *lemma* submodule.sup_orthogonal_of_is_complete
- \- *lemma* sum_inner

Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.I_im'
- \+ *lemma* is_R_or_C.abs_sqr_re_add_conj'
- \+ *lemma* is_R_or_C.abs_sqr_re_add_conj
- \+ *lemma* is_R_or_C.conj_div
- \+ *lemma* is_R_or_C.conj_inv
- \+ *lemma* is_R_or_C.conj_mul_eq_norm_sq_left
- \+ *def* is_R_or_C.conj_to_ring_equiv
- \+ *lemma* is_R_or_C.div_re_of_real
- \+/\- *lemma* is_R_or_C.inv_def
- \+ *lemma* is_R_or_C.norm_conj
- \+/\- *lemma* is_R_or_C.of_real_add
- \+/\- *lemma* is_R_or_C.of_real_mul
- \+ *lemma* is_R_or_C.of_real_mul_re
- \+/\- *lemma* is_R_or_C.of_real_neg
- \+ *lemma* is_R_or_C.re_eq_abs_of_mul_conj
- \+ *lemma* is_R_or_C.sqrt_norm_sq_eq_norm
- \+ *lemma* is_R_or_C.zero_re'
- \+/\- *lemma* is_R_or_C.zero_re

Modified src/geometry/euclidean/basic.lean
- \+/\- *lemma* inner_product_geometry.inner_eq_zero_iff_angle_eq_pi_div_two

Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/euclidean/monge_point.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/geometry/manifold/instances/real.lean
- \+/\- *def* euclidean_quadrant

Modified src/linear_algebra/sesquilinear_form.lean
- \+ *lemma* sesq_form.is_add_monoid_hom_left
- \+ *lemma* sesq_form.is_add_monoid_hom_right
- \+ *lemma* sesq_form.map_sum_left
- \+ *lemma* sesq_form.map_sum_right

Modified src/ring_theory/algebra.lean
- \- *def* subspace.restrict_scalars



## [2020-10-01 02:57:05](https://github.com/leanprover-community/mathlib/commit/1b97326)
feat(data/fintype): pigeonhole principles ([#4096](https://github.com/leanprover-community/mathlib/pull/4096))
Add pigeonhole principles for finitely and infinitely many pigeons in finitely many holes. There are also strong versions of these, which say that there is a hole containing at least as many pigeons as the average number of pigeons per hole. Fixes [#2272](https://github.com/leanprover-community/mathlib/pull/2272).
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *theorem* finset.card_eq_sum_card_fiberwise
- \+ *lemma* finset.prod_fiberwise_of_maps_to

Modified src/algebra/big_operators/order.lean
- \+ *theorem* finset.card_le_mul_card_image_of_maps_to
- \+ *theorem* finset.exists_lt_of_sum_lt
- \+ *lemma* finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg
- \+ *lemma* finset.sum_le_sum_fiberwise_of_sum_fiber_nonpos

Modified src/algebra/ordered_group.lean


Added src/combinatorics/pigeonhole.lean
- \+ *lemma* finset.exists_card_fiber_le_of_card_le_mul
- \+ *lemma* finset.exists_card_fiber_lt_of_card_lt_mul
- \+ *lemma* finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
- \+ *lemma* finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
- \+ *lemma* finset.exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum
- \+ *lemma* finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
- \+ *lemma* finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum
- \+ *lemma* finset.exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum
- \+ *lemma* finset.exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul
- \+ *lemma* finset.exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
- \+ *lemma* finset.exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul
- \+ *lemma* finset.exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
- \+ *lemma* fintype.exists_card_fiber_le_of_card_le_mul
- \+ *lemma* fintype.exists_card_fiber_lt_of_card_lt_mul
- \+ *lemma* fintype.exists_le_card_fiber_of_mul_le_card
- \+ *lemma* fintype.exists_le_sum_fiber_of_nsmul_le_sum
- \+ *lemma* fintype.exists_lt_card_fiber_of_mul_lt_card
- \+ *lemma* fintype.exists_lt_sum_fiber_of_nsmul_lt_sum
- \+ *lemma* fintype.exists_sum_fiber_le_of_sum_le_nsmul
- \+ *lemma* fintype.exists_sum_fiber_lt_of_sum_lt_nsmul

Modified src/data/finset/basic.lean
- \+ *lemma* finset.bind_filter_eq_of_maps_to
- \+ *lemma* finset.exists_ne_map_eq_of_card_lt_of_maps_to
- \+ *lemma* finset.fiber_card_ne_zero_iff_mem_image
- \+ *lemma* finset.fiber_nonempty_iff_mem_image
- \+ *lemma* finset.filter_mem_image_eq_image

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_nonempty
- \+ *lemma* fintype.exists_infinite_fiber
- \+ *lemma* fintype.exists_ne_map_eq_of_card_lt
- \+ *lemma* fintype.exists_ne_map_eq_of_infinite

Modified src/data/fintype/card.lean




## [2020-10-01 01:07:36](https://github.com/leanprover-community/mathlib/commit/af99416)
chore(scripts): update nolints.txt ([#4341](https://github.com/leanprover-community/mathlib/pull/4341))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


