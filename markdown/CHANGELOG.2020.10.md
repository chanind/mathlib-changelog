## [2020-10-31 22:44:12](https://github.com/leanprover-community/mathlib/commit/6f7c539)
docs(order/complete_lattice): make two docstrings more detailed ([#4859](https://github.com/leanprover-community/mathlib/pull/4859))
Following [discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Constructing.20a.20complete.20lattice), clarify information about how to construct a complete lattice while preserving good definitional equalities.
#### Estimated changes
modified src/order/complete_lattice.lean



## [2020-10-31 20:22:31](https://github.com/leanprover-community/mathlib/commit/51cbb83)
refactor(tactic/norm_num): move norm_num extensions ([#4822](https://github.com/leanprover-community/mathlib/pull/4822))
[#4820](https://github.com/leanprover-community/mathlib/pull/4820) adds the long awaited ability for `norm_num` to be extended in other files. There are two norm_num extensions currently in mathlib: `norm_digits`, which was previously exposed as a standalone tactic, and `eval_prime`, which was a part of `norm_num` and so caused `tactic.norm_num` to depend on `data.nat.prime`. This PR turns both of these into norm_num extensions, and changes the dependencies so that `data.nat.prime` can import `norm_num` rather than the other way around (which required splitting `pnat` primality and gcd facts to their own file).
#### Estimated changes
modified archive/imo/imo1959_q1.lean

modified archive/imo/imo1960_q1.lean

modified archive/imo/imo1969_q1.lean

modified archive/imo/imo1988_q6.lean

modified src/data/nat/digits.lean

modified src/data/nat/prime.lean
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

modified src/number_theory/divisors.lean

modified src/tactic/norm_num.lean
- \- *lemma* not_prime_helper
- \- *lemma* is_prime_helper
- \- *lemma* min_fac_bit0
- \- *lemma* min_fac_ne_bit0
- \- *lemma* min_fac_helper_0
- \- *lemma* min_fac_helper_1
- \- *lemma* min_fac_helper_2
- \- *lemma* min_fac_helper_3
- \- *lemma* min_fac_helper_4
- \- *lemma* min_fac_helper_5
- \- *theorem* min_fac_helper.n_pos
- \- *def* min_fac_helper

modified test/linarith.lean

modified test/norm_digits.lean

modified test/norm_num.lean

modified test/omega.lean



## [2020-10-31 17:41:26](https://github.com/leanprover-community/mathlib/commit/be161d1)
feat(category_theory/sites): functor inclusion constructions ([#4845](https://github.com/leanprover-community/mathlib/pull/4845))
#### Estimated changes
modified src/category_theory/sites/sieves.lean
- \+ *lemma* sieve_of_subfunctor_apply
- \+ *lemma* sieve_of_subfunctor_functor_inclusion
- \+ *def* sieve_of_subfunctor



## [2020-10-31 17:41:24](https://github.com/leanprover-community/mathlib/commit/d91c878)
chore(group_theory/group_action): introduce `smul_comm_class` ([#4770](https://github.com/leanprover-community/mathlib/pull/4770))
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+/\- *lemma* smul_algebra_smul_comm
- \+/\- *lemma* smul_algebra_smul_comm
- \- *lemma* map_smul_eq_smul_map
- \- *lemma* algebra_module.smul_apply
- \- *lemma* smul_apply'
- \- *def* restrict_scalars

modified src/algebra/module/linear_map.lean
- \+ *lemma* map_smul_of_tower
- \+ *def* restrict_scalars

modified src/analysis/convex/basic.lean

modified src/data/complex/module.lean

modified src/group_theory/group_action.lean
- \+ *lemma* smul_comm_class.symm
- \+/\- *lemma* smul_assoc
- \+ *lemma* smul_one_smul
- \- *lemma* smul_comm
- \+/\- *lemma* smul_assoc
- \- *theorem* mul_smul

modified src/linear_algebra/basic.lean
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_apply
- \+/\- *theorem* smul_comp
- \+/\- *theorem* comp_smul
- \+/\- *theorem* smul_comp
- \+/\- *theorem* comp_smul
- \+ *def* applyₗ'

modified src/linear_algebra/matrix.lean

modified src/representation_theory/maschke.lean

modified src/ring_theory/derivation.lean

modified src/topology/algebra/module.lean



## [2020-10-31 15:07:49](https://github.com/leanprover-community/mathlib/commit/9a03bdf)
chore(algebra/ordered_group): use implicit args, add `add_eq_coe` ([#4853](https://github.com/leanprover-community/mathlib/pull/4853))
* Use implicit arguments in various `iff` lemmas about `with_top`.
* Add `add_eq_coe`.
* Rewrite `with_top.ordered_add_comm_monoid` moving `begin .. end` blocks inside the structure.
This way we don't depend on the fact that `refine` doesn't introduce any `id`s and it's easier to see right away which block proves which statement.
#### Estimated changes
modified src/algebra/ordered_group.lean
- \+/\- *lemma* add_top
- \+/\- *lemma* top_add
- \+/\- *lemma* add_eq_top
- \+/\- *lemma* add_lt_top
- \+ *lemma* add_eq_coe
- \+/\- *lemma* add_top
- \+/\- *lemma* top_add
- \+/\- *lemma* add_eq_top
- \+/\- *lemma* add_lt_top

modified src/data/real/ennreal.lean
- \+/\- *lemma* add_eq_top
- \+/\- *lemma* add_lt_top
- \+/\- *lemma* le_coe_iff
- \+/\- *lemma* coe_le_iff
- \+/\- *lemma* lt_iff_exists_coe
- \+ *lemma* coe_finset_sup
- \+/\- *lemma* add_eq_top
- \+/\- *lemma* add_lt_top
- \+/\- *lemma* le_coe_iff
- \+/\- *lemma* coe_le_iff
- \+/\- *lemma* lt_iff_exists_coe

modified src/order/bounded_lattice.lean
- \+/\- *theorem* le_coe_iff
- \+/\- *theorem* coe_le_iff
- \+/\- *theorem* lt_iff_exists_coe
- \+ *theorem* coe_lt_iff
- \+/\- *theorem* le_coe_iff
- \+/\- *theorem* coe_le_iff
- \+/\- *theorem* lt_iff_exists_coe

modified src/order/conditionally_complete_lattice.lean

modified src/topology/metric_space/basic.lean



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
modified src/order/filter/bases.lean
- \+ *lemma* has_basis.inf_basis_ne_bot_iff
- \+ *lemma* has_basis.inf_ne_bot_iff
- \+ *lemma* has_basis.inf_principal_ne_bot_iff
- \+ *lemma* inf_ne_bot_iff
- \+ *lemma* inf_principal_ne_bot_iff
- \+ *lemma* inf_eq_bot_iff
- \+ *lemma* mem_iff_inf_principal_compl
- \+ *lemma* mem_iff_disjoint_principal_compl
- \+ *lemma* le_iff_forall_disjoint_principal_compl
- \+ *lemma* le_iff_forall_inf_principal_compl
- \+ *lemma* inf_ne_bot_iff_frequently_left
- \+ *lemma* inf_ne_bot_iff_frequently_right

modified src/order/filter/basic.lean
- \- *lemma* inf_ne_bot_iff
- \- *lemma* inf_principal_ne_bot_iff
- \- *lemma* inf_eq_bot_iff
- \- *lemma* mem_iff_inf_principal_compl
- \- *lemma* le_iff_forall_inf_principal_compl
- \- *lemma* inf_ne_bot_iff_frequently_left
- \- *lemma* inf_ne_bot_iff_frequently_right

modified src/topology/algebra/ordered.lean

modified src/topology/basic.lean

modified src/topology/uniform_space/separation.lean



## [2020-10-31 08:44:02](https://github.com/leanprover-community/mathlib/commit/f9c8abe)
chore(data/finset/basic): a few lemmas about `finset.piecewise` ([#4852](https://github.com/leanprover-community/mathlib/pull/4852))
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* piecewise_congr
- \+ *lemma* piecewise_cases
- \+ *lemma* piecewise_mem_set_pi
- \+ *lemma* piecewise_singleton
- \+ *lemma* update_piecewise
- \+ *lemma* update_piecewise_of_mem
- \+ *lemma* update_piecewise_of_not_mem
- \+ *lemma* piecewise_le_of_le_of_le
- \+ *lemma* le_piecewise_of_le_of_le

modified src/data/set/function.lean
- \+ *lemma* piecewise_mem_pi



## [2020-10-31 08:44:00](https://github.com/leanprover-community/mathlib/commit/7756265)
chore(linear_algebra/affine_space/ordered): compare endpoints to midpoint ([#4851](https://github.com/leanprover-community/mathlib/pull/4851))
#### Estimated changes
modified src/linear_algebra/affine_space/ordered.lean
- \+ *lemma* left_le_midpoint
- \+ *lemma* midpoint_le_left
- \+ *lemma* midpoint_le_right
- \+ *lemma* right_le_midpoint



## [2020-10-31 08:43:59](https://github.com/leanprover-community/mathlib/commit/1f61621)
feat(linear_algebra/affine_space/affine_map): add `affine_map.proj` ([#4850](https://github.com/leanprover-community/mathlib/pull/4850))
#### Estimated changes
modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* proj_apply
- \+ *lemma* proj_linear
- \+ *lemma* pi_line_map_apply
- \+ *def* proj

modified src/linear_algebra/affine_space/midpoint.lean
- \+ *lemma* pi_midpoint_apply



## [2020-10-31 08:43:57](https://github.com/leanprover-community/mathlib/commit/6a44930)
refactor(data/pnat): move data.pnat.prime ([#4839](https://github.com/leanprover-community/mathlib/pull/4839))
Remove the dependency `data.pnat.basic -> data.nat.prime`. Needed for [#4822](https://github.com/leanprover-community/mathlib/pull/4822).
#### Estimated changes
modified src/data/pnat/basic.lean
- \- *lemma* eq_one_of_lt_two
- \- *lemma* prime.one_lt
- \- *lemma* prime_two
- \- *lemma* dvd_prime
- \- *lemma* prime.ne_one
- \- *lemma* not_prime_one
- \- *lemma* prime.not_dvd_one
- \- *lemma* exists_prime_and_dvd
- \- *lemma* coprime_coe
- \- *lemma* coprime.mul
- \- *lemma* coprime.mul_right
- \- *lemma* gcd_comm
- \- *lemma* gcd_eq_left_iff_dvd
- \- *lemma* gcd_eq_right_iff_dvd
- \- *lemma* coprime.gcd_mul_left_cancel
- \- *lemma* coprime.gcd_mul_right_cancel
- \- *lemma* coprime.gcd_mul_left_cancel_right
- \- *lemma* coprime.gcd_mul_right_cancel_right
- \- *lemma* one_gcd
- \- *lemma* gcd_one
- \- *lemma* coprime.symm
- \- *lemma* one_coprime
- \- *lemma* coprime_one
- \- *lemma* coprime.coprime_dvd_left
- \- *lemma* coprime.factor_eq_gcd_left
- \- *lemma* coprime.factor_eq_gcd_right
- \- *lemma* coprime.factor_eq_gcd_left_right
- \- *lemma* coprime.factor_eq_gcd_right_right
- \- *lemma* coprime.gcd_mul
- \- *lemma* gcd_eq_left
- \- *lemma* coprime.pow
- \- *theorem* coe_pnat_nat
- \- *theorem* coe_pnat_inj
- \- *theorem* gcd_coe
- \- *theorem* lcm_coe
- \- *theorem* gcd_dvd_left
- \- *theorem* gcd_dvd_right
- \- *theorem* dvd_gcd
- \- *theorem* dvd_lcm_left
- \- *theorem* dvd_lcm_right
- \- *theorem* lcm_dvd
- \- *theorem* gcd_mul_lcm
- \- *def* gcd
- \- *def* lcm
- \- *def* prime
- \- *def* coprime

modified src/data/pnat/factors.lean

created src/data/pnat/prime.lean
- \+ *lemma* eq_one_of_lt_two
- \+ *lemma* prime.one_lt
- \+ *lemma* prime_two
- \+ *lemma* dvd_prime
- \+ *lemma* prime.ne_one
- \+ *lemma* not_prime_one
- \+ *lemma* prime.not_dvd_one
- \+ *lemma* exists_prime_and_dvd
- \+ *lemma* coprime_coe
- \+ *lemma* coprime.mul
- \+ *lemma* coprime.mul_right
- \+ *lemma* gcd_comm
- \+ *lemma* gcd_eq_left_iff_dvd
- \+ *lemma* gcd_eq_right_iff_dvd
- \+ *lemma* coprime.gcd_mul_left_cancel
- \+ *lemma* coprime.gcd_mul_right_cancel
- \+ *lemma* coprime.gcd_mul_left_cancel_right
- \+ *lemma* coprime.gcd_mul_right_cancel_right
- \+ *lemma* one_gcd
- \+ *lemma* gcd_one
- \+ *lemma* coprime.symm
- \+ *lemma* one_coprime
- \+ *lemma* coprime_one
- \+ *lemma* coprime.coprime_dvd_left
- \+ *lemma* coprime.factor_eq_gcd_left
- \+ *lemma* coprime.factor_eq_gcd_right
- \+ *lemma* coprime.factor_eq_gcd_left_right
- \+ *lemma* coprime.factor_eq_gcd_right_right
- \+ *lemma* coprime.gcd_mul
- \+ *lemma* gcd_eq_left
- \+ *lemma* coprime.pow
- \+ *theorem* coe_pnat_nat
- \+ *theorem* coe_pnat_inj
- \+ *theorem* gcd_coe
- \+ *theorem* lcm_coe
- \+ *theorem* gcd_dvd_left
- \+ *theorem* gcd_dvd_right
- \+ *theorem* dvd_gcd
- \+ *theorem* dvd_lcm_left
- \+ *theorem* dvd_lcm_right
- \+ *theorem* lcm_dvd
- \+ *theorem* gcd_mul_lcm
- \+ *def* gcd
- \+ *def* lcm
- \+ *def* prime
- \+ *def* coprime

modified src/data/pnat/xgcd.lean

modified src/data/rat/basic.lean

modified src/tactic/norm_num.lean



## [2020-10-31 08:43:55](https://github.com/leanprover-community/mathlib/commit/3b2c97f)
feat(data/dfinsupp): Port `finsupp.lsum` and lemmas about `lift_add_hom` ([#4833](https://github.com/leanprover-community/mathlib/pull/4833))
This then removes the proofs of any `direct_sum` lemmas which become equivalent to the `lift_add_hom` lemmas
#### Estimated changes
modified src/algebra/direct_sum.lean

modified src/data/dfinsupp.lean
- \+ *lemma* lhom_ext
- \+ *lemma* lhom_ext'
- \+ *lemma* sum_add_hom_comp_single
- \+ *lemma* lift_add_hom_single_add_hom
- \+ *lemma* lift_add_hom_apply_single
- \+ *lemma* lift_add_hom_comp_single
- \+ *lemma* comp_lift_add_hom
- \+ *def* lsum

modified src/linear_algebra/direct_sum_module.lean



## [2020-10-31 08:43:53](https://github.com/leanprover-community/mathlib/commit/17697a6)
feat(data/dfinsupp): Add dfinsupp.single_eq_single_iff, and subtype.heq_iff_coe_eq ([#4810](https://github.com/leanprover-community/mathlib/pull/4810))
This ought to make working with dfinsupps over subtypes easier
#### Estimated changes
modified src/data/dfinsupp.lean
- \+ *lemma* single_eq_single_iff

modified src/data/subtype.lean
- \+ *lemma* heq_iff_coe_eq



## [2020-10-31 06:18:28](https://github.com/leanprover-community/mathlib/commit/67c2b5a)
feat(analysis/normed_space/add_torsor): distance to midpoint ([#4849](https://github.com/leanprover-community/mathlib/pull/4849))
#### Estimated changes
modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* dist_vadd_left
- \+ *lemma* dist_vadd_right
- \+ *lemma* dist_center_homothety
- \+ *lemma* dist_homothety_center
- \+ *lemma* dist_homothety_self
- \+ *lemma* dist_self_homothety
- \+ *lemma* dist_left_midpoint
- \+ *lemma* dist_midpoint_left
- \+ *lemma* dist_midpoint_right
- \+ *lemma* dist_right_midpoint



## [2020-10-31 06:18:25](https://github.com/leanprover-community/mathlib/commit/1521da6)
feat(order/conditionally_complete_lattice): nested intervals lemma ([#4848](https://github.com/leanprover-community/mathlib/pull/4848))
* Add a few versions of the nested intervals lemma.
* Add `pi`-instance for `conditionally_complete_lattice`.
#### Estimated changes
modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* csupr_mem_Inter_Icc_of_mono_incr_of_mono_decr
- \+ *lemma* csupr_mem_Inter_Icc_of_mono_decr_Icc
- \+ *lemma* csupr_mem_Inter_Icc_of_mono_decr_Icc_nat

modified src/order/lattice.lean
- \+ *theorem* forall_le_of_monotone_of_mono_decr



## [2020-10-31 06:18:24](https://github.com/leanprover-community/mathlib/commit/f5fd218)
feat(algebra/module/ordered): add pi instance ([#4847](https://github.com/leanprover-community/mathlib/pull/4847))
#### Estimated changes
modified src/algebra/module/ordered.lean



## [2020-10-31 06:18:21](https://github.com/leanprover-community/mathlib/commit/6fc3517)
feat(category_theory/sites): generate lemmas ([#4840](https://github.com/leanprover-community/mathlib/pull/4840))
A couple of simple lemmas about the sieve generated by certain presieves.
#### Estimated changes
modified src/category_theory/sites/pretopology.lean

modified src/category_theory/sites/sieves.lean
- \+ *lemma* le_generate
- \+/\- *lemma* id_mem_iff_eq_top
- \+ *lemma* generate_of_contains_split_epi
- \+ *lemma* generate_of_singleton_split_epi
- \+ *lemma* generate_top
- \+/\- *lemma* id_mem_iff_eq_top



## [2020-10-31 06:18:19](https://github.com/leanprover-community/mathlib/commit/517f0b5)
feat(ring_theory/polynomial/basic): prerequisites for galois_definition ([#4829](https://github.com/leanprover-community/mathlib/pull/4829))
#### Estimated changes
modified src/data/polynomial/degree/basic.lean
- \+ *lemma* as_sum_range'

modified src/ring_theory/polynomial/basic.lean
- \+ *def* degree_lt_equiv



## [2020-10-31 06:18:16](https://github.com/leanprover-community/mathlib/commit/0f39d7a)
feat(data/prod): comp_map ([#4826](https://github.com/leanprover-community/mathlib/pull/4826))
#### Estimated changes
modified src/data/prod.lean
- \+ *lemma* map_comp_map
- \+ *lemma* map_map



## [2020-10-31 04:53:40](https://github.com/leanprover-community/mathlib/commit/2283cf0)
chore(order/filter/bases): golf a proof ([#4834](https://github.com/leanprover-community/mathlib/pull/4834))
* rename `filter.has_basis.forall_nonempty_iff_ne_bot` to
  `filter.has_basis.ne_bot_iff`, swap LHS with RHS;
* add `filter.has_basis.eq_bot_iff`;
* golf the proof of `filter.has_basis.ne_bot` using `filter.has_basis.forall_iff`.
#### Estimated changes
modified src/order/filter/at_top_bot.lean

modified src/order/filter/bases.lean
- \+/\- *lemma* has_basis.exists_iff
- \+/\- *lemma* has_basis.forall_iff
- \+ *lemma* has_basis.ne_bot_iff
- \+ *lemma* has_basis.eq_bot_iff
- \- *lemma* has_basis.forall_nonempty_iff_ne_bot
- \+/\- *lemma* has_basis.exists_iff
- \+/\- *lemma* has_basis.forall_iff



## [2020-10-31 02:07:09](https://github.com/leanprover-community/mathlib/commit/94fa905)
feat(analysis/calculus/times_cont_diff): differentiability of field inverse ([#4795](https://github.com/leanprover-community/mathlib/pull/4795))
#### Estimated changes
modified src/algebra/field.lean
- \+ *lemma* inverse_eq_has_inv

modified src/analysis/calculus/times_cont_diff.lean
- \+/\- *lemma* times_cont_diff_within_at.continuous_within_at
- \+ *lemma* times_cont_diff_within_at.mono_of_mem
- \+/\- *lemma* times_cont_diff_within_at.mono
- \+ *lemma* times_cont_diff_within_at.congr_nhds
- \+ *lemma* times_cont_diff_within_at_congr_nhds
- \+ *lemma* times_cont_diff_at.congr_of_eventually_eq
- \+ *lemma* times_cont_diff_within_at_id
- \+ *lemma* times_cont_diff_at_id
- \+ *lemma* times_cont_diff_on_id
- \+ *lemma* times_cont_diff_at.comp_times_cont_diff_within_at
- \+/\- *lemma* times_cont_diff_at.comp
- \+ *lemma* times_cont_diff.pow
- \+ *lemma* times_cont_diff_at_inv
- \+ *lemma* times_cont_diff_within_at.inv
- \+ *lemma* times_cont_diff_at.inv
- \+ *lemma* times_cont_diff_within_at.div
- \+ *lemma* times_cont_diff_at.div
- \+ *lemma* times_cont_diff.div
- \- *lemma* times_cont_diff_within_at.continuous_within_at'
- \+/\- *lemma* times_cont_diff_within_at.continuous_within_at
- \+/\- *lemma* times_cont_diff_within_at.mono
- \+/\- *lemma* times_cont_diff_at.comp

modified src/geometry/manifold/times_cont_mdiff.lean

modified src/topology/algebra/module.lean
- \+ *lemma* one_def

modified src/topology/continuous_on.lean
- \+/\- *lemma* mem_nhds_within_insert
- \+ *lemma* insert_mem_nhds_within_insert
- \+ *lemma* continuous_within_at.mono_of_mem
- \+ *lemma* continuous_within_at_union
- \+/\- *lemma* continuous_within_at_singleton
- \+ *lemma* continuous_within_at_insert_self
- \+/\- *lemma* mem_nhds_within_insert
- \+/\- *lemma* continuous_within_at_singleton
- \+ *theorem* nhds_within_singleton
- \+ *theorem* nhds_within_insert



## [2020-10-31 00:58:01](https://github.com/leanprover-community/mathlib/commit/d5650a7)
chore(scripts): update nolints.txt ([#4844](https://github.com/leanprover-community/mathlib/pull/4844))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt

modified scripts/nolints.txt



## [2020-10-30 18:58:08](https://github.com/leanprover-community/mathlib/commit/cc7f06b)
feat(data/polynomial/lifts): polynomials that lift ([#4796](https://github.com/leanprover-community/mathlib/pull/4796))
Given semirings `R` and `S` with a morphism `f : R →+* S`, a polynomial with coefficients in `S` lifts if there exist `q : polynomial R` such that `map f p = q`. I proved some basic results about polynomials that lifts, for example concerning the sum etc.
Almost all the proof are trivial (and essentially identical), fell free to comment just the first ones, I will do the changes in all the relevant lemmas.
The proofs of `lifts_iff_lifts_deg` (a polynomial that lifts can be lifted to a polynomial of the same degree) and of `lifts_iff_lifts_deg_monic` (the same for monic polynomials) are quite painful, but this are the shortest proofs I found... I think that at least these two results deserve to be in mathlib (I'm using them to prove that the cyclotomic polynomial lift to `\Z`).
#### Estimated changes
created src/data/polynomial/lifts.lean
- \+ *lemma* mem_lifts
- \+ *lemma* lifts_iff_set_range
- \+ *lemma* lifts_iff_coeff_lifts
- \+ *lemma* C_mem_lifts
- \+ *lemma* C'_mem_lifts
- \+ *lemma* X_mem_lifts
- \+ *lemma* X_pow_mem_lifts
- \+ *lemma* base_mul_mem_lifts
- \+ *lemma* monomial_mem_lifts
- \+ *lemma* erase_mem_lifts
- \+ *lemma* monomial_mem_lifts_and_degree_eq
- \+ *lemma* mem_lifts_and_degree_eq
- \+ *lemma* lifts_and_degree_eq_and_monic
- \+ *lemma* lifts_iff_lifts_ring
- \+ *lemma* map_alg_eq_map
- \+ *lemma* mem_lifts_iff_mem_alg
- \+ *lemma* smul_mem_lifts
- \+ *def* lifts
- \+ *def* lifts_ring
- \+ *def* map_alg



## [2020-10-30 14:20:39](https://github.com/leanprover-community/mathlib/commit/bfadf05)
feat(algebra, logic): Pi instances for nontrivial and monoid_with_zero ([#4766](https://github.com/leanprover-community/mathlib/pull/4766))
#### Estimated changes
modified src/algebra/group/pi.lean
- \- *lemma* single_eq_same
- \- *lemma* single_eq_of_ne
- \- *def* single

modified src/algebra/ring/pi.lean

created src/data/pi.lean
- \+ *lemma* single_eq_same
- \+ *lemma* single_eq_of_ne
- \+ *lemma* single_injective
- \+ *def* single

modified src/logic/function/basic.lean
- \+ *lemma* update_injective

modified src/logic/nontrivial.lean
- \+ *lemma* nontrivial_at



## [2020-10-30 11:09:12](https://github.com/leanprover-community/mathlib/commit/58f8817)
feat(number_theory/fermat4): The n=4 case of fermat ([#4720](https://github.com/leanprover-community/mathlib/pull/4720))
Fermat's last theorem for n=4.
#### Estimated changes
modified src/algebra/gcd_monoid.lean
- \+/\- *theorem* exists_associated_pow_of_mul_eq_pow
- \+/\- *theorem* exists_associated_pow_of_mul_eq_pow

modified src/algebra/group_power/lemmas.lean
- \+ *lemma* abs_le_self_pow_two
- \+ *lemma* le_self_pow_two

modified src/algebra/group_with_zero_power.lean
- \+/\- *lemma* zero_pow'
- \+ *lemma* ne_zero_pow
- \+/\- *lemma* zero_pow_eq_zero
- \+/\- *lemma* zero_pow'
- \+/\- *lemma* zero_pow_eq_zero
- \+/\- *theorem* pow_eq_zero'
- \+/\- *theorem* pow_ne_zero'
- \+/\- *theorem* pow_eq_zero'
- \+/\- *theorem* pow_ne_zero'

modified src/data/int/basic.lean
- \+ *lemma* neg_mod_two

created src/number_theory/fermat4.lean
- \+ *lemma* comm
- \+ *lemma* mul
- \+ *lemma* ne_zero
- \+ *lemma* exists_minimal
- \+ *lemma* coprime_of_minimal
- \+ *lemma* minimal_comm
- \+ *lemma* neg_of_minimal
- \+ *lemma* exists_odd_minimal
- \+ *lemma* exists_pos_odd_minimal
- \+ *lemma* int.coprime_of_sqr_sum
- \+ *lemma* int.coprime_of_sqr_sum'
- \+ *lemma* not_minimal
- \+ *lemma* not_fermat_42
- \+ *theorem* not_fermat_4
- \+ *def* fermat_42
- \+ *def* minimal

modified src/number_theory/pythagorean_triples.lean
- \+ *theorem* coprime_classification'

modified src/ring_theory/int/basic.lean
- \+ *lemma* exists_unit_of_abs
- \+ *lemma* gcd_eq_one_iff_coprime
- \+ *lemma* sqr_of_gcd_eq_one
- \+ *lemma* sqr_of_coprime
- \+ *lemma* int.prime.dvd_pow
- \+ *lemma* int.prime.dvd_pow'



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
created src/ring_theory/witt_vector/is_poly.lean
- \+ *lemma* bind₁_frobenius_poly_witt_polynomial
- \+ *lemma* poly_eq_of_witt_polynomial_bind_eq'
- \+ *lemma* poly_eq_of_witt_polynomial_bind_eq
- \+ *lemma* ext
- \+ *lemma* comp
- \+ *lemma* is_poly₂.comp
- \+ *lemma* is_poly.comp₂
- \+ *lemma* is_poly₂.diag
- \+ *lemma* neg_is_poly
- \+ *lemma* bind₁_zero_witt_polynomial
- \+ *lemma* bind₁_one_poly_witt_polynomial
- \+ *lemma* add_is_poly₂
- \+ *lemma* mul_is_poly₂
- \+ *lemma* is_poly.map
- \+ *lemma* comp_left
- \+ *lemma* comp_right
- \+ *lemma* ext
- \+ *lemma* map
- \+ *def* is_poly
- \+ *def* is_poly₂
- \+ *def* one_poly



## [2020-10-30 08:20:23](https://github.com/leanprover-community/mathlib/commit/3aac028)
feat(field_theory/intermediate_field): equalities from inclusions and dimension bounds ([#4828](https://github.com/leanprover-community/mathlib/pull/4828))
#### Estimated changes
modified src/field_theory/intermediate_field.lean
- \+ *lemma* eq_of_le_of_findim_le
- \+ *lemma* eq_of_le_of_findim_eq
- \+ *lemma* eq_of_le_of_findim_le'
- \+ *lemma* eq_of_le_of_findim_eq'

modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* eq_of_le_of_findim_le



## [2020-10-30 08:20:21](https://github.com/leanprover-community/mathlib/commit/6ec7aec)
feat(data/polynomial): ext lemmas for homomorphisms from `polynomial R` ([#4823](https://github.com/leanprover-community/mathlib/pull/4823))
#### Estimated changes
modified src/data/polynomial/algebra_map.lean
- \+ *lemma* alg_hom_ext

modified src/data/polynomial/basic.lean
- \+ *lemma* add_hom_ext'
- \+ *lemma* add_hom_ext
- \+ *lemma* lhom_ext'

modified src/data/polynomial/monomial.lean
- \+ *lemma* ring_hom_ext
- \+ *lemma* ring_hom_ext'



## [2020-10-30 08:20:19](https://github.com/leanprover-community/mathlib/commit/03a477c)
feat(data/dfinsupp): Port over the `finsupp.lift_add_hom` API ([#4821](https://github.com/leanprover-community/mathlib/pull/4821))
These lemmas are mostly copied with minimal translation from `finsupp`.
A few proofs are taken from `direct_sum`.
The API of `direct_sum` is deliberately unchanged in this PR.
#### Estimated changes
modified src/algebra/direct_sum.lean

modified src/data/dfinsupp.lean
- \+ *lemma* add_closure_Union_range_single
- \+ *lemma* add_hom_ext
- \+ *lemma* add_hom_ext'
- \+ *lemma* sum_add_hom_single
- \+ *lemma* sum_add_hom_apply
- \+ *def* single_add_hom
- \+ *def* sum_add_hom
- \+ *def* lift_add_hom



## [2020-10-30 08:20:18](https://github.com/leanprover-community/mathlib/commit/5ae192e)
feat(data/equiv, algebra/*): Add simps projections to many equivs and homs ([#4818](https://github.com/leanprover-community/mathlib/pull/4818))
This doesn't actually change any existing lemmas to use these projections.
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *def* simps.inv_fun

modified src/algebra/group/hom.lean

modified src/algebra/module/linear_map.lean
- \+ *def* simps.inv_fun

modified src/algebra/ring/basic.lean

modified src/data/equiv/mul_add.lean
- \+ *def* simps.inv_fun

modified src/data/equiv/ring.lean
- \+ *def* simps.inv_fun



## [2020-10-30 08:20:16](https://github.com/leanprover-community/mathlib/commit/d46d0c2)
chore(topology/basic): the set of cluster pts of a filter is a closed set ([#4815](https://github.com/leanprover-community/mathlib/pull/4815))
#### Estimated changes
modified src/topology/basic.lean
- \+ *lemma* interior_eq_nhds'
- \+ *lemma* interior_set_of_eq
- \+ *lemma* is_open_set_of_eventually_nhds
- \+ *lemma* is_closed_set_of_cluster_pt

modified src/topology/subset_properties.lean

modified src/topology/uniform_space/compact_separated.lean



## [2020-10-30 08:20:14](https://github.com/leanprover-community/mathlib/commit/072cfc5)
chore(data/dfinsupp): Provide dfinsupp with a semimodule instance ([#4801](https://github.com/leanprover-community/mathlib/pull/4801))
finsupp already has one, it seems pointless to hide the one for dfinsupp behind a def.
#### Estimated changes
modified src/data/dfinsupp.lean
- \- *def* to_has_scalar
- \- *def* to_semimodule

modified src/linear_algebra/direct_sum_module.lean



## [2020-10-30 08:20:09](https://github.com/leanprover-community/mathlib/commit/63c0dac)
refactor(module/ordered): make ordered_semimodule a mixin ([#4719](https://github.com/leanprover-community/mathlib/pull/4719))
Per @urkud's suggestion at [#4683](https://github.com/leanprover-community/mathlib/pull/4683). This should avoid having to introduce a separate `ordered_algebra` class.
#### Estimated changes
modified src/algebra/module/ordered.lean
- \+ *lemma* ordered_semimodule.mk''
- \+ *lemma* ordered_semimodule.mk'
- \- *def* ordered_semimodule.mk''
- \- *def* ordered_semimodule.mk'

modified src/analysis/convex/basic.lean
- \+/\- *lemma* neg_convex_on_iff
- \+/\- *lemma* neg_concave_on_iff
- \+/\- *lemma* convex_on.smul
- \+/\- *lemma* concave_on.smul
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* concave_on.concave_le
- \+/\- *lemma* convex_on.convex_lt
- \+/\- *lemma* concave_on.convex_lt
- \+/\- *lemma* convex_on.convex_epigraph
- \+/\- *lemma* concave_on.convex_hypograph
- \+/\- *lemma* convex_on_iff_convex_epigraph
- \+/\- *lemma* concave_on_iff_convex_hypograph
- \+/\- *lemma* neg_convex_on_iff
- \+/\- *lemma* neg_concave_on_iff
- \+/\- *lemma* convex_on.smul
- \+/\- *lemma* concave_on.smul
- \+/\- *lemma* convex_on.convex_le
- \+/\- *lemma* concave_on.concave_le
- \+/\- *lemma* convex_on.convex_lt
- \+/\- *lemma* concave_on.convex_lt
- \+/\- *lemma* convex_on.convex_epigraph
- \+/\- *lemma* concave_on.convex_hypograph
- \+/\- *lemma* convex_on_iff_convex_epigraph
- \+/\- *lemma* concave_on_iff_convex_hypograph

modified src/analysis/convex/cone.lean
- \+ *lemma* to_ordered_semimodule
- \- *def* to_ordered_semimodule

modified src/analysis/convex/extrema.lean

modified src/linear_algebra/affine_space/ordered.lean



## [2020-10-30 05:28:30](https://github.com/leanprover-community/mathlib/commit/4003b3e)
feat(*): a, switch to lean 3.23 ([#4802](https://github.com/leanprover-community/mathlib/pull/4802))
There are three changes affecting mathlib:
1. `ℕ → ℕ` is now elaborated as `∀ ᾰ : ℕ, ℕ`.  This means that `intro` introduces assumptions with names like `ᾰ_1`, etc.  These names should not be used, and instead provided explicitly to `intro` (and other tactics).
2. The heuristic to determine the definition name for `instance : foo bar` has been changed.
3. `by_contra` now uses classical logic, and defaults to the hypothesis name `h`.
4. adds a few new simp-lemmas in `data/typevec`
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified leanpkg.toml

modified scripts/lint-copy-mod-doc.py
- \+ *def* small_alpha_vrachy_check(lines,

modified src/algebra/algebra/subalgebra.lean

modified src/algebra/category/Group/basic.lean

modified src/algebra/free_algebra.lean

modified src/algebra/group/ulift.lean

modified src/analysis/special_functions/trigonometric.lean

modified src/category_theory/is_connected.lean

modified src/category_theory/limits/cofinal.lean

modified src/category_theory/limits/connected.lean

modified src/category_theory/limits/shapes/equalizers.lean

modified src/category_theory/preadditive/biproducts.lean

modified src/category_theory/reflects_isomorphisms.lean

modified src/combinatorics/simple_graph.lean

modified src/computability/tm_to_partrec.lean

modified src/control/functor/multivariate.lean

modified src/control/lawful_fix.lean

modified src/data/dfinsupp.lean

modified src/data/finsupp/lattice.lean

modified src/data/int/basic.lean

modified src/data/list/basic.lean

modified src/data/list/sigma.lean

modified src/data/matrix/basic.lean

modified src/data/mv_polynomial/monad.lean

modified src/data/nat/factorial.lean

modified src/data/nat/prime.lean

modified src/data/nat/sqrt.lean

modified src/data/num/lemmas.lean

modified src/data/padics/padic_integers.lean

modified src/data/padics/padic_numbers.lean

modified src/data/pfunctor/univariate/M.lean

modified src/data/polynomial/algebra_map.lean

modified src/data/polynomial/degree/basic.lean

modified src/data/real/basic.lean
- \+/\- *def* comm_ring_aux
- \+/\- *def* comm_ring_aux

modified src/data/real/cau_seq_completion.lean

modified src/data/sym2.lean

modified src/data/typevec.lean
- \+ *lemma* prod_fst_mk
- \+ *lemma* prod_snd_mk
- \+ *lemma* subtype_val_to_subtype
- \+ *lemma* to_subtype'_of_subtype'
- \+ *lemma* subtype_val_to_subtype'

modified src/geometry/manifold/algebra/smooth_functions.lean

modified src/group_theory/abelianization.lean

modified src/group_theory/group_action.lean

modified src/group_theory/presented_group.lean

modified src/group_theory/quotient_group.lean

modified src/group_theory/sylow.lean

modified src/logic/basic.lean

modified src/number_theory/lucas_lehmer.lean

modified src/order/omega_complete_partial_order.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/localization.lean

modified src/testing/slim_check/sampleable.lean

modified src/topology/algebra/uniform_ring.lean

modified src/topology/category/Compactum.lean

modified src/topology/category/UniformSpace.lean

modified src/topology/omega_complete_partial_order.lean

modified test/finish3.lean

modified test/norm_cast.lean

modified test/pretty_cases.lean

modified test/qpf.lean



## [2020-10-30 02:02:16](https://github.com/leanprover-community/mathlib/commit/581b2af)
feat(analysis/asymptotics): Equivalent definitions for `is_[oO] u v l` looking like `u = φ * v` for some `φ` ([#4646](https://github.com/leanprover-community/mathlib/pull/4646))
The advantage of these statements over `u/v` tendsto 0 / is bounded is they do not require any nonvanishing assumptions about `v`
#### Estimated changes
modified src/analysis/asymptotics.lean
- \+ *lemma* is_O_with.eventually_mul_div_cancel
- \+ *lemma* is_O.eventually_mul_div_cancel
- \+ *lemma* is_o.eventually_mul_div_cancel
- \+ *lemma* is_O_with_of_eq_mul
- \+ *lemma* is_O_with_iff_exists_eq_mul
- \+ *lemma* is_O_with.exists_eq_mul
- \+ *lemma* is_O_iff_exists_eq_mul
- \+ *lemma* is_o_iff_exists_eq_mul



## [2020-10-30 01:08:49](https://github.com/leanprover-community/mathlib/commit/f510728)
chore(scripts): update nolints.txt ([#4825](https://github.com/leanprover-community/mathlib/pull/4825))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



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
modified src/tactic/abel.lean

modified src/tactic/norm_num.lean

modified src/tactic/ring_exp.lean

modified test/norm_num.lean
- \+ *def* foo



## [2020-10-29 19:28:13](https://github.com/leanprover-community/mathlib/commit/2c7efdf)
feat(category_theory/sites): Grothendieck topology on a space ([#4819](https://github.com/leanprover-community/mathlib/pull/4819))
The grothendieck topology associated to a topological space.
I also changed a definition I meant to change in [#4816](https://github.com/leanprover-community/mathlib/pull/4816), and updated the TODOs of some docstrings; I can split these into separate PRs if needed but I think all the changes are quite minor
#### Estimated changes
modified src/category_theory/sites/grothendieck.lean

modified src/category_theory/sites/pretopology.lean

modified src/category_theory/sites/sieves.lean
- \+ *lemma* singleton_self
- \- *lemma* singleton_arrow_self

created src/category_theory/sites/spaces.lean
- \+ *lemma* pretopology_to_grothendieck
- \+ *def* grothendieck_topology
- \+ *def* pretopology



## [2020-10-29 19:28:10](https://github.com/leanprover-community/mathlib/commit/92af9fa)
feat(category_theory/limits/pullbacks): pullback self is id iff mono ([#4813](https://github.com/leanprover-community/mathlib/pull/4813))
#### Estimated changes
modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* mono_of_is_limit_mk_id_id
- \+ *def* is_limit_mk_id_id



## [2020-10-29 19:28:07](https://github.com/leanprover-community/mathlib/commit/78811e0)
feat(ring_theory/unique_factorization_domain): `unique_factorization_monoid` structure on polynomials over ufd ([#4774](https://github.com/leanprover-community/mathlib/pull/4774))
Provides the `unique_factorization_monoid` structure on polynomials over a UFD
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified src/ring_theory/polynomial/basic.lean
- \+/\- *theorem* exists_irreducible_of_degree_pos
- \+/\- *theorem* exists_irreducible_of_nat_degree_pos
- \+/\- *theorem* exists_irreducible_of_nat_degree_ne_zero
- \+/\- *theorem* exists_irreducible_of_degree_pos
- \+/\- *theorem* exists_irreducible_of_nat_degree_pos
- \+/\- *theorem* exists_irreducible_of_nat_degree_ne_zero

modified src/ring_theory/polynomial/content.lean

modified src/ring_theory/unique_factorization_domain.lean



## [2020-10-29 19:28:03](https://github.com/leanprover-community/mathlib/commit/856381c)
chore(data/equiv/basic): arrow_congr preserves properties of binary operators ([#4759](https://github.com/leanprover-community/mathlib/pull/4759))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* semiconj_conj
- \+ *lemma* semiconj₂_conj

modified src/logic/function/conjugate.lean
- \+ *lemma* is_associative_right
- \+ *lemma* is_associative_left
- \+ *lemma* is_idempotent_right
- \+ *lemma* is_idempotent_left



## [2020-10-29 19:28:00](https://github.com/leanprover-community/mathlib/commit/ccc98d0)
refactor(*): `midpoint`, `point_reflection`, and Mazur-Ulam in affine spaces ([#4752](https://github.com/leanprover-community/mathlib/pull/4752))
* redefine `midpoint` for points in an affine space;
* redefine `point_reflection` for affine spaces (as `equiv`,
  `affine_equiv`, and `isometric`);
* define `const_vsub` as `equiv`, `affine_equiv`, and `isometric`;
* define `affine_map.of_map_midpoint`;
* fully migrate the proof of Mazur-Ulam theorem to affine spaces;
#### Estimated changes
modified src/algebra/add_torsor.lean
- \+ *lemma* coe_const_vsub
- \+ *lemma* coe_const_vsub_symm
- \+ *lemma* point_reflection_apply
- \+ *lemma* point_reflection_symm
- \+ *lemma* point_reflection_self
- \+ *lemma* point_reflection_involutive
- \+ *lemma* point_reflection_fixed_iff_of_injective_bit0
- \+ *lemma* injective_point_reflection_left_of_injective_bit0
- \+ *def* const_vsub
- \+ *def* point_reflection

modified src/algebra/invertible.lean
- \+ *lemma* one_sub_inv_of_two

deleted src/algebra/midpoint.lean
- \- *lemma* midpoint_eq_iff
- \- *lemma* midpoint_add_self
- \- *lemma* midpoint_unique
- \- *lemma* midpoint_self
- \- *lemma* midpoint_def
- \- *lemma* midpoint_comm
- \- *lemma* midpoint_zero_add
- \- *lemma* midpoint_add_add
- \- *lemma* midpoint_add_right
- \- *lemma* midpoint_add_left
- \- *lemma* midpoint_smul_smul
- \- *lemma* midpoint_neg_neg
- \- *lemma* midpoint_sub_sub
- \- *lemma* midpoint_sub_right
- \- *lemma* midpoint_sub_left
- \- *lemma* coe_of_map_midpoint
- \- *lemma* point_reflection_midpoint_left
- \- *lemma* point_reflection_midpoint_right
- \- *def* midpoint
- \- *def* of_map_midpoint

modified src/algebra/module/basic.lean
- \+ *theorem* two_smul'

modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* coe_const_vsub
- \+ *lemma* coe_const_vsub_symm
- \+ *lemma* point_reflection_apply
- \+ *lemma* point_reflection_to_equiv
- \+ *lemma* point_reflection_self
- \+ *lemma* point_reflection_involutive
- \+ *lemma* point_reflection_symm
- \+ *lemma* dist_point_reflection_fixed
- \+ *lemma* dist_point_reflection_self'
- \+ *lemma* dist_point_reflection_self
- \+ *lemma* point_reflection_fixed_iff
- \+ *lemma* dist_point_reflection_self_real
- \+ *lemma* point_reflection_midpoint_left
- \+ *lemma* point_reflection_midpoint_right
- \+ *def* const_vsub
- \+ *def* point_reflection
- \+ *def* affine_map.of_map_midpoint

modified src/analysis/normed_space/mazur_ulam.lean
- \+/\- *lemma* midpoint_fixed
- \+/\- *lemma* map_midpoint
- \+ *lemma* coe_to_affine_equiv
- \+/\- *lemma* midpoint_fixed
- \+/\- *lemma* map_midpoint
- \- *lemma* coe_to_affine_map
- \+ *def* to_affine_equiv
- \- *def* to_affine_map

deleted src/analysis/normed_space/point_reflection.lean
- \- *lemma* equiv.point_reflection_fixed_iff_of_module
- \- *lemma* point_reflection_apply
- \- *lemma* point_reflection_to_equiv
- \- *lemma* point_reflection_self
- \- *lemma* point_reflection_involutive
- \- *lemma* point_reflection_symm
- \- *lemma* point_reflection_dist_fixed
- \- *lemma* point_reflection_dist_self'
- \- *lemma* point_reflection_midpoint_left
- \- *lemma* point_reflection_midpoint_right
- \- *lemma* point_reflection_fixed_iff
- \- *lemma* point_reflection_dist_self
- \- *lemma* point_reflection_dist_self_real
- \- *def* point_reflection

modified src/data/equiv/mul_add.lean
- \- *lemma* point_reflection_apply
- \- *lemma* point_reflection_self
- \- *lemma* point_reflection_involutive
- \- *lemma* point_reflection_symm
- \- *lemma* point_reflection_fixed_iff_of_bit0_injective
- \- *def* point_reflection

modified src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* apply_line_map
- \+ *lemma* coe_const_vsub
- \+ *lemma* coe_const_vsub_symm
- \+ *lemma* point_reflection_apply
- \+ *lemma* point_reflection_symm
- \+ *lemma* to_equiv_point_reflection
- \+ *lemma* point_reflection_self
- \+ *lemma* point_reflection_involutive
- \+ *lemma* point_reflection_fixed_iff_of_injective_bit0
- \+ *lemma* injective_point_reflection_left_of_injective_bit0
- \+ *lemma* injective_point_reflection_left_of_module
- \+ *lemma* point_reflection_fixed_iff_of_module
- \+ *lemma* line_map_vadd
- \+ *lemma* line_map_vsub
- \+ *lemma* vsub_line_map
- \+ *lemma* vadd_line_map
- \+ *lemma* homothety_neg_one_apply
- \+ *def* const_vsub
- \+ *def* point_reflection

modified src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* line_map_vsub_left
- \+ *lemma* left_vsub_line_map
- \+ *lemma* line_map_vsub_right
- \+ *lemma* right_vsub_line_map
- \+ *lemma* line_map_vadd_line_map
- \+ *lemma* line_map_vsub_line_map
- \+ *lemma* homothety_eq_line_map

created src/linear_algebra/affine_space/midpoint.lean
- \+ *lemma* affine_map.map_midpoint
- \+ *lemma* affine_equiv.map_midpoint
- \+ *lemma* affine_equiv.point_reflection_midpoint_left
- \+ *lemma* midpoint_comm
- \+ *lemma* affine_equiv.point_reflection_midpoint_right
- \+ *lemma* midpoint_vsub_midpoint
- \+ *lemma* midpoint_vadd_midpoint
- \+ *lemma* midpoint_eq_iff
- \+ *lemma* midpoint_eq_midpoint_iff_vsub_eq_vsub
- \+ *lemma* midpoint_eq_iff'
- \+ *lemma* midpoint_unique
- \+ *lemma* midpoint_self
- \+ *lemma* midpoint_add_self
- \+ *lemma* midpoint_zero_add
- \+ *lemma* line_map_inv_two
- \+ *lemma* line_map_one_half
- \+ *lemma* homothety_inv_of_two
- \+ *lemma* homothety_inv_two
- \+ *lemma* homothety_one_half
- \+ *lemma* coe_of_map_midpoint
- \+ *def* midpoint
- \+ *def* of_map_midpoint



## [2020-10-29 19:27:56](https://github.com/leanprover-community/mathlib/commit/4d19191)
feat(algebra/monoid_algebra): Add an equivalence between `add_monoid_algebra` and `monoid_algebra` in terms of `multiplicative` ([#4402](https://github.com/leanprover-community/mathlib/pull/4402))
#### Estimated changes
modified src/algebra/monoid_algebra.lean
- \+ *lemma* map_domain_mul
- \+ *lemma* map_domain_mul



## [2020-10-29 18:26:22](https://github.com/leanprover-community/mathlib/commit/d709ed6)
feat(algebra/direct_sum*): relax a lot of constraints to add_comm_monoid ([#3537](https://github.com/leanprover-community/mathlib/pull/3537))
#### Estimated changes
modified src/algebra/direct_limit.lean

modified src/algebra/direct_sum.lean
- \+ *lemma* sub_apply
- \+ *lemma* to_add_monoid_of
- \- *lemma* to_group_of
- \+ *theorem* to_add_monoid.unique
- \- *theorem* to_group.unique
- \+/\- *def* direct_sum
- \+ *def* to_add_monoid
- \+/\- *def* direct_sum
- \- *def* to_group

modified src/linear_algebra/direct_sum_module.lean
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_apply



## [2020-10-29 15:42:46](https://github.com/leanprover-community/mathlib/commit/f83468d)
feat(category_theory/functor_category): monos in the functor category ([#4811](https://github.com/leanprover-community/mathlib/pull/4811))
#### Estimated changes
modified src/category_theory/functor_category.lean
- \+ *lemma* mono_app_of_mono
- \+ *lemma* epi_app_of_epi



## [2020-10-29 14:18:55](https://github.com/leanprover-community/mathlib/commit/7d7e850)
chore(category_theory/sites): nicer names ([#4816](https://github.com/leanprover-community/mathlib/pull/4816))
Changes the name `arrows_with_codomain` to `presieve` which is more suggestive and shorter, and changes `singleton_arrow` to `singleton`, since it's in the presieve namespace anyway.
#### Estimated changes
modified src/category_theory/sites/pretopology.lean
- \+/\- *def* pullback_arrows
- \+/\- *def* pullback_arrows

modified src/category_theory/sites/sieves.lean
- \+/\- *lemma* bind_comp
- \+ *lemma* singleton_eq_iff_domain
- \+/\- *lemma* singleton_arrow_self
- \+/\- *lemma* mem_generate
- \+/\- *lemma* sets_iff_generate
- \+/\- *lemma* pushforward_le_bind_of_mem
- \+/\- *lemma* le_pullback_bind
- \+/\- *lemma* bind_comp
- \- *lemma* singleton_arrow_eq_iff_domain
- \+/\- *lemma* singleton_arrow_self
- \+/\- *lemma* mem_generate
- \+/\- *lemma* sets_iff_generate
- \+/\- *lemma* pushforward_le_bind_of_mem
- \+/\- *lemma* le_pullback_bind
- \+ *def* presieve
- \+/\- *def* bind
- \+ *def* singleton
- \+/\- *def* generate
- \+/\- *def* bind
- \+/\- *def* gi_generate
- \- *def* arrows_with_codomain
- \+/\- *def* bind
- \- *def* singleton_arrow
- \+/\- *def* generate
- \+/\- *def* bind
- \+/\- *def* gi_generate



## [2020-10-29 13:24:15](https://github.com/leanprover-community/mathlib/commit/8b858d0)
feat(data/dfinsupp): Relax requirements of semimodule conversion to add_comm_monoid ([#3490](https://github.com/leanprover-community/mathlib/pull/3490))
The extra `_`s required to make this still build are unfortunate, but hopefully someone else can work out how to remove them in a later PR.
#### Estimated changes
modified src/algebra/direct_limit.lean

modified src/algebra/direct_sum.lean
- \+ *lemma* zero_apply
- \+ *lemma* add_apply

modified src/algebra/lie/basic.lean
- \+/\- *lemma* of_associative_algebra_hom_id
- \+/\- *lemma* of_associative_algebra_hom_id

modified src/data/dfinsupp.lean
- \+/\- *lemma* ext
- \+/\- *lemma* smul_apply
- \+/\- *lemma* support_smul
- \+/\- *lemma* ext
- \+/\- *lemma* smul_apply
- \+/\- *lemma* support_smul
- \+/\- *def* to_has_scalar
- \+/\- *def* to_semimodule
- \+/\- *def* to_has_scalar
- \+/\- *def* to_semimodule

modified src/linear_algebra/direct_sum_module.lean
- \+ *lemma* smul_apply
- \+ *lemma* support_smul



## [2020-10-29 09:49:53](https://github.com/leanprover-community/mathlib/commit/d510a63)
feat(linear_algebra/finite_dimensional): finite dimensional algebra_hom of fields is bijective ([#4793](https://github.com/leanprover-community/mathlib/pull/4793))
Changes to finite_dimensional.lean from [#4786](https://github.com/leanprover-community/mathlib/pull/4786)
#### Estimated changes
modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* bijective



## [2020-10-29 07:30:22](https://github.com/leanprover-community/mathlib/commit/1baf701)
feat(category_theory/Fintype): Adds the category of finite types and its "standard" skeleton. ([#4809](https://github.com/leanprover-community/mathlib/pull/4809))
This PR adds the category `Fintype` of finite types, as well as its "standard" skeleton whose objects are `fin n`.
#### Estimated changes
created src/category_theory/Fintype.lean
- \+ *lemma* is_skeletal
- \+ *lemma* incl_mk_nat_card
- \+ *def* Fintype
- \+ *def* of
- \+ *def* incl
- \+ *def* skeleton
- \+ *def* mk
- \+ *def* to_nat
- \+ *def* incl

modified src/data/fintype/basic.lean
- \+ *lemma* fin.equiv_iff_eq



## [2020-10-29 01:05:47](https://github.com/leanprover-community/mathlib/commit/d9c8215)
chore(scripts): update nolints.txt ([#4814](https://github.com/leanprover-community/mathlib/pull/4814))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



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
modified src/meta/expr.lean

modified src/meta/rb_map.lean

modified src/tactic/basic.lean

modified src/tactic/core.lean

created src/tactic/dependencies.lean

modified src/tactic/interactive.lean

modified src/tactic/wlog.lean

created test/dependencies.lean

modified test/tactics.lean



## [2020-10-28 18:09:43](https://github.com/leanprover-community/mathlib/commit/d75da1a)
feat(topology/algebra/group_with_zero): introduce `has_continuous_inv'` ([#4804](https://github.com/leanprover-community/mathlib/pull/4804))
Move lemmas about continuity of division from `normed_field`, add a few new lemmas, and introduce a new typeclass. Also use it for `nnreal`s.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \- *lemma* tendsto_inv
- \- *lemma* continuous_on_inv
- \- *lemma* filter.tendsto.inv'
- \- *lemma* continuous_at.inv'
- \- *lemma* continuous_within_at.inv'
- \- *lemma* continuous.inv'
- \- *lemma* continuous_on.inv'
- \- *lemma* filter.tendsto.div_const
- \- *lemma* filter.tendsto.div
- \- *lemma* continuous_within_at.div
- \- *lemma* continuous_on.div
- \- *lemma* continuous_at.div
- \- *lemma* continuous.div

modified src/measure_theory/borel_space.lean

created src/topology/algebra/group_with_zero.lean
- \+ *lemma* filter.tendsto.div_const
- \+ *lemma* continuous_at.div_const
- \+ *lemma* continuous_within_at.div_const
- \+ *lemma* continuous_on.div_const
- \+ *lemma* continuous.div_const
- \+ *lemma* tendsto_inv'
- \+ *lemma* continuous_on_inv'
- \+ *lemma* filter.tendsto.inv'
- \+ *lemma* continuous_within_at.inv'
- \+ *lemma* continuous_at.inv'
- \+ *lemma* continuous.inv'
- \+ *lemma* continuous_on.inv'
- \+ *lemma* filter.tendsto.div
- \+ *lemma* continuous_within_at.div
- \+ *lemma* continuous_on.div
- \+ *lemma* continuous_at.div
- \+ *lemma* continuous.div
- \+ *lemma* continuous_on_div

modified src/topology/instances/ennreal.lean

modified src/topology/instances/nnreal.lean
- \+/\- *lemma* tendsto_coe
- \+/\- *lemma* tendsto_coe
- \- *lemma* tendsto.sub



## [2020-10-28 18:09:41](https://github.com/leanprover-community/mathlib/commit/80ffad0)
chore(data/dfinsupp): Make some lemma arguments explicit ([#4803](https://github.com/leanprover-community/mathlib/pull/4803))
This file is long and this is not exhaustive, but this hits most of the simpler ones
#### Estimated changes
modified src/algebra/lie/basic.lean

modified src/data/dfinsupp.lean
- \+/\- *lemma* zero_apply
- \+/\- *lemma* add_apply
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+/\- *lemma* filter_pos_add_filter_neg
- \+/\- *lemma* zero_apply
- \+/\- *lemma* add_apply
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+/\- *lemma* filter_pos_add_filter_neg

modified src/linear_algebra/direct_sum_module.lean



## [2020-10-28 18:09:39](https://github.com/leanprover-community/mathlib/commit/7a37dd4)
feat(algebra/monoid_algebra): Bundle lift_nc_mul and lift_nc_one into a ring_hom and alg_hom ([#4789](https://github.com/leanprover-community/mathlib/pull/4789))
#### Estimated changes
modified src/algebra/monoid_algebra.lean
- \+ *def* lift_nc_ring_hom
- \+ *def* lift_nc_alg_hom
- \+ *def* lift_nc_ring_hom
- \+ *def* lift_nc_alg_hom



## [2020-10-28 18:09:37](https://github.com/leanprover-community/mathlib/commit/28cc74f)
feat(ring_theory/unique_factorization_domain): a `normalization_monoid` structure for ufms ([#4772](https://github.com/leanprover-community/mathlib/pull/4772))
Provides a default `normalization_monoid` structure on a `unique_factorization_monoid`
#### Estimated changes
modified src/algebra/associated.lean
- \+ *lemma* mk_monoid_hom_apply
- \+ *lemma* associated_map_mk

modified src/algebra/gcd_monoid.lean
- \+ *def* normalization_monoid_of_monoid_hom_right_inverse

modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* factors_one
- \+ *lemma* factors_mul



## [2020-10-28 18:09:35](https://github.com/leanprover-community/mathlib/commit/25df267)
feat(category_theory/limits/presheaf): free cocompletion ([#4740](https://github.com/leanprover-community/mathlib/pull/4740))
Fill in the missing part of [#4401](https://github.com/leanprover-community/mathlib/pull/4401), showing that the yoneda extension is unique. Also adds some basic API around [#4401](https://github.com/leanprover-community/mathlib/pull/4401).
#### Estimated changes
modified docs/references.bib

modified src/category_theory/elements.lean
- \+ *lemma* map_π
- \+ *def* map

modified src/category_theory/limits/preserves/basic.lean
- \+ *def* is_limit_of_preserves
- \+ *def* is_colimit_of_preserves

modified src/category_theory/limits/presheaf.lean
- \+ *lemma* cocone_of_representable_ι_app
- \+ *lemma* cocone_of_representable_naturality
- \+ *def* nat_iso_of_nat_iso_on_representables
- \+ *def* unique_extension_along_yoneda



## [2020-10-28 18:09:33](https://github.com/leanprover-community/mathlib/commit/dfa85b5)
feat(archive/imo): formalize IMO 1981 problem Q3 ([#4599](https://github.com/leanprover-community/mathlib/pull/4599))
Determine the maximum value of `m ^ 2 + n ^ 2`, where `m` and `n` are integers in
`{1, 2, ..., 1981}` and `(n ^ 2 - m * n - m ^ 2) ^ 2 = 1`.
#### Estimated changes
created archive/imo/imo1981_q3.lean
- \+ *lemma* m_le_n
- \+ *lemma* eq_imp_1
- \+ *lemma* reduction
- \+ *lemma* m_le_n
- \+ *lemma* eq_imp_1
- \+ *lemma* reduction
- \+ *lemma* n_pos
- \+ *lemma* m_pos
- \+ *lemma* n_le_N
- \+ *lemma* imp_fib
- \+ *lemma* m_n_bounds
- \+ *lemma* k_bound
- \+ *lemma* solution_bound
- \+ *theorem* solution_greatest
- \+ *theorem* imo1981_q3
- \+ *def* specified_set
- \+ *def* nat_predicate

modified src/algebra/ordered_ring.lean
- \+ *lemma* zero_lt_three
- \+ *lemma* mul_self_inj
- \+ *lemma* abs_eq_iff_mul_self_eq
- \+ *lemma* abs_lt_iff_mul_self_lt
- \+ *lemma* abs_le_iff_mul_self_le

modified src/data/int/basic.lean
- \+ *lemma* nat_abs_eq_iff_mul_self_eq
- \+ *lemma* nat_abs_lt_iff_mul_self_lt
- \+ *lemma* nat_abs_le_iff_mul_self_le
- \+ *lemma* nat_abs_eq_iff_sq_eq
- \+ *lemma* nat_abs_lt_iff_sq_lt
- \+ *lemma* nat_abs_le_iff_sq_le

modified src/data/nat/basic.lean
- \+/\- *lemma* zero_max
- \+/\- *lemma* zero_max
- \+ *theorem* eq_one_of_mul_eq_one_right
- \+ *theorem* eq_one_of_mul_eq_one_left

modified src/data/nat/fib.lean
- \+ *lemma* fib_two



## [2020-10-28 15:21:10](https://github.com/leanprover-community/mathlib/commit/40da087)
feat(equiv/basic): use @[simps] ([#4652](https://github.com/leanprover-community/mathlib/pull/4652))
Use the `@[simps]` attribute to automatically generate equation lemmas for equivalences.
The names `foo_apply` and `foo_symm_apply` are used for the projection lemmas of `foo`.
#### Estimated changes
modified src/data/equiv/basic.lean
- \- *lemma* coe_ulift
- \- *lemma* coe_ulift_symm
- \- *lemma* coe_plift
- \- *lemma* coe_plift_symm
- \- *lemma* arrow_congr_apply
- \- *lemma* arrow_congr'_apply
- \- *lemma* conj_apply
- \- *lemma* coe_prod_comm
- \- *lemma* sum_comm_apply
- \- *lemma* sigma_preimage_equiv_apply
- \- *lemma* sigma_preimage_equiv_symm_apply_fst
- \- *lemma* sigma_preimage_equiv_symm_apply_snd_fst
- \- *lemma* subtype_preimage_apply
- \- *lemma* subtype_preimage_symm_apply_coe
- \- *lemma* fun_unique_apply
- \- *lemma* fun_unique_symm_apply
- \- *lemma* psigma_equiv_sigma_apply
- \- *lemma* psigma_equiv_sigma_symm_apply
- \- *lemma* sigma_congr_right_apply
- \- *lemma* sigma_congr_right_symm_apply
- \- *lemma* sigma_congr_left_apply
- \- *lemma* sigma_equiv_prod_apply
- \- *lemma* sigma_equiv_prod_symm_apply
- \- *lemma* subtype_congr_right_mk
- \- *lemma* univ_apply
- \- *lemma* univ_symm_apply
- \- *lemma* of_eq_apply
- \- *lemma* of_eq_symm_apply
- \- *lemma* of_injective_apply
- \- *lemma* Pi_congr_left'_apply
- \- *lemma* Pi_congr_left'_symm_apply
- \- *theorem* coe_prod_congr
- \- *theorem* prod_assoc_apply
- \- *theorem* prod_assoc_sym_apply
- \- *theorem* prod_punit_apply
- \- *theorem* punit_prod_apply
- \- *theorem* sum_congr_apply
- \- *theorem* image_apply
- \- *theorem* range_apply
- \- *theorem* coe_of_bijective
- \+ *def* simps.inv_fun
- \+/\- *def* arrow_congr
- \+/\- *def* prod_congr
- \+/\- *def* prod_comm
- \+/\- *def* prod_assoc
- \+/\- *def* prod_punit
- \+/\- *def* fun_unique
- \+/\- *def* psigma_equiv_sigma
- \+/\- *def* sigma_equiv_prod
- \+/\- *def* Pi_congr_left'
- \+/\- *def* arrow_congr
- \+/\- *def* prod_congr
- \+/\- *def* prod_comm
- \+/\- *def* prod_assoc
- \+/\- *def* prod_punit
- \+/\- *def* fun_unique
- \+/\- *def* psigma_equiv_sigma
- \+/\- *def* sigma_equiv_prod
- \+/\- *def* Pi_congr_left'

modified src/data/subtype.lean
- \+ *def* simps.val
- \+/\- *def* coind
- \+/\- *def* map
- \+/\- *def* coind
- \+/\- *def* map

modified src/tactic/simps.lean
- \- *lemma* {nm.append_suffix

modified test/simps.lean
- \- *lemma* specify.specify5_snd_snd.



## [2020-10-28 10:34:25](https://github.com/leanprover-community/mathlib/commit/e8f8de6)
feat(ring_theory/valuation): ring of integers ([#4729](https://github.com/leanprover-community/mathlib/pull/4729))
#### Estimated changes
modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \+ *lemma* zero_lt_one''
- \+ *lemma* pow_lt_pow_succ
- \+ *lemma* pow_lt_pow'

modified src/ring_theory/valuation/basic.lean
- \+ *lemma* map_add_le
- \+ *lemma* map_add_lt
- \+ *lemma* map_sum_le
- \+ *lemma* map_sum_lt
- \+ *lemma* map_sum_lt'

created src/ring_theory/valuation/integers.lean
- \+ *lemma* one_of_is_unit
- \+ *lemma* is_unit_of_one
- \+ *lemma* le_of_dvd
- \+ *lemma* dvd_of_le
- \+ *lemma* dvd_iff_le
- \+ *lemma* le_iff_dvd
- \+ *theorem* integer.integers
- \+ *def* integer

created src/ring_theory/valuation/integral.lean
- \+ *lemma* mem_of_integral



## [2020-10-28 09:18:54](https://github.com/leanprover-community/mathlib/commit/216cbc4)
feat(analysis/special_functions/trigonometric): simp attributes for trig values ([#4806](https://github.com/leanprover-community/mathlib/pull/4806))
simp attributes for the trig values that didn't already have them
#### Estimated changes
modified src/analysis/special_functions/trigonometric.lean
- \+/\- *lemma* cos_pi_div_four
- \+/\- *lemma* sin_pi_div_four
- \+/\- *lemma* cos_pi_div_eight
- \+/\- *lemma* sin_pi_div_eight
- \+/\- *lemma* cos_pi_div_sixteen
- \+/\- *lemma* sin_pi_div_sixteen
- \+/\- *lemma* cos_pi_div_thirty_two
- \+/\- *lemma* sin_pi_div_thirty_two
- \+/\- *lemma* cos_pi_div_three
- \+/\- *lemma* cos_pi_div_six
- \+/\- *lemma* sin_pi_div_six
- \+/\- *lemma* sin_pi_div_three
- \+/\- *lemma* cos_pi_div_four
- \+/\- *lemma* sin_pi_div_four
- \+/\- *lemma* cos_pi_div_eight
- \+/\- *lemma* sin_pi_div_eight
- \+/\- *lemma* cos_pi_div_sixteen
- \+/\- *lemma* sin_pi_div_sixteen
- \+/\- *lemma* cos_pi_div_thirty_two
- \+/\- *lemma* sin_pi_div_thirty_two
- \+/\- *lemma* cos_pi_div_three
- \+/\- *lemma* cos_pi_div_six
- \+/\- *lemma* sin_pi_div_six
- \+/\- *lemma* sin_pi_div_three



## [2020-10-28 07:49:32](https://github.com/leanprover-community/mathlib/commit/6dfa952)
refactor(order/filter): make `filter.has_mem semireducible ([#4807](https://github.com/leanprover-community/mathlib/pull/4807))
This way `simp only []` does not simplify `s ∈ f` to `s ∈ f.sets`.
* Add protected simp lemmas `filter.mem_mk` and `filter.mem_sets`.
* Use implicit argument in `filter.mem_generate_iff`.
* Use `∃ t, s ∈ ...` instead of `s ∈ ⋃ t, ...` in
  `filter.mem_infi_finite` and `filter.mem_infi_finite'`.
* Use an implicit argument in `(non/ne_)empty_of_mem_ultrafilter`.
#### Estimated changes
modified src/analysis/calculus/fderiv.lean

modified src/data/analysis/topology.lean

modified src/order/filter/basic.lean
- \+/\- *lemma* mem_generate_iff
- \+/\- *lemma* binfi_sets_eq
- \+/\- *lemma* mem_generate_iff
- \+/\- *lemma* binfi_sets_eq

modified src/order/filter/lift.lean

modified src/order/filter/partial.lean

modified src/order/filter/pointwise.lean

modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* nonempty_of_mem_ultrafilter
- \+/\- *lemma* ne_empty_of_mem_ultrafilter
- \+/\- *lemma* ne_empty_of_mem_ultrafilter
- \+/\- *lemma* nonempty_of_mem_ultrafilter

modified src/topology/category/Compactum.lean

modified src/topology/metric_space/gluing.lean

modified src/topology/order.lean

modified src/topology/uniform_space/compact_separated.lean



## [2020-10-28 06:06:38](https://github.com/leanprover-community/mathlib/commit/7807f3d)
chore(linear_algebra/affine_space/basic): split ([#4767](https://github.com/leanprover-community/mathlib/pull/4767))
* Split `linear_algebra/affine_space/basic` into two files: `affine_map` and `affine_subspace`.
* Move notation `affine_space` to the bottom of `algebra/add_torsor`.
#### Estimated changes
modified src/algebra/add_torsor.lean

modified src/analysis/convex/basic.lean

modified src/analysis/normed_space/mazur_ulam.lean

modified src/linear_algebra/affine_space/affine_equiv.lean

created src/linear_algebra/affine_space/affine_map.lean
- \+ *lemma* coe_to_affine_map
- \+ *lemma* to_affine_map_linear
- \+ *lemma* coe_mk
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* map_vadd
- \+ *lemma* linear_map_vsub
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* injective_coe_fn
- \+ *lemma* coe_const
- \+ *lemma* const_linear
- \+ *lemma* coe_mk'
- \+ *lemma* mk'_linear
- \+ *lemma* coe_zero
- \+ *lemma* zero_linear
- \+ *lemma* coe_add
- \+ *lemma* add_linear
- \+ *lemma* vadd_apply
- \+ *lemma* vsub_apply
- \+ *lemma* coe_fst
- \+ *lemma* fst_linear
- \+ *lemma* coe_snd
- \+ *lemma* snd_linear
- \+ *lemma* coe_id
- \+ *lemma* id_linear
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* comp_assoc
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_line_map
- \+ *lemma* line_map_apply
- \+ *lemma* line_map_apply_module'
- \+ *lemma* line_map_apply_module
- \+ *lemma* line_map_apply_ring'
- \+ *lemma* line_map_apply_ring
- \+ *lemma* line_map_vadd_apply
- \+ *lemma* line_map_linear
- \+ *lemma* line_map_same_apply
- \+ *lemma* line_map_same
- \+ *lemma* line_map_apply_zero
- \+ *lemma* line_map_apply_one
- \+ *lemma* apply_line_map
- \+ *lemma* comp_line_map
- \+ *lemma* fst_line_map
- \+ *lemma* snd_line_map
- \+ *lemma* line_map_symm
- \+ *lemma* line_map_apply_one_sub
- \+ *lemma* decomp
- \+ *lemma* decomp'
- \+ *lemma* image_interval
- \+ *lemma* coe_smul
- \+ *lemma* homothety_def
- \+ *lemma* homothety_apply
- \+ *lemma* homothety_one
- \+ *lemma* homothety_mul
- \+ *lemma* homothety_zero
- \+ *lemma* homothety_add
- \+ *lemma* coe_homothety_hom
- \+ *lemma* coe_homothety_affine
- \+ *def* to_affine_map
- \+ *def* const
- \+ *def* mk'
- \+ *def* fst
- \+ *def* snd
- \+ *def* id
- \+ *def* comp
- \+ *def* line_map
- \+ *def* homothety
- \+ *def* homothety_hom
- \+ *def* homothety_affine

created src/linear_algebra/affine_space/affine_subspace.lean
- \+ *lemma* vector_span_def
- \+ *lemma* vector_span_mono
- \+ *lemma* vector_span_empty
- \+ *lemma* vector_span_singleton
- \+ *lemma* vsub_set_subset_vector_span
- \+ *lemma* vsub_mem_vector_span
- \+ *lemma* mem_span_points
- \+ *lemma* subset_span_points
- \+ *lemma* span_points_nonempty
- \+ *lemma* vadd_mem_span_points_of_mem_span_points_of_mem_vector_span
- \+ *lemma* vsub_mem_vector_span_of_mem_span_points_of_mem_span_points
- \+ *lemma* mem_coe
- \+ *lemma* direction_eq_vector_span
- \+ *lemma* direction_of_nonempty_eq_direction
- \+ *lemma* coe_direction_eq_vsub_set
- \+ *lemma* mem_direction_iff_eq_vsub
- \+ *lemma* vadd_mem_of_mem_direction
- \+ *lemma* vsub_mem_direction
- \+ *lemma* vadd_mem_iff_mem_direction
- \+ *lemma* coe_direction_eq_vsub_set_right
- \+ *lemma* coe_direction_eq_vsub_set_left
- \+ *lemma* mem_direction_iff_eq_vsub_right
- \+ *lemma* mem_direction_iff_eq_vsub_left
- \+ *lemma* vsub_right_mem_direction_iff_mem
- \+ *lemma* vsub_left_mem_direction_iff_mem
- \+ *lemma* ext
- \+ *lemma* ext_of_direction_eq
- \+ *lemma* eq_iff_direction_eq_of_mem
- \+ *lemma* self_mem_mk'
- \+ *lemma* vadd_mem_mk'
- \+ *lemma* mk'_nonempty
- \+ *lemma* direction_mk'
- \+ *lemma* mk'_eq
- \+ *lemma* span_points_subset_coe_of_subset_coe
- \+ *lemma* coe_affine_span
- \+ *lemma* subset_affine_span
- \+ *lemma* direction_affine_span
- \+ *lemma* mem_affine_span
- \+ *lemma* le_def
- \+ *lemma* le_def'
- \+ *lemma* lt_def
- \+ *lemma* not_le_iff_exists
- \+ *lemma* exists_of_lt
- \+ *lemma* lt_iff_le_and_exists
- \+ *lemma* eq_of_direction_eq_of_nonempty_of_le
- \+ *lemma* affine_span_eq_Inf
- \+ *lemma* span_empty
- \+ *lemma* span_univ
- \+ *lemma* coe_affine_span_singleton
- \+ *lemma* mem_affine_span_singleton
- \+ *lemma* span_union
- \+ *lemma* span_Union
- \+ *lemma* top_coe
- \+ *lemma* mem_top
- \+ *lemma* direction_top
- \+ *lemma* bot_coe
- \+ *lemma* not_mem_bot
- \+ *lemma* direction_bot
- \+ *lemma* direction_eq_top_iff_of_nonempty
- \+ *lemma* inf_coe
- \+ *lemma* mem_inf_iff
- \+ *lemma* direction_inf
- \+ *lemma* direction_inf_of_mem
- \+ *lemma* direction_inf_of_mem_inf
- \+ *lemma* direction_le
- \+ *lemma* direction_lt_of_nonempty
- \+ *lemma* sup_direction_le
- \+ *lemma* sup_direction_lt_of_nonempty_of_inter_empty
- \+ *lemma* inter_nonempty_of_nonempty_of_sup_direction_eq_top
- \+ *lemma* inter_eq_singleton_of_nonempty_of_is_compl
- \+ *lemma* affine_span_coe
- \+ *lemma* vector_span_eq_span_vsub_set_left
- \+ *lemma* vector_span_eq_span_vsub_set_right
- \+ *lemma* vector_span_eq_span_vsub_set_left_ne
- \+ *lemma* vector_span_eq_span_vsub_set_right_ne
- \+ *lemma* vector_span_image_eq_span_vsub_set_left_ne
- \+ *lemma* vector_span_image_eq_span_vsub_set_right_ne
- \+ *lemma* vector_span_range_eq_span_range_vsub_left
- \+ *lemma* vector_span_range_eq_span_range_vsub_right
- \+ *lemma* vector_span_range_eq_span_range_vsub_left_ne
- \+ *lemma* vector_span_range_eq_span_range_vsub_right_ne
- \+ *lemma* affine_span_nonempty
- \+ *lemma* affine_span_singleton_union_vadd_eq_top_of_span_eq_top
- \+ *lemma* affine_span_mono
- \+ *lemma* affine_span_insert_affine_span
- \+ *lemma* affine_span_insert_eq_affine_span
- \+ *lemma* direction_sup
- \+ *lemma* direction_affine_span_insert
- \+ *lemma* mem_affine_span_insert_iff
- \+ *def* vector_span
- \+ *def* span_points
- \+ *def* to_affine_subspace
- \+ *def* direction
- \+ *def* direction_of_nonempty
- \+ *def* mk'
- \+ *def* affine_span

modified src/linear_algebra/affine_space/basic.lean
- \- *lemma* vector_span_def
- \- *lemma* vector_span_mono
- \- *lemma* vector_span_empty
- \- *lemma* vector_span_singleton
- \- *lemma* vsub_set_subset_vector_span
- \- *lemma* vsub_mem_vector_span
- \- *lemma* mem_span_points
- \- *lemma* subset_span_points
- \- *lemma* span_points_nonempty
- \- *lemma* vadd_mem_span_points_of_mem_span_points_of_mem_vector_span
- \- *lemma* vsub_mem_vector_span_of_mem_span_points_of_mem_span_points
- \- *lemma* mem_coe
- \- *lemma* direction_eq_vector_span
- \- *lemma* direction_of_nonempty_eq_direction
- \- *lemma* coe_direction_eq_vsub_set
- \- *lemma* mem_direction_iff_eq_vsub
- \- *lemma* vadd_mem_of_mem_direction
- \- *lemma* vsub_mem_direction
- \- *lemma* vadd_mem_iff_mem_direction
- \- *lemma* coe_direction_eq_vsub_set_right
- \- *lemma* coe_direction_eq_vsub_set_left
- \- *lemma* mem_direction_iff_eq_vsub_right
- \- *lemma* mem_direction_iff_eq_vsub_left
- \- *lemma* vsub_right_mem_direction_iff_mem
- \- *lemma* vsub_left_mem_direction_iff_mem
- \- *lemma* ext
- \- *lemma* ext_of_direction_eq
- \- *lemma* eq_iff_direction_eq_of_mem
- \- *lemma* self_mem_mk'
- \- *lemma* vadd_mem_mk'
- \- *lemma* mk'_nonempty
- \- *lemma* direction_mk'
- \- *lemma* mk'_eq
- \- *lemma* span_points_subset_coe_of_subset_coe
- \- *lemma* coe_affine_span
- \- *lemma* subset_affine_span
- \- *lemma* direction_affine_span
- \- *lemma* mem_affine_span
- \- *lemma* le_def
- \- *lemma* le_def'
- \- *lemma* lt_def
- \- *lemma* not_le_iff_exists
- \- *lemma* exists_of_lt
- \- *lemma* lt_iff_le_and_exists
- \- *lemma* eq_of_direction_eq_of_nonempty_of_le
- \- *lemma* affine_span_eq_Inf
- \- *lemma* span_empty
- \- *lemma* span_univ
- \- *lemma* coe_affine_span_singleton
- \- *lemma* mem_affine_span_singleton
- \- *lemma* span_union
- \- *lemma* span_Union
- \- *lemma* top_coe
- \- *lemma* mem_top
- \- *lemma* direction_top
- \- *lemma* bot_coe
- \- *lemma* not_mem_bot
- \- *lemma* direction_bot
- \- *lemma* direction_eq_top_iff_of_nonempty
- \- *lemma* inf_coe
- \- *lemma* mem_inf_iff
- \- *lemma* direction_inf
- \- *lemma* direction_inf_of_mem
- \- *lemma* direction_inf_of_mem_inf
- \- *lemma* direction_le
- \- *lemma* direction_lt_of_nonempty
- \- *lemma* sup_direction_le
- \- *lemma* sup_direction_lt_of_nonempty_of_inter_empty
- \- *lemma* inter_nonempty_of_nonempty_of_sup_direction_eq_top
- \- *lemma* inter_eq_singleton_of_nonempty_of_is_compl
- \- *lemma* affine_span_coe
- \- *lemma* vector_span_eq_span_vsub_set_left
- \- *lemma* vector_span_eq_span_vsub_set_right
- \- *lemma* vector_span_eq_span_vsub_set_left_ne
- \- *lemma* vector_span_eq_span_vsub_set_right_ne
- \- *lemma* vector_span_image_eq_span_vsub_set_left_ne
- \- *lemma* vector_span_image_eq_span_vsub_set_right_ne
- \- *lemma* vector_span_range_eq_span_range_vsub_left
- \- *lemma* vector_span_range_eq_span_range_vsub_right
- \- *lemma* vector_span_range_eq_span_range_vsub_left_ne
- \- *lemma* vector_span_range_eq_span_range_vsub_right_ne
- \- *lemma* affine_span_nonempty
- \- *lemma* affine_span_singleton_union_vadd_eq_top_of_span_eq_top
- \- *lemma* affine_span_mono
- \- *lemma* affine_span_insert_affine_span
- \- *lemma* affine_span_insert_eq_affine_span
- \- *lemma* direction_sup
- \- *lemma* direction_affine_span_insert
- \- *lemma* mem_affine_span_insert_iff
- \- *lemma* coe_to_affine_map
- \- *lemma* to_affine_map_linear
- \- *lemma* coe_mk
- \- *lemma* to_fun_eq_coe
- \- *lemma* map_vadd
- \- *lemma* linear_map_vsub
- \- *lemma* ext
- \- *lemma* ext_iff
- \- *lemma* injective_coe_fn
- \- *lemma* coe_const
- \- *lemma* const_linear
- \- *lemma* coe_mk'
- \- *lemma* mk'_linear
- \- *lemma* coe_zero
- \- *lemma* zero_linear
- \- *lemma* coe_add
- \- *lemma* add_linear
- \- *lemma* vadd_apply
- \- *lemma* vsub_apply
- \- *lemma* coe_fst
- \- *lemma* fst_linear
- \- *lemma* coe_snd
- \- *lemma* snd_linear
- \- *lemma* coe_id
- \- *lemma* id_linear
- \- *lemma* id_apply
- \- *lemma* coe_comp
- \- *lemma* comp_apply
- \- *lemma* comp_id
- \- *lemma* id_comp
- \- *lemma* comp_assoc
- \- *lemma* coe_mul
- \- *lemma* coe_one
- \- *lemma* coe_line_map
- \- *lemma* line_map_apply
- \- *lemma* line_map_apply_module'
- \- *lemma* line_map_apply_module
- \- *lemma* line_map_apply_ring'
- \- *lemma* line_map_apply_ring
- \- *lemma* line_map_vadd_apply
- \- *lemma* line_map_linear
- \- *lemma* line_map_same_apply
- \- *lemma* line_map_same
- \- *lemma* line_map_apply_zero
- \- *lemma* line_map_apply_one
- \- *lemma* apply_line_map
- \- *lemma* comp_line_map
- \- *lemma* fst_line_map
- \- *lemma* snd_line_map
- \- *lemma* line_map_symm
- \- *lemma* line_map_apply_one_sub
- \- *lemma* decomp
- \- *lemma* decomp'
- \- *lemma* image_interval
- \- *lemma* coe_smul
- \- *lemma* homothety_def
- \- *lemma* homothety_apply
- \- *lemma* homothety_one
- \- *lemma* homothety_mul
- \- *lemma* homothety_zero
- \- *lemma* homothety_add
- \- *lemma* coe_homothety_hom
- \- *lemma* coe_homothety_affine
- \- *def* vector_span
- \- *def* span_points
- \- *def* to_affine_subspace
- \- *def* direction
- \- *def* direction_of_nonempty
- \- *def* mk'
- \- *def* affine_span
- \- *def* to_affine_map
- \- *def* const
- \- *def* mk'
- \- *def* fst
- \- *def* snd
- \- *def* id
- \- *def* comp
- \- *def* line_map
- \- *def* homothety
- \- *def* homothety_hom
- \- *def* homothety_affine

modified src/linear_algebra/affine_space/combination.lean

modified src/linear_algebra/affine_space/finite_dimensional.lean

modified src/linear_algebra/affine_space/independent.lean

modified src/linear_algebra/affine_space/ordered.lean

modified src/topology/algebra/affine.lean



## [2020-10-28 01:11:30](https://github.com/leanprover-community/mathlib/commit/4d1da54)
chore(scripts): update nolints.txt ([#4808](https://github.com/leanprover-community/mathlib/pull/4808))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-27 22:22:51](https://github.com/leanprover-community/mathlib/commit/c737996)
feat(algebra/algebra/subalgebra): algebra equalizer ([#4791](https://github.com/leanprover-community/mathlib/pull/4791))
Changes to subalgebra.lean from [#4786](https://github.com/leanprover-community/mathlib/pull/4786)
#### Estimated changes
modified src/algebra/algebra/subalgebra.lean
- \+ *lemma* mem_equalizer
- \+ *def* equalizer



## [2020-10-27 22:22:50](https://github.com/leanprover-community/mathlib/commit/2a7e215)
feat(data/vector2): scanl and associated lemmas ([#4613](https://github.com/leanprover-community/mathlib/pull/4613))
#### Estimated changes
modified src/data/vector2.lean
- \+/\- *lemma* nth_cons_nil
- \+ *lemma* scanl_nil
- \+ *lemma* scanl_cons
- \+ *lemma* scanl_val
- \+ *lemma* to_list_scanl
- \+ *lemma* scanl_singleton
- \+ *lemma* scanl_head
- \+ *lemma* scanl_nth
- \+/\- *lemma* nth_cons_nil
- \+ *def* scanl



## [2020-10-27 19:53:05](https://github.com/leanprover-community/mathlib/commit/51e12c0)
chore(ring_theory/fractional_ideal): change exists_eq_span_singleton_mul ([#4800](https://github.com/leanprover-community/mathlib/pull/4800))
Replace assumption `(a : K)` with `(a : R)`
Add result `a \ne 0` 
Change `span_singleton` a to `span singleton (g.to_map a)^-1`
.. in the statement of lemma `exists_eq_span_singleton_mul`
Adapt dependences
#### Estimated changes
modified src/ring_theory/fractional_ideal.lean



## [2020-10-27 19:53:03](https://github.com/leanprover-community/mathlib/commit/97065db)
refactor(data/polynomial): use `linear_map` for `monomial`, review `degree` ([#4784](https://github.com/leanprover-community/mathlib/pull/4784))
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* map_int_cast

modified src/algebra/group/basic.lean
- \+ *theorem* one_eq_inv

modified src/analysis/calculus/deriv.lean

modified src/data/polynomial/algebra_map.lean

modified src/data/polynomial/basic.lean
- \+/\- *lemma* monomial_zero_right
- \+ *lemma* monomial_def
- \+ *lemma* smul_monomial
- \+/\- *lemma* monomial_zero_right
- \+/\- *def* monomial
- \+/\- *def* monomial

modified src/data/polynomial/degree.lean
- \- *lemma* eq_C_of_nat_degree_eq_zero

modified src/data/polynomial/degree/basic.lean
- \+ *lemma* coeff_nat_degree
- \+/\- *lemma* le_nat_degree_of_mem_supp
- \+ *lemma* supp_subset_range
- \+/\- *lemma* supp_subset_range_nat_degree_succ
- \+/\- *lemma* degree_monomial
- \+ *lemma* degree_C_mul_X_pow
- \+/\- *lemma* degree_monomial_le
- \+ *lemma* degree_C_mul_X_pow_le
- \+ *lemma* as_sum_support_C_mul_X_pow
- \+/\- *lemma* as_sum_range
- \+ *lemma* as_sum_range_C_mul_X_pow
- \+ *lemma* eq_X_add_C_of_nat_degree_le_one
- \+ *lemma* exists_eq_X_add_C_of_nat_degree_le_one
- \+/\- *lemma* mem_support_C_mul_X_pow
- \+/\- *lemma* support_C_mul_X_pow_nonzero
- \+/\- *lemma* C_eq_int_cast
- \+/\- *lemma* nat_degree_C_mul_X_pow_of_nonzero
- \+/\- *lemma* monic.ne_zero
- \+ *lemma* monic.ne_zero_of_ne
- \+ *lemma* monic.ne_zero_of_polynomial_ne
- \+/\- *lemma* eq_C_of_nat_degree_le_zero
- \+ *lemma* eq_C_of_nat_degree_eq_zero
- \+/\- *lemma* degree_X_pow
- \+/\- *lemma* degree_monomial
- \+/\- *lemma* degree_monomial_le
- \+/\- *lemma* as_sum_range
- \+/\- *lemma* mem_support_C_mul_X_pow
- \+/\- *lemma* le_nat_degree_of_mem_supp
- \+/\- *lemma* supp_subset_range_nat_degree_succ
- \+/\- *lemma* support_C_mul_X_pow_nonzero
- \+/\- *lemma* C_eq_int_cast
- \+/\- *lemma* nat_degree_C_mul_X_pow_of_nonzero
- \- *lemma* monic.ne_zero_of_zero_ne_one
- \+/\- *lemma* monic.ne_zero
- \+/\- *lemma* eq_C_of_nat_degree_le_zero
- \+/\- *lemma* degree_X_pow
- \+ *theorem* nat_degree_le_iff_degree_le
- \- *theorem* nat_degree_le_of_degree_le
- \- *theorem* degree_C_mul_X_pow_le

modified src/data/polynomial/degree/trailing_degree.lean
- \+/\- *lemma* trailing_degree_monomial
- \+ *lemma* nat_trailing_degree_monomial
- \+ *lemma* nat_trailing_degree_monomial_le
- \+ *lemma* le_trailing_degree_monomial
- \+ *lemma* trailing_degree_C_mul_X_pow
- \+ *lemma* le_trailing_degree_C_mul_X_pow
- \+/\- *lemma* trailing_degree_monomial
- \- *lemma* monomial_le_trailing_degree
- \- *theorem* le_trailing_degree_C_mul_X_pow

modified src/data/polynomial/derivative.lean
- \+/\- *lemma* derivative_monomial
- \+ *lemma* derivative_C_mul_X_pow
- \+/\- *lemma* derivative_monomial

modified src/data/polynomial/div.lean

modified src/data/polynomial/erase_lead.lean

modified src/data/polynomial/eval.lean

modified src/data/polynomial/field_division.lean

modified src/data/polynomial/monic.lean

modified src/data/polynomial/monomial.lean
- \+ *theorem* nontrivial.of_polynomial_ne
- \- *theorem* nonzero.of_polynomial_ne

modified src/data/real/irrational.lean
- \+ *lemma* one_lt_nat_degree_of_irrational_root
- \- *lemma* nat_degree_gt_one_of_irrational_root

modified src/field_theory/separable.lean

modified src/ring_theory/polynomial/basic.lean

modified src/ring_theory/polynomial/scale_roots.lean

modified src/ring_theory/polynomial_algebra.lean
- \+ *lemma* inv_fun_monomial



## [2020-10-27 19:53:01](https://github.com/leanprover-community/mathlib/commit/a1ab984)
feat(data/finset/lattice,order/basic): add lemmas in order_dual, prove dual order exchanges max' and min' ([#4715](https://github.com/leanprover-community/mathlib/pull/4715))
Introduce functionality to work with order duals and monotone decreasing maps.  The pretty part of the code is by Johan Commelin, the ugly part is my own addition!
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* nonempty.map

modified src/data/finset/lattice.lean
- \+ *lemma* max'_eq_of_dual_min'
- \+ *lemma* min'_eq_of_dual_max'
- \+ *lemma* of_dual_max_eq_min_of_dual
- \+ *lemma* of_dual_min_eq_max_of_dual

created src/order/order_dual.lean
- \+ *lemma* to_dual_symm_eq
- \+ *lemma* of_dual_symm_eq
- \+ *lemma* to_dual_of_dual
- \+ *lemma* of_dual_to_dual
- \+ *lemma* to_dual_inj
- \+ *lemma* to_dual_le_to_dual
- \+ *lemma* to_dual_lt_to_dual
- \+ *lemma* of_dual_inj
- \+ *lemma* of_dual_le_of_dual
- \+ *lemma* of_dual_lt_of_dual
- \+ *lemma* le_to_dual
- \+ *lemma* lt_to_dual
- \+ *lemma* to_dual_le
- \+ *lemma* to_dual_lt
- \+ *def* to_dual
- \+ *def* of_dual



## [2020-10-27 17:20:51](https://github.com/leanprover-community/mathlib/commit/1efbf13)
feat(data/vector2): add lemma map_id ([#4799](https://github.com/leanprover-community/mathlib/pull/4799))
`map_id` proves that a vector is unchanged when mapped under the `id` function. This is similar to `list.map_id`. This lemma was marked with the `simp` attribute to make it available to the simplifier.
#### Estimated changes
modified src/data/vector2.lean
- \+ *lemma* map_id



## [2020-10-27 17:20:47](https://github.com/leanprover-community/mathlib/commit/40e514c)
feat(algebra/monoid_algebra): formula for `lift_nc f g (c • φ)` ([#4782](https://github.com/leanprover-community/mathlib/pull/4782))
#### Estimated changes
modified src/algebra/monoid_algebra.lean
- \+ *lemma* lift_nc_smul
- \+/\- *lemma* single_algebra_map_eq_algebra_map_mul_of
- \+ *lemma* lift_nc_smul
- \+/\- *lemma* single_algebra_map_eq_algebra_map_mul_of



## [2020-10-27 17:20:45](https://github.com/leanprover-community/mathlib/commit/99acfda)
feat(category_theory/sites): pretopology ([#4648](https://github.com/leanprover-community/mathlib/pull/4648))
Adds pretopologies.
#### Estimated changes
created src/category_theory/sites/pretopology.lean
- \+ *lemma* pullback_arrows_comm
- \+ *lemma* pullback_singleton
- \+ *lemma* mem_to_grothendieck
- \+ *lemma* to_grothendieck_bot
- \+ *def* pullback_arrows
- \+ *def* to_grothendieck
- \+ *def* of_grothendieck
- \+ *def* gi
- \+ *def* trivial



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
modified src/algebra/big_operators/basic.lean

modified src/field_theory/fixed.lean
- \+ *lemma* to_alg_hom_apply_apply
- \- *lemma* to_alg_hom_apply

modified src/logic/embedding.lean
- \+/\- *def* sigma_mk
- \+/\- *def* sigma_map
- \+/\- *def* embedding_of_subset
- \+/\- *def* sigma_mk
- \+/\- *def* sigma_map
- \+/\- *def* embedding_of_subset

modified src/measure_theory/haar_measure.lean

modified src/tactic/simps.lean
- \- *lemma* {simp_lemma}.
- \- *lemma* {simp_lemma}.

modified test/simps.lean
- \- *lemma* specify.specify1_fst_fst.
- \- *lemma* specify.specify1_foo_fst.
- \- *lemma* specify.specify1_foo_fst.
- \- *lemma* specify.specify1_snd_bar.
- \- *lemma* specify.specify1_snd_bar.
- \- *lemma* specify.specify5_snd_snd.
- \+ *def* equiv.symm
- \+ *def* equiv.simps.inv_fun



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
modified archive/100-theorems-list/82_cubing_a_cube.lean
- \+/\- *lemma* Ico_lemma
- \+/\- *lemma* Ico_lemma

modified leanpkg.toml

modified src/algebra/archimedean.lean
- \+/\- *lemma* exists_int_pow_near
- \+/\- *lemma* exists_int_pow_near'
- \+/\- *lemma* exists_int_pow_near
- \+/\- *lemma* exists_int_pow_near'

modified src/algebra/big_operators/order.lean
- \+/\- *lemma* abs_sum_le_sum_abs
- \+/\- *lemma* abs_sum_le_sum_abs

modified src/algebra/continued_fractions/computation/approximations.lean

modified src/algebra/continued_fractions/computation/basic.lean

modified src/algebra/continued_fractions/computation/correctness_terminating.lean

modified src/algebra/continued_fractions/computation/translations.lean

modified src/algebra/field_power.lean
- \+/\- *lemma* one_lt_fpow
- \+/\- *lemma* one_lt_fpow

modified src/algebra/floor.lean
- \+/\- *lemma* abs_sub_lt_one_of_floor_eq_floor
- \+/\- *lemma* abs_sub_lt_one_of_floor_eq_floor

modified src/algebra/group_power/basic.lean
- \+/\- *lemma* pow_abs
- \+/\- *lemma* abs_neg_one_pow
- \+/\- *lemma* pow_abs
- \+/\- *lemma* abs_neg_one_pow

modified src/algebra/group_power/lemmas.lean

modified src/algebra/order.lean
- \+/\- *lemma* le_imp_le_iff_lt_imp_lt
- \+/\- *lemma* le_iff_le_iff_lt_iff_lt
- \+/\- *lemma* le_imp_le_iff_lt_imp_lt
- \+/\- *lemma* le_iff_le_iff_lt_iff_lt
- \+ *theorem* compares_swap
- \+ *theorem* swap_eq_iff_eq_swap
- \+ *theorem* compares.ne_lt
- \+/\- *theorem* compares.eq_gt
- \+ *theorem* compares.ne_gt
- \+ *theorem* compares.le_total
- \+ *theorem* compares.le_antisymm
- \+/\- *theorem* cmp_compares
- \+/\- *theorem* compares.eq_gt
- \+/\- *theorem* cmp_compares
- \+ *def* linear_order_of_compares

modified src/algebra/order_functions.lean

modified src/algebra/ordered_field.lean

modified src/algebra/ordered_group.lean
- \+/\- *lemma* fn_min_mul_fn_max
- \+/\- *lemma* min_mul_max
- \+ *lemma* linear_ordered_add_comm_group.add_lt_add_left
- \+ *lemma* exists_gt_zero
- \+/\- *lemma* fn_min_mul_fn_max
- \+/\- *lemma* min_mul_max
- \- *lemma* decidable_linear_ordered_add_comm_group.add_lt_add_left
- \+/\- *theorem* max_coe
- \+/\- *theorem* min_coe
- \+/\- *theorem* max_coe
- \+/\- *theorem* min_coe
- \+ *def* to_linear_ordered_add_comm_group
- \- *def* to_decidable_linear_ordered_add_comm_group

modified src/algebra/ordered_ring.lean
- \+/\- *lemma* abs_one
- \+/\- *lemma* abs_two
- \+/\- *lemma* abs_mul
- \+/\- *lemma* abs_mul_abs_self
- \+/\- *lemma* abs_mul_self
- \+/\- *lemma* sub_le_of_abs_sub_le_left
- \+/\- *lemma* sub_le_of_abs_sub_le_right
- \+/\- *lemma* sub_lt_of_abs_sub_lt_left
- \+/\- *lemma* sub_lt_of_abs_sub_lt_right
- \+/\- *lemma* eq_zero_of_mul_self_add_mul_self_eq_zero
- \+/\- *lemma* abs_one
- \+/\- *lemma* abs_mul
- \+/\- *lemma* abs_mul_abs_self
- \+/\- *lemma* abs_mul_self
- \+/\- *lemma* sub_le_of_abs_sub_le_left
- \+/\- *lemma* sub_le_of_abs_sub_le_right
- \+/\- *lemma* sub_lt_of_abs_sub_lt_left
- \+/\- *lemma* sub_lt_of_abs_sub_lt_right
- \+/\- *lemma* eq_zero_of_mul_self_add_mul_self_eq_zero
- \+/\- *lemma* abs_two
- \+/\- *def* abs_hom
- \+/\- *def* to_linear_order
- \+/\- *def* to_linear_ordered_ring
- \+ *def* to_linear_ordered_comm_ring
- \+/\- *def* abs_hom
- \+/\- *def* to_linear_order
- \+/\- *def* to_linear_ordered_ring
- \- *def* to_decidable_linear_ordered_comm_ring

modified src/algebra/punit_instances.lean

modified src/analysis/convex/basic.lean

modified src/analysis/convex/extrema.lean

modified src/combinatorics/pigeonhole.lean

modified src/data/bool.lean

modified src/data/char.lean

modified src/data/complex/exponential.lean
- \+/\- *lemma* sum_div_factorial_le
- \+/\- *lemma* sum_div_factorial_le

modified src/data/fin.lean

modified src/data/finset/fold.lean

modified src/data/finset/lattice.lean

modified src/data/finset/sort.lean

modified src/data/fintype/sort.lean

modified src/data/int/basic.lean

modified src/data/int/cast.lean
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs

modified src/data/list/basic.lean
- \+/\- *lemma* exists_lt_of_sum_lt
- \+/\- *lemma* exists_le_of_sum_le
- \+/\- *lemma* exists_lt_of_sum_lt
- \+/\- *lemma* exists_le_of_sum_le

modified src/data/list/min_max.lean

modified src/data/matrix/pequiv.lean

modified src/data/multiset/basic.lean
- \+/\- *lemma* abs_sum_le_sum_abs
- \+/\- *lemma* abs_sum_le_sum_abs

modified src/data/nat/basic.lean

modified src/data/nat/cast.lean
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* abs_cast
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* abs_cast

modified src/data/nat/choose/dvd.lean

modified src/data/nat/enat.lean

modified src/data/num/lemmas.lean

modified src/data/padics/padic_numbers.lean

modified src/data/padics/ring_homs.lean

modified src/data/pnat/basic.lean

modified src/data/polynomial/degree/trailing_degree.lean
- \+/\- *lemma* trailing_degree_eq_nat_trailing_degree
- \+/\- *lemma* nat_trailing_degree_le_trailing_degree
- \+/\- *lemma* nat_trailing_degree_eq_of_trailing_degree_eq
- \+/\- *lemma* trailing_degree_le_trailing_degree
- \+/\- *lemma* nat_trailing_degree_le_nat_trailing_degree
- \+/\- *lemma* nat_trailing_degree_one
- \+/\- *lemma* monomial_le_trailing_degree
- \+/\- *lemma* coeff_eq_zero_of_trailing_degree_lt
- \+/\- *lemma* coeff_eq_zero_of_lt_nat_trailing_degree
- \+/\- *lemma* coeff_nat_trailing_degree_pred_eq_zero
- \+/\- *lemma* nat_trailing_degree_neg
- \+/\- *lemma* coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt
- \+/\- *lemma* trailing_degree_eq_nat_trailing_degree
- \+/\- *lemma* nat_trailing_degree_le_trailing_degree
- \+/\- *lemma* nat_trailing_degree_eq_of_trailing_degree_eq
- \+/\- *lemma* trailing_degree_le_trailing_degree
- \+/\- *lemma* nat_trailing_degree_le_nat_trailing_degree
- \+/\- *lemma* nat_trailing_degree_one
- \+/\- *lemma* monomial_le_trailing_degree
- \+/\- *lemma* coeff_eq_zero_of_trailing_degree_lt
- \+/\- *lemma* coeff_eq_zero_of_lt_nat_trailing_degree
- \+/\- *lemma* coeff_nat_trailing_degree_pred_eq_zero
- \+/\- *lemma* nat_trailing_degree_neg
- \+/\- *lemma* coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt
- \+/\- *theorem* nat_trailing_degree_le_of_trailing_degree_le
- \+/\- *theorem* le_trailing_degree_C_mul_X_pow
- \+/\- *theorem* le_trailing_degree_X_pow
- \+/\- *theorem* nat_trailing_degree_le_of_trailing_degree_le
- \+/\- *theorem* le_trailing_degree_C_mul_X_pow
- \+/\- *theorem* le_trailing_degree_X_pow

modified src/data/polynomial/eval.lean

modified src/data/rat/basic.lean

modified src/data/rat/cast.lean
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs

modified src/data/rat/order.lean

modified src/data/real/basic.lean

modified src/data/real/cau_seq.lean
- \+/\- *def* is_cau_seq
- \+/\- *def* cau_seq
- \+/\- *def* is_cau_seq
- \+/\- *def* cau_seq

modified src/data/real/cau_seq_completion.lean

modified src/data/real/hyperreal.lean
- \+/\- *lemma* coe_abs
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_min
- \+/\- *lemma* coe_abs
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_min

modified src/data/real/nnreal.lean

modified src/data/set/finite.lean
- \+/\- *lemma* Union_Inter_of_monotone
- \+/\- *lemma* Union_Inter_of_monotone

modified src/data/set/intervals/basic.lean

modified src/data/set/intervals/disjoint.lean

modified src/data/set/intervals/ord_connected.lean

modified src/data/set/intervals/unordered_interval.lean

modified src/data/string/basic.lean

modified src/data/support.lean
- \+/\- *lemma* support_max
- \+/\- *lemma* support_min
- \+/\- *lemma* support_max
- \+/\- *lemma* support_min

modified src/data/zsqrtd/basic.lean

modified src/group_theory/archimedean.lean

modified src/group_theory/congruence.lean

modified src/group_theory/perm/cycles.lean
- \+/\- *def* cycle_factors
- \+/\- *def* cycle_factors

modified src/group_theory/perm/sign.lean
- \+/\- *def* swap_factors
- \+/\- *def* swap_factors

modified src/linear_algebra/affine_space/basic.lean
- \+/\- *lemma* image_interval
- \+/\- *lemma* image_interval

modified src/linear_algebra/finite_dimensional.lean

modified src/measure_theory/ae_eq_fun.lean

modified src/measure_theory/bochner_integration.lean

modified src/measure_theory/borel_space.lean

modified src/measure_theory/interval_integral.lean

modified src/order/basic.lean
- \- *def* decidable_linear_order.lift

modified src/order/bounded_lattice.lean
- \+/\- *theorem* coe_le_coe
- \+/\- *theorem* some_le_some
- \+/\- *theorem* lattice_eq_DLO
- \+/\- *theorem* sup_eq_max
- \+/\- *theorem* inf_eq_min
- \+/\- *theorem* lattice_eq_DLO
- \+/\- *theorem* sup_eq_max
- \+/\- *theorem* inf_eq_min
- \+/\- *theorem* coe_le_coe
- \+/\- *theorem* some_le_some
- \+/\- *theorem* lattice_eq_DLO
- \+/\- *theorem* sup_eq_max
- \+/\- *theorem* inf_eq_min
- \+/\- *theorem* lattice_eq_DLO
- \+/\- *theorem* sup_eq_max
- \+/\- *theorem* inf_eq_min

modified src/order/bounds.lean
- \+/\- *lemma* is_least.union
- \+/\- *lemma* is_greatest.union
- \+/\- *lemma* is_greatest.insert
- \+/\- *lemma* is_least.insert
- \+/\- *lemma* is_least_pair
- \+/\- *lemma* is_greatest_pair
- \+/\- *lemma* is_least.union
- \+/\- *lemma* is_greatest.union
- \+/\- *lemma* is_greatest.insert
- \+/\- *lemma* is_least.insert
- \+/\- *lemma* is_least_pair
- \+/\- *lemma* is_greatest_pair

modified src/order/category/NonemptyFinLinOrd.lean

modified src/order/complete_lattice.lean

modified src/order/conditionally_complete_lattice.lean

modified src/order/filter/at_top_bot.lean

modified src/order/filter/extr.lean

modified src/order/filter/filter_product.lean
- \+/\- *lemma* max_def
- \+/\- *lemma* min_def
- \+/\- *lemma* abs_def
- \+/\- *lemma* const_max
- \+/\- *lemma* const_min
- \+/\- *lemma* const_abs
- \+/\- *lemma* max_def
- \+/\- *lemma* min_def
- \+/\- *lemma* abs_def
- \+/\- *lemma* const_max
- \+/\- *lemma* const_min
- \+/\- *lemma* const_abs

modified src/order/lattice.lean
- \+/\- *theorem* sup_eq_max
- \+/\- *theorem* inf_eq_min
- \+/\- *theorem* sup_eq_max
- \+/\- *theorem* inf_eq_min

modified src/order/lexicographic.lean

modified src/order/pilex.lean

modified src/order/rel_classes.lean
- \+/\- *def* linear_order_of_STO'
- \+/\- *def* linear_order_of_STO'
- \- *def* decidable_linear_order_of_STO'

modified src/ring_theory/int/basic.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/valuation/basic.lean

modified src/set_theory/cardinal.lean

modified src/set_theory/cardinal_ordinal.lean

modified src/set_theory/ordinal.lean

modified src/set_theory/ordinal_notation.lean

modified src/set_theory/surreal.lean

modified src/tactic/interval_cases.lean

modified src/tactic/monotonicity/interactive.lean
- \+/\- *def* list.minimum_on
- \+/\- *def* list.minimum_on

modified src/testing/slim_check/sampleable.lean

modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* summable_abs_iff
- \+/\- *lemma* summable_abs_iff

modified src/topology/algebra/ordered.lean
- \+/\- *lemma* tendsto_abs_at_top_at_top
- \+ *lemma* linear_ordered_add_comm_group.tendsto_nhds
- \+/\- *lemma* tendsto_abs_at_top_at_top
- \- *lemma* decidable_linear_ordered_add_comm_group.tendsto_nhds

modified src/topology/algebra/polynomial.lean
- \+/\- *lemma* polynomial.tendsto_infinity
- \+/\- *lemma* polynomial.tendsto_infinity

modified src/topology/local_extr.lean

modified src/topology/uniform_space/absolute_value.lean

modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* cauchy_seq.mem_entourage
- \+/\- *lemma* cauchy_seq.mem_entourage

modified test/linarith.lean

modified test/monotonicity.lean



## [2020-10-27 01:56:15](https://github.com/leanprover-community/mathlib/commit/69db7a3)
chore(scripts): update nolints.txt ([#4797](https://github.com/leanprover-community/mathlib/pull/4797))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-26 23:04:21](https://github.com/leanprover-community/mathlib/commit/6e2980c)
chore(*): reflow some long lines ([#4794](https://github.com/leanprover-community/mathlib/pull/4794))
#### Estimated changes
modified archive/sensitivity.lean

modified src/algebra/algebra/basic.lean
- \+/\- *def* of_alg_hom
- \+/\- *def* of_alg_hom

modified src/algebra/algebra/operations.lean

modified src/algebra/archimedean.lean

modified src/algebra/associated.lean
- \+/\- *lemma* irreducible_of_prime
- \+/\- *lemma* prime_of_associated
- \+/\- *lemma* irreducible_of_prime
- \+/\- *lemma* prime_of_associated

modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* ring_hom.map_prod
- \+/\- *lemma* ring_hom.map_prod

modified src/algebra/big_operators/intervals.lean

modified src/algebra/big_operators/ring.lean
- \+/\- *lemma* prod_powerset_insert
- \+/\- *lemma* prod_powerset_insert

modified src/algebra/category/Algebra/basic.lean

modified src/algebra/category/CommRing/adjunctions.lean

modified src/algebra/char_p.lean
- \+/\- *lemma* char_p_of_prime_pow_injective
- \+/\- *lemma* char_p_of_prime_pow_injective

modified src/algebra/continued_fractions/computation/basic.lean

modified src/algebra/direct_limit.lean
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *lemma* of_add
- \+/\- *lemma* of_sub
- \+/\- *lemma* lift_add
- \+/\- *lemma* lift_sub
- \+/\- *lemma* of_pow
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *lemma* of_add
- \+/\- *lemma* of_sub
- \+/\- *lemma* lift_add
- \+/\- *lemma* lift_sub
- \+/\- *lemma* of_pow
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *theorem* induction_on
- \+/\- *theorem* induction_on

modified src/algebra/gcd_monoid.lean

modified src/algebra/geom_sum.lean
- \+/\- *lemma* op_geom_series
- \+/\- *lemma* op_geom_series

modified src/algebra/monoid_algebra.lean



## [2020-10-26 23:04:19](https://github.com/leanprover-community/mathlib/commit/8746f08)
feat(data/equiv/basic): equiv.set.powerset ([#4790](https://github.com/leanprover-community/mathlib/pull/4790))
#### Estimated changes
modified src/data/equiv/basic.lean



## [2020-10-26 21:30:45](https://github.com/leanprover-community/mathlib/commit/c76c3c5)
feat(degree/basic.lean): degree_lt_iff_coeff_zero ([#4792](https://github.com/leanprover-community/mathlib/pull/4792))
Changes to degree/basic.lean from [#4786](https://github.com/leanprover-community/mathlib/pull/4786)
#### Estimated changes
modified src/data/polynomial/degree/basic.lean
- \+ *theorem* degree_lt_iff_coeff_zero



## [2020-10-26 18:39:32](https://github.com/leanprover-community/mathlib/commit/95b3add)
fix(tactic/derive_fintype): add support for props ([#4777](https://github.com/leanprover-community/mathlib/pull/4777))
This adds support for propositional arguments in inductive constructors.
It was previously not handled, and while it *almost* works without
change, we have to use `Sigma' (a:A) (b:B) (c:C), unit` to tuple up the
arguments instead of `Sigma' (a:A) (b:B), C` because it would cause problems
in the unary case where there is only one propositional field.
#### Estimated changes
modified src/tactic/derive_fintype.lean

modified test/derive_fintype.lean



## [2020-10-26 18:39:30](https://github.com/leanprover-community/mathlib/commit/9428598)
feat(tactic/rcases): add `rintro (x y : t)` support ([#4722](https://github.com/leanprover-community/mathlib/pull/4722))
As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/rintros/near/213999254
#### Estimated changes
modified src/tactic/rcases.lean

modified test/rcases.lean



## [2020-10-26 18:39:29](https://github.com/leanprover-community/mathlib/commit/877a20e)
feat(ring_theory/finiteness): some finiteness notions in commutative algebra ([#4634](https://github.com/leanprover-community/mathlib/pull/4634))
#### Estimated changes
modified src/data/mv_polynomial/basic.lean

modified src/ring_theory/adjoin.lean

created src/ring_theory/finiteness.lean
- \+ *lemma* finite_def
- \+ *lemma* of_surjective
- \+ *lemma* of_injective
- \+ *lemma* equiv
- \+ *lemma* trans
- \+ *lemma* self
- \+ *lemma* of_surjective
- \+ *lemma* equiv
- \+ *lemma* trans
- \+ *lemma* id
- \+ *lemma* of_surjective
- \+ *lemma* comp
- \+ *lemma* finite_type
- \+ *lemma* id
- \+ *lemma* comp_surjective
- \+ *lemma* of_surjective
- \+ *lemma* comp
- \+ *lemma* id
- \+ *lemma* comp
- \+ *lemma* of_surjective
- \+ *lemma* finite_type
- \+ *lemma* id
- \+ *lemma* comp
- \+ *lemma* comp_surjective
- \+ *lemma* of_surjective
- \+ *def* module.finite
- \+ *def* algebra.finite_type
- \+ *def* finite
- \+ *def* finite_type
- \+ *def* finite
- \+ *def* finite_type



## [2020-10-26 18:39:27](https://github.com/leanprover-community/mathlib/commit/61c095f)
chore(algebra/module,linear_algebra): split off a `linear_map` file ([#4476](https://github.com/leanprover-community/mathlib/pull/4476))
In order to make `algebra/module/basic.lean` and `linear_algebra/basic.lean` a bit more manageable, move the basic facts about `linear_map`s and `linear_equiv`s into a separate file. `linear_algebra/basic.lean` still needs to be split a bit more.
#### Estimated changes
modified src/algebra/module/basic.lean
- \- *lemma* coe_mk
- \- *lemma* id_apply
- \- *lemma* id_coe
- \- *lemma* to_fun_eq_coe
- \- *lemma* map_add
- \- *lemma* map_smul
- \- *lemma* map_zero
- \- *lemma* to_add_monoid_hom_coe
- \- *lemma* map_sum
- \- *lemma* comp_apply
- \- *lemma* comp_coe
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *lemma* is_linear_map_smul
- \- *lemma* is_linear_map_smul'
- \- *lemma* map_zero
- \- *lemma* is_linear_map_neg
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *theorem* is_linear
- \- *theorem* coe_injective
- \- *theorem* ext
- \- *theorem* ext_iff
- \- *theorem* to_add_monoid_hom_injective
- \- *theorem* ext_ring
- \- *theorem* mk'_apply
- \- *def* id
- \- *def* to_add_monoid_hom
- \- *def* comp
- \- *def* mk'
- \- *def* add_monoid_hom.to_int_linear_map
- \- *def* add_monoid_hom.to_rat_linear_map

created src/algebra/module/linear_map.lean
- \+ *lemma* coe_mk
- \+ *lemma* id_apply
- \+ *lemma* id_coe
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* map_add
- \+ *lemma* map_smul
- \+ *lemma* map_zero
- \+ *lemma* to_add_monoid_hom_coe
- \+ *lemma* map_sum
- \+ *lemma* comp_apply
- \+ *lemma* comp_coe
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* is_linear_map_smul
- \+ *lemma* is_linear_map_smul'
- \+ *lemma* map_zero
- \+ *lemma* is_linear_map_neg
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* mk_apply
- \+ *lemma* injective_to_equiv
- \+ *lemma* to_equiv_inj
- \+ *lemma* injective_to_linear_map
- \+ *lemma* to_linear_map_inj
- \+ *lemma* coe_to_equiv
- \+ *lemma* to_fun_apply
- \+ *lemma* ext
- \+ *lemma* refl_apply
- \+ *lemma* inv_fun_apply
- \+ *lemma* coe_to_add_equiv
- \+ *lemma* symm_trans_apply
- \+ *lemma* trans_refl
- \+ *lemma* refl_trans
- \+ *lemma* symm_apply_eq
- \+ *lemma* eq_symm_apply
- \+ *lemma* trans_symm
- \+ *lemma* symm_trans
- \+ *lemma* refl_to_linear_map
- \+ *lemma* comp_coe
- \+ *lemma* map_sum
- \+ *theorem* is_linear
- \+ *theorem* coe_injective
- \+ *theorem* ext
- \+ *theorem* ext_iff
- \+ *theorem* to_add_monoid_hom_injective
- \+ *theorem* ext_ring
- \+ *theorem* mk'_apply
- \+ *theorem* coe_coe
- \+ *theorem* trans_apply
- \+ *theorem* apply_symm_apply
- \+ *theorem* symm_apply_apply
- \+ *theorem* map_add
- \+ *theorem* map_zero
- \+ *theorem* map_smul
- \+ *theorem* map_eq_zero_iff
- \+ *theorem* map_ne_zero_iff
- \+ *theorem* symm_symm
- \+ *def* id
- \+ *def* to_add_monoid_hom
- \+ *def* comp
- \+ *def* inverse
- \+ *def* mk'
- \+ *def* add_monoid_hom.to_int_linear_map
- \+ *def* add_monoid_hom.to_rat_linear_map
- \+ *def* to_equiv
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans

modified src/algebra/module/submodule.lean

modified src/data/dfinsupp.lean

modified src/data/finsupp/basic.lean

modified src/linear_algebra/basic.lean
- \- *lemma* mk_apply
- \- *lemma* injective_to_equiv
- \- *lemma* to_equiv_inj
- \- *lemma* injective_to_linear_map
- \- *lemma* to_linear_map_inj
- \- *lemma* coe_to_equiv
- \- *lemma* to_fun_apply
- \- *lemma* ext
- \- *lemma* refl_apply
- \- *lemma* inv_fun_apply
- \- *lemma* coe_to_add_equiv
- \- *lemma* symm_trans_apply
- \- *lemma* trans_refl
- \- *lemma* refl_trans
- \- *lemma* symm_apply_eq
- \- *lemma* eq_symm_apply
- \- *lemma* trans_symm
- \- *lemma* symm_trans
- \- *lemma* refl_to_linear_map
- \- *lemma* comp_coe
- \- *lemma* map_sum
- \- *theorem* coe_coe
- \- *theorem* trans_apply
- \- *theorem* apply_symm_apply
- \- *theorem* symm_apply_apply
- \- *theorem* map_add
- \- *theorem* map_zero
- \- *theorem* map_smul
- \- *theorem* map_eq_zero_iff
- \- *theorem* map_ne_zero_iff
- \- *theorem* symm_symm
- \- *def* inverse
- \- *def* to_equiv
- \- *def* refl
- \- *def* symm
- \- *def* trans



## [2020-10-26 16:13:21](https://github.com/leanprover-community/mathlib/commit/83edb50)
feat(simps): improve error messages ([#4653](https://github.com/leanprover-community/mathlib/pull/4653))
If a custom projection has a different type than the expected projection, then it will show a more specific error message.
Also reflow most long lines
Also add some tests
#### Estimated changes
modified src/tactic/simps.lean
- \- *lemma* {nm.append_suffix
- \- *lemma* {nm.append_suffix
- \- *lemma* {nm.append_suffix
- \- *lemma* {nm.append_suffix

modified test/simps.lean
- \- *lemma* specify.specify1_fst_fst.
- \- *lemma* specify.specify1_fst_fst.
- \- *lemma* specify.specify1_foo_fst.
- \- *lemma* specify.specify1_snd_bar.
- \- *lemma* specify.specify5_snd_snd.
- \- *lemma* specify.specify5_snd_snd.
- \+ *def* equiv.symm
- \+ *def* equiv.simps.inv_fun
- \+ *def* equiv.symm
- \+ *def* equiv.simps.inv_fun



## [2020-10-26 14:18:36](https://github.com/leanprover-community/mathlib/commit/ba5594a)
feat(data/dfinsupp): Add missing to_additive lemmas ([#4788](https://github.com/leanprover-community/mathlib/pull/4788))
#### Estimated changes
modified src/data/dfinsupp.lean
- \+ *lemma* prod_one
- \+ *lemma* prod_mul
- \+ *lemma* prod_inv
- \- *lemma* sum_zero
- \- *lemma* sum_add
- \- *lemma* sum_neg



## [2020-10-26 13:22:48](https://github.com/leanprover-community/mathlib/commit/2e90c60)
feat(ring_theory/witt_vector/basic): verifying the ring axioms ([#4694](https://github.com/leanprover-community/mathlib/pull/4694))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
created src/ring_theory/witt_vector/basic.lean
- \+ *lemma* injective
- \+ *lemma* surjective
- \+ *lemma* zero
- \+ *lemma* one
- \+ *lemma* add
- \+ *lemma* mul
- \+ *lemma* neg
- \+ *lemma* map_injective
- \+ *lemma* map_surjective
- \+ *lemma* map_coeff
- \+ *lemma* ghost_component_apply
- \+ *lemma* ghost_map_apply
- \+ *lemma* ghost_equiv_coe
- \+ *lemma* ghost_map.bijective_of_invertible
- \+ *def* map_fun
- \+ *def* map
- \+ *def* ghost_map
- \+ *def* ghost_component
- \+ *def* ghost_equiv



## [2020-10-26 05:21:12](https://github.com/leanprover-community/mathlib/commit/7be82f9)
chore(scripts): update nolints.txt ([#4785](https://github.com/leanprover-community/mathlib/pull/4785))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-26 05:21:10](https://github.com/leanprover-community/mathlib/commit/b2b39ed)
chore(order/galois_connection): define `with_bot.gi_get_or_else_bot` ([#4781](https://github.com/leanprover-community/mathlib/pull/4781))
This Galois insertion can be used to golf proofs about
`polynomial.degree` vs `polynomial.nat_degree`.
#### Estimated changes
modified src/data/option/basic.lean
- \+ *lemma* get_or_else_coe

modified src/order/bounded_lattice.lean
- \+ *lemma* get_or_else_bot
- \+ *lemma* get_or_else_bot_le_iff

modified src/order/galois_connection.lean
- \+ *def* with_bot.gi_get_or_else_bot



## [2020-10-26 05:21:08](https://github.com/leanprover-community/mathlib/commit/121c9a4)
chore(algebra/group/hom): use `coe_comp` in `simp` lemmas ([#4780](https://github.com/leanprover-community/mathlib/pull/4780))
This way Lean will simplify `⇑(f.comp g)` even if it is not applied to
an element.
#### Estimated changes
modified src/algebra/group/hom.lean
- \+ *lemma* one_hom.coe_comp
- \+ *lemma* mul_hom.coe_comp
- \+ *lemma* monoid_hom.coe_comp
- \+/\- *lemma* one_hom.comp_apply
- \+/\- *lemma* mul_hom.comp_apply
- \+/\- *lemma* monoid_hom.comp_apply
- \+/\- *lemma* one_hom.comp_apply
- \+/\- *lemma* mul_hom.comp_apply
- \+/\- *lemma* monoid_hom.comp_apply

modified src/algebra/ring/basic.lean
- \+ *lemma* coe_mul_right
- \+/\- *lemma* mul_right_apply
- \+/\- *lemma* mul_right_apply



## [2020-10-26 05:21:06](https://github.com/leanprover-community/mathlib/commit/6e4fe98)
chore(data/polynomial/{degree/basic, eval}): Some trivial lemmas about polynomials ([#4768](https://github.com/leanprover-community/mathlib/pull/4768))
I have added the lemma `supp_card_le_succ_nat_degree` about the cardinality of the support of a polynomial and removed the useless commutativity assumptio in `map_sum` and `map_neg`.
#### Estimated changes
modified src/data/polynomial/degree/basic.lean
- \+ *lemma* supp_subset_range_nat_degree_succ
- \+ *lemma* card_supp_le_succ_nat_degree

modified src/data/polynomial/eval.lean
- \+/\- *lemma* map_sum
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg
- \+ *lemma* map_int_cast
- \+/\- *lemma* map_sum
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg



## [2020-10-26 04:25:05](https://github.com/leanprover-community/mathlib/commit/4036212)
feat(algebra/big_operators/nat_antidiagonal): a few more lemmas ([#4783](https://github.com/leanprover-community/mathlib/pull/4783))
#### Estimated changes
modified src/algebra/big_operators/nat_antidiagonal.lean
- \+ *lemma* prod_antidiagonal_succ
- \+/\- *lemma* sum_antidiagonal_succ
- \+ *lemma* prod_antidiagonal_swap
- \+ *lemma* prod_antidiagonal_succ'
- \+ *lemma* sum_antidiagonal_succ'
- \+ *lemma* prod_antidiagonal_subst
- \+/\- *lemma* sum_antidiagonal_succ



## [2020-10-25 21:53:20](https://github.com/leanprover-community/mathlib/commit/a9d3ce8)
feat(analysis/normed_space/add_torsor): continuity of `vadd`/`vsub` ([#4751](https://github.com/leanprover-community/mathlib/pull/4751))
Prove that `vadd`/`vsub` are Lipschitz continuous, hence uniform
continuous and continuous.
#### Estimated changes
modified src/algebra/add_torsor.lean
- \+ *lemma* vadd_eq_vadd_iff_neg_add_eq_vsub
- \+ *lemma* vadd_eq_vadd_iff_sub_eq_vsub
- \+ *lemma* vsub_sub_vsub_comm

modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* dist_vsub_cancel_left
- \+ *lemma* dist_vsub_cancel_right
- \+ *lemma* dist_vadd_vadd_le
- \+ *lemma* dist_vsub_vsub_le
- \+ *lemma* nndist_vadd_vadd_le
- \+ *lemma* nndist_vsub_vsub_le
- \+ *lemma* edist_vadd_vadd_le
- \+ *lemma* edist_vsub_vsub_le
- \+ *lemma* lipschitz_with.vadd
- \+ *lemma* lipschitz_with.vsub
- \+ *lemma* uniform_continuous_vadd
- \+ *lemma* uniform_continuous_vsub
- \+ *lemma* continuous_vadd
- \+ *lemma* continuous_vsub
- \+ *lemma* filter.tendsto.vadd
- \+ *lemma* filter.tendsto.vsub
- \+ *lemma* continuous.vadd
- \+ *lemma* continuous.vsub
- \+ *lemma* continuous_at.vadd
- \+ *lemma* continuous_at.vsub
- \+ *lemma* continuous_within_at.vadd
- \+ *lemma* continuous_within_at.vsub
- \+/\- *def* metric_space_of_normed_group_of_add_torsor
- \+/\- *def* metric_space_of_normed_group_of_add_torsor

modified src/analysis/normed_space/basic.lean



## [2020-10-25 18:29:34](https://github.com/leanprover-community/mathlib/commit/e7a4b12)
fix(tactic/core): fix infinite loop in emit_code_here ([#4746](https://github.com/leanprover-community/mathlib/pull/4746))
Previously `emit_code_here "\n"` would go into an infinite loop because the `command_like` parser consumes nothing, but the string is not yet empty. Now we recurse on the length of the string to ensure termination.
#### Estimated changes
modified src/tactic/core.lean

modified test/run_parser.lean



## [2020-10-25 16:45:20](https://github.com/leanprover-community/mathlib/commit/151f0dd)
chore(linear_algebra/tensor_product): missing simp lemmas ([#4769](https://github.com/leanprover-community/mathlib/pull/4769))
#### Estimated changes
modified src/linear_algebra/tensor_product.lean
- \+ *lemma* lid_symm_apply
- \+ *lemma* rid_symm_apply
- \+ *lemma* map_comp
- \+ *lemma* lift_comp_map
- \+ *theorem* comm_symm_tmul
- \+ *theorem* assoc_symm_tmul
- \+ *theorem* congr_symm_tmul



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
modified src/ring_theory/discrete_valuation_ring.lean

modified src/ring_theory/polynomial/rational_root.lean

modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* wf_dvd_monoid.of_exists_prime_factors
- \+ *lemma* irreducible_iff_prime_of_exists_prime_factors
- \+ *lemma* no_factors_of_no_prime_factors
- \+ *lemma* dvd_of_dvd_mul_left_of_no_prime_factors
- \+ *lemma* dvd_of_dvd_mul_right_of_no_prime_factors
- \- *lemma* wf_dvd_monoid_of_exists_prime_of_factor
- \- *lemma* irreducible_iff_prime_of_exists_prime_of_factor
- \- *lemma* no_factors_of_no_prime_of_factor
- \- *lemma* dvd_of_dvd_mul_left_of_no_prime_of_factor
- \- *lemma* dvd_of_dvd_mul_right_of_no_prime_of_factor
- \+ *theorem* exists_prime_factors
- \+ *theorem* unique_factorization_monoid.of_exists_prime_factors
- \+ *theorem* unique_factorization_monoid.iff_exists_prime_factors
- \+ *theorem* irreducible_iff_prime_of_exists_unique_irreducible_factors
- \+ *theorem* unique_factorization_monoid.of_exists_unique_irreducible_factors
- \- *theorem* exists_prime_of_factor
- \- *theorem* unique_factorization_monoid_of_exists_prime_of_factor
- \- *theorem* unique_factorization_monoid_iff_exists_prime_of_factor
- \- *theorem* irreducible_iff_prime_of_exists_unique_irreducible_of_factor
- \- *theorem* unique_factorization_monoid.of_exists_unique_irreducible_of_factor



## [2020-10-25 14:56:50](https://github.com/leanprover-community/mathlib/commit/14cff9a)
chore(algebra/group/pi): add `pi.has_div` ([#4776](https://github.com/leanprover-community/mathlib/pull/4776))
Motivated by [#4646](https://github.com/leanprover-community/mathlib/pull/4646)
#### Estimated changes
modified src/algebra/group/pi.lean
- \+ *lemma* div_apply



## [2020-10-24 22:07:59](https://github.com/leanprover-community/mathlib/commit/f056468)
chore(analysis/normed_space): add 2 `@[simp]` attrs ([#4775](https://github.com/leanprover-community/mathlib/pull/4775))
Add `@[simp]` to `norm_pos_iff` and `norm_le_zero_iff`
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_pos_iff
- \+/\- *lemma* norm_le_zero_iff
- \+/\- *lemma* norm_pos_iff
- \+/\- *lemma* norm_le_zero_iff

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/normed_space/units.lean

modified src/data/padics/hensel.lean



## [2020-10-24 11:48:11](https://github.com/leanprover-community/mathlib/commit/cae77dc)
feat(algebra/direct_sum): Fix two todos about generalizing over unique types ([#4764](https://github.com/leanprover-community/mathlib/pull/4764))
Also promotes `id` to a `≃+`, and prefers coercion over direct use of `subtype.val`.
#### Estimated changes
modified src/algebra/direct_sum.lean

modified src/data/dfinsupp.lean
- \+ *lemma* single_injective

modified src/linear_algebra/direct_sum_module.lean



## [2020-10-24 05:36:36](https://github.com/leanprover-community/mathlib/commit/de6a9d4)
feat(ring_theory/polynomial/content): `gcd_monoid` instance on polynomials over gcd domain ([#4760](https://github.com/leanprover-community/mathlib/pull/4760))
Refactors `ring_theory/polynomial/content` a bit to introduce `prim_part`
Provides a `gcd_monoid` instance on polynomials over a gcd domain
#### Estimated changes
created src/data/polynomial/cancel_leads.lean
- \+ *lemma* neg_cancel_leads
- \+ *lemma* dvd_cancel_leads_of_dvd_of_dvd
- \+ *lemma* nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree
- \+ *def* cancel_leads

modified src/ring_theory/polynomial/content.lean
- \+ *lemma* eq_C_content_mul_prim_part
- \+ *lemma* prim_part_zero
- \+ *lemma* is_primitive_prim_part
- \+ *lemma* content_prim_part
- \+ *lemma* prim_part_ne_zero
- \+ *lemma* nat_degree_prim_part
- \+ *lemma* is_primitive.prim_part_eq
- \+ *lemma* is_unit_prim_part_C
- \+ *lemma* prim_part_dvd
- \+ *lemma* is_primitive.dvd_prim_part_iff_dvd
- \+ *lemma* dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part
- \- *lemma* eq_C_mul_primitive
- \+ *theorem* is_primitive.mul
- \+ *theorem* prim_part_mul
- \+ *theorem* exists_primitive_lcm_of_is_primitive
- \+ *def* prim_part



## [2020-10-24 05:36:34](https://github.com/leanprover-community/mathlib/commit/570c293)
feat(data/polynomial/ring_division): Two easy lemmas about polynomials ([#4742](https://github.com/leanprover-community/mathlib/pull/4742))
Two easy lemmas from my previous, now splitted, PR.
#### Estimated changes
modified src/data/polynomial/monic.lean
- \+ *lemma* monic_X_pow_sub_C

modified src/data/polynomial/ring_division.lean
- \+ *lemma* leading_coeff_div_by_monic_of_monic



## [2020-10-24 05:36:32](https://github.com/leanprover-community/mathlib/commit/b9a94d6)
feat(linear_algebra/nonsingular_inverse): add stronger form of Cramer's rule ([#4737](https://github.com/leanprover-community/mathlib/pull/4737))
Also renaming `cramer_transpose_eq_adjugate_mul_vec` --> `cramer_eq_adjugate_mul_vec` after the transpose was rendered redundant.
#### Estimated changes
modified docs/100.yaml

modified src/linear_algebra/nonsingular_inverse.lean
- \+ *lemma* cramer_eq_adjugate_mul_vec
- \+ *lemma* det_smul_inv_mul_vec_eq_cramer
- \+ *lemma* mul_vec_cramer
- \- *lemma* cramer_transpose_eq_adjugate_mul_vec
- \- *lemma* cramers_rule



## [2020-10-24 03:10:11](https://github.com/leanprover-community/mathlib/commit/2987a49)
fix(tactic/core): use eval_pexpr in run_parser_cmd ([#4761](https://github.com/leanprover-community/mathlib/pull/4761))
Continuation of [#4745](https://github.com/leanprover-community/mathlib/pull/4745), see https://github.com/leanprover-community/mathlib/pull/4745#discussion_r510771137
#### Estimated changes
modified src/tactic/core.lean



## [2020-10-24 01:02:28](https://github.com/leanprover-community/mathlib/commit/8255507)
feat(data/pnat/basic): Add strong induction on pnat ([#4736](https://github.com/leanprover-community/mathlib/pull/4736))
I added strong induction on `pnat`. (This was from a previous PR that I am splitting.)
#### Estimated changes
modified src/data/pnat/basic.lean
- \+ *lemma* strong_induction_on
- \+ *lemma* exists_eq_succ_of_ne_one
- \+ *lemma* case_strong_induction_on



## [2020-10-23 22:12:51](https://github.com/leanprover-community/mathlib/commit/c141eed)
feat(data/list/basic): Add prod_reverse_noncomm ([#4757](https://github.com/leanprover-community/mathlib/pull/4757))
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* prod_reverse_noncomm



## [2020-10-23 22:12:50](https://github.com/leanprover-community/mathlib/commit/4ec88db)
feat(algebra/direct_sum): Bundle the homomorphisms ([#4754](https://github.com/leanprover-community/mathlib/pull/4754))
#### Estimated changes
modified src/algebra/direct_sum.lean
- \- *lemma* mk_zero
- \- *lemma* mk_add
- \- *lemma* mk_neg
- \- *lemma* mk_sub
- \- *lemma* of_zero
- \- *lemma* of_add
- \- *lemma* of_neg
- \- *lemma* of_sub
- \- *lemma* to_group_zero
- \- *lemma* to_group_add
- \- *lemma* to_group_neg
- \- *lemma* to_group_sub
- \+/\- *def* mk
- \+/\- *def* of
- \+/\- *def* to_group
- \+/\- *def* mk
- \+/\- *def* of
- \+/\- *def* to_group

modified src/linear_algebra/direct_sum/finsupp.lean

modified src/linear_algebra/direct_sum_module.lean



## [2020-10-23 22:12:48](https://github.com/leanprover-community/mathlib/commit/aa59039)
feat(category_theory): presheaf is colimit of representables ([#4401](https://github.com/leanprover-community/mathlib/pull/4401))
Show every presheaf (on a small category) is a colimit of representables, and some related results. 
Suggestions for better names more than welcome.
#### Estimated changes
modified docs/references.bib

modified src/category_theory/adjunction/default.lean

modified src/category_theory/adjunction/opposites.lean
- \+ *def* nat_iso_of_left_adjoint_nat_iso
- \+ *def* nat_iso_of_right_adjoint_nat_iso

created src/category_theory/limits/presheaf.lean
- \+ *lemma* restrict_yoneda_hom_equiv_natural
- \+ *lemma* extend_along_yoneda_obj
- \+ *lemma* cocone_of_representable_X
- \+ *def* restricted_yoneda
- \+ *def* restricted_yoneda_yoneda
- \+ *def* restrict_yoneda_hom_equiv
- \+ *def* extend_along_yoneda
- \+ *def* yoneda_adjunction
- \+ *def* elements.initial
- \+ *def* is_initial
- \+ *def* is_extension_along_yoneda
- \+ *def* extend_along_yoneda_yoneda
- \+ *def* functor_to_representables
- \+ *def* cocone_of_representable
- \+ *def* colimit_of_representable

modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* terminal_op_of_initial
- \+ *def* terminal_unop_of_initial
- \+ *def* initial_op_of_terminal
- \+ *def* initial_unop_of_terminal



## [2020-10-23 20:04:40](https://github.com/leanprover-community/mathlib/commit/5afeb9b)
chore(*): a few more type-specific ext lemmas ([#4741](https://github.com/leanprover-community/mathlib/pull/4741))
* mark lemmas about homs from `multiplicative nat` and `multiplicative int` as `@[ext]`;
* add a special case lemma about linear maps from the base semiring;
* ext lemmas for ring homs from `(add_)monoid_algebra`;
* ext lemmas for multiplicative homs from `multiplicative (α →₀ M)`;
* make sure that Lean can chain ext lemmas by using hom equalities in lemmas about `finsupp`/`(add_)monoid_algebra`.
#### Estimated changes
modified src/algebra/group_power/lemmas.lean
- \+/\- *lemma* monoid_hom.ext_mnat
- \+/\- *lemma* monoid_hom.ext_mint
- \+/\- *lemma* monoid_hom.ext_mnat
- \+/\- *lemma* monoid_hom.ext_mint

modified src/algebra/module/basic.lean
- \+ *theorem* ext_ring

modified src/algebra/monoid_algebra.lean
- \+ *lemma* ring_hom_ext
- \+ *lemma* ring_hom_ext'
- \+/\- *lemma* alg_hom_ext
- \+ *lemma* alg_hom_ext'
- \+ *lemma* ring_hom_ext
- \+ *lemma* ring_hom_ext'
- \+/\- *lemma* alg_hom_ext
- \+ *lemma* alg_hom_ext'
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* alg_hom_ext

modified src/data/finsupp/basic.lean
- \+/\- *lemma* add_hom_ext
- \+ *lemma* add_hom_ext'
- \+ *lemma* mul_hom_ext
- \+ *lemma* mul_hom_ext'
- \+/\- *lemma* add_hom_ext
- \- *lemma* lhom_ext'
- \- *lemma* lhom_ext

modified src/data/mv_polynomial/basic.lean
- \+/\- *lemma* ring_hom_ext
- \+/\- *lemma* ring_hom_ext

modified src/linear_algebra/finsupp.lean
- \+ *lemma* lhom_ext
- \+ *lemma* lhom_ext'

modified src/linear_algebra/matrix.lean



## [2020-10-23 17:42:40](https://github.com/leanprover-community/mathlib/commit/0bbf3e2)
fix(deprecated/group): Correct the name of `is_add_group_hom has_neg.neg` ([#4755](https://github.com/leanprover-community/mathlib/pull/4755))
Rename `inv.is_add_group_hom` to `neg.is_add_group_hom`.
#### Estimated changes
modified src/deprecated/group.lean



## [2020-10-23 13:03:43](https://github.com/leanprover-community/mathlib/commit/5886961)
feat(data/{nat,list}/basic): Add some trivial lemmas ([#4738](https://github.com/leanprover-community/mathlib/pull/4738))
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* prod_inv_reverse
- \+ *lemma* prod_inv

modified src/data/nat/basic.lean



## [2020-10-23 10:15:32](https://github.com/leanprover-community/mathlib/commit/b651c6f)
feat(tactic/core): add `run_parser` user command ([#4745](https://github.com/leanprover-community/mathlib/pull/4745))
Allows for writing things like:
```lean
import tactic.core
run_parser emit_code_here "def foo := 1"
```
Relevant Zulip conversation: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/universes/near/214229509
#### Estimated changes
modified src/tactic/core.lean

created test/run_parser.lean



## [2020-10-23 10:15:30](https://github.com/leanprover-community/mathlib/commit/fb4aee0)
fix(deprecated/*): remove instances ([#4735](https://github.com/leanprover-community/mathlib/pull/4735))
Remove all instances constructing structures from `is_*` predicates, like for example:
```lean
instance subset.ring {S : set R} [is_subring S] : ring S :=
...
```
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *def* of_is_subring

modified src/algebra/group_action_hom.lean

modified src/algebra/group_ring_action.lean

modified src/deprecated/subfield.lean

modified src/deprecated/subgroup.lean
- \+ *def* subtype.group
- \+ *def* subtype.comm_group

modified src/deprecated/submonoid.lean
- \+ *def* subtype.monoid
- \+ *def* subtype.comm_monoid

modified src/deprecated/subring.lean
- \+ *def* subset.ring
- \+ *def* subtype.ring
- \+ *def* subset.comm_ring
- \+ *def* subtype.comm_ring
- \+ *def* subring.domain

modified src/ring_theory/adjoin.lean

modified src/ring_theory/algebra_tower.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/integral_domain.lean

modified src/ring_theory/noetherian.lean

modified src/ring_theory/polynomial/basic.lean

created test/import_order_timeout.lean
- \+ *lemma* injective_iff
- \+ *lemma* foo



## [2020-10-23 10:15:28](https://github.com/leanprover-community/mathlib/commit/70b14ce)
refactor(*): use is_scalar_tower instead of restrict_scalars ([#4733](https://github.com/leanprover-community/mathlib/pull/4733))
- rename `semimodule.restrict_scalars` to `restrict_scalars`
- rename `restrict_scalars` to `subspace.restrict_scalars`
- use `is_scalar_tower` wherever possible
- add warnings to docstrings about `restrict_scalars` to encourage `is_scalar_tower` instead
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra_map_smul
- \+ *lemma* coe_restrict_scalars_eq_coe
- \+ *lemma* coe_coe_is_scalar_tower
- \+ *lemma* algebra_module.smul_apply
- \+ *lemma* restrict_scalars_smul_def
- \+ *lemma* restrict_scalars_mem
- \+ *lemma* restrict_scalars_injective
- \+ *lemma* restrict_scalars_inj
- \+ *lemma* restrict_scalars_bot
- \+ *lemma* restrict_scalars_top
- \+ *lemma* linear_map.ker_restrict_scalars
- \+ *lemma* smul_apply'
- \- *lemma* semimodule.restrict_scalars_smul_def
- \- *lemma* algebra.restrict_scalars_equiv_apply
- \- *lemma* algebra.restrict_scalars_equiv_symm_apply
- \- *lemma* submodule.restrict_scalars_mem
- \- *lemma* submodule.restrict_scalars_bot
- \- *lemma* submodule.restrict_scalars_top
- \- *lemma* linear_map.coe_restrict_scalars_eq_coe
- \- *lemma* restrict_scalars_ker
- \- *lemma* linear_map_algebra_module.smul_apply
- \+/\- *theorem* smul_algebra_right_apply
- \+/\- *theorem* smul_algebra_right_apply
- \+ *def* restrict_scalars
- \+ *def* lto_fun
- \+ *def* restrict_scalars
- \+ *def* restrict_scalars
- \+/\- *def* smul_algebra_right
- \- *def* semimodule.restrict_scalars'
- \- *def* semimodule.restrict_scalars
- \- *def* algebra.restrict_scalars_equiv
- \- *def* submodule.restrict_scalars
- \- *def* linear_map.restrict_scalars
- \- *def* linear_map.lto_fun
- \+/\- *def* smul_algebra_right
- \- *def* linear_map_algebra_has_scalar
- \- *def* linear_map_algebra_module

modified src/algebra/monoid_algebra.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/complex/basic.lean

modified src/analysis/normed_space/basic.lean
- \+ *def* normed_space.restrict_scalars
- \- *def* normed_space.restrict_scalars'

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/analysis/normed_space/hahn_banach.lean

modified src/analysis/normed_space/inner_product.lean

modified src/analysis/normed_space/operator_norm.lean
- \+/\- *theorem* smul_algebra_right_apply
- \+/\- *theorem* smul_algebra_right_apply
- \+/\- *def* smul_algebra_right
- \+/\- *def* smul_algebra_right

modified src/data/complex/is_R_or_C.lean

modified src/data/complex/module.lean

modified src/field_theory/tower.lean

modified src/representation_theory/maschke.lean
- \+/\- *lemma* equivariant_projection_condition
- \+/\- *lemma* equivariant_projection_condition
- \+/\- *def* conjugate
- \+/\- *def* sum_of_conjugates
- \+/\- *def* sum_of_conjugates_equivariant
- \+/\- *def* equivariant_projection
- \+/\- *def* conjugate
- \+/\- *def* sum_of_conjugates
- \+/\- *def* sum_of_conjugates_equivariant
- \+/\- *def* equivariant_projection

modified src/ring_theory/algebra_tower.lean
- \- *theorem* restrict_scalars'_top
- \- *theorem* restrict_scalars'_injective
- \- *theorem* restrict_scalars'_inj
- \- *def* restrict_scalars'



## [2020-10-23 10:15:26](https://github.com/leanprover-community/mathlib/commit/82b4843)
feat(ring_theory/roots_of_unity): Roots of unity as union of primitive roots ([#4644](https://github.com/leanprover-community/mathlib/pull/4644))
I have added some lemmas about roots of unity, especially `root_of_unity_eq_uniun_prim` that says that, if there is a primitive `n`-th root of unity in `R`, then the set of `n`-th roots of unity is equal to the union of `primitive_roots i R` for `i | n`.
I will use this lemma in to develop the theory of cyclotomic polynomials.
#### Estimated changes
modified src/data/pnat/basic.lean
- \+ *lemma* pos_of_div_pos

modified src/data/polynomial/ring_division.lean
- \+ *lemma* mem_nth_roots_finset
- \+ *def* nth_roots_finset

modified src/number_theory/divisors.lean
- \+ *lemma* filter_dvd_eq_divisors

modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* card_nth_roots
- \+ *lemma* nth_roots_nodup
- \+ *lemma* card_nth_roots_finset
- \+ *lemma* disjoint
- \+ *lemma* pow
- \+ *lemma* nth_roots_one_eq_bind_primitive_roots



## [2020-10-23 10:15:24](https://github.com/leanprover-community/mathlib/commit/278a14b)
feat(analysis/p_series): prove the p-series convergence test ([#4360](https://github.com/leanprover-community/mathlib/pull/4360))
#### Estimated changes
modified docs/100.yaml

created src/analysis/p_series.lean
- \+ *lemma* le_sum_condensed'
- \+ *lemma* le_sum_condensed
- \+ *lemma* sum_condensed_le'
- \+ *lemma* sum_condensed_le
- \+ *lemma* le_tsum_condensed
- \+ *lemma* tsum_condensed_le
- \+ *lemma* summable_condensed_iff
- \+ *lemma* summable_condensed_iff_of_nonneg
- \+ *lemma* real.summable_nat_rpow_inv
- \+ *lemma* real.summable_one_div_nat_rpow
- \+ *lemma* real.summable_nat_pow_inv
- \+ *lemma* real.summable_one_div_nat_pow
- \+ *lemma* real.not_summable_nat_cast_inv
- \+ *lemma* real.not_summable_one_div_nat_cast
- \+ *lemma* real.tendsto_sum_range_one_div_nat_succ_at_top
- \+ *lemma* nnreal.summable_one_rpow_inv
- \+ *lemma* nnreal.summable_one_div_rpow

modified src/analysis/specific_limits.lean
- \- *lemma* mono_harmonic
- \- *lemma* half_le_harmonic_double_sub_harmonic
- \- *lemma* self_div_two_le_harmonic_two_pow
- \- *theorem* harmonic_tendsto_at_top
- \- *def* harmonic_series

modified src/order/filter/cofinite.lean
- \+ *lemma* filter.eventually_cofinite_ne



## [2020-10-23 10:15:21](https://github.com/leanprover-community/mathlib/commit/04b5572)
feat(ring_theory/witt_vector/defs): type of witt vectors + ring operations ([#4332](https://github.com/leanprover-community/mathlib/pull/4332))
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
modified src/ring_theory/witt_vector/defs.lean
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* coeff_mk
- \+ *lemma* zero_coeff
- \+ *lemma* one_coeff_zero
- \+ *lemma* one_coeff_eq_of_pos
- \+ *lemma* add_coeff
- \+ *lemma* mul_coeff
- \+ *lemma* neg_coeff
- \+ *def* witt_vector
- \+ *def* mk
- \+ *def* coeff
- \+ *def* peval
- \+ *def* eval



## [2020-10-23 07:42:45](https://github.com/leanprover-community/mathlib/commit/9e4ef85)
feat(linear_algebra/affine_space): define `affine_equiv.mk'` ([#4750](https://github.com/leanprover-community/mathlib/pull/4750))
Similarly to `affine_map.mk'`, this constructor checks that the map
agrees with its linear part only for one base point.
#### Estimated changes
modified src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* coe_mk'
- \+ *lemma* to_equiv_mk'
- \+ *lemma* linear_mk'
- \+ *def* mk'



## [2020-10-23 07:42:43](https://github.com/leanprover-community/mathlib/commit/468c01c)
chore(topology/*): add two missing simp coe lemmas ([#4748](https://github.com/leanprover-community/mathlib/pull/4748))
#### Estimated changes
modified src/topology/algebra/module.lean
- \+ *lemma* coe_to_linear_equiv

modified src/topology/metric_space/isometry.lean
- \+ *lemma* coe_to_equiv



## [2020-10-23 07:42:40](https://github.com/leanprover-community/mathlib/commit/458c833)
chore(algebra/group/basic): Mark inv_involutive simp ([#4744](https://github.com/leanprover-community/mathlib/pull/4744))
This means expressions like `has_inv.inv ∘ has_inv.inv` can be simplified
#### Estimated changes
modified src/algebra/group/basic.lean



## [2020-10-23 05:47:36](https://github.com/leanprover-community/mathlib/commit/bb52355)
feat(linear_algebra/basic): define `linear_equiv.neg` ([#4749](https://github.com/leanprover-community/mathlib/pull/4749))
Also weaken requirements for `has_neg (M →ₗ[R] M₂)` from
`[add_comm_group M]` `[add_comm_group M₂]` to `[add_comm_monoid M]`
`[add_comm_group M₂]`.
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *lemma* coe_neg
- \+ *lemma* neg_apply
- \+ *lemma* symm_neg
- \+ *def* neg



## [2020-10-23 05:47:34](https://github.com/leanprover-community/mathlib/commit/dc4ad81)
refactor(*): lmul is an algebra hom ([#4724](https://github.com/leanprover-community/mathlib/pull/4724))
also, make some arguments implicit, and add simp lemmas
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+/\- *lemma* algebra_map_End_eq_smul_id
- \+/\- *lemma* algebra_map_End_apply
- \+/\- *lemma* ker_algebra_map_End
- \+/\- *lemma* lmul_apply
- \+/\- *lemma* lmul_left_apply
- \+/\- *lemma* lmul_right_apply
- \+/\- *lemma* lmul_left_right_apply
- \+ *lemma* lmul_left_one
- \+ *lemma* lmul_left_mul
- \+ *lemma* lmul_right_one
- \+ *lemma* lmul_right_mul
- \+/\- *lemma* lmul'_apply
- \+/\- *lemma* lmul_apply
- \+/\- *lemma* lmul_left_apply
- \+/\- *lemma* lmul_right_apply
- \+/\- *lemma* lmul_left_right_apply
- \+/\- *lemma* lmul'_apply
- \+/\- *lemma* algebra_map_End_eq_smul_id
- \+/\- *lemma* algebra_map_End_apply
- \+/\- *lemma* ker_algebra_map_End
- \+/\- *def* lmul
- \+/\- *def* lmul_left
- \+/\- *def* lmul_right
- \+/\- *def* lmul_left_right
- \+/\- *def* lmul'
- \+/\- *def* lmul
- \+/\- *def* lmul_left
- \+/\- *def* lmul_right
- \+/\- *def* lmul_left_right
- \+/\- *def* lmul'

modified src/algebra/algebra/operations.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/category_theory/monoidal/internal/Module.lean

modified src/linear_algebra/basic.lean
- \+/\- *lemma* mul_apply
- \+/\- *lemma* mul_apply

modified src/linear_algebra/finite_dimensional.lean



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
modified src/measure_theory/measure_space.lean
- \+ *lemma* restrict_to_outer_measure_eq_to_outer_measure_restrict
- \+ *lemma* restrict_Inf_eq_Inf_restrict
- \+/\- *lemma* measure.le_of_add_le_add_left
- \+/\- *lemma* measure.le_of_add_le_add_left

modified src/measure_theory/outer_measure.lean
- \+ *lemma* of_function_apply
- \+/\- *lemma* Inf_gen_nonempty2
- \+ *lemma* Inf_apply
- \+ *lemma* restrict_Inf_eq_Inf_restrict
- \+ *lemma* restrict_trim
- \+/\- *lemma* Inf_gen_nonempty2



## [2020-10-23 04:31:09](https://github.com/leanprover-community/mathlib/commit/f279313)
feat(category_theory/yoneda): better simp lemmas for small yoneda ([#4743](https://github.com/leanprover-community/mathlib/pull/4743))
Gives nicer (d)simp lemmas for yoneda_sections_small.
#### Estimated changes
modified src/category_theory/yoneda.lean
- \+ *lemma* yoneda_sections_small_hom
- \+ *lemma* yoneda_sections_small_inv_app_apply
- \+/\- *def* yoneda_sections_small
- \+/\- *def* yoneda_sections_small



## [2020-10-23 01:10:33](https://github.com/leanprover-community/mathlib/commit/8bd1df5)
chore(scripts): update nolints.txt ([#4747](https://github.com/leanprover-community/mathlib/pull/4747))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-22 17:33:36](https://github.com/leanprover-community/mathlib/commit/de12036)
chore(data/polynomial): remove monomial_one_eq_X_pow ([#4734](https://github.com/leanprover-community/mathlib/pull/4734))
monomial_one_eq_X_pow was a duplicate of X_pow_eq_monomial
#### Estimated changes
modified src/data/polynomial/coeff.lean

modified src/data/polynomial/eval.lean

modified src/data/polynomial/monomial.lean
- \- *lemma* monomial_one_eq_X_pow

modified src/ring_theory/polynomial_algebra.lean



## [2020-10-22 14:57:55](https://github.com/leanprover-community/mathlib/commit/6eb5564)
chore(data/equiv/basic): Add a simp lemma perm.coe_mul ([#4723](https://github.com/leanprover-community/mathlib/pull/4723))
This mirrors `equiv.coe_trans`
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* coe_mul
- \+/\- *theorem* mul_apply
- \+/\- *theorem* mul_apply



## [2020-10-22 07:48:25](https://github.com/leanprover-community/mathlib/commit/add5096)
chore(*): 3 unrelated small changes ([#4732](https://github.com/leanprover-community/mathlib/pull/4732))
* fix universe levels in `equiv.set.compl`: by default Lean uses some
`max` universes both for `α` and `β`, and it backfires when one tries
to apply it.
* add `nat.mul_factorial_pred`;
* add instance `fixed_points.decidable`.
Part of [#4731](https://github.com/leanprover-community/mathlib/pull/4731)
#### Estimated changes
modified src/data/equiv/basic.lean

modified src/data/nat/factorial.lean
- \+ *theorem* mul_factorial_pred

modified src/dynamics/fixed_points/basic.lean



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
modified src/algebra/algebra/basic.lean

modified src/algebra/category/CommRing/adjunctions.lean

modified src/algebra/monoid_algebra.lean
- \+ *lemma* lift_nc_single
- \+ *lemma* lift_nc_one
- \+ *lemma* lift_nc_mul
- \+/\- *lemma* alg_hom_ext
- \+ *lemma* lift_apply'
- \+ *lemma* lift_def
- \+ *lemma* lift_nc_single
- \+ *lemma* lift_nc_one
- \+ *lemma* lift_nc_mul
- \+/\- *lemma* of_apply
- \+/\- *lemma* alg_hom_ext
- \+ *lemma* lift_apply'
- \+ *lemma* lift_apply
- \+ *lemma* lift_def
- \+ *lemma* lift_symm_apply
- \+ *lemma* lift_of
- \+ *lemma* lift_single
- \+ *lemma* lift_unique'
- \+ *lemma* lift_unique
- \+/\- *lemma* alg_hom_ext_iff
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* of_apply
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* alg_hom_ext_iff
- \+ *def* lift_nc
- \+ *def* lift_nc
- \+/\- *def* lift
- \+/\- *def* lift

modified src/data/finsupp/basic.lean
- \+ *lemma* sum_add_index'
- \+ *lemma* prod_add_index'
- \+ *lemma* lift_add_hom_apply_single
- \+ *lemma* lift_add_hom_comp_single
- \+ *lemma* comp_lift_add_hom

modified src/data/mv_polynomial/basic.lean
- \+ *lemma* single_eq_monomial
- \+/\- *lemma* ring_hom_ext
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* ring_hom_ext
- \+/\- *lemma* alg_hom_ext
- \+ *theorem* aeval_unique
- \- *theorem* eval_unique

modified src/data/mv_polynomial/comap.lean

modified src/data/mv_polynomial/monad.lean
- \+/\- *lemma* bind₂_C_left
- \+/\- *lemma* bind₂_comp_bind₂
- \+ *lemma* rename_comp_bind₁
- \+ *lemma* bind₁_comp_rename
- \+/\- *lemma* eval₂_hom_bind₂
- \+/\- *lemma* bind₂_C_left
- \+/\- *lemma* bind₂_comp_bind₂
- \+/\- *lemma* eval₂_hom_bind₂



## [2020-10-22 07:48:21](https://github.com/leanprover-community/mathlib/commit/fb5ef2b)
feat(linear_algebra/nonsingular_inverse): state Cramer's rule explicitly ([#4700](https://github.com/leanprover-community/mathlib/pull/4700))
Mostly so that we can add an entry to the Freek 100.
#### Estimated changes
modified docs/100.yaml

modified src/data/matrix/basic.lean
- \+ *lemma* smul_mul_vec_assoc

modified src/linear_algebra/determinant.lean
- \+ *lemma* det_eq_zero_of_row_eq_zero
- \+/\- *lemma* det_eq_zero_of_column_eq_zero
- \+/\- *lemma* det_eq_zero_of_column_eq_zero
- \+ *theorem* det_zero_of_row_eq
- \- *theorem* det_zero_of_column_eq

modified src/linear_algebra/nonsingular_inverse.lean
- \+/\- *lemma* cramer_apply
- \+ *lemma* cramer_transpose_row_self
- \+ *lemma* cramer_transpose_eq_adjugate_mul_vec
- \+ *lemma* cramers_rule
- \+/\- *lemma* cramer_apply
- \- *lemma* cramer_column_self
- \+/\- *def* cramer_map
- \+/\- *def* cramer
- \+/\- *def* adjugate
- \+/\- *def* cramer_map
- \+/\- *def* cramer
- \+/\- *def* adjugate



## [2020-10-22 06:38:42](https://github.com/leanprover-community/mathlib/commit/03f0285)
refactor(algebra/add_torsor): define pointwise `-ᵥ` and `+ᵥ` on sets ([#4710](https://github.com/leanprover-community/mathlib/pull/4710))
This seems more natural than `vsub_set` to me.
#### Estimated changes
modified src/algebra/add_torsor.lean
- \+ *lemma* vsub_empty
- \+ *lemma* empty_vsub
- \+ *lemma* singleton_vsub
- \+ *lemma* vsub_singleton
- \+ *lemma* singleton_vsub_self
- \+ *lemma* finite.vsub
- \+ *lemma* vsub_mem_vsub
- \+ *lemma* vsub_subset_vsub
- \+ *lemma* vsub_self_mono
- \+ *lemma* vsub_subset_iff
- \+ *lemma* vadd_subset_vadd
- \+ *lemma* vadd_singleton
- \+ *lemma* singleton_vadd
- \+ *lemma* finite.vadd
- \- *lemma* vsub_set_empty
- \- *lemma* vsub_set_singleton
- \- *lemma* vsub_set_finite_of_finite
- \- *lemma* vsub_mem_vsub_set
- \- *lemma* vsub_set_mono
- \- *def* vsub_set

modified src/geometry/euclidean/monge_point.lean

modified src/linear_algebra/affine_space/basic.lean
- \+/\- *lemma* vector_span_def
- \+/\- *lemma* vsub_set_subset_vector_span
- \+/\- *lemma* vector_span_def
- \+/\- *lemma* vsub_set_subset_vector_span
- \+/\- *def* vector_span
- \+/\- *def* vector_span

modified src/linear_algebra/affine_space/finite_dimensional.lean



## [2020-10-22 05:15:46](https://github.com/leanprover-community/mathlib/commit/4c4d47c)
feat(algebra/gcd_monoid): noncomputably defines `gcd_monoid` structures from partial information ([#4664](https://github.com/leanprover-community/mathlib/pull/4664))
Adds the following 4 noncomputable functions which define `gcd_monoid` instances.
`gcd_monoid_of_gcd` takes as input a `gcd` function and a few of its properties
`gcd_monoid_of_lcm` takes as input a `lcm` function and a few of its properties
`gcd_monoid_of_exists_gcd` takes as input the prop that every two elements have a `gcd`
`gcd_monoid_of_exists_lcm` takes as input the prop that every two elements have an `lcm`
#### Estimated changes
modified src/algebra/gcd_monoid.lean



## [2020-10-22 01:14:08](https://github.com/leanprover-community/mathlib/commit/fca876e)
chore(scripts): update nolints.txt ([#4730](https://github.com/leanprover-community/mathlib/pull/4730))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-21 15:31:43](https://github.com/leanprover-community/mathlib/commit/df45002)
feat(archive): formalize compiler correctness by McCarthy and Painter ([#4702](https://github.com/leanprover-community/mathlib/pull/4702))
Add a formalization of the correctness of a compiler from arithmetic expressions to machine language described by McCarthy and Painter, which is considered the first proof of compiler correctness.
#### Estimated changes
created archive/arithcc.lean
- \+ *lemma* register.lt_succ_self
- \+ *lemma* register.le_of_lt_succ
- \+ *lemma* outcome_append
- \+ *lemma* state_eq_implies_write_eq
- \+ *lemma* state_eq_rs_implies_write_eq_rs
- \+ *lemma* write_eq_implies_state_eq
- \+ *theorem* compiler_correctness
- \+ *def* word
- \+ *def* identifier
- \+ *def* register
- \+ *def* value
- \+ *def* read
- \+ *def* write
- \+ *def* step
- \+ *def* outcome
- \+ *def* loc
- \+ *def* compile
- \+ *def* state_eq_rs
- \+ *def* state_eq



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
modified src/algebra/add_torsor.lean
- \+/\- *lemma* coe_vadd_const
- \+/\- *lemma* coe_vadd_const_symm
- \+/\- *lemma* coe_vadd_const
- \+/\- *lemma* coe_vadd_const_symm

modified src/analysis/normed_space/add_torsor.lean
- \+/\- *lemma* vadd_const_to_equiv
- \+/\- *lemma* vadd_const_to_equiv

created src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* coe_to_affine_equiv
- \+ *lemma* coe_refl
- \+ *lemma* refl_apply
- \+ *lemma* to_equiv_refl
- \+ *lemma* linear_refl
- \+ *lemma* map_vadd
- \+ *lemma* coe_to_equiv
- \+ *lemma* coe_to_affine_map
- \+ *lemma* to_affine_map_mk
- \+ *lemma* linear_to_affine_map
- \+ *lemma* injective_to_affine_map
- \+ *lemma* to_affine_map_inj
- \+ *lemma* ext
- \+ *lemma* injective_coe_fn
- \+ *lemma* coe_fn_inj
- \+ *lemma* injective_to_equiv
- \+ *lemma* to_equiv_inj
- \+ *lemma* symm_to_equiv
- \+ *lemma* symm_linear
- \+ *lemma* range_eq
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* apply_eq_iff_eq_symm_apply
- \+ *lemma* apply_eq_iff_eq
- \+ *lemma* symm_refl
- \+ *lemma* coe_trans
- \+ *lemma* trans_apply
- \+ *lemma* trans_assoc
- \+ *lemma* trans_refl
- \+ *lemma* refl_trans
- \+ *lemma* trans_symm
- \+ *lemma* symm_trans
- \+ *lemma* one_def
- \+ *lemma* coe_one
- \+ *lemma* mul_def
- \+ *lemma* coe_mul
- \+ *lemma* inv_def
- \+ *lemma* linear_vadd_const
- \+ *lemma* vadd_const_apply
- \+ *lemma* vadd_const_symm_apply
- \+ *lemma* linear_const_vadd
- \+ *lemma* const_vadd_apply
- \+ *lemma* const_vadd_symm_apply
- \+ *def* to_affine_equiv
- \+ *def* refl
- \+ *def* to_affine_map
- \+ *def* symm
- \+ *def* trans
- \+ *def* vadd_const
- \+ *def* const_vadd



## [2020-10-21 13:35:00](https://github.com/leanprover-community/mathlib/commit/75316ca)
chore(linear_algebra/basic): a few simp lemmas ([#4727](https://github.com/leanprover-community/mathlib/pull/4727))
* add `submodule.nonempty`;
* add `@[simp]` to `submodule.map_id`;
* add `submodule.neg_coe`, `protected submodule.map_neg`, and `submodule.span_neg`.
#### Estimated changes
modified src/algebra/module/submodule.lean

modified src/linear_algebra/basic.lean
- \+/\- *lemma* map_id
- \+ *lemma* neg_coe
- \+ *lemma* span_neg
- \+/\- *lemma* map_id



## [2020-10-21 01:39:35](https://github.com/leanprover-community/mathlib/commit/01c1e6f)
chore(scripts): update nolints.txt ([#4721](https://github.com/leanprover-community/mathlib/pull/4721))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-21 01:39:33](https://github.com/leanprover-community/mathlib/commit/3a860cc)
fixup(category_theory/sites): add arrow sets that aren't sieves  ([#4703](https://github.com/leanprover-community/mathlib/pull/4703))
Broken off from [#4648](https://github.com/leanprover-community/mathlib/pull/4648).
- I realised that by creating a type `arrows_with_codomain` I can avoid using `set (over X)` entirely (the bit I was missing was that `derive complete_lattice` works on the new type even though it wasn't inferred on the pi-type), so I changed sieves to use that instead. 
- I added constructors for special arrow sets. The definitions of `singleton_arrow` and `pullback_arrows` look a bit dubious because of the equality and `eq_to_hom` stuff; I don't love that either so if there's a suggestion on how to achieve the same things (in particular stating (1) and (3) from: https://stacks.math.columbia.edu/tag/00VH, as well as a complete lattice structure) I'd be happy to consider.
- I added a coercion so we can write `S f` instead of `S.arrows f` for sieves.
#### Estimated changes
modified src/category_theory/sites/grothendieck.lean
- \+ *lemma* ext
- \+ *lemma* bind_covering
- \+/\- *lemma* arrow_max
- \+/\- *lemma* dense_covering
- \+/\- *lemma* arrow_max
- \+/\- *lemma* dense_covering

modified src/category_theory/sites/sieves.lean
- \+ *lemma* bind_comp
- \+ *lemma* singleton_arrow_eq_iff_domain
- \+ *lemma* singleton_arrow_self
- \+ *lemma* downward_closed
- \+/\- *lemma* mem_top
- \+ *lemma* mem_generate
- \+/\- *lemma* sets_iff_generate
- \+/\- *lemma* id_mem_iff_eq_top
- \+/\- *lemma* pullback_eq_top_iff_mem
- \+/\- *lemma* pullback_eq_top_of_mem
- \+/\- *lemma* mem_pushforward_of_comp
- \+ *lemma* pushforward_le_bind_of_mem
- \+ *lemma* le_pullback_bind
- \+/\- *lemma* mem_top
- \+/\- *lemma* sets_iff_generate
- \+/\- *lemma* id_mem_iff_eq_top
- \+/\- *lemma* pullback_eq_top_iff_mem
- \+/\- *lemma* pullback_eq_top_of_mem
- \+/\- *lemma* mem_pushforward_of_comp
- \+ *def* arrows_with_codomain
- \+ *def* bind
- \+ *def* singleton_arrow
- \+/\- *def* generate
- \+ *def* bind
- \+/\- *def* gi_generate
- \- *def* set_over
- \+/\- *def* generate
- \+/\- *def* gi_generate



## [2020-10-21 00:42:57](https://github.com/leanprover-community/mathlib/commit/857cbd5)
chore(category_theory/limits/preserves): split up files and remove redundant defs ([#4717](https://github.com/leanprover-community/mathlib/pull/4717))
Broken off from [#4163](https://github.com/leanprover-community/mathlib/pull/4163) and [#4716](https://github.com/leanprover-community/mathlib/pull/4716).
While the diff of this PR is quite big, it actually doesn't do very much: 
- I removed the definitions of `preserves_(co)limits_iso` from `preserves/basic`, since there's already a version in `preserves/shapes` which has lemmas about it. (I didn't keep them in `preserves/basic` since that file is already getting quite big, so I chose to instead put them into the smaller file.
- I split up `preserves/shapes` into two files: `preserves/limits` and `preserves/shapes`. From my other PRs my plan is for `shapes` to contain isomorphisms and constructions for special shapes, eg `fan.mk` and `fork`s, some of which aren't already present, and `limits` to have things for the general case. In this PR I don't change the situation for special shapes (other than simplifying some proofs), other than moving it into a separate file for clarity.
#### Estimated changes
modified src/algebraic_geometry/presheafed_space/has_colimits.lean

modified src/category_theory/limits/functor_category.lean

modified src/category_theory/limits/preserves/basic.lean
- \- *def* preserves_limit_iso
- \- *def* preserves_colimit_iso

created src/category_theory/limits/preserves/limits.lean
- \+ *lemma* preserves_lift_map_cone
- \+ *lemma* preserves_limits_iso_hom_π
- \+ *lemma* preserves_limits_iso_inv_π
- \+ *lemma* lift_comp_preserves_limits_iso_hom
- \+ *lemma* preserves_desc_map_cocone
- \+ *lemma* ι_preserves_colimits_iso_inv
- \+ *lemma* ι_preserves_colimits_iso_hom
- \+ *lemma* preserves_colimits_iso_inv_comp_desc
- \+ *def* preserves_limit_iso
- \+ *def* preserves_colimit_iso

modified src/category_theory/limits/preserves/shapes.lean
- \- *lemma* preserves_limits_iso_hom_π
- \- *def* preserves_limits_iso



## [2020-10-20 13:15:11](https://github.com/leanprover-community/mathlib/commit/8489972)
feat(data/complex/module): ![1, I] is a basis of C over R ([#4713](https://github.com/leanprover-community/mathlib/pull/4713))
#### Estimated changes
modified src/data/complex/module.lean
- \+ *lemma* coe_algebra_map
- \+ *lemma* re_smul
- \+ *lemma* im_smul
- \+ *lemma* is_basis_one_I
- \+ *lemma* findim_real_complex
- \+ *lemma* dim_real_complex
- \+ *lemma* {u}
- \+ *lemma* dim_real_of_complex
- \+ *lemma* findim_real_of_complex

modified src/data/matrix/notation.lean
- \+ *lemma* range_cons
- \+ *lemma* range_empty



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
modified src/algebra/module/basic.lean
- \- *lemma* coe_fn_congr
- \- *lemma* lcongr_fun

modified src/analysis/normed_space/enorm.lean
- \+ *lemma* injective_coe_fn
- \+ *lemma* coe_inj
- \- *lemma* coe_fn_injective

modified src/analysis/normed_space/operator_norm.lean

modified src/category_theory/monoidal/internal/Module.lean

modified src/data/equiv/basic.lean
- \+ *theorem* injective_coe_fn
- \- *theorem* coe_fn_injective

modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* injective_coe_fn

modified src/linear_algebra/basic.lean
- \+ *lemma* injective_to_equiv
- \+ *lemma* to_equiv_inj
- \+ *lemma* injective_to_linear_map
- \+ *lemma* to_linear_map_inj
- \+/\- *lemma* trans_refl
- \+/\- *lemma* refl_trans
- \- *lemma* to_equiv_injective
- \- *lemma* eq_of_linear_map_eq
- \+/\- *lemma* trans_refl
- \+/\- *lemma* refl_trans

modified src/linear_algebra/basis.lean

modified src/linear_algebra/determinant.lean

modified src/measure_theory/outer_measure.lean
- \+ *lemma* injective_coe_fn
- \- *lemma* coe_fn_injective

modified src/order/rel_iso.lean
- \+ *theorem* injective_to_equiv
- \+ *theorem* injective_coe_fn
- \- *theorem* to_equiv_injective
- \- *theorem* coe_fn_injective

modified src/set_theory/ordinal.lean

modified src/topology/algebra/module.lean
- \+ *theorem* injective_coe_fn
- \- *theorem* coe_fn_injective



## [2020-10-20 10:23:25](https://github.com/leanprover-community/mathlib/commit/5d52ea4)
chore(.gitignore): gitignore for emacs temp files ([#4699](https://github.com/leanprover-community/mathlib/pull/4699))
Emacs backup files end in `~`, and you don't want them in the repo. Just makes things mildly easier for emacs users if that pattern is in the gitignore.
#### Estimated changes
modified .gitignore



## [2020-10-20 08:10:53](https://github.com/leanprover-community/mathlib/commit/8131349)
fix(tactic/norm_num): remove one_div from simp set ([#4705](https://github.com/leanprover-community/mathlib/pull/4705))
fixes [#4701](https://github.com/leanprover-community/mathlib/pull/4701)
#### Estimated changes
modified src/tactic/norm_num.lean

modified test/norm_num.lean



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
modified src/algebra/module/ordered.lean
- \+ *lemma* eq_of_smul_eq_smul_of_pos_of_le
- \+ *lemma* lt_of_smul_lt_smul_of_nonneg
- \+ *lemma* smul_lt_smul_iff_of_pos
- \+ *lemma* smul_pos_iff_of_pos
- \+ *lemma* smul_le_smul_iff_of_pos
- \+ *lemma* smul_le_smul_iff_of_neg
- \+ *lemma* smul_lt_iff_of_pos
- \+ *lemma* smul_le_iff_of_pos
- \+ *lemma* le_smul_iff_of_pos
- \+ *def* ordered_semimodule.mk''
- \+ *def* ordered_semimodule.mk'

modified src/analysis/convex/cone.lean

modified src/group_theory/group_action.lean
- \+ *lemma* units.smul_left_cancel
- \+ *lemma* units.smul_eq_iff_eq_inv_smul
- \+ *lemma* is_unit.smul_left_cancel
- \+ *def* units.smul_perm_hom
- \+/\- *def* to_perm
- \+/\- *def* to_perm

modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* line_map_apply_module'
- \+ *lemma* line_map_apply_module
- \+ *lemma* line_map_apply_ring'
- \+ *lemma* line_map_apply_ring
- \+ *lemma* line_map_same_apply
- \+ *lemma* fst_line_map
- \+ *lemma* snd_line_map
- \+ *lemma* line_map_apply_one_sub

created src/linear_algebra/affine_space/ordered.lean
- \+ *lemma* slope_def_field
- \+ *lemma* slope_same
- \+ *lemma* eq_of_slope_eq_zero
- \+ *lemma* slope_comm
- \+ *lemma* sub_div_sub_smul_slope_add_sub_div_sub_smul_slope
- \+ *lemma* line_map_slope_slope_sub_div_sub
- \+ *lemma* line_map_slope_line_map_slope_line_map
- \+ *lemma* line_map_mono_left
- \+ *lemma* line_map_strict_mono_left
- \+ *lemma* line_map_mono_right
- \+ *lemma* line_map_strict_mono_right
- \+ *lemma* line_map_mono_endpoints
- \+ *lemma* line_map_strict_mono_endpoints
- \+ *lemma* line_map_lt_line_map_iff_of_lt
- \+ *lemma* left_lt_line_map_iff_lt
- \+ *lemma* line_map_lt_left_iff_lt
- \+ *lemma* line_map_lt_right_iff_lt
- \+ *lemma* right_lt_line_map_iff_lt
- \+ *lemma* line_map_le_line_map_iff_of_lt
- \+ *lemma* left_le_line_map_iff_le
- \+ *lemma* line_map_le_left_iff_le
- \+ *lemma* line_map_le_right_iff_le
- \+ *lemma* right_le_line_map_iff_le
- \+ *lemma* map_le_line_map_iff_slope_le_slope_left
- \+ *lemma* map_le_line_map_iff_slope_le_slope_left
- \+ *lemma* line_map_le_map_iff_slope_le_slope_left
- \+ *lemma* map_lt_line_map_iff_slope_lt_slope_left
- \+ *lemma* line_map_lt_map_iff_slope_lt_slope_left
- \+ *lemma* map_le_line_map_iff_slope_le_slope_right
- \+ *lemma* line_map_le_map_iff_slope_le_slope_right
- \+ *lemma* map_lt_line_map_iff_slope_lt_slope_right
- \+ *lemma* line_map_lt_map_iff_slope_lt_slope_right
- \+ *lemma* map_le_line_map_iff_slope_le_slope
- \+ *lemma* line_map_le_map_iff_slope_le_slope
- \+ *lemma* map_lt_line_map_iff_slope_lt_slope
- \+ *lemma* line_map_lt_map_iff_slope_lt_slope
- \+ *def* slope



## [2020-10-20 05:38:10](https://github.com/leanprover-community/mathlib/commit/b46190f)
chore(data/finsupp): minor review ([#4712](https://github.com/leanprover-community/mathlib/pull/4712))
* add a few lemmas about injectivity of `coe_fn` etc;
* simplify definition of `finsupp.on_finset`;
* replace the proof of `support_on_finset` by `rfl`;
* make `finsupp.mem_support_on_finset` a `simp` lemma.
#### Estimated changes
modified src/data/finsupp/basic.lean
- \+ *lemma* coe_mk
- \+ *lemma* coe_zero
- \+/\- *lemma* zero_apply
- \+ *lemma* injective_coe_fn
- \+/\- *lemma* ext
- \+ *lemma* ext_iff'
- \+/\- *lemma* mem_support_on_finset
- \+/\- *lemma* zero_apply
- \+/\- *lemma* ext
- \+/\- *lemma* mem_support_on_finset

modified src/linear_algebra/basis.lean



## [2020-10-20 05:38:08](https://github.com/leanprover-community/mathlib/commit/288802b)
chore(data/polynomial): slightly generalize `map_eq_zero` and `map_ne_zero` ([#4708](https://github.com/leanprover-community/mathlib/pull/4708))
We don't need the codomain to be a field.
#### Estimated changes
modified src/data/polynomial/field_division.lean
- \+/\- *lemma* map_eq_zero
- \+/\- *lemma* map_ne_zero
- \+/\- *lemma* map_eq_zero
- \+/\- *lemma* map_ne_zero



## [2020-10-20 05:38:07](https://github.com/leanprover-community/mathlib/commit/21415c8)
chore(topology/algebra/ordered): drop section vars, golf 2 proofs ([#4706](https://github.com/leanprover-community/mathlib/pull/4706))
* Explicitly specify explicit arguments instead of using section
  variables;
* Add `continuous_min` and `continuous_max`;
* Use them for `tendsto.min` and `tendsto.max`
#### Estimated changes
modified src/topology/algebra/ordered.lean
- \+/\- *lemma* frontier_le_subset_eq
- \+/\- *lemma* frontier_lt_subset_eq
- \+/\- *lemma* continuous.min
- \+/\- *lemma* continuous.max
- \+ *lemma* continuous_min
- \+ *lemma* continuous_max
- \+/\- *lemma* frontier_le_subset_eq
- \+/\- *lemma* frontier_lt_subset_eq
- \+/\- *lemma* continuous.min
- \+/\- *lemma* continuous.max



## [2020-10-20 05:38:04](https://github.com/leanprover-community/mathlib/commit/0cf8a98)
chore(data/set): a few more lemmas about `image2` ([#4695](https://github.com/leanprover-community/mathlib/pull/4695))
Also add `@[simp]` to `set.image2_singleton_left` and `set.image2_singleton_rigt`.
#### Estimated changes
modified src/algebra/pointwise.lean

modified src/data/set/basic.lean
- \+ *lemma* exists_prod_set
- \+ *lemma* forall_image2_iff
- \+ *lemma* image2_subset_iff
- \+/\- *lemma* image2_singleton_left
- \+/\- *lemma* image2_singleton_right
- \+/\- *lemma* image2_singleton
- \+ *lemma* image2_assoc
- \+/\- *lemma* image2_singleton
- \+/\- *lemma* image2_singleton_left
- \+/\- *lemma* image2_singleton_right



## [2020-10-20 05:38:01](https://github.com/leanprover-community/mathlib/commit/050b5a1)
feat(data/real/pi): Leibniz's series for pi ([#4228](https://github.com/leanprover-community/mathlib/pull/4228))
Freek No. 26 
<!-- put comments you want to keep out of the PR commit here -->
#### Estimated changes
modified docs/100.yaml

modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* tendsto_exp_nhds_0_nhds_1
- \+ *lemma* tendsto_mul_exp_add_div_pow_at_top
- \+ *lemma* tendsto_div_pow_mul_exp_add_at_top

modified src/analysis/special_functions/pow.lean
- \+ *lemma* log_rpow
- \+ *lemma* tendsto_rpow_at_top
- \+ *lemma* tendsto_rpow_neg_at_top
- \+ *lemma* tendsto_rpow_div_mul_add
- \+ *lemma* tendsto_rpow_div
- \+ *lemma* tendsto_rpow_neg_div

modified src/data/real/pi.lean
- \+ *theorem* tendsto_sum_pi_div_four

modified src/topology/algebra/monoid.lean
- \+ *lemma* tendsto.const_mul
- \+ *lemma* tendsto.mul_const

modified src/topology/algebra/ordered.lean
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
modified src/data/equiv/basic.lean
- \+ *lemma* prod_assoc_preimage

modified src/data/nat/pairing.lean
- \+ *lemma* Union_unpair_prod

modified src/data/set/lattice.lean
- \+ *lemma* prod_Union
- \+ *lemma* prod_bUnion
- \+ *lemma* prod_sUnion
- \+ *lemma* Union_prod
- \+ *lemma* bUnion_prod
- \+ *lemma* sUnion_prod

modified src/measure_theory/measurable_space.lean
- \+/\- *lemma* is_measurable.Union
- \+/\- *lemma* is_measurable.sUnion
- \+/\- *lemma* is_measurable.Union_Prop
- \+/\- *lemma* is_measurable.Inter
- \+/\- *lemma* is_measurable.sInter
- \+/\- *lemma* is_measurable.Inter_Prop
- \+/\- *lemma* is_measurable.disjointed
- \+/\- *lemma* measurable_space.ext
- \+/\- *lemma* generate_from_le
- \+ *lemma* generate_from_is_measurable
- \+/\- *lemma* comap_bot
- \+/\- *lemma* comap_supr
- \+/\- *lemma* map_top
- \+/\- *lemma* measurable_from_top
- \+/\- *lemma* measurable_id
- \+/\- *lemma* measurable.comp
- \+/\- *lemma* subsingleton.measurable
- \+/\- *lemma* measurable.piecewise
- \+/\- *lemma* measurable_const
- \+/\- *lemma* measurable.indicator
- \+/\- *lemma* measurable_one
- \+/\- *lemma* measurable_to_encodable
- \+/\- *lemma* measurable_unit
- \+/\- *lemma* measurable_from_nat
- \+/\- *lemma* measurable_to_nat
- \+/\- *lemma* measurable_find_greatest'
- \+/\- *lemma* measurable_find_greatest
- \+/\- *lemma* measurable_find
- \+/\- *lemma* measurable_subtype_coe
- \+/\- *lemma* measurable.subtype_coe
- \+/\- *lemma* measurable.subtype_mk
- \+/\- *lemma* is_measurable.subtype_image
- \+/\- *lemma* measurable_of_measurable_on_compl_singleton
- \+/\- *lemma* measurable.fst
- \+/\- *lemma* measurable.snd
- \+/\- *lemma* measurable_pi_apply
- \+/\- *lemma* measurable_pi_lambda
- \+ *lemma* measurable.sum_elim
- \+/\- *lemma* coe_eq
- \+ *lemma* is_pi_system_is_measurable
- \+/\- *lemma* ext
- \+/\- *lemma* generate_le
- \+ *lemma* is_countably_spanning_is_measurable
- \+/\- *lemma* is_measurable.Union
- \+/\- *lemma* is_measurable.sUnion
- \+/\- *lemma* is_measurable.Union_Prop
- \+/\- *lemma* is_measurable.Inter
- \+/\- *lemma* is_measurable.sInter
- \+/\- *lemma* is_measurable.Inter_Prop
- \+/\- *lemma* is_measurable.disjointed
- \+/\- *lemma* measurable_space.ext
- \+/\- *lemma* generate_from_le
- \+/\- *lemma* comap_bot
- \+/\- *lemma* comap_supr
- \+/\- *lemma* map_top
- \+/\- *lemma* subsingleton.measurable
- \+/\- *lemma* measurable_id
- \+/\- *lemma* measurable.comp
- \+/\- *lemma* measurable_from_top
- \+/\- *lemma* measurable.piecewise
- \+/\- *lemma* measurable_const
- \+/\- *lemma* measurable.indicator
- \+/\- *lemma* measurable_one
- \+/\- *lemma* measurable_to_encodable
- \+/\- *lemma* measurable_unit
- \+/\- *lemma* measurable_from_nat
- \+/\- *lemma* measurable_to_nat
- \+/\- *lemma* measurable_find_greatest'
- \+/\- *lemma* measurable_find_greatest
- \+/\- *lemma* measurable_find
- \+/\- *lemma* measurable_subtype_coe
- \+/\- *lemma* measurable.subtype_coe
- \+/\- *lemma* measurable.subtype_mk
- \+/\- *lemma* is_measurable.subtype_image
- \+/\- *lemma* measurable_of_measurable_on_compl_singleton
- \+/\- *lemma* measurable.fst
- \+/\- *lemma* measurable.snd
- \+/\- *lemma* measurable_pi_apply
- \+/\- *lemma* measurable_pi_lambda
- \- *lemma* measurable.sum_rec
- \+/\- *lemma* coe_eq
- \- *lemma* trans_to_equiv
- \- *lemma* symm_to_equiv
- \+/\- *lemma* ext
- \+/\- *lemma* generate_le
- \+/\- *def* gi_generate_from
- \+/\- *def* trans
- \+/\- *def* symm
- \+/\- *def* prod_congr
- \+/\- *def* prod_comm
- \+ *def* prod_assoc
- \+/\- *def* sum_congr
- \+/\- *def* set.prod
- \+/\- *def* set.singleton
- \+/\- *def* set.range_inl
- \+/\- *def* set.range_inr
- \+/\- *def* to_measurable_space
- \+ *def* is_countably_spanning
- \+/\- *def* gi_generate_from
- \+/\- *def* trans
- \+/\- *def* symm
- \+/\- *def* prod_congr
- \+/\- *def* prod_comm
- \+/\- *def* sum_congr
- \+/\- *def* set.prod
- \+/\- *def* set.singleton
- \+/\- *def* set.range_inl
- \+/\- *def* set.range_inr
- \+/\- *def* to_measurable_space

modified src/measure_theory/measure_space.lean
- \+/\- *lemma* ext_of_generate_from_of_Union
- \+ *lemma* finite_at_bot
- \+ *lemma* is_countably_spanning_spanning_sets
- \+/\- *lemma* ext_of_generate_from_of_Union
- \- *lemma* measure.finite_at_bot
- \- *lemma* exists_finite_spanning_sets
- \+ *def* finite_at_filter
- \+ *def* sigma_finite
- \+ *def* measure.to_finite_spanning_sets_in
- \+/\- *def* null_measurable
- \+/\- *def* completion
- \- *def* measure.finite_at_filter
- \+/\- *def* null_measurable
- \+/\- *def* completion

modified src/measure_theory/prod.lean
- \+ *lemma* is_pi_system.prod
- \+ *lemma* is_countably_spanning.prod
- \+ *lemma* generate_from_prod_eq
- \+ *lemma* generate_from_eq_prod
- \+ *lemma* prod_eq_generate_from
- \+ *lemma* prod_assoc_prod
- \- *lemma* prod_unique
- \+ *def* finite_spanning_sets_in.prod



## [2020-10-20 01:14:13](https://github.com/leanprover-community/mathlib/commit/9755ae3)
chore(scripts): update nolints.txt ([#4704](https://github.com/leanprover-community/mathlib/pull/4704))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-19 22:45:26](https://github.com/leanprover-community/mathlib/commit/accc50e)
chore(data/finsupp): `to_additive` on `on_finset_sum` ([#4698](https://github.com/leanprover-community/mathlib/pull/4698))
#### Estimated changes
modified src/data/finsupp/basic.lean
- \+ *lemma* on_finset_prod
- \- *lemma* on_finset_sum



## [2020-10-19 22:45:23](https://github.com/leanprover-community/mathlib/commit/706b484)
chore(data/multiset): add a few lemmas ([#4697](https://github.com/leanprover-community/mathlib/pull/4697))
#### Estimated changes
modified src/data/multiset/basic.lean
- \+ *theorem* map_nsmul
- \+ *theorem* sum_map_singleton
- \+ *theorem* count_cons



## [2020-10-19 22:45:21](https://github.com/leanprover-community/mathlib/commit/b707e98)
refactor(ring_theory/witt_vector): move lemmas to separate file ([#4693](https://github.com/leanprover-community/mathlib/pull/4693))
This new file has almost no module docstring.
This is on purpose, it is a refactor PR.
A follow-up PR will add a module docstring and more definitions.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
created src/ring_theory/witt_vector/defs.lean
- \+ *lemma* witt_zero_eq_zero
- \+ *lemma* witt_one_zero_eq_one
- \+ *lemma* witt_one_pos_eq_zero
- \+ *lemma* witt_add_zero
- \+ *lemma* witt_sub_zero
- \+ *lemma* witt_mul_zero
- \+ *lemma* witt_neg_zero
- \+ *lemma* constant_coeff_witt_add
- \+ *lemma* constant_coeff_witt_sub
- \+ *lemma* constant_coeff_witt_mul
- \+ *lemma* constant_coeff_witt_neg
- \+ *lemma* witt_add_vars
- \+ *lemma* witt_mul_vars
- \+ *lemma* witt_neg_vars
- \+ *def* witt_zero
- \+ *def* witt_one
- \+ *def* witt_add
- \+ *def* witt_sub
- \+ *def* witt_mul
- \+ *def* witt_neg

modified src/ring_theory/witt_vector/structure_polynomial.lean
- \- *lemma* witt_zero_eq_zero
- \- *lemma* witt_one_zero_eq_one
- \- *lemma* witt_one_pos_eq_zero
- \- *lemma* witt_add_zero
- \- *lemma* witt_sub_zero
- \- *lemma* witt_mul_zero
- \- *lemma* witt_neg_zero
- \- *lemma* constant_coeff_witt_add
- \- *lemma* constant_coeff_witt_sub
- \- *lemma* constant_coeff_witt_mul
- \- *lemma* constant_coeff_witt_neg
- \- *lemma* witt_add_vars
- \- *lemma* witt_mul_vars
- \- *lemma* witt_neg_vars



## [2020-10-19 22:45:19](https://github.com/leanprover-community/mathlib/commit/b300302)
feat(algebra/free_algebra): Add a ring instance ([#4692](https://github.com/leanprover-community/mathlib/pull/4692))
This also adds a ring instance to `tensor_algebra`.
The approach here does not work for `exterior_algebra` and `clifford_algebra`, and produces weird errors.
Those will be easier to investigate when their foundations are in mathlib.
#### Estimated changes
modified src/algebra/free_algebra.lean

modified src/linear_algebra/tensor_algebra.lean



## [2020-10-19 22:45:17](https://github.com/leanprover-community/mathlib/commit/cc6594a)
doc(algebra/algebra/basic): Fixes some documentation about `R`-algebras ([#4689](https://github.com/leanprover-community/mathlib/pull/4689))
See the associated zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/The.20Type.20of.20R-algebras/near/213722713
#### Estimated changes
modified src/algebra/algebra/basic.lean



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
modified src/data/real/ennreal.lean
- \+/\- *lemma* some_eq_coe
- \+/\- *lemma* coe_nnreal_eq
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_to_real
- \+/\- *lemma* forall_ennreal
- \+ *lemma* forall_ne_top
- \+ *lemma* exists_ne_top
- \+/\- *lemma* coe_mono
- \+/\- *lemma* coe_two
- \+ *lemma* cinfi_ne_top
- \+ *lemma* infi_ne_top
- \+ *lemma* csupr_ne_top
- \+ *lemma* supr_ne_top
- \+/\- *lemma* infi_ennreal
- \+ *lemma* supr_ennreal
- \+/\- *lemma* coe_indicator
- \+/\- *lemma* coe_finset_sum
- \+/\- *lemma* coe_finset_prod
- \+/\- *lemma* coe_nat
- \+/\- *lemma* le_coe_iff
- \+/\- *lemma* coe_le_iff
- \+/\- *lemma* lt_iff_exists_coe
- \+/\- *lemma* le_of_forall_epsilon_le
- \+/\- *lemma* lt_iff_exists_add_pos_lt
- \+/\- *lemma* coe_min
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_Sup
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* coe_mem_upper_bounds
- \+/\- *lemma* coe_inv_two
- \+/\- *lemma* some_eq_coe
- \+/\- *lemma* coe_nnreal_eq
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_to_real
- \+/\- *lemma* forall_ennreal
- \+/\- *lemma* coe_mono
- \+/\- *lemma* coe_two
- \+/\- *lemma* coe_indicator
- \+/\- *lemma* coe_finset_sum
- \+/\- *lemma* coe_finset_prod
- \+/\- *lemma* coe_nat
- \+/\- *lemma* le_coe_iff
- \+/\- *lemma* coe_le_iff
- \+/\- *lemma* lt_iff_exists_coe
- \+/\- *lemma* le_of_forall_epsilon_le
- \+/\- *lemma* lt_iff_exists_add_pos_lt
- \+/\- *lemma* coe_min
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_Sup
- \+/\- *lemma* coe_Inf
- \+/\- *lemma* coe_mem_upper_bounds
- \+/\- *lemma* infi_ennreal
- \+/\- *lemma* coe_inv_two
- \+/\- *def* ennreal
- \+ *def* ne_top_equiv_nnreal
- \+/\- *def* of_nnreal_hom
- \+/\- *def* ennreal
- \+/\- *def* of_nnreal_hom

modified src/data/real/nnreal.lean

modified src/order/filter/basic.lean
- \+/\- *lemma* comap_map
- \+/\- *lemma* comap_map

modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_nhds_top_mono
- \+ *lemma* tendsto_nhds_bot_mono
- \+ *lemma* tendsto_nhds_top_mono'
- \+ *lemma* tendsto_nhds_bot_mono'

modified src/topology/instances/ennreal.lean
- \+/\- *lemma* nhds_top
- \+ *lemma* nhds_top'
- \+ *lemma* tendsto_nhds_top_iff_nnreal
- \+ *lemma* tendsto_nhds_top_iff_nat
- \+ *lemma* tendsto_coe_nhds_top
- \+/\- *lemma* tsum_coe_ne_top_iff_summable
- \+/\- *lemma* has_sum_iff_tendsto_nat
- \+ *lemma* not_summable_iff_tendsto_nat_at_top
- \+ *lemma* not_summable_iff_tendsto_nat_at_top_of_nonneg
- \+/\- *lemma* nhds_top
- \- *lemma* tendsto_coe_nnreal_nhds_top
- \+/\- *lemma* tsum_coe_ne_top_iff_summable
- \+/\- *lemma* has_sum_iff_tendsto_nat
- \- *lemma* infi_real_pos_eq_infi_nnreal_pos
- \+/\- *def* ne_top_homeomorph_nnreal
- \+/\- *def* lt_top_homeomorph_nnreal
- \+/\- *def* ne_top_homeomorph_nnreal
- \+/\- *def* lt_top_homeomorph_nnreal

modified src/topology/instances/nnreal.lean
- \+/\- *lemma* tendsto_coe
- \+ *lemma* tendsto_coe'
- \+ *lemma* map_coe_at_top
- \+ *lemma* comap_coe_at_top
- \+ *lemma* tendsto_coe_at_top
- \+ *lemma* infi_real_pos_eq_infi_nnreal_pos
- \+/\- *lemma* tendsto_coe



## [2020-10-19 22:45:12](https://github.com/leanprover-community/mathlib/commit/3019581)
feat({field,ring}_theory/adjoin): generalize `induction_on_adjoin` ([#4647](https://github.com/leanprover-community/mathlib/pull/4647))
We can prove `induction_on_adjoin` for both `algebra.adjoin` and `intermediate_field.adjoin` in a very similar way, if we add a couple of small lemmas. The extra lemmas I introduced for `algebra.adjoin` shorten the proof of `intermediate_field.adjoin` noticeably.
#### Estimated changes
modified src/field_theory/adjoin.lean
- \+ *lemma* adjoin_empty
- \+ *lemma* adjoin_insert_adjoin
- \+ *lemma* adjoin_eq_algebra_adjoin
- \+ *lemma* eq_adjoin_of_eq_algebra_adjoin
- \+ *lemma* fg_adjoin_finset
- \+ *lemma* fg_of_fg_to_subalgebra
- \+ *lemma* fg_of_noetherian
- \- *lemma* adjoin_le_algebra_adjoin
- \+ *theorem* fg_def
- \+ *theorem* fg_bot
- \+ *def* fg

modified src/field_theory/intermediate_field.lean
- \+ *lemma* to_subalgebra_le_to_subalgebra
- \+ *lemma* to_subalgebra_lt_to_subalgebra

modified src/ring_theory/adjoin.lean
- \+ *lemma* adjoin_insert_adjoin
- \+ *lemma* induction_on_adjoin
- \+ *theorem* fg_of_fg_to_submodule
- \+ *theorem* fg_of_noetherian



## [2020-10-19 22:45:10](https://github.com/leanprover-community/mathlib/commit/006b2e7)
feat(data/polynomial/reverse): define `reverse f`, prove that `reverse` is a multiplicative monoid homomorphism ([#4598](https://github.com/leanprover-community/mathlib/pull/4598))
#### Estimated changes
created src/data/polynomial/reverse.lean
- \+ *lemma* rev_at_fun_invol
- \+ *lemma* rev_at_fun_inj
- \+ *lemma* rev_at_fun_eq
- \+ *lemma* rev_at_invol
- \+ *lemma* rev_at_le
- \+ *lemma* rev_at_add
- \+ *lemma* reflect_support
- \+ *lemma* coeff_reflect
- \+ *lemma* reflect_zero
- \+ *lemma* reflect_eq_zero_iff
- \+ *lemma* reflect_add
- \+ *lemma* reflect_C_mul
- \+ *lemma* reflect_C_mul_X_pow
- \+ *lemma* reflect_monomial
- \+ *lemma* reflect_mul_induction
- \+ *lemma* reverse_zero
- \+ *lemma* reverse_mul_of_domain
- \+ *theorem* reflect_mul
- \+ *theorem* reverse_mul
- \+ *def* rev_at_fun
- \+ *def* rev_at



## [2020-10-19 22:45:07](https://github.com/leanprover-community/mathlib/commit/0c70cf3)
feat(tactic/unify_equations): add unify_equations tactic ([#4515](https://github.com/leanprover-community/mathlib/pull/4515))
`unify_equations` is a first-order unification tactic for propositional
equalities. It implements the algorithm that `cases` uses to simplify
indices of inductive types, with one extension: `unify_equations` can
derive a contradiction from 'cyclic' equations like `n = n + 1`.
`unify_equations` is unlikely to be particularly useful on its own, but
I'll use it as part of my new `induction` tactic.
#### Estimated changes
modified docs/references.bib

modified src/tactic/basic.lean

modified src/tactic/core.lean

created src/tactic/unify_equations.lean
- \+ *lemma* add_add_one_ne

created test/unify_equations.lean



## [2020-10-19 22:45:05](https://github.com/leanprover-community/mathlib/commit/a249c9a)
feat(archive/imo): formalize IMO 1998 problem 2 ([#4502](https://github.com/leanprover-community/mathlib/pull/4502))
#### Estimated changes
created archive/imo/imo1998_q2.lean
- \+ *lemma* judge_pair.agree_iff_same_rating
- \+ *lemma* A_maps_to_off_diag_judge_pair
- \+ *lemma* A_fibre_over_contestant
- \+ *lemma* A_fibre_over_contestant_card
- \+ *lemma* A_fibre_over_judge_pair
- \+ *lemma* A_fibre_over_judge_pair_card
- \+ *lemma* A_card_upper_bound
- \+ *lemma* add_sq_add_sq_sub
- \+ *lemma* norm_bound_of_odd_sum
- \+ *lemma* judge_pairs_card_lower_bound
- \+ *lemma* distinct_judge_pairs_card_lower_bound
- \+ *lemma* A_card_lower_bound
- \+ *lemma* clear_denominators
- \+ *theorem* imo1998_q2
- \+ *def* agreed_contestants
- \+ *def* A

modified src/data/finset/basic.lean
- \+ *lemma* filter_product_card
- \+ *lemma* filter_card_add_filter_neg_card_eq_card
- \+ *lemma* mem_diag
- \+ *lemma* mem_off_diag
- \+ *lemma* diag_card
- \+ *lemma* off_diag_card
- \+ *theorem* filter_product
- \+ *def* diag
- \+ *def* off_diag

modified src/data/int/parity.lean
- \+ *lemma* ne_of_odd_sum

modified src/data/nat/parity.lean
- \+ *lemma* odd_gt_zero



## [2020-10-19 22:45:03](https://github.com/leanprover-community/mathlib/commit/5065471)
feat(data/monoid_algebra): add missing has_coe_to_fun ([#4315](https://github.com/leanprover-community/mathlib/pull/4315))
Also does the same for the additive version `semimodule k (add_monoid_algebra k G)`.
#### Estimated changes
modified src/algebra/monoid_algebra.lean



## [2020-10-19 20:01:36](https://github.com/leanprover-community/mathlib/commit/0523b61)
chore(logic/function): `simp`lify applications of `(un)curry` ([#4696](https://github.com/leanprover-community/mathlib/pull/4696))
#### Estimated changes
modified src/logic/function/basic.lean
- \+ *lemma* uncurry_apply_pair
- \+ *lemma* curry_apply



## [2020-10-19 15:37:07-04:00](https://github.com/leanprover-community/mathlib/commit/a1f1770)
Revert "chore(data/multiset): add a few lemmas"
This reverts commit 45caa4f392fe4f7622fef576cf3811b9ff6fd307.
#### Estimated changes
modified src/data/multiset/basic.lean
- \- *theorem* map_nsmul
- \- *theorem* sum_map_singleton
- \- *theorem* count_cons



## [2020-10-19 15:30:42-04:00](https://github.com/leanprover-community/mathlib/commit/45caa4f)
chore(data/multiset): add a few lemmas
#### Estimated changes
modified src/data/multiset/basic.lean
- \+ *theorem* map_nsmul
- \+ *theorem* sum_map_singleton
- \+ *theorem* count_cons



## [2020-10-19 15:11:45](https://github.com/leanprover-community/mathlib/commit/cacc297)
fix(tactic/norm_num): remove unnecessary argument to rat.cast_zero ([#4682](https://github.com/leanprover-community/mathlib/pull/4682))
See [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60norm_num.60.20error.20message).
#### Estimated changes
modified src/tactic/norm_num.lean
- \+/\- *lemma* int_div
- \+/\- *lemma* int_mod
- \+/\- *lemma* int_div
- \+/\- *lemma* int_mod
- \+/\- *theorem* adc_bit1_bit0
- \+/\- *theorem* adc_bit0_bit1
- \+/\- *theorem* adc_bit1_bit1
- \+/\- *theorem* lt_bit0_bit0
- \+/\- *theorem* lt_bit1_bit1
- \+/\- *theorem* le_bit0_bit0
- \+/\- *theorem* le_bit1_bit1
- \+/\- *theorem* sle_one_bit0
- \+/\- *theorem* sle_one_bit1
- \+/\- *theorem* sle_bit0_bit0
- \+/\- *theorem* sle_bit0_bit1
- \+/\- *theorem* sle_bit1_bit0
- \+/\- *theorem* sle_bit1_bit1
- \+/\- *theorem* rat_cast_bit0
- \+/\- *theorem* rat_cast_bit1
- \+/\- *theorem* adc_bit1_bit0
- \+/\- *theorem* adc_bit0_bit1
- \+/\- *theorem* adc_bit1_bit1
- \+/\- *theorem* lt_bit0_bit0
- \+/\- *theorem* lt_bit1_bit1
- \+/\- *theorem* le_bit0_bit0
- \+/\- *theorem* le_bit1_bit1
- \+/\- *theorem* sle_one_bit0
- \+/\- *theorem* sle_one_bit1
- \+/\- *theorem* sle_bit0_bit0
- \+/\- *theorem* sle_bit0_bit1
- \+/\- *theorem* sle_bit1_bit0
- \+/\- *theorem* sle_bit1_bit1
- \+/\- *theorem* rat_cast_bit0
- \+/\- *theorem* rat_cast_bit1

modified test/norm_num.lean



## [2020-10-19 11:39:07](https://github.com/leanprover-community/mathlib/commit/0f1bc68)
feat(ring_theory/witt_vector/structure_polynomial): examples and basic properties ([#4467](https://github.com/leanprover-community/mathlib/pull/4467))
This is the 4th and final PR in a series on a fundamental theorem about Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
modified src/data/mv_polynomial/basic.lean
- \+ *lemma* eval₂_hom_zero
- \+ *lemma* eval₂_hom_zero'
- \+/\- *lemma* aeval_zero
- \+/\- *lemma* aeval_zero

modified src/data/mv_polynomial/variables.lean
- \+ *lemma* mem_vars_bind₁
- \+ *lemma* mem_vars_rename

modified src/ring_theory/witt_vector/structure_polynomial.lean
- \+ *lemma* constant_coeff_witt_structure_rat_zero
- \+ *lemma* constant_coeff_witt_structure_rat
- \+ *lemma* constant_coeff_witt_structure_int_zero
- \+ *lemma* constant_coeff_witt_structure_int
- \+ *lemma* witt_zero_eq_zero
- \+ *lemma* witt_one_zero_eq_one
- \+ *lemma* witt_one_pos_eq_zero
- \+ *lemma* witt_add_zero
- \+ *lemma* witt_sub_zero
- \+ *lemma* witt_mul_zero
- \+ *lemma* witt_neg_zero
- \+ *lemma* constant_coeff_witt_add
- \+ *lemma* constant_coeff_witt_sub
- \+ *lemma* constant_coeff_witt_mul
- \+ *lemma* constant_coeff_witt_neg
- \+ *lemma* witt_structure_rat_vars
- \+ *lemma* witt_structure_int_vars
- \+ *lemma* witt_add_vars
- \+ *lemma* witt_mul_vars
- \+ *lemma* witt_neg_vars



## [2020-10-19 11:39:05](https://github.com/leanprover-community/mathlib/commit/4140f78)
feat(algebra/ordered_semiring): relax 0 < 1 to 0 ≤ 1 ([#4363](https://github.com/leanprover-community/mathlib/pull/4363))
Per [discussion](https://github.com/leanprover-community/mathlib/pull/4296#issuecomment-701953077) in [#4296](https://github.com/leanprover-community/mathlib/pull/4296).
#### Estimated changes
modified archive/imo/imo1972_b2.lean

modified src/algebra/group_power/basic.lean

modified src/algebra/linear_ordered_comm_group_with_zero.lean
- \- *lemma* zero_lt_one'

modified src/algebra/ordered_field.lean

modified src/algebra/ordered_ring.lean
- \+ *lemma* zero_le_two
- \+/\- *lemma* zero_lt_one
- \+/\- *lemma* bit1_pos'
- \+ *lemma* zero_lt_one'
- \+/\- *lemma* le_of_mul_le_of_one_le
- \+/\- *lemma* zero_lt_one
- \+/\- *lemma* zero_lt_one
- \+/\- *lemma* bit1_pos'
- \+/\- *lemma* le_of_mul_le_of_one_le
- \+/\- *lemma* zero_lt_one
- \+/\- *def* to_linear_nonneg_ring
- \- *def* to_ordered_ring
- \+/\- *def* to_linear_nonneg_ring

modified src/algebra/punit_instances.lean

modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_two
- \+/\- *lemma* norm_two

modified src/analysis/normed_space/mazur_ulam.lean

modified src/analysis/special_functions/pow.lean

modified src/analysis/special_functions/trigonometric.lean

modified src/data/complex/basic.lean

modified src/data/complex/is_R_or_C.lean

modified src/data/int/basic.lean

modified src/data/nat/basic.lean

modified src/data/num/lemmas.lean

modified src/data/polynomial/div.lean

modified src/data/rat/order.lean

modified src/data/real/basic.lean

modified src/data/real/ennreal.lean
- \+/\- *lemma* one_lt_two
- \+/\- *lemma* one_lt_two

modified src/data/real/nnreal.lean

modified src/data/zsqrtd/basic.lean

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/order/filter/filter_product.lean
- \+ *lemma* le_def

modified src/ring_theory/subsemiring.lean

modified src/tactic/linarith/verification.lean

modified src/tactic/norm_num.lean

modified src/tactic/omega/coeffs.lean

modified src/topology/algebra/floor_ring.lean

modified src/topology/metric_space/basic.lean

modified src/topology/path_connected.lean



## [2020-10-19 10:38:52](https://github.com/leanprover-community/mathlib/commit/ef9d00f)
feat(linear_algebra/matrix): multiplying `is_basis.to_matrix` and `linear_map.to_matrix` ([#4650](https://github.com/leanprover-community/mathlib/pull/4650))
This basically tells us that `is_basis.to_matrix` is indeed a basis change matrix.
#### Estimated changes
modified src/linear_algebra/matrix.lean
- \+ *lemma* matrix.to_lin_self
- \+ *lemma* to_matrix_eq_to_matrix_constr
- \+/\- *lemma* to_matrix_self
- \+/\- *lemma* to_matrix_update
- \+ *lemma* sum_to_matrix_smul_self
- \+ *lemma* to_lin_to_matrix
- \+ *lemma* is_basis_to_matrix_mul_linear_map_to_matrix
- \+ *lemma* linear_map_to_matrix_mul_is_basis_to_matrix
- \+/\- *lemma* to_matrix_self
- \+/\- *lemma* to_matrix_update
- \+/\- *def* is_basis.to_matrix
- \+/\- *def* is_basis.to_matrix



## [2020-10-19 10:38:50](https://github.com/leanprover-community/mathlib/commit/47dcecd)
feat(data/complex/exponential): bounds on exp ([#4432](https://github.com/leanprover-community/mathlib/pull/4432))
Define `real.exp_bound` using `complex.exp_bound`.  Deduce numerical
bounds on `exp 1` analogous to those we have for pi.
#### Estimated changes
modified src/data/complex/exponential.lean
- \+ *lemma* exp_bound
- \+ *lemma* exp_approx_end
- \+ *lemma* exp_approx_succ
- \+ *lemma* exp_approx_end'
- \+ *lemma* exp_1_approx_succ_eq
- \+ *lemma* exp_approx_start
- \+ *theorem* exp_near_zero
- \+ *theorem* exp_near_succ
- \+ *theorem* exp_near_sub
- \+ *def* exp_near

created src/data/complex/exponential_bounds.lean
- \+ *lemma* exp_one_near_10
- \+ *lemma* exp_one_near_20
- \+ *lemma* exp_one_gt_271828182
- \+ *lemma* exp_one_lt_271828183
- \+ *lemma* exp_neg_one_gt_0367879441
- \+ *lemma* exp_neg_one_lt_0367879442



## [2020-10-19 10:38:48](https://github.com/leanprover-community/mathlib/commit/c38d128)
feat(ring_theory/polynomial/chebyshev): chebyshev polynomials of the first kind ([#4267](https://github.com/leanprover-community/mathlib/pull/4267))
If T_n denotes the n-th Chebyshev polynomial of the first kind, then the
polynomials 2*T_n(X/2) form a Lambda structure on Z[X].
I call these polynomials the lambdashev polynomials, because, as far as I
am aware they don't have a name in the literature.
We show that they commute, and that the p-th polynomial is congruent to X^p
mod p. In other words: a Lambda structure.
#### Estimated changes
modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* chebyshev₁_complex_cos
- \+ *lemma* cos_nat_mul

created src/ring_theory/polynomial/chebyshev/basic.lean
- \+ *lemma* chebyshev₁_mul
- \+ *lemma* lambdashev_eval_add_inv
- \+ *lemma* lambdashev_eq_chebyshev₁
- \+ *lemma* chebyshev₁_eq_lambdashev
- \+ *lemma* lambdashev_mul
- \+ *lemma* lambdashev_comp_comm
- \+ *lemma* lambdashev_zmod_p
- \+ *lemma* lambdashev_char_p

created src/ring_theory/polynomial/chebyshev/default.lean

created src/ring_theory/polynomial/chebyshev/defs.lean
- \+ *lemma* chebyshev₁_zero
- \+ *lemma* chebyshev₁_one
- \+ *lemma* chebyshev₁_two
- \+ *lemma* chebyshev₁_add_two
- \+ *lemma* chebyshev₁_of_two_le
- \+ *lemma* map_chebyshev₁
- \+ *lemma* lambdashev_zero
- \+ *lemma* lambdashev_one
- \+ *lemma* lambdashev_two
- \+ *lemma* lambdashev_add_two
- \+ *lemma* lambdashev_eq_two_le
- \+ *lemma* map_lambdashev



## [2020-10-19 07:13:04](https://github.com/leanprover-community/mathlib/commit/f75dbd3)
feat(algebra/*): some simp lemmas, and changing binders ([#4681](https://github.com/leanprover-community/mathlib/pull/4681))
#### Estimated changes
modified src/algebra/algebra/basic.lean

modified src/algebra/invertible.lean
- \+ *lemma* inv_of_mul_self_assoc
- \+ *lemma* mul_inv_of_self_assoc

modified src/group_theory/group_action.lean



## [2020-10-19 07:13:01](https://github.com/leanprover-community/mathlib/commit/41c227a)
feat(algebra/infinite_sum): make tsum irreducible ([#4679](https://github.com/leanprover-community/mathlib/pull/4679))
See https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/congr'.20is.20slow
#### Estimated changes
modified src/topology/algebra/infinite_sum.lean
- \+/\- *def* tsum
- \+/\- *def* tsum



## [2020-10-19 07:12:58](https://github.com/leanprover-community/mathlib/commit/7601a7a)
feat(ring_theory/adjoin): adjoin_singleton_one ([#4633](https://github.com/leanprover-community/mathlib/pull/4633))
#### Estimated changes
modified src/ring_theory/adjoin.lean
- \+ *lemma* adjoin_singleton_one



## [2020-10-19 04:45:06](https://github.com/leanprover-community/mathlib/commit/4b890a2)
feat(*): make int.nonneg irreducible ([#4601](https://github.com/leanprover-community/mathlib/pull/4601))
In [#4474](https://github.com/leanprover-community/mathlib/pull/4474), `int.lt` was made irreducible. We make `int.nonneg` irreducible, which is stronger as `int.lt` is expressed in terms of `int.nonneg`.
#### Estimated changes
modified src/algebra/field_power.lean

modified src/data/int/basic.lean

modified src/data/int/range.lean

modified src/data/int/sqrt.lean
- \+/\- *theorem* sqrt_nonneg
- \+/\- *theorem* sqrt_nonneg

modified src/data/nat/modeq.lean

modified src/data/rat/sqrt.lean

modified src/data/zmod/basic.lean

modified src/data/zsqrtd/gaussian_int.lean
- \+/\- *lemma* norm_nonneg
- \+/\- *lemma* norm_nonneg

modified src/number_theory/lucas_lehmer.lean

modified src/tactic/omega/eq_elim.lean

modified src/tactic/omega/nat/dnf.lean

modified test/monotonicity.lean

modified test/tactics.lean



## [2020-10-19 01:25:23](https://github.com/leanprover-community/mathlib/commit/d174295)
chore(scripts): update nolints.txt ([#4680](https://github.com/leanprover-community/mathlib/pull/4680))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-19 01:25:21](https://github.com/leanprover-community/mathlib/commit/9d1bbd1)
fix(data/equiv): nolint typo ([#4677](https://github.com/leanprover-community/mathlib/pull/4677))
#### Estimated changes
modified src/data/equiv/basic.lean



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
modified src/tactic/norm_num.lean
- \+/\- *lemma* lt_neg_pos
- \+/\- *lemma* pow_bit0
- \+/\- *lemma* pow_bit1
- \+/\- *lemma* pow_bit0
- \+/\- *lemma* pow_bit1
- \+/\- *lemma* lt_neg_pos
- \+/\- *theorem* nonneg_pos
- \+/\- *theorem* lt_one_bit0
- \+/\- *theorem* lt_one_bit1
- \+/\- *theorem* lt_bit0_bit0
- \+/\- *theorem* lt_bit0_bit1
- \+/\- *theorem* lt_bit1_bit0
- \+/\- *theorem* lt_bit1_bit1
- \+/\- *theorem* le_one_bit0
- \+/\- *theorem* le_one_bit1
- \+/\- *theorem* le_bit0_bit0
- \+/\- *theorem* le_bit0_bit1
- \+/\- *theorem* le_bit1_bit0
- \+/\- *theorem* le_bit1_bit1
- \+/\- *theorem* sle_one_bit0
- \+/\- *theorem* sle_one_bit1
- \+/\- *theorem* sle_bit0_bit0
- \+/\- *theorem* sle_bit0_bit1
- \+/\- *theorem* sle_bit1_bit0
- \+/\- *theorem* sle_bit1_bit1
- \+/\- *theorem* clear_denom_lt
- \+/\- *theorem* clear_denom_le
- \+/\- *theorem* rat_cast_div
- \+/\- *theorem* int_cast_neg
- \+/\- *theorem* rat_cast_neg
- \+/\- *theorem* nat_cast_ne
- \+/\- *theorem* int_cast_ne
- \+/\- *theorem* rat_cast_ne
- \+/\- *theorem* clear_denom_add
- \+/\- *theorem* add_pos_neg_pos
- \+/\- *theorem* add_pos_neg_neg
- \+/\- *theorem* add_neg_pos_pos
- \+/\- *theorem* add_neg_pos_neg
- \+/\- *theorem* add_neg_neg
- \+/\- *theorem* clear_denom_simple_nat
- \+/\- *theorem* clear_denom_simple_div
- \+/\- *theorem* clear_denom_mul
- \+/\- *theorem* mul_neg_pos
- \+/\- *theorem* mul_pos_neg
- \+/\- *theorem* mul_neg_neg
- \+/\- *theorem* inv_neg
- \+/\- *theorem* inv_one
- \+/\- *theorem* inv_one_div
- \+/\- *theorem* inv_div_one
- \+/\- *theorem* inv_div
- \+/\- *theorem* div_eq
- \+/\- *theorem* sub_pos
- \+/\- *theorem* sub_neg
- \+/\- *theorem* sub_nat_pos
- \+/\- *theorem* sub_nat_neg
- \+/\- *theorem* int_sub_hack
- \+/\- *theorem* clear_denom_add
- \+/\- *theorem* add_pos_neg_pos
- \+/\- *theorem* add_pos_neg_neg
- \+/\- *theorem* add_neg_pos_pos
- \+/\- *theorem* add_neg_pos_neg
- \+/\- *theorem* add_neg_neg
- \+/\- *theorem* clear_denom_simple_nat
- \+/\- *theorem* clear_denom_simple_div
- \+/\- *theorem* clear_denom_mul
- \+/\- *theorem* mul_neg_pos
- \+/\- *theorem* mul_pos_neg
- \+/\- *theorem* mul_neg_neg
- \+/\- *theorem* inv_neg
- \+/\- *theorem* inv_one
- \+/\- *theorem* inv_one_div
- \+/\- *theorem* inv_div_one
- \+/\- *theorem* inv_div
- \+/\- *theorem* div_eq
- \+/\- *theorem* sub_pos
- \+/\- *theorem* sub_neg
- \+/\- *theorem* sub_nat_pos
- \+/\- *theorem* sub_nat_neg
- \+/\- *theorem* int_sub_hack
- \+/\- *theorem* nonneg_pos
- \+/\- *theorem* lt_one_bit0
- \+/\- *theorem* lt_one_bit1
- \+/\- *theorem* lt_bit0_bit0
- \+/\- *theorem* lt_bit0_bit1
- \+/\- *theorem* lt_bit1_bit0
- \+/\- *theorem* lt_bit1_bit1
- \+/\- *theorem* le_one_bit0
- \+/\- *theorem* le_one_bit1
- \+/\- *theorem* le_bit0_bit0
- \+/\- *theorem* le_bit0_bit1
- \+/\- *theorem* le_bit1_bit0
- \+/\- *theorem* le_bit1_bit1
- \+/\- *theorem* sle_one_bit0
- \+/\- *theorem* sle_one_bit1
- \+/\- *theorem* sle_bit0_bit0
- \+/\- *theorem* sle_bit0_bit1
- \+/\- *theorem* sle_bit1_bit0
- \+/\- *theorem* sle_bit1_bit1
- \+/\- *theorem* clear_denom_lt
- \+/\- *theorem* clear_denom_le
- \+/\- *theorem* rat_cast_div
- \+/\- *theorem* int_cast_neg
- \+/\- *theorem* rat_cast_neg
- \+/\- *theorem* nat_cast_ne
- \+/\- *theorem* int_cast_ne
- \+/\- *theorem* rat_cast_ne

modified test/ring.lean



## [2020-10-18 23:06:55](https://github.com/leanprover-community/mathlib/commit/1ac5d82)
fix(logic/nontrivial): change tactic doc entry tag to more common "type class" ([#4676](https://github.com/leanprover-community/mathlib/pull/4676))
#### Estimated changes
modified src/logic/nontrivial.lean



## [2020-10-18 21:34:51](https://github.com/leanprover-community/mathlib/commit/61e1111)
chore(linear_algebra/affine_space): introduce notation for `affine_map` ([#4675](https://github.com/leanprover-community/mathlib/pull/4675))
#### Estimated changes
modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.combo_affine_apply
- \+/\- *lemma* convex.affine_preimage
- \+/\- *lemma* convex.affine_image
- \+/\- *lemma* convex_on.comp_affine_map
- \+/\- *lemma* concave_on.comp_affine_map
- \+/\- *lemma* convex.combo_affine_apply
- \+/\- *lemma* convex.affine_preimage
- \+/\- *lemma* convex.affine_image
- \+/\- *lemma* convex_on.comp_affine_map
- \+/\- *lemma* concave_on.comp_affine_map

modified src/analysis/convex/extrema.lean

modified src/analysis/normed_space/mazur_ulam.lean
- \+/\- *def* to_affine_map
- \+/\- *def* to_affine_map

modified src/geometry/euclidean/basic.lean
- \+/\- *def* orthogonal_projection
- \+/\- *def* orthogonal_projection

modified src/linear_algebra/affine_space/basic.lean
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* map_vadd
- \+/\- *lemma* linear_map_vsub
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coe_zero
- \+/\- *lemma* zero_linear
- \+/\- *lemma* coe_add
- \+/\- *lemma* add_linear
- \+/\- *lemma* vadd_apply
- \+/\- *lemma* vsub_apply
- \+/\- *lemma* coe_fst
- \+/\- *lemma* fst_linear
- \+/\- *lemma* coe_snd
- \+/\- *lemma* snd_linear
- \+/\- *lemma* coe_comp
- \+/\- *lemma* comp_apply
- \+/\- *lemma* comp_id
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_assoc
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* apply_line_map
- \+/\- *lemma* comp_line_map
- \+/\- *lemma* decomp
- \+/\- *lemma* decomp'
- \+/\- *lemma* image_interval
- \+/\- *lemma* coe_smul
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* map_vadd
- \+/\- *lemma* linear_map_vsub
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coe_zero
- \+/\- *lemma* zero_linear
- \+/\- *lemma* coe_add
- \+/\- *lemma* add_linear
- \+/\- *lemma* vadd_apply
- \+/\- *lemma* vsub_apply
- \+/\- *lemma* coe_fst
- \+/\- *lemma* fst_linear
- \+/\- *lemma* coe_snd
- \+/\- *lemma* snd_linear
- \+/\- *lemma* coe_comp
- \+/\- *lemma* comp_apply
- \+/\- *lemma* comp_id
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_assoc
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* apply_line_map
- \+/\- *lemma* comp_line_map
- \+/\- *lemma* decomp
- \+/\- *lemma* decomp'
- \+/\- *lemma* image_interval
- \+/\- *lemma* coe_smul
- \+/\- *def* to_affine_map
- \+/\- *def* const
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* line_map
- \+/\- *def* homothety
- \+/\- *def* homothety_hom
- \+/\- *def* homothety_affine
- \+/\- *def* to_affine_map
- \+/\- *def* const
- \+/\- *def* fst
- \+/\- *def* snd
- \+/\- *def* id
- \+/\- *def* comp
- \+/\- *def* line_map
- \+/\- *def* homothety
- \+/\- *def* homothety_hom
- \+/\- *def* homothety_affine

modified src/linear_algebra/affine_space/combination.lean
- \+/\- *def* affine_combination
- \+/\- *def* weighted_vsub_of_point
- \+/\- *def* affine_combination
- \+/\- *def* weighted_vsub_of_point

modified src/topology/algebra/affine.lean
- \+/\- *lemma* continuous_iff
- \+/\- *lemma* continuous_iff



## [2020-10-18 21:34:49](https://github.com/leanprover-community/mathlib/commit/4faf2e2)
chore(order/filter): use implicit arguments in `tendsto_at_top` etc ([#4672](https://github.com/leanprover-community/mathlib/pull/4672))
Also weaken some assumptions from a decidable linear order to a linear order.
#### Estimated changes
modified src/data/real/hyperreal.lean

modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* tendsto_at_top
- \+/\- *lemma* tendsto_at_bot
- \+ *lemma* tendsto_at_top_mul_at_top
- \+/\- *lemma* tendsto_at_top'
- \+/\- *lemma* tendsto_at_bot'
- \+/\- *lemma* tendsto_at_top_at_top
- \+/\- *lemma* tendsto_at_top_at_bot
- \+/\- *lemma* tendsto_at_bot_at_top
- \+/\- *lemma* tendsto_at_bot_at_bot
- \+/\- *lemma* tendsto_at_top
- \+/\- *lemma* tendsto_at_bot
- \+/\- *lemma* tendsto_at_top'
- \+/\- *lemma* tendsto_at_bot'
- \+/\- *lemma* tendsto_at_top_at_top
- \+/\- *lemma* tendsto_at_top_at_bot
- \+/\- *lemma* tendsto_at_bot_at_top
- \+/\- *lemma* tendsto_at_bot_at_bot

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/ordered.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* tendsto_at_top
- \+/\- *theorem* tendsto_at_top

modified src/topology/sequences.lean

modified src/topology/uniform_space/cauchy.lean



## [2020-10-18 21:34:47](https://github.com/leanprover-community/mathlib/commit/392d52c)
chore(order/filter): run `dsimp only [set.mem_set_of_eq]` in `filter_upwards` ([#4671](https://github.com/leanprover-community/mathlib/pull/4671))
#### Estimated changes
modified src/analysis/asymptotics.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/local_extr.lean

modified src/analysis/calculus/specific_functions.lean

modified src/analysis/special_functions/exp_log.lean

modified src/measure_theory/bochner_integration.lean

modified src/measure_theory/interval_integral.lean

modified src/measure_theory/l1_space.lean

modified src/measure_theory/prod.lean

modified src/order/filter/basic.lean



## [2020-10-18 19:21:09](https://github.com/leanprover-community/mathlib/commit/93b7e63)
feat(analysis/special_functions/trigonometric): range_{exp,cos,sin} ([#4595](https://github.com/leanprover-community/mathlib/pull/4595))
#### Estimated changes
modified src/algebra/ordered_ring.lean

modified src/algebra/quadratic_discriminant.lean

modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* range_exp
- \+ *lemma* log_surjective
- \+ *lemma* range_log

modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* range_cos_infinite
- \+ *lemma* range_sin_infinite
- \+ *lemma* range_exp
- \+ *lemma* exists_pow_nat_eq
- \+ *lemma* exists_eq_mul_self
- \+ *lemma* cos_surjective
- \+ *lemma* range_cos
- \+ *lemma* sin_surjective
- \+ *lemma* range_sin

modified src/data/set/finite.lean
- \+ *theorem* infinite_of_infinite_image



## [2020-10-18 16:02:22](https://github.com/leanprover-community/mathlib/commit/fee2dfa)
chore(analysis/calculus/fderiv): golf a lemma using new `nontriviality` ([#4584](https://github.com/leanprover-community/mathlib/pull/4584))
#### Estimated changes
modified src/analysis/calculus/fderiv.lean

modified src/linear_algebra/linear_independent.lean

modified src/topology/algebra/module.lean



## [2020-10-18 09:59:52](https://github.com/leanprover-community/mathlib/commit/e21dc7a)
feat(topology/subset_properties): define `filter.cocompact` ([#4666](https://github.com/leanprover-community/mathlib/pull/4666))
The filter of complements to compact subsets.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* tendsto_norm_cocompact_at_top
- \+ *lemma* continuous.norm

modified src/data/set/basic.lean
- \+ *lemma* nonempty_insert

modified src/topology/algebra/ordered.lean
- \+/\- *lemma* is_compact.exists_Sup_image_eq
- \+/\- *lemma* eq_Icc_of_connected_compact
- \+ *lemma* continuous.exists_forall_le
- \+ *lemma* continuous.exists_forall_ge
- \+/\- *lemma* is_compact.exists_Sup_image_eq
- \+/\- *lemma* eq_Icc_of_connected_compact

modified src/topology/metric_space/basic.lean
- \+ *lemma* tendsto_dist_right_cocompact_at_top
- \+ *lemma* tendsto_dist_left_cocompact_at_top

modified src/topology/separation.lean

modified src/topology/subset_properties.lean
- \+ *lemma* is_compact.insert
- \+ *lemma* filter.has_basis_cocompact
- \+ *lemma* filter.mem_cocompact
- \+ *lemma* filter.mem_cocompact'
- \+ *lemma* is_compact.compl_mem_cocompact
- \+ *def* filter.cocompact



## [2020-10-18 05:51:33](https://github.com/leanprover-community/mathlib/commit/cc32876)
chore(analysis/normed_space/basic): add `continuous_at.inv'`, `continuous.div` etc ([#4667](https://github.com/leanprover-community/mathlib/pull/4667))
Also add `continuous_on_(cos/sin)`.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* continuous_at.inv'
- \+ *lemma* continuous_within_at.inv'
- \+ *lemma* continuous.inv'
- \+ *lemma* continuous_on.inv'
- \+/\- *lemma* filter.tendsto.div_const
- \+ *lemma* continuous_within_at.div
- \+ *lemma* continuous_on.div
- \+ *lemma* continuous.div
- \+/\- *lemma* filter.tendsto.div_const

modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* continuous_on_sin
- \+ *lemma* continuous_on_cos
- \+ *lemma* continuous_on_cos
- \+/\- *lemma* continuous_tan
- \+/\- *lemma* continuous_tan



## [2020-10-18 04:29:30](https://github.com/leanprover-community/mathlib/commit/db06b67)
feat(measure_theory/prod): product measures and Fubini's theorem ([#4590](https://github.com/leanprover-community/mathlib/pull/4590))
* Define the product measure of two σ-finite measures.
* Prove Tonelli's theorem.
* Prove Fubini's theorem.
#### Estimated changes
modified docs/overview.yaml

modified docs/references.bib

modified docs/undergrad.yaml

modified src/data/indicator_function.lean
- \+ *lemma* indicator_mul_left
- \+ *lemma* indicator_mul_right

modified src/measure_theory/measure_space.lean

created src/measure_theory/prod.lean
- \+ *lemma* generate_from_prod
- \+ *lemma* is_pi_system_prod
- \+ *lemma* measurable_measure_prod_mk_left_finite
- \+ *lemma* measurable_measure_prod_mk_left
- \+ *lemma* measurable_measure_prod_mk_right
- \+ *lemma* measurable.map_prod_mk_left
- \+ *lemma* measurable.map_prod_mk_right
- \+ *lemma* measurable.lintegral_prod_right'
- \+ *lemma* measurable.lintegral_prod_right
- \+ *lemma* measurable.lintegral_prod_left'
- \+ *lemma* measurable.lintegral_prod_left
- \+ *lemma* is_measurable_integrable
- \+ *lemma* measurable.integral_prod_right
- \+ *lemma* measurable.integral_prod_right'
- \+ *lemma* measurable.integral_prod_left
- \+ *lemma* measurable.integral_prod_left'
- \+ *lemma* prod_apply
- \+ *lemma* prod_prod
- \+ *lemma* ae_measure_lt_top
- \+ *lemma* integrable_measure_prod_mk_left
- \+ *lemma* measure_prod_null
- \+ *lemma* measure_ae_null_of_prod_null
- \+ *lemma* ae_ae_of_ae_prod
- \+ *lemma* prod_unique
- \+ *lemma* prod_eq
- \+ *lemma* prod_swap
- \+ *lemma* prod_apply_symm
- \+ *lemma* prod_restrict
- \+ *lemma* prod_dirac
- \+ *lemma* dirac_prod
- \+ *lemma* dirac_prod_dirac
- \+ *lemma* prod_sum
- \+ *lemma* sum_prod
- \+ *lemma* prod_add
- \+ *lemma* add_prod
- \+ *lemma* lintegral_prod_swap
- \+ *lemma* lintegral_prod
- \+ *lemma* lintegral_prod_symm
- \+ *lemma* lintegral_lintegral
- \+ *lemma* lintegral_lintegral_symm
- \+ *lemma* lintegral_lintegral_swap
- \+ *lemma* integrable.swap
- \+ *lemma* integrable_swap_iff
- \+ *lemma* has_finite_integral_prod_iff
- \+ *lemma* integrable_prod_iff
- \+ *lemma* integrable_prod_iff'
- \+ *lemma* integrable.prod_left_ae
- \+ *lemma* integrable.prod_right_ae
- \+ *lemma* integrable.integral_norm_prod_left
- \+ *lemma* integrable.integral_norm_prod_right
- \+ *lemma* integrable.integral_prod_left
- \+ *lemma* integrable.integral_prod_right
- \+ *lemma* integral_prod_swap
- \+ *lemma* integral_fn_integral_add
- \+ *lemma* integral_fn_integral_sub
- \+ *lemma* lintegral_fn_integral_sub
- \+ *lemma* integral_integral_add
- \+ *lemma* integral_integral_add'
- \+ *lemma* integral_integral_sub
- \+ *lemma* integral_integral_sub'
- \+ *lemma* continuous_integral_integral
- \+ *lemma* integral_prod
- \+ *lemma* integral_prod_symm
- \+ *lemma* integral_integral
- \+ *lemma* integral_integral_symm
- \+ *lemma* integral_integral_swap



## [2020-10-18 01:46:58](https://github.com/leanprover-community/mathlib/commit/c7782bb)
chore(scripts): update nolints.txt ([#4665](https://github.com/leanprover-community/mathlib/pull/4665))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-18 01:46:56](https://github.com/leanprover-community/mathlib/commit/77dc679)
chore(data/set/intervals): more lemmas ([#4662](https://github.com/leanprover-community/mathlib/pull/4662))
#### Estimated changes
modified src/data/set/intervals/basic.lean
- \+ *lemma* Ioc_subset_Iic_self
- \+ *lemma* Ico_subset_Ici_self
- \+ *lemma* Ioo_union_left
- \+ *lemma* Ioo_union_right
- \+ *lemma* Ioc_union_left
- \+ *lemma* Ico_union_right
- \+/\- *lemma* Ici_top
- \+ *lemma* Iic_top
- \+ *lemma* Icc_top
- \+ *lemma* Ioc_top
- \+ *lemma* Iic_bot
- \+/\- *lemma* Ici_bot
- \+ *lemma* Icc_bot
- \+ *lemma* Ico_bot
- \+/\- *lemma* Ici_top
- \+/\- *lemma* Ici_bot



## [2020-10-18 01:46:53](https://github.com/leanprover-community/mathlib/commit/9585210)
chore(order/filter): add a few lemmas ([#4661](https://github.com/leanprover-community/mathlib/pull/4661))
#### Estimated changes
modified src/order/filter/at_top_bot.lean
- \+ *lemma* eventually_gt_at_top
- \+ *lemma* eventually_lt_at_bot
- \+ *lemma* at_top_basis_Ioi

modified src/order/filter/bases.lean
- \+ *lemma* has_basis.frequently_iff

modified src/order/filter/basic.lean
- \+/\- *lemma* eventually_sup
- \+ *lemma* tendsto_top
- \+/\- *lemma* eventually_sup



## [2020-10-18 01:46:51](https://github.com/leanprover-community/mathlib/commit/f990838)
chore(data/finsupp/basic): rename type variables ([#4624](https://github.com/leanprover-community/mathlib/pull/4624))
Use `M`, `N`, `P` for types with `has_zero`, `add_monoid`, or
`add_comm_monoid` structure, and `R`, `S` for types with at least
a `semiring` instance.
API change: `single_add_erase` and `erase_add_single` now use explicit arguments.
#### Estimated changes
modified src/data/finsupp/basic.lean
- \+/\- *lemma* zero_apply
- \+/\- *lemma* support_zero
- \+/\- *lemma* mem_support_iff
- \+/\- *lemma* not_mem_support_iff
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* support_eq_empty
- \+/\- *lemma* card_support_eq_zero
- \+/\- *lemma* finite_supp
- \+/\- *lemma* support_subset_iff
- \+/\- *lemma* single_apply
- \+/\- *lemma* single_eq_same
- \+/\- *lemma* single_eq_of_ne
- \+/\- *lemma* single_zero
- \+/\- *lemma* single_injective
- \+/\- *lemma* mem_support_single
- \+/\- *lemma* eq_single_iff
- \+/\- *lemma* single_eq_single_iff
- \+/\- *lemma* single_swap
- \+/\- *lemma* unique_single
- \+/\- *lemma* unique_ext
- \+/\- *lemma* unique_ext_iff
- \+/\- *lemma* unique_single_eq_iff
- \+/\- *lemma* support_eq_singleton
- \+/\- *lemma* support_eq_singleton'
- \+/\- *lemma* card_support_eq_one
- \+/\- *lemma* card_support_eq_one'
- \+/\- *lemma* on_finset_apply
- \+/\- *lemma* support_on_finset_subset
- \+/\- *lemma* map_range_apply
- \+/\- *lemma* map_range_zero
- \+/\- *lemma* support_map_range
- \+/\- *lemma* map_range_single
- \+/\- *lemma* support_emb_domain
- \+/\- *lemma* emb_domain_zero
- \+/\- *lemma* emb_domain_apply
- \+/\- *lemma* emb_domain_notin_range
- \+/\- *lemma* emb_domain_injective
- \+/\- *lemma* emb_domain_inj
- \+/\- *lemma* emb_domain_eq_zero
- \+/\- *lemma* support_zip_with
- \+/\- *lemma* support_erase
- \+/\- *lemma* erase_same
- \+/\- *lemma* erase_ne
- \+/\- *lemma* erase_single
- \+/\- *lemma* erase_single_ne
- \+/\- *lemma* erase_zero
- \+/\- *lemma* prod_of_support_subset
- \+/\- *lemma* prod_fintype
- \+/\- *lemma* prod_single_index
- \+/\- *lemma* prod_map_range_index
- \+/\- *lemma* prod_zero_index
- \+/\- *lemma* prod_comm
- \+/\- *lemma* prod_ite_eq
- \+/\- *lemma* prod_ite_eq'
- \+/\- *lemma* prod_pow
- \+/\- *lemma* on_finset_sum
- \+/\- *lemma* add_apply
- \+/\- *lemma* support_add
- \+/\- *lemma* support_add_eq
- \+/\- *lemma* single_add
- \+/\- *lemma* eval_add_hom_apply
- \+/\- *lemma* single_add_erase
- \+/\- *lemma* erase_add_single
- \+/\- *lemma* erase_add
- \+/\- *lemma* induction₂
- \+/\- *lemma* add_hom_ext
- \+/\- *lemma* map_range_add
- \+/\- *lemma* single_multiset_sum
- \+/\- *lemma* single_finset_sum
- \+/\- *lemma* single_sum
- \+/\- *lemma* prod_neg_index
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+/\- *lemma* support_neg
- \+/\- *lemma* sum_apply
- \+/\- *lemma* support_sum
- \+/\- *lemma* sum_zero
- \+ *lemma* prod_mul
- \+ *lemma* prod_inv
- \+/\- *lemma* sum_sub
- \+/\- *lemma* prod_add_index
- \+/\- *lemma* lift_add_hom_apply
- \+/\- *lemma* lift_add_hom_symm_apply
- \+/\- *lemma* lift_add_hom_symm_apply_apply
- \+/\- *lemma* lift_add_hom_single_add_hom
- \+/\- *lemma* sum_single
- \+/\- *lemma* prod_emb_domain
- \+/\- *lemma* prod_finset_sum_index
- \+/\- *lemma* multiset_map_sum
- \+/\- *lemma* multiset_sum_sum
- \+/\- *lemma* map_range_multiset_sum
- \+/\- *lemma* map_range_finset_sum
- \+/\- *lemma* map_domain_apply
- \+/\- *lemma* map_domain_notin_range
- \+/\- *lemma* map_domain_comp
- \+/\- *lemma* map_domain_single
- \+/\- *lemma* map_domain_zero
- \+/\- *lemma* map_domain_congr
- \+/\- *lemma* map_domain_add
- \+/\- *lemma* map_domain_finset_sum
- \+/\- *lemma* map_domain_sum
- \+/\- *lemma* map_domain_support
- \+/\- *lemma* prod_map_domain_index
- \+/\- *lemma* emb_domain_eq_map_domain
- \+/\- *lemma* prod_map_domain_index_inj
- \+/\- *lemma* map_domain_injective
- \+/\- *lemma* comap_domain_apply
- \+/\- *lemma* sum_comap_domain
- \+/\- *lemma* eq_zero_of_comap_domain_eq_zero
- \+/\- *lemma* map_domain_comap_domain
- \+/\- *lemma* filter_zero
- \+/\- *lemma* filter_pos_add_filter_neg
- \+/\- *lemma* support_subtype_domain
- \+/\- *lemma* subtype_domain_apply
- \+/\- *lemma* subtype_domain_zero
- \+/\- *lemma* subtype_domain_eq_zero_iff'
- \+/\- *lemma* subtype_domain_eq_zero_iff
- \+/\- *lemma* prod_subtype_domain_index
- \+/\- *lemma* subtype_domain_add
- \+/\- *lemma* filter_add
- \+/\- *lemma* subtype_domain_sum
- \+/\- *lemma* subtype_domain_finsupp_sum
- \+/\- *lemma* filter_sum
- \+/\- *lemma* subtype_domain_neg
- \+/\- *lemma* subtype_domain_sub
- \+/\- *lemma* prod_to_multiset
- \+/\- *lemma* mem_support_multiset_sum
- \+/\- *lemma* mem_support_finset_sum
- \+/\- *lemma* sum_curry_index
- \+/\- *lemma* filter_curry
- \+/\- *lemma* support_curry
- \+/\- *lemma* comap_smul_single
- \+/\- *lemma* comap_smul_apply
- \+/\- *lemma* smul_apply'
- \+/\- *lemma* coe_leval'
- \+/\- *lemma* coe_leval
- \+/\- *lemma* support_smul
- \+/\- *lemma* filter_smul
- \+/\- *lemma* map_domain_smul
- \+/\- *lemma* smul_single
- \+/\- *lemma* smul_single'
- \+/\- *lemma* smul_single_one
- \+/\- *lemma* lhom_ext'
- \+/\- *lemma* lhom_ext
- \+/\- *lemma* smul_apply
- \+/\- *lemma* sum_smul_index
- \+/\- *lemma* sum_smul_index'
- \+/\- *lemma* sum_mul
- \+/\- *lemma* mul_sum
- \+/\- *lemma* mul_equiv.map_finsupp_prod
- \+/\- *lemma* monoid_hom.map_finsupp_prod
- \+/\- *lemma* ring_hom.map_finsupp_sum
- \+/\- *lemma* ring_hom.map_finsupp_prod
- \+/\- *lemma* sigma_sum
- \+/\- *lemma* le_iff
- \+/\- *lemma* add_eq_zero_iff
- \+/\- *lemma* to_multiset_to_finsupp
- \+/\- *lemma* to_multiset_strict_mono
- \+/\- *lemma* sum_id_lt_of_lt
- \+/\- *lemma* lt_wf
- \+/\- *lemma* mem_antidiagonal_support
- \+/\- *lemma* antidiagonal_zero
- \+/\- *lemma* swap_mem_antidiagonal_support
- \+/\- *lemma* finite_le_nat
- \+/\- *lemma* finite_lt_nat
- \+/\- *lemma* zero_apply
- \+/\- *lemma* support_zero
- \+/\- *lemma* mem_support_iff
- \+/\- *lemma* not_mem_support_iff
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* support_eq_empty
- \+/\- *lemma* card_support_eq_zero
- \+/\- *lemma* finite_supp
- \+/\- *lemma* support_subset_iff
- \+/\- *lemma* single_apply
- \+/\- *lemma* single_eq_same
- \+/\- *lemma* single_eq_of_ne
- \+/\- *lemma* single_zero
- \+/\- *lemma* single_injective
- \+/\- *lemma* eq_single_iff
- \+/\- *lemma* single_eq_single_iff
- \+/\- *lemma* single_swap
- \+/\- *lemma* unique_single
- \+/\- *lemma* unique_ext
- \+/\- *lemma* unique_ext_iff
- \+/\- *lemma* unique_single_eq_iff
- \+/\- *lemma* support_eq_singleton
- \+/\- *lemma* support_eq_singleton'
- \+/\- *lemma* card_support_eq_one
- \+/\- *lemma* card_support_eq_one'
- \+/\- *lemma* on_finset_apply
- \+/\- *lemma* support_on_finset_subset
- \+/\- *lemma* map_range_apply
- \+/\- *lemma* map_range_zero
- \+/\- *lemma* support_map_range
- \+/\- *lemma* map_range_single
- \+/\- *lemma* support_emb_domain
- \+/\- *lemma* emb_domain_zero
- \+/\- *lemma* emb_domain_apply
- \+/\- *lemma* emb_domain_notin_range
- \+/\- *lemma* emb_domain_injective
- \+/\- *lemma* emb_domain_inj
- \+/\- *lemma* emb_domain_eq_zero
- \+/\- *lemma* support_zip_with
- \+/\- *lemma* support_erase
- \+/\- *lemma* erase_same
- \+/\- *lemma* erase_ne
- \+/\- *lemma* erase_single
- \+/\- *lemma* erase_single_ne
- \+/\- *lemma* erase_zero
- \+/\- *lemma* prod_of_support_subset
- \+/\- *lemma* prod_fintype
- \+/\- *lemma* prod_single_index
- \+/\- *lemma* prod_map_range_index
- \+/\- *lemma* prod_zero_index
- \+/\- *lemma* prod_comm
- \+/\- *lemma* prod_ite_eq
- \+/\- *lemma* prod_ite_eq'
- \+/\- *lemma* prod_pow
- \+/\- *lemma* on_finset_sum
- \+/\- *lemma* add_apply
- \+/\- *lemma* support_add
- \+/\- *lemma* support_add_eq
- \+/\- *lemma* single_add
- \+/\- *lemma* eval_add_hom_apply
- \+/\- *lemma* single_add_erase
- \+/\- *lemma* erase_add_single
- \+/\- *lemma* erase_add
- \+/\- *lemma* induction₂
- \+/\- *lemma* add_hom_ext
- \+/\- *lemma* map_range_add
- \+/\- *lemma* single_multiset_sum
- \+/\- *lemma* single_finset_sum
- \+/\- *lemma* single_sum
- \+/\- *lemma* prod_neg_index
- \+/\- *lemma* neg_apply
- \+/\- *lemma* sub_apply
- \+/\- *lemma* support_neg
- \+/\- *lemma* sum_apply
- \+/\- *lemma* support_sum
- \+/\- *lemma* sum_zero
- \- *lemma* sum_add
- \- *lemma* sum_neg
- \+/\- *lemma* sum_sub
- \+/\- *lemma* prod_add_index
- \+/\- *lemma* lift_add_hom_apply
- \+/\- *lemma* lift_add_hom_symm_apply
- \+/\- *lemma* lift_add_hom_symm_apply_apply
- \+/\- *lemma* lift_add_hom_single_add_hom
- \+/\- *lemma* sum_single
- \+/\- *lemma* prod_emb_domain
- \+/\- *lemma* prod_finset_sum_index
- \+/\- *lemma* multiset_map_sum
- \+/\- *lemma* multiset_sum_sum
- \+/\- *lemma* map_range_multiset_sum
- \+/\- *lemma* map_range_finset_sum
- \+/\- *lemma* map_domain_apply
- \+/\- *lemma* map_domain_notin_range
- \+/\- *lemma* map_domain_comp
- \+/\- *lemma* map_domain_single
- \+/\- *lemma* map_domain_zero
- \+/\- *lemma* map_domain_congr
- \+/\- *lemma* map_domain_add
- \+/\- *lemma* map_domain_finset_sum
- \+/\- *lemma* map_domain_sum
- \+/\- *lemma* map_domain_support
- \+/\- *lemma* prod_map_domain_index
- \+/\- *lemma* emb_domain_eq_map_domain
- \+/\- *lemma* prod_map_domain_index_inj
- \+/\- *lemma* map_domain_injective
- \+/\- *lemma* comap_domain_apply
- \+/\- *lemma* sum_comap_domain
- \+/\- *lemma* eq_zero_of_comap_domain_eq_zero
- \+/\- *lemma* map_domain_comap_domain
- \+/\- *lemma* filter_zero
- \+/\- *lemma* filter_pos_add_filter_neg
- \+/\- *lemma* support_subtype_domain
- \+/\- *lemma* subtype_domain_apply
- \+/\- *lemma* subtype_domain_zero
- \+/\- *lemma* subtype_domain_eq_zero_iff'
- \+/\- *lemma* subtype_domain_eq_zero_iff
- \+/\- *lemma* prod_subtype_domain_index
- \+/\- *lemma* subtype_domain_add
- \+/\- *lemma* filter_add
- \+/\- *lemma* subtype_domain_sum
- \+/\- *lemma* subtype_domain_finsupp_sum
- \+/\- *lemma* filter_sum
- \+/\- *lemma* subtype_domain_neg
- \+/\- *lemma* subtype_domain_sub
- \+/\- *lemma* prod_to_multiset
- \+/\- *lemma* mem_support_multiset_sum
- \+/\- *lemma* mem_support_finset_sum
- \+/\- *lemma* mem_support_single
- \+/\- *lemma* sum_curry_index
- \+/\- *lemma* filter_curry
- \+/\- *lemma* support_curry
- \+/\- *lemma* comap_smul_single
- \+/\- *lemma* comap_smul_apply
- \+/\- *lemma* smul_apply'
- \+/\- *lemma* coe_leval'
- \+/\- *lemma* coe_leval
- \+/\- *lemma* support_smul
- \+/\- *lemma* filter_smul
- \+/\- *lemma* map_domain_smul
- \+/\- *lemma* smul_single
- \+/\- *lemma* smul_single'
- \+/\- *lemma* smul_single_one
- \+/\- *lemma* lhom_ext'
- \+/\- *lemma* lhom_ext
- \+/\- *lemma* smul_apply
- \+/\- *lemma* sum_smul_index
- \+/\- *lemma* sum_smul_index'
- \+/\- *lemma* sum_mul
- \+/\- *lemma* mul_sum
- \+/\- *lemma* mul_equiv.map_finsupp_prod
- \+/\- *lemma* monoid_hom.map_finsupp_prod
- \+/\- *lemma* ring_hom.map_finsupp_sum
- \+/\- *lemma* ring_hom.map_finsupp_prod
- \+/\- *lemma* sigma_sum
- \+/\- *lemma* le_iff
- \+/\- *lemma* add_eq_zero_iff
- \+/\- *lemma* to_multiset_to_finsupp
- \+/\- *lemma* to_multiset_strict_mono
- \+/\- *lemma* sum_id_lt_of_lt
- \+/\- *lemma* lt_wf
- \+/\- *lemma* mem_antidiagonal_support
- \+/\- *lemma* antidiagonal_zero
- \+/\- *lemma* swap_mem_antidiagonal_support
- \+/\- *lemma* finite_le_nat
- \+/\- *lemma* finite_lt_nat
- \+/\- *theorem* mem_frange
- \+/\- *theorem* zero_not_mem_frange
- \+/\- *theorem* frange_single
- \+/\- *theorem* mem_frange
- \+/\- *theorem* zero_not_mem_frange
- \+/\- *theorem* frange_single
- \+/\- *def* equiv_fun_on_fintype
- \+/\- *def* single
- \+/\- *def* on_finset
- \+/\- *def* map_range
- \+/\- *def* emb_domain
- \+/\- *def* zip_with
- \+/\- *def* erase
- \+/\- *def* sum
- \+/\- *def* prod
- \+/\- *def* single_add_hom
- \+/\- *def* eval_add_hom
- \+/\- *def* lift_add_hom
- \+/\- *def* map_range.add_monoid_hom
- \+/\- *def* map_domain
- \+/\- *def* comap_domain
- \+/\- *def* filter
- \+/\- *def* frange
- \+/\- *def* subtype_domain
- \+/\- *def* finsupp_prod_equiv
- \+/\- *def* comap_has_scalar
- \+/\- *def* comap_mul_action
- \+/\- *def* leval'
- \+/\- *def* leval
- \+/\- *def* restrict_support_equiv
- \+/\- *def* split
- \+/\- *def* split_comp
- \+/\- *def* antidiagonal
- \+/\- *def* equiv_fun_on_fintype
- \+/\- *def* single
- \+/\- *def* on_finset
- \+/\- *def* map_range
- \+/\- *def* emb_domain
- \+/\- *def* zip_with
- \+/\- *def* erase
- \+/\- *def* sum
- \+/\- *def* prod
- \+/\- *def* single_add_hom
- \+/\- *def* eval_add_hom
- \+/\- *def* lift_add_hom
- \+/\- *def* map_range.add_monoid_hom
- \+/\- *def* map_domain
- \+/\- *def* comap_domain
- \+/\- *def* filter
- \+/\- *def* frange
- \+/\- *def* subtype_domain
- \+/\- *def* finsupp_prod_equiv
- \+/\- *def* comap_has_scalar
- \+/\- *def* comap_mul_action
- \+/\- *def* leval'
- \+/\- *def* leval
- \+/\- *def* restrict_support_equiv
- \+/\- *def* split
- \+/\- *def* split_comp
- \+/\- *def* antidiagonal

modified src/data/polynomial/degree/basic.lean

modified src/linear_algebra/finsupp.lean



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
modified src/algebra/group/units.lean
- \+/\- *lemma* is_unit_of_subsingleton
- \+/\- *lemma* is_unit_of_subsingleton

modified src/analysis/asymptotics.lean
- \+ *lemma* is_o_of_subsingleton
- \+ *lemma* is_O_of_subsingleton

modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_of_subsingleton
- \+ *lemma* times_cont_diff_at_of_subsingleton
- \+ *lemma* times_cont_diff_within_at_of_subsingleton
- \+ *lemma* times_cont_diff_on_of_subsingleton

modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_of_subsingleton

modified src/analysis/normed_space/units.lean

modified src/data/polynomial/degree/basic.lean
- \+ *lemma* monic_of_subsingleton

modified src/linear_algebra/char_poly/coeff.lean

modified src/linear_algebra/linear_independent.lean

modified src/logic/nontrivial.lean
- \+ *def* myeq

modified test/nontriviality.lean
- \+ *lemma* subsingleton.set_empty_or_univ
- \+ *lemma* subsingleton.set_empty_or_univ'
- \+ *def* empty_or_univ



## [2020-10-18 01:46:47](https://github.com/leanprover-community/mathlib/commit/b977dba)
fix(solve_by_elim): handle multiple goals with different hypotheses ([#4519](https://github.com/leanprover-community/mathlib/pull/4519))
Previously `solve_by_elim*` would operate on multiple goals (only succeeding if it could close all of them, and performing backtracking across goals), however it would incorrectly only use the local context from the main goal. If other goals had different sets of hypotheses, ... various bad things could happen!
This PR arranges so that `solve_by_elim*` inspects the local context later, so it picks up the correct hypotheses.
#### Estimated changes
modified src/tactic/equiv_rw.lean

modified src/tactic/solve_by_elim.lean

modified src/tactic/suggest.lean

modified test/solve_by_elim.lean



## [2020-10-17 23:24:37](https://github.com/leanprover-community/mathlib/commit/13cd192)
feat(measure_theory/measure_space): added sub for measure_theory.measure ([#4639](https://github.com/leanprover-community/mathlib/pull/4639))
This definition is useful for proving the Lebesgue-Radon-Nikodym theorem for non-negative measures.
#### Estimated changes
modified src/data/real/ennreal.lean
- \+ *lemma* le_of_add_le_add_left

modified src/measure_theory/measure_space.lean
- \+ *lemma* le_zero_iff_eq'
- \+ *lemma* measure.le_of_add_le_add_left
- \+ *lemma* sub_def
- \+ *lemma* sub_eq_zero_of_le
- \+ *lemma* sub_apply
- \+ *lemma* sub_add_cancel_of_le

modified src/topology/instances/ennreal.lean
- \+ *lemma* tsum_sub



## [2020-10-17 23:24:35](https://github.com/leanprover-community/mathlib/commit/e83458c)
feat(algebra/group_power): Add mul/add variants of powers_hom and friends ([#4636](https://github.com/leanprover-community/mathlib/pull/4636))
#### Estimated changes
modified src/algebra/group_power/lemmas.lean
- \+ *lemma* powers_mul_hom_apply
- \+ *lemma* powers_mul_hom_symm_apply
- \+ *lemma* gpowers_mul_hom_apply
- \+ *lemma* gpowers_mul_hom_symm_apply
- \+ *lemma* multiples_add_hom_apply
- \+ *lemma* multiples_add_hom_symm_apply
- \+ *lemma* gmultiples_add_hom_apply
- \+ *lemma* gmultiples_add_hom_symm_apply
- \+ *def* powers_mul_hom
- \+ *def* gpowers_mul_hom
- \+ *def* multiples_add_hom
- \+ *def* gmultiples_add_hom



## [2020-10-17 23:24:33](https://github.com/leanprover-community/mathlib/commit/c83c28a)
feat(archive/imo): add IMO 2019 problem 4 ([#4482](https://github.com/leanprover-community/mathlib/pull/4482))
#### Estimated changes
created archive/imo/imo2019_q4.lean
- \+ *theorem* imo2019_q4_upper_bound
- \+ *theorem* imo2019_q4

modified src/algebra/big_operators/default.lean

created src/algebra/big_operators/enat.lean
- \+ *lemma* sum_nat_coe_enat

modified src/data/int/basic.lean
- \+ *lemma* exists_lt_and_lt_iff_not_dvd

modified src/data/nat/basic.lean
- \+ *lemma* exists_lt_and_lt_iff_not_dvd

modified src/data/nat/bitwise.lean
- \+ *lemma* bit_eq_zero

modified src/data/nat/enat.lean
- \+ *def* coe_hom

modified src/data/nat/multiplicity.lean
- \+/\- *lemma* multiplicity_one
- \+ *lemma* multiplicity_factorial_mul_succ
- \+ *lemma* multiplicity_factorial_mul
- \+ *lemma* multiplicity_two_factorial_lt
- \+/\- *lemma* multiplicity_one

modified src/order/basic.lean
- \+ *lemma* monotone.ne_of_lt_of_lt_nat
- \+ *lemma* monotone.ne_of_lt_of_lt_int



## [2020-10-17 20:50:45](https://github.com/leanprover-community/mathlib/commit/95d33ee)
refactor(algebra/quadratic_discriminant): drop linearity condition; cleanup ([#4656](https://github.com/leanprover-community/mathlib/pull/4656))
Renames:
- `discriminant_le_zero` to `discrim_le_zero`
- `discriminant_lt_zero` to `discrim_lt_zero`
#### Estimated changes
modified src/algebra/ordered_ring.lean
- \+ *lemma* exists_lt_mul_self
- \+ *lemma* exists_le_mul_self

modified src/algebra/quadratic_discriminant.lean
- \+/\- *lemma* quadratic_eq_zero_iff_discrim_eq_square
- \+/\- *lemma* quadratic_ne_zero_of_discrim_ne_square
- \+/\- *lemma* quadratic_eq_zero_iff
- \+ *lemma* exists_quadratic_eq_zero
- \+/\- *lemma* quadratic_eq_zero_iff_of_discrim_eq_zero
- \+ *lemma* discrim_le_zero
- \+ *lemma* discrim_lt_zero
- \- *lemma* exists_le_mul_self
- \- *lemma* exists_lt_mul_self
- \+/\- *lemma* quadratic_eq_zero_iff_discrim_eq_square
- \+/\- *lemma* quadratic_eq_zero_iff
- \- *lemma* exist_quadratic_eq_zero
- \+/\- *lemma* quadratic_eq_zero_iff_of_discrim_eq_zero
- \+/\- *lemma* quadratic_ne_zero_of_discrim_ne_square
- \- *lemma* discriminant_le_zero
- \- *lemma* discriminant_lt_zero
- \+/\- *def* discrim
- \+/\- *def* discrim



## [2020-10-17 20:50:43](https://github.com/leanprover-community/mathlib/commit/0367467)
chore(group/type_tags): Add missing simp lemmas ([#4651](https://github.com/leanprover-community/mathlib/pull/4651))
#### Estimated changes
modified src/algebra/group/type_tags.lean
- \+ *lemma* of_mul_symm_eq
- \+ *lemma* to_mul_symm_eq
- \+ *lemma* of_add_symm_eq
- \+ *lemma* to_add_symm_eq
- \+ *def* of_mul
- \+ *def* to_mul
- \+ *def* of_add
- \+ *def* to_add
- \- *def* additive.of_mul
- \- *def* additive.to_mul
- \- *def* multiplicative.of_add
- \- *def* multiplicative.to_add



## [2020-10-17 20:50:41](https://github.com/leanprover-community/mathlib/commit/0b9afe1)
chore(linear_algebra/affine_space): redefine `line_map`, add `to_affine_subspace` ([#4643](https://github.com/leanprover-community/mathlib/pull/4643))
* now `line_map` takes two points on the line, not a point and a
  direction, update/review lemmas;
* add `submodule.to_affine_subspace`;
* add `affine_map.fst` and `affine_map.snd`;
* prove that an affine map `ℝ → ℝ` sends an unordered interval to an unordered interval.
#### Estimated changes
modified src/analysis/convex/basic.lean

modified src/analysis/convex/extrema.lean

modified src/data/set/function.lean
- \+ *theorem* maps_to_union
- \+ *theorem* maps_to_inter

modified src/linear_algebra/affine_space/basic.lean
- \+/\- *lemma* coe_to_affine_map
- \+/\- *lemma* to_affine_map_linear
- \+ *lemma* coe_fst
- \+ *lemma* fst_linear
- \+ *lemma* coe_snd
- \+ *lemma* snd_linear
- \+ *lemma* coe_line_map
- \+/\- *lemma* line_map_apply
- \+ *lemma* line_map_vadd_apply
- \+/\- *lemma* line_map_linear
- \+ *lemma* line_map_same
- \+/\- *lemma* line_map_apply_zero
- \+ *lemma* line_map_apply_one
- \+ *lemma* apply_line_map
- \+ *lemma* comp_line_map
- \+ *lemma* line_map_symm
- \+ *lemma* image_interval
- \+/\- *lemma* line_map_apply
- \+/\- *lemma* line_map_linear
- \- *lemma* line_map_zero
- \+/\- *lemma* line_map_apply_zero
- \- *lemma* affine_apply_line_map
- \- *lemma* affine_comp_line_map
- \- *lemma* line_map_vadd_neg
- \+/\- *lemma* coe_to_affine_map
- \+/\- *lemma* to_affine_map_linear
- \+ *def* to_affine_subspace
- \+/\- *def* to_affine_map
- \+ *def* fst
- \+ *def* snd
- \+/\- *def* line_map
- \+/\- *def* line_map
- \+/\- *def* to_affine_map

modified src/order/basic.lean
- \+ *lemma* monotone.reflect_lt
- \- *lemma* reflect_lt

modified src/topology/algebra/affine.lean



## [2020-10-17 18:26:05](https://github.com/leanprover-community/mathlib/commit/589ebf5)
chore(algebra/*): add a few `prod.*` instances ([#4659](https://github.com/leanprover-community/mathlib/pull/4659))
* `prod.left_cancel_semigroup`;
* `prod_right_cancel_semigroup`;
* `prod.ordered_cancel_comm_monoid`;
* `ordered_comm_group`.
#### Estimated changes
modified src/algebra/group/prod.lean

modified src/algebra/ordered_group.lean



## [2020-10-17 18:26:02](https://github.com/leanprover-community/mathlib/commit/6e5b6cc)
feat(algebra/gcd_monoid, polynomial/field_division): generalizing `normalization_monoid` on polynomials ([#4655](https://github.com/leanprover-community/mathlib/pull/4655))
Defines a `normalization_monoid` instance on any `comm_group_with_zero`, including fields
Defines a `normalization_monoid` instance on `polynomial R` when `R` has a `normalization_monoid` instance
#### Estimated changes
modified src/algebra/gcd_monoid.lean
- \+ *lemma* coe_norm_unit

modified src/data/polynomial/field_division.lean
- \+/\- *lemma* coe_norm_unit
- \+ *lemma* leading_coeff_normalize
- \+ *lemma* coe_norm_unit_of_ne_zero
- \+ *lemma* normalize_monic
- \+/\- *lemma* coe_norm_unit

modified src/field_theory/algebraic_closure.lean

modified src/field_theory/splitting_field.lean



## [2020-10-17 18:26:00](https://github.com/leanprover-community/mathlib/commit/edddb3b)
feat(finsupp/basic): Add a variant of `prod_map_domain_index` for when f is injective ([#4645](https://github.com/leanprover-community/mathlib/pull/4645))
This puts much weaker restrictions on `h`, making this easier to apply in some situations
#### Estimated changes
modified src/data/finsupp/basic.lean
- \+ *lemma* prod_emb_domain
- \+ *lemma* prod_map_domain_index_inj



## [2020-10-17 18:25:58](https://github.com/leanprover-community/mathlib/commit/85eb12d)
feat(algebra/algebra/basic): product of two algebras ([#4632](https://github.com/leanprover-community/mathlib/pull/4632))
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* algebra_map_prod_apply



## [2020-10-17 18:25:57](https://github.com/leanprover-community/mathlib/commit/82ff1e5)
feat(algebra/algebra/subalgebra): subalgebra.subsingleton ([#4631](https://github.com/leanprover-community/mathlib/pull/4631))
#### Estimated changes
modified src/algebra/algebra/subalgebra.lean

modified src/order/bounded_lattice.lean
- \+ *lemma* subsingleton_of_top_le_bot



## [2020-10-17 18:25:55](https://github.com/leanprover-community/mathlib/commit/688157f)
feat(ring_theory/polynomial/content): definition of content + proof that it is multiplicative ([#4393](https://github.com/leanprover-community/mathlib/pull/4393))
Defines `polynomial.content` to be the `gcd` of the coefficients of a polynomial
Says a polynomial `is_primitive` if its content is 1
Proves that `(p * q).content = p.content * q.content
#### Estimated changes
modified src/algebra/ordered_group.lean
- \+ *lemma* with_bot.add_lt_add_iff_left
- \+ *lemma* with_bot.add_lt_add_iff_right

modified src/data/polynomial/erase_lead.lean
- \+ *lemma* erase_lead_nat_degree_lt_or_erase_lead_eq_zero

created src/ring_theory/polynomial/content.lean
- \+ *lemma* content_dvd_coeff
- \+ *lemma* content_C
- \+ *lemma* content_zero
- \+ *lemma* content_one
- \+ *lemma* content_X_mul
- \+ *lemma* content_X_pow
- \+ *lemma* content_X
- \+ *lemma* content_C_mul
- \+ *lemma* content_monomial
- \+ *lemma* content_eq_zero_iff
- \+ *lemma* normalize_content
- \+ *lemma* content_eq_gcd_range_of_lt
- \+ *lemma* content_eq_gcd_range_succ
- \+ *lemma* content_eq_gcd_leading_coeff_content_erase_lead
- \+ *lemma* dvd_content_iff_C_dvd
- \+ *lemma* C_content_dvd
- \+ *lemma* is_primitive_one
- \+ *lemma* is_primitive.ne_zero
- \+ *lemma* is_primitive.content_eq_one
- \+ *lemma* is_primitive_iff_is_unit_of_C_dvd
- \+ *lemma* eq_C_mul_primitive
- \+ *lemma* gcd_content_eq_of_dvd_sub
- \+ *lemma* content_mul_aux
- \+ *theorem* content_mul
- \+ *def* content
- \+ *def* is_primitive



## [2020-10-17 16:08:01](https://github.com/leanprover-community/mathlib/commit/b145c36)
feat(archive/imo): variant solution to IMO 1962 problem 4 ([#4640](https://github.com/leanprover-community/mathlib/pull/4640))
Continuation of a discussion at [#4518](https://github.com/leanprover-community/mathlib/pull/4518)
#### Estimated changes
modified archive/imo/imo1962_q4.lean
- \+ *lemma* formula
- \+ *lemma* solve_cos2x_0
- \+ *theorem* imo1962_q4'

modified src/algebra/group_power/basic.lean
- \+ *lemma* pow_eq_zero_iff



## [2020-10-17 13:41:26](https://github.com/leanprover-community/mathlib/commit/25d8343)
feat(topology/sheaves): an equivalent sheaf condition ([#4538](https://github.com/leanprover-community/mathlib/pull/4538))
Another condition equivalent to the sheaf condition: for every open cover `U`, `F.obj (supr U)` is the limit point of the diagram consisting of all the `F.obj V`, where `V ≤ U i` for some `i`.
This condition is particularly straightforward to state, and makes some proofs easier (however we don't do this here: just prove the equivalence with the "official" definition). It's particularly nice because there is no case splitting (depending on whether you're looking at single or double intersections) when checking the sheaf condition.
This is the statement Lurie uses in Spectral Algebraic Geometry.
Later I may propose that we make this the official definition, but I'll wait to see how it pans out in actual use, first. For now it's just provided as yet another equivalent version of the sheaf condition.
#### Estimated changes
modified docs/references.bib

modified src/topology/sheaves/sheaf.lean

created src/topology/sheaves/sheaf_condition/opens_le_cover.lean
- \+ *def* opens_le_cover
- \+ *def* index
- \+ *def* hom_to_index
- \+ *def* opens_le_cover_cocone
- \+ *def* sheaf_condition_opens_le_cover
- \+ *def* pairwise_to_opens_le_cover_obj
- \+ *def* pairwise_to_opens_le_cover_map
- \+ *def* pairwise_to_opens_le_cover
- \+ *def* pairwise_diagram_iso
- \+ *def* pairwise_cocone_iso
- \+ *def* sheaf_condition_opens_le_cover_equiv_sheaf_condition_pairwise_intersections
- \+ *def* sheaf_condition_equiv_sheaf_condition_opens_le_cover



## [2020-10-17 01:11:20](https://github.com/leanprover-community/mathlib/commit/ca2e6f4)
chore(scripts): update nolints.txt ([#4654](https://github.com/leanprover-community/mathlib/pull/4654))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-16 21:43:46](https://github.com/leanprover-community/mathlib/commit/7b9acd9)
chore(measure_theory/*): reflow long lines ([#4642](https://github.com/leanprover-community/mathlib/pull/4642))
Also do some minor golfing.
#### Estimated changes
modified src/measure_theory/ae_eq_fun.lean

modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_pos_part
- \+/\- *lemma* coe_neg_part
- \+/\- *lemma* integral_add_measure'
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_pos_part
- \+/\- *lemma* coe_neg_part
- \+/\- *lemma* integral_add_measure'

modified src/measure_theory/content.lean

modified src/measure_theory/giry_monad.lean

modified src/measure_theory/integration.lean
- \+/\- *lemma* supr_approx_apply
- \+/\- *lemma* supr_approx_apply

modified src/measure_theory/interval_integral.lean

modified src/measure_theory/l1_space.lean

modified src/measure_theory/lebesgue_measure.lean

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/measure_space.lean

modified src/measure_theory/set_integral.lean
- \+/\- *lemma* integral_on_add
- \+/\- *lemma* integral_on_le_integral_on_ae
- \+/\- *lemma* integral_on_add
- \+/\- *lemma* integral_on_le_integral_on_ae



## [2020-10-16 19:41:32](https://github.com/leanprover-community/mathlib/commit/189e538)
feat(geometry/manifold): stab at diffeomorphisms ([#4351](https://github.com/leanprover-community/mathlib/pull/4351))
#### Estimated changes
created src/geometry/manifold/diffeomorph.lean
- \+ *lemma* coe_eq_to_equiv
- \+ *def* diffeomorph

modified src/topology/homeomorph.lean



## [2020-10-16 18:01:28](https://github.com/leanprover-community/mathlib/commit/86b298f)
feat(category_theory/sites): grothendieck topologies ([#4577](https://github.com/leanprover-community/mathlib/pull/4577))
#### Estimated changes
created src/category_theory/sites/grothendieck.lean
- \+ *lemma* mem_sieves_iff_coe
- \+ *lemma* top_mem
- \+ *lemma* pullback_stable
- \+ *lemma* transitive
- \+ *lemma* covering_of_eq_top
- \+ *lemma* superset_covering
- \+ *lemma* intersection_covering
- \+ *lemma* intersection_covering_iff
- \+ *lemma* covers_iff
- \+ *lemma* covering_iff_covers_id
- \+ *lemma* arrow_max
- \+ *lemma* arrow_stable
- \+ *lemma* arrow_trans
- \+ *lemma* arrow_intersect
- \+ *lemma* trivial_covering
- \+ *lemma* is_glb_Inf
- \+ *lemma* trivial_eq_bot
- \+ *lemma* discrete_eq_top
- \+ *lemma* bot_covering
- \+ *lemma* top_covering
- \+ *lemma* bot_covers
- \+ *lemma* top_covers
- \+ *lemma* dense_covering
- \+ *lemma* right_ore_of_pullbacks
- \+ *def* covers
- \+ *def* trivial
- \+ *def* discrete
- \+ *def* dense
- \+ *def* right_ore_condition
- \+ *def* atomic

modified src/category_theory/sites/sieves.lean
- \+ *lemma* pullback_id
- \+ *lemma* pullback_eq_top_of_mem



## [2020-10-16 16:28:29](https://github.com/leanprover-community/mathlib/commit/0d9227f)
feat(category_theory/monad/kleisli): add Kleisli category of a monad ([#4542](https://github.com/leanprover-community/mathlib/pull/4542))
Adds the Kleisli category of a monad, and shows the Kleisli category for a lawful control monad is equivalent to the Kleisli category of its category-theoretic version.
Following discussion at https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/kleisli.20vs.20kleisli.
I'd appreciate suggestions for names more sensible than the ones already there.
#### Estimated changes
created src/category_theory/monad/kleisli.lean
- \+ *def* kleisli
- \+ *def* to_kleisli
- \+ *def* from_kleisli
- \+ *def* adj
- \+ *def* to_kleisli_comp_from_kleisli_iso_self

modified src/category_theory/monad/types.lean
- \+ *def* eq



## [2020-10-16 07:43:42](https://github.com/leanprover-community/mathlib/commit/f675a00)
chore(set_theory/zfc): split long lines ([#4641](https://github.com/leanprover-community/mathlib/pull/4641))
Also add `Set.subset_def` and rewrite `Set.mem_pair_sep` in tactic mode
#### Estimated changes
modified src/set_theory/zfc.lean
- \+ *lemma* subset_def
- \+/\- *theorem* definable.eq
- \+/\- *theorem* image.mk
- \+/\- *theorem* mem_image
- \+/\- *theorem* mem_pair_sep
- \+/\- *theorem* mem_map
- \+/\- *theorem* map_unique
- \+/\- *theorem* map_is_func
- \+/\- *theorem* sep_hom
- \+/\- *theorem* map_fval
- \+/\- *theorem* definable.eq
- \+/\- *theorem* image.mk
- \+/\- *theorem* mem_image
- \+/\- *theorem* mem_pair_sep
- \+/\- *theorem* mem_map
- \+/\- *theorem* map_unique
- \+/\- *theorem* map_is_func
- \+/\- *theorem* sep_hom
- \+/\- *theorem* map_fval
- \+/\- *def* eval_aux
- \+/\- *def* eval_aux



## [2020-10-16 05:34:17](https://github.com/leanprover-community/mathlib/commit/1cce606)
feat(analysis/special_functions/trigonometric): some lemmas ([#4638](https://github.com/leanprover-community/mathlib/pull/4638))
The following changes:
- `sin_sub_sin` and friends (sum-to-product lemmas) moved from `trigonometric` to the earlier file `exponential`.  (I think the distinction between the files is that `trigonometric` collects the facts that require either differentiation or the definition `pi`, whereas purely algebraic facts about trigonometry go in `exponential`?  For example the double-angle formula is in `exponential`).
- rewrite proof of `cos_lt_cos_of_nonneg_of_le_pi_div_two` to avoid dependence on `cos_eq_one_iff_of_lt_of_lt` (but not sure if the result is actually simpler, feel free to propose this be reverted)
- some new explicit values of trig functions, `cos (π / 3)` and similar
- correct a series of lemmas in the `complex` namespace that were stated for real arguments (presumably the author copy-pasted but forgot to rewrite)
- lemmas `sin_eq_zero_iff`, `cos_eq_cos_iff`, `sin_eq_sin_iff`
#### Estimated changes
modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* cos_pi_div_three
- \+ *lemma* square_cos_pi_div_six
- \+ *lemma* cos_pi_div_six
- \+ *lemma* sin_pi_div_six
- \+ *lemma* square_sin_pi_div_three
- \+ *lemma* sin_pi_div_three
- \+/\- *lemma* sin_add_pi
- \+/\- *lemma* sin_add_two_pi
- \+/\- *lemma* cos_add_two_pi
- \+/\- *lemma* sin_pi_sub
- \+/\- *lemma* cos_add_pi
- \+/\- *lemma* cos_pi_sub
- \+/\- *lemma* sin_add_pi_div_two
- \+/\- *lemma* sin_sub_pi_div_two
- \+/\- *lemma* sin_pi_div_two_sub
- \+/\- *lemma* cos_add_pi_div_two
- \+/\- *lemma* cos_sub_pi_div_two
- \+/\- *lemma* cos_pi_div_two_sub
- \+ *lemma* cos_eq_cos_iff
- \+ *lemma* sin_eq_sin_iff
- \+ *lemma* cos_eq_cos_iff
- \+ *lemma* sin_eq_sin_iff
- \+/\- *lemma* sin_add_pi
- \+/\- *lemma* sin_add_two_pi
- \+/\- *lemma* cos_add_two_pi
- \+/\- *lemma* sin_pi_sub
- \+/\- *lemma* cos_add_pi
- \+/\- *lemma* cos_pi_sub
- \+/\- *lemma* sin_add_pi_div_two
- \+/\- *lemma* sin_sub_pi_div_two
- \+/\- *lemma* sin_pi_div_two_sub
- \+/\- *lemma* cos_add_pi_div_two
- \+/\- *lemma* cos_sub_pi_div_two
- \+/\- *lemma* cos_pi_div_two_sub
- \+ *theorem* sin_eq_zero_iff
- \+ *theorem* sin_ne_zero_iff
- \- *theorem* sin_sub_sin
- \- *theorem* cos_sub_cos

modified src/data/complex/exponential.lean
- \+ *lemma* cos_add_cos
- \+ *lemma* sin_sub_sin
- \+ *lemma* cos_add_cos
- \+ *theorem* sin_sub_sin
- \+ *theorem* cos_sub_cos
- \+ *theorem* cos_sub_cos



## [2020-10-16 05:34:15](https://github.com/leanprover-community/mathlib/commit/e7b8421)
chore(linear_algebra/finsupp): turn `finsupp.lsum` into `add_equiv` ([#4597](https://github.com/leanprover-community/mathlib/pull/4597))
#### Estimated changes
modified src/data/finsupp/basic.lean
- \+ *lemma* lift_add_hom_symm_apply_apply
- \+ *lemma* lhom_ext'
- \+ *lemma* lhom_ext
- \- *lemma* hom_ext

modified src/linear_algebra/direct_sum/finsupp.lean
- \+/\- *def* finsupp_lequiv_direct_sum
- \+/\- *def* finsupp_lequiv_direct_sum

modified src/linear_algebra/finsupp.lean
- \+ *theorem* lsum_symm_apply
- \+/\- *def* lsum
- \+/\- *def* lsum



## [2020-10-16 03:25:42](https://github.com/leanprover-community/mathlib/commit/8280190)
chore(scripts): update nolints.txt ([#4637](https://github.com/leanprover-community/mathlib/pull/4637))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt

modified scripts/nolints.txt



## [2020-10-16 03:25:39](https://github.com/leanprover-community/mathlib/commit/cc14658)
chore(algebra/group_powers): Add missing lemmas ([#4635](https://github.com/leanprover-community/mathlib/pull/4635))
This part of the file defines four equivalences, but goes on to state lemmas about only one of them.
This provides the lemmas for the other three.
#### Estimated changes
modified src/algebra/group_power/lemmas.lean
- \+ *lemma* gpowers_hom_apply
- \+ *lemma* gpowers_hom_symm_apply
- \+ *lemma* multiples_hom_apply
- \+ *lemma* multiples_hom_symm_apply
- \+ *lemma* gmultiples_hom_apply
- \+ *lemma* gmultiples_hom_symm_apply
- \+ *lemma* monoid_hom.apply_mnat
- \+ *lemma* monoid_hom.ext_mnat
- \+ *lemma* monoid_hom.apply_mint
- \+ *lemma* monoid_hom.ext_mint
- \+ *lemma* add_monoid_hom.apply_nat
- \+ *lemma* add_monoid_hom.apply_int
- \- *lemma* mnat_monoid_hom_eq
- \- *lemma* mnat_monoid_hom_ext



## [2020-10-16 00:56:13](https://github.com/leanprover-community/mathlib/commit/dca1393)
feat(data/equiv/basic): add `equiv.set.compl` ([#4630](https://github.com/leanprover-community/mathlib/pull/4630))
Given an equivalence between two sets `e₀ : s ≃ t`, the set of
`e : α ≃ β` that agree with `e₀` on `s` is equivalent to `sᶜ ≃ tᶜ`.
Also add a bunch of lemmas to `data/set/function`; some of them are
used in the definition of `equiv.set.compl`.
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* subtype_congr_apply
- \+ *lemma* subtype_congr_symm_apply
- \+ *lemma* union_symm_apply_left
- \+ *lemma* union_symm_apply_right
- \+ *lemma* sum_compl_symm_apply
- \+ *lemma* sum_compl_symm_apply_compl
- \+ *def* set_prod_equiv_sigma

modified src/data/set/function.lean
- \+ *lemma* maps_to_iff_exists_map_subtype
- \+ *lemma* inj_on_of_injective
- \+ *lemma* surj_on_iff_exists_map_subtype
- \+ *lemma* surj_on.maps_to_compl
- \+ *lemma* maps_to.surj_on_compl
- \+ *lemma* bij_on.compl
- \+ *lemma* inv_on.mono
- \- *lemma* injective.inj_on
- \+/\- *theorem* maps_to_range
- \+ *theorem* surjective_maps_to_image_restrict
- \+ *theorem* maps_to.mem_iff
- \+/\- *theorem* left_inv_on.surj_on
- \+ *theorem* left_inv_on.maps_to
- \+ *theorem* left_inv_on.mono
- \+ *theorem* right_inv_on.maps_to
- \+ *theorem* right_inv_on.mono
- \+/\- *theorem* maps_to_range
- \+/\- *theorem* left_inv_on.surj_on



## [2020-10-16 00:56:11](https://github.com/leanprover-community/mathlib/commit/b0b61e6)
feat(order/category/omega-complete): omega-complete partial orders form a complete category ([#4397](https://github.com/leanprover-community/mathlib/pull/4397))
as discussed in [#4348](https://github.com/leanprover-community/mathlib/pull/4348).
#### Estimated changes
modified src/category_theory/limits/shapes/biproducts.lean

modified src/category_theory/limits/shapes/equalizers.lean
- \- *lemma* fork.of_ι_app_zero
- \- *lemma* fork.of_ι_app_one
- \- *lemma* cofork.of_π_app_zero
- \- *lemma* cofork.of_π_app_one

modified src/category_theory/limits/shapes/products.lean
- \- *lemma* fan.mk_π_app
- \- *lemma* cofan.mk_π_app
- \+/\- *def* fan.mk
- \+/\- *def* cofan.mk
- \+/\- *def* fan.mk
- \+/\- *def* cofan.mk

modified src/category_theory/limits/shapes/types.lean

modified src/order/category/omega_complete_partial_order.lean
- \+/\- *def* ωCPO
- \+ *def* product
- \+ *def* is_product
- \+ *def* equalizer_ι
- \+ *def* equalizer
- \+ *def* is_equalizer
- \+/\- *def* ωCPO

modified src/order/omega_complete_partial_order.lean
- \+ *theorem* congr_fun
- \+ *theorem* congr_arg
- \+ *def* subtype

modified src/order/preorder_hom.lean
- \+ *def* subtype.val



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
modified src/category_theory/abelian/non_preadditive.lean
- \+ *lemma* diag_σ
- \- *lemma* Δ_σ
- \- *lemma* Δ_map
- \+/\- *def* is_colimit_σ
- \+/\- *def* is_colimit_σ

modified src/category_theory/closed/cartesian.lean
- \+ *lemma* ev_naturality
- \+ *lemma* coev_naturality
- \+/\- *def* exp.adjunction
- \+/\- *def* ev
- \+/\- *def* coev
- \+/\- *def* exp.adjunction
- \+/\- *def* ev
- \+/\- *def* coev

modified src/category_theory/limits/connected.lean
- \+/\- *def* γ₂
- \+/\- *def* γ₁
- \+/\- *def* forget_cone
- \+/\- *def* γ₂
- \+/\- *def* γ₁
- \+/\- *def* forget_cone

modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* prod.comp_lift
- \+ *lemma* prod.comp_diag
- \+/\- *lemma* prod.map_fst
- \+/\- *lemma* prod.map_snd
- \+ *lemma* prod.map_id_id
- \+ *lemma* prod.lift_fst_snd
- \+/\- *lemma* prod.lift_map
- \+ *lemma* prod.lift_fst_comp_snd_comp
- \+ *lemma* prod.map_map
- \+ *lemma* prod.map_swap
- \+ *lemma* prod.map_comp_id
- \+ *lemma* prod.map_id_comp
- \+/\- *lemma* prod.diag_map
- \+/\- *lemma* prod.diag_map_fst_snd
- \+/\- *lemma* prod.diag_map_fst_snd_comp
- \+ *lemma* coprod.desc_comp
- \+ *lemma* coprod.diag_comp
- \+/\- *lemma* coprod.inl_map
- \+/\- *lemma* coprod.inr_map
- \+ *lemma* coprod.map_id_id
- \+ *lemma* coprod.desc_inl_inr
- \+/\- *lemma* coprod.map_desc
- \+ *lemma* coprod.desc_comp_inl_comp_inr
- \+ *lemma* coprod.map_map
- \+ *lemma* coprod.map_swap
- \+ *lemma* coprod.map_comp_id
- \+ *lemma* coprod.map_id_comp
- \+/\- *lemma* coprod.map_codiag
- \+/\- *lemma* coprod.map_inl_inr_codiag
- \+/\- *lemma* coprod.map_comp_inl_inr_codiag
- \+/\- *lemma* prod_comparison_natural
- \+/\- *lemma* inv_prod_comparison_map_fst
- \+/\- *lemma* inv_prod_comparison_map_snd
- \+/\- *lemma* prod_comparison_inv_natural
- \- *lemma* prod.lift_comp_comp
- \- *lemma* coprod.desc_comp_comp
- \- *lemma* prod.map_iso_hom
- \- *lemma* prod.map_iso_inv
- \+/\- *lemma* prod.diag_map
- \+/\- *lemma* prod.diag_map_fst_snd
- \- *lemma* prod.diag_map_comp
- \+/\- *lemma* prod.diag_map_fst_snd_comp
- \- *lemma* coprod.map_iso_hom
- \- *lemma* coprod.map_iso_inv
- \+/\- *lemma* prod.map_fst
- \+/\- *lemma* prod.map_snd
- \- *lemma* prod_map_id_id
- \- *lemma* prod_lift_fst_snd
- \- *lemma* prod_map_map
- \- *lemma* prod_map_comp_id
- \- *lemma* prod_map_id_comp
- \+/\- *lemma* prod.lift_map
- \+/\- *lemma* coprod.inl_map
- \+/\- *lemma* coprod.inr_map
- \- *lemma* coprod_map_id_id
- \- *lemma* coprod_desc_inl_inr
- \- *lemma* coprod_map_map
- \- *lemma* coprod_map_comp_id
- \- *lemma* coprod_map_id_comp
- \+/\- *lemma* coprod.map_desc
- \+/\- *lemma* coprod.map_codiag
- \+/\- *lemma* coprod.map_inl_inr_codiag
- \- *lemma* coprod.map_comp_codiag
- \+/\- *lemma* coprod.map_comp_inl_inr_codiag
- \+/\- *lemma* prod_comparison_natural
- \+/\- *lemma* inv_prod_comparison_map_fst
- \+/\- *lemma* inv_prod_comparison_map_snd
- \+/\- *lemma* prod_comparison_inv_natural
- \+ *def* prod.map
- \+ *def* coprod.map
- \+ *def* prod.map_iso
- \+ *def* coprod.map_iso
- \+ *def* prod.functor
- \+/\- *def* prod_comparison
- \- *def* prod_functor
- \+/\- *def* prod_comparison

modified src/category_theory/monoidal/of_has_finite_products.lean
- \+ *lemma* prod.left_unitor_hom_naturality
- \+ *lemma* prod.left_unitor_inv_naturality
- \+ *lemma* prod.right_unitor_hom_naturality
- \- *lemma* prod_left_unitor_hom_naturality
- \- *lemma* prod_left_unitor_inv_naturality
- \- *lemma* prod_right_unitor_hom_naturality
- \+ *def* prod.functor_left_comp
- \- *def* prod_functor_left_comp



## [2020-10-15 22:31:38](https://github.com/leanprover-community/mathlib/commit/b7d176e)
feat(category_theory/cones): some isomorphisms relating operations ([#4536](https://github.com/leanprover-community/mathlib/pull/4536))
#### Estimated changes
modified src/category_theory/limits/cones.lean
- \+ *def* map_cone_postcompose
- \+ *def* map_cone_postcompose_equivalence_functor
- \+ *def* map_cocone_precompose
- \+ *def* map_cocone_precompose_equivalence_functor
- \+ *def* map_cone_whisker
- \+ *def* map_cocone_whisker



## [2020-10-15 20:34:24](https://github.com/leanprover-community/mathlib/commit/8985e39)
feat(archive/100-theorems-list/70_perfect_numbers): Perfect Number Theorem, Direction 2 ([#4621](https://github.com/leanprover-community/mathlib/pull/4621))
Adds a few extra lemmas about `divisors`, `proper_divisors` and sums of proper divisors
Proves Euler's direction of the Perfect Number theorem, finishing Freek 70
#### Estimated changes
modified archive/100-theorems-list/70_perfect_numbers.lean
- \+ *lemma* eq_pow_two_mul_odd
- \+ *theorem* eq_two_pow_mul_prime_mersenne_of_even_perfect
- \+ *theorem* even_and_perfect_iff

modified docs/100.yaml

modified src/number_theory/divisors.lean
- \+ *lemma* proper_divisors_subset_divisors
- \+ *lemma* divisors_one
- \+ *lemma* proper_divisors_one
- \+ *lemma* pos_of_mem_divisors
- \+ *lemma* pos_of_mem_proper_divisors
- \+ *lemma* one_mem_proper_divisors_iff_one_lt
- \+/\- *lemma* swap_mem_divisors_antidiagonal
- \+/\- *lemma* fst_mem_divisors_of_mem_antidiagonal
- \+/\- *lemma* snd_mem_divisors_of_mem_antidiagonal
- \+/\- *lemma* map_swap_divisors_antidiagonal
- \+ *lemma* prime.divisors
- \+ *lemma* prime.proper_divisors
- \+ *lemma* eq_proper_divisors_of_subset_of_sum_eq_sum
- \+ *lemma* sum_proper_divisors_dvd
- \+ *lemma* prime.sum_proper_divisors
- \+ *lemma* prime.sum_divisors
- \+ *lemma* proper_divisors_eq_singleton_one_iff_prime
- \+ *lemma* sum_proper_divisors_eq_one_iff_prime
- \+/\- *lemma* swap_mem_divisors_antidiagonal
- \+/\- *lemma* fst_mem_divisors_of_mem_antidiagonal
- \+/\- *lemma* snd_mem_divisors_of_mem_antidiagonal
- \+/\- *lemma* map_swap_divisors_antidiagonal
- \- *lemma* divisors_prime
- \- *lemma* sum_divisors_prime
- \+/\- *theorem* perfect_iff_sum_proper_divisors
- \+/\- *theorem* perfect_iff_sum_divisors_eq_two_mul
- \+/\- *theorem* perfect_iff_sum_proper_divisors
- \+/\- *theorem* perfect_iff_sum_divisors_eq_two_mul



## [2020-10-15 16:29:11](https://github.com/leanprover-community/mathlib/commit/d473517)
chore(algebra/group/hom): add `monoid_hom.eval` ([#4629](https://github.com/leanprover-community/mathlib/pull/4629))
#### Estimated changes
modified src/algebra/big_operators/pi.lean
- \+/\- *lemma* list_prod_apply
- \+ *lemma* monoid_hom.finset_prod_apply
- \+/\- *lemma* list_prod_apply

modified src/algebra/group/hom.lean
- \+ *lemma* eval_apply
- \+ *def* eval



## [2020-10-15 16:29:09](https://github.com/leanprover-community/mathlib/commit/38a5f5d)
chore(data/equiv/mul_add): add `monoid_hom.to_mul_equiv` ([#4628](https://github.com/leanprover-community/mathlib/pull/4628))
#### Estimated changes
modified src/algebra/category/Group/basic.lean

modified src/algebra/category/Mon/basic.lean

modified src/data/equiv/mul_add.lean
- \+ *lemma* coe_to_monoid_hom
- \+ *lemma* monoid_hom.coe_to_mul_equiv
- \+ *def* add_monoid_hom.to_add_equiv
- \+ *def* monoid_hom.to_mul_equiv



## [2020-10-15 16:29:07](https://github.com/leanprover-community/mathlib/commit/46b0528)
refactor(data/polynomial): Move some lemmas to `monoid_algebra` ([#4627](https://github.com/leanprover-community/mathlib/pull/4627))
The `add_monoid_algebra.mul_apply_antidiagonal` lemma is copied verbatim from `monoid_algebra.mul_apply_antidiagonal`.
#### Estimated changes
modified src/algebra/monoid_algebra.lean
- \+ *lemma* mul_apply_antidiagonal

modified src/data/polynomial/algebra_map.lean

modified src/data/polynomial/basic.lean
- \- *lemma* coeff_single
- \+/\- *def* coeff
- \+/\- *def* coeff

modified src/data/polynomial/coeff.lean



## [2020-10-15 16:29:05](https://github.com/leanprover-community/mathlib/commit/abaf3c2)
feat(algebra/category/Algebra/basic): Add free/forget adjunction. ([#4620](https://github.com/leanprover-community/mathlib/pull/4620))
This PR adds the usual free/forget adjunction for the category of `R`-algebras.
#### Estimated changes
modified src/algebra/category/Algebra/basic.lean
- \+ *def* free
- \+ *def* adj



## [2020-10-15 16:29:03](https://github.com/leanprover-community/mathlib/commit/07ee11e)
feat(algebra/algebra/basic): Add `map_finsupp_(sum|prod)` to `alg_(hom|equiv)` ([#4603](https://github.com/leanprover-community/mathlib/pull/4603))
Also copies some lemmas from `alg_hom` to `alg_equiv` that were missing
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* map_finsupp_sum
- \+ *lemma* map_finsupp_prod
- \+ *lemma* map_finsupp_sum
- \+ *lemma* map_prod
- \+ *lemma* map_finsupp_prod
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+ *lemma* map_inv
- \+ *lemma* map_div
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub



## [2020-10-15 16:29:00](https://github.com/leanprover-community/mathlib/commit/bb1f549)
feat(algebra/gcd_monoid): in a gcd_domain a coprime factor of a power is a power ([#4589](https://github.com/leanprover-community/mathlib/pull/4589))
The main result is:
```
theorem associated_pow_of_mul_eq_pow {a b c : α} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : gcd a b = 1) {k : ℕ} (h : a * b = c ^ k) :
  ∃ (d : α), associated (d ^ k) a
```
#### Estimated changes
modified src/algebra/gcd_monoid.lean
- \+ *lemma* dvd_gcd_mul_of_dvd_mul
- \+ *lemma* dvd_mul_gcd_of_dvd_mul
- \+ *theorem* gcd_pow_right_dvd_pow_gcd
- \+ *theorem* gcd_pow_left_dvd_pow_gcd
- \+ *theorem* pow_dvd_of_mul_eq_pow
- \+ *theorem* exists_associated_pow_of_mul_eq_pow



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
modified src/data/fin.lean
- \+ *def* append

modified src/data/matrix/notation.lean
- \+ *lemma* empty_append
- \+ *lemma* cons_append
- \+ *lemma* vec_alt0_append
- \+ *lemma* vec_alt1_append
- \+ *lemma* cons_vec_bit0_eq_alt0
- \+ *lemma* cons_vec_bit1_eq_alt1
- \+ *lemma* cons_vec_alt0
- \+ *lemma* empty_vec_alt0
- \+ *lemma* cons_vec_alt1
- \+ *lemma* empty_vec_alt1
- \+ *def* vec_alt0
- \+ *def* vec_alt1

modified test/matrix.lean



## [2020-10-15 15:01:02](https://github.com/leanprover-community/mathlib/commit/85d4b57)
feat(data/polynomial/eval): bit0_comp, bit1_comp ([#4617](https://github.com/leanprover-community/mathlib/pull/4617))
#### Estimated changes
modified src/data/polynomial/eval.lean
- \+ *lemma* bit0_comp
- \+ *lemma* bit1_comp



## [2020-10-15 14:04:18](https://github.com/leanprover-community/mathlib/commit/1444fa5)
fix(haar_measure): minor changes ([#4623](https://github.com/leanprover-community/mathlib/pull/4623))
There were some mistakes in the doc, which made it sound like `chaar` and `haar_outer_measure` coincide on compact sets, which is not generally true. 
Also cleanup various proofs.
#### Estimated changes
modified src/measure_theory/content.lean
- \+ *lemma* of_content_le

modified src/measure_theory/haar_measure.lean
- \+/\- *lemma* is_left_invariant_index
- \+/\- *lemma* is_left_invariant_chaar
- \+ *lemma* echaar_self
- \+ *lemma* is_left_invariant_echaar
- \+ *lemma* echaar_le_haar_outer_measure
- \+ *lemma* haar_outer_measure_le_echaar
- \+/\- *lemma* is_left_invariant_index
- \+/\- *lemma* is_left_invariant_chaar
- \- *lemma* chaar_le_haar_outer_measure
- \- *lemma* haar_outer_measure_le_chaar



## [2020-10-15 08:51:18](https://github.com/leanprover-community/mathlib/commit/7559d1c)
lint(data/num/*): add docs and remove some [has_zero] requirements ([#4604](https://github.com/leanprover-community/mathlib/pull/4604))
#### Estimated changes
modified src/data/num/basic.lean

modified src/data/num/bitwise.lean

modified src/data/num/lemmas.lean
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_one'
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_one'
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1



## [2020-10-15 07:30:22](https://github.com/leanprover-community/mathlib/commit/fa65282)
chore(category_theory/monoidal): fix typo in docstrings ([#4625](https://github.com/leanprover-community/mathlib/pull/4625))
#### Estimated changes
modified src/category_theory/monoidal/category.lean
- \+/\- *lemma* right_unitor_conjugation
- \+/\- *lemma* left_unitor_conjugation
- \+/\- *lemma* right_unitor_conjugation
- \+/\- *lemma* left_unitor_conjugation
- \+/\- *def* tensor_iso
- \+/\- *def* tensor_iso



## [2020-10-15 01:11:53](https://github.com/leanprover-community/mathlib/commit/2e1129e)
chore(scripts): update nolints.txt ([#4622](https://github.com/leanprover-community/mathlib/pull/4622))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-14 18:39:39](https://github.com/leanprover-community/mathlib/commit/084b7e7)
chore(algebra/order,data/set/intervals): a few more trivial lemmas ([#4611](https://github.com/leanprover-community/mathlib/pull/4611))
* a few more lemmas for `has_le.le` and `has_lt.lt` namespaces;
* a few lemmas about intersections of intervals;
* fix section header in `topology/algebra/module`.
#### Estimated changes
modified src/algebra/order.lean
- \+ *lemma* lt_or_le
- \+ *lemma* le_or_lt
- \+ *lemma* le_or_le
- \+ *lemma* ne'
- \+ *lemma* lt_or_lt
- \- *lemma* has_le.le.lt_or_le
- \- *lemma* has_le.le.le_or_lt

modified src/data/set/intervals/basic.lean
- \+ *lemma* Ioc_inter_Ioo_of_left_lt
- \+ *lemma* Ioc_inter_Ioo_of_right_le
- \+ *lemma* Ioo_inter_Ioc_of_left_le
- \+ *lemma* Ioo_inter_Ioc_of_right_lt

modified src/topology/algebra/module.lean



## [2020-10-14 18:39:37](https://github.com/leanprover-community/mathlib/commit/d11eb84)
fix(tactic/suggest): properly remove "Try this: exact " prefix from library_search hole command ([#4609](https://github.com/leanprover-community/mathlib/pull/4609))
[See Zulip](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/mechanisms.20to.20search.20through.20mathlilb/near/213223321)
#### Estimated changes
modified src/tactic/core.lean

modified src/tactic/suggest.lean



## [2020-10-14 17:31:01](https://github.com/leanprover-community/mathlib/commit/40844f0)
doc(category_theory/comma): Fix markdown rendering in docs ([#4618](https://github.com/leanprover-community/mathlib/pull/4618))
#### Estimated changes
modified src/category_theory/comma.lean



## [2020-10-14 14:46:32](https://github.com/leanprover-community/mathlib/commit/de46349)
feat(data/set/intervals): more lemmas about `unordered_interval` ([#4607](https://github.com/leanprover-community/mathlib/pull/4607))
Add images/preimages of unordered intervals under common arithmetic operations.
#### Estimated changes
modified src/data/set/basic.lean
- \+/\- *theorem* nonempty.image_const
- \+/\- *theorem* nonempty.image_const

modified src/data/set/intervals/unordered_interval.lean
- \+ *lemma* preimage_const_add_interval
- \+ *lemma* preimage_add_const_interval
- \+ *lemma* preimage_neg_interval
- \+ *lemma* preimage_sub_const_interval
- \+ *lemma* preimage_const_sub_interval
- \+ *lemma* image_const_add_interval
- \+ *lemma* image_add_const_interval
- \+ *lemma* image_const_sub_interval
- \+ *lemma* image_sub_const_interval
- \+ *lemma* image_neg_interval
- \+ *lemma* preimage_mul_const_interval
- \+ *lemma* preimage_const_mul_interval
- \+ *lemma* preimage_div_const_interval
- \+ *lemma* image_mul_const_interval
- \+ *lemma* image_const_mul_interval
- \+ *lemma* image_div_const_interval



## [2020-10-14 14:46:30](https://github.com/leanprover-community/mathlib/commit/442ef22)
feat(linear_algebra/clifford_algebra): Add a definition derived from exterior_algebra.lean ([#4430](https://github.com/leanprover-community/mathlib/pull/4430))
#### Estimated changes
created src/linear_algebra/clifford_algebra.lean
- \+ *theorem* ι_square_scalar
- \+ *theorem* ι_comp_lift
- \+ *theorem* lift_ι_apply
- \+ *theorem* lift_unique
- \+ *theorem* comp_ι_square_scalar
- \+ *theorem* lift_comp_ι
- \+ *theorem* hom_ext
- \+ *def* clifford_algebra
- \+ *def* ι
- \+ *def* lift
- \+ *def* as_exterior

modified src/linear_algebra/exterior_algebra.lean



## [2020-10-14 15:36:40+02:00](https://github.com/leanprover-community/mathlib/commit/1a1655c)
doc(docs/100): link to actual triangle inequality ([#4614](https://github.com/leanprover-community/mathlib/pull/4614))
#### Estimated changes
modified docs/100.yaml



## [2020-10-14 09:45:28](https://github.com/leanprover-community/mathlib/commit/f7edbca)
feat(algebra/char_zero): char_zero.infinite ([#4593](https://github.com/leanprover-community/mathlib/pull/4593))
#### Estimated changes
modified src/algebra/char_zero.lean
- \+/\- *lemma* two_ne_zero'
- \+/\- *lemma* two_ne_zero'

modified src/data/fintype/basic.lean
- \+ *lemma* nonempty



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
modified src/algebra/algebra/subalgebra.lean
- \+ *theorem* to_submodule_bot
- \+ *def* to_submodule_equiv

modified src/data/equiv/basic.lean
- \+/\- *lemma* option_equiv_sum_punit_none
- \+ *lemma* option_equiv_sum_punit_coe
- \+ *lemma* insert_symm_apply_inl
- \+ *lemma* insert_symm_apply_inr
- \+ *lemma* insert_apply_left
- \+ *lemma* insert_apply_right
- \+/\- *lemma* option_equiv_sum_punit_none

modified src/field_theory/fixed.lean

modified src/linear_algebra/basic.lean
- \+ *lemma* disjoint_span_singleton'
- \+ *lemma* is_compl_range_inl_inr
- \+/\- *lemma* sup_range_inl_inr
- \+/\- *lemma* sup_range_inl_inr
- \+ *theorem* disjoint_def'

modified src/linear_algebra/basis.lean

modified src/linear_algebra/dual.lean
- \+/\- *lemma* eval_apply
- \+/\- *lemma* to_dual_apply_left
- \+/\- *lemma* to_dual_apply_right
- \+/\- *lemma* to_dual_swap_eq_to_dual
- \+/\- *lemma* to_dual_eq_repr
- \+/\- *lemma* to_dual_eq_equiv_fun
- \+/\- *lemma* to_dual_inj
- \+/\- *lemma* eval_apply
- \+/\- *lemma* to_dual_apply_left
- \+/\- *lemma* to_dual_apply_right
- \+/\- *lemma* to_dual_swap_eq_to_dual
- \+/\- *lemma* to_dual_eq_repr
- \+/\- *lemma* to_dual_eq_equiv_fun
- \+/\- *lemma* to_dual_inj
- \+/\- *theorem* to_dual_ker
- \+/\- *theorem* to_dual_range
- \+/\- *theorem* to_dual_ker
- \+/\- *theorem* to_dual_range
- \+/\- *def* to_dual_flip
- \+/\- *def* dual_basis
- \+/\- *def* to_dual_flip
- \+/\- *def* dual_basis

modified src/linear_algebra/finite_dimensional.lean

modified src/linear_algebra/finsupp.lean
- \+ *theorem* supported_inter
- \+ *theorem* disjoint_supported_supported
- \+ *theorem* disjoint_supported_supported_iff
- \+ *theorem* total_unique

modified src/linear_algebra/finsupp_vector_space.lean

modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent.map
- \+ *lemma* linear_independent.map'
- \+ *lemma* linear_independent.of_comp
- \+/\- *lemma* linear_independent_of_subsingleton
- \+ *lemma* linear_independent.disjoint_span_image
- \+ *lemma* linear_independent_sum
- \+ *lemma* linear_independent.sum_type
- \+ *lemma* linear_independent_unique_iff
- \+ *lemma* linear_independent_option'
- \+ *lemma* linear_independent.option
- \+ *lemma* linear_independent_option
- \+ *lemma* linear_independent_pair
- \+ *lemma* linear_independent_fin_cons
- \+ *lemma* linear_independent.fin_cons
- \+ *lemma* linear_independent_fin_succ
- \+ *lemma* linear_independent_fin2
- \+/\- *lemma* linear_independent_of_subsingleton
- \- *lemma* linear_independent.unique
- \- *lemma* linear_independent_of_comp
- \- *lemma* linear_independent.to_subtype_range
- \- *lemma* linear_independent.of_subtype_range
- \- *lemma* linear_independent.image
- \- *lemma* linear_independent_unique
- \- *lemma* disjoint_span_singleton
- \+ *theorem* linear_independent_iff_injective_total
- \+ *theorem* fintype.linear_independent_iff
- \+ *theorem* linear_independent_subtype_range
- \+ *theorem* linear_independent.to_subtype_range
- \+ *theorem* linear_independent.to_subtype_range'
- \+ *theorem* linear_independent.image
- \+/\- *theorem* linear_independent_insert'
- \- *theorem* linear_independent.image'
- \+/\- *theorem* linear_independent_insert'



## [2020-10-14 08:24:05](https://github.com/leanprover-community/mathlib/commit/8511729)
refactor(data/int/gcd,ring_theory/int/basic): collect integer divisibility results from various files ([#4572](https://github.com/leanprover-community/mathlib/pull/4572))
Applying comments from PR [#4384](https://github.com/leanprover-community/mathlib/pull/4384). In particular:
1) Move the gcd and lcm results from gcd_monoid to `data/int/gcd.lean` with new proofs (for a few lcm results) that do not need ring theory.
2) Try to collect applications of ring theory to ℕ and ℤ into a new file `ring_theory/int/basic.lean`.
#### Estimated changes
modified src/algebra/gcd_monoid.lean
- \- *lemma* normalize_of_nonneg
- \- *lemma* normalize_of_neg
- \- *lemma* normalize_coe_nat
- \- *lemma* coe_gcd
- \- *lemma* coe_lcm
- \- *lemma* nat_abs_gcd
- \- *lemma* nat_abs_lcm
- \- *lemma* nat.prime_iff_prime
- \- *lemma* nat.prime_iff_prime_int
- \- *lemma* int.prime.dvd_mul
- \- *lemma* int.prime.dvd_mul'
- \- *lemma* prime_two_or_dvd_of_dvd_two_mul_pow_self_two
- \- *theorem* coe_nat_abs_eq_normalize
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
- \- *theorem* gcd_div_gcd_div_gcd
- \- *theorem* gcd_dvd_gcd_of_dvd_left
- \- *theorem* gcd_dvd_gcd_of_dvd_right
- \- *theorem* gcd_dvd_gcd_mul_left
- \- *theorem* gcd_dvd_gcd_mul_right
- \- *theorem* gcd_dvd_gcd_mul_left_right
- \- *theorem* gcd_dvd_gcd_mul_right_right
- \- *theorem* gcd_eq_left
- \- *theorem* gcd_eq_right
- \- *theorem* ne_zero_of_gcd
- \- *theorem* exists_gcd_one
- \- *theorem* exists_gcd_one'
- \- *theorem* pow_dvd_pow_iff
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
- \- *theorem* irreducible_iff_nat_prime
- \- *def* lcm
- \- *def* associates_int_equiv_nat

modified src/data/int/gcd.lean
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
- \+ *theorem* gcd_div_gcd_div_gcd
- \+ *theorem* gcd_dvd_gcd_of_dvd_left
- \+ *theorem* gcd_dvd_gcd_of_dvd_right
- \+ *theorem* gcd_dvd_gcd_mul_left
- \+ *theorem* gcd_dvd_gcd_mul_right
- \+ *theorem* gcd_dvd_gcd_mul_left_right
- \+ *theorem* gcd_dvd_gcd_mul_right_right
- \+ *theorem* gcd_eq_left
- \+ *theorem* gcd_eq_right
- \+ *theorem* ne_zero_of_gcd
- \+ *theorem* exists_gcd_one
- \+ *theorem* exists_gcd_one'
- \+ *theorem* pow_dvd_pow_iff
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
- \+ *def* lcm

deleted src/data/nat/associated.lean
- \- *theorem* nat.prime_iff
- \- *theorem* nat.irreducible_iff_prime

modified src/data/nat/multiplicity.lean

deleted src/data/nat/unique_factorization.lean
- \- *theorem* nat.factors_eq

modified src/data/padics/padic_norm.lean

modified src/data/real/irrational.lean

modified src/number_theory/pythagorean_triples.lean

created src/ring_theory/int/basic.lean
- \+ *lemma* normalize_of_nonneg
- \+ *lemma* normalize_of_neg
- \+ *lemma* normalize_coe_nat
- \+ *lemma* coe_gcd
- \+ *lemma* coe_lcm
- \+ *lemma* nat_abs_gcd
- \+ *lemma* nat_abs_lcm
- \+ *lemma* nat.prime_iff_prime
- \+ *lemma* nat.prime_iff_prime_int
- \+ *lemma* int.prime.dvd_mul
- \+ *lemma* int.prime.dvd_mul'
- \+ *lemma* prime_two_or_dvd_of_dvd_two_mul_pow_self_two
- \+ *lemma* finite_int_iff_nat_abs_finite
- \+ *lemma* finite_int_iff
- \+ *theorem* nat.prime_iff
- \+ *theorem* nat.irreducible_iff_prime
- \+ *theorem* coe_nat_abs_eq_normalize
- \+ *theorem* irreducible_iff_nat_prime
- \+ *theorem* nat.factors_eq
- \+ *def* associates_int_equiv_nat

modified src/ring_theory/multiplicity.lean
- \- *lemma* finite_int_iff_nat_abs_finite
- \- *lemma* finite_int_iff



## [2020-10-14 08:24:03](https://github.com/leanprover-community/mathlib/commit/20006f1)
feat(data/polynomial/field_division, field_theory/splitting_field): Splits if enough roots ([#4557](https://github.com/leanprover-community/mathlib/pull/4557))
I have added some lemmas about polynomials that split. In particular the fact that if `p` has as many roots as its degree than it can be written as a product of `(X - a)` and so it splits.
The proof of this for monic polynomial, in `eq_prod_of_card_roots_monic`, is rather messy and can probably be improved a lot.
#### Estimated changes
modified src/data/polynomial/field_division.lean
- \+ *lemma* prod_multiset_root_eq_finset_root
- \+ *lemma* prod_multiset_X_sub_C_dvd
- \+ *lemma* roots_C_mul

modified src/data/polynomial/monomial.lean
- \+/\- *lemma* C_inj
- \+ *lemma* C_eq_zero
- \+/\- *lemma* C_inj

modified src/field_theory/splitting_field.lean
- \+ *lemma* prod_multiset_X_sub_C_of_monic_of_roots_card_eq
- \+ *lemma* C_leading_coeff_mul_prod_multiset_X_sub_C
- \+ *lemma* splits_iff_card_roots



## [2020-10-14 01:06:37](https://github.com/leanprover-community/mathlib/commit/1c12bd9)
chore(scripts): update nolints.txt ([#4610](https://github.com/leanprover-community/mathlib/pull/4610))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-13 23:51:13](https://github.com/leanprover-community/mathlib/commit/e2dd1c6)
feat(analysis/normed_space): unconditionally convergent series in `R^n` is absolutely convergent ([#4551](https://github.com/leanprover-community/mathlib/pull/4551))
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \- *lemma* has_sum_of_bounded_monoid_hom_of_has_sum
- \- *lemma* has_sum_of_bounded_monoid_hom_of_summable

modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* summable_norm_iff

modified src/analysis/normed_space/operator_norm.lean
- \- *lemma* has_sum_of_summable

modified src/analysis/specific_limits.lean

modified src/data/indicator_function.lean
- \+ *lemma* indicator_eq_zero_or_self

modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable.of_neg
- \+ *lemma* summable_neg_iff
- \+ *lemma* summable_subtype_and_compl
- \+ *lemma* summable_abs_iff



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
modified src/analysis/calculus/fderiv.lean
- \+ *theorem* has_fderiv_within_at.unique_on

modified src/analysis/calculus/tangent_cone.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/geometry/manifold/mfderiv.lean
- \+ *lemma* mfderiv_bijective
- \+ *lemma* mfderiv_surjective

modified src/linear_algebra/basic.lean
- \+ *lemma* eq_on_span
- \+ *lemma* eq_on_span'
- \+ *lemma* ext_on
- \+ *lemma* ext_on_range
- \- *lemma* linear_eq_on
- \- *lemma* linear_map.ext_on

modified src/linear_algebra/basis.lean

modified src/measure_theory/simple_func_dense.lean

modified src/topology/algebra/module.lean
- \+ *lemma* eq_on_closure_span
- \+ *lemma* ext_on

modified src/topology/bases.lean
- \+/\- *lemma* exists_dense_seq
- \+ *lemma* dense_range_dense_seq
- \- *lemma* exists_countable_closure_eq_univ
- \+/\- *lemma* exists_dense_seq
- \- *lemma* dense_seq_dense
- \- *lemma* dense_range.separable_space

modified src/topology/basic.lean
- \+ *lemma* dense_closure
- \+ *lemma* dense_univ
- \+ *lemma* dense.nonempty_iff
- \+ *lemma* dense.nonempty
- \+ *lemma* dense.mono
- \+ *lemma* dense.inter_of_open_left
- \+ *lemma* dense.inter_of_open_right
- \+ *lemma* function.surjective.dense_range
- \+ *lemma* continuous.range_subset_closure_image_dense
- \+ *lemma* dense_range.dense_image
- \+ *lemma* dense_range.dense_of_maps_to
- \+/\- *lemma* dense_range.comp
- \+ *lemma* dense_range.nonempty_iff
- \+/\- *lemma* dense_range.nonempty
- \- *lemma* dense_of_subset_dense
- \- *lemma* dense_inter_of_open_left
- \- *lemma* dense_inter_of_open_right
- \+/\- *lemma* dense_range.comp
- \+/\- *lemma* dense_range.nonempty
- \- *lemma* continuous.dense_image_of_dense_range
- \+ *def* dense_range.some
- \- *def* dense_range.inhabited

modified src/topology/constructions.lean
- \+ *lemma* dense.quotient
- \+ *lemma* dense_range.quotient
- \+ *lemma* dense.prod
- \+ *lemma* dense_range.prod_map
- \- *lemma* quotient_dense_of_dense
- \- *lemma* dense_range.prod

modified src/topology/dense_embedding.lean
- \- *lemma* separable
- \- *lemma* separable

modified src/topology/extend_from_subset.lean
- \+/\- *lemma* continuous_extend_from
- \+/\- *lemma* continuous_extend_from

modified src/topology/instances/real.lean

modified src/topology/metric_space/baire.lean
- \+/\- *lemma* mem_residual
- \+/\- *lemma* mem_residual
- \+ *theorem* dense.inter_of_Gδ
- \- *theorem* dense_inter_of_Gδ

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/isometry.lean
- \+/\- *lemma* embedding_of_subset_isometry
- \+/\- *lemma* embedding_of_subset_isometry

modified src/topology/separation.lean
- \+ *lemma* set.eq_on.closure
- \+ *lemma* continuous.ext_on

modified src/topology/stone_cech.lean
- \+ *lemma* dense_range_pure
- \+ *lemma* induced_topology_pure
- \+ *lemma* dense_range_stone_cech_unit
- \- *lemma* stone_cech_unit_dense

modified src/topology/uniform_space/abstract_completion.lean
- \+ *lemma* closure_range
- \- *lemma* dense'

modified src/topology/uniform_space/cauchy.lean

modified src/topology/uniform_space/completion.lean
- \+ *lemma* dense_range_pure_cauchy
- \+ *lemma* dense_range_coe
- \+ *lemma* dense_range_coe₂
- \+ *lemma* dense_range_coe₃
- \- *lemma* pure_cauchy_dense
- \- *lemma* dense
- \- *lemma* dense₂
- \- *lemma* dense₃



## [2020-10-13 19:48:34](https://github.com/leanprover-community/mathlib/commit/fde3d78)
chore(multiset): dedicated notation for multiset.cons ([#4600](https://github.com/leanprover-community/mathlib/pull/4600))
#### Estimated changes
modified src/algebra/big_operators/basic.lean

modified src/data/dfinsupp.lean

modified src/data/finmap.lean

modified src/data/finset/basic.lean
- \+/\- *theorem* singleton_val
- \+/\- *theorem* cons_val
- \+/\- *theorem* mk_cons
- \+/\- *theorem* insert_val'
- \+/\- *theorem* insert_val_of_not_mem
- \+/\- *theorem* singleton_val
- \+/\- *theorem* cons_val
- \+/\- *theorem* mk_cons
- \+/\- *theorem* insert_val'
- \+/\- *theorem* insert_val_of_not_mem

modified src/data/finset/pi.lean

modified src/data/finsupp/basic.lean

modified src/data/fintype/basic.lean

modified src/data/multiset/antidiagonal.lean
- \+/\- *theorem* antidiagonal_zero
- \+/\- *theorem* antidiagonal_cons
- \+/\- *theorem* antidiagonal_zero
- \+/\- *theorem* antidiagonal_cons

modified src/data/multiset/basic.lean
- \+/\- *lemma* mem_cons_of_mem
- \+/\- *lemma* zero_ne_cons
- \+/\- *lemma* cons_ne_zero
- \+/\- *lemma* repeat_succ
- \+/\- *lemma* repeat_one
- \+/\- *lemma* mem_cons_of_mem
- \+/\- *lemma* zero_ne_cons
- \+/\- *lemma* cons_ne_zero
- \+/\- *lemma* repeat_succ
- \+/\- *lemma* repeat_one
- \+/\- *theorem* singleton_coe
- \+/\- *theorem* cons_inj_right
- \+/\- *theorem* cons_swap
- \+/\- *theorem* mem_cons
- \+/\- *theorem* mem_cons_self
- \+/\- *theorem* exists_cons_of_mem
- \+/\- *theorem* cons_subset
- \+/\- *theorem* lt_cons_self
- \+/\- *theorem* le_cons_self
- \+/\- *theorem* cons_le_cons_iff
- \+/\- *theorem* cons_le_cons
- \+/\- *theorem* le_cons_of_not_mem
- \+/\- *theorem* card_cons
- \+/\- *theorem* card_singleton
- \+/\- *theorem* lt_iff_cons_le
- \+/\- *theorem* singleton_eq_singleton
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_self
- \+/\- *theorem* singleton_inj
- \+/\- *theorem* singleton_ne_zero
- \+/\- *theorem* singleton_le
- \+/\- *theorem* card_eq_one
- \+/\- *theorem* singleton_add
- \+/\- *theorem* cons_add
- \+/\- *theorem* add_cons
- \+/\- *theorem* repeat_subset_singleton
- \+/\- *theorem* erase_cons_head
- \+/\- *theorem* erase_cons_tail
- \+/\- *theorem* cons_erase
- \+/\- *theorem* le_cons_erase
- \+/\- *theorem* erase_le_iff_le_cons
- \+/\- *theorem* map_cons
- \+/\- *theorem* foldl_cons
- \+/\- *theorem* foldr_cons
- \+/\- *theorem* prod_cons
- \+/\- *theorem* prod_singleton
- \+/\- *theorem* join_cons
- \+/\- *theorem* cons_bind
- \+/\- *theorem* product_singleton
- \+/\- *theorem* sub_cons
- \+/\- *theorem* cons_union_distrib
- \+/\- *theorem* cons_inter_distrib
- \+/\- *theorem* filter_cons_of_pos
- \+/\- *theorem* filter_cons_of_neg
- \+/\- *theorem* countp_cons_of_pos
- \+/\- *theorem* countp_cons_of_neg
- \+/\- *theorem* count_cons_self
- \+/\- *theorem* count_cons_of_ne
- \+/\- *theorem* count_le_count_cons
- \+/\- *theorem* count_singleton
- \+/\- *theorem* singleton_disjoint
- \+/\- *theorem* disjoint_singleton
- \+/\- *theorem* singleton_coe
- \+/\- *theorem* cons_inj_right
- \+/\- *theorem* cons_swap
- \+/\- *theorem* mem_cons
- \+/\- *theorem* mem_cons_self
- \+/\- *theorem* exists_cons_of_mem
- \+/\- *theorem* cons_subset
- \+/\- *theorem* lt_cons_self
- \+/\- *theorem* le_cons_self
- \+/\- *theorem* cons_le_cons_iff
- \+/\- *theorem* cons_le_cons
- \+/\- *theorem* le_cons_of_not_mem
- \+/\- *theorem* card_cons
- \+/\- *theorem* card_singleton
- \+/\- *theorem* lt_iff_cons_le
- \+/\- *theorem* singleton_eq_singleton
- \+/\- *theorem* mem_singleton
- \+/\- *theorem* mem_singleton_self
- \+/\- *theorem* singleton_inj
- \+/\- *theorem* singleton_ne_zero
- \+/\- *theorem* singleton_le
- \+/\- *theorem* card_eq_one
- \+/\- *theorem* singleton_add
- \+/\- *theorem* cons_add
- \+/\- *theorem* add_cons
- \+/\- *theorem* repeat_subset_singleton
- \+/\- *theorem* erase_cons_head
- \+/\- *theorem* erase_cons_tail
- \+/\- *theorem* cons_erase
- \+/\- *theorem* le_cons_erase
- \+/\- *theorem* erase_le_iff_le_cons
- \+/\- *theorem* map_cons
- \+/\- *theorem* foldl_cons
- \+/\- *theorem* foldr_cons
- \+/\- *theorem* prod_cons
- \+/\- *theorem* prod_singleton
- \+/\- *theorem* join_cons
- \+/\- *theorem* cons_bind
- \+/\- *theorem* product_singleton
- \+/\- *theorem* sub_cons
- \+/\- *theorem* cons_union_distrib
- \+/\- *theorem* cons_inter_distrib
- \+/\- *theorem* filter_cons_of_pos
- \+/\- *theorem* filter_cons_of_neg
- \+/\- *theorem* countp_cons_of_pos
- \+/\- *theorem* countp_cons_of_neg
- \+/\- *theorem* count_cons_self
- \+/\- *theorem* count_cons_of_ne
- \+/\- *theorem* count_le_count_cons
- \+/\- *theorem* count_singleton
- \+/\- *theorem* singleton_disjoint
- \+/\- *theorem* disjoint_singleton

modified src/data/multiset/erase_dup.lean
- \+/\- *theorem* erase_dup_singleton
- \+/\- *theorem* erase_dup_singleton

modified src/data/multiset/finset_ops.lean
- \+/\- *theorem* ndinsert_zero
- \+/\- *theorem* ndinsert_of_not_mem
- \+/\- *theorem* ndinsert_zero
- \+/\- *theorem* ndinsert_of_not_mem

modified src/data/multiset/fold.lean
- \+/\- *theorem* fold_cons_right
- \+/\- *theorem* fold_cons'_right
- \+/\- *theorem* fold_cons'_left
- \+/\- *theorem* fold_singleton
- \+/\- *theorem* fold_cons_right
- \+/\- *theorem* fold_cons'_right
- \+/\- *theorem* fold_cons'_left
- \+/\- *theorem* fold_singleton

modified src/data/multiset/functor.lean
- \+/\- *lemma* pure_def
- \+/\- *lemma* pure_def

modified src/data/multiset/gcd.lean
- \+/\- *lemma* lcm_singleton
- \+/\- *lemma* gcd_singleton
- \+/\- *lemma* lcm_singleton
- \+/\- *lemma* gcd_singleton

modified src/data/multiset/intervals.lean
- \+/\- *theorem* succ_top
- \+/\- *theorem* eq_cons
- \+/\- *theorem* succ_top
- \+/\- *theorem* eq_cons

modified src/data/multiset/lattice.lean
- \+/\- *lemma* sup_singleton
- \+/\- *lemma* inf_singleton
- \+/\- *lemma* sup_singleton
- \+/\- *lemma* inf_singleton

modified src/data/multiset/nat_antidiagonal.lean

modified src/data/multiset/nodup.lean
- \+/\- *lemma* nodup_iff_ne_cons_cons
- \+/\- *lemma* nodup_iff_ne_cons_cons
- \+/\- *theorem* nodup_cons
- \+/\- *theorem* nodup_cons_of_nodup
- \+/\- *theorem* nodup_singleton
- \+/\- *theorem* nodup_of_nodup_cons
- \+/\- *theorem* not_mem_of_nodup_cons
- \+/\- *theorem* not_nodup_pair
- \+/\- *theorem* nodup_iff_le
- \+/\- *theorem* nodup_cons
- \+/\- *theorem* nodup_cons_of_nodup
- \+/\- *theorem* nodup_singleton
- \+/\- *theorem* nodup_of_nodup_cons
- \+/\- *theorem* not_mem_of_nodup_cons
- \+/\- *theorem* not_nodup_pair
- \+/\- *theorem* nodup_iff_le

modified src/data/multiset/pi.lean
- \+/\- *lemma* pi.cons_same
- \+/\- *lemma* pi_zero
- \+/\- *lemma* pi.cons_same
- \+/\- *lemma* pi_zero
- \+/\- *def* pi.cons
- \+/\- *def* pi.cons

modified src/data/multiset/powerset.lean
- \+/\- *theorem* powerset_zero
- \+/\- *theorem* powerset_zero

modified src/data/multiset/range.lean
- \+/\- *theorem* range_succ
- \+/\- *theorem* range_succ

modified src/data/multiset/sections.lean
- \+/\- *lemma* sections_zero
- \+/\- *lemma* sections_zero

modified src/data/pnat/factors.lean
- \+/\- *def* of_prime
- \+/\- *def* of_prime

modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* roots_X_sub_C
- \+/\- *lemma* roots_X_sub_C

modified src/data/set/finite.lean

modified src/data/sym.lean

modified src/field_theory/splitting_field.lean

modified src/group_theory/perm/sign.lean

modified src/number_theory/sum_four_squares.lean

modified src/ring_theory/unique_factorization_domain.lean



## [2020-10-13 18:44:25](https://github.com/leanprover-community/mathlib/commit/7368d71)
chore(number_theory/arithmetic_function): Define in terms of zero_hom ([#4606](https://github.com/leanprover-community/mathlib/pull/4606))
No need to write these proofs in two places
#### Estimated changes
modified src/number_theory/arithmetic_function.lean
- \+/\- *lemma* map_zero
- \+/\- *lemma* zero_apply
- \+/\- *lemma* map_zero
- \+/\- *lemma* zero_apply
- \+ *def* arithmetic_function



## [2020-10-13 16:46:02](https://github.com/leanprover-community/mathlib/commit/b1c1033)
feat(analysis/normed_space/operator_norm): construct a continuous_linear_equiv from a linear_equiv and bounds in both directions ([#4583](https://github.com/leanprover-community/mathlib/pull/4583))
#### Estimated changes
modified src/analysis/normed_space/operator_norm.lean
- \+ *def* linear_equiv.to_continuous_linear_equiv_of_bounds



## [2020-10-13 16:46:00](https://github.com/leanprover-community/mathlib/commit/7cff825)
feat(data/vector2): induction principle, define last, and some lemmas (blocked by [#4578](https://github.com/leanprover-community/mathlib/pull/4578)) ([#4554](https://github.com/leanprover-community/mathlib/pull/4554))
#### Estimated changes
modified src/data/vector2.lean
- \+ *lemma* tail_nil
- \+ *lemma* singleton_tail
- \+ *lemma* to_list_singleton
- \+ *lemma* to_list_reverse
- \+ *lemma* nth_cons_nil
- \+ *lemma* last_def
- \+ *lemma* reverse_nth_zero
- \+/\- *theorem* ext
- \+/\- *theorem* ext
- \+ *def* last
- \+ *def* induction_on



## [2020-10-13 15:24:50](https://github.com/leanprover-community/mathlib/commit/71bb9f2)
chore(linear_algebra/finsupp): Implement lsingle in terms of single_add_hom ([#4605](https://github.com/leanprover-community/mathlib/pull/4605))
While not shorter, this makes it easier to relate the two definitions
#### Estimated changes
modified src/linear_algebra/finsupp.lean
- \+/\- *def* lapply
- \+/\- *def* lapply



## [2020-10-13 14:02:34](https://github.com/leanprover-community/mathlib/commit/ca6af1c)
chore(algebra/monoid_algebra): Replace `algebra_map'` with `single_(zero|one)_ring_hom` ([#4582](https://github.com/leanprover-community/mathlib/pull/4582))
`algebra_map'` is now trivially equal to `single_(zero|one)_ring_hom.comp`, so is no longer needed.
#### Estimated changes
modified src/algebra/monoid_algebra.lean
- \+ *def* single_one_ring_hom
- \+ *def* single_one_alg_hom
- \+ *def* single_zero_ring_hom
- \+ *def* single_zero_alg_hom
- \- *def* algebra_map'
- \- *def* algebra_map'

modified src/data/polynomial/monomial.lean
- \+/\- *def* C
- \+/\- *def* C



## [2020-10-13 11:12:28](https://github.com/leanprover-community/mathlib/commit/9f9344d)
feat(algebra/char_p): fields with a hom between them have same char ([#4594](https://github.com/leanprover-community/mathlib/pull/4594))
#### Estimated changes
modified src/algebra/char_p.lean
- \+ *lemma* ring_hom.char_p_iff_char_p



## [2020-10-13 09:47:17](https://github.com/leanprover-community/mathlib/commit/dd8bf2c)
feat(data/polynomial/eval): easy lemmas + speedup ([#4596](https://github.com/leanprover-community/mathlib/pull/4596))
#### Estimated changes
modified src/data/polynomial/algebra_map.lean
- \- *lemma* mul_comp

modified src/data/polynomial/eval.lean
- \+ *lemma* eval₂_congr
- \+ *lemma* mul_comp
- \+ *lemma* comp_assoc
- \+ *lemma* neg_comp
- \+ *lemma* sub_comp



## [2020-10-13 06:30:22](https://github.com/leanprover-community/mathlib/commit/7fff35f)
chore(algebra/pointwise): remove `@[simp]` from `singleton_one`/`singleton_zero` ([#4592](https://github.com/leanprover-community/mathlib/pull/4592))
This lemma simplified `{1}` and `{0}` to `1` and `0` making them unusable for other `singleton` lemmas.
#### Estimated changes
modified src/algebra/pointwise.lean
- \+ *lemma* preimage_mul_left_singleton
- \+ *lemma* preimage_mul_right_singleton

modified src/ring_theory/fractional_ideal.lean

modified src/topology/metric_space/gromov_hausdorff.lean



## [2020-10-13 06:30:20](https://github.com/leanprover-community/mathlib/commit/c9ae9e6)
chore(linear_algebra/dimension): more same-universe versions of `is_basis.mk_eq_dim` ([#4591](https://github.com/leanprover-community/mathlib/pull/4591))
While all the `lift` magic is good for general theory, it is not that convenient for the case when everything is in `Type`.
* add `mk_eq_mk_of_basis'`: same-universe version of `mk_eq_mk_of_basis`;
* generalize `is_basis.mk_eq_dim''` to any index type in the same universe as `V`, not necessarily `s : set V`;
* reorder lemmas to optimize the total length of the proofs;
* drop one `finite_dimensional` assumption in `findim_of_infinite_dimensional`.
#### Estimated changes
modified src/field_theory/tower.lean
- \+/\- *theorem* findim_mul_findim
- \+/\- *theorem* findim_mul_findim

modified src/linear_algebra/dimension.lean
- \+ *theorem* mk_eq_mk_of_basis'
- \+/\- *theorem* is_basis.mk_eq_dim''
- \+/\- *theorem* is_basis.mk_range_eq_dim
- \+/\- *theorem* is_basis.mk_range_eq_dim
- \+/\- *theorem* is_basis.mk_eq_dim''

modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* findim_of_infinite_dimensional



## [2020-10-13 04:39:56](https://github.com/leanprover-community/mathlib/commit/766d860)
fix(big_operators): fix imports ([#4588](https://github.com/leanprover-community/mathlib/pull/4588))
Previously `algebra.big_operators.pi` imported `algebra.big_operators.default`. That import direction is now reversed.
#### Estimated changes
modified src/algebra/big_operators/default.lean

modified src/algebra/big_operators/pi.lean

modified src/data/polynomial/iterated_deriv.lean

modified src/deprecated/submonoid.lean



## [2020-10-13 03:48:58](https://github.com/leanprover-community/mathlib/commit/505b969)
feat(archive/imo): formalize IMO 1962 problem Q1 ([#4450](https://github.com/leanprover-community/mathlib/pull/4450))
The problem statement:
Find the smallest natural number $n$ which has the following properties:
(a) Its decimal representation has 6 as the last digit.
(b) If the last digit 6 is erased and placed in front of the remaining digits,
the resulting number is four times as large as the original number $n$.
This is a proof that 153846 is the smallest member of the set satisfying these conditions.
#### Estimated changes
created archive/imo/imo1962_q1.lean
- \+ *lemma* without_digits
- \+ *lemma* case_0_digit
- \+ *lemma* case_1_digit
- \+ *lemma* case_2_digit
- \+ *lemma* case_3_digit
- \+ *lemma* case_4_digit
- \+ *lemma* helper_5_digit
- \+ *lemma* case_5_digit
- \+ *lemma* case_more_digits
- \+ *lemma* satisfied_by_153846
- \+ *lemma* no_smaller_solutions
- \+ *theorem* imo1962_q1
- \+ *def* problem_predicate



## [2020-10-13 02:01:14](https://github.com/leanprover-community/mathlib/commit/e957269)
chore(scripts): update nolints.txt ([#4587](https://github.com/leanprover-community/mathlib/pull/4587))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt

modified scripts/nolints.txt



## [2020-10-13 02:01:12](https://github.com/leanprover-community/mathlib/commit/9eb341a)
feat(mv_polynomial): minor simplification in coeff_mul ([#4586](https://github.com/leanprover-community/mathlib/pull/4586))
The proof was already golfed in [#4472](https://github.com/leanprover-community/mathlib/pull/4472).
Use `×` instead of `sigma`.
Shorten one line over 100 chars.
#### Estimated changes
modified src/data/mv_polynomial/basic.lean



## [2020-10-13 02:01:09](https://github.com/leanprover-community/mathlib/commit/7dcaee1)
feat(archive/imo): formalize IMO 1962 problem 4 ([#4518](https://github.com/leanprover-community/mathlib/pull/4518))
The problem statement: Solve the equation `cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1`.
There are a bunch of trig formulas I proved along the way; there are sort of an infinite number of trig formulas so I'm open to feedback on whether some should go in the core libraries. Also possibly some of them have a shorter proof that would render the lemma unnecessary.
For what it's worth, the actual method of solution is not how a human would do it; a more intuitive human method is to simplify in terms of `cos x` and then solve, but I think this is simpler in Lean because it doesn't rely on solving `cos x = y` for several different `y`.
#### Estimated changes
created archive/imo/imo1962_q4.lean
- \+ *lemma* cos_sum_equiv
- \+ *lemma* alt_equiv
- \+ *lemma* finding_zeros
- \+ *lemma* solve_cos2_half
- \+ *lemma* solve_cos3x_0
- \+ *theorem* imo1962_q4
- \+ *def* problem_equation
- \+ *def* solution_set
- \+ *def* alt_formula

modified src/data/complex/exponential.lean
- \+ *lemma* cosh_square
- \+ *lemma* sinh_square
- \+ *lemma* cosh_two_mul
- \+ *lemma* sinh_two_mul
- \+ *lemma* cosh_three_mul
- \+ *lemma* sinh_three_mul
- \+ *lemma* cos_square'
- \+ *lemma* cos_three_mul
- \+ *lemma* sin_three_mul
- \+ *lemma* cos_two_mul'
- \+ *lemma* cos_square'
- \+ *lemma* cos_three_mul
- \+ *lemma* sin_three_mul
- \+ *lemma* cosh_add_sinh
- \+ *lemma* sinh_add_cosh
- \+/\- *lemma* cosh_sq_sub_sinh_sq
- \+ *lemma* cosh_square
- \+ *lemma* sinh_square
- \+ *lemma* cosh_two_mul
- \+ *lemma* sinh_two_mul
- \+ *lemma* cosh_three_mul
- \+ *lemma* sinh_three_mul
- \+/\- *lemma* cosh_sq_sub_sinh_sq



## [2020-10-13 02:01:07](https://github.com/leanprover-community/mathlib/commit/b231d8e)
feat(archive/imo): formalize IMO 1960 problem 1 ([#4366](https://github.com/leanprover-community/mathlib/pull/4366))
The problem:
Determine all three-digit numbers $N$ having the property that $N$ is divisible by 11, and
$\dfrac{N}{11}$ is equal to the sum of the squares of the digits of $N$.
Art of Problem Solving offers three solutions to this problem - https://artofproblemsolving.com/wiki/index.php/1960_IMO_Problems/Problem_1 - but they all involve a fairly large amount of bashing through cases and solving basic algebra. This proof is also essentially bashing through cases, using the `iterate` tactic and calls to `norm_num`.
#### Estimated changes
created archive/imo/imo1960_q1.lean
- \+ *lemma* not_zero
- \+ *lemma* ge_100
- \+ *lemma* lt_1000
- \+ *lemma* search_up_to_start
- \+ *lemma* search_up_to_step
- \+ *lemma* search_up_to_end
- \+ *lemma* right_direction
- \+ *lemma* left_direction
- \+ *theorem* imo1960_q1
- \+ *def* sum_of_squares
- \+ *def* problem_predicate
- \+ *def* solution_predicate
- \+ *def* search_up_to



## [2020-10-12 23:17:41](https://github.com/leanprover-community/mathlib/commit/a6d445d)
feat(data/finsupp): Add `map_finsupp_prod` to homs ([#4585](https://github.com/leanprover-community/mathlib/pull/4585))
This is a convenience alias for `map_prod`, which is awkward to use.
#### Estimated changes
modified src/data/finsupp/basic.lean
- \+ *lemma* mul_equiv.map_finsupp_prod
- \+ *lemma* monoid_hom.map_finsupp_prod
- \+ *lemma* ring_hom.map_finsupp_sum
- \+ *lemma* ring_hom.map_finsupp_prod



## [2020-10-12 23:17:40](https://github.com/leanprover-community/mathlib/commit/d1bb5ea)
feat(topology/category/Compactum): Compact Hausdorff spaces ([#4555](https://github.com/leanprover-community/mathlib/pull/4555))
This PR provides the equivalence between the category of compact Hausdorff topological spaces and the category of algebras for the ultrafilter monad.
## Notation
1. `Compactum` is the category of algebras for the ultrafilter monad. It's a wrapper around `monad.algebra (of_type_functor $ ultrafilter)`.
2. `CompHaus` is the full subcategory of `Top` consisting of topological spaces which are compact and Hausdorff.
#### Estimated changes
created src/data/set/constructions.lean
- \+ *lemma* finite_inter_mem
- \+ *lemma* finite_inter_closure_insert
- \+ *def* finite_inter_closure_has_finite_inter

modified src/order/filter/ultrafilter.lean
- \+ *lemma* ultrafilter_iff_compl_mem_iff_not_mem'
- \+ *lemma* ne_empty_of_mem_ultrafilter
- \+ *lemma* nonempty_of_mem_ultrafilter

modified src/topology/basic.lean
- \+ *def* Lim'
- \+ *def* filter.ultrafilter.Lim

created src/topology/category/CompHaus.lean
- \+ *def* CompHaus_to_Top

created src/topology/category/Compactum.lean
- \+ *lemma* str_incl
- \+ *lemma* str_hom_commute
- \+ *lemma* join_distrib
- \+ *lemma* is_closed_cl
- \+ *lemma* str_eq_of_le_nhds
- \+ *lemma* le_nhds_of_str_eq
- \+ *lemma* Lim_eq_str
- \+ *lemma* cl_eq_closure
- \+ *lemma* continuous_of_hom
- \+ *lemma* faithful
- \+ *theorem* is_closed_iff
- \+ *def* Compactum
- \+ *def* forget
- \+ *def* free
- \+ *def* adj
- \+ *def* str
- \+ *def* join
- \+ *def* incl
- \+ *def* hom_of_continuous
- \+ *def* Compactum_to_CompHaus
- \+ *def* full

modified src/topology/separation.lean
- \+ *lemma* is_open_iff_ultrafilter'



## [2020-10-12 23:17:37](https://github.com/leanprover-community/mathlib/commit/bc77a23)
feat(data/list/*): add left- and right-biased versions of map₂ and zip ([#4512](https://github.com/leanprover-community/mathlib/pull/4512))
When given lists of different lengths, `map₂` and `zip` truncate the output to
the length of the shorter input list. This commit adds variations on `map₂` and
`zip` whose output is always as long as the left/right input.
#### Estimated changes
modified src/data/list/basic.lean
- \+ *theorem* map₂_flip
- \+ *theorem* map₂_left'_nil_right
- \+ *theorem* map₂_right'_nil_left
- \+ *theorem* map₂_right'_nil_right
- \+ *theorem* map₂_right'_nil_cons
- \+ *theorem* map₂_right'_cons_cons
- \+ *theorem* zip_left'_nil_right
- \+ *theorem* zip_left'_nil_left
- \+ *theorem* zip_left'_cons_nil
- \+ *theorem* zip_left'_cons_cons
- \+ *theorem* zip_right'_nil_left
- \+ *theorem* zip_right'_nil_right
- \+ *theorem* zip_right'_nil_cons
- \+ *theorem* zip_right'_cons_cons
- \+ *theorem* map₂_left_nil_right
- \+ *theorem* map₂_left_eq_map₂_left'
- \+ *theorem* map₂_left_eq_map₂
- \+ *theorem* map₂_right_nil_left
- \+ *theorem* map₂_right_nil_right
- \+ *theorem* map₂_right_nil_cons
- \+ *theorem* map₂_right_cons_cons
- \+ *theorem* map₂_right_eq_map₂_right'
- \+ *theorem* map₂_right_eq_map₂
- \+ *theorem* zip_left_nil_right
- \+ *theorem* zip_left_nil_left
- \+ *theorem* zip_left_cons_nil
- \+ *theorem* zip_left_cons_cons
- \+ *theorem* zip_left_eq_zip_left'
- \+ *theorem* zip_right_nil_left
- \+ *theorem* zip_right_nil_right
- \+ *theorem* zip_right_nil_cons
- \+ *theorem* zip_right_cons_cons
- \+ *theorem* zip_right_eq_zip_right'

modified src/data/list/defs.lean
- \+ *def* map₂_left'
- \+ *def* map₂_right'
- \+ *def* zip_left'
- \+ *def* zip_right'
- \+ *def* map₂_left
- \+ *def* map₂_right
- \+ *def* zip_left
- \+ *def* zip_right



## [2020-10-12 20:50:13](https://github.com/leanprover-community/mathlib/commit/d3d70f1)
chore(algebra/order*): move `abs`/`min`/`max`, review ([#4581](https://github.com/leanprover-community/mathlib/pull/4581))
* make `algebra.ordered_group` import `algebra.order_functions`, not vice versa;
* move some proofs from `algebra.ordered_functions` to `algebra.ordered_group` and `algebra.ordered_ring`;
* deduplicate API;
* golf some proofs.
#### Estimated changes
modified archive/sensitivity.lean

modified src/algebra/group_power/basic.lean

modified src/algebra/order_functions.lean
- \+/\- *lemma* min_le_iff
- \+/\- *lemma* le_max_iff
- \+/\- *lemma* min_le_iff
- \+/\- *lemma* le_max_iff
- \- *lemma* min_sub
- \- *lemma* fn_min_mul_fn_max
- \- *lemma* min_mul_max
- \- *lemma* abs_add
- \- *lemma* abs_lt
- \- *lemma* lt_abs
- \- *lemma* abs_sub_le_iff
- \- *lemma* abs_sub_lt_iff
- \- *lemma* sub_abs_le_abs_sub
- \- *lemma* abs_abs_sub_le_abs_sub
- \- *lemma* abs_eq
- \- *lemma* abs_eq_zero
- \- *lemma* abs_pos_iff
- \- *lemma* abs_nonpos_iff
- \- *lemma* abs_le_max_abs_abs
- \- *lemma* min_le_add_of_nonneg_right
- \- *lemma* min_le_add_of_nonneg_left
- \- *lemma* max_le_add_of_nonneg
- \- *lemma* max_zero_sub_eq_self
- \- *lemma* abs_max_sub_max_le_abs
- \- *lemma* max_sub_min_eq_abs'
- \- *lemma* max_sub_min_eq_abs
- \- *lemma* mul_max_of_nonneg
- \- *lemma* mul_min_of_nonneg
- \- *lemma* max_mul_of_nonneg
- \- *lemma* min_mul_of_nonneg
- \- *lemma* abs_one
- \- *lemma* max_mul_mul_le_max_mul_max
- \- *theorem* abs_le
- \- *theorem* abs_le_abs

modified src/algebra/ordered_field.lean
- \+ *lemma* min_div_div_right
- \+ *lemma* max_div_div_right
- \+ *lemma* min_div_div_right_of_nonpos
- \+ *lemma* max_div_div_right_of_nonpos

modified src/algebra/ordered_group.lean
- \+ *lemma* fn_min_mul_fn_max
- \+ *lemma* min_mul_max
- \+ *lemma* min_le_add_of_nonneg_right
- \+ *lemma* min_le_add_of_nonneg_left
- \+ *lemma* max_le_add_of_nonneg
- \+/\- *lemma* min_neg_neg
- \+/\- *lemma* max_neg_neg
- \+ *lemma* min_sub_sub_right
- \+ *lemma* max_sub_sub_right
- \+ *lemma* min_sub_sub_left
- \+ *lemma* max_sub_sub_left
- \+ *lemma* max_zero_sub_eq_self
- \+/\- *lemma* abs_of_nonneg
- \+/\- *lemma* abs_of_pos
- \+/\- *lemma* abs_of_nonpos
- \+/\- *lemma* abs_of_neg
- \+/\- *lemma* abs_zero
- \+/\- *lemma* abs_neg
- \+ *lemma* abs_pos
- \+/\- *lemma* abs_pos_of_pos
- \+/\- *lemma* abs_pos_of_neg
- \+/\- *lemma* le_abs_self
- \+/\- *lemma* neg_le_abs_self
- \+/\- *lemma* abs_nonneg
- \+/\- *lemma* abs_abs
- \+ *lemma* abs_eq_zero
- \+ *lemma* abs_nonpos_iff
- \+ *lemma* abs_lt
- \+ *lemma* lt_abs
- \+ *lemma* max_sub_min_eq_abs'
- \+ *lemma* max_sub_min_eq_abs
- \+ *lemma* abs_add
- \+ *lemma* abs_sub_le_iff
- \+ *lemma* abs_sub_lt_iff
- \+/\- *lemma* abs_sub_abs_le_abs_sub
- \+ *lemma* abs_abs_sub_abs_le_abs_sub
- \+ *lemma* abs_eq
- \+ *lemma* abs_le_max_abs_abs
- \+ *lemma* abs_max_sub_max_le_abs
- \+ *lemma* eq_of_abs_sub_nonpos
- \+/\- *lemma* max_neg_neg
- \- *lemma* min_eq_neg_max_neg_neg
- \+/\- *lemma* min_neg_neg
- \- *lemma* max_eq_neg_min_neg_neg
- \+/\- *lemma* abs_of_nonneg
- \+/\- *lemma* abs_of_pos
- \+/\- *lemma* abs_of_nonpos
- \+/\- *lemma* abs_of_neg
- \+/\- *lemma* abs_zero
- \+/\- *lemma* abs_neg
- \+/\- *lemma* abs_pos_of_pos
- \+/\- *lemma* abs_pos_of_neg
- \- *lemma* ne_zero_of_abs_ne_zero
- \+/\- *lemma* abs_nonneg
- \+/\- *lemma* abs_abs
- \+/\- *lemma* le_abs_self
- \+/\- *lemma* neg_le_abs_self
- \- *lemma* eq_zero_of_abs_eq_zero
- \- *lemma* abs_pos_of_ne_zero
- \- *lemma* abs_le_of_le_of_neg_le
- \- *lemma* abs_lt_of_lt_of_neg_lt
- \- *lemma* abs_add_le_abs_add_abs
- \+/\- *lemma* abs_sub_abs_le_abs_sub
- \- *lemma* decidable_linear_ordered_add_comm_group.eq_of_abs_sub_nonpos
- \+ *theorem* abs_le'
- \+ *theorem* abs_le
- \+ *theorem* abs_le_abs

modified src/algebra/ordered_ring.lean
- \+ *lemma* mul_max_of_nonneg
- \+ *lemma* mul_min_of_nonneg
- \+ *lemma* max_mul_of_nonneg
- \+ *lemma* min_mul_of_nonneg
- \+ *lemma* abs_one
- \+ *lemma* max_mul_mul_le_max_mul_max
- \- *lemma* abs_abs_sub_abs_le_abs_sub
- \+ *def* abs_hom
- \+ *def* to_ordered_ring
- \+ *def* to_linear_order
- \+ *def* to_linear_ordered_ring

modified src/analysis/special_functions/exp_log.lean

modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* rpow_zero
- \+/\- *lemma* zero_rpow
- \+/\- *lemma* rpow_one
- \+/\- *lemma* one_rpow
- \+/\- *lemma* zero_rpow_le_one
- \+/\- *lemma* zero_rpow_nonneg
- \+/\- *lemma* rpow_nonneg_of_nonneg
- \+/\- *lemma* rpow_zero
- \+/\- *lemma* zero_rpow
- \+/\- *lemma* rpow_one
- \+/\- *lemma* one_rpow
- \+/\- *lemma* zero_rpow_le_one
- \+/\- *lemma* zero_rpow_nonneg
- \+/\- *lemma* rpow_nonneg_of_nonneg

modified src/data/int/basic.lean

modified src/data/real/hyperreal.lean

modified src/data/set/intervals/basic.lean

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/measure_theory/bochner_integration.lean

modified src/measure_theory/l1_space.lean

modified src/tactic/monotonicity/basic.lean

modified src/topology/instances/real.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean



## [2020-10-12 20:50:11](https://github.com/leanprover-community/mathlib/commit/6ea6200)
feat(tactic/rcases): rcases_many ([#4569](https://github.com/leanprover-community/mathlib/pull/4569))
This allows you to pattern match many variables at once, using the
syntax `obtain ⟨a|b, c|d⟩ := ⟨x, y⟩`. This doesn't require any change
to the front end documentation, as it is in some sense the obvious thing,
but this doesn't break any existing uses because this could never work
before (since the expected type of the tuple expression is not known).
#### Estimated changes
modified src/tactic/core.lean

modified src/tactic/rcases.lean

modified test/rcases.lean



## [2020-10-12 20:50:09](https://github.com/leanprover-community/mathlib/commit/9bed456)
feta(data/fin): induction principle on fin (n + 1) ([#4546](https://github.com/leanprover-community/mathlib/pull/4546))
#### Estimated changes
modified src/data/fin.lean
- \+ *theorem* cases_succ'
- \+ *def* induction
- \+ *def* induction_on

modified src/data/matrix/notation.lean



## [2020-10-12 20:50:06](https://github.com/leanprover-community/mathlib/commit/8ccfb0a)
chore(control/functor): linting ([#4496](https://github.com/leanprover-community/mathlib/pull/4496))
#### Estimated changes
modified src/control/functor.lean



## [2020-10-12 18:08:56](https://github.com/leanprover-community/mathlib/commit/9713e96)
chore(*): update to Lean 3.21.0c ([#4578](https://github.com/leanprover-community/mathlib/pull/4578))
The only real change is the removal of notation for `vector.cons`.
#### Estimated changes
modified leanpkg.toml

modified src/computability/halting.lean

modified src/computability/primrec.lean

modified src/computability/tm_to_partrec.lean

modified src/computability/turing_machine.lean

modified src/data/bitvec/core.lean

modified src/data/num/bitwise.lean

modified src/data/sym.lean
- \+/\- *lemma* cons_of_coe_eq
- \+/\- *lemma* cons_of_coe_eq

modified src/data/vector2.lean
- \+/\- *theorem* cons_val
- \+/\- *theorem* cons_head
- \+/\- *theorem* cons_tail
- \+/\- *theorem* cons_val
- \+/\- *theorem* cons_head
- \+/\- *theorem* cons_tail

modified src/group_theory/sylow.lean
- \+/\- *lemma* mem_fixed_points_mul_left_cosets_iff_mem_normalizer
- \+/\- *lemma* mem_fixed_points_mul_left_cosets_iff_mem_normalizer

modified src/number_theory/sum_four_squares.lean

modified src/topology/list.lean



## [2020-10-12 18:08:53](https://github.com/leanprover-community/mathlib/commit/6816b83)
feat(archive/100-theorems-list/70_perfect_numbers): Direction 1 of the Perfect Number Theorem ([#4544](https://github.com/leanprover-community/mathlib/pull/4544))
Proves Euclid's half of the Euclid-Euler Theorem that if `2 ^ (k + 1) - 1` is prime, then `2 ^ k * (2 ^ (k + 1) - 1)` is an (even) perfect number.
#### Estimated changes
created archive/100-theorems-list/70_perfect_numbers.lean
- \+ *lemma* odd_mersenne_succ
- \+ *lemma* sigma_two_pow_eq_mersenne_succ
- \+ *lemma* ne_zero_of_prime_mersenne
- \+ *theorem* perfect_two_pow_mul_mersenne_of_prime
- \+ *theorem* even_two_pow_mul_mersenne_of_prime

modified src/number_theory/arithmetic_function.lean
- \+ *lemma* sigma_one_apply

modified src/number_theory/divisors.lean
- \+ *lemma* mem_divisors_prime_pow
- \+ *lemma* divisors_prime
- \+ *lemma* divisors_prime_pow
- \+ *lemma* sum_divisors_prime
- \+ *lemma* prod_divisors_prime
- \+ *lemma* sum_divisors_prime_pow
- \+ *lemma* prod_divisors_prime_pow
- \+/\- *theorem* perfect_iff_sum_proper_divisors
- \+/\- *theorem* perfect_iff_sum_divisors_eq_two_mul
- \+/\- *theorem* perfect_iff_sum_proper_divisors
- \+/\- *theorem* perfect_iff_sum_divisors_eq_two_mul
- \+/\- *def* perfect
- \+/\- *def* perfect

modified src/number_theory/lucas_lehmer.lean
- \+ *lemma* succ_mersenne



## [2020-10-12 17:14:21](https://github.com/leanprover-community/mathlib/commit/9379050)
chore(data/hash_map): linting ([#4498](https://github.com/leanprover-community/mathlib/pull/4498))
#### Estimated changes
modified src/data/hash_map.lean



## [2020-10-12 14:57:35](https://github.com/leanprover-community/mathlib/commit/266895f)
fix(algebra/ordered_group): use `add_neg` in autogenerated lemma name ([#4580](https://github.com/leanprover-community/mathlib/pull/4580))
Explicitly add `sub_le_sub_iff` with `a - b`.
#### Estimated changes
modified src/algebra/linear_ordered_comm_group_with_zero.lean

modified src/algebra/ordered_group.lean
- \+/\- *lemma* div_le_div_iff'
- \+ *lemma* sub_le_sub_iff
- \+/\- *lemma* div_le_div_iff'



## [2020-10-12 14:57:33](https://github.com/leanprover-community/mathlib/commit/b3ce883)
feat(algebra/*_power): simplify `(-a)^(bit0 _)` and `(-a)^(bit1 _)` ([#4573](https://github.com/leanprover-community/mathlib/pull/4573))
Works for `pow` and `fpow`. Also simplify powers of `I : ℂ`.
#### Estimated changes
modified src/algebra/field_power.lean
- \+ *lemma* neg_fpow_bit0
- \+ *lemma* neg_fpow_bit1

modified src/algebra/group_power/basic.lean
- \+ *theorem* pow_bit0'
- \+ *theorem* bit0_nsmul'
- \+ *theorem* pow_bit1'
- \+ *theorem* bit1_nsmul'
- \+ *theorem* neg_pow_bit0
- \+ *theorem* neg_pow_bit1

modified src/algebra/group_power/lemmas.lean

modified src/algebra/group_with_zero_power.lean
- \+ *lemma* fpow_add'
- \+ *theorem* fpow_bit0
- \+ *theorem* fpow_bit1
- \+ *theorem* fpow_bit0'
- \+ *theorem* fpow_bit1'

modified src/data/complex/basic.lean
- \+ *lemma* I_pow_bit0
- \+ *lemma* I_pow_bit1
- \+ *lemma* I_fpow_bit0
- \+ *lemma* I_fpow_bit1

modified src/data/int/basic.lean
- \+/\- *lemma* bodd_two
- \+ *lemma* bodd_bit0
- \+ *lemma* bodd_bit1
- \+ *lemma* bit0_ne_bit1
- \+ *lemma* bit1_ne_bit0
- \+ *lemma* bit1_ne_zero
- \+/\- *lemma* bodd_two



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
created archive/imo/imo2020_q2.lean
- \+ *theorem* imo2020_q2

modified src/analysis/mean_inequalities.lean
- \+ *theorem* geom_mean_le_arith_mean4_weighted
- \+ *theorem* geom_mean_le_arith_mean3_weighted
- \+ *theorem* geom_mean_le_arith_mean4_weighted



## [2020-10-12 14:57:28](https://github.com/leanprover-community/mathlib/commit/5022425)
feat(algebra/free_algebra): Add an inductive principle ([#4335](https://github.com/leanprover-community/mathlib/pull/4335))
#### Estimated changes
modified src/algebra/free_algebra.lean
- \+ *lemma* induction



## [2020-10-12 14:57:26](https://github.com/leanprover-community/mathlib/commit/3d1f16a)
feat(analysis/normed_space/multilinear): define `mk_pi_algebra` ([#4316](https://github.com/leanprover-community/mathlib/pull/4316))
I'm going to use this definition for converting `(mv_)power_series` to `formal_multilinear_series`.
#### Estimated changes
modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* mk_pi_algebra_apply
- \+ *lemma* norm_mk_pi_algebra_le
- \+ *lemma* norm_mk_pi_algebra_of_empty
- \+ *lemma* norm_mk_pi_algebra
- \+ *lemma* mk_pi_algebra_fin_apply
- \+ *lemma* norm_mk_pi_algebra_fin_succ_le
- \+ *lemma* norm_mk_pi_algebra_fin_le_of_pos
- \+ *lemma* norm_mk_pi_algebra_fin_zero
- \+ *lemma* norm_mk_pi_algebra_fin
- \+ *lemma* mk_pi_field_apply_one_eq_self
- \- *lemma* mk_pi_ring_apply_one_eq_self

modified src/linear_algebra/multilinear.lean
- \+ *lemma* coe_comp_multilinear_map
- \+ *lemma* comp_multilinear_map_apply
- \+ *lemma* mk_pi_algebra_apply
- \+ *lemma* mk_pi_algebra_fin_apply
- \+ *lemma* mk_pi_algebra_fin_apply_const
- \+ *lemma* smul_right_apply
- \+/\- *def* comp_multilinear_map
- \+ *def* smul_right
- \+/\- *def* comp_multilinear_map

modified src/topology/algebra/multilinear.lean
- \+ *theorem* to_multilinear_map_inj



## [2020-10-12 12:21:50](https://github.com/leanprover-community/mathlib/commit/1362701)
refactor(field_theory): Adjoin intermediate field ([#4468](https://github.com/leanprover-community/mathlib/pull/4468))
Refactor adjoin to be an intermediate field rather than a subalgebra.
#### Estimated changes
modified src/field_theory/adjoin.lean
- \+ *lemma* adjoin_le_iff
- \+ *lemma* gc
- \+ *lemma* mem_bot
- \+ *lemma* mem_top
- \+ *lemma* bot_to_subalgebra
- \+ *lemma* top_to_subalgebra
- \+ *lemma* coe_bot_eq_self
- \+ *lemma* coe_top_eq_top
- \+/\- *lemma* adjoin.mono
- \+/\- *lemma* adjoin_contains_field_as_subfield
- \+/\- *lemma* subset_adjoin_of_subset_left
- \+ *lemma* adjoin_le_subfield
- \+/\- *lemma* adjoin_adjoin_left
- \+ *lemma* adjoin_map
- \+ *lemma* algebra_adjoin_le_adjoin
- \+ *lemma* adjoin_le_algebra_adjoin
- \+ *lemma* adjoin_induction
- \+/\- *lemma* adjoin_simple_adjoin_simple
- \+/\- *lemma* adjoin_simple_comm
- \+/\- *lemma* adjoin_eq_bot_iff
- \+/\- *lemma* adjoin_simple_eq_bot_iff
- \+/\- *lemma* adjoin_zero
- \+/\- *lemma* adjoin_one
- \+ *lemma* adjoin_int
- \+ *lemma* adjoin_nat
- \+ *lemma* dim_intermediate_field_eq_dim_subalgebra
- \+ *lemma* findim_intermediate_field_eq_findim_subalgebra
- \+ *lemma* to_subalgebra_eq_iff
- \+ *lemma* dim_adjoin_eq_one_iff
- \+ *lemma* dim_adjoin_simple_eq_one_iff
- \+ *lemma* findim_adjoin_eq_one_iff
- \+ *lemma* findim_adjoin_simple_eq_one_iff
- \+/\- *lemma* bot_eq_top_of_dim_adjoin_eq_one
- \+ *lemma* subsingleton_of_dim_adjoin_eq_one
- \+ *lemma* subsingleton_of_findim_adjoin_eq_one
- \+ *lemma* subsingleton_of_findim_adjoin_le_one
- \+ *lemma* induction_on_adjoin
- \+/\- *lemma* subset_adjoin_of_subset_left
- \+/\- *lemma* adjoin.mono
- \+/\- *lemma* adjoin_contains_field_as_subfield
- \- *lemma* adjoin_subset_subfield
- \- *lemma* adjoin_subset_iff
- \- *lemma* subfield_subset_adjoin_self
- \+/\- *lemma* adjoin_adjoin_left
- \+/\- *lemma* adjoin_simple_adjoin_simple
- \+/\- *lemma* adjoin_simple_comm
- \- *lemma* adjoin_eq_bot
- \- *lemma* adjoin_simple_eq_bot
- \+/\- *lemma* adjoin_zero
- \+/\- *lemma* adjoin_one
- \- *lemma* sub_bot_of_adjoin_sub_bot
- \- *lemma* mem_bot_of_adjoin_simple_sub_bot
- \+/\- *lemma* adjoin_eq_bot_iff
- \+/\- *lemma* adjoin_simple_eq_bot_iff
- \- *lemma* sub_bot_of_adjoin_dim_eq_one
- \- *lemma* mem_bot_of_adjoin_simple_dim_eq_one
- \- *lemma* adjoin_dim_eq_one_of_sub_bot
- \- *lemma* adjoin_simple_dim_eq_one_of_mem_bot
- \- *lemma* adjoin_dim_eq_one_iff
- \- *lemma* adjoin_simple_dim_eq_one_iff
- \- *lemma* adjoin_findim_eq_one_iff
- \- *lemma* adjoin_simple_findim_eq_one_iff
- \+/\- *lemma* bot_eq_top_of_dim_adjoin_eq_one
- \+/\- *def* adjoin
- \+ *def* gi
- \+/\- *def* adjoin

modified src/field_theory/intermediate_field.lean
- \+/\- *lemma* pow_mem
- \+ *lemma* mem_lift2
- \+/\- *lemma* pow_mem
- \+ *def* lift1
- \+ *def* lift2

modified src/field_theory/primitive_element.lean
- \- *theorem* exists_primitive_element_inf
- \- *theorem* exists_primitive_element_aux

modified src/field_theory/subfield.lean

modified src/order/bounded_lattice.lean
- \+ *lemma* eq_bot_of_bot_eq_top
- \+ *lemma* eq_top_of_bot_eq_top
- \+ *lemma* subsingleton_of_bot_eq_top



## [2020-10-12 10:16:23](https://github.com/leanprover-community/mathlib/commit/8fa9125)
feat(data/polynomial/degree/erase_lead): definition and basic lemmas ([#4527](https://github.com/leanprover-community/mathlib/pull/4527))
erase_lead serves as the reduction step in an induction, breaking off one monomial from a polynomial.  It is used in a later PR to prove that reverse is a multiplicative monoid map on polynomials.
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *theorem* subset_of_eq
- \+ *theorem* pred_card_le_card_erase

modified src/data/finsupp/basic.lean
- \+ *lemma* card_support_eq_zero
- \+ *lemma* eq_single_iff
- \+ *lemma* support_eq_singleton
- \+ *lemma* support_eq_singleton'
- \+ *lemma* card_support_eq_one
- \+ *lemma* card_support_eq_one'
- \+ *lemma* erase_zero

modified src/data/polynomial/basic.lean
- \+ *lemma* X_pow_eq_monomial
- \- *lemma* monomial_eq_X_pow

modified src/data/polynomial/degree.lean
- \+ *lemma* monomial_nat_degree_leading_coeff_eq_self
- \+ *lemma* C_mul_X_pow_eq_self

modified src/data/polynomial/degree/basic.lean
- \+ *lemma* nat_degree_monomial
- \+ *lemma* leading_coeff_monomial'

created src/data/polynomial/erase_lead.lean
- \+ *lemma* erase_lead_support
- \+ *lemma* erase_lead_coeff
- \+ *lemma* erase_lead_coeff_nat_degree
- \+ *lemma* erase_lead_coeff_of_ne
- \+ *lemma* erase_lead_zero
- \+ *lemma* erase_lead_add_monomial_nat_degree_leading_coeff
- \+ *lemma* erase_lead_add_C_mul_X_pow
- \+ *lemma* self_sub_monomial_nat_degree_leading_coeff
- \+ *lemma* self_sub_C_mul_X_pow
- \+ *lemma* erase_lead_ne_zero
- \+ *lemma* nat_degree_not_mem_erase_lead_support
- \+ *lemma* ne_nat_degree_of_mem_erase_lead_support
- \+ *lemma* erase_lead_support_card_lt
- \+ *lemma* erase_lead_monomial
- \+ *lemma* erase_lead_C
- \+ *lemma* erase_lead_X
- \+ *lemma* erase_lead_X_pow
- \+ *lemma* erase_lead_C_mul_X_pow
- \+ *lemma* erase_lead_degree_le
- \+ *lemma* erase_lead_nat_degree_le
- \+ *lemma* erase_lead_nat_degree_lt
- \+ *def* erase_lead



## [2020-10-12 08:30:01](https://github.com/leanprover-community/mathlib/commit/0bfc68f)
feat(ring_theory/witt_vector/structure_polynomial): witt_structure_int_prop ([#4466](https://github.com/leanprover-community/mathlib/pull/4466))
This is the 3rd PR in a series on a fundamental theorem about Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
modified src/ring_theory/witt_vector/structure_polynomial.lean
- \+ *lemma* eq_witt_structure_int
- \+ *lemma* witt_structure_int_rename
- \+ *theorem* witt_structure_int_prop
- \+ *theorem* witt_structure_int_exists_unique
- \+ *theorem* witt_structure_prop



## [2020-10-12 06:33:28](https://github.com/leanprover-community/mathlib/commit/b953717)
feat(set_theory/cardinal): cardinality of powerset ([#4576](https://github.com/leanprover-community/mathlib/pull/4576))
adds a lemma for cardinality of powerset
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+ *theorem* mk_set



## [2020-10-12 01:08:24](https://github.com/leanprover-community/mathlib/commit/81b8123)
chore(scripts): update nolints.txt ([#4575](https://github.com/leanprover-community/mathlib/pull/4575))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-11 21:16:36](https://github.com/leanprover-community/mathlib/commit/665cc13)
chore(topology/algebra/group): review ([#4570](https://github.com/leanprover-community/mathlib/pull/4570))
* Ensure that we don't use `[topological_group G]` when it suffices to ask for, e.g., `[has_continuous_mul G]`.
* Introduce `[has_continuous_sub]`, add an instance for `nnreal`.
#### Estimated changes
modified src/analysis/convex/topology.lean

modified src/measure_theory/borel_space.lean

modified src/topology/algebra/group.lean
- \+/\- *lemma* is_open_map_mul_left
- \+/\- *lemma* is_closed_map_mul_left
- \+/\- *lemma* is_open_map_mul_right
- \+/\- *lemma* is_closed_map_mul_right
- \+/\- *lemma* continuous_on_inv
- \+ *lemma* continuous_within_at_inv
- \+ *lemma* continuous_at_inv
- \+/\- *lemma* tendsto_inv
- \+/\- *lemma* filter.tendsto.inv
- \+/\- *lemma* continuous.inv
- \+/\- *lemma* continuous_on.inv
- \+/\- *lemma* continuous_within_at.inv
- \+/\- *lemma* nhds_one_symm
- \+/\- *lemma* exists_nhds_split_inv
- \+/\- *lemma* nhds_translation_mul_inv
- \+/\- *lemma* filter.tendsto.sub
- \+/\- *lemma* continuous.sub
- \+ *lemma* continuous_within_at.sub
- \+/\- *lemma* continuous_on.sub
- \+/\- *lemma* nhds_translation
- \+ *lemma* is_open.mul_left
- \+ *lemma* is_open.mul_right
- \- *lemma* continuous_inv
- \+/\- *lemma* continuous.inv
- \+/\- *lemma* continuous_on_inv
- \+/\- *lemma* continuous_on.inv
- \+/\- *lemma* tendsto_inv
- \+/\- *lemma* filter.tendsto.inv
- \- *lemma* continuous_at.inv
- \+/\- *lemma* continuous_within_at.inv
- \+/\- *lemma* is_open_map_mul_left
- \+/\- *lemma* is_closed_map_mul_left
- \+/\- *lemma* is_open_map_mul_right
- \+/\- *lemma* is_closed_map_mul_right
- \+/\- *lemma* exists_nhds_split_inv
- \+/\- *lemma* nhds_one_symm
- \+/\- *lemma* nhds_translation_mul_inv
- \+/\- *lemma* continuous.sub
- \- *lemma* continuous_sub
- \+/\- *lemma* continuous_on.sub
- \+/\- *lemma* filter.tendsto.sub
- \+/\- *lemma* nhds_translation
- \- *lemma* is_open_mul_left
- \- *lemma* is_open_mul_right

modified src/topology/instances/nnreal.lean
- \- *lemma* continuous_sub
- \- *lemma* continuous.sub



## [2020-10-11 20:09:45](https://github.com/leanprover-community/mathlib/commit/952a407)
feat(data/nat/digits): add norm_digits tactic ([#4452](https://github.com/leanprover-community/mathlib/pull/4452))
This adds a basic tactic for normalizing expressions of the form `nat.digits a b = l`. As requested on Zulip: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/simplifying.20nat.2Edigits/near/212152395
#### Estimated changes
modified src/data/nat/digits.lean
- \+ *theorem* digits_zero_succ'
- \+ *theorem* digits_def'
- \+ *theorem* digits_succ
- \+ *theorem* digits_one

created test/norm_digits.lean



## [2020-10-11 20:09:43](https://github.com/leanprover-community/mathlib/commit/b1ca33e)
feat(analysis/calculus/times_cont_diff, analysis/calculus/inverse): smooth inverse function theorem ([#4407](https://github.com/leanprover-community/mathlib/pull/4407))
The inverse function theorem, in the C^k and smooth categories.
#### Estimated changes
modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_at.of_local_homeomorph

modified src/analysis/calculus/inverse.lean
- \+ *lemma* to_local_homeomorph_coe
- \+ *lemma* mem_to_local_homeomorph_source
- \+ *lemma* image_mem_to_local_homeomorph_target
- \+ *lemma* local_inverse_apply_image
- \+ *lemma* to_local_inverse
- \+ *def* to_local_homeomorph
- \+ *def* local_inverse

modified src/analysis/calculus/times_cont_diff.lean
- \+ *lemma* times_cont_diff_within_at_zero
- \+ *lemma* times_cont_diff_at_zero
- \+ *lemma* times_cont_diff_at.has_strict_fderiv_at'
- \+ *theorem* times_cont_diff_at.of_local_homeomorph



## [2020-10-11 18:49:02](https://github.com/leanprover-community/mathlib/commit/b48b4ff)
feat(analysis/normed_space/inner_product): Cauchy-Schwarz equality case and other lemmas ([#4571](https://github.com/leanprover-community/mathlib/pull/4571))
#### Estimated changes
modified src/analysis/normed_space/inner_product.lean
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square_of_inner_eq_zero
- \+ *lemma* abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
- \+ *lemma* abs_inner_div_norm_mul_norm_eq_one_iff
- \+/\- *lemma* abs_real_inner_div_norm_mul_norm_eq_one_iff
- \+ *lemma* abs_inner_eq_norm_iff
- \+ *lemma* submodule.is_compl_orthogonal_of_is_complete
- \+ *lemma* submodule.top_orthogonal_eq_bot
- \+ *lemma* submodule.bot_orthogonal_eq_top
- \+ *lemma* submodule.eq_top_iff_orthogonal_eq_bot
- \+/\- *lemma* abs_real_inner_div_norm_mul_norm_eq_one_iff
- \- *lemma* submodule.is_compl_orthogonal_of_is_complete_real
- \+/\- *def* euclidean_space
- \+/\- *def* euclidean_space

modified src/data/complex/is_R_or_C.lean
- \+ *lemma* norm_eq_abs

modified src/geometry/euclidean/basic.lean



## [2020-10-11 18:49:00](https://github.com/leanprover-community/mathlib/commit/0f085b9)
chore(linear_algebra/finite_dimensional): rename `of_finite_basis` ([#4562](https://github.com/leanprover-community/mathlib/pull/4562))
* rename `of_finite_basis` to `of_fintype_basis`;
* add new `of_finite_basis` assuming that the domain the basis is a
  `finite` set;
* allow `s : finset ι` and any function `s → V` in `of_finset_basis`.
#### Estimated changes
modified archive/sensitivity.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/field_theory/tower.lean

modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* of_fintype_basis
- \+/\- *lemma* of_finite_basis
- \+/\- *lemma* of_finset_basis
- \+/\- *lemma* of_finite_basis
- \+/\- *lemma* of_finset_basis



## [2020-10-11 16:27:35](https://github.com/leanprover-community/mathlib/commit/14dcfe0)
chore(*): assorted lemmas ([#4566](https://github.com/leanprover-community/mathlib/pull/4566))
Non-bc changes:
* make some lemmas use `coe` instead of `subtype.val`;
* make the arguments of `range_comp` explicit, reorder them.
#### Estimated changes
modified src/data/dfinsupp.lean

modified src/data/equiv/basic.lean
- \+ *lemma* option_equiv_sum_punit_symm_inl
- \+ *lemma* option_equiv_sum_punit_symm_inr
- \+/\- *def* option_equiv_sum_punit
- \+/\- *def* option_equiv_sum_punit

modified src/data/finset/basic.lean
- \+ *lemma* subtype_eq_empty

modified src/data/finsupp/basic.lean
- \+ *lemma* unique_ext
- \+ *lemma* unique_ext_iff
- \+/\- *lemma* support_emb_domain
- \+/\- *lemma* emb_domain_zero
- \+/\- *lemma* emb_domain_apply
- \+ *lemma* emb_domain_injective
- \+/\- *lemma* emb_domain_inj
- \+ *lemma* emb_domain_eq_zero
- \+ *lemma* subtype_domain_eq_zero_iff'
- \+ *lemma* subtype_domain_eq_zero_iff
- \+/\- *lemma* support_emb_domain
- \+/\- *lemma* emb_domain_zero
- \+/\- *lemma* emb_domain_apply
- \+/\- *lemma* emb_domain_inj

modified src/data/option/basic.lean
- \+ *lemma* cases_on'_none
- \+ *lemma* cases_on'_some
- \+ *lemma* cases_on'_coe
- \+ *lemma* cases_on'_none_coe

modified src/data/set/basic.lean
- \- *lemma* surjective.range_eq
- \+ *theorem* pair_comm
- \+ *theorem* is_compl_range_inl_range_inr
- \+/\- *theorem* range_comp
- \+/\- *theorem* range_comp

modified src/data/set/function.lean

modified src/data/set/lattice.lean
- \+ *theorem* subset_Inter_iff

modified src/data/sum.lean
- \+ *lemma* injective_inl
- \+ *lemma* injective_inr

modified src/logic/nontrivial.lean
- \+ *lemma* not_subsingleton

modified src/measure_theory/simple_func_dense.lean

modified src/topology/metric_space/gromov_hausdorff.lean



## [2020-10-11 16:27:33](https://github.com/leanprover-community/mathlib/commit/918e5d8)
chore(data/finsupp): replace `eq_zero_of_zero_eq_one` with `finsupp.unique_of_right` ([#4563](https://github.com/leanprover-community/mathlib/pull/4563))
Also add a lemma `semimodule.subsingleton`: if `R` is a subsingleton semiring, then any semimodule over `R` is a subsingleton.
#### Estimated changes
modified src/algebra/group/units.lean
- \+ *lemma* is_unit_of_subsingleton

modified src/algebra/group_with_zero.lean
- \+/\- *lemma* mul_eq_zero_of_ne_zero_imp_eq_zero
- \+/\- *lemma* mul_eq_zero_of_ne_zero_imp_eq_zero
- \+ *theorem* subsingleton_iff_zero_eq_one
- \- *theorem* subsingleton_of_zero_eq_one

modified src/algebra/module/basic.lean
- \+ *theorem* semimodule.subsingleton

modified src/data/finsupp/basic.lean

modified src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent_of_subsingleton
- \- *lemma* linear_independent_of_zero_eq_one



## [2020-10-11 15:12:38](https://github.com/leanprover-community/mathlib/commit/33f7870)
chore(measure_theory/measurable_space): add `finset.is_measurable_bUnion` etc ([#4553](https://github.com/leanprover-community/mathlib/pull/4553))
I always forget how to convert `finset` or `set.finite` to `set.countable. Also `finset.is_measurable_bUnion` uses `finset`'s `has_mem`, not coercion to `set`.
Also replace `tendsto_at_top_supr_nat` etc with slightly more general versions using a `[semilattice_sup β] [nonempty β]` instead of `nat`.
#### Estimated changes
modified src/measure_theory/borel_space.lean

modified src/measure_theory/measurable_space.lean
- \+ *lemma* set.finite.is_measurable_bUnion
- \+ *lemma* finset.is_measurable_bUnion
- \+ *lemma* set.finite.is_measurable_sUnion
- \+ *lemma* set.finite.is_measurable_bInter
- \+ *lemma* finset.is_measurable_bInter
- \+ *lemma* set.finite.is_measurable_sInter

modified src/measure_theory/measure_space.lean

modified src/topology/algebra/ordered.lean
- \+ *lemma* tendsto_at_top_cinfi
- \+ *lemma* tendsto_at_top_infi
- \+/\- *lemma* supr_eq_of_tendsto
- \+/\- *lemma* infi_eq_of_tendsto
- \- *lemma* tendsto_at_top_supr_nat
- \- *lemma* tendsto_at_top_infi_nat
- \+/\- *lemma* supr_eq_of_tendsto
- \+/\- *lemma* infi_eq_of_tendsto



## [2020-10-11 12:30:22](https://github.com/leanprover-community/mathlib/commit/99130d8)
chore(algebra/monoid_algebra): Reorder lemmas, name some sections for clarity ([#4535](https://github.com/leanprover-community/mathlib/pull/4535))
This also reduces the scope of `local attribute [reducible] add_monoid_algebra` to the sections which actually need it.
#### Estimated changes
modified src/algebra/monoid_algebra.lean
- \+/\- *lemma* one_def
- \+/\- *lemma* mul_apply
- \+/\- *lemma* support_mul
- \+/\- *lemma* one_def
- \+/\- *lemma* mul_apply
- \+/\- *lemma* support_mul



## [2020-10-11 10:42:23](https://github.com/leanprover-community/mathlib/commit/0487a1d)
chore(algebra/algebra/basic): fix definition of `ring_hom.to_algebra` ([#4561](https://github.com/leanprover-community/mathlib/pull/4561))
The new definition uses `to_ring_hom := i` instead of `.. i` to get
defeq `algebra_map R S = i`, and adds it as a lemma.
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* ring_hom.algebra_map_to_algebra



## [2020-10-11 04:06:05](https://github.com/leanprover-community/mathlib/commit/2c53e5e)
chore(order/well_founded): move to a file ([#4568](https://github.com/leanprover-community/mathlib/pull/4568))
I want to use `order/rel_classes` before `data/set/basic`.
#### Estimated changes
modified archive/imo/imo1988_q6.lean

modified src/data/fintype/basic.lean

modified src/order/lattice.lean
- \+ *lemma* lt_sup_iff

modified src/order/pilex.lean

modified src/order/rel_classes.lean
- \- *lemma* eq_iff_not_lt_of_le
- \- *theorem* has_min
- \- *theorem* min_mem
- \- *theorem* not_lt_min
- \- *theorem* well_founded_iff_has_min
- \- *theorem* well_founded_iff_has_max'
- \- *theorem* well_founded_iff_has_min'

created src/order/well_founded.lean
- \+ *lemma* eq_iff_not_lt_of_le
- \+ *theorem* has_min
- \+ *theorem* min_mem
- \+ *theorem* not_lt_min
- \+ *theorem* well_founded_iff_has_min
- \+ *theorem* well_founded_iff_has_max'
- \+ *theorem* well_founded_iff_has_min'



## [2020-10-11 03:06:27](https://github.com/leanprover-community/mathlib/commit/4dbebe3)
chore(scripts): update nolints.txt ([#4564](https://github.com/leanprover-community/mathlib/pull/4564))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt



## [2020-10-11 01:02:23](https://github.com/leanprover-community/mathlib/commit/d8d6e18)
feat(data/finset/basic): equivalence of finsets from equivalence of types ([#4560](https://github.com/leanprover-community/mathlib/pull/4560))
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
Given an equivalence `α` to `β`, produce an equivalence between `finset α` and `finset β`, and simp lemmas about it.
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* finset_congr_apply
- \+ *lemma* finset_congr_symm_apply



## [2020-10-10 23:06:12](https://github.com/leanprover-community/mathlib/commit/df5adc5)
chore(topology/*): golf some proofs ([#4528](https://github.com/leanprover-community/mathlib/pull/4528))
* move `exists_nhds_split` to `topology/algebra/monoid`, rename to `exists_nhds_one_split`;
* add a version `exists_open_nhds_one_split`;
* move `exists_nhds_split4` to `topology/algebra/monoid`, rename to `exists_nhds_one_split4`;
* move `one_open_separated_mul` to `topology/algebra/monoid`, rename to `exists_open_nhds_one_mul_subset`;
* add `mem_prod_nhds_iff`;
* golf some proofs.
#### Estimated changes
modified src/topology/algebra/group.lean
- \- *lemma* exists_nhds_split
- \- *lemma* exists_nhds_split4
- \- *lemma* one_open_separated_mul

modified src/topology/algebra/monoid.lean
- \+ *lemma* exists_open_nhds_one_split
- \+ *lemma* exists_nhds_one_split
- \+ *lemma* exists_nhds_one_split4
- \+ *lemma* exists_open_nhds_one_mul_subset

modified src/topology/algebra/uniform_group.lean

modified src/topology/constructions.lean
- \+ *lemma* mem_nhds_prod_iff
- \+ *lemma* filter.has_basis.prod_nhds
- \+/\- *lemma* exists_nhds_square
- \+/\- *lemma* exists_nhds_square



## [2020-10-10 20:25:23](https://github.com/leanprover-community/mathlib/commit/c726898)
feat(data/equiv/basic): equivalence on functions from bool ([#4559](https://github.com/leanprover-community/mathlib/pull/4559))
An equivalence of functions from bool and pairs, together with some simp lemmas about it.
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *lemma* bool_to_equiv_prod_apply
- \+ *lemma* bool_to_equiv_prod_symm_apply_ff
- \+ *lemma* bool_to_equiv_prod_symm_apply_tt
- \+ *def* bool_to_equiv_prod



## [2020-10-10 18:28:05](https://github.com/leanprover-community/mathlib/commit/f91e0c6)
feat(data/finset/pi): pi singleton lemmas ([#4558](https://github.com/leanprover-community/mathlib/pull/4558))
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259). 
Two lemmas to reduce `finset.pi` on singletons.
#### Estimated changes
modified src/data/finset/pi.lean
- \+ *lemma* pi_singletons
- \+ *lemma* pi_const_singleton



## [2020-10-10 15:18:44](https://github.com/leanprover-community/mathlib/commit/c8738cb)
feat(topology/uniform_space/cauchy): generalize `second_countable_of_separable` to uniform spaces ([#4530](https://github.com/leanprover-community/mathlib/pull/4530))
Also generalize `is_countably_generated.has_antimono_basis` to `is_countably_generated.exists_antimono_subbasis` and add a few lemmas about bases of the uniformity filter.
#### Estimated changes
modified src/order/filter/at_top_bot.lean

modified src/order/filter/bases.lean
- \+ *lemma* has_basis.property_index
- \+ *lemma* has_basis.set_index_mem
- \+ *lemma* has_basis.set_index_subset
- \+ *lemma* exists_antimono_subbasis
- \+ *lemma* exists_antimono_basis
- \+/\- *lemma* is_countably_generated_iff_exists_antimono_basis
- \+/\- *lemma* inf
- \+/\- *lemma* inf_principal
- \- *lemma* exists_antimono_seq
- \- *lemma* has_antimono_basis
- \+/\- *lemma* is_countably_generated_iff_exists_antimono_basis
- \+/\- *lemma* inf
- \+/\- *lemma* inf_principal

modified src/topology/bases.lean
- \+ *lemma* exists_countable_dense

modified src/topology/basic.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/sequences.lean

modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniform_space.mem_ball_self
- \+ *lemma* uniform_space.is_open_ball
- \+/\- *lemma* nhds_eq_uniformity
- \+ *lemma* uniformity_has_basis_open
- \+ *lemma* uniformity_has_basis_open_symmetric
- \+/\- *lemma* nhds_eq_uniformity

modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* second_countable_of_separable

modified src/topology/uniform_space/completion.lean



## [2020-10-10 09:40:05](https://github.com/leanprover-community/mathlib/commit/6676917)
feat(analysis/special_functions/*): a few more simp lemmas ([#4550](https://github.com/leanprover-community/mathlib/pull/4550))
Add more lemmas for simplifying inequalities with `exp`, `log`, and
`rpow`. Lemmas that generate more than one inequality are not marked
as `simp`.
#### Estimated changes
modified src/algebra/ordered_ring.lean

modified src/analysis/special_functions/exp_log.lean
- \+ *lemma* log_nonneg_iff
- \+/\- *lemma* log_nonneg
- \+ *lemma* log_nonpos_iff
- \+ *lemma* log_nonpos_iff'
- \+/\- *lemma* log_nonpos
- \+/\- *lemma* log_nonneg
- \+/\- *lemma* log_nonpos

modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* one_lt_rpow_of_pos_of_lt_one_of_neg
- \+/\- *lemma* one_le_rpow_of_pos_of_le_one_of_nonpos
- \+ *lemma* rpow_lt_one_iff_of_pos
- \+ *lemma* rpow_lt_one_iff
- \+ *lemma* one_lt_rpow_iff_of_pos
- \+ *lemma* one_lt_rpow_iff
- \+ *lemma* rpow_le_one_iff_of_pos
- \+/\- *lemma* one_lt_rpow_of_pos_of_lt_one_of_neg
- \+/\- *lemma* one_le_rpow_of_pos_of_le_one_of_nonpos

modified src/data/complex/exponential.lean
- \+/\- *lemma* one_lt_exp_iff
- \+/\- *lemma* exp_lt_one_iff
- \+ *lemma* exp_le_one_iff
- \+ *lemma* one_le_exp_iff
- \+/\- *lemma* one_lt_exp_iff
- \+/\- *lemma* exp_lt_one_iff



## [2020-10-10 01:04:50](https://github.com/leanprover-community/mathlib/commit/b084a06)
chore(scripts): update nolints.txt ([#4556](https://github.com/leanprover-community/mathlib/pull/4556))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt

modified scripts/nolints.txt



## [2020-10-09 19:22:53](https://github.com/leanprover-community/mathlib/commit/40b55c0)
feat(measure_theory): additions ([#4324](https://github.com/leanprover-community/mathlib/pull/4324))
Many additional lemmas. 
Notable addition: sequential limits of measurable functions into a metric space are measurable.
Rename `integral_map_measure` -> `integral_map` (to be consistent with the version for `lintegral`)
Fix the precedence of all notations for integrals. From now on `∫ x, abs ∥f x∥ ∂μ` will be parsed
correctly (previously it gave a parse error).
Some cleanup (moving lemmas, and some nicer presentation by opening locales and namespaces).
#### Estimated changes
modified src/data/indicator_function.lean
- \+ *lemma* indicator_comp_right
- \+ *lemma* indicator_prod_one

modified src/data/set/finite.lean
- \+ *lemma* Union_Inter_of_monotone

modified src/data/set/lattice.lean
- \+ *lemma* Union_inter_subset
- \+ *lemma* Union_inter_of_monotone
- \+ *lemma* Union_Inter_subset

modified src/logic/basic.lean
- \+ *lemma* ite_and

modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integral_eq_sum_of_subset
- \+ *lemma* integral_zero'
- \+ *lemma* integral_add'
- \+ *lemma* integral_neg'
- \+ *lemma* integral_sub'
- \+ *lemma* ennnorm_integral_le_lintegral_ennnorm
- \+ *lemma* lintegral_coe_eq_integral
- \+ *lemma* integral_to_real
- \+ *lemma* integral_map
- \- *lemma* integral_map_measure

modified src/measure_theory/borel_space.lean
- \+ *lemma* measurable_liminf'
- \+ *lemma* measurable_limsup'
- \+ *lemma* measurable_liminf
- \+ *lemma* measurable_limsup
- \+ *lemma* measurable_inf_nndist
- \+ *lemma* measurable.inf_nndist
- \+/\- *lemma* measurable_dist
- \+/\- *lemma* measurable_nndist
- \+/\- *lemma* measurable_edist
- \+/\- *lemma* measurable.sub_nnreal
- \+/\- *lemma* nnreal.measurable_coe
- \+/\- *lemma* measurable.nnreal_coe
- \+/\- *lemma* measurable.ennreal_coe
- \+/\- *lemma* measurable_coe
- \+/\- *lemma* measurable_ennreal_coe_iff
- \+/\- *lemma* measurable.norm
- \+/\- *lemma* measurable_nnnorm
- \+/\- *lemma* measurable.nnnorm
- \+ *lemma* measurable_of_tendsto_nnreal'
- \+ *lemma* measurable_of_tendsto_nnreal
- \+ *lemma* measurable_of_tendsto_metric'
- \+ *lemma* measurable_of_tendsto_metric
- \+/\- *lemma* measurable_dist
- \+/\- *lemma* measurable_nndist
- \+/\- *lemma* measurable_edist
- \+/\- *lemma* measurable.sub_nnreal
- \+/\- *lemma* nnreal.measurable_coe
- \+/\- *lemma* measurable.nnreal_coe
- \+/\- *lemma* measurable.ennreal_coe
- \+/\- *lemma* measurable_coe
- \+/\- *lemma* measurable_ennreal_coe_iff
- \+/\- *lemma* measurable.norm
- \+/\- *lemma* measurable_nnnorm
- \+/\- *lemma* measurable.nnnorm
- \+/\- *def* measurable_equiv.ennreal_equiv_nnreal
- \+/\- *def* measurable_equiv.ennreal_equiv_nnreal

modified src/measure_theory/integration.lean
- \+ *lemma* lintegral_mul_const
- \+ *lemma* lintegral_mul_const_le
- \+ *lemma* lintegral_mul_const'
- \+ *lemma* lintegral_comp
- \+ *lemma* ae_lt_top

modified src/measure_theory/l1_space.lean
- \+ *lemma* integrable_smul_const
- \+ *lemma* norm_eq_lintegral
- \+ *lemma* norm_sub_eq_lintegral
- \+ *lemma* of_real_norm_eq_lintegral
- \+ *lemma* of_real_norm_sub_eq_lintegral

modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_Union_null_iff
- \+ *lemma* measure_union_null_iff
- \+ *lemma* measure_if
- \+/\- *lemma* measure_univ_eq_zero
- \+ *lemma* sum_cond
- \+/\- *lemma* dirac_ae_eq
- \+/\- *lemma* measure_univ_eq_zero
- \+/\- *lemma* dirac_ae_eq
- \+/\- *theorem* le_iff
- \+/\- *theorem* to_outer_measure_le
- \+/\- *theorem* le_iff'
- \+/\- *theorem* lt_iff
- \+/\- *theorem* lt_iff'
- \+/\- *theorem* le_iff
- \+/\- *theorem* to_outer_measure_le
- \+/\- *theorem* le_iff'
- \+/\- *theorem* lt_iff
- \+/\- *theorem* lt_iff'

modified src/measure_theory/set_integral.lean
- \+ *lemma* integral_smul_const

modified src/measure_theory/simple_func_dense.lean
- \+ *lemma* norm_approx_on_zero_le
- \+/\- *lemma* tendsto_approx_on_l1_edist
- \+/\- *lemma* integrable_approx_on
- \+/\- *lemma* tendsto_approx_on_univ_l1_edist
- \+/\- *lemma* integrable_approx_on_univ
- \+/\- *lemma* tendsto_approx_on_univ_l1
- \+/\- *lemma* tendsto_approx_on_l1_edist
- \+/\- *lemma* integrable_approx_on
- \+/\- *lemma* tendsto_approx_on_univ_l1_edist
- \+/\- *lemma* integrable_approx_on_univ
- \+/\- *lemma* tendsto_approx_on_univ_l1



## [2020-10-09 18:15:49](https://github.com/leanprover-community/mathlib/commit/d533e1c)
feat(ring_theory/power_series): inverse lemmas ([#4552](https://github.com/leanprover-community/mathlib/pull/4552))
Broken off from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
#### Estimated changes
modified src/ring_theory/power_series.lean
- \+ *lemma* eq_mul_inv_iff_mul_eq
- \+ *lemma* eq_inv_iff_mul_eq_one
- \+ *lemma* inv_eq_iff_mul_eq_one



## [2020-10-09 15:44:20](https://github.com/leanprover-community/mathlib/commit/b167809)
feat(topology/basic): Lim_spec etc. cleanup ([#4545](https://github.com/leanprover-community/mathlib/pull/4545))
Fixes [#4543](https://github.com/leanprover-community/mathlib/pull/4543)
See [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/More.20point.20set.20topology.20questions/near/212757136)
#### Estimated changes
modified src/order/filter/ultrafilter.lean

modified src/topology/basic.lean
- \+ *lemma* le_nhds_Lim
- \+ *lemma* tendsto_nhds_lim
- \- *lemma* Lim_spec
- \- *lemma* lim_spec

modified src/topology/extend_from_subset.lean

modified src/topology/separation.lean
- \+ *lemma* Lim_eq_iff
- \+ *lemma* is_ultrafilter.Lim_eq_iff_le_nhds
- \+/\- *lemma* filter.tendsto.lim_eq
- \+ *lemma* filter.lim_eq_iff
- \+/\- *lemma* filter.tendsto.lim_eq

modified src/topology/subset_properties.lean
- \+ *lemma* is_ultrafilter.le_nhds_Lim

modified src/topology/uniform_space/cauchy.lean

modified src/topology/uniform_space/uniform_embedding.lean



## [2020-10-09 13:16:06](https://github.com/leanprover-community/mathlib/commit/fcaf6e9)
feat(meta/expr): add parser for generated binder names ([#4540](https://github.com/leanprover-community/mathlib/pull/4540))
During elaboration, Lean generates a name for anonymous Π binders. This commit
adds a parser that recognises such names.
#### Estimated changes
modified src/data/string/defs.lean
- \+ *def* is_nat

modified src/data/sum.lean

modified src/meta/expr.lean



## [2020-10-09 13:16:04](https://github.com/leanprover-community/mathlib/commit/306dc8a)
chore(algebra/big_operators/basic): add lemma prod_multiset_count' that generalize prod_multiset_count to consider a function to a monoid ([#4534](https://github.com/leanprover-community/mathlib/pull/4534))
I have added `prod_multiset_count'` that is very similar to `prod_multiset_count` but takes into account a function `f : \a \r M` where `M` is a commutative monoid. The proof is essentially the same (I didn't try to prove it using `prod_multiset_count` because maybe we can remove it and just keep the more general version).
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_multiset_map_count
- \+/\- *lemma* prod_multiset_count
- \+/\- *lemma* prod_multiset_count



## [2020-10-09 11:06:01](https://github.com/leanprover-community/mathlib/commit/656ef0a)
chore(topology/instances/nnreal): use notation ([#4548](https://github.com/leanprover-community/mathlib/pull/4548))
#### Estimated changes
modified src/topology/instances/nnreal.lean
- \+/\- *lemma* continuous_coe
- \+/\- *lemma* tendsto_coe
- \+/\- *lemma* tendsto.sub
- \+/\- *lemma* continuous_sub
- \+/\- *lemma* continuous.sub
- \+/\- *lemma* has_sum_coe
- \+/\- *lemma* coe_tsum
- \+/\- *lemma* summable_comp_injective
- \+/\- *lemma* summable_nat_add
- \+/\- *lemma* sum_add_tsum_nat_add
- \+/\- *lemma* continuous_coe
- \+/\- *lemma* tendsto_coe
- \+/\- *lemma* tendsto.sub
- \+/\- *lemma* continuous_sub
- \+/\- *lemma* continuous.sub
- \+/\- *lemma* has_sum_coe
- \+/\- *lemma* coe_tsum
- \+/\- *lemma* summable_comp_injective
- \+/\- *lemma* summable_nat_add
- \+/\- *lemma* sum_add_tsum_nat_add



## [2020-10-09 11:05:59](https://github.com/leanprover-community/mathlib/commit/d0f45f5)
lint(various): nolint has_inhabited_instance for injective functions ([#4541](https://github.com/leanprover-community/mathlib/pull/4541))
`function.embedding`, `homeomorph`, `isometric` represent injective/bijective functions, so it's silly to expect them to be inhabited.
#### Estimated changes
modified src/logic/embedding.lean

modified src/topology/homeomorph.lean

modified src/topology/metric_space/isometry.lean



## [2020-10-09 08:54:38](https://github.com/leanprover-community/mathlib/commit/cc75e4e)
chore(data/nat/cast): a few `simp`/`norm_cast` lemmas ([#4549](https://github.com/leanprover-community/mathlib/pull/4549))
#### Estimated changes
modified src/data/nat/cast.lean
- \+/\- *lemma* coe_nat_dvd
- \+/\- *lemma* coe_nat_dvd
- \+ *theorem* strict_mono_cast
- \+/\- *theorem* cast_le
- \+ *theorem* one_lt_cast
- \+ *theorem* one_le_cast
- \+ *theorem* cast_lt_one
- \+ *theorem* cast_le_one
- \+/\- *theorem* cast_le



## [2020-10-09 01:44:31](https://github.com/leanprover-community/mathlib/commit/f6836c1)
chore(scripts): update nolints.txt ([#4547](https://github.com/leanprover-community/mathlib/pull/4547))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/copy-mod-doc-exceptions.txt

modified scripts/nolints.txt



## [2020-10-08 23:44:06](https://github.com/leanprover-community/mathlib/commit/8004fb6)
chore(topology/algebra/group): move a lemma to `group_theory/coset` ([#4522](https://github.com/leanprover-community/mathlib/pull/4522))
`quotient_group_saturate` didn't use any topology. Move it to
`group_theory/coset` and rename to
`quotient_group.preimage_image_coe`.
Also rename `quotient_group.open_coe` to `quotient_group.is_open_map_coe`
#### Estimated changes
modified src/group_theory/coset.lean
- \+ *lemma* preimage_image_coe

modified src/group_theory/quotient_group.lean
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_inv
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_gpow
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_inv
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_gpow

modified src/topology/algebra/group.lean
- \+ *lemma* quotient_group.is_open_map_coe
- \- *lemma* quotient_group_saturate
- \- *lemma* quotient_group.open_coe



## [2020-10-08 22:15:42](https://github.com/leanprover-community/mathlib/commit/ce999a8)
feat(topology/basic): add `is_open_iff_ultrafilter` ([#4529](https://github.com/leanprover-community/mathlib/pull/4529))
Requested on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F)
by Adam Topaz
#### Estimated changes
modified src/order/filter/ultrafilter.lean
- \+ *lemma* le_iff_ultrafilter
- \+ *lemma* mem_iff_ultrafilter

modified src/topology/basic.lean
- \+ *theorem* is_open_iff_ultrafilter



## [2020-10-08 18:04:05](https://github.com/leanprover-community/mathlib/commit/a912455)
fix(bors.toml, build.yml): check for new linter, rename linter to "Lint style" ([#4539](https://github.com/leanprover-community/mathlib/pull/4539))
#### Estimated changes
modified .github/workflows/build.yml

modified bors.toml



## [2020-10-08 15:41:18](https://github.com/leanprover-community/mathlib/commit/73f119e)
refactor(category_theory/pairwise): change direction of morphisms in the category of pairwise intersections ([#4537](https://github.com/leanprover-community/mathlib/pull/4537))
Even though this makes some proofs slightly more awkward, this is the more natural definition.
In a subsequent PR about another equivalent sheaf condition, it also makes proofs less awkward, too!
#### Estimated changes
modified src/category_theory/category/pairwise.lean
- \+/\- *def* diagram_obj
- \+/\- *def* diagram
- \+ *def* cocone_ι_app
- \+ *def* cocone
- \+ *def* cocone_is_colimit
- \+/\- *def* diagram_obj
- \+/\- *def* diagram
- \- *def* cone_π_app
- \- *def* cone
- \- *def* cone_is_limit

modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean



## [2020-10-08 15:41:16](https://github.com/leanprover-community/mathlib/commit/0ae4a3d)
fix(update-copy-mod-doc-exceptions.sh): cleanup, sort properly ([#4533](https://github.com/leanprover-community/mathlib/pull/4533))
Followup to [#4513](https://github.com/leanprover-community/mathlib/pull/4513).
#### Estimated changes
modified scripts/update-copy-mod-doc-exceptions.sh



## [2020-10-08 15:41:14](https://github.com/leanprover-community/mathlib/commit/427564e)
chore(algebra/monoid_algebra): Fix TODO about unwanted unfolding ([#4532](https://github.com/leanprover-community/mathlib/pull/4532))
For whatever reason, supplying `zero` and `add` explicitly makes the proofs work inline.
This TODO was added by @johoelzl in f09abb1c47a846c33c0e996ffa9bf12951b40b15.
#### Estimated changes
modified src/algebra/monoid_algebra.lean



## [2020-10-08 15:41:12](https://github.com/leanprover-community/mathlib/commit/0c18d96)
chore(data/padics/*): linting + squeeze_simp speedup ([#4531](https://github.com/leanprover-community/mathlib/pull/4531))
#### Estimated changes
modified src/data/padics/padic_norm.lean

modified src/data/padics/padic_numbers.lean
- \+/\- *def* padic_seq
- \+/\- *def* padic_seq



## [2020-10-08 15:41:08](https://github.com/leanprover-community/mathlib/commit/60be8ed)
feat(data/equiv/*): to_monoid_hom_injective and to_ring_hom_injective ([#4525](https://github.com/leanprover-community/mathlib/pull/4525))
#### Estimated changes
modified src/data/equiv/mul_add.lean
- \+ *lemma* to_monoid_hom_injective

modified src/data/equiv/ring.lean
- \+ *lemma* to_ring_hom_injective



## [2020-10-08 15:41:06](https://github.com/leanprover-community/mathlib/commit/253f225)
lint(computability/halting): docstrings ([#4524](https://github.com/leanprover-community/mathlib/pull/4524))
Adds docstrings in `computability/halting.lean`
#### Estimated changes
modified src/computability/halting.lean



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
modified src/algebra/category/Module/limits.lean

modified src/algebra/module/basic.lean
- \+ *theorem* coe_injective
- \+/\- *theorem* to_add_monoid_hom_injective
- \- *theorem* coe_inj
- \+/\- *theorem* to_add_monoid_hom_injective

modified src/analysis/calculus/times_cont_diff.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/data/equiv/basic.lean

modified src/geometry/euclidean/basic.lean

modified src/linear_algebra/basic.lean
- \+ *lemma* default_def

modified src/logic/unique.lean
- \+ *lemma* pi.default_def
- \+ *lemma* pi.default_apply
- \- *lemma* injective.comap_subsingleton
- \- *lemma* nonempty_unique_or_exists_ne
- \- *lemma* subsingleton_or_exists_ne
- \+ *def* mk'
- \- *def* surjective.unique

modified src/ring_theory/derivation.lean

modified src/topology/algebra/module.lean
- \+ *lemma* default_def
- \+ *theorem* coe_fn_injective
- \- *theorem* coe_inj



## [2020-10-08 15:41:02](https://github.com/leanprover-community/mathlib/commit/7b42c71)
feat(archive/imo): revive @kbuzzard's imo2019_q1 ([#4377](https://github.com/leanprover-community/mathlib/pull/4377))
#### Estimated changes
created archive/imo/imo2019_q1.lean
- \+ *theorem* imo2019Q1



## [2020-10-08 15:40:59](https://github.com/leanprover-community/mathlib/commit/9b0d30c)
feat(number_theory/arithmetic_function): define `is_multiplicative` on `arithmetic_function`s, provides examples ([#4312](https://github.com/leanprover-community/mathlib/pull/4312))
Provides a few basic examples of important arithmetic functions
Defines what it means for an arithmetic function to be multiplicative
#### Estimated changes
modified src/data/nat/gcd.lean
- \+ *lemma* gcd_mul_gcd_of_coprime_of_mul_eq_mul

modified src/number_theory/arithmetic_function.lean
- \+/\- *lemma* to_fun_eq
- \+/\- *lemma* map_zero
- \+/\- *lemma* zero_apply
- \+/\- *lemma* one_one
- \+/\- *lemma* one_apply_ne
- \+/\- *lemma* nat_coe_apply
- \+/\- *lemma* int_coe_apply
- \+/\- *lemma* coe_coe
- \+/\- *lemma* add_apply
- \+/\- *lemma* mul_apply
- \+ *lemma* zeta_apply
- \+ *lemma* zeta_apply_ne
- \+ *lemma* pmul_apply
- \+ *lemma* pmul_comm
- \+ *lemma* pmul_zeta
- \+ *lemma* zeta_pmul
- \+ *lemma* ppow_zero
- \+ *lemma* ppow_apply
- \+ *lemma* ppow_succ
- \+ *lemma* ppow_succ'
- \+ *lemma* map_one
- \+ *lemma* map_mul_of_coprime
- \+ *lemma* nat_cast
- \+ *lemma* int_cast
- \+ *lemma* mul
- \+ *lemma* pmul
- \+ *lemma* id_apply
- \+ *lemma* pow_apply
- \+ *lemma* sigma_apply
- \+ *lemma* zeta_mul_pow_eq_sigma
- \+ *lemma* is_multiplicative_zeta
- \+ *lemma* is_multiplicative_id
- \+ *lemma* is_multiplicative.ppow
- \+ *lemma* is_multiplicative_pow
- \+ *lemma* is_multiplicative_sigma
- \+/\- *lemma* to_fun_eq
- \+/\- *lemma* map_zero
- \+/\- *lemma* zero_apply
- \+/\- *lemma* one_one
- \+/\- *lemma* one_apply_ne
- \+/\- *lemma* nat_coe_apply
- \+/\- *lemma* int_coe_apply
- \+/\- *lemma* coe_coe
- \+/\- *lemma* add_apply
- \+/\- *lemma* mul_apply
- \+/\- *theorem* coe_inj
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+ *theorem* zeta_mul_apply
- \+ *theorem* mul_zeta_apply
- \+/\- *theorem* coe_inj
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+ *def* zeta
- \+ *def* pmul
- \+ *def* ppow
- \+ *def* is_multiplicative
- \+ *def* id
- \+ *def* pow
- \+ *def* sigma

modified src/number_theory/divisors.lean
- \+ *lemma* divisors_eq_proper_divisors_insert_self_of_pos
- \+/\- *lemma* divisors_zero
- \- *lemma* divisors_eq_proper_divisors_insert_self
- \+/\- *lemma* divisors_zero
- \+/\- *def* divisors
- \+/\- *def* proper_divisors
- \+/\- *def* divisors
- \+/\- *def* proper_divisors



## [2020-10-08 13:27:56](https://github.com/leanprover-community/mathlib/commit/5a01549)
lint(multiset/pi): remove unused instance ([#4526](https://github.com/leanprover-community/mathlib/pull/4526))
Removes an unused instance from `multiset/pi`
#### Estimated changes
modified src/data/finset/pi.lean
- \+/\- *def* pi.empty
- \+/\- *def* pi.empty

modified src/data/multiset/pi.lean
- \+/\- *lemma* pi.cons_ne
- \+/\- *lemma* pi.cons_ne
- \+/\- *def* pi.empty
- \+/\- *def* pi.empty



## [2020-10-08 13:27:54](https://github.com/leanprover-community/mathlib/commit/48a3604)
feat(logic/nontrivial): a tactic to summon nontrivial instances ([#4374](https://github.com/leanprover-community/mathlib/pull/4374))
```
Given a goal `a = b` or `a ≤ b` in a type `α`, generates an additional hypothesis `nontrivial α`
(as otherwise `α` is a subsingleton and the goal is trivial).
Alternatively, given a hypothesis `a ≠ b` or `a < b` in a type `α`, tries to generate a `nontrivial α`
hypothesis from existing hypotheses using `nontrivial_of_ne` and `nontrivial_of_lt`.
```
#### Estimated changes
modified src/linear_algebra/char_poly/coeff.lean
- \+/\- *lemma* char_poly_monic
- \- *lemma* char_poly_monic_of_nontrivial
- \+/\- *lemma* char_poly_monic

modified src/logic/nontrivial.lean
- \+ *lemma* nontrivial_of_lt
- \+/\- *lemma* subsingleton_or_nontrivial
- \+/\- *lemma* subsingleton_or_nontrivial

created test/nontriviality.lean



## [2020-10-08 10:23:23](https://github.com/leanprover-community/mathlib/commit/43f52dd)
chore(algebra/char_zero): rename vars, add `with_top` instance ([#4523](https://github.com/leanprover-community/mathlib/pull/4523))
Motivated by [#3135](https://github.com/leanprover-community/mathlib/pull/3135).
* Use `R` as a `Type*` variable;
* Add `add_monoid_hom.map_nat_cast` and `with_top.coe_add_hom`;
* Drop versions of `char_zero_of_inj_zero`, use `[add_left_cancel_monoid R]` instead.
#### Estimated changes
modified src/algebra/char_p.lean

modified src/algebra/char_zero.lean
- \+/\- *lemma* cast_add_one_ne_zero
- \+/\- *lemma* two_ne_zero'
- \+/\- *lemma* add_self_eq_zero
- \+/\- *lemma* bit0_eq_zero
- \+/\- *lemma* half_add_self
- \+/\- *lemma* add_halves'
- \+/\- *lemma* sub_half
- \+/\- *lemma* half_sub
- \+/\- *lemma* cast_add_one_ne_zero
- \+/\- *lemma* two_ne_zero'
- \+/\- *lemma* add_self_eq_zero
- \+/\- *lemma* bit0_eq_zero
- \+/\- *lemma* half_add_self
- \+/\- *lemma* add_halves'
- \+/\- *lemma* sub_half
- \+/\- *lemma* half_sub
- \+/\- *theorem* char_zero_of_inj_zero
- \+/\- *theorem* cast_injective
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_eq_zero
- \+/\- *theorem* cast_ne_zero
- \+/\- *theorem* cast_dvd_char_zero
- \+/\- *theorem* char_zero_of_inj_zero
- \- *theorem* add_group.char_zero_of_inj_zero
- \- *theorem* ordered_cancel_comm_monoid.char_zero_of_inj_zero
- \+/\- *theorem* cast_injective
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_eq_zero
- \+/\- *theorem* cast_ne_zero
- \+/\- *theorem* cast_dvd_char_zero

modified src/algebra/ordered_group.lean
- \+ *lemma* coe_coe_add_hom
- \+ *def* coe_add_hom

modified src/data/complex/basic.lean

modified src/data/complex/is_R_or_C.lean

modified src/data/nat/cast.lean
- \+/\- *lemma* eq_nat_cast
- \+ *lemma* map_nat_cast
- \+/\- *lemma* eq_nat_cast



## [2020-10-08 05:32:06](https://github.com/leanprover-community/mathlib/commit/34a4471)
chore(data/quot): `quot.mk` etc are surjective ([#4517](https://github.com/leanprover-community/mathlib/pull/4517))
#### Estimated changes
modified src/data/quot.lean
- \+ *lemma* surjective_quot_mk
- \+ *lemma* surjective_quotient_mk
- \+ *lemma* surjective_quotient_mk'
- \+/\- *theorem* quotient.lift_on_beta₂
- \+/\- *theorem* quotient.lift_on_beta₂



## [2020-10-08 05:32:04](https://github.com/leanprover-community/mathlib/commit/4f75760)
chore(*/hom,equiv): Split `monoid_hom` into more fundamental structures, and reuse them elsewhere ([#4423](https://github.com/leanprover-community/mathlib/pull/4423))
Notably this adds `add_hom` and `mul_hom`, which become base classes of `add_equiv`, `mul_equiv`, `linear_map`, and `linear_equiv`.
Primarily to avoid breaking assumptions of field order in `monoid_hom` and `add_monoid_hom`, this also adds `one_hom` and `zero_hom`.
A massive number of lemmas here are totally uninteresting and hold for pretty much all objects that define `coe_to_fun`.
This PR translates all those lemmas, but doesn't bother attempting to generalize later ones.
#### Estimated changes
modified src/algebra/group/hom.lean
- \+ *lemma* one_hom.to_fun_eq_coe
- \+ *lemma* mul_hom.to_fun_eq_coe
- \+ *lemma* monoid_hom.to_fun_eq_coe
- \+ *lemma* one_hom.coe_mk
- \+ *lemma* mul_hom.coe_mk
- \+ *lemma* monoid_hom.coe_mk
- \+ *lemma* one_hom.coe_inj
- \+ *lemma* mul_hom.coe_inj
- \+ *lemma* monoid_hom.coe_inj
- \+ *lemma* one_hom.ext
- \+ *lemma* mul_hom.ext
- \+ *lemma* monoid_hom.ext
- \+ *lemma* one_hom.ext_iff
- \+ *lemma* mul_hom.ext_iff
- \+ *lemma* monoid_hom.ext_iff
- \+ *lemma* one_hom.map_one
- \+ *lemma* monoid_hom.map_one
- \+ *lemma* mul_hom.map_mul
- \+ *lemma* monoid_hom.map_mul
- \+ *lemma* one_hom.id_apply
- \+ *lemma* mul_hom.id_apply
- \+ *lemma* monoid_hom.id_apply
- \+ *lemma* one_hom.comp_apply
- \+ *lemma* mul_hom.comp_apply
- \+ *lemma* monoid_hom.comp_apply
- \+ *lemma* one_hom.comp_assoc
- \+ *lemma* mul_hom.comp_assoc
- \+ *lemma* monoid_hom.comp_assoc
- \+ *lemma* one_hom.cancel_right
- \+ *lemma* mul_hom.cancel_right
- \+ *lemma* monoid_hom.cancel_right
- \+ *lemma* one_hom.cancel_left
- \+ *lemma* mul_hom.cancel_left
- \+ *lemma* monoid_hom.cancel_left
- \+ *lemma* one_hom.comp_id
- \+ *lemma* mul_hom.comp_id
- \+ *lemma* monoid_hom.comp_id
- \+ *lemma* one_hom.id_comp
- \+ *lemma* mul_hom.id_comp
- \+ *lemma* monoid_hom.id_comp
- \+ *lemma* one_hom.one_apply
- \+ *lemma* monoid_hom.one_apply
- \- *lemma* to_fun_eq_coe
- \- *lemma* coe_mk
- \- *lemma* coe_inj
- \- *lemma* ext
- \- *lemma* ext_iff
- \- *lemma* map_one
- \- *lemma* map_mul
- \- *lemma* id_apply
- \- *lemma* comp_apply
- \- *lemma* comp_assoc
- \- *lemma* cancel_right
- \- *lemma* cancel_left
- \- *lemma* comp_id
- \- *lemma* id_comp
- \- *lemma* one_apply
- \+ *theorem* one_hom.congr_fun
- \+ *theorem* mul_hom.congr_fun
- \+ *theorem* monoid_hom.congr_fun
- \+ *theorem* one_hom.congr_arg
- \+ *theorem* mul_hom.congr_arg
- \+ *theorem* monoid_hom.congr_arg
- \- *theorem* congr_fun
- \- *theorem* congr_arg
- \+ *def* one_hom.id
- \+ *def* mul_hom.id
- \+ *def* monoid_hom.id
- \+ *def* one_hom.comp
- \+ *def* mul_hom.comp
- \+ *def* monoid_hom.comp
- \- *def* id
- \- *def* comp

modified src/algebra/module/basic.lean

modified src/data/equiv/mul_add.lean

modified src/linear_algebra/basic.lean
- \+ *def* to_equiv
- \- *def* to_add_equiv



## [2020-10-08 04:37:20](https://github.com/leanprover-community/mathlib/commit/b4dc912)
ci(*): run style lint in parallel job, fix update-copy-mod-doc-exceptions.sh ([#4513](https://github.com/leanprover-community/mathlib/pull/4513))
Followup to [#4486](https://github.com/leanprover-community/mathlib/pull/4486):
- run the linter in a separate parallel job, per request
- the update-*.sh script now correctly generates a full exceptions file
- add some more comments to the shell scripts
#### Estimated changes
modified .github/workflows/build.yml

modified scripts/copy-mod-doc-exceptions.txt

modified scripts/lint-copy-mod-doc.sh

modified scripts/update-copy-mod-doc-exceptions.sh



## [2020-10-08 04:37:18](https://github.com/leanprover-community/mathlib/commit/3d1d4fb)
feat(data/polynomial/degree/trailing_degree): fixed formatting and streamlined a couple of proofs ([#4509](https://github.com/leanprover-community/mathlib/pull/4509))
#### Estimated changes
modified src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* trailing_coeff_eq_zero
- \+ *lemma* trailing_coeff_nonzero_iff_nonzero
- \+ *lemma* nat_trailing_degree_mem_support_of_nonzero
- \+ *lemma* nat_trailing_degree_le_of_mem_supp
- \+ *lemma* nat_trailing_degree_eq_support_min'



## [2020-10-08 03:44:56](https://github.com/leanprover-community/mathlib/commit/7a71554)
doc(tactic/slim_check): improve advice in error message ([#4520](https://github.com/leanprover-community/mathlib/pull/4520))
The error message in `slim_check` suggests to look for `testable` and it now specifies which namespace to find `testable` in.
#### Estimated changes
modified src/tactic/slim_check.lean



## [2020-10-08 01:08:47](https://github.com/leanprover-community/mathlib/commit/e9d1dc4)
chore(scripts): update nolints.txt ([#4521](https://github.com/leanprover-community/mathlib/pull/4521))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-10-07 23:27:32](https://github.com/leanprover-community/mathlib/commit/a5b0376)
chore(topology/algebra/monoid,group): rename variables ([#4516](https://github.com/leanprover-community/mathlib/pull/4516))
Use `M`, `N` for monoids, `G`, `H` for groups.
#### Estimated changes
modified src/topology/algebra/group.lean
- \+/\- *lemma* continuous_inv
- \+/\- *lemma* continuous.inv
- \+/\- *lemma* continuous_on_inv
- \+/\- *lemma* continuous_on.inv
- \+/\- *lemma* tendsto_inv
- \+/\- *lemma* filter.tendsto.inv
- \+/\- *lemma* continuous_at.inv
- \+/\- *lemma* continuous_within_at.inv
- \+/\- *lemma* is_open_map_mul_left
- \+/\- *lemma* is_closed_map_mul_left
- \+/\- *lemma* is_open_map_mul_right
- \+/\- *lemma* is_closed_map_mul_right
- \+/\- *lemma* exists_nhds_split
- \+/\- *lemma* exists_nhds_split_inv
- \+/\- *lemma* exists_nhds_split4
- \+/\- *lemma* nhds_one_symm
- \+/\- *lemma* nhds_translation_mul_inv
- \+/\- *lemma* quotient_group_saturate
- \+/\- *lemma* quotient_group.open_coe
- \+/\- *lemma* continuous.sub
- \+/\- *lemma* continuous_sub
- \+/\- *lemma* continuous_on.sub
- \+/\- *lemma* filter.tendsto.sub
- \+/\- *lemma* nhds_translation
- \+/\- *lemma* neg_Z
- \+/\- *lemma* add_Z
- \+/\- *lemma* exists_Z_half
- \+/\- *lemma* nhds_eq
- \+/\- *lemma* nhds_zero_eq_Z
- \+/\- *lemma* is_open_mul_left
- \+/\- *lemma* is_open_mul_right
- \+/\- *lemma* topological_group.t1_space
- \+/\- *lemma* topological_group.regular_space
- \+/\- *lemma* topological_group.t2_space
- \+/\- *lemma* one_open_separated_mul
- \+/\- *lemma* compact_open_separated_mul
- \+/\- *lemma* compact_covered_by_mul_left_translates
- \+/\- *lemma* nhds_mul
- \+/\- *lemma* nhds_is_mul_hom
- \+/\- *lemma* continuous_inv
- \+/\- *lemma* continuous.inv
- \+/\- *lemma* continuous_on_inv
- \+/\- *lemma* continuous_on.inv
- \+/\- *lemma* tendsto_inv
- \+/\- *lemma* filter.tendsto.inv
- \+/\- *lemma* continuous_at.inv
- \+/\- *lemma* continuous_within_at.inv
- \+/\- *lemma* is_open_map_mul_left
- \+/\- *lemma* is_closed_map_mul_left
- \+/\- *lemma* is_open_map_mul_right
- \+/\- *lemma* is_closed_map_mul_right
- \+/\- *lemma* exists_nhds_split
- \+/\- *lemma* exists_nhds_split_inv
- \+/\- *lemma* exists_nhds_split4
- \+/\- *lemma* nhds_one_symm
- \+/\- *lemma* nhds_translation_mul_inv
- \+/\- *lemma* quotient_group_saturate
- \+/\- *lemma* quotient_group.open_coe
- \+/\- *lemma* continuous.sub
- \+/\- *lemma* continuous_sub
- \+/\- *lemma* continuous_on.sub
- \+/\- *lemma* filter.tendsto.sub
- \+/\- *lemma* nhds_translation
- \+/\- *lemma* neg_Z
- \+/\- *lemma* add_Z
- \+/\- *lemma* exists_Z_half
- \+/\- *lemma* nhds_eq
- \+/\- *lemma* nhds_zero_eq_Z
- \+/\- *lemma* is_open_mul_left
- \+/\- *lemma* is_open_mul_right
- \+/\- *lemma* topological_group.t1_space
- \+/\- *lemma* topological_group.regular_space
- \+/\- *lemma* topological_group.t2_space
- \+/\- *lemma* one_open_separated_mul
- \+/\- *lemma* compact_open_separated_mul
- \+/\- *lemma* compact_covered_by_mul_left_translates
- \+/\- *lemma* nhds_mul
- \+/\- *lemma* nhds_is_mul_hom

modified src/topology/algebra/monoid.lean
- \+/\- *lemma* continuous_mul
- \+/\- *lemma* continuous.mul
- \+/\- *lemma* continuous_mul_left
- \+/\- *lemma* continuous_mul_right
- \+/\- *lemma* continuous_on.mul
- \+/\- *lemma* tendsto_mul
- \+/\- *lemma* filter.tendsto.mul
- \+/\- *lemma* continuous_at.mul
- \+/\- *lemma* continuous_within_at.mul
- \+/\- *lemma* tendsto_list_prod
- \+/\- *lemma* continuous_list_prod
- \+/\- *lemma* continuous_pow
- \+/\- *lemma* continuous.pow
- \+/\- *lemma* submonoid.mem_nhds_one
- \+/\- *lemma* tendsto_multiset_prod
- \+/\- *lemma* tendsto_finset_prod
- \+/\- *lemma* continuous_multiset_prod
- \+/\- *lemma* continuous_finset_prod
- \+/\- *lemma* continuous_mul
- \+/\- *lemma* continuous.mul
- \+/\- *lemma* continuous_mul_left
- \+/\- *lemma* continuous_mul_right
- \+/\- *lemma* continuous_on.mul
- \+/\- *lemma* tendsto_mul
- \+/\- *lemma* filter.tendsto.mul
- \+/\- *lemma* continuous_at.mul
- \+/\- *lemma* continuous_within_at.mul
- \+/\- *lemma* tendsto_list_prod
- \+/\- *lemma* continuous_list_prod
- \+/\- *lemma* continuous_pow
- \+/\- *lemma* continuous.pow
- \+/\- *lemma* submonoid.mem_nhds_one
- \+/\- *lemma* tendsto_multiset_prod
- \+/\- *lemma* tendsto_finset_prod
- \+/\- *lemma* continuous_multiset_prod
- \+/\- *lemma* continuous_finset_prod



## [2020-10-07 21:39:17](https://github.com/leanprover-community/mathlib/commit/d67062f)
chore(algebra/pointwise): add `###` here and there ([#4514](https://github.com/leanprover-community/mathlib/pull/4514))
#### Estimated changes
modified src/algebra/pointwise.lean



## [2020-10-07 21:39:15](https://github.com/leanprover-community/mathlib/commit/fa8b7ba)
chore(topology/*): use dot notation for `is_open.prod` and `is_closed.prod` ([#4510](https://github.com/leanprover-community/mathlib/pull/4510))
#### Estimated changes
modified src/analysis/calculus/deriv.lean

modified src/analysis/special_functions/pow.lean

modified src/topology/algebra/open_subgroup.lean

modified src/topology/compact_open.lean

modified src/topology/constructions.lean
- \+ *lemma* is_open.prod
- \+ *lemma* is_closed.prod
- \- *lemma* is_open_prod
- \- *lemma* is_closed_prod

modified src/topology/instances/complex.lean

modified src/topology/instances/real.lean

modified src/topology/local_homeomorph.lean

modified src/topology/topological_fiber_bundle.lean

modified src/topology/uniform_space/compact_separated.lean



## [2020-10-07 20:25:40](https://github.com/leanprover-community/mathlib/commit/2b89d59)
chore(ring_theory/coprime): weaken assumptions of finset.prod_dvd_of_coprime ([#4506](https://github.com/leanprover-community/mathlib/pull/4506))
#### Estimated changes
modified src/ring_theory/coprime.lean
- \+/\- *theorem* finset.prod_dvd_of_coprime
- \+/\- *theorem* finset.prod_dvd_of_coprime



## [2020-10-07 18:09:31](https://github.com/leanprover-community/mathlib/commit/4635aee)
chore(algebra/continuous_functions): `coninuous` -> `continuous` ([#4508](https://github.com/leanprover-community/mathlib/pull/4508))
#### Estimated changes
modified src/topology/algebra/continuous_functions.lean



## [2020-10-07 18:09:28](https://github.com/leanprover-community/mathlib/commit/4e8427e)
fix(data/list/defs): remove map_head; rename map_last to modify_last ([#4507](https://github.com/leanprover-community/mathlib/pull/4507))
`map_head` is removed in favour of the equivalent `modify_head`.
`map_last` is renamed to `modify_last` for consistency with the other
`modify_*` functions.
#### Estimated changes
modified src/data/list/defs.lean
- \+ *def* modify_last
- \- *def* map_head
- \- *def* map_last



## [2020-10-07 18:09:25](https://github.com/leanprover-community/mathlib/commit/a4a20ac)
doc(data/num/basic): added doc-strings to most defs ([#4439](https://github.com/leanprover-community/mathlib/pull/4439))
#### Estimated changes
modified src/data/num/basic.lean



## [2020-10-07 16:08:11](https://github.com/leanprover-community/mathlib/commit/8f9c10f)
feat(data/matrix): add `matrix.mul_sub` and `matrix.sub_mul` ([#4505](https://github.com/leanprover-community/mathlib/pull/4505))
I was quite surprised that we didn't have this yet, but I guess they weren't needed when `sub_eq_add_neg` was still `@[simp]`.
#### Estimated changes
modified src/data/matrix/basic.lean



## [2020-10-07 16:08:08](https://github.com/leanprover-community/mathlib/commit/2d34e94)
chore(*big_operators*): line length ([#4504](https://github.com/leanprover-community/mathlib/pull/4504))
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* ring_hom.map_prod
- \+/\- *lemma* prod_subset
- \+/\- *lemma* ring_hom.map_prod
- \+/\- *lemma* prod_subset
- \+/\- *theorem* prod_eq_fold
- \+/\- *theorem* prod_eq_fold

modified src/algebra/polynomial/big_operators.lean



## [2020-10-07 16:08:05](https://github.com/leanprover-community/mathlib/commit/6b50fb9)
fix(tactic/ring): use int_sub_hack to avoid defeq blowup ([#4503](https://github.com/leanprover-community/mathlib/pull/4503))
#### Estimated changes
modified src/tactic/ring.lean

modified test/ring.lean



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
modified .github/workflows/build.yml

created scripts/copy-mod-doc-exceptions.txt

created scripts/lint-copy-mod-doc.py
- \+ *def* long_lines_check(lines,
- \+ *def* import_only_check(lines,
- \+ *def* regular_check(lines,
- \+ *def* format_errors(errors):
- \+ *def* lint(fn):

created scripts/lint-copy-mod-doc.sh

created scripts/update-copy-mod-doc-exceptions.sh

modified scripts/update_nolints.sh



## [2020-10-07 14:26:58](https://github.com/leanprover-community/mathlib/commit/c9d4567)
lint(data/matrix/basic): add definition docstrings ([#4478](https://github.com/leanprover-community/mathlib/pull/4478))
#### Estimated changes
modified src/data/matrix/basic.lean



## [2020-10-07 10:12:05](https://github.com/leanprover-community/mathlib/commit/6a85279)
fix(tactic/doc_commands): do not construct json by hand ([#4501](https://github.com/leanprover-community/mathlib/pull/4501))
Fixes three lines going over the 100 character limit.
The first one was a hand-rolled JSON serializer, I took the liberty to migrate it to the new `json` API.
#### Estimated changes
modified src/tactic/doc_commands.lean



## [2020-10-07 10:12:04](https://github.com/leanprover-community/mathlib/commit/0386ada)
chore(data/tree): linting ([#4499](https://github.com/leanprover-community/mathlib/pull/4499))
#### Estimated changes
modified src/data/tree.lean



## [2020-10-07 10:12:02](https://github.com/leanprover-community/mathlib/commit/cbbc123)
lint(category_theory/equivalence): docstring and a module doc ([#4495](https://github.com/leanprover-community/mathlib/pull/4495))
#### Estimated changes
modified src/category_theory/equivalence.lean



## [2020-10-07 10:12:00](https://github.com/leanprover-community/mathlib/commit/8a4b491)
feat(ring_theory/witt_vector/structure_polynomial): {map_}witt_structure_int ([#4465](https://github.com/leanprover-community/mathlib/pull/4465))
This is the second PR in a series on a fundamental theorem about Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
modified src/ring_theory/witt_vector/structure_polynomial.lean
- \+ *lemma* witt_structure_rat_rec_aux
- \+ *lemma* witt_structure_rat_rec
- \+ *lemma* bind₁_rename_expand_witt_polynomial
- \+ *lemma* C_p_pow_dvd_bind₁_rename_witt_polynomial_sub_sum
- \+ *lemma* map_witt_structure_int



## [2020-10-07 07:56:34](https://github.com/leanprover-community/mathlib/commit/e5ce9d3)
chore(data/quot): linting ([#4500](https://github.com/leanprover-community/mathlib/pull/4500))
#### Estimated changes
modified src/data/quot.lean



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
modified src/data/polynomial/field_division.lean

modified src/data/polynomial/integral_normalization.lean

modified src/data/set/function.lean

modified src/measure_theory/category/Meas.lean

modified src/tactic/derive_fintype.lean

modified src/tactic/derive_inhabited.lean

modified src/tactic/interactive.lean

modified src/tactic/omega/clause.lean

modified src/tactic/omega/coeffs.lean

modified src/tactic/omega/eq_elim.lean

modified src/tactic/omega/find_ees.lean

modified src/tactic/omega/find_scalars.lean

modified src/tactic/omega/int/dnf.lean

modified src/tactic/omega/int/form.lean

modified src/tactic/omega/int/main.lean

modified src/tactic/omega/int/preterm.lean

modified src/tactic/omega/lin_comb.lean

modified src/tactic/omega/main.lean

modified src/tactic/omega/misc.lean

modified src/tactic/omega/nat/dnf.lean

modified src/tactic/omega/nat/form.lean

modified src/tactic/omega/nat/main.lean

modified src/tactic/omega/nat/neg_elim.lean

modified src/tactic/omega/nat/preterm.lean

modified src/tactic/omega/nat/sub_elim.lean

modified src/tactic/omega/prove_unsats.lean

modified src/tactic/omega/term.lean



## [2020-10-07 06:23:11](https://github.com/leanprover-community/mathlib/commit/3c75527)
lint(group_theory/*): docstrings and an inhabited instance ([#4493](https://github.com/leanprover-community/mathlib/pull/4493))
An inhabited instance for `presented_group`
Docstrings in `group_theory/abelianization` and `group_theory/congruence`.
#### Estimated changes
modified src/group_theory/abelianization.lean

modified src/group_theory/congruence.lean

modified src/group_theory/presented_group.lean



## [2020-10-07 04:25:17](https://github.com/leanprover-community/mathlib/commit/8c528b9)
lint(group_theory/perm/*): docstrings ([#4492](https://github.com/leanprover-community/mathlib/pull/4492))
Adds missing docstrings in `group_theory/perm/cycles` and `group_theory/perm/sign`.
#### Estimated changes
modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/sign.lean



## [2020-10-07 01:06:50](https://github.com/leanprover-community/mathlib/commit/cb3118d)
chore(scripts): update nolints.txt ([#4490](https://github.com/leanprover-community/mathlib/pull/4490))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-10-07 01:06:47](https://github.com/leanprover-community/mathlib/commit/2e77ef6)
lint(order/lexographic, pilex): docstrings ([#4489](https://github.com/leanprover-community/mathlib/pull/4489))
Docstrings in `order/lexographic` and `order/pilex`
#### Estimated changes
modified src/order/lexicographic.lean

modified src/order/pilex.lean



## [2020-10-07 01:06:45](https://github.com/leanprover-community/mathlib/commit/afffab1)
lint(order/order_iso_nat): docstrings ([#4488](https://github.com/leanprover-community/mathlib/pull/4488))
Adds docstrings to `rel_embedding.nat_lt` and `rel_embedding.nat_gt`
#### Estimated changes
modified src/order/order_iso_nat.lean



## [2020-10-07 01:06:42](https://github.com/leanprover-community/mathlib/commit/93cdc3a)
feat(control/traversable/basic): composition of applicative transformations ([#4487](https://github.com/leanprover-community/mathlib/pull/4487))
Added composition law for applicative transformations, added rest of interface for coercion of applicative transformations to functions (lifted from `monoid_hom`), and proved composition was associative and has an identity.  Also corrected some documentation.
#### Estimated changes
modified src/control/traversable/basic.lean
- \+ *lemma* app_eq_coe
- \+ *lemma* coe_mk
- \+ *lemma* congr_fun
- \+ *lemma* congr_arg
- \+ *lemma* coe_inj
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* preserves_map'
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *def* comp



## [2020-10-07 01:06:41](https://github.com/leanprover-community/mathlib/commit/fe8b631)
lint(ring_theory/*): docstrings ([#4485](https://github.com/leanprover-community/mathlib/pull/4485))
Docstrings in `ring_theory/ideal/operations`, `ring_theory/multiplicity`, and `ring_theory/ring_invo`.
#### Estimated changes
modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/multiplicity.lean

modified src/ring_theory/ring_invo.lean



## [2020-10-06 22:45:54](https://github.com/leanprover-community/mathlib/commit/7488f8e)
lint(order/bounded_lattice): docstring ([#4484](https://github.com/leanprover-community/mathlib/pull/4484))
#### Estimated changes
modified src/order/bounded_lattice.lean



## [2020-10-06 22:45:52](https://github.com/leanprover-community/mathlib/commit/f4ccbdf)
feat(data/nat/basic): add_succ_lt_add ([#4483](https://github.com/leanprover-community/mathlib/pull/4483))
Add the lemma that, for natural numbers, if `a < b` and `c < d` then
`a + c + 1 < b + d` (i.e. a stronger version of `add_lt_add` for the
natural number case).  `library_search` did not find this in mathlib.
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* add_succ_lt_add



## [2020-10-06 22:45:50](https://github.com/leanprover-community/mathlib/commit/f88234d)
feat(measure_theory): integral of a non-negative function is >0 iff μ(support f) > 0 ([#4410](https://github.com/leanprover-community/mathlib/pull/4410))
Also add a few supporting lemmas
#### Estimated changes
modified src/algebra/order.lean
- \+ *lemma* lt_iff_ne
- \+ *lemma* le_iff_eq

modified src/data/indicator_function.lean
- \+ *lemma* indicator_of_support_subset
- \+ *lemma* indicator_support

modified src/data/support.lean
- \+ *lemma* support_eq_empty_iff

modified src/measure_theory/bochner_integration.lean
- \+ *lemma* integral_eq_zero_iff_of_nonneg_ae
- \+ *lemma* integral_eq_zero_iff_of_nonneg
- \+ *lemma* integral_pos_iff_support_of_nonneg_ae
- \+ *lemma* integral_pos_iff_support_of_nonneg

modified src/measure_theory/integration.lean
- \+/\- *lemma* lintegral_eq_zero_iff
- \+ *lemma* lintegral_pos_iff_support
- \+/\- *lemma* lintegral_eq_zero_iff

modified src/measure_theory/interval_integral.lean
- \+ *lemma* measure_theory.integrable.interval_integrable
- \+ *lemma* integral_zero
- \+ *lemma* integral_non_measurable
- \+ *lemma* integral_eq_integral_of_support_subset
- \+ *lemma* integral_eq_zero_iff_of_le_of_nonneg_ae
- \+ *lemma* integral_eq_zero_iff_of_nonneg_ae
- \+ *lemma* integral_pos_iff_support_of_nonneg_ae'
- \+ *lemma* integral_pos_iff_support_of_nonneg_ae

modified src/measure_theory/lebesgue_measure.lean
- \+ *lemma* filter.eventually.volume_pos_of_nhds_real

modified src/measure_theory/set_integral.lean
- \+ *lemma* set_integral_eq_zero_iff_of_nonneg_ae
- \+ *lemma* set_integral_pos_iff_support_of_nonneg_ae
- \+ *lemma* continuous.integrable_of_compact_closure_support

modified src/order/filter/basic.lean
- \+ *lemma* eventually_le.le_iff_eq

modified src/topology/algebra/ordered.lean
- \+ *lemma* filter.eventually.exists_Ioo_subset

modified src/topology/basic.lean
- \+ *lemma* is_open.eventually_mem



## [2020-10-06 21:23:34](https://github.com/leanprover-community/mathlib/commit/5192fd9)
feat(data/polynomial/degree/basic): add lemmas dealing with monomials, their support and their nat_degrees ([#4475](https://github.com/leanprover-community/mathlib/pull/4475))
#### Estimated changes
modified src/data/polynomial/degree/basic.lean
- \+ *lemma* nat_degree_C_mul_X_pow
- \+ *lemma* mem_support_C_mul_X_pow
- \+ *lemma* support_C_mul_X_pow
- \+ *lemma* card_support_C_mul_X_pow_le_one
- \+ *lemma* le_nat_degree_of_mem_supp
- \+ *lemma* le_degree_of_mem_supp
- \+ *lemma* nonempty_support_iff
- \+ *lemma* support_C_mul_X_pow_nonzero
- \+ *lemma* nat_degree_mem_support_of_nonzero
- \+ *lemma* nat_degree_eq_support_max'
- \+ *lemma* nat_degree_C_mul_X_pow_le
- \+ *lemma* nat_degree_C_mul_X_pow_of_nonzero



## [2020-10-06 21:23:32](https://github.com/leanprover-community/mathlib/commit/d768e46)
feat(ring_theory/witt_vector/structure_polynomial): witt_structure_rat{_prop} ([#4464](https://github.com/leanprover-community/mathlib/pull/4464))
This is the first PR in a series on a fundamental theorem for Witt polynomials.
Co-Authored-By: Rob Y. Lewis <rob.y.lewis@gmail.com>
#### Estimated changes
created src/ring_theory/witt_vector/structure_polynomial.lean
- \+ *theorem* witt_structure_rat_prop
- \+ *theorem* witt_structure_rat_exists_unique



## [2020-10-06 19:36:49](https://github.com/leanprover-community/mathlib/commit/7948b5a)
chore(*): fix authorship for split files ([#4480](https://github.com/leanprover-community/mathlib/pull/4480))
A few files with missing copyright headers in [#4477](https://github.com/leanprover-community/mathlib/pull/4477) came from splitting up older files, so the attribution was incorrect:
- `data/setoid/partition.lean` was split from `data/setoid.lean` in [#2853](https://github.com/leanprover-community/mathlib/pull/2853).
- `data/finset/order.lean` was split from `algebra/big_operators.lean` in [#3495](https://github.com/leanprover-community/mathlib/pull/3495).
- `group_theory/submonoid/operations.lean` was split from `group_theory/submonoid.lean` in  [#3058](https://github.com/leanprover-community/mathlib/pull/3058).
#### Estimated changes
modified src/data/finset/order.lean

modified src/data/setoid/partition.lean

modified src/group_theory/submonoid/operations.lean



## [2020-10-06 17:40:04](https://github.com/leanprover-community/mathlib/commit/ac05889)
chore(topology/list): one import per line ([#4479](https://github.com/leanprover-community/mathlib/pull/4479))
This one seems to have slipped through previous efforts
#### Estimated changes
modified src/topology/list.lean



## [2020-10-06 15:23:11](https://github.com/leanprover-community/mathlib/commit/e559ca9)
chore(*): add copyright headers ([#4477](https://github.com/leanprover-community/mathlib/pull/4477))
#### Estimated changes
modified src/category_theory/category/pairwise.lean

modified src/category_theory/limits/punit.lean

modified src/data/finset/order.lean

modified src/data/list/indexes.lean

modified src/data/setoid/partition.lean

modified src/group_theory/submonoid/operations.lean

modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean



## [2020-10-06 15:23:09](https://github.com/leanprover-community/mathlib/commit/7416127)
feat(data/polynomial/ring_division): add multiplicity of sum of polynomials is at least minimum of multiplicities ([#4442](https://github.com/leanprover-community/mathlib/pull/4442))
I've added the lemma `root_multiplicity_add` inside `data/polynomial/ring_division` that says that the multiplicity of a root in a sum of two polynomials is at least the minimum of the multiplicities.
#### Estimated changes
modified src/algebra/group_power/basic.lean
- \+ *lemma* min_pow_dvd_add

modified src/data/polynomial/ring_division.lean
- \+ *lemma* root_multiplicity_X_sub_C_pow
- \+ *lemma* root_multiplicity_of_dvd
- \+ *lemma* root_multiplicity_add



## [2020-10-06 12:41:50](https://github.com/leanprover-community/mathlib/commit/8d19939)
feat(*): make `int.le` irreducible ([#4474](https://github.com/leanprover-community/mathlib/pull/4474))
There's very rarely a reason to unfold `int.le` and it can create trouble: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/deep.20recursion.20was.20detected.20at.20'replace'
#### Estimated changes
modified src/algebra/field_power.lean

modified src/algebra/gcd_monoid.lean

modified src/data/int/basic.lean

modified src/data/int/range.lean

modified src/data/zsqrtd/gaussian_int.lean

modified src/number_theory/pythagorean_triples.lean

modified src/tactic/linarith/preprocessing.lean

modified src/tactic/omega/eq_elim.lean



## [2020-10-06 12:41:47](https://github.com/leanprover-community/mathlib/commit/99e308d)
chore(parity): even and odd in semiring ([#4473](https://github.com/leanprover-community/mathlib/pull/4473))
Replaces the ad-hoc `nat.even`, `nat.odd`, `int.even` and `int.odd` by definitions that make sense in semirings and get that `odd` can be `rintros`/`rcases`'ed. This requires almost no change except that `even` is not longer usable as a dot notation (which I see as a feature since I find `even n` to be more readable than `n.even`).
#### Estimated changes
modified src/algebra/ring/basic.lean
- \+ *lemma* even_iff_two_dvd
- \+ *def* even
- \+ *def* odd

modified src/analysis/convex/specific_functions.lean
- \+/\- *lemma* convex_on_pow_of_even
- \+/\- *lemma* int_prod_range_nonneg
- \+/\- *lemma* convex_on_pow_of_even
- \+/\- *lemma* int_prod_range_nonneg

modified src/analysis/mean_inequalities.lean

modified src/data/int/parity.lean
- \+ *lemma* odd_iff_not_even
- \- *lemma* odd_def
- \+/\- *theorem* mod_two_ne_one
- \+/\- *theorem* mod_two_ne_zero
- \+/\- *theorem* even_coe_nat
- \+/\- *theorem* even_iff
- \+ *theorem* odd_iff
- \+/\- *theorem* two_dvd_ne_zero
- \+/\- *theorem* even_zero
- \+/\- *theorem* not_even_one
- \+/\- *theorem* even_bit0
- \+/\- *theorem* even_add
- \+/\- *theorem* even_neg
- \+/\- *theorem* not_even_bit1
- \+/\- *theorem* even_sub
- \+/\- *theorem* even_mul
- \+/\- *theorem* even_pow
- \+/\- *theorem* mod_two_ne_one
- \+/\- *theorem* mod_two_ne_zero
- \+/\- *theorem* even_coe_nat
- \+/\- *theorem* even_iff
- \+/\- *theorem* two_dvd_ne_zero
- \+/\- *theorem* even_zero
- \+/\- *theorem* not_even_one
- \+/\- *theorem* even_bit0
- \+/\- *theorem* even_add
- \+/\- *theorem* even_neg
- \+/\- *theorem* not_even_bit1
- \+/\- *theorem* even_sub
- \+/\- *theorem* even_mul
- \+/\- *theorem* even_pow
- \- *def* even
- \- *def* odd

modified src/data/nat/parity.lean
- \+ *lemma* odd_iff_not_even
- \- *lemma* odd_def
- \+/\- *theorem* mod_two_ne_one
- \+/\- *theorem* mod_two_ne_zero
- \+/\- *theorem* even_iff
- \+ *theorem* odd_iff
- \+/\- *theorem* even_bit0
- \+/\- *theorem* even_add
- \+/\- *theorem* even.add
- \+/\- *theorem* not_even_bit1
- \+/\- *theorem* even_sub
- \+/\- *theorem* even.sub
- \+/\- *theorem* even_succ
- \+/\- *theorem* even_mul
- \+/\- *theorem* even_pow
- \+/\- *theorem* mod_two_ne_one
- \+/\- *theorem* mod_two_ne_zero
- \+/\- *theorem* even_iff
- \+/\- *theorem* even_bit0
- \+/\- *theorem* even_add
- \+/\- *theorem* even.add
- \+/\- *theorem* not_even_bit1
- \+/\- *theorem* even_sub
- \+/\- *theorem* even.sub
- \+/\- *theorem* even_succ
- \+/\- *theorem* even_mul
- \+/\- *theorem* even_pow
- \- *def* even
- \- *def* odd

modified src/number_theory/sum_four_squares.lean



## [2020-10-06 12:41:45](https://github.com/leanprover-community/mathlib/commit/1d1a041)
chore(data/mv_polynomial/basic): coeff_mul, more golfing and speedup ([#4472](https://github.com/leanprover-community/mathlib/pull/4472))
#### Estimated changes
modified src/algebra/group_with_zero.lean
- \+ *lemma* mul_eq_zero_of_ne_zero_imp_eq_zero

modified src/data/mv_polynomial/basic.lean



## [2020-10-06 12:41:43](https://github.com/leanprover-community/mathlib/commit/8cebd2b)
chore(algebra/algebra): Split subalgebras into their own file ([#4471](https://github.com/leanprover-community/mathlib/pull/4471))
This matches how `subring` and `submonoid` both have their own files.
This also remove `noncomputable theory` which is unnecessary for almost all the definitions
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \- *lemma* coe_val
- \- *lemma* val_apply
- \- *lemma* mem_to_submodule
- \- *lemma* map_mono
- \- *lemma* map_injective
- \- *lemma* mem_map
- \- *lemma* mem_range
- \- *lemma* coe_range
- \- *lemma* range_val
- \- *lemma* mem_subalgebra_of_subsemiring
- \- *lemma* mem_subalgebra_of_subring
- \- *lemma* mem_subalgebra_of_is_subring
- \- *theorem* mem_coe
- \- *theorem* ext
- \- *theorem* ext_iff
- \- *theorem* algebra_map_mem
- \- *theorem* srange_le
- \- *theorem* range_subset
- \- *theorem* range_le
- \- *theorem* one_mem
- \- *theorem* mul_mem
- \- *theorem* smul_mem
- \- *theorem* pow_mem
- \- *theorem* zero_mem
- \- *theorem* add_mem
- \- *theorem* neg_mem
- \- *theorem* sub_mem
- \- *theorem* nsmul_mem
- \- *theorem* gsmul_mem
- \- *theorem* coe_nat_mem
- \- *theorem* coe_int_mem
- \- *theorem* list_prod_mem
- \- *theorem* list_sum_mem
- \- *theorem* multiset_prod_mem
- \- *theorem* multiset_sum_mem
- \- *theorem* prod_mem
- \- *theorem* sum_mem
- \- *theorem* to_submodule_injective
- \- *theorem* to_submodule_inj
- \- *theorem* map_le
- \- *theorem* injective_cod_restrict
- \- *theorem* mem_bot
- \- *theorem* mem_top
- \- *theorem* coe_top
- \- *theorem* coe_bot
- \- *theorem* eq_top_iff
- \- *theorem* map_top
- \- *theorem* map_bot
- \- *theorem* comap_top
- \- *theorem* surjective_algebra_map_iff
- \- *theorem* bijective_algebra_map_iff
- \- *def* of_bijective
- \- *def* to_subring
- \- *def* val
- \- *def* to_submodule
- \- *def* comap
- \- *def* under
- \- *def* map
- \- *def* comap'
- \- *def* cod_restrict
- \- *def* adjoin
- \- *def* to_top
- \- *def* bot_equiv_of_injective
- \- *def* bot_equiv
- \- *def* subalgebra_of_subsemiring
- \- *def* subalgebra_of_subring
- \- *def* subalgebra_of_is_subring

created src/algebra/algebra/subalgebra.lean
- \+ *lemma* coe_val
- \+ *lemma* val_apply
- \+ *lemma* mem_to_submodule
- \+ *lemma* map_mono
- \+ *lemma* map_injective
- \+ *lemma* mem_map
- \+ *lemma* mem_range
- \+ *lemma* coe_range
- \+ *lemma* range_val
- \+ *lemma* mem_subalgebra_of_subsemiring
- \+ *lemma* mem_subalgebra_of_subring
- \+ *lemma* mem_subalgebra_of_is_subring
- \+ *theorem* mem_coe
- \+ *theorem* ext
- \+ *theorem* ext_iff
- \+ *theorem* algebra_map_mem
- \+ *theorem* srange_le
- \+ *theorem* range_subset
- \+ *theorem* range_le
- \+ *theorem* one_mem
- \+ *theorem* mul_mem
- \+ *theorem* smul_mem
- \+ *theorem* pow_mem
- \+ *theorem* zero_mem
- \+ *theorem* add_mem
- \+ *theorem* neg_mem
- \+ *theorem* sub_mem
- \+ *theorem* nsmul_mem
- \+ *theorem* gsmul_mem
- \+ *theorem* coe_nat_mem
- \+ *theorem* coe_int_mem
- \+ *theorem* list_prod_mem
- \+ *theorem* list_sum_mem
- \+ *theorem* multiset_prod_mem
- \+ *theorem* multiset_sum_mem
- \+ *theorem* prod_mem
- \+ *theorem* sum_mem
- \+ *theorem* to_submodule_injective
- \+ *theorem* to_submodule_inj
- \+ *theorem* map_le
- \+ *theorem* injective_cod_restrict
- \+ *theorem* mem_bot
- \+ *theorem* mem_top
- \+ *theorem* coe_top
- \+ *theorem* coe_bot
- \+ *theorem* eq_top_iff
- \+ *theorem* map_top
- \+ *theorem* map_bot
- \+ *theorem* comap_top
- \+ *theorem* surjective_algebra_map_iff
- \+ *theorem* bijective_algebra_map_iff
- \+ *def* to_subring
- \+ *def* val
- \+ *def* to_submodule
- \+ *def* comap
- \+ *def* under
- \+ *def* map
- \+ *def* comap'
- \+ *def* cod_restrict
- \+ *def* adjoin
- \+ *def* to_top
- \+ *def* subalgebra_of_subsemiring
- \+ *def* subalgebra_of_subring
- \+ *def* subalgebra_of_is_subring

modified src/algebra/category/Algebra/basic.lean

modified src/linear_algebra/finite_dimensional.lean

modified src/ring_theory/adjoin.lean



## [2020-10-06 12:41:42](https://github.com/leanprover-community/mathlib/commit/94bc31d)
lint(logic/unique): module doc, docstring ([#4461](https://github.com/leanprover-community/mathlib/pull/4461))
#### Estimated changes
modified src/logic/unique.lean



## [2020-10-06 12:41:40](https://github.com/leanprover-community/mathlib/commit/2fc6598)
lint(group_theory/eckmann_hilton): docs, module docs, unused argument ([#4459](https://github.com/leanprover-community/mathlib/pull/4459))
#### Estimated changes
modified src/group_theory/eckmann_hilton.lean
- \+/\- *def* comm_group
- \+/\- *def* comm_group



## [2020-10-06 12:41:38](https://github.com/leanprover-community/mathlib/commit/f4207aa)
feat(data/*): lemmas about lists and finsets ([#4457](https://github.com/leanprover-community/mathlib/pull/4457))
A part of [#4316](https://github.com/leanprover-community/mathlib/pull/4316)
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* prod_mk
- \+/\- *lemma* prod_mk

modified src/data/fintype/basic.lean
- \+ *lemma* univ_nonempty_iff
- \+/\- *lemma* univ_nonempty
- \+ *lemma* univ_eq_empty
- \+ *lemma* fin.univ_def
- \+/\- *lemma* univ_nonempty

modified src/data/fintype/card.lean
- \+ *theorem* fin.prod_univ_def
- \+ *theorem* fin.prod_of_fn

modified src/data/list/basic.lean
- \+ *lemma* prod_update_nth
- \+ *lemma* pmap_eq_nil
- \+ *lemma* attach_eq_nil

modified src/data/list/nodup.lean
- \+ *lemma* nodup.map_update

modified src/data/list/of_fn.lean
- \+ *lemma* of_fn_const
- \+/\- *theorem* of_fn_zero
- \+/\- *theorem* of_fn_succ
- \+/\- *theorem* of_fn_zero
- \+/\- *theorem* of_fn_succ

modified src/data/list/range.lean
- \+ *lemma* fin_range_zero
- \+ *lemma* fin_range_eq_nil
- \+ *theorem* range'_eq_nil
- \+ *theorem* range_eq_nil
- \+ *theorem* of_fn_id
- \+ *theorem* of_fn_eq_map

modified src/data/multiset/basic.lean



## [2020-10-06 12:41:36](https://github.com/leanprover-community/mathlib/commit/1fa07c2)
chore(category_theory/monoidal): add module docs ([#4454](https://github.com/leanprover-community/mathlib/pull/4454))
#### Estimated changes
modified src/category_theory/monoidal/category.lean

modified src/category_theory/monoidal/functor.lean



## [2020-10-06 12:41:33](https://github.com/leanprover-community/mathlib/commit/4d9406e)
feat(geometry/euclidean/monge_point): orthocentric systems ([#4448](https://github.com/leanprover-community/mathlib/pull/4448))
Define orthocentric systems of points, and prove some basic properties
of them.  In particular, if we say that an orthocentric system
consists of four points, one of which is the orthocenter of the
triangle formed by the other three, then each of the points is the
orthocenter of the triangle formed by the other three, and all four
triangles have the same circumradius.
#### Estimated changes
modified src/geometry/euclidean/basic.lean
- \+ *lemma* cospherical.affine_independent

modified src/geometry/euclidean/monge_point.lean
- \+ *lemma* exists_of_range_subset_orthocentric_system
- \+ *lemma* exists_dist_eq_circumradius_of_subset_insert_orthocenter
- \+ *lemma* orthocentric_system.affine_independent
- \+ *lemma* affine_span_of_orthocentric_system
- \+ *lemma* orthocentric_system.exists_circumradius_eq
- \+ *lemma* orthocentric_system.eq_insert_orthocenter
- \+ *def* orthocentric_system



## [2020-10-06 10:22:31](https://github.com/leanprover-community/mathlib/commit/e9b43b6)
lint(data/equiv/ring): docstrings, inhabited ([#4460](https://github.com/leanprover-community/mathlib/pull/4460))
#### Estimated changes
modified src/data/equiv/ring.lean



## [2020-10-06 10:22:29](https://github.com/leanprover-community/mathlib/commit/58a54d3)
chore(category_theory/*): doc-strings ([#4453](https://github.com/leanprover-community/mathlib/pull/4453))
#### Estimated changes
modified src/category_theory/endomorphism.lean

modified src/category_theory/groupoid.lean

modified src/category_theory/monoidal/functor.lean



## [2020-10-06 10:22:27](https://github.com/leanprover-community/mathlib/commit/6b59725)
chore(control/traversable/{basic,equiv,instances,lemmas}): linting ([#4444](https://github.com/leanprover-community/mathlib/pull/4444))
The `nolint`s in `instances.lean` are there because all the arguments need to be there for `is_lawful_traversable`.  In the same file, I moved `traverse_map` because it does not need the `is_lawful_applicative` instances.
#### Estimated changes
modified src/control/traversable/basic.lean
- \+ *def* id_transformation

modified src/control/traversable/equiv.lean

modified src/control/traversable/instances.lean

modified src/control/traversable/lemmas.lean



## [2020-10-06 10:22:25](https://github.com/leanprover-community/mathlib/commit/372d294)
feat(data/finsupp): lift a collection of `add_monoid_hom`s to an `add_monoid_hom` on `α →₀ β` ([#4395](https://github.com/leanprover-community/mathlib/pull/4395))
#### Estimated changes
modified src/algebra/module/basic.lean
- \+ *theorem* to_add_monoid_hom_injective

modified src/data/finsupp/basic.lean
- \+ *lemma* prod_of_support_subset
- \+/\- *lemma* prod_single_index
- \+ *lemma* add_closure_Union_range_single
- \+ *lemma* add_hom_ext
- \+ *lemma* lift_add_hom_apply
- \+ *lemma* lift_add_hom_symm_apply
- \+ *lemma* lift_add_hom_single_add_hom
- \+/\- *lemma* sum_single
- \+/\- *lemma* hom_ext
- \+/\- *lemma* prod_single_index
- \+/\- *lemma* sum_single
- \+/\- *lemma* hom_ext
- \+ *def* single_add_hom
- \+ *def* lift_add_hom



## [2020-10-06 09:02:45](https://github.com/leanprover-community/mathlib/commit/b1d3ef9)
chore(data/mv_polynomial/basic): speedup coeff_mul ([#4469](https://github.com/leanprover-community/mathlib/pull/4469))
#### Estimated changes
modified src/data/mv_polynomial/basic.lean



## [2020-10-06 09:02:43](https://github.com/leanprover-community/mathlib/commit/c08a868)
feat(trailing_degree): added two lemmas support_X, support_X_empty computing the support of X, simplified a couple of lemmas ([#4294](https://github.com/leanprover-community/mathlib/pull/4294))
#### Estimated changes
modified src/data/polynomial/basic.lean
- \+ *lemma* support_monomial
- \+ *lemma* support_monomial'
- \+ *lemma* monomial_eq_X_pow
- \+ *lemma* support_X_pow
- \+ *lemma* support_X_empty
- \+ *lemma* support_X

modified src/data/polynomial/coeff.lean
- \+ *lemma* C_mul_X_pow_eq_monomial
- \+ *lemma* support_mul_X_pow
- \+ *lemma* support_C_mul_X_pow'
- \- *lemma* monomial_one_eq_X_pow
- \- *lemma* monomial_eq_smul_X

modified src/data/polynomial/degree/trailing_degree.lean
- \+/\- *lemma* trailing_degree_lt_wf
- \+/\- *lemma* trailing_degree_lt_wf

modified src/data/polynomial/monomial.lean
- \+ *lemma* monomial_one_eq_X_pow
- \+ *lemma* monomial_eq_smul_X



## [2020-10-06 09:02:41](https://github.com/leanprover-community/mathlib/commit/fc7e943)
feat(normed_space/basic): remove localized notation ([#4246](https://github.com/leanprover-community/mathlib/pull/4246))
Remove notation for `tendsto` in `nhds`. 
Also make `is_bounded_linear_map.tendsto` protected.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* lim_norm
- \+/\- *lemma* lim_norm_zero
- \+/\- *lemma* lim_norm
- \+/\- *lemma* lim_norm_zero

modified src/analysis/normed_space/bounded_linear_maps.lean
- \- *lemma* tendsto



## [2020-10-06 07:07:40](https://github.com/leanprover-community/mathlib/commit/32b5b68)
chore(topology/compacts): inhabit instances ([#4462](https://github.com/leanprover-community/mathlib/pull/4462))
#### Estimated changes
modified src/topology/compacts.lean



## [2020-10-06 07:07:38](https://github.com/leanprover-community/mathlib/commit/d3b1d65)
lint(measure_theory): docstrings and style ([#4455](https://github.com/leanprover-community/mathlib/pull/4455))
#### Estimated changes
modified src/measure_theory/category/Meas.lean

modified src/measure_theory/measurable_space.lean

modified src/measure_theory/probability_mass_function.lean
- \+/\- *lemma* tsum_coe
- \+/\- *lemma* bind_apply
- \+/\- *lemma* tsum_coe
- \+/\- *lemma* bind_apply
- \+/\- *def* {u}
- \+/\- *def* pure
- \+/\- *def* seq
- \+/\- *def* of_fintype
- \+/\- *def* bernoulli
- \+/\- *def* {u}
- \+/\- *def* pure
- \+/\- *def* seq
- \+/\- *def* of_fintype
- \+/\- *def* bernoulli



## [2020-10-06 02:54:28](https://github.com/leanprover-community/mathlib/commit/523bddb)
doc(data/nat/prime, data/int/basic, data/int/modeq): docstrings ([#4445](https://github.com/leanprover-community/mathlib/pull/4445))
Filling in docstrings on `data/nat/prime`, `data/int/basic`, `data/int/modeq`.
#### Estimated changes
modified src/data/int/basic.lean

modified src/data/int/modeq.lean

modified src/data/nat/prime.lean



## [2020-10-06 02:54:26](https://github.com/leanprover-community/mathlib/commit/cd78599)
lint(category_theory/monad): doc-strings ([#4428](https://github.com/leanprover-community/mathlib/pull/4428))
#### Estimated changes
modified src/category_theory/monad/adjunction.lean

modified src/category_theory/monad/algebra.lean



## [2020-10-06 02:04:28](https://github.com/leanprover-community/mathlib/commit/a228af6)
chore(scripts): update nolints.txt ([#4456](https://github.com/leanprover-community/mathlib/pull/4456))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-10-06 00:55:20](https://github.com/leanprover-community/mathlib/commit/27b6c23)
lint(category_theory/limits): docstrings and inhabited instances ([#4435](https://github.com/leanprover-community/mathlib/pull/4435))
#### Estimated changes
modified src/category_theory/limits/cones.lean

modified src/category_theory/limits/over.lean

modified src/category_theory/limits/preserves/basic.lean

modified src/category_theory/limits/shapes/products.lean



## [2020-10-06 00:09:52](https://github.com/leanprover-community/mathlib/commit/37879aa)
feat(undergrad): minimal polynomial ([#4308](https://github.com/leanprover-community/mathlib/pull/4308))
Adds minimal polynomial of endomorphisms to the undergrad list, although its use will be hard to guess for undergrads.
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified src/field_theory/minimal_polynomial.lean

modified src/linear_algebra/eigenspace.lean



## [2020-10-05 23:18:37](https://github.com/leanprover-community/mathlib/commit/432da5f)
feat(measure_theory/integration): add lintegral_with_density_eq_lintegral_mul ([#4350](https://github.com/leanprover-community/mathlib/pull/4350))
This is Exercise 1.2.1 from Terence Tao's "An Epsilon of Room"
#### Estimated changes
modified docs/references.bib

modified src/measure_theory/integration.lean
- \+/\- *lemma* lintegral_add
- \+/\- *lemma* lintegral_smul_measure
- \+/\- *lemma* lintegral_sum_measure
- \+/\- *lemma* lintegral_add_measure
- \+/\- *lemma* lintegral_const_mul
- \+/\- *lemma* with_density_apply
- \+ *lemma* lintegral_with_density_eq_lintegral_mul
- \+/\- *lemma* lintegral_add
- \+/\- *lemma* lintegral_smul_measure
- \+/\- *lemma* lintegral_sum_measure
- \+/\- *lemma* lintegral_add_measure
- \+/\- *lemma* lintegral_const_mul
- \+/\- *lemma* with_density_apply



## [2020-10-05 22:01:48](https://github.com/leanprover-community/mathlib/commit/97c444e)
lint(topology/algebra): docstrings ([#4446](https://github.com/leanprover-community/mathlib/pull/4446))
#### Estimated changes
modified src/topology/algebra/group.lean

modified src/topology/algebra/open_subgroup.lean

modified src/topology/algebra/ring.lean

modified src/topology/algebra/uniform_group.lean

modified src/topology/algebra/uniform_ring.lean



## [2020-10-05 19:45:24](https://github.com/leanprover-community/mathlib/commit/21158c4)
lint(data/pnat): Docstrings and an unused argument in `pnat.basic`, `pnat.factors` ([#4443](https://github.com/leanprover-community/mathlib/pull/4443))
Adds docstrings
Changes `div_exact` from having one unused input of type `k | m` to `div_exact m k`.
#### Estimated changes
modified src/data/pnat/basic.lean
- \+/\- *theorem* mul_div_exact
- \+/\- *theorem* mul_div_exact
- \+/\- *def* div_exact
- \+/\- *def* div_exact

modified src/data/pnat/factors.lean



## [2020-10-05 19:45:21](https://github.com/leanprover-community/mathlib/commit/45347f9)
lint(src/order/rel_iso): docstrings and inhabited ([#4441](https://github.com/leanprover-community/mathlib/pull/4441))
#### Estimated changes
modified src/order/rel_iso.lean



## [2020-10-05 19:45:19](https://github.com/leanprover-community/mathlib/commit/2127165)
chore(linear_algebra/basis): split off `linear_independent.lean` ([#4440](https://github.com/leanprover-community/mathlib/pull/4440))
The file `basis.lean` was getting rather long (1500 lines), so I decided to split it into two not as long files at a natural point: everything using `linear_independent` but not `basis` can go into a new file `linear_independent.lean`. As a result, we can import `basis.lean` a bit later in the `ring_theory` hierarchy.
#### Estimated changes
modified src/linear_algebra/basis.lean
- \- *lemma* linear_independent_empty_type
- \- *lemma* linear_independent.ne_zero
- \- *lemma* linear_independent.comp
- \- *lemma* linear_independent_of_zero_eq_one
- \- *lemma* linear_independent.unique
- \- *lemma* linear_independent.injective
- \- *lemma* linear_independent_span
- \- *lemma* linear_independent_of_comp
- \- *lemma* linear_independent.to_subtype_range
- \- *lemma* linear_independent.of_subtype_range
- \- *lemma* linear_independent.restrict_of_comp_subtype
- \- *lemma* linear_independent_empty
- \- *lemma* linear_independent.mono
- \- *lemma* linear_independent.union
- \- *lemma* linear_independent_of_finite
- \- *lemma* linear_independent_Union_of_directed
- \- *lemma* linear_independent_sUnion_of_directed
- \- *lemma* linear_independent_bUnion_of_directed
- \- *lemma* linear_independent_Union_finite_subtype
- \- *lemma* linear_independent_Union_finite
- \- *lemma* linear_independent.total_repr
- \- *lemma* linear_independent.total_comp_repr
- \- *lemma* linear_independent.repr_ker
- \- *lemma* linear_independent.repr_range
- \- *lemma* linear_independent.repr_eq
- \- *lemma* linear_independent.repr_eq_single
- \- *lemma* linear_independent_iff_not_smul_mem_span
- \- *lemma* surjective_of_linear_independent_of_span
- \- *lemma* eq_of_linear_independent_of_span_subtype
- \- *lemma* linear_independent.image
- \- *lemma* linear_independent.image_subtype
- \- *lemma* linear_independent.inl_union_inr
- \- *lemma* linear_independent_inl_union_inr'
- \- *lemma* le_of_span_le_span
- \- *lemma* span_le_span_iff
- \- *lemma* mem_span_insert_exchange
- \- *lemma* linear_independent_iff_not_mem_span
- \- *lemma* linear_independent_unique
- \- *lemma* linear_independent_singleton
- \- *lemma* disjoint_span_singleton
- \- *lemma* linear_independent.insert
- \- *lemma* exists_linear_independent
- \- *lemma* exists_of_linear_independent_of_finite_span
- \- *lemma* exists_finite_card_le_of_finite_of_linear_independent_of_span
- \- *theorem* linear_independent_iff
- \- *theorem* linear_independent_iff'
- \- *theorem* linear_independent_iff''
- \- *theorem* linear_dependent_iff
- \- *theorem* linear_independent_equiv
- \- *theorem* linear_independent_equiv'
- \- *theorem* linear_independent_image
- \- *theorem* linear_independent.image'
- \- *theorem* linear_independent_comp_subtype
- \- *theorem* linear_independent_subtype
- \- *theorem* linear_independent_comp_subtype_disjoint
- \- *theorem* linear_independent_subtype_disjoint
- \- *theorem* linear_independent_iff_total_on
- \- *theorem* linear_independent_monoid_hom
- \- *theorem* linear_independent_insert
- \- *theorem* linear_independent_insert'
- \- *def* linear_independent
- \- *def* linear_independent.total_equiv
- \- *def* linear_independent.repr

created src/linear_algebra/linear_independent.lean
- \+ *lemma* linear_independent_empty_type
- \+ *lemma* linear_independent.ne_zero
- \+ *lemma* linear_independent.comp
- \+ *lemma* linear_independent_of_zero_eq_one
- \+ *lemma* linear_independent.unique
- \+ *lemma* linear_independent.injective
- \+ *lemma* linear_independent_span
- \+ *lemma* linear_independent_of_comp
- \+ *lemma* linear_independent.to_subtype_range
- \+ *lemma* linear_independent.of_subtype_range
- \+ *lemma* linear_independent.restrict_of_comp_subtype
- \+ *lemma* linear_independent_empty
- \+ *lemma* linear_independent.mono
- \+ *lemma* linear_independent.union
- \+ *lemma* linear_independent_of_finite
- \+ *lemma* linear_independent_Union_of_directed
- \+ *lemma* linear_independent_sUnion_of_directed
- \+ *lemma* linear_independent_bUnion_of_directed
- \+ *lemma* linear_independent_Union_finite_subtype
- \+ *lemma* linear_independent_Union_finite
- \+ *lemma* linear_independent.total_repr
- \+ *lemma* linear_independent.total_comp_repr
- \+ *lemma* linear_independent.repr_ker
- \+ *lemma* linear_independent.repr_range
- \+ *lemma* linear_independent.repr_eq
- \+ *lemma* linear_independent.repr_eq_single
- \+ *lemma* linear_independent_iff_not_smul_mem_span
- \+ *lemma* surjective_of_linear_independent_of_span
- \+ *lemma* eq_of_linear_independent_of_span_subtype
- \+ *lemma* linear_independent.image
- \+ *lemma* linear_independent.image_subtype
- \+ *lemma* linear_independent.inl_union_inr
- \+ *lemma* linear_independent_inl_union_inr'
- \+ *lemma* le_of_span_le_span
- \+ *lemma* span_le_span_iff
- \+ *lemma* mem_span_insert_exchange
- \+ *lemma* linear_independent_iff_not_mem_span
- \+ *lemma* linear_independent_unique
- \+ *lemma* linear_independent_singleton
- \+ *lemma* disjoint_span_singleton
- \+ *lemma* linear_independent.insert
- \+ *lemma* exists_linear_independent
- \+ *lemma* exists_of_linear_independent_of_finite_span
- \+ *lemma* exists_finite_card_le_of_finite_of_linear_independent_of_span
- \+ *theorem* linear_independent_iff
- \+ *theorem* linear_independent_iff'
- \+ *theorem* linear_independent_iff''
- \+ *theorem* linear_dependent_iff
- \+ *theorem* linear_independent_equiv
- \+ *theorem* linear_independent_equiv'
- \+ *theorem* linear_independent_image
- \+ *theorem* linear_independent.image'
- \+ *theorem* linear_independent_comp_subtype
- \+ *theorem* linear_independent_subtype
- \+ *theorem* linear_independent_comp_subtype_disjoint
- \+ *theorem* linear_independent_subtype_disjoint
- \+ *theorem* linear_independent_iff_total_on
- \+ *theorem* linear_independent_monoid_hom
- \+ *theorem* linear_independent_insert
- \+ *theorem* linear_independent_insert'
- \+ *def* linear_independent
- \+ *def* linear_independent.total_equiv
- \+ *def* linear_independent.repr

modified src/ring_theory/algebra_tower.lean

modified src/ring_theory/noetherian.lean



## [2020-10-05 19:45:18](https://github.com/leanprover-community/mathlib/commit/88c76ab)
feat(order/filter/ultrafilter): Add variant of `exists_ultrafilter`. ([#4436](https://github.com/leanprover-community/mathlib/pull/4436))
The lemma `exists_ultrafilter` tells us that any proper filter can be extended to an ultrafilter (using Zorn's lemma). This PR adds a variant, called `exists_ultrafilter_of_finite_inter_nonempty` which says that any collection of sets `S` can be extended to an ultrafilter whenever it satisfies the property that the intersection of any finite subcollection `T` is nonempty.
#### Estimated changes
modified src/order/filter/ultrafilter.lean
- \+ *lemma* exists_ultrafilter_of_finite_inter_nonempty



## [2020-10-05 19:45:15](https://github.com/leanprover-community/mathlib/commit/9151532)
lint(order/conditionally_complete_lattice): docstrings ([#4434](https://github.com/leanprover-community/mathlib/pull/4434))
#### Estimated changes
modified src/order/conditionally_complete_lattice.lean



## [2020-10-05 19:45:13](https://github.com/leanprover-community/mathlib/commit/221ec60)
feat(ring_theory/ideal): ideals in product rings ([#4431](https://github.com/leanprover-community/mathlib/pull/4431))
#### Estimated changes
modified src/algebra/group/prod.lean
- \+ *lemma* coe_prod_comm
- \+ *lemma* coe_prod_comm_symm
- \+ *def* prod_comm

modified src/algebra/ring/prod.lean
- \+ *lemma* coe_prod_comm
- \+ *lemma* coe_prod_comm_symm
- \+ *lemma* coe_coe_prod_comm
- \+ *lemma* coe_coe_prod_comm_symm
- \+ *lemma* fst_comp_coe_prod_comm
- \+ *lemma* snd_comp_coe_prod_comm
- \+ *def* prod_comm

modified src/algebraic_geometry/prime_spectrum.lean
- \+ *lemma* prime_spectrum_prod_symm_inl_as_ideal
- \+ *lemma* prime_spectrum_prod_symm_inr_as_ideal

modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ker_coe_equiv
- \+ *theorem* map_is_prime_of_equiv

created src/ring_theory/ideal/prod.lean
- \+ *lemma* mem_prod
- \+ *lemma* prod_top_top
- \+ *lemma* map_fst_prod
- \+ *lemma* map_snd_prod
- \+ *lemma* map_prod_comm_prod
- \+ *lemma* ideal_prod_equiv_symm_apply
- \+ *lemma* prod.ext_iff
- \+ *lemma* is_prime_of_is_prime_prod_top
- \+ *lemma* is_prime_of_is_prime_prod_top'
- \+ *lemma* is_prime_ideal_prod_top
- \+ *lemma* is_prime_ideal_prod_top'
- \+ *lemma* ideal_prod_prime_aux
- \+ *lemma* prime_ideals_equiv_symm_inl
- \+ *lemma* prime_ideals_equiv_symm_inr
- \+ *theorem* ideal_prod_eq
- \+ *theorem* ideal_prod_prime
- \+ *def* prod
- \+ *def* ideal_prod_equiv



## [2020-10-05 19:45:10](https://github.com/leanprover-community/mathlib/commit/f9e3779)
lint(category_theory/whiskering): add doc-strings ([#4417](https://github.com/leanprover-community/mathlib/pull/4417))
#### Estimated changes
modified src/category_theory/whiskering.lean
- \+/\- *def* left_unitor
- \+/\- *def* right_unitor
- \+/\- *def* left_unitor
- \+/\- *def* right_unitor



## [2020-10-05 19:45:08](https://github.com/leanprover-community/mathlib/commit/d2140ef)
feat(algebra/gcd_monoid): `gcd_mul_dvd_mul_gcd` ([#4386](https://github.com/leanprover-community/mathlib/pull/4386))
Adds a `gcd_monoid` version of `nat.gcd_mul_dvd_mul_gcd`
#### Estimated changes
modified src/algebra/gcd_monoid.lean
- \+ *lemma* exists_dvd_and_dvd_of_dvd_mul
- \+ *theorem* gcd_mul_dvd_mul_gcd



## [2020-10-05 17:20:44](https://github.com/leanprover-community/mathlib/commit/c58c4e6)
docs(tactic/{fin_cases,lift}): lint ([#4421](https://github.com/leanprover-community/mathlib/pull/4421))
#### Estimated changes
modified src/tactic/fin_cases.lean

modified src/tactic/lift.lean



## [2020-10-05 17:20:42](https://github.com/leanprover-community/mathlib/commit/e89d0ed)
chore(*/multilinear): generalize `comp_linear_map` to a family of linear maps ([#4408](https://github.com/leanprover-community/mathlib/pull/4408))
Together with [#4316](https://github.com/leanprover-community/mathlib/pull/4316) this will give us multilinear maps corresponding to monomials.
#### Estimated changes
modified src/analysis/calculus/times_cont_diff.lean

modified src/analysis/normed_space/bounded_linear_maps.lean

modified src/linear_algebra/multilinear.lean
- \+ *lemma* comp_linear_map_apply
- \+/\- *def* comp_linear_map
- \+/\- *def* comp_linear_map

modified src/logic/function/basic.lean
- \+ *lemma* apply_update
- \+/\- *lemma* comp_update
- \+/\- *lemma* comp_update

modified src/topology/algebra/multilinear.lean
- \+ *lemma* comp_continuous_linear_map_apply



## [2020-10-05 15:18:22](https://github.com/leanprover-community/mathlib/commit/7f74e6b)
feat(data/mv_polynomial/basic): map_map_range_eq_iff ([#4438](https://github.com/leanprover-community/mathlib/pull/4438))
Split off from [#4268](https://github.com/leanprover-community/mathlib/pull/4268)
#### Estimated changes
modified src/data/mv_polynomial/basic.lean
- \+ *lemma* map_map_range_eq_iff



## [2020-10-05 15:18:20](https://github.com/leanprover-community/mathlib/commit/39f5d6b)
feat(data/rat/basic): denom_eq_one_iff ([#4437](https://github.com/leanprover-community/mathlib/pull/4437))
Split off from [#4268](https://github.com/leanprover-community/mathlib/pull/4268)
#### Estimated changes
modified src/data/rat/basic.lean
- \+ *lemma* denom_eq_one_iff



## [2020-10-05 15:18:18](https://github.com/leanprover-community/mathlib/commit/22398f3)
chore(src/linear_algebra): linting ([#4427](https://github.com/leanprover-community/mathlib/pull/4427))
#### Estimated changes
modified src/linear_algebra/dual.lean



## [2020-10-05 11:39:07](https://github.com/leanprover-community/mathlib/commit/ca269b4)
feat(linear_algebra/affine_space/finite_dimensional): collinearity ([#4433](https://github.com/leanprover-community/mathlib/pull/4433))
Define collinearity of a set of points in an affine space for a vector
space (as meaning the `vector_span` has dimension at most 1), and
prove some basic lemmas about it, leading to three points being
collinear if and only if they are not affinely independent.
#### Estimated changes
modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* collinear_iff_dim_le_one
- \+ *lemma* collinear_iff_findim_le_one
- \+ *lemma* collinear_empty
- \+ *lemma* collinear_singleton
- \+ *lemma* collinear_iff_of_mem
- \+ *lemma* collinear_iff_exists_forall_eq_smul_vadd
- \+ *lemma* collinear_insert_singleton
- \+ *lemma* affine_independent_iff_not_collinear
- \+ *lemma* collinear_iff_not_affine_independent
- \+ *def* collinear



## [2020-10-05 11:39:05](https://github.com/leanprover-community/mathlib/commit/b0fe280)
chore(category_theory/yoneda): doc-strings ([#4429](https://github.com/leanprover-community/mathlib/pull/4429))
#### Estimated changes
modified src/category_theory/products/basic.lean

modified src/category_theory/yoneda.lean



## [2020-10-05 11:39:03](https://github.com/leanprover-community/mathlib/commit/1501bf6)
chore(data/fin2): linting ([#4426](https://github.com/leanprover-community/mathlib/pull/4426))
#### Estimated changes
modified src/data/fin2.lean



## [2020-10-05 11:39:01](https://github.com/leanprover-community/mathlib/commit/dd73dd2)
chore(linear_algebra/finsupp*): linting ([#4425](https://github.com/leanprover-community/mathlib/pull/4425))
#### Estimated changes
modified src/linear_algebra/finsupp.lean

modified src/linear_algebra/finsupp_vector_space.lean



## [2020-10-05 11:38:58](https://github.com/leanprover-community/mathlib/commit/c058524)
chore(data/fintype/basic): linting ([#4424](https://github.com/leanprover-community/mathlib/pull/4424))
#### Estimated changes
modified src/data/fintype/basic.lean



## [2020-10-05 11:38:56](https://github.com/leanprover-community/mathlib/commit/70b8e82)
data(data/dlist/{basic,instances}): linting ([#4422](https://github.com/leanprover-community/mathlib/pull/4422))
#### Estimated changes
modified src/data/dlist/basic.lean

modified src/data/dlist/instances.lean



## [2020-10-05 11:38:54](https://github.com/leanprover-community/mathlib/commit/da1265c)
chore(data/buffer/basic): linting ([#4420](https://github.com/leanprover-community/mathlib/pull/4420))
#### Estimated changes
modified src/data/buffer/basic.lean



## [2020-10-05 11:38:52](https://github.com/leanprover-community/mathlib/commit/768ff76)
chore(data/array/lemmas): linting ([#4419](https://github.com/leanprover-community/mathlib/pull/4419))
#### Estimated changes
modified src/data/array/lemmas.lean
- \+/\- *def* d_array_equiv_fin
- \+/\- *def* d_array_equiv_fin



## [2020-10-05 11:38:50](https://github.com/leanprover-community/mathlib/commit/c370bd0)
chore(data/W): linting ([#4418](https://github.com/leanprover-community/mathlib/pull/4418))
#### Estimated changes
modified src/data/W.lean



## [2020-10-05 11:38:48](https://github.com/leanprover-community/mathlib/commit/6a4fd24)
lint(category_theory/adjunction): add doc-strings ([#4415](https://github.com/leanprover-community/mathlib/pull/4415))
#### Estimated changes
modified src/category_theory/adjunction/basic.lean

modified src/category_theory/adjunction/limits.lean



## [2020-10-05 11:38:46](https://github.com/leanprover-community/mathlib/commit/17b607f)
chore(algebra/direct_sum): linting ([#4412](https://github.com/leanprover-community/mathlib/pull/4412))
#### Estimated changes
modified src/algebra/direct_sum.lean

modified src/algebra/lie/basic.lean

modified src/linear_algebra/direct_sum_module.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* lof_apply
- \+/\- *lemma* lof_apply
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff



## [2020-10-05 11:38:43](https://github.com/leanprover-community/mathlib/commit/b44e927)
feat(data/finsupp): Make `finsupp.dom_congr` a `≃+` ([#4398](https://github.com/leanprover-community/mathlib/pull/4398))
Since this has additional structure, it may as well be part of the type
#### Estimated changes
modified src/data/finsupp/basic.lean

modified src/linear_algebra/basic.lean
- \+ *lemma* coe_to_linear_equiv
- \+ *lemma* coe_to_linear_equiv_symm
- \+ *def* to_linear_equiv

modified src/linear_algebra/finsupp.lean



## [2020-10-05 11:38:41](https://github.com/leanprover-community/mathlib/commit/54a2c6b)
chore(algebra/group/with_one): prove `group_with_zero` earlier, drop custom lemmas ([#4385](https://github.com/leanprover-community/mathlib/pull/4385))
#### Estimated changes
modified src/algebra/continued_fractions/computation/approximations.lean

modified src/algebra/group/with_one.lean
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_one
- \- *lemma* zero_div
- \- *lemma* div_zero
- \- *lemma* one_div
- \- *lemma* div_one
- \- *lemma* mul_right_inv
- \- *lemma* mul_left_inv
- \- *lemma* mul_inv_rev
- \- *lemma* mul_div_cancel
- \- *lemma* div_mul_cancel
- \- *lemma* div_eq_iff_mul_eq
- \- *lemma* mul_inv_cancel
- \- *lemma* div_eq_div
- \- *theorem* mul_comm

modified src/data/option/basic.lean
- \+ *lemma* coe_def



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
modified src/algebra/lie/basic.lean

modified src/field_theory/tower.lean

modified src/linear_algebra/basis.lean
- \+ *lemma* is_basis.range_repr_self
- \+ *lemma* is_basis.range_repr

modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* matrix.to_bilin_form_comp
- \+/\- *lemma* matrix_is_adjoint_pair_bilin_form
- \+/\- *lemma* matrix.to_bilin_form_comp
- \+/\- *lemma* matrix_is_adjoint_pair_bilin_form

modified src/linear_algebra/matrix.lean
- \+ *lemma* matrix.mul_vec_lin_apply
- \+ *lemma* matrix.mul_vec_std_basis
- \+ *lemma* linear_map.to_matrix'_symm
- \+ *lemma* matrix.to_lin'_symm
- \+ *lemma* linear_map.to_matrix'_to_lin'
- \+ *lemma* matrix.to_lin'_to_matrix'
- \+ *lemma* linear_map.to_matrix'_apply
- \+ *lemma* matrix.to_lin'_apply
- \+ *lemma* matrix.to_lin'_one
- \+ *lemma* linear_map.to_matrix'_id
- \+ *lemma* matrix.to_lin'_mul
- \+ *lemma* linear_map.to_matrix'_comp
- \+ *lemma* linear_map.to_matrix'_mul
- \+ *lemma* linear_map.to_matrix_symm
- \+ *lemma* matrix.to_lin_symm
- \+ *lemma* matrix.to_lin_to_matrix
- \+ *lemma* linear_map.to_matrix_to_lin
- \+ *lemma* linear_map.to_matrix_apply
- \+ *lemma* linear_map.to_matrix_apply'
- \+ *lemma* matrix.to_lin_apply
- \+ *lemma* linear_map.to_matrix_id
- \+ *lemma* matrix.to_lin_one
- \+ *lemma* linear_map.to_matrix_comp
- \+ *lemma* linear_map.to_matrix_mul
- \+ *lemma* matrix.to_lin_mul
- \+ *lemma* linear_map.to_matrix_transpose
- \+ *lemma* linear_map.to_matrix_symm_transpose
- \+ *lemma* diagonal_to_lin'
- \+/\- *lemma* rank_vec_mul_vec
- \+ *lemma* ker_diagonal_to_lin'
- \- *lemma* to_lin_add
- \- *lemma* to_lin_zero
- \- *lemma* to_lin_neg
- \- *lemma* to_lin_apply
- \- *lemma* mul_to_lin
- \- *lemma* to_lin_one
- \- *lemma* to_matrix_id
- \- *lemma* to_matrix_to_lin
- \- *lemma* to_lin_to_matrix
- \- *lemma* linear_equiv_matrix'_apply
- \- *lemma* linear_equiv_matrix'_symm_apply
- \- *lemma* linear_equiv_matrix_apply
- \- *lemma* linear_equiv_matrix_symm_apply
- \- *lemma* linear_equiv_matrix_apply'
- \- *lemma* linear_equiv_matrix_id
- \- *lemma* linear_equiv_matrix_symm_one
- \- *lemma* comp_to_matrix_mul
- \- *lemma* linear_equiv_matrix_comp
- \- *lemma* linear_equiv_matrix_mul
- \- *lemma* linear_equiv_matrix_symm_mul
- \- *lemma* linear_equiv_matrix_transpose
- \- *lemma* linear_equiv_matrix_symm_transpose
- \- *lemma* diagonal_to_lin
- \+/\- *lemma* rank_vec_mul_vec
- \- *lemma* ker_diagonal_to_lin
- \+ *theorem* linear_map.to_matrix_range
- \- *theorem* to_lin_of_equiv
- \- *theorem* to_matrix_of_equiv
- \- *theorem* linear_equiv_matrix_range
- \+ *def* matrix.mul_vec_lin
- \+ *def* linear_map.to_matrix'
- \+ *def* matrix.to_lin'
- \+ *def* linear_map.to_matrix
- \+ *def* matrix.to_lin
- \+/\- *def* alg_equiv_matrix'
- \+/\- *def* alg_equiv_matrix
- \- *def* eval
- \- *def* to_lin
- \- *def* to_matrixₗ
- \- *def* to_matrix
- \- *def* linear_equiv_matrix'
- \- *def* linear_equiv_matrix
- \+/\- *def* alg_equiv_matrix'
- \+/\- *def* alg_equiv_matrix

modified src/linear_algebra/quadratic_form.lean

modified src/linear_algebra/special_linear_group.lean
- \+ *lemma* to_lin'_mul
- \+ *lemma* to_lin'_one
- \- *lemma* to_lin_mul
- \- *lemma* to_lin_one
- \+ *def* to_lin'
- \- *def* to_lin



## [2020-10-05 08:49:57](https://github.com/leanprover-community/mathlib/commit/67b312c)
chore(logic/relation): linting ([#4414](https://github.com/leanprover-community/mathlib/pull/4414))
#### Estimated changes
modified src/logic/relation.lean



## [2020-10-05 08:49:55](https://github.com/leanprover-community/mathlib/commit/186660c)
feat(*): assorted `simp` lemmas for IMO 2019 q1 ([#4383](https://github.com/leanprover-community/mathlib/pull/4383))
* mark some lemmas about cancelling in expressions with `(-)` as `simp`;
* simplify `a * b = a * c` to `b = c ∨ a = 0`, and similarly for
  `a * c = b * c;
* change `priority` of `monoid.has_pow` and `group.has_pow` to the
  default priority.
* simplify `monoid.pow` and `group.gpow` to `has_pow.pow`.
#### Estimated changes
modified src/algebra/group/basic.lean
- \+/\- *lemma* sub_sub_cancel
- \+/\- *lemma* add_add_neg_cancel'_right
- \+/\- *lemma* add_add_sub_cancel
- \+/\- *lemma* sub_add_add_cancel
- \+/\- *lemma* sub_add_sub_cancel'
- \+/\- *lemma* add_sub_sub_cancel
- \+/\- *lemma* sub_sub_sub_cancel_left
- \+/\- *lemma* sub_sub_cancel
- \+/\- *lemma* add_add_neg_cancel'_right
- \+/\- *lemma* add_add_sub_cancel
- \+/\- *lemma* sub_add_add_cancel
- \+/\- *lemma* sub_add_sub_cancel'
- \+/\- *lemma* add_sub_sub_cancel
- \+/\- *lemma* sub_sub_sub_cancel_left

modified src/algebra/group/commute.lean
- \+ *lemma* mul_inv_cancel_comm
- \+ *lemma* mul_inv_cancel_comm_assoc
- \+ *lemma* inv_mul_cancel_comm
- \+ *lemma* inv_mul_cancel_comm_assoc
- \+ *theorem* inv_mul_cancel_assoc
- \+ *theorem* mul_inv_cancel_assoc

modified src/algebra/group_power/basic.lean
- \+ *lemma* monoid.pow_eq_has_pow
- \+ *lemma* group.gpow_eq_has_pow

modified src/algebra/group_with_zero.lean
- \+ *lemma* mul_eq_mul_right_iff
- \+ *lemma* mul_eq_mul_left_iff

modified src/analysis/calculus/specific_functions.lean

modified src/analysis/special_functions/trigonometric.lean

modified src/data/int/basic.lean

modified src/data/padics/padic_integers.lean
- \+ *lemma* coet_pow
- \- *lemma* cast_pow

modified src/set_theory/ordinal_notation.lean



## [2020-10-05 08:49:53](https://github.com/leanprover-community/mathlib/commit/8f4475b)
feat(combinatorics/partitions): Add partitions ([#4303](https://github.com/leanprover-community/mathlib/pull/4303))
#### Estimated changes
modified src/combinatorics/composition.lean

created src/combinatorics/partition.lean
- \+ *lemma* of_composition_surj
- \+ *lemma* count_of_sums_of_ne_zero
- \+ *lemma* count_of_sums_zero
- \+ *def* of_composition
- \+ *def* of_sums
- \+ *def* of_multiset
- \+ *def* indiscrete_partition
- \+ *def* odds
- \+ *def* distincts
- \+ *def* odd_distincts



## [2020-10-05 07:39:36](https://github.com/leanprover-community/mathlib/commit/ca679ac)
chore(algebra/direct_limit): linting ([#4411](https://github.com/leanprover-community/mathlib/pull/4411))
#### Estimated changes
modified src/algebra/direct_limit.lean
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *lemma* lift_unique
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *lemma* of.zero_exact_aux
- \- *lemma* directed_system
- \+/\- *lemma* lift_unique
- \+/\- *lemma* of.zero_exact_aux
- \+/\- *theorem* exists_of
- \+/\- *theorem* lift_unique
- \+/\- *theorem* of.zero_exact
- \+/\- *theorem* exists_of
- \+/\- *theorem* polynomial.exists_of
- \+/\- *theorem* induction_on
- \+/\- *theorem* of_injective
- \+/\- *theorem* lift_unique
- \+/\- *theorem* exists_of
- \+/\- *theorem* lift_unique
- \+/\- *theorem* of.zero_exact
- \+/\- *theorem* exists_of
- \+/\- *theorem* polynomial.exists_of
- \+/\- *theorem* induction_on
- \+/\- *theorem* of_injective
- \+/\- *theorem* lift_unique
- \+/\- *def* direct_limit
- \+/\- *def* direct_limit



## [2020-10-05 07:39:32](https://github.com/leanprover-community/mathlib/commit/581b141)
feat(data/complex): norm_cast lemmas ([#4405](https://github.com/leanprover-community/mathlib/pull/4405))
Mark various existing lemmas such as `abs_of_real` and `of_real_exp`
as `norm_cast` lemmas so that `norm_cast` and related tactics can
handle expressions involving those functions, and add lemmas
`of_real_prod` and `of_real_sum` to allow those tactics to work with
sums and products involving coercions from real to complex.
#### Estimated changes
modified src/data/complex/basic.lean
- \+/\- *lemma* abs_of_real
- \+ *lemma* of_real_prod
- \+ *lemma* of_real_sum
- \+/\- *lemma* abs_of_real

modified src/data/complex/exponential.lean
- \+/\- *lemma* of_real_exp
- \+/\- *lemma* of_real_sinh
- \+/\- *lemma* of_real_cosh
- \+/\- *lemma* of_real_tanh
- \+/\- *lemma* of_real_sin
- \+/\- *lemma* of_real_cos
- \+/\- *lemma* of_real_tan
- \+/\- *lemma* of_real_exp
- \+/\- *lemma* of_real_sinh
- \+/\- *lemma* of_real_cosh
- \+/\- *lemma* of_real_tanh
- \+/\- *lemma* of_real_sin
- \+/\- *lemma* of_real_cos
- \+/\- *lemma* of_real_tan



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
modified src/linear_algebra/affine_space/basic.lean
- \+ *lemma* vector_span_range_eq_span_range_vsub_left_ne
- \+ *lemma* vector_span_range_eq_span_range_vsub_right_ne

modified src/linear_algebra/affine_space/finite_dimensional.lean
- \+ *lemma* findim_vector_span_image_finset_le
- \+ *lemma* findim_vector_span_range_le
- \+ *lemma* affine_independent_iff_findim_vector_span_eq
- \+ *lemma* affine_independent_iff_le_findim_vector_span
- \+ *lemma* affine_independent_iff_not_findim_vector_span_le
- \+ *lemma* findim_vector_span_le_iff_not_affine_independent



## [2020-10-05 07:39:28](https://github.com/leanprover-community/mathlib/commit/565e961)
feat(number_theory/arithmetic_function): Define arithmetic functions/the Dirichlet ring ([#4352](https://github.com/leanprover-community/mathlib/pull/4352))
Defines a type `arithmetic_function A` of functions from `nat` to `A` sending 0 to 0
Defines the Dirichlet ring structure on `arithmetic_function A`
#### Estimated changes
created src/number_theory/arithmetic_function.lean
- \+ *lemma* to_fun_eq
- \+ *lemma* map_zero
- \+ *lemma* zero_apply
- \+ *lemma* one_one
- \+ *lemma* one_apply_ne
- \+ *lemma* nat_coe_apply
- \+ *lemma* int_coe_apply
- \+ *lemma* coe_coe
- \+ *lemma* add_apply
- \+ *lemma* mul_apply
- \+ *theorem* coe_inj
- \+ *theorem* ext
- \+ *theorem* ext_iff

modified src/number_theory/divisors.lean
- \+ *lemma* dvd_of_mem_divisors



## [2020-10-05 05:24:10](https://github.com/leanprover-community/mathlib/commit/9ab7f05)
feat(category_theory/limits/terminal): limit of a diagram with initial object ([#4404](https://github.com/leanprover-community/mathlib/pull/4404))
If the index category for a functor has an initial object, the image of the functor is a limit.
#### Estimated changes
modified src/category_theory/limits/shapes/terminal.lean
- \+/\- *def* as_empty_cone
- \+/\- *def* as_empty_cocone
- \+ *def* cone_of_diagram_initial
- \+ *def* limit_of_diagram_initial
- \+ *def* limit_of_initial
- \+ *def* cocone_of_diagram_terminal
- \+ *def* colimit_of_diagram_terminal
- \+ *def* colimit_of_terminal
- \+/\- *def* as_empty_cone
- \+/\- *def* as_empty_cocone



## [2020-10-05 05:24:08](https://github.com/leanprover-community/mathlib/commit/91d9e96)
chore(algebra/ring/basic): docs, simps ([#4375](https://github.com/leanprover-community/mathlib/pull/4375))
* add docstrings to all typeclasses in `algebra/ring/basic`;
* add `ring_hom.inhabited := ⟨id α⟩` to make linter happy;
* given `f : α →+* β`, simplify `f.to_monoid_hom` and
`f.to_add_monoid_hom` to coercions;
* add `simp` lemmas for coercions of `ring_hom.mk f _ _ _ _` to
`monoid_hom` and `add_monoid_hom`.
#### Estimated changes
modified src/algebra/ring/basic.lean
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* coe_mk
- \+/\- *lemma* coe_monoid_hom
- \+ *lemma* to_monoid_hom_eq_coe
- \+ *lemma* coe_monoid_hom_mk
- \+/\- *lemma* coe_add_monoid_hom
- \+ *lemma* to_add_monoid_hom_eq_coe
- \+ *lemma* coe_add_monoid_hom_mk
- \+/\- *lemma* coe_monoid_hom
- \+/\- *lemma* coe_add_monoid_hom
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* coe_mk

modified src/ring_theory/algebra_tower.lean



## [2020-10-05 05:24:06](https://github.com/leanprover-community/mathlib/commit/08cdf37)
feat(analysis/complex/roots_of_unity): complex (primitive) roots of unity ([#4330](https://github.com/leanprover-community/mathlib/pull/4330))
#### Estimated changes
modified docs/undergrad.yaml

created src/analysis/complex/roots_of_unity.lean
- \+ *lemma* is_primitive_root_exp_of_coprime
- \+ *lemma* is_primitive_root_exp
- \+ *lemma* is_primitive_root_iff
- \+ *lemma* mem_roots_of_unity
- \+ *lemma* card_roots_of_unity
- \+ *lemma* card_primitive_roots

modified src/analysis/special_functions/trigonometric.lean
- \+ *lemma* pi_ne_zero
- \+ *lemma* two_pi_I_ne_zero



## [2020-10-05 04:08:17](https://github.com/leanprover-community/mathlib/commit/bf99889)
feat(category_theory/limits): lift self limit ([#4403](https://github.com/leanprover-community/mathlib/pull/4403))
A couple of little lemmas to simplify lift of a limit cone.
#### Estimated changes
modified src/category_theory/limits/limits.lean
- \+ *lemma* lift_self
- \+ *lemma* desc_self



## [2020-10-05 02:16:27](https://github.com/leanprover-community/mathlib/commit/916b5d3)
feat(topology): completion of separable space is separable ([#4399](https://github.com/leanprover-community/mathlib/pull/4399))
API change:
* `dense` renamed to `exists_between`;
* new `dense (s : set α)` means `∀ x, x ∈ closure s`.
#### Estimated changes
modified src/analysis/calculus/local_extr.lean

modified src/analysis/calculus/mean_value.lean

modified src/analysis/specific_limits.lean

modified src/data/real/ennreal.lean

modified src/data/real/nnreal.lean

modified src/data/set/intervals/basic.lean

modified src/data/set/intervals/infinite.lean

modified src/data/set/intervals/ord_connected.lean

modified src/order/basic.lean
- \+ *lemma* exists_between
- \- *lemma* dense

modified src/order/bounded_lattice.lean

modified src/order/bounds.lean

modified src/topology/algebra/ordered.lean

modified src/topology/bases.lean
- \+ *lemma* exists_countable_closure_eq_univ
- \+ *lemma* dense_range.separable_space

modified src/topology/basic.lean
- \+ *lemma* dense_iff_closure_eq
- \+ *lemma* dense.closure_eq
- \+/\- *lemma* dense_of_subset_dense
- \+ *lemma* dense_range_iff_closure_range
- \+ *lemma* dense_range.closure_range
- \+ *lemma* dense_range.comp
- \+ *lemma* dense_range.nonempty
- \+ *lemma* continuous.dense_image_of_dense_range
- \+/\- *lemma* dense_of_subset_dense
- \+ *def* dense
- \+ *def* dense_range
- \+ *def* dense_range.inhabited

modified src/topology/bounded_continuous_function.lean

modified src/topology/constructions.lean
- \+ *lemma* dense_range.prod

modified src/topology/continuous_on.lean
- \+ *lemma* dense_range.nhds_within_ne_bot

modified src/topology/dense_embedding.lean
- \+ *lemma* separable
- \+ *lemma* separable
- \- *lemma* dense_range_iff_closure_range
- \- *lemma* dense_range.closure_range
- \- *lemma* dense_range.nhds_within_ne_bot
- \- *lemma* dense_range.comp
- \- *lemma* dense_range.nonempty
- \- *lemma* dense_range.prod
- \- *def* dense_range
- \- *def* dense_range.inhabited

modified src/topology/instances/ennreal.lean

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/closeds.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/uniform_space/completion.lean



## [2020-10-05 01:18:46](https://github.com/leanprover-community/mathlib/commit/fc09dba)
feat(analysis/special_functions/pow): exp_mul ([#4409](https://github.com/leanprover-community/mathlib/pull/4409))
Add the lemma that `exp (x * y) = (exp x) ^ y`, for real `x` and `y`.
#### Estimated changes
modified src/analysis/special_functions/pow.lean
- \+ *lemma* exp_mul



## [2020-10-04 20:49:23](https://github.com/leanprover-community/mathlib/commit/d13d21b)
feat(algebra/big_operators/order): bounding finite fibration cardinalities from below ([#4396](https://github.com/leanprover-community/mathlib/pull/4396))
Also including unrelated change `finset.inter_eq_sdiff_sdiff`.
#### Estimated changes
modified src/algebra/big_operators/order.lean
- \+ *theorem* mul_card_image_le_card_of_maps_to
- \+ *theorem* mul_card_image_le_card

modified src/data/finset/basic.lean
- \+ *lemma* inter_eq_sdiff_sdiff



## [2020-10-04 19:18:31](https://github.com/leanprover-community/mathlib/commit/f437365)
feat(linear_algebra/dimension): one-dimensional spaces ([#4400](https://github.com/leanprover-community/mathlib/pull/4400))
Add some lemmas about the vectors in spaces and subspaces of dimension
at most 1.
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *lemma* le_span_singleton_iff

modified src/linear_algebra/dimension.lean
- \+ *lemma* dim_le_one_iff
- \+ *lemma* dim_submodule_le_one_iff
- \+ *lemma* dim_submodule_le_one_iff'



## [2020-10-04 15:27:55](https://github.com/leanprover-community/mathlib/commit/8f53676)
feat(data/nat): Slightly strengthen nat.coprime_of_dvd/nat.coprime_of_dvd' ([#4368](https://github.com/leanprover-community/mathlib/pull/4368))
It is sufficient to consider prime factors.
The theorems now depend on nat.prime (data/nat/prime.lean), which depends on
data/nat/gcd.lean, so I moved them to prime.lean.
#### Estimated changes
modified archive/imo/imo1959_q1.lean

modified src/data/nat/gcd.lean
- \- *theorem* coprime_of_dvd
- \- *theorem* coprime_of_dvd'

modified src/data/nat/modeq.lean

modified src/data/nat/prime.lean
- \+ *theorem* coprime_of_dvd
- \+ *theorem* coprime_of_dvd'

modified src/number_theory/pell.lean



## [2020-10-04 11:10:48](https://github.com/leanprover-community/mathlib/commit/729b60a)
feat(data/set/basic): subsingleton_coe ([#4388](https://github.com/leanprover-community/mathlib/pull/4388))
Add a lemma relating a set being a subsingleton set to its coercion to
a type being a subsingleton type.
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* subsingleton_coe



## [2020-10-04 11:10:45](https://github.com/leanprover-community/mathlib/commit/e8b65e6)
feat(data/set/basic): eq_singleton_iff_unique_mem ([#4387](https://github.com/leanprover-community/mathlib/pull/4387))
We have this lemma for `finset`.  Add a version for `set` (with the
same name).
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* eq_singleton_iff_unique_mem



## [2020-10-04 11:10:43](https://github.com/leanprover-community/mathlib/commit/e1b1d17)
feat(algebra/group): construct `add_monoid_hom` from `map_sub` ([#4382](https://github.com/leanprover-community/mathlib/pull/4382))
#### Estimated changes
modified src/algebra/group/hom.lean
- \+ *lemma* coe_of_map_mul_inv
- \+ *lemma* coe_of_map_sub
- \+/\- *theorem* map_sub
- \+/\- *theorem* map_sub
- \+ *def* of_map_mul_inv
- \+ *def* of_map_sub



## [2020-10-04 11:10:41](https://github.com/leanprover-community/mathlib/commit/231271d)
chore(data/equiv/mul_add): add more `equiv` lemmas to `mul_equiv` namespace ([#4380](https://github.com/leanprover-community/mathlib/pull/4380))
Also make `apply_eq_iff_eq` and `apply_eq_iff_eq_symm_apply` use
implicit arguments.
#### Estimated changes
modified src/category_theory/limits/types.lean

modified src/data/equiv/basic.lean
- \+/\- *theorem* apply_eq_iff_eq
- \+/\- *theorem* apply_eq_iff_eq_symm_apply
- \+/\- *theorem* apply_eq_iff_eq
- \+/\- *theorem* apply_eq_iff_eq_symm_apply

modified src/data/equiv/encodable/basic.lean

modified src/data/equiv/mul_add.lean
- \+ *lemma* apply_eq_iff_symm_apply
- \+ *lemma* symm_apply_eq
- \+ *lemma* eq_symm_apply
- \+ *theorem* apply_eq_iff_eq

modified src/data/opposite.lean

modified src/group_theory/monoid_localization.lean



## [2020-10-04 11:10:39](https://github.com/leanprover-community/mathlib/commit/5d35b9a)
feat(algebra/gcd_monoid, data/*set/gcd): a few lemmas about gcds ([#4354](https://github.com/leanprover-community/mathlib/pull/4354))
Adds lemmas about gcds useful for proving Gauss's Lemma
#### Estimated changes
modified src/algebra/gcd_monoid.lean
- \+ *lemma* gcd_eq_of_dvd_sub_right
- \+ *lemma* gcd_eq_of_dvd_sub_left

modified src/data/finset/gcd.lean
- \+ *lemma* gcd_eq_gcd_filter_ne_zero
- \+ *lemma* gcd_mul_left
- \+ *lemma* gcd_mul_right
- \+ *lemma* gcd_eq_of_dvd_sub
- \+ *theorem* gcd_eq_zero_iff

modified src/data/multiset/gcd.lean
- \+ *theorem* gcd_eq_zero_iff



## [2020-10-04 09:48:24](https://github.com/leanprover-community/mathlib/commit/509dd9e)
feat(linear_algebra/basic): span_singleton smul lemmas ([#4394](https://github.com/leanprover-community/mathlib/pull/4394))
Add two submodule lemmas relating `span R ({r • x})` and `span R {x}`.
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *lemma* span_singleton_smul_le
- \+ *lemma* span_singleton_smul_eq



## [2020-10-04 06:59:45](https://github.com/leanprover-community/mathlib/commit/c3d0835)
chore(data/mv_polynomial): rename `pderivative` to `pderiv` ([#4381](https://github.com/leanprover-community/mathlib/pull/4381))
This name matches `fderiv` and `deriv` we have in `analysis/`.
#### Estimated changes
renamed src/data/mv_polynomial/pderivative.lean to src/data/mv_polynomial/pderiv.lean
- \+ *lemma* pderiv_monomial
- \+ *lemma* pderiv_C
- \+ *lemma* pderiv_eq_zero_of_not_mem_vars
- \+ *lemma* pderiv_monomial_single
- \+ *lemma* pderiv_monomial_mul
- \+ *lemma* pderiv_mul
- \+ *lemma* pderiv_C_mul
- \- *lemma* pderivative_monomial
- \- *lemma* pderivative_C
- \- *lemma* pderivative_eq_zero_of_not_mem_vars
- \- *lemma* pderivative_monomial_single
- \- *lemma* pderivative_monomial_mul
- \- *lemma* pderivative_mul
- \- *lemma* pderivative_C_mul
- \+ *def* pderiv
- \- *def* pderivative



## [2020-10-04 05:39:03](https://github.com/leanprover-community/mathlib/commit/e902cae)
feat(category_theory/limits/cofinal): better API for cofinal functors ([#4276](https://github.com/leanprover-community/mathlib/pull/4276))
This PR
1. Proves that `F : C ⥤ D` being cofinal is equivalent to `colimit (F ⋙ G) ≅ colimit G` for all `G : D ⥤ E`. (Previously we just had the implication.)
2. Proves that if `F` is cofinal then `limit (F.op ⋙ H) ≅ limit H` for all `H: Dᵒᵖ ⥤ E`.
#### Estimated changes
modified src/category_theory/is_connected.lean
- \+ *lemma* zag_symmetric
- \+ *lemma* zigzag_symmetric

modified src/category_theory/limits/cofinal.lean
- \+ *lemma* limit_cone_comp_aux
- \+ *lemma* limit_pre_is_iso_aux
- \+ *lemma* has_limit_of_comp
- \+ *lemma* zigzag_of_eqv_gen_quot_rel
- \+ *lemma* cofinal_of_colimit_comp_coyoneda_iso_punit
- \+ *def* extend_cone_cone_to_cocone
- \+ *def* extend_cone_cocone_to_cone
- \+ *def* extend_cone
- \+ *def* cones_equiv
- \+ *def* is_limit_whisker_equiv
- \+ *def* is_limit_extend_cone_equiv
- \+ *def* limit_cone_comp
- \+ *def* limit_iso
- \+ *def* limit_cone_of_comp
- \+ *def* limit_iso'
- \+ *def* colimit_comp_coyoneda_iso

modified src/category_theory/limits/limits.lean
- \+ *lemma* of_cone_equiv_apply_desc
- \+ *lemma* of_cone_equiv_symm_apply_desc

modified src/category_theory/limits/types.lean
- \+ *lemma* colimit_equiv_quot_apply
- \+ *lemma* colimit_eq
- \+ *def* quot.rel

created src/category_theory/limits/yoneda.lean
- \+ *def* colimit_cocone
- \+ *def* colimit_cocone_is_colimit
- \+ *def* colimit_coyoneda_iso

modified src/category_theory/opposites.lean



## [2020-10-04 03:45:24](https://github.com/leanprover-community/mathlib/commit/e738e90)
feat(algebra/group_power/identities): named ring identities ([#4390](https://github.com/leanprover-community/mathlib/pull/4390))
This PR adds a new file containing some "named" ring identities provable by `ring`.
#### Estimated changes
created src/algebra/group_power/identities.lean
- \+ *theorem* pow_two_add_pow_two_mul_pow_two_add_pow_two
- \+ *theorem* pow_two_add_mul_pow_two_mul_pow_two_add_mul_pow_two
- \+ *theorem* pow_four_add_four_mul_pow_four
- \+ *theorem* pow_four_add_four_mul_pow_four'
- \+ *theorem* sum_four_sq_mul_sum_four_sq
- \+ *theorem* sum_eight_sq_mul_sum_eight_sq

modified src/number_theory/sum_four_squares.lean



## [2020-10-04 01:55:07](https://github.com/leanprover-community/mathlib/commit/f2044a5)
chore(scripts): update nolints.txt ([#4392](https://github.com/leanprover-community/mathlib/pull/4392))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-10-03 23:52:40](https://github.com/leanprover-community/mathlib/commit/333c216)
chore(algebra/group/type_tags): Use ≃ instead of → ([#4346](https://github.com/leanprover-community/mathlib/pull/4346))
These functions are all equivalences, so we may as well expose that in their type
This also fills in some conversions that were missing.
Unfortunately this requires some type ascriptions in a handful of places.
It might be possible to remove these somehow.
This zulip thread contains a mwe: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Type.20inference.20on.20.60.E2.86.92.60.20vs.20.60.E2.89.83.60/near/211922501.
#### Estimated changes
modified src/algebra/group/type_tags.lean
- \- *lemma* of_mul_injective
- \- *lemma* to_mul_injective
- \- *lemma* of_add_injective
- \- *lemma* to_add_injective
- \+/\- *def* additive.of_mul
- \+/\- *def* additive.to_mul
- \+/\- *def* multiplicative.of_add
- \+/\- *def* multiplicative.to_add
- \+/\- *def* add_monoid_hom.to_multiplicative
- \+/\- *def* monoid_hom.to_additive
- \+/\- *def* add_monoid_hom.to_multiplicative'
- \+/\- *def* monoid_hom.to_additive'
- \+ *def* add_monoid_hom.to_multiplicative''
- \+ *def* monoid_hom.to_additive''
- \+/\- *def* additive.of_mul
- \+/\- *def* additive.to_mul
- \+/\- *def* multiplicative.of_add
- \+/\- *def* multiplicative.to_add
- \+/\- *def* add_monoid_hom.to_multiplicative
- \+/\- *def* monoid_hom.to_additive
- \+/\- *def* add_monoid_hom.to_multiplicative'
- \+/\- *def* monoid_hom.to_additive'

modified src/data/equiv/mul_add.lean
- \+/\- *def* add_equiv.to_multiplicative
- \+/\- *def* mul_equiv.to_additive
- \+ *def* add_equiv.to_multiplicative'
- \+ *def* mul_equiv.to_additive'
- \+ *def* add_equiv.to_multiplicative''
- \+ *def* mul_equiv.to_additive''
- \+/\- *def* add_equiv.to_multiplicative
- \+/\- *def* mul_equiv.to_additive

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/ring_theory/roots_of_unity.lean



## [2020-10-03 20:51:17](https://github.com/leanprover-community/mathlib/commit/a0ba5e7)
doc(data/real/*): add a few docstrings, `ereal.has_zero`, and `ereal.inhabited` ([#4378](https://github.com/leanprover-community/mathlib/pull/4378))
#### Estimated changes
modified src/data/real/basic.lean

modified src/data/real/ereal.lean

modified src/data/real/nnreal.lean



## [2020-10-03 20:51:15](https://github.com/leanprover-community/mathlib/commit/e593ffa)
feat(algebra/ordered*): more simp lemmas ([#4359](https://github.com/leanprover-community/mathlib/pull/4359))
Simplify expressions like `0 < a * b`, `0 < a / b`, `a / b < 1` etc. to FOL formulas of inequalities on `a`, `b`.
#### Estimated changes
modified src/algebra/gcd_monoid.lean

modified src/algebra/group_power/basic.lean
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_nonneg
- \+/\- *theorem* pow_pos
- \+/\- *theorem* pow_nonneg

modified src/algebra/group_with_zero.lean
- \+ *lemma* inv_eq_one'

modified src/algebra/order.lean
- \+ *lemma* ne.le_iff_lt
- \+ *lemma* ne.lt_or_lt

modified src/algebra/ordered_field.lean
- \+ *lemma* div_pos_iff
- \+ *lemma* div_neg_iff
- \+ *lemma* div_nonneg_iff
- \+ *lemma* div_nonpos_iff
- \+ *lemma* inv_lt_one_iff_of_pos
- \+ *lemma* inv_lt_one_iff
- \+ *lemma* one_lt_inv_iff
- \+ *lemma* inv_le_one_iff
- \+ *lemma* one_le_inv_iff
- \+ *lemma* one_lt_div_iff
- \+ *lemma* one_le_div_iff
- \+ *lemma* div_lt_one_iff
- \+ *lemma* div_le_one_iff

modified src/algebra/ordered_ring.lean
- \+/\- *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \+ *lemma* nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg
- \+/\- *lemma* pos_of_mul_pos_left
- \+/\- *lemma* pos_of_mul_pos_right
- \+ *lemma* mul_pos_iff
- \+ *lemma* mul_neg_iff
- \+ *lemma* mul_nonneg_iff
- \+ *lemma* mul_nonpos_iff
- \+/\- *lemma* pos_of_mul_pos_left
- \+/\- *lemma* pos_of_mul_pos_right
- \+/\- *lemma* pos_and_pos_or_neg_and_neg_of_mul_pos
- \- *lemma* linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero

modified src/analysis/hofer.lean

modified src/data/int/basic.lean
- \+/\- *lemma* coe_nat_nonneg
- \+/\- *lemma* coe_nat_nonneg

modified src/data/padics/hensel.lean

modified src/data/rat/order.lean

modified src/data/real/nnreal.lean

modified src/number_theory/lucas_lehmer.lean



## [2020-10-03 18:56:38](https://github.com/leanprover-community/mathlib/commit/b790b27)
feat(slim_check): sampleable instance for generating functions and injective functions ([#3967](https://github.com/leanprover-community/mathlib/pull/3967))
This also adds `printable_prop` to trace why propositions hold or don't hold and `sampleable_ext` to allow the data structure generated and shrunken by `slim_check` to have a different type from the type we are looking for.
#### Estimated changes
modified src/control/uliftable.lean
- \+/\- *def* adapt_up
- \+/\- *def* adapt_up

modified src/data/list/perm.lean

modified src/system/random/basic.lean

modified src/tactic/slim_check.lean

created src/testing/slim_check/functions.lean
- \+ *lemma* list.apply_id_cons
- \+ *lemma* list.apply_id_zip_eq
- \+ *lemma* apply_id_mem_iff
- \+ *lemma* list.apply_id_eq_self
- \+ *lemma* apply_id_injective
- \+ *def* apply
- \+ *def* repr_aux
- \+ *def* list.to_finmap'
- \+ *def* total.sizeof
- \+ *def* apply
- \+ *def* list.apply_id
- \+ *def* perm.slice
- \+ *def* slice_sizes

modified src/testing/slim_check/gen.lean
- \+ *def* choose_nat'
- \+ *def* resize
- \+ *def* elements
- \+ *def* freq_aux
- \+ *def* freq
- \- *def* one_of_aux

modified src/testing/slim_check/sampleable.lean
- \+ *lemma* rec_shrink_with_eq
- \+/\- *def* sizeof_lt
- \+/\- *def* shrink_fn
- \+ *def* int.has_sizeof
- \+/\- *def* sum.shrink
- \+ *def* rec_shrink_with
- \+ *def* small
- \+ *def* small.mk
- \+ *def* large
- \+ *def* large.mk
- \+/\- *def* print_samples
- \+/\- *def* sizeof_lt
- \+/\- *def* shrink_fn
- \+/\- *def* sum.shrink
- \+/\- *def* print_samples

modified src/testing/slim_check/testable.lean
- \+/\- *def* add_var_to_counter_example
- \+ *def* use_has_to_string
- \+ *def* use_has_to_string.mk
- \+/\- *def* trace_if_giveup
- \+ *def* format_failure
- \+ *def* format_failure'
- \+ *def* add_shrinks
- \+/\- *def* minimize_aux
- \+/\- *def* minimize
- \- *def* test_result.to_string
- \+/\- *def* add_var_to_counter_example
- \+/\- *def* trace_if_giveup
- \+/\- *def* minimize_aux
- \+/\- *def* minimize

created test/mk_slim_check_test.lean

modified test/slim_check.lean



## [2020-10-03 15:26:49](https://github.com/leanprover-community/mathlib/commit/c39170e)
doc(*): add a few short module docstrings ([#4370](https://github.com/leanprover-community/mathlib/pull/4370))
#### Estimated changes
modified src/algebra/opposites.lean

modified src/data/equiv/basic.lean

modified src/data/opposite.lean



## [2020-10-03 10:25:54](https://github.com/leanprover-community/mathlib/commit/946ab02)
chore(.github/workflows): github action for crossing off PR dependencies ([#4367](https://github.com/leanprover-community/mathlib/pull/4367))
#### Estimated changes
modified .github/PULL_REQUEST_TEMPLATE.md

created .github/workflows/sync_closed_tasks.yaml



## [2020-10-03 05:00:16](https://github.com/leanprover-community/mathlib/commit/069952b)
chore(category_theory/limits/binary_products): weaken assumptions ([#4373](https://github.com/leanprover-community/mathlib/pull/4373))
weakens the assumptions on which limits need to exist for these constructions
not much of a change but the assumptions I used were too strong so just a small fix
#### Estimated changes
modified src/category_theory/limits/shapes/constructions/preserve_binary_products.lean
- \+/\- *def* alternative_cone
- \+/\- *def* alternative_cone_is_limit
- \+/\- *def* alternative_cone
- \+/\- *def* alternative_cone_is_limit



## [2020-10-03 05:00:15](https://github.com/leanprover-community/mathlib/commit/9e455c1)
feat(data/monoid_algebra): Allow R ≠ k in semimodule R (monoid_algebra k G) ([#4365](https://github.com/leanprover-community/mathlib/pull/4365))
Also does the same for the additive version `semimodule R (add_monoid_algebra k G)`.
#### Estimated changes
modified src/algebra/monoid_algebra.lean
- \+/\- *lemma* coe_algebra_map
- \+ *lemma* single_algebra_map_eq_algebra_map_mul_of
- \+/\- *lemma* lift_apply
- \+/\- *lemma* lift_symm_apply
- \+/\- *lemma* lift_of
- \+/\- *lemma* lift_single
- \+/\- *lemma* lift_unique'
- \+/\- *lemma* lift_unique
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* coe_algebra_map
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* alg_hom_ext_iff
- \+/\- *lemma* coe_algebra_map
- \+/\- *lemma* lift_apply
- \+/\- *lemma* lift_symm_apply
- \+/\- *lemma* lift_of
- \+/\- *lemma* lift_single
- \+/\- *lemma* lift_unique'
- \+/\- *lemma* lift_unique
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* coe_algebra_map
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* alg_hom_ext_iff
- \+/\- *def* lift
- \+/\- *def* algebra_map'
- \+/\- *def* lift
- \+/\- *def* lift
- \+/\- *def* algebra_map'
- \+/\- *def* lift



## [2020-10-03 04:08:49](https://github.com/leanprover-community/mathlib/commit/6ab3eb7)
chore(category_theory/limits/equalizers): some equalizer fixups ([#4372](https://github.com/leanprover-community/mathlib/pull/4372))
A couple of minor changes for equalizers:
- Add some `simps` attributes
- Removes some redundant brackets
- Simplify the construction of an iso between cones (+dual)
- Show the equalizer fork is a limit (+dual)
#### Estimated changes
modified src/category_theory/limits/shapes/equalizers.lean
- \+/\- *lemma* fork.condition
- \+/\- *lemma* cofork.condition
- \+/\- *lemma* fork.condition
- \+/\- *lemma* cofork.condition
- \+/\- *def* fork.ext
- \+/\- *def* cofork.mk_hom
- \+/\- *def* cofork.ext
- \+ *def* equalizer_is_equalizer
- \+ *def* coequalizer_is_coequalizer
- \+/\- *def* fork.ext
- \+/\- *def* cofork.ext
- \+/\- *def* cofork.mk_hom



## [2020-10-03 01:06:52](https://github.com/leanprover-community/mathlib/commit/6a52400)
chore(scripts): update nolints.txt ([#4371](https://github.com/leanprover-community/mathlib/pull/4371))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-10-02 20:49:45](https://github.com/leanprover-community/mathlib/commit/da24add)
feat(data/multiset): ordered sum lemmas ([#4305](https://github.com/leanprover-community/mathlib/pull/4305))
Add some lemmas about products in ordered monoids and sums in ordered add monoids, and a multiset count filter lemma (and a rename of a count filter lemma)
#### Estimated changes
modified src/data/list/basic.lean
- \+ *lemma* one_le_prod_of_one_le
- \+ *lemma* single_le_prod
- \+ *lemma* all_one_of_le_one_le_of_prod_eq_one
- \+ *lemma* sum_eq_zero_iff

modified src/data/multiset/basic.lean
- \+ *lemma* one_le_prod_of_one_le
- \+ *lemma* single_le_prod
- \+ *lemma* all_one_of_le_one_le_of_prod_eq_one
- \+ *lemma* sum_eq_zero_iff
- \+ *theorem* count_filter_of_pos
- \+ *theorem* count_filter_of_neg
- \- *theorem* count_filter



## [2020-10-02 18:01:52](https://github.com/leanprover-community/mathlib/commit/2634c1b)
feat(category_theory/cones): map_cone_inv as an equivalence ([#4253](https://github.com/leanprover-community/mathlib/pull/4253))
When `G` is an equivalence, we have `G.map_cone_inv : cone (F ⋙ G) → cone F`, and that this is an inverse to `G.map_cone`, but not quite that these constitute an equivalence of categories. This PR fixes that.
#### Estimated changes
modified src/category_theory/equivalence.lean
- \+ *lemma* counit_inv_app_functor
- \+ *lemma* counit_app_functor
- \+ *lemma* unit_app_inverse
- \+ *lemma* unit_inv_app_inverse
- \- *lemma* functor_unit
- \- *lemma* counit_functor
- \- *lemma* unit_inverse
- \- *lemma* inverse_counit

modified src/category_theory/limits/cones.lean
- \+ *def* functoriality_equivalence
- \+ *def* functoriality_equivalence
- \+/\- *def* map_cone_inv
- \+ *def* map_cocone_inv
- \+ *def* map_cocone_map_cocone_inv
- \+ *def* map_cocone_inv_map_cocone
- \+/\- *def* map_cone_inv

modified src/category_theory/limits/limits.lean

modified src/category_theory/monoidal/transport.lean



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
modified src/data/int/parity.lean
- \+ *lemma* odd_def
- \+ *def* odd

modified src/data/nat/parity.lean
- \+ *lemma* odd_def
- \+ *def* odd



## [2020-10-02 12:12:21](https://github.com/leanprover-community/mathlib/commit/53570c0)
chore(README): add zulip badge ([#4362](https://github.com/leanprover-community/mathlib/pull/4362))
#### Estimated changes
modified README.md



## [2020-10-02 10:14:33](https://github.com/leanprover-community/mathlib/commit/eeb9bb6)
feat(data/polynomial/coeff): single-variate `C_dvd_iff_dvd_coeff` ([#4355](https://github.com/leanprover-community/mathlib/pull/4355))
Adds a single-variate version of the lemma `mv_polynomial.C_dvd_iff_dvd_coeff`
(Useful for Gauss's Lemma)
#### Estimated changes
modified src/data/polynomial/coeff.lean
- \+ *lemma* C_dvd_iff_dvd_coeff



## [2020-10-02 10:14:31](https://github.com/leanprover-community/mathlib/commit/8876ba2)
feat(ring_theory/roots_of_unity): (primitive) roots of unity ([#4260](https://github.com/leanprover-community/mathlib/pull/4260))
#### Estimated changes
created src/ring_theory/roots_of_unity.lean
- \+ *lemma* mem_roots_of_unity
- \+ *lemma* roots_of_unity_le_of_dvd
- \+ *lemma* map_roots_of_unity
- \+ *lemma* mem_roots_of_unity_iff_mem_nth_roots
- \+ *lemma* roots_of_unity_equiv_nth_roots_apply
- \+ *lemma* roots_of_unity_equiv_nth_roots_symm_apply
- \+ *lemma* card_roots_of_unity
- \+ *lemma* mem_primitive_roots
- \+ *lemma* iff_def
- \+ *lemma* mk_of_lt
- \+ *lemma* pow_eq_one_iff_dvd
- \+ *lemma* is_unit
- \+ *lemma* pow_ne_one_of_pos_of_lt
- \+ *lemma* pow_inj
- \+ *lemma* one
- \+ *lemma* one_right_iff
- \+ *lemma* coe_units_iff
- \+ *lemma* pow_of_coprime
- \+ *lemma* pow_iff_coprime
- \+ *lemma* gpow_eq_one
- \+ *lemma* gpow_eq_one_iff_dvd
- \+ *lemma* inv
- \+ *lemma* inv_iff
- \+ *lemma* gpow_of_gcd_eq_one
- \+ *lemma* coe_subgroup_iff
- \+ *lemma* fpow_eq_one
- \+ *lemma* fpow_eq_one_iff_dvd
- \+ *lemma* inv'
- \+ *lemma* inv_iff'
- \+ *lemma* fpow_of_gcd_eq_one
- \+ *lemma* neg_one
- \+ *lemma* eq_neg_one_of_two_right
- \+ *lemma* mem_roots_of_unity
- \+ *lemma* zmod_equiv_gpowers_apply_coe_int
- \+ *lemma* zmod_equiv_gpowers_apply_coe_nat
- \+ *lemma* zmod_equiv_gpowers_symm_apply_gpow
- \+ *lemma* zmod_equiv_gpowers_symm_apply_gpow'
- \+ *lemma* zmod_equiv_gpowers_symm_apply_pow
- \+ *lemma* zmod_equiv_gpowers_symm_apply_pow'
- \+ *lemma* gpowers_eq
- \+ *lemma* eq_pow_of_mem_roots_of_unity
- \+ *lemma* eq_pow_of_pow_eq_one
- \+ *lemma* is_primitive_root_iff'
- \+ *lemma* is_primitive_root_iff
- \+ *lemma* card_roots_of_unity'
- \+ *lemma* card_roots_of_unity
- \+ *lemma* card_primitive_roots
- \+ *def* roots_of_unity
- \+ *def* roots_of_unity_equiv_nth_roots
- \+ *def* primitive_roots
- \+ *def* zmod_equiv_gpowers



## [2020-10-02 08:35:04](https://github.com/leanprover-community/mathlib/commit/d631126)
chore(algebra): move algebra and monoid algebra to algebra/ ([#4298](https://github.com/leanprover-community/mathlib/pull/4298))
On the basis that all the basic definitions of algebraic gadgets are otherwise in `src/algebra/`, I'd like to move `ring_theory/algebra.lean`, `ring_theory/algebra_operations.lean`, and `data/monoid_algebra.lean` there too.
#### Estimated changes
renamed src/ring_theory/algebra.lean to src/algebra/algebra/basic.lean

renamed src/ring_theory/algebra_operations.lean to src/algebra/algebra/operations.lean

modified src/algebra/category/Algebra/basic.lean

modified src/algebra/free_algebra.lean

modified src/algebra/lie/basic.lean

renamed src/data/monoid_algebra.lean to src/algebra/monoid_algebra.lean

modified src/algebra/ring_quot.lean

modified src/data/complex/module.lean

modified src/data/equiv/transfer_instance.lean

modified src/data/polynomial/basic.lean

modified src/linear_algebra/determinant.lean

modified src/linear_algebra/finsupp.lean

modified src/representation_theory/maschke.lean

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/tensor_product.lean

modified src/topology/algebra/module.lean



## [2020-10-02 07:19:29](https://github.com/leanprover-community/mathlib/commit/1f91d93)
chore(ring_theory/power_series): rename variables ([#4361](https://github.com/leanprover-community/mathlib/pull/4361))
Use `R`, `S`, `T` for (semi)rings and `k` for a field.
#### Estimated changes
modified src/ring_theory/power_series.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coeff_monomial
- \+/\- *lemma* coeff_monomial'
- \+/\- *lemma* coeff_zero
- \+/\- *lemma* coeff_zero_one
- \+/\- *lemma* coeff_mul
- \+/\- *lemma* monomial_mul_monomial
- \+/\- *lemma* monomial_zero_eq_C
- \+/\- *lemma* monomial_zero_eq_C_apply
- \+/\- *lemma* coeff_C
- \+/\- *lemma* coeff_zero_C
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* X_def
- \+/\- *lemma* coeff_mul_C
- \+/\- *lemma* coeff_C_mul
- \+/\- *lemma* coeff_zero_mul_X
- \+/\- *lemma* coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* constant_coeff_C
- \+/\- *lemma* constant_coeff_zero
- \+/\- *lemma* constant_coeff_one
- \+/\- *lemma* constant_coeff_X
- \+/\- *lemma* is_unit_constant_coeff
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* X_inj
- \+/\- *lemma* map_id
- \+/\- *lemma* coeff_map
- \+/\- *lemma* constant_coeff_map
- \+/\- *lemma* coeff_trunc
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \+/\- *lemma* X_pow_dvd_iff
- \+/\- *lemma* X_dvd_iff
- \+/\- *lemma* coeff_inv_aux
- \+/\- *lemma* coeff_inv_of_unit
- \+/\- *lemma* constant_coeff_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+/\- *lemma* coeff_inv
- \+/\- *lemma* constant_coeff_inv
- \+/\- *lemma* inv_eq_zero
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq'
- \+/\- *lemma* coeff_coe
- \+/\- *lemma* coe_monomial
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_C
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coeff_mk
- \+/\- *lemma* coeff_monomial
- \+/\- *lemma* monomial_eq_mk
- \+/\- *lemma* coeff_monomial'
- \+/\- *lemma* coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* monomial_zero_eq_C
- \+/\- *lemma* monomial_zero_eq_C_apply
- \+/\- *lemma* coeff_C
- \+/\- *lemma* coeff_zero_C
- \+/\- *lemma* X_eq
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* coeff_one_X
- \+/\- *lemma* X_pow_eq
- \+/\- *lemma* coeff_zero_one
- \+/\- *lemma* coeff_mul
- \+/\- *lemma* coeff_mul_C
- \+/\- *lemma* coeff_C_mul
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* coeff_succ_mul_X
- \+/\- *lemma* constant_coeff_C
- \+/\- *lemma* constant_coeff_zero
- \+/\- *lemma* constant_coeff_one
- \+/\- *lemma* constant_coeff_X
- \+/\- *lemma* coeff_zero_mul_X
- \+/\- *lemma* is_unit_constant_coeff
- \+/\- *lemma* map_id
- \+/\- *lemma* coeff_map
- \+/\- *lemma* X_pow_dvd_iff
- \+/\- *lemma* X_dvd_iff
- \+/\- *lemma* coeff_trunc
- \+/\- *lemma* trunc_zero
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \+/\- *lemma* trunc_add
- \+/\- *lemma* coeff_inv_aux
- \+/\- *lemma* coeff_inv_of_unit
- \+/\- *lemma* constant_coeff_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+/\- *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+/\- *lemma* span_X_is_prime
- \+/\- *lemma* X_prime
- \+/\- *lemma* inv_eq_inv_aux
- \+/\- *lemma* coeff_inv
- \+/\- *lemma* constant_coeff_inv
- \+/\- *lemma* inv_eq_zero
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq'
- \+/\- *lemma* order_finite_of_coeff_ne_zero
- \+/\- *lemma* coeff_order
- \+/\- *lemma* order_le
- \+/\- *lemma* coeff_of_lt_order
- \+/\- *lemma* order_eq_top
- \+/\- *lemma* order_zero
- \+/\- *lemma* nat_le_order
- \+/\- *lemma* le_order
- \+/\- *lemma* order_eq_nat
- \+/\- *lemma* order_eq
- \+/\- *lemma* le_order_add
- \+/\- *lemma* order_add_of_order_eq
- \+/\- *lemma* order_mul_ge
- \+/\- *lemma* order_monomial
- \+/\- *lemma* order_monomial_of_ne_zero
- \+/\- *lemma* order_one
- \+/\- *lemma* order_X
- \+/\- *lemma* order_X_pow
- \+/\- *lemma* order_mul
- \+/\- *lemma* coeff_coe
- \+/\- *lemma* coe_monomial
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_C
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coeff_monomial
- \+/\- *lemma* coeff_monomial'
- \+/\- *lemma* coeff_zero
- \+/\- *lemma* coeff_zero_one
- \+/\- *lemma* coeff_mul
- \+/\- *lemma* monomial_mul_monomial
- \+/\- *lemma* monomial_zero_eq_C
- \+/\- *lemma* monomial_zero_eq_C_apply
- \+/\- *lemma* coeff_C
- \+/\- *lemma* coeff_zero_C
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* X_def
- \+/\- *lemma* coeff_mul_C
- \+/\- *lemma* coeff_C_mul
- \+/\- *lemma* coeff_zero_mul_X
- \+/\- *lemma* coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* constant_coeff_C
- \+/\- *lemma* constant_coeff_zero
- \+/\- *lemma* constant_coeff_one
- \+/\- *lemma* constant_coeff_X
- \+/\- *lemma* is_unit_constant_coeff
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* X_inj
- \+/\- *lemma* map_id
- \+/\- *lemma* coeff_map
- \+/\- *lemma* constant_coeff_map
- \+/\- *lemma* coeff_trunc
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \+/\- *lemma* X_pow_dvd_iff
- \+/\- *lemma* X_dvd_iff
- \+/\- *lemma* coeff_inv_aux
- \+/\- *lemma* coeff_inv_of_unit
- \+/\- *lemma* constant_coeff_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+/\- *lemma* coeff_inv
- \+/\- *lemma* constant_coeff_inv
- \+/\- *lemma* inv_eq_zero
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq'
- \+/\- *lemma* coeff_coe
- \+/\- *lemma* coe_monomial
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_C
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coeff_mk
- \+/\- *lemma* coeff_monomial
- \+/\- *lemma* monomial_eq_mk
- \+/\- *lemma* coeff_monomial'
- \+/\- *lemma* coeff_zero_eq_constant_coeff_apply
- \+/\- *lemma* monomial_zero_eq_C
- \+/\- *lemma* monomial_zero_eq_C_apply
- \+/\- *lemma* coeff_C
- \+/\- *lemma* coeff_zero_C
- \+/\- *lemma* X_eq
- \+/\- *lemma* coeff_zero_X
- \+/\- *lemma* coeff_one_X
- \+/\- *lemma* X_pow_eq
- \+/\- *lemma* coeff_zero_one
- \+/\- *lemma* coeff_mul
- \+/\- *lemma* coeff_mul_C
- \+/\- *lemma* coeff_C_mul
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* coeff_succ_mul_X
- \+/\- *lemma* constant_coeff_C
- \+/\- *lemma* constant_coeff_zero
- \+/\- *lemma* constant_coeff_one
- \+/\- *lemma* constant_coeff_X
- \+/\- *lemma* coeff_zero_mul_X
- \+/\- *lemma* is_unit_constant_coeff
- \+/\- *lemma* map_id
- \+/\- *lemma* coeff_map
- \+/\- *lemma* X_pow_dvd_iff
- \+/\- *lemma* X_dvd_iff
- \+/\- *lemma* coeff_trunc
- \+/\- *lemma* trunc_zero
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \+/\- *lemma* trunc_add
- \+/\- *lemma* coeff_inv_aux
- \+/\- *lemma* coeff_inv_of_unit
- \+/\- *lemma* constant_coeff_inv_of_unit
- \+/\- *lemma* mul_inv_of_unit
- \+/\- *lemma* eq_zero_or_eq_zero_of_mul_eq_zero
- \+/\- *lemma* span_X_is_prime
- \+/\- *lemma* X_prime
- \+/\- *lemma* inv_eq_inv_aux
- \+/\- *lemma* coeff_inv
- \+/\- *lemma* constant_coeff_inv
- \+/\- *lemma* inv_eq_zero
- \+/\- *lemma* inv_of_unit_eq
- \+/\- *lemma* inv_of_unit_eq'
- \+/\- *lemma* order_finite_of_coeff_ne_zero
- \+/\- *lemma* coeff_order
- \+/\- *lemma* order_le
- \+/\- *lemma* coeff_of_lt_order
- \+/\- *lemma* order_eq_top
- \+/\- *lemma* order_zero
- \+/\- *lemma* nat_le_order
- \+/\- *lemma* le_order
- \+/\- *lemma* order_eq_nat
- \+/\- *lemma* order_eq
- \+/\- *lemma* le_order_add
- \+/\- *lemma* order_add_of_order_eq
- \+/\- *lemma* order_mul_ge
- \+/\- *lemma* order_monomial
- \+/\- *lemma* order_monomial_of_ne_zero
- \+/\- *lemma* order_one
- \+/\- *lemma* order_X
- \+/\- *lemma* order_X_pow
- \+/\- *lemma* order_mul
- \+/\- *lemma* coeff_coe
- \+/\- *lemma* coe_monomial
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_C
- \+/\- *def* mv_power_series
- \+/\- *def* monomial
- \+/\- *def* coeff
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* constant_coeff
- \+/\- *def* map
- \+/\- *def* trunc_fun
- \+/\- *def* trunc
- \+/\- *def* inv_of_unit
- \+/\- *def* coe_to_mv_power_series.ring_hom
- \+/\- *def* power_series
- \+/\- *def* coeff
- \+/\- *def* monomial
- \+/\- *def* mk
- \+/\- *def* constant_coeff
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* map
- \+/\- *def* trunc
- \+/\- *def* inv_of_unit
- \+/\- *def* order
- \+/\- *def* coe_to_power_series.ring_hom
- \+/\- *def* mv_power_series
- \+/\- *def* monomial
- \+/\- *def* coeff
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* constant_coeff
- \+/\- *def* map
- \+/\- *def* trunc_fun
- \+/\- *def* trunc
- \+/\- *def* inv_of_unit
- \+/\- *def* coe_to_mv_power_series.ring_hom
- \+/\- *def* power_series
- \+/\- *def* coeff
- \+/\- *def* monomial
- \+/\- *def* mk
- \+/\- *def* constant_coeff
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* map
- \+/\- *def* trunc
- \+/\- *def* inv_of_unit
- \+/\- *def* order
- \+/\- *def* coe_to_power_series.ring_hom



## [2020-10-02 05:57:43](https://github.com/leanprover-community/mathlib/commit/140db10)
chore(data/monoid_algebra): Make the style in `lift` consistent ([#4347](https://github.com/leanprover-community/mathlib/pull/4347))
This continues from a06c87ed28989d062aa3d5324e880e62edf4a2f8, which changed add_monoid_algebra.lift but not monoid_algebra.lift.
Note only the additive proof needs `erw` (to unfold `multiplicative`).
#### Estimated changes
modified src/data/monoid_algebra.lean



## [2020-10-02 01:04:21](https://github.com/leanprover-community/mathlib/commit/d41f386)
chore(scripts): update nolints.txt ([#4358](https://github.com/leanprover-community/mathlib/pull/4358))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt



## [2020-10-01 20:40:02](https://github.com/leanprover-community/mathlib/commit/4ef680b)
feat(group_theory): subgroups of real numbers ([#4334](https://github.com/leanprover-community/mathlib/pull/4334))
This fills the last hole in the "Topology of R" section of our undergrad curriculum: additive subgroups of real numbers are either dense or cyclic. Most of this PR is supporting material about ordered abelian groups. 
Co-Authored-By: Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>
#### Estimated changes
modified docs/undergrad.yaml

modified src/algebra/archimedean.lean
- \+ *lemma* exists_int_smul_near_of_pos
- \+ *lemma* exists_int_smul_near_of_pos'

modified src/algebra/group_power/basic.lean
- \+ *lemma* nsmul_pos
- \+/\- *theorem* nsmul_nonneg
- \+ *theorem* gsmul_nonneg
- \+ *theorem* nsmul_lt_nsmul
- \+/\- *theorem* nsmul_nonneg

modified src/algebra/group_power/lemmas.lean
- \+ *lemma* gsmul_pos
- \+ *theorem* gsmul_le_gsmul
- \+ *theorem* gsmul_lt_gsmul
- \+ *theorem* gsmul_le_gsmul_iff
- \+ *theorem* gsmul_lt_gsmul_iff
- \+ *theorem* nsmul_le_nsmul_iff
- \+ *theorem* nsmul_lt_nsmul_iff

created src/group_theory/archimedean.lean
- \+ *lemma* add_subgroup.cyclic_of_min
- \+ *lemma* int.subgroup_cyclic

modified src/group_theory/subgroup.lean
- \+ *lemma* eq_bot_iff_forall
- \+ *lemma* nontrivial_iff_exists_ne_one
- \+ *lemma* bot_or_nontrivial
- \+ *lemma* bot_or_exists_ne_one
- \+ *lemma* closure_singleton_one
- \+ *lemma* closure_singleton_zero

modified src/group_theory/submonoid/membership.lean
- \+ *lemma* closure_singleton_one
- \+ *lemma* closure_singleton_zero

modified src/group_theory/submonoid/operations.lean
- \+ *lemma* eq_bot_iff_forall
- \+ *lemma* nontrivial_iff_exists_ne_one
- \+ *lemma* bot_or_nontrivial
- \+ *lemma* bot_or_exists_ne_one

modified src/order/bounds.lean
- \+ *lemma* is_glb.exists_between_self_add
- \+ *lemma* is_glb.exists_between_self_add'
- \+ *lemma* is_lub.exists_between_sub_self
- \+ *lemma* is_lub.exists_between_sub_self'

modified src/ring_theory/subring.lean
- \+ *lemma* add_subgroup.int_mul_mem

modified src/topology/instances/real.lean
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
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_mk

modified src/analysis/asymptotics.lean

modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* nnnorm_one
- \+/\- *lemma* norm_mul_le
- \+ *lemma* list.norm_prod_le'
- \+ *lemma* list.norm_prod_le
- \+ *lemma* finset.norm_prod_le'
- \+ *lemma* finset.norm_prod_le
- \+ *lemma* norm_pow_le'
- \+/\- *lemma* norm_pow_le
- \+/\- *lemma* eventually_norm_pow_le
- \+/\- *lemma* units.norm_pos
- \+/\- *lemma* mul_left_bound
- \+/\- *lemma* mul_right_bound
- \+ *lemma* normed_algebra.norm_one_class
- \+ *lemma* normed_algebra.nontrivial
- \+/\- *lemma* norm_mul_le
- \+/\- *lemma* norm_pow_le
- \+/\- *lemma* eventually_norm_pow_le
- \+/\- *lemma* units.norm_pos
- \+/\- *lemma* mul_left_bound
- \+/\- *lemma* mul_right_bound
- \- *lemma* norm_one
- \+/\- *lemma* nnnorm_one
- \- *lemma* normed_algebra.to_nonzero

modified src/analysis/normed_space/units.lean

modified src/analysis/specific_limits.lean

modified src/data/finset/basic.lean
- \+ *lemma* nonempty_mk_coe
- \+ *theorem* not_nonempty_empty
- \+ *theorem* mk_zero
- \+ *theorem* mk_cons
- \+ *theorem* nonempty_cons

modified src/data/padics/padic_integers.lean
- \+/\- *lemma* norm_def
- \+/\- *lemma* norm_def
- \- *lemma* norm_one



## [2020-10-01 17:37:36](https://github.com/leanprover-community/mathlib/commit/d5834ee)
feat(data/real/irrational): add a lemma to deduce nat_degree from irrational root ([#4349](https://github.com/leanprover-community/mathlib/pull/4349))
This PR is splitted from [#4301](https://github.com/leanprover-community/mathlib/pull/4301) .
#### Estimated changes
modified src/data/real/irrational.lean
- \+ *lemma* nat_degree_gt_one_of_irrational_root



## [2020-10-01 17:37:34](https://github.com/leanprover-community/mathlib/commit/ddaa325)
feat(archive/imo): formalize IMO 1969 problem 1 ([#4261](https://github.com/leanprover-community/mathlib/pull/4261))
This is a formalization of the problem and solution for the first problem on the 1969 IMO:
Prove that there are infinitely many natural numbers $a$ with the following property: the number $z = n^4 + a$ is not prime for any natural number $n$
#### Estimated changes
created archive/imo/imo1969_q1.lean
- \+ *lemma* factorization
- \+ *lemma* left_factor_large
- \+ *lemma* right_factor_large
- \+ *lemma* int_large
- \+ *lemma* int_not_prime
- \+ *lemma* polynomial_not_prime
- \+ *theorem* imo1969_q1



## [2020-10-01 16:43:25](https://github.com/leanprover-community/mathlib/commit/7767ef8)
feat(number_theory/divisors): defines the finsets of divisors/proper divisors, perfect numbers, etc. ([#4310](https://github.com/leanprover-community/mathlib/pull/4310))
Defines `nat.divisors n` to be the set of divisors of `n`, and `nat.proper_divisors` to be the set of divisors of `n` other than `n`.
Defines `nat.divisors_antidiagonal` in analogy to other `antidiagonal`s used to define convolutions
Defines `nat.perfect`, the predicate for perfect numbers
#### Estimated changes
created src/number_theory/divisors.lean
- \+ *lemma* proper_divisors.not_self_mem
- \+ *lemma* mem_proper_divisors
- \+ *lemma* divisors_eq_proper_divisors_insert_self
- \+ *lemma* mem_divisors
- \+ *lemma* mem_divisors_antidiagonal
- \+ *lemma* divisor_le
- \+ *lemma* divisors_zero
- \+ *lemma* proper_divisors_zero
- \+ *lemma* divisors_antidiagonal_zero
- \+ *lemma* divisors_antidiagonal_one
- \+ *lemma* swap_mem_divisors_antidiagonal
- \+ *lemma* fst_mem_divisors_of_mem_antidiagonal
- \+ *lemma* snd_mem_divisors_of_mem_antidiagonal
- \+ *lemma* map_swap_divisors_antidiagonal
- \+ *lemma* sum_divisors_eq_sum_proper_divisors_add_self
- \+ *theorem* perfect_iff_sum_proper_divisors
- \+ *theorem* perfect_iff_sum_divisors_eq_two_mul
- \+ *def* divisors
- \+ *def* proper_divisors
- \+ *def* divisors_antidiagonal
- \+ *def* perfect



## [2020-10-01 14:28:11](https://github.com/leanprover-community/mathlib/commit/f10dda0)
feat(data/nat/basic): simp-lemmas for bit0 and bit1 mod two ([#4343](https://github.com/leanprover-community/mathlib/pull/4343))
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* bit0_mod_two
- \+ *lemma* bit1_mod_two



## [2020-10-01 14:28:07](https://github.com/leanprover-community/mathlib/commit/0fc7b29)
feat(data/mv_polynomial): stub on invertible elements ([#4320](https://github.com/leanprover-community/mathlib/pull/4320))
More from the Witt vector branch.
#### Estimated changes
created src/data/mv_polynomial/invertible.lean

modified src/ring_theory/algebra_tower.lean
- \+ *def* invertible.algebra_tower
- \+ *def* invertible_algebra_coe_nat



## [2020-10-01 14:28:01](https://github.com/leanprover-community/mathlib/commit/3d58fce)
feat(linear_algebra): determinant of `matrix.block_diagonal` ([#4300](https://github.com/leanprover-community/mathlib/pull/4300))
This PR shows the determinant of `matrix.block_diagonal` is the product of the determinant of each subblock.
The only contributing permutations in the expansion of the determinant are those which map each block to the same block. Each of those permutations has the form `equiv.prod_congr_left σ`. Using `equiv.perm.extend` and `equiv.prod_congr_right`, we can compute the sign of `equiv.prod_congr_left σ`, and with a bit of algebraic manipulation we reach the conclusion.
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_to_finset
- \+ *lemma* nat.coe_prod
- \+ *lemma* int.coe_prod
- \+ *lemma* units.coe_prod

modified src/data/equiv/basic.lean
- \+ *lemma* prod_congr_left_apply
- \+ *lemma* prod_congr_refl_right
- \+ *lemma* prod_congr_right_apply
- \+ *lemma* prod_congr_refl_left
- \+ *lemma* prod_congr_left_trans_prod_comm
- \+ *lemma* prod_congr_right_trans_prod_comm
- \+ *lemma* sigma_congr_right_sigma_equiv_prod
- \+ *lemma* sigma_equiv_prod_sigma_congr_right
- \+ *lemma* prod_extend_right_apply_eq
- \+ *lemma* prod_extend_right_apply_ne
- \+ *lemma* eq_of_prod_extend_right_ne
- \+ *lemma* fst_prod_extend_right
- \+ *def* prod_congr_left
- \+ *def* prod_congr_right
- \+ *def* prod_extend_right

modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_pi_univ

modified src/group_theory/perm/sign.lean
- \+/\- *lemma* is_cycle_swap
- \+/\- *lemma* is_cycle_swap_mul_aux₁
- \+/\- *lemma* is_cycle_swap_mul_aux₂
- \+/\- *lemma* eq_swap_of_is_cycle_of_apply_apply_eq_self
- \+/\- *lemma* is_cycle_swap_mul
- \+/\- *lemma* support_swap
- \+/\- *lemma* card_support_swap
- \+/\- *lemma* sign_cycle
- \+ *lemma* prod_prod_extend_right
- \+ *lemma* sign_prod_extend_right
- \+ *lemma* sign_prod_congr_right
- \+ *lemma* sign_prod_congr_left
- \+/\- *lemma* is_cycle_swap
- \+/\- *lemma* is_cycle_swap_mul_aux₁
- \+/\- *lemma* is_cycle_swap_mul_aux₂
- \+/\- *lemma* eq_swap_of_is_cycle_of_apply_apply_eq_self
- \+/\- *lemma* is_cycle_swap_mul
- \+/\- *lemma* support_swap
- \+/\- *lemma* card_support_swap
- \+/\- *lemma* sign_cycle

modified src/linear_algebra/determinant.lean
- \+ *lemma* det_block_diagonal



## [2020-10-01 14:27:59](https://github.com/leanprover-community/mathlib/commit/13e9cc4)
feat(linear_algebra/exterior_algebra): Add an exterior algebra ([#4297](https://github.com/leanprover-community/mathlib/pull/4297))
This adds the basic exterior algebra definitions using a very similar approach to `universal_enveloping_algebra`.
It's based off the `exterior_algebra` branch, dropping the `wedge` stuff for now as development in multilinear maps is happening elsewhere.
#### Estimated changes
created src/linear_algebra/exterior_algebra.lean
- \+ *theorem* ι_square_zero
- \+ *theorem* ι_comp_lift
- \+ *theorem* lift_ι_apply
- \+ *theorem* lift_unique
- \+ *theorem* comp_ι_square_zero
- \+ *theorem* lift_comp_ι
- \+ *theorem* hom_ext
- \+ *def* exterior_algebra
- \+ *def* ι
- \+ *def* lift



## [2020-10-01 14:27:57](https://github.com/leanprover-community/mathlib/commit/268073a)
feat(geometry/manifold): derivative of the zero section of the tangent bundle ([#4292](https://github.com/leanprover-community/mathlib/pull/4292))
We show that the zero section of the tangent bundle to a smooth manifold is smooth, and compute its derivative.
Along the way, some streamlining of supporting material.
#### Estimated changes
modified src/analysis/calculus/fderiv.lean
- \+ *lemma* fderiv_within_eq_fderiv
- \+/\- *lemma* fderiv_id'
- \+/\- *lemma* fderiv_const
- \+/\- *lemma* fderiv_id'
- \+/\- *lemma* fderiv_const

modified src/geometry/manifold/basic_smooth_bundle.lean

modified src/geometry/manifold/mfderiv.lean

modified src/geometry/manifold/times_cont_mdiff.lean
- \+ *lemma* smooth.mdifferentiable
- \+ *lemma* smooth.mdifferentiable_at
- \+ *lemma* smooth.mdifferentiable_within_at
- \+ *lemma* smooth_const_section
- \+ *lemma* smooth_zero_section
- \+ *lemma* tangent_map_tangent_bundle_pure
- \+ *def* zero_section

modified src/topology/topological_fiber_bundle.lean
- \+ *lemma* local_triv'_apply
- \+ *lemma* local_triv'_symm_apply
- \+ *lemma* local_triv_apply
- \+/\- *lemma* mem_local_triv_at_source
- \+ *lemma* continuous_const_section
- \- *lemma* local_triv'_fst
- \- *lemma* local_triv'_inv_fst
- \- *lemma* local_triv_fst
- \+/\- *lemma* mem_local_triv_at_source



## [2020-10-01 14:27:55](https://github.com/leanprover-community/mathlib/commit/11cdc8c)
feat(data/polynomial/*) : as_sum_support  ([#4286](https://github.com/leanprover-community/mathlib/pull/4286))
#### Estimated changes
modified src/data/polynomial/algebra_map.lean

modified src/data/polynomial/degree/basic.lean
- \+ *lemma* as_sum_range
- \+ *lemma* as_sum_support
- \- *lemma* as_sum

modified src/data/polynomial/eval.lean
- \+ *lemma* eval_finset_sum

modified src/data/polynomial/monic.lean



## [2020-10-01 12:28:37](https://github.com/leanprover-community/mathlib/commit/0ccc157)
feat(data/nat/fact, analysis/specific_limits): rename nat.fact, add few lemmas about its behaviour along at_top ([#4309](https://github.com/leanprover-community/mathlib/pull/4309))
Main content : 
- Rename `nat.fact` to `nat.factorial`, and add notation `n!` in locale `factorial`. This fixes [#2786](https://github.com/leanprover-community/mathlib/pull/2786)
- Generalize `prod_inv_distrib` to `comm_group_with_zero` *without any nonzero assumptions*
- `factorial_tendsto_at_top` : n! --> infinity as n--> infinity
- `tendsto_factorial_div_pow_self_at_top` : n!/(n^n) --> 0 as n --> infinity
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* pow_eq_prod_const
- \+ *lemma* prod_inv_distrib'

modified src/algebra/big_operators/intervals.lean
- \+ *lemma* prod_Ico_id_eq_factorial
- \+ *lemma* prod_range_add_one_eq_factorial
- \- *lemma* prod_Ico_id_eq_fact

modified src/algebra/big_operators/order.lean
- \+ *lemma* prod_le_one

modified src/analysis/specific_limits.lean
- \+ *lemma* factorial_tendsto_at_top
- \+ *lemma* tendsto_factorial_div_pow_self_at_top

modified src/data/complex/exponential.lean
- \+ *lemma* sum_div_factorial_le
- \- *lemma* sum_div_fact_le

modified src/data/fintype/basic.lean
- \+/\- *lemma* length_perms_of_list
- \+/\- *lemma* fintype.card_perm
- \+/\- *lemma* length_perms_of_list
- \+/\- *lemma* fintype.card_perm

modified src/data/list/perm.lean
- \+/\- *theorem* length_permutations
- \+/\- *theorem* length_permutations

modified src/data/nat/choose/basic.lean
- \+ *lemma* choose_mul_factorial_mul_factorial
- \- *lemma* choose_mul_fact_mul_fact
- \+ *theorem* choose_eq_factorial_div_factorial
- \+ *theorem* factorial_mul_factorial_dvd_factorial
- \- *theorem* choose_eq_fact_div_fact
- \- *theorem* fact_mul_fact_dvd_fact

modified src/data/nat/choose/dvd.lean

deleted src/data/nat/fact.lean
- \- *lemma* fact_mul_pow_le_fact
- \- *lemma* monotone_fact
- \- *lemma* fact_lt
- \- *lemma* one_lt_fact
- \- *lemma* fact_eq_one
- \- *lemma* fact_inj
- \- *theorem* fact_zero
- \- *theorem* fact_succ
- \- *theorem* fact_one
- \- *theorem* fact_pos
- \- *theorem* fact_ne_zero
- \- *theorem* fact_dvd_fact
- \- *theorem* dvd_fact
- \- *theorem* fact_le
- \- *def* fact

created src/data/nat/factorial.lean
- \+ *lemma* factorial_mul_pow_le_factorial
- \+ *lemma* monotone_factorial
- \+ *lemma* factorial_lt
- \+ *lemma* one_lt_factorial
- \+ *lemma* factorial_eq_one
- \+ *lemma* factorial_inj
- \+ *lemma* self_le_factorial
- \+ *theorem* factorial_zero
- \+ *theorem* factorial_succ
- \+ *theorem* factorial_one
- \+ *theorem* factorial_pos
- \+ *theorem* factorial_ne_zero
- \+ *theorem* factorial_dvd_factorial
- \+ *theorem* dvd_factorial
- \+ *theorem* factorial_le
- \+ *def* factorial

modified src/data/nat/multiplicity.lean
- \+ *lemma* multiplicity_factorial
- \+ *lemma* pow_dvd_factorial_iff
- \- *lemma* multiplicity_fact
- \- *lemma* pow_dvd_fact_iff

modified src/data/nat/prime.lean
- \+ *lemma* prime.dvd_factorial
- \- *lemma* prime.dvd_fact

modified src/number_theory/primorial.lean

modified src/number_theory/quadratic_reciprocity.lean
- \+/\- *lemma* wilsons_lemma
- \+/\- *lemma* wilsons_lemma



## [2020-10-01 09:16:51](https://github.com/leanprover-community/mathlib/commit/9c241b0)
feat(*): a few more tests for `summable`, docstrings ([#4325](https://github.com/leanprover-community/mathlib/pull/4325))
### Important new theorems:
* `summable_geometric_iff_norm_lt_1`: a geometric series in a normed field is summable iff the norm of the common ratio is less than 1;
* `summable.tendsto_cofinite_zero`: divergence test: if `f` is a `summable` function, then `f x` tends to zero along `cofinite`;
### API change
* rename `cauchy_seq_of_tendsto_nhds` to `filter.tendsto.cauchy_seq` to enable dot syntax.
#### Estimated changes
modified src/analysis/specific_limits.lean
- \+ *lemma* summable_geometric_iff_norm_lt_1

modified src/order/filter/cofinite.lean
- \+ *lemma* set.finite.compl_mem_cofinite
- \+ *lemma* set.finite.eventually_cofinite_nmem
- \+ *lemma* finset.eventually_cofinite_nmem
- \+/\- *lemma* set.infinite_iff_frequently_cofinite
- \+/\- *lemma* set.infinite_iff_frequently_cofinite

modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* summable_iff_cauchy_seq_finset
- \+ *lemma* summable.vanishing
- \+ *lemma* summable.tendsto_cofinite_zero
- \+/\- *lemma* summable_iff_cauchy_seq_finset

modified src/topology/instances/ennreal.lean
- \+/\- *lemma* exists_le_has_sum_of_le
- \+/\- *lemma* summable_of_le
- \+/\- *lemma* has_sum_iff_tendsto_nat
- \+/\- *lemma* tsum_comp_le_tsum_of_inj
- \+/\- *lemma* tendsto_sum_nat_add
- \+/\- *lemma* exists_le_has_sum_of_le
- \+/\- *lemma* summable_of_le
- \+/\- *lemma* has_sum_iff_tendsto_nat
- \+/\- *lemma* tsum_comp_le_tsum_of_inj
- \+/\- *lemma* tendsto_sum_nat_add

modified src/topology/sequences.lean

modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* filter.tendsto.cauchy_map
- \+ *lemma* filter.tendsto.cauchy_seq
- \- *lemma* cauchy_seq_of_tendsto_nhds



## [2020-10-01 09:16:49](https://github.com/leanprover-community/mathlib/commit/fb2b1de)
feat(algebra/ordered_ring): ask for 0 < 1 earlier. ([#4296](https://github.com/leanprover-community/mathlib/pull/4296))
It used to be that `linear_ordered_semiring` asked for `0 < 1`, while `ordered_semiring` didn't.
I'd prefer that `ordered_semiring` asks for this already:
1. because lots of interesting examples (e.g. rings of operators) satisfy this property
2. because the rest of mathlib doesn't care
#### Estimated changes
modified src/algebra/ordered_ring.lean
- \+/\- *lemma* zero_lt_one
- \+/\- *lemma* zero_le_one
- \+/\- *lemma* zero_lt_two
- \+/\- *lemma* two_ne_zero
- \+/\- *lemma* one_lt_two
- \+/\- *lemma* one_le_two
- \+/\- *lemma* zero_lt_four
- \+/\- *lemma* mul_lt_mul''
- \+/\- *lemma* le_mul_of_one_le_right
- \+/\- *lemma* le_mul_of_one_le_left
- \+/\- *lemma* bit1_pos
- \+/\- *lemma* bit1_pos'
- \+/\- *lemma* lt_add_one
- \+/\- *lemma* lt_one_add
- \+/\- *lemma* one_lt_mul
- \+/\- *lemma* mul_le_one
- \+/\- *lemma* one_lt_mul_of_le_of_lt
- \+/\- *lemma* one_lt_mul_of_lt_of_le
- \+/\- *lemma* mul_le_of_le_one_right
- \+/\- *lemma* mul_le_of_le_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_right
- \+/\- *lemma* zero_lt_one
- \+/\- *lemma* zero_le_one
- \+/\- *lemma* zero_lt_two
- \+/\- *lemma* two_ne_zero
- \+/\- *lemma* one_lt_two
- \+/\- *lemma* one_le_two
- \+/\- *lemma* zero_lt_four
- \+/\- *lemma* mul_lt_mul''
- \+/\- *lemma* le_mul_of_one_le_right
- \+/\- *lemma* le_mul_of_one_le_left
- \+/\- *lemma* bit1_pos
- \+/\- *lemma* bit1_pos'
- \+/\- *lemma* lt_add_one
- \+/\- *lemma* lt_one_add
- \+/\- *lemma* one_lt_mul
- \+/\- *lemma* mul_le_one
- \+/\- *lemma* one_lt_mul_of_le_of_lt
- \+/\- *lemma* one_lt_mul_of_lt_of_le
- \+/\- *lemma* mul_le_of_le_one_right
- \+/\- *lemma* mul_le_of_le_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_left
- \+/\- *lemma* mul_lt_one_of_nonneg_of_lt_one_right

modified src/order/filter/filter_product.lean



## [2020-10-01 07:41:14](https://github.com/leanprover-community/mathlib/commit/9ceb114)
feat(analysis/normed_space/inner_product): Define the inner product based on `is_R_or_C` ([#4057](https://github.com/leanprover-community/mathlib/pull/4057))
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* abs_norm_eq_norm

modified src/analysis/normed_space/hahn_banach.lean

created src/analysis/normed_space/inner_product.lean
- \+ *lemma* inner_conj_sym
- \+ *lemma* inner_self_nonneg
- \+ *lemma* inner_self_nonneg_im
- \+ *lemma* inner_self_im_zero
- \+ *lemma* inner_add_left
- \+ *lemma* inner_add_right
- \+ *lemma* inner_norm_sq_eq_inner_self
- \+ *lemma* inner_re_symm
- \+ *lemma* inner_im_symm
- \+ *lemma* inner_smul_left
- \+ *lemma* inner_smul_right
- \+ *lemma* inner_zero_left
- \+ *lemma* inner_zero_right
- \+ *lemma* inner_self_eq_zero
- \+ *lemma* inner_self_re_to_K
- \+ *lemma* inner_abs_conj_sym
- \+ *lemma* inner_neg_left
- \+ *lemma* inner_neg_right
- \+ *lemma* inner_sub_left
- \+ *lemma* inner_sub_right
- \+ *lemma* inner_mul_conj_re_abs
- \+ *lemma* inner_add_add_self
- \+ *lemma* inner_sub_sub_self
- \+ *lemma* inner_mul_inner_self_le
- \+ *lemma* norm_eq_sqrt_inner
- \+ *lemma* inner_self_eq_norm_square
- \+ *lemma* sqrt_norm_sq_eq_norm
- \+ *lemma* abs_inner_le_norm
- \+ *lemma* inner_conj_sym
- \+ *lemma* real_inner_comm
- \+ *lemma* inner_eq_zero_sym
- \+ *lemma* inner_self_nonneg_im
- \+ *lemma* inner_self_im_zero
- \+ *lemma* inner_add_left
- \+ *lemma* inner_add_right
- \+ *lemma* inner_re_symm
- \+ *lemma* inner_im_symm
- \+ *lemma* inner_smul_left
- \+ *lemma* real_inner_smul_left
- \+ *lemma* inner_smul_right
- \+ *lemma* real_inner_smul_right
- \+ *lemma* sum_inner
- \+ *lemma* inner_sum
- \+ *lemma* inner_zero_left
- \+ *lemma* inner_re_zero_left
- \+ *lemma* inner_zero_right
- \+ *lemma* inner_re_zero_right
- \+ *lemma* inner_self_nonneg
- \+ *lemma* real_inner_self_nonneg
- \+ *lemma* inner_self_eq_zero
- \+ *lemma* inner_self_nonpos
- \+ *lemma* real_inner_self_nonpos
- \+ *lemma* inner_self_re_to_K
- \+ *lemma* inner_self_re_abs
- \+ *lemma* inner_self_abs_to_K
- \+ *lemma* real_inner_self_abs
- \+ *lemma* inner_abs_conj_sym
- \+ *lemma* inner_neg_left
- \+ *lemma* inner_neg_right
- \+ *lemma* inner_neg_neg
- \+ *lemma* inner_self_conj
- \+ *lemma* inner_sub_left
- \+ *lemma* inner_sub_right
- \+ *lemma* inner_mul_conj_re_abs
- \+ *lemma* inner_add_add_self
- \+ *lemma* real_inner_add_add_self
- \+ *lemma* inner_sub_sub_self
- \+ *lemma* real_inner_sub_sub_self
- \+ *lemma* parallelogram_law
- \+ *lemma* inner_mul_inner_self_le
- \+ *lemma* real_inner_mul_inner_self_le
- \+ *lemma* linear_independent_of_ne_zero_of_inner_eq_zero
- \+ *lemma* norm_eq_sqrt_inner
- \+ *lemma* norm_eq_sqrt_real_inner
- \+ *lemma* inner_self_eq_norm_square
- \+ *lemma* real_inner_self_eq_norm_square
- \+ *lemma* norm_add_pow_two
- \+ *lemma* norm_add_pow_two_real
- \+ *lemma* norm_add_mul_self
- \+ *lemma* norm_add_mul_self_real
- \+ *lemma* norm_sub_pow_two
- \+ *lemma* norm_sub_pow_two_real
- \+ *lemma* norm_sub_mul_self
- \+ *lemma* norm_sub_mul_self_real
- \+ *lemma* abs_inner_le_norm
- \+ *lemma* abs_real_inner_le_norm
- \+ *lemma* parallelogram_law_with_norm
- \+ *lemma* parallelogram_law_with_norm_real
- \+ *lemma* real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
- \+ *lemma* real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero
- \+ *lemma* norm_add_square_eq_norm_square_add_norm_square_real
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero
- \+ *lemma* norm_sub_square_eq_norm_square_add_norm_square_real
- \+ *lemma* real_inner_add_sub_eq_zero_iff
- \+ *lemma* abs_real_inner_div_norm_mul_norm_le_one
- \+ *lemma* real_inner_smul_self_left
- \+ *lemma* real_inner_smul_self_right
- \+ *lemma* abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
- \+ *lemma* real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
- \+ *lemma* real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
- \+ *lemma* abs_real_inner_div_norm_mul_norm_eq_one_iff
- \+ *lemma* real_inner_div_norm_mul_norm_eq_one_iff
- \+ *lemma* real_inner_div_norm_mul_norm_eq_neg_one_iff
- \+ *lemma* inner_sum_smul_sum_smul_of_sum_eq_zero
- \+ *lemma* real_inner_eq_re_inner
- \+ *lemma* findim_euclidean_space
- \+ *lemma* findim_euclidean_space_fin
- \+ *lemma* orthogonal_projection_fn_mem
- \+ *lemma* is
- \+ *lemma* orthogonal_projection_fn_inner_eq_zero
- \+ *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \+ *lemma* orthogonal_projection_def
- \+ *lemma* orthogonal_projection_fn_eq
- \+ *lemma* orthogonal_projection_mem
- \+ *lemma* orthogonal_projection_inner_eq_zero
- \+ *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \+ *lemma* submodule.mem_orthogonal
- \+ *lemma* submodule.mem_orthogonal'
- \+ *lemma* submodule.inner_right_of_mem_orthogonal
- \+ *lemma* submodule.inner_left_of_mem_orthogonal
- \+ *lemma* submodule.orthogonal_disjoint
- \+ *lemma* submodule.orthogonal_gc
- \+ *lemma* submodule.orthogonal_le
- \+ *lemma* submodule.le_orthogonal_orthogonal
- \+ *lemma* submodule.inf_orthogonal
- \+ *lemma* submodule.infi_orthogonal
- \+ *lemma* submodule.Inf_orthogonal
- \+ *lemma* submodule.sup_orthogonal_inf_of_is_complete
- \+ *lemma* submodule.sup_orthogonal_of_is_complete
- \+ *lemma* submodule.is_compl_orthogonal_of_is_complete_real
- \+ *lemma* submodule.findim_add_inf_findim_orthogonal
- \+ *theorem* exists_norm_eq_infi_of_complete_convex
- \+ *theorem* norm_eq_infi_iff_real_inner_le_zero
- \+ *theorem* exists_norm_eq_infi_of_complete_subspace
- \+ *theorem* norm_eq_infi_iff_real_inner_eq_zero
- \+ *theorem* norm_eq_infi_iff_inner_eq_zero
- \+ *def* to_has_inner
- \+ *def* norm_sq
- \+ *def* to_has_norm
- \+ *def* to_normed_group
- \+ *def* to_normed_space
- \+ *def* inner_product_space.of_core
- \+ *def* sesq_form_of_inner
- \+ *def* bilin_form_of_real_inner
- \+ *def* euclidean_space
- \+ *def* has_inner.is_R_or_C_to_real
- \+ *def* inner_product_space.is_R_or_C_to_real
- \+ *def* orthogonal_projection_fn
- \+ *def* orthogonal_projection_of_complete
- \+ *def* orthogonal_projection
- \+ *def* submodule.orthogonal

deleted src/analysis/normed_space/real_inner_product.lean
- \- *lemma* inner_comm
- \- *lemma* inner_add_left
- \- *lemma* inner_add_right
- \- *lemma* inner_smul_left
- \- *lemma* inner_smul_right
- \- *lemma* norm_eq_sqrt_inner
- \- *lemma* inner_self_eq_norm_square
- \- *lemma* inner_add_add_self
- \- *lemma* inner_mul_inner_self_le
- \- *lemma* abs_inner_le_norm
- \- *lemma* inner_comm
- \- *lemma* inner_add_left
- \- *lemma* inner_add_right
- \- *lemma* inner_smul_left
- \- *lemma* inner_smul_right
- \- *lemma* sum_inner
- \- *lemma* inner_sum
- \- *lemma* inner_zero_left
- \- *lemma* inner_zero_right
- \- *lemma* inner_self_eq_zero
- \- *lemma* inner_self_nonneg
- \- *lemma* inner_self_nonpos
- \- *lemma* inner_neg_left
- \- *lemma* inner_neg_right
- \- *lemma* inner_neg_neg
- \- *lemma* inner_sub_left
- \- *lemma* inner_sub_right
- \- *lemma* inner_add_add_self
- \- *lemma* inner_sub_sub_self
- \- *lemma* parallelogram_law
- \- *lemma* inner_mul_inner_self_le
- \- *lemma* linear_independent_of_ne_zero_of_inner_eq_zero
- \- *lemma* inner_self_eq_norm_square
- \- *lemma* norm_add_pow_two
- \- *lemma* norm_add_mul_self
- \- *lemma* norm_sub_pow_two
- \- *lemma* norm_sub_mul_self
- \- *lemma* abs_inner_le_norm
- \- *lemma* parallelogram_law_with_norm
- \- *lemma* inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
- \- *lemma* inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
- \- *lemma* inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
- \- *lemma* norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero
- \- *lemma* norm_add_square_eq_norm_square_add_norm_square
- \- *lemma* norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero
- \- *lemma* norm_sub_square_eq_norm_square_add_norm_square
- \- *lemma* inner_add_sub_eq_zero_iff
- \- *lemma* abs_inner_div_norm_mul_norm_le_one
- \- *lemma* inner_smul_self_left
- \- *lemma* inner_smul_self_right
- \- *lemma* abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
- \- *lemma* inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
- \- *lemma* inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
- \- *lemma* abs_inner_div_norm_mul_norm_eq_one_iff
- \- *lemma* inner_div_norm_mul_norm_eq_one_iff
- \- *lemma* inner_div_norm_mul_norm_eq_neg_one_iff
- \- *lemma* inner_sum_smul_sum_smul_of_sum_eq_zero
- \- *lemma* findim_euclidean_space
- \- *lemma* findim_euclidean_space_fin
- \- *lemma* orthogonal_projection_fn_mem
- \- *lemma* is
- \- *lemma* orthogonal_projection_fn_inner_eq_zero
- \- *lemma* eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
- \- *lemma* orthogonal_projection_def
- \- *lemma* orthogonal_projection_fn_eq
- \- *lemma* orthogonal_projection_mem
- \- *lemma* orthogonal_projection_inner_eq_zero
- \- *lemma* eq_orthogonal_projection_of_mem_of_inner_eq_zero
- \- *lemma* submodule.mem_orthogonal
- \- *lemma* submodule.mem_orthogonal'
- \- *lemma* submodule.inner_right_of_mem_orthogonal
- \- *lemma* submodule.inner_left_of_mem_orthogonal
- \- *lemma* submodule.orthogonal_disjoint
- \- *lemma* submodule.orthogonal_gc
- \- *lemma* submodule.orthogonal_le
- \- *lemma* submodule.le_orthogonal_orthogonal
- \- *lemma* submodule.inf_orthogonal
- \- *lemma* submodule.infi_orthogonal
- \- *lemma* submodule.Inf_orthogonal
- \- *lemma* submodule.sup_orthogonal_inf_of_is_complete
- \- *lemma* submodule.sup_orthogonal_of_is_complete
- \- *lemma* submodule.is_compl_orthogonal_of_is_complete
- \- *lemma* submodule.findim_add_inf_findim_orthogonal
- \- *theorem* exists_norm_eq_infi_of_complete_convex
- \- *theorem* norm_eq_infi_iff_inner_le_zero
- \- *theorem* exists_norm_eq_infi_of_complete_subspace
- \- *theorem* norm_eq_infi_iff_inner_eq_zero
- \- *def* to_has_inner
- \- *def* to_has_norm
- \- *def* to_normed_group
- \- *def* to_normed_space
- \- *def* inner_product_space.of_core
- \- *def* bilin_form_of_inner
- \- *def* euclidean_space
- \- *def* orthogonal_projection_fn
- \- *def* orthogonal_projection_of_complete
- \- *def* orthogonal_projection
- \- *def* submodule.orthogonal

modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* inv_def
- \+/\- *lemma* zero_re
- \+ *lemma* zero_re'
- \+/\- *lemma* of_real_add
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* of_real_mul
- \+ *lemma* of_real_mul_re
- \+ *lemma* I_im'
- \+ *lemma* sqrt_norm_sq_eq_norm
- \+ *lemma* div_re_of_real
- \+ *lemma* norm_conj
- \+ *lemma* conj_inv
- \+ *lemma* conj_div
- \+ *lemma* re_eq_abs_of_mul_conj
- \+ *lemma* abs_sqr_re_add_conj
- \+ *lemma* abs_sqr_re_add_conj'
- \+ *lemma* conj_mul_eq_norm_sq_left
- \+/\- *lemma* zero_re
- \+/\- *lemma* of_real_add
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* of_real_mul
- \+/\- *lemma* inv_def
- \+ *def* conj_to_ring_equiv

modified src/geometry/euclidean/basic.lean
- \+/\- *lemma* inner_eq_zero_iff_angle_eq_pi_div_two
- \+/\- *lemma* inner_eq_zero_iff_angle_eq_pi_div_two

modified src/geometry/euclidean/circumcenter.lean

modified src/geometry/euclidean/monge_point.lean

modified src/geometry/euclidean/triangle.lean

modified src/geometry/manifold/instances/real.lean
- \+/\- *def* euclidean_quadrant
- \+/\- *def* euclidean_quadrant

modified src/linear_algebra/sesquilinear_form.lean
- \+ *lemma* is_add_monoid_hom_left
- \+ *lemma* is_add_monoid_hom_right
- \+ *lemma* map_sum_left
- \+ *lemma* map_sum_right

modified src/ring_theory/algebra.lean
- \- *def* subspace.restrict_scalars



## [2020-10-01 02:57:05](https://github.com/leanprover-community/mathlib/commit/1b97326)
feat(data/fintype): pigeonhole principles ([#4096](https://github.com/leanprover-community/mathlib/pull/4096))
Add pigeonhole principles for finitely and infinitely many pigeons in finitely many holes. There are also strong versions of these, which say that there is a hole containing at least as many pigeons as the average number of pigeons per hole. Fixes [#2272](https://github.com/leanprover-community/mathlib/pull/2272).
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_fiberwise_of_maps_to
- \+ *theorem* card_eq_sum_card_fiberwise

modified src/algebra/big_operators/order.lean
- \+ *lemma* sum_fiberwise_le_sum_of_sum_fiber_nonneg
- \+ *lemma* sum_le_sum_fiberwise_of_sum_fiber_nonpos
- \+ *theorem* card_le_mul_card_image_of_maps_to
- \+ *theorem* exists_lt_of_sum_lt

modified src/algebra/ordered_group.lean

created src/combinatorics/pigeonhole.lean
- \+ *lemma* exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum
- \+ *lemma* exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul
- \+ *lemma* exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum
- \+ *lemma* exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
- \+ *lemma* exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
- \+ *lemma* exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul
- \+ *lemma* exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum
- \+ *lemma* exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
- \+ *lemma* exists_lt_card_fiber_of_mul_lt_card_of_maps_to
- \+ *lemma* exists_card_fiber_lt_of_card_lt_mul
- \+ *lemma* exists_le_card_fiber_of_mul_le_card_of_maps_to
- \+ *lemma* exists_card_fiber_le_of_card_le_mul
- \+ *lemma* exists_lt_sum_fiber_of_nsmul_lt_sum
- \+ *lemma* exists_le_sum_fiber_of_nsmul_le_sum
- \+ *lemma* exists_sum_fiber_lt_of_sum_lt_nsmul
- \+ *lemma* exists_sum_fiber_le_of_sum_le_nsmul
- \+ *lemma* exists_lt_card_fiber_of_mul_lt_card
- \+ *lemma* exists_card_fiber_lt_of_card_lt_mul
- \+ *lemma* exists_le_card_fiber_of_mul_le_card
- \+ *lemma* exists_card_fiber_le_of_card_le_mul

modified src/data/finset/basic.lean
- \+ *lemma* filter_mem_image_eq_image
- \+ *lemma* fiber_nonempty_iff_mem_image
- \+ *lemma* fiber_card_ne_zero_iff_mem_image
- \+ *lemma* exists_ne_map_eq_of_card_lt_of_maps_to
- \+ *lemma* bind_filter_eq_of_maps_to
- \+/\- *lemma* image_bind_filter_eq
- \+/\- *lemma* image_bind_filter_eq

modified src/data/fintype/basic.lean
- \+ *lemma* univ_nonempty
- \+ *lemma* exists_ne_map_eq_of_card_lt
- \+ *lemma* fintype.exists_ne_map_eq_of_infinite
- \+ *lemma* fintype.exists_infinite_fiber

modified src/data/fintype/card.lean



## [2020-10-01 01:07:36](https://github.com/leanprover-community/mathlib/commit/af99416)
chore(scripts): update nolints.txt ([#4341](https://github.com/leanprover-community/mathlib/pull/4341))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt

