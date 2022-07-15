## [2022-02-28 16:08:55](https://github.com/leanprover-community/mathlib/commit/456898c)
feat(data/finsupp/basic): Version of `finsupp.prod_add_index` with weaker premises ([#11353](https://github.com/leanprover-community/mathlib/pull/11353))
A simpler proof of `finsupp.prod_add_index : (f + g).prod h = f.prod h * g.prod h` with weaker premises.
Specifically, this only requires:
* `[add_zero_class M]` rather than `[add_comm_monoid M]`
* `h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 1` rather than `h_zero : ∀a, h a 0 = 1`.  
* `h_add : ∀ (a ∈ f.support ∪ g.support) b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂` rather than `h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂` (thanks to Anne Baanen for spotting this weakening).
The original version has been retained and re-named to `finsupp.prod_add_index'`, since in some places this is more convenient to use.  (There was already a lemma called `prod_add_index'` which appears not to have been used anywhere.  This has been renamed to `prod_hom_add_index`.)
Discussed in this Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Variant.20of.20finsupp.2Eprod_add_index.3F
#### Estimated changes
Modified src/algebra/big_operators/finsupp.lean


Modified src/data/finsupp/basic.lean
- \+/\- *def* finsupp.lift_add_hom
- \+/\- *lemma* finsupp.prod_add_index'
- \+/\- *lemma* finsupp.prod_add_index
- \+ *lemma* finsupp.prod_hom_add_index
- \- *lemma* finsupp.sum_add_index'
- \+ *lemma* finsupp.sum_hom_add_index

Modified src/data/finsupp/multiset.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/nat/factorization.lean


Modified src/data/polynomial/basic.lean




## [2022-02-28 12:46:18](https://github.com/leanprover-community/mathlib/commit/1447c40)
refactor(group_theory/general_commutator): Rename `general_commutator` to `subgroup.commutator` ([#12308](https://github.com/leanprover-community/mathlib/pull/12308))
This PR renames `general_commutator` to `subgroup.commutator`.
I'll change the file name in a followup PR, so that this PR is easier to review.
(This is one of the several orthogonal changes from https://github.com/leanprover-community/mathlib/pull/12134)
#### Estimated changes
Modified src/group_theory/abelianization.lean


Modified src/group_theory/general_commutator.lean
- \- *lemma* bot_general_commutator
- \- *lemma* general_commutator_bot
- \- *lemma* general_commutator_comm
- \- *lemma* general_commutator_containment
- \- *lemma* general_commutator_def'
- \- *lemma* general_commutator_def
- \- *lemma* general_commutator_le
- \- *lemma* general_commutator_le_inf
- \- *lemma* general_commutator_le_left
- \- *lemma* general_commutator_le_right
- \- *lemma* general_commutator_mono
- \- *lemma* general_commutator_pi_pi_le
- \- *lemma* general_commutator_pi_pi_of_fintype
- \- *lemma* general_commutator_prod_prod
- \- *lemma* map_general_commutator
- \+ *lemma* subgroup.bot_commutator
- \+ *lemma* subgroup.commutator_bot
- \+ *lemma* subgroup.commutator_comm
- \+ *lemma* subgroup.commutator_containment
- \+ *lemma* subgroup.commutator_def'
- \+ *lemma* subgroup.commutator_def
- \+ *lemma* subgroup.commutator_le
- \+ *lemma* subgroup.commutator_le_inf
- \+ *lemma* subgroup.commutator_le_left
- \+ *lemma* subgroup.commutator_le_right
- \+ *lemma* subgroup.commutator_mono
- \+ *lemma* subgroup.commutator_pi_pi_le
- \+ *lemma* subgroup.commutator_pi_pi_of_fintype
- \+ *lemma* subgroup.commutator_prod_prod
- \+ *lemma* subgroup.map_commutator

Modified src/group_theory/nilpotent.lean


Modified src/group_theory/solvable.lean




## [2022-02-28 12:46:17](https://github.com/leanprover-community/mathlib/commit/92cbcc3)
chore(algebra): move star_ring structure on free_algebra ([#12297](https://github.com/leanprover-community/mathlib/pull/12297))
There's no need to have `algebra.star.basic` imported transitively into pretty much everything, just to put the `star_ring` structure on `free_algebra`, so I've moved this construction to its own file.
(I was changing definitions in `algebra.star.basic` to allow for more non-unital structures, it recompiling was very painful because of this transitive dependence.)
#### Estimated changes
Modified src/algebra/free_algebra.lean
- \- *lemma* free_algebra.star_algebra_map
- \- *def* free_algebra.star_hom
- \- *lemma* free_algebra.star_ι

Modified src/algebra/free_monoid.lean
- \- *lemma* free_monoid.star_of
- \- *lemma* free_monoid.star_one

Modified src/algebra/module/linear_map.lean


Added src/algebra/star/free.lean
- \+ *lemma* free_algebra.star_algebra_map
- \+ *def* free_algebra.star_hom
- \+ *lemma* free_algebra.star_ι
- \+ *lemma* free_monoid.star_of
- \+ *lemma* free_monoid.star_one

Modified src/data/nat/factorization.lean




## [2022-02-28 12:46:16](https://github.com/leanprover-community/mathlib/commit/9c71c0f)
feat(algebra/monoid_algebra/basic): add monomial_hom ([#12283](https://github.com/leanprover-community/mathlib/pull/12283))
Just adding one definition
#### Estimated changes
Modified src/algebra/monoid_algebra/basic.lean
- \+ *def* add_monoid_algebra.single_hom
- \+ *def* monoid_algebra.single_hom



## [2022-02-28 12:46:15](https://github.com/leanprover-community/mathlib/commit/c7498d0)
feat(algebra/{group/with_one,order/monoid}): equivs for `with_zero` and `with_one` ([#12275](https://github.com/leanprover-community/mathlib/pull/12275))
This provides:
* `add_equiv.with_zero_congr : α ≃+ β → with_zero α ≃+ with_zero β`
* `mul_equiv.with_one_congr : α ≃* β → with_one α ≃* with_one β`
* `with_zero.to_mul_bot : with_zero (multiplicative α) ≃* multiplicative (with_bot α)`
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/with_zero.20.28multiplicative.20A.29.20.E2.89.83*.20multiplicative.20.28with_bot.20A.29/near/272980650)
#### Estimated changes
Modified src/algebra/group/with_one.lean
- \+ *def* mul_equiv.with_one_congr
- \+ *lemma* mul_equiv.with_one_congr_refl
- \+ *lemma* mul_equiv.with_one_congr_symm
- \+ *lemma* mul_equiv.with_one_congr_trans
- \+ *lemma* with_one.map_coe
- \+/\- *lemma* with_one.map_comp
- \+ *lemma* with_one.map_map

Modified src/algebra/order/monoid.lean
- \- *def* with_zero.ordered_add_comm_monoid
- \+ *def* with_zero.to_mul_bot
- \+ *lemma* with_zero.to_mul_bot_coe
- \+ *lemma* with_zero.to_mul_bot_coe_of_add
- \+ *lemma* with_zero.to_mul_bot_le
- \+ *lemma* with_zero.to_mul_bot_lt
- \+ *lemma* with_zero.to_mul_bot_strict_mono
- \+ *lemma* with_zero.to_mul_bot_symm_bot
- \+ *lemma* with_zero.to_mul_bot_zero



## [2022-02-28 12:46:14](https://github.com/leanprover-community/mathlib/commit/474aecb)
doc(algebra,data/fun_like): small morphism documentation improvements ([#11642](https://github.com/leanprover-community/mathlib/pull/11642))
 * The `fun_like` docs talked about a `to_fun` class, this doesn't exist (anymore).
 * Warn that `{one,mul,monoid,monoid_with_zero}_hom.{congr_fun,congr_arg,coe_inj,ext_iff}` has been superseded by `fun_like`.
Thanks to @YaelDillies for pointing out these issues.
#### Estimated changes
Modified src/algebra/group/hom.lean


Modified src/algebra/module/linear_map.lean


Modified src/algebra/ring/basic.lean


Modified src/analysis/normed_space/linear_isometry.lean


Modified src/analysis/seminorm.lean


Modified src/data/fun_like/basic.lean


Modified src/ring_theory/derivation.lean




## [2022-02-28 12:16:38](https://github.com/leanprover-community/mathlib/commit/33c0a1c)
feat(ring_theory/dedekind_domain/ideal): add height_one_spectrum ([#12244](https://github.com/leanprover-community/mathlib/pull/12244))
#### Estimated changes
Modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* is_dedekind_domain.height_one_spectrum.associates.irreducible
- \+ *lemma* is_dedekind_domain.height_one_spectrum.irreducible
- \+ *lemma* is_dedekind_domain.height_one_spectrum.prime
- \+ *structure* is_dedekind_domain.height_one_spectrum



## [2022-02-28 10:33:37](https://github.com/leanprover-community/mathlib/commit/200c254)
feat(algebra/algebra,data/equiv/ring): `{ring,alg}_equiv.Pi_congr_right` ([#12289](https://github.com/leanprover-community/mathlib/pull/12289))
We extend `{add,mul}_equiv.Pi_congr_right` to rings and algebras.
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60ring_equiv.2EPi_congr_right.60
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *def* alg_equiv.Pi_congr_right
- \+ *lemma* alg_equiv.Pi_congr_right_refl
- \+ *lemma* alg_equiv.Pi_congr_right_symm
- \+ *lemma* alg_equiv.Pi_congr_right_trans

Modified src/data/equiv/ring.lean
- \+ *def* ring_equiv.Pi_congr_right
- \+ *lemma* ring_equiv.Pi_congr_right_refl
- \+ *lemma* ring_equiv.Pi_congr_right_symm
- \+ *lemma* ring_equiv.Pi_congr_right_trans



## [2022-02-28 10:33:35](https://github.com/leanprover-community/mathlib/commit/e700d56)
feat(ring_theory/polynomial/eisenstein): add a technical lemma ([#11839](https://github.com/leanprover-community/mathlib/pull/11839))
A technical lemma about Eiseinstein minimal polynomials.
From flt-regular
#### Estimated changes
Modified src/algebra/associated.lean
- \+ *lemma* prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd

Modified src/data/nat/basic.lean
- \+ *lemma* nat.le_add_pred_of_pos

Modified src/data/polynomial/monic.lean
- \+ *lemma* polynomial.degree_map_of_monic
- \+ *lemma* polynomial.nat_degree_map_of_monic

Modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral_smul

Modified src/ring_theory/polynomial/eisenstein.lean
- \+ *lemma* dvd_coeff_zero_of_aeval_eq_prime_smul_of_minpoly_is_eiseinstein_at



## [2022-02-28 10:33:34](https://github.com/leanprover-community/mathlib/commit/770a7ce)
feat(measure_theory/function/convergence_in_measure): Define convergence in measure ([#11774](https://github.com/leanprover-community/mathlib/pull/11774))
This PR defines convergence in measure and proves some properties about them. 
In particular, we prove that 
- convergence a.e. in a finite measure space implies convergence in measure
- convergence in measure implies there exists a subsequence that converges a.e.
- convergence in Lp implies convergence in measure
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/analysis/specific_limits.lean
- \+ *lemma* tsum_geometric_inv_two
- \+ *lemma* tsum_geometric_inv_two_ge

Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* ae_measurable_of_tendsto_metric_ae'
- \+/\- *lemma* ae_measurable_of_tendsto_metric_ae

Added src/measure_theory/function/convergence_in_measure.lean
- \+ *lemma* measure_theory.exists_seq_tendsto_ae.exists_nat_measure_lt_two_inv
- \+ *def* measure_theory.exists_seq_tendsto_ae.seq_tendsto_ae_seq
- \+ *def* measure_theory.exists_seq_tendsto_ae.seq_tendsto_ae_seq_aux
- \+ *lemma* measure_theory.exists_seq_tendsto_ae.seq_tendsto_ae_seq_spec
- \+ *lemma* measure_theory.exists_seq_tendsto_ae.seq_tendsto_ae_seq_strict_mono
- \+ *lemma* measure_theory.exists_seq_tendsto_ae.seq_tendsto_ae_seq_succ
- \+ *lemma* measure_theory.tendsto_in_measure.ae_measurable
- \+ *lemma* measure_theory.tendsto_in_measure.congr_left
- \+ *lemma* measure_theory.tendsto_in_measure.congr_right
- \+ *lemma* measure_theory.tendsto_in_measure.exists_seq_tendsto_ae'
- \+ *lemma* measure_theory.tendsto_in_measure.exists_seq_tendsto_ae
- \+ *lemma* measure_theory.tendsto_in_measure.exists_seq_tendsto_in_measure_at_top
- \+ *def* measure_theory.tendsto_in_measure
- \+ *lemma* measure_theory.tendsto_in_measure_iff_norm
- \+ *lemma* measure_theory.tendsto_in_measure_of_tendsto_Lp
- \+ *lemma* measure_theory.tendsto_in_measure_of_tendsto_ae
- \+ *lemma* measure_theory.tendsto_in_measure_of_tendsto_ae_of_measurable
- \+ *lemma* measure_theory.tendsto_in_measure_of_tendsto_snorm
- \+ *lemma* measure_theory.tendsto_in_measure_of_tendsto_snorm_of_measurable
- \+ *lemma* measure_theory.tendsto_in_measure_of_tendsto_snorm_of_ne_top
- \+ *lemma* measure_theory.tendsto_in_measure_of_tendsto_snorm_top

Modified src/measure_theory/function/l1_space.lean


Modified src/measure_theory/integral/set_to_l1.lean


Modified src/topology/instances/ennreal.lean




## [2022-02-28 10:33:33](https://github.com/leanprover-community/mathlib/commit/b25bad7)
feat(archive/100-theorems-list): Partition theorem ([#4259](https://github.com/leanprover-community/mathlib/pull/4259))
A proof of Euler's partition theorem, from the Freek list.
The proof is sorry-free but currently unpleasant, and some parts don't belong in `archive/`, so WIP for now.
#### Estimated changes
Added archive/100-theorems-list/45_partition.lean
- \+ *lemma* coeff_indicator
- \+ *lemma* coeff_indicator_neg
- \+ *lemma* coeff_indicator_pos
- \+ *lemma* coeff_prod_range
- \+ *lemma* constant_coeff_indicator
- \+ *def* cut
- \+ *lemma* cut_empty_succ
- \+ *lemma* cut_equiv_antidiag
- \+ *lemma* cut_insert
- \+ *lemma* cut_zero
- \+ *theorem* distinct_gf_prop
- \+ *def* indicator_series
- \+ *lemma* mem_cut
- \+ *def* mk_odd
- \+ *lemma* num_series'
- \+ *theorem* odd_gf_prop
- \+ *def* partial_distinct_gf
- \+ *lemma* partial_distinct_gf_prop
- \+ *lemma* partial_gf_prop
- \+ *def* partial_odd_gf
- \+ *lemma* partial_odd_gf_prop
- \+ *theorem* partition_theorem
- \+ *lemma* same_coeffs
- \+ *lemma* same_gf
- \+ *lemma* two_series

Modified docs/100.yaml


Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.mem_sum

Modified src/data/list/nat_antidiagonal.lean




## [2022-02-28 09:09:20](https://github.com/leanprover-community/mathlib/commit/dc72624)
chore(measure_theory/function/strongly_measurable): remove useless no_zero_divisors assumption ([#12353](https://github.com/leanprover-community/mathlib/pull/12353))
#### Estimated changes
Modified src/algebra/support.lean
- \+ *lemma* function.support_mul_subset_left
- \+ *lemma* function.support_mul_subset_right

Modified src/measure_theory/function/strongly_measurable.lean




## [2022-02-28 08:31:53](https://github.com/leanprover-community/mathlib/commit/58c20c1)
feat(measure_theory/group): add measures invariant under inversion/negation ([#11954](https://github.com/leanprover-community/mathlib/pull/11954))
* Define measures invariant under `inv` or `neg`
* Prove lemmas about measures invariant under `inv` similar to the lemmas about measures invariant under `mul`
* Also provide more `pi` instances in `arithmetic`.
* Rename some `integral_zero...` lemmas to `integral_eq_zero...`
* Reformulate `pi.is_mul_left_invariant_volume` using nondependent functions, so that type class inference can find it for `ι → ℝ`)
* Add some more integration lemmas, also for multiplication
#### Estimated changes
Modified src/analysis/fourier.lean


Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable.comp_measurable

Modified src/measure_theory/group/arithmetic.lean


Modified src/measure_theory/group/integration.lean
- \+ *lemma* measure_theory.integrable.comp_div_left
- \+ *lemma* measure_theory.integrable.comp_div_right
- \+ *lemma* measure_theory.integrable.comp_inv
- \+ *lemma* measure_theory.integrable.comp_mul_left
- \+ *lemma* measure_theory.integrable.comp_mul_right
- \+ *lemma* measure_theory.integral_div_left_eq_self
- \+ *lemma* measure_theory.integral_eq_zero_of_mul_left_eq_neg
- \+ *lemma* measure_theory.integral_eq_zero_of_mul_right_eq_neg
- \+ *lemma* measure_theory.integral_inv_eq_self
- \- *lemma* measure_theory.integral_zero_of_mul_left_eq_neg
- \- *lemma* measure_theory.integral_zero_of_mul_right_eq_neg

Modified src/measure_theory/group/measure.lean
- \+ *lemma* measure_theory.map_div_right_eq_self
- \+ *lemma* measure_theory.measure.inv_eq_self
- \+ *lemma* measure_theory.measure.map_div_left_eq_self
- \+ *lemma* measure_theory.measure.map_inv_eq_self
- \+ *lemma* measure_theory.measure.map_mul_right_inv_eq_self
- \+ *lemma* measure_theory.measure.measure_inv
- \+ *lemma* measure_theory.measure.measure_preimage_inv

Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.integral_norm_eq_lintegral_nnnorm

Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/measure_theory/measure/lebesgue.lean
- \- *lemma* real.map_volume_neg

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.map_id'



## [2022-02-28 02:34:22](https://github.com/leanprover-community/mathlib/commit/f3a04ed)
feat(group_theory/subgroup/basic): Centralizer subgroup ([#11946](https://github.com/leanprover-community/mathlib/pull/11946))
This PR defines the centralizer subgroup, and provides a few basic lemmas.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *def* subgroup.centralizer
- \+ *lemma* subgroup.centralizer_top
- \+ *lemma* subgroup.mem_centralizer_iff
- \+ *lemma* subgroup.mem_centralizer_iff_commutator_eq_one

Added src/group_theory/submonoid/centralizer.lean
- \+ *lemma* set.add_mem_centralizer
- \+ *def* set.centralizer
- \+ *lemma* set.centralizer_eq_univ
- \+ *lemma* set.centralizer_subset
- \+ *lemma* set.centralizer_univ
- \+ *lemma* set.div_mem_centralizer
- \+ *lemma* set.div_mem_centralizer₀
- \+ *lemma* set.inv_mem_centralizer
- \+ *lemma* set.inv_mem_centralizer₀
- \+ *lemma* set.mem_centralizer_iff
- \+ *lemma* set.mul_mem_centralizer
- \+ *lemma* set.neg_mem_centralizer
- \+ *lemma* set.one_mem_centralizer
- \+ *lemma* set.zero_mem_centralizer
- \+ *def* submonoid.centralizer
- \+ *lemma* submonoid.centralizer_subset
- \+ *lemma* submonoid.centralizer_univ
- \+ *lemma* submonoid.coe_centralizer
- \+ *lemma* submonoid.mem_centralizer_iff



## [2022-02-27 23:09:46](https://github.com/leanprover-community/mathlib/commit/2f86b49)
doc(data/set_like/basic): tidy up docstring ([#12337](https://github.com/leanprover-community/mathlib/pull/12337))
Hopefully this makes the docstring slightly clearer.
#### Estimated changes
Modified src/data/set_like/basic.lean




## [2022-02-27 23:09:45](https://github.com/leanprover-community/mathlib/commit/dfacfd3)
chore(linear_algebra/basic): make `linear_map.id_coe` elegible for `dsimp` ([#12334](https://github.com/leanprover-community/mathlib/pull/12334))
`dsimp` only considers lemmas which _are_ proved by `rfl`, not ones that just _could_ be.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+/\- *lemma* linear_map.id_coe

Modified src/linear_algebra/finsupp.lean




## [2022-02-27 22:39:10](https://github.com/leanprover-community/mathlib/commit/f322fa0)
refactor(group_theory/solvable): Delete duplicate lemma ([#12307](https://github.com/leanprover-community/mathlib/pull/12307))
`map_commutator_eq_commutator_map` is a duplicate of `map_general_commutator`.
(This is one of the several orthogonal changes from [#12134](https://github.com/leanprover-community/mathlib/pull/12134))
#### Estimated changes
Modified src/group_theory/solvable.lean
- \- *lemma* map_commutator_eq_commutator_map



## [2022-02-27 22:00:44](https://github.com/leanprover-community/mathlib/commit/7f52f94)
feat(analysis/complex): maximum modulus principle ([#12050](https://github.com/leanprover-community/mathlib/pull/12050))
#### Estimated changes
Added src/analysis/complex/abs_max.lean
- \+ *lemma* complex.eq_on_of_eq_on_frontier
- \+ *lemma* complex.exists_mem_frontier_is_max_on_norm
- \+ *lemma* complex.is_open_set_of_mem_nhds_and_is_max_on_norm
- \+ *lemma* complex.norm_eq_norm_of_is_max_on_of_closed_ball_subset
- \+ *lemma* complex.norm_eq_on_closed_ball_of_is_max_on
- \+ *lemma* complex.norm_eventually_eq_of_is_local_max
- \+ *lemma* complex.norm_le_of_forall_mem_frontier_norm_le
- \+ *lemma* complex.norm_max_aux₁
- \+ *lemma* complex.norm_max_aux₂
- \+ *lemma* complex.norm_max_aux₃



## [2022-02-27 21:28:31](https://github.com/leanprover-community/mathlib/commit/b5faa34)
feat(analysis/complex/liouville): prove Liouville's theorem ([#12095](https://github.com/leanprover-community/mathlib/pull/12095))
#### Estimated changes
Added src/analysis/complex/liouville.lean
- \+ *lemma* complex.deriv_eq_smul_circle_integral
- \+ *lemma* complex.liouville_theorem_aux
- \+ *lemma* complex.norm_deriv_le_aux
- \+ *lemma* complex.norm_deriv_le_of_forall_mem_sphere_norm_le
- \+ *lemma* differentiable.apply_eq_apply_of_bounded
- \+ *lemma* differentiable.exists_const_forall_eq_of_bounded
- \+ *lemma* differentiable.exists_eq_const_of_bounded



## [2022-02-27 20:07:58](https://github.com/leanprover-community/mathlib/commit/a5ffb9b)
feat(analysis/special_functions): little o behaviour of exp/log at infinity ([#11840](https://github.com/leanprover-community/mathlib/pull/11840))
from the unit-fractions project
#### Estimated changes
Modified src/analysis/special_functions/exp.lean
- \+ *lemma* real.is_o_pow_exp_at_top
- \+/\- *lemma* real.tendsto_div_pow_mul_exp_add_at_top
- \+/\- *lemma* real.tendsto_mul_exp_add_div_pow_at_top

Modified src/analysis/special_functions/log.lean
- \+ *lemma* real.is_o_pow_log_id_at_top
- \+ *lemma* real.tendsto_pow_log_div_mul_add_at_top

Modified src/analysis/special_functions/pow.lean




## [2022-02-27 16:32:35](https://github.com/leanprover-community/mathlib/commit/c4cf451)
fix(catgory_theory/limits): fix a typo ([#12341](https://github.com/leanprover-community/mathlib/pull/12341))
#### Estimated changes
Modified src/category_theory/limits/preserves/shapes/zero.lean




## [2022-02-27 16:04:10](https://github.com/leanprover-community/mathlib/commit/8ef4331)
feat(ring_theory/witt_vector): Witt vectors are a DVR ([#12213](https://github.com/leanprover-community/mathlib/pull/12213))
This PR adds two connected files. `mul_coeff.lean` adds an auxiliary result that's used in a few places in [#12041](https://github.com/leanprover-community/mathlib/pull/12041) . One of these places is in `discrete_valuation_ring.lean`, which shows that Witt vectors over a perfect field form a DVR.
#### Estimated changes
Added src/ring_theory/witt_vector/discrete_valuation_ring.lean
- \+ *lemma* witt_vector.coe_mk_unit
- \+ *lemma* witt_vector.exists_eq_pow_p_mul'
- \+ *lemma* witt_vector.exists_eq_pow_p_mul
- \+ *lemma* witt_vector.irreducible
- \+ *lemma* witt_vector.is_unit_of_coeff_zero_ne_zero
- \+ *def* witt_vector.mk_unit
- \+ *def* witt_vector.succ_nth_val_units

Modified src/ring_theory/witt_vector/identities.lean
- \+ *lemma* witt_vector.coeff_p
- \+ *lemma* witt_vector.coeff_p_one
- \+ *lemma* witt_vector.coeff_p_zero

Added src/ring_theory/witt_vector/mul_coeff.lean
- \+ *lemma* witt_vector.mul_poly_of_interest_aux1
- \+ *lemma* witt_vector.mul_poly_of_interest_aux2
- \+ *lemma* witt_vector.mul_poly_of_interest_aux3
- \+ *lemma* witt_vector.mul_poly_of_interest_aux4
- \+ *lemma* witt_vector.mul_poly_of_interest_aux5
- \+ *lemma* witt_vector.mul_poly_of_interest_vars
- \+ *lemma* witt_vector.nth_mul_coeff'
- \+ *lemma* witt_vector.nth_mul_coeff
- \+ *def* witt_vector.nth_remainder
- \+ *lemma* witt_vector.nth_remainder_spec
- \+ *lemma* witt_vector.peval_poly_of_interest'
- \+ *lemma* witt_vector.peval_poly_of_interest
- \+ *def* witt_vector.poly_of_interest
- \+ *lemma* witt_vector.poly_of_interest_vars
- \+ *lemma* witt_vector.poly_of_interest_vars_eq
- \+ *def* witt_vector.remainder
- \+ *lemma* witt_vector.remainder_vars
- \+ *def* witt_vector.witt_poly_prod
- \+ *def* witt_vector.witt_poly_prod_remainder
- \+ *lemma* witt_vector.witt_poly_prod_remainder_vars
- \+ *lemma* witt_vector.witt_poly_prod_vars



## [2022-02-27 15:35:55](https://github.com/leanprover-community/mathlib/commit/1dfb38d)
doc(imo*,algebra/continued_fractions/computation): change \minus to - ([#12338](https://github.com/leanprover-community/mathlib/pull/12338))
Change around 14 instances of a non-standard minus to `-`.
#### Estimated changes
Modified archive/imo/imo1998_q2.lean


Modified archive/imo/imo2005_q4.lean


Modified archive/imo/imo2011_q5.lean


Modified archive/imo/imo2019_q4.lean


Modified src/algebra/continued_fractions/computation/basic.lean




## [2022-02-27 14:12:55](https://github.com/leanprover-community/mathlib/commit/00a3d02)
feat(geometry/euclidean/oriented_angle): oriented angles with respect to an orientation ([#12236](https://github.com/leanprover-community/mathlib/pull/12236))
Add definitions and lemmas for oriented angles defined to take an
orientation, instead of an orthonormal basis, as an argument.  These
are the versions intended to be used by most users when working with
oriented angles between vectors, instead of users needing to deal with
a choice of basis.
Apart from the last five lemmas that relate angles and rotations for
different orientations or relate them explicitly to the definitions
with respect to a basis, everything is deduced directly from the
corresponding lemma that takes an orthonormal basis as an argument.
#### Estimated changes
Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/oriented_angle.lean
- \+ *lemma* orientation.det_rotation
- \+ *lemma* orientation.eq_iff_norm_eq_and_oangle_eq_zero
- \+ *lemma* orientation.eq_iff_norm_eq_of_oangle_eq_zero
- \+ *lemma* orientation.eq_iff_oangle_eq_zero_of_norm_eq
- \+ *lemma* orientation.eq_rotation_self_iff
- \+ *lemma* orientation.eq_rotation_self_iff_angle_eq_zero
- \+ *lemma* orientation.exists_linear_isometry_equiv_eq_of_det_pos
- \+ *lemma* orientation.linear_equiv_det_rotation
- \+ *def* orientation.oangle
- \+ *lemma* orientation.oangle_add
- \+ *lemma* orientation.oangle_add_cyc3
- \+ *lemma* orientation.oangle_add_cyc3_neg_left
- \+ *lemma* orientation.oangle_add_cyc3_neg_right
- \+ *lemma* orientation.oangle_add_oangle_rev
- \+ *lemma* orientation.oangle_add_oangle_rev_neg_left
- \+ *lemma* orientation.oangle_add_oangle_rev_neg_right
- \+ *lemma* orientation.oangle_add_swap
- \+ *lemma* orientation.oangle_eq_basis_oangle
- \+ *lemma* orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero
- \+ *lemma* orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero
- \+ *lemma* orientation.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
- \+ *lemma* orientation.oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero
- \+ *lemma* orientation.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq
- \+ *lemma* orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq
- \+ *lemma* orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real
- \+ *lemma* orientation.oangle_map
- \+ *lemma* orientation.oangle_neg_left
- \+ *lemma* orientation.oangle_neg_left_eq_neg_right
- \+ *lemma* orientation.oangle_neg_neg
- \+ *lemma* orientation.oangle_neg_orientation_eq_neg
- \+ *lemma* orientation.oangle_neg_right
- \+ *lemma* orientation.oangle_neg_self_left
- \+ *lemma* orientation.oangle_neg_self_right
- \+ *lemma* orientation.oangle_rev
- \+ *lemma* orientation.oangle_rotation
- \+ *lemma* orientation.oangle_rotation_left
- \+ *lemma* orientation.oangle_rotation_oangle_left
- \+ *lemma* orientation.oangle_rotation_oangle_right
- \+ *lemma* orientation.oangle_rotation_right
- \+ *lemma* orientation.oangle_rotation_self_left
- \+ *lemma* orientation.oangle_rotation_self_right
- \+ *lemma* orientation.oangle_self
- \+ *lemma* orientation.oangle_smul_left_of_neg
- \+ *lemma* orientation.oangle_smul_left_of_pos
- \+ *lemma* orientation.oangle_smul_left_self_of_nonneg
- \+ *lemma* orientation.oangle_smul_right_of_neg
- \+ *lemma* orientation.oangle_smul_right_of_pos
- \+ *lemma* orientation.oangle_smul_right_self_of_nonneg
- \+ *lemma* orientation.oangle_smul_smul_self_of_nonneg
- \+ *lemma* orientation.oangle_sub_eq_oangle_sub_rev_of_norm_eq
- \+ *lemma* orientation.oangle_sub_left
- \+ *lemma* orientation.oangle_sub_right
- \+ *lemma* orientation.oangle_zero_left
- \+ *lemma* orientation.oangle_zero_right
- \+ *def* orientation.rotation
- \+ *lemma* orientation.rotation_eq_basis_rotation
- \+ *lemma* orientation.rotation_eq_self_iff
- \+ *lemma* orientation.rotation_eq_self_iff_angle_eq_zero
- \+ *lemma* orientation.rotation_neg_orientation_eq_neg
- \+ *lemma* orientation.rotation_oangle_eq_iff_norm_eq
- \+ *lemma* orientation.rotation_pi
- \+ *lemma* orientation.rotation_symm
- \+ *lemma* orientation.rotation_trans
- \+ *lemma* orientation.rotation_zero
- \+ *lemma* orientation.two_zsmul_oangle_neg_left
- \+ *lemma* orientation.two_zsmul_oangle_neg_right
- \+ *lemma* orientation.two_zsmul_oangle_neg_self_left
- \+ *lemma* orientation.two_zsmul_oangle_neg_self_right
- \+ *lemma* orientation.two_zsmul_oangle_smul_left_of_ne_zero
- \+ *lemma* orientation.two_zsmul_oangle_smul_left_self
- \+ *lemma* orientation.two_zsmul_oangle_smul_right_of_ne_zero
- \+ *lemma* orientation.two_zsmul_oangle_smul_right_self
- \+ *lemma* orientation.two_zsmul_oangle_smul_smul_self
- \+ *lemma* orientation.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq



## [2022-02-27 10:57:38](https://github.com/leanprover-community/mathlib/commit/77e76ee)
feat(data/list/basic): add last'_append and head'_append_of_ne_nil ([#12221](https://github.com/leanprover-community/mathlib/pull/12221))
we already have `head'_append` and `last'_append_of_ne_nil`, and users
might expect a symmetric API.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.head'_append_of_ne_nil
- \+ *theorem* list.last'_append



## [2022-02-27 09:13:42](https://github.com/leanprover-community/mathlib/commit/b1c2d70)
feat(logic/function/basic): not_surjective_Type ([#12311](https://github.com/leanprover-community/mathlib/pull/12311))
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *theorem* function.not_surjective_Type



## [2022-02-27 08:45:41](https://github.com/leanprover-community/mathlib/commit/7ae0b36)
chore(category_theory/idempotents): minor suggestions ([#12303](https://github.com/leanprover-community/mathlib/pull/12303))
@joelriou, here are some minor suggestions on your earlier Karoubi envelope work (I wasn't around when the PR went through.)
The two separate suggestions are some typos, and dropping some unnecessary proofs.
#### Estimated changes
Modified src/category_theory/idempotents/basic.lean


Modified src/category_theory/idempotents/karoubi.lean




## [2022-02-27 06:00:11](https://github.com/leanprover-community/mathlib/commit/07374a2)
feat(set_theory/cardinal): add three_le ([#12225](https://github.com/leanprover-community/mathlib/pull/12225))
#### Estimated changes
Modified src/data/finset/card.lean
- \+ *lemma* finset.le_card_sdiff

Modified src/set_theory/cardinal.lean
- \+ *lemma* cardinal.exists_not_mem_of_length_le
- \+ *lemma* cardinal.three_le



## [2022-02-27 04:07:15](https://github.com/leanprover-community/mathlib/commit/86d686c)
feat(category_theory/category/Groupoid): Add coercion to sort ([#12324](https://github.com/leanprover-community/mathlib/pull/12324))
Use coercion to type instead of `.α`
#### Estimated changes
Modified src/category_theory/category/Groupoid.lean
- \+ *lemma* category_theory.Groupoid.coe_of

Modified src/topology/homotopy/fundamental_groupoid.lean
- \+/\- *def* fundamental_groupoid.from_top
- \+/\- *def* fundamental_groupoid.to_path
- \+/\- *def* fundamental_groupoid.to_top

Modified src/topology/homotopy/product.lean
- \+/\- *def* fundamental_groupoid_functor.pi_iso
- \+/\- *def* fundamental_groupoid_functor.pi_to_pi_Top
- \+/\- *def* fundamental_groupoid_functor.prod_iso
- \+/\- *def* fundamental_groupoid_functor.prod_to_prod_Top
- \+/\- *def* fundamental_groupoid_functor.proj
- \+/\- *def* fundamental_groupoid_functor.proj_left
- \+/\- *lemma* fundamental_groupoid_functor.proj_left_map
- \+/\- *lemma* fundamental_groupoid_functor.proj_map
- \+/\- *def* fundamental_groupoid_functor.proj_right
- \+/\- *lemma* fundamental_groupoid_functor.proj_right_map



## [2022-02-27 04:07:14](https://github.com/leanprover-community/mathlib/commit/907e5ba)
fix(set_theory/ordinal_arithmetic): Fix universes ([#12320](https://github.com/leanprover-community/mathlib/pull/12320))
`lsub_le_of_range_subset` and `lsub_eq_of_range_eq` should have had 3 universes, but they had only two.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean




## [2022-02-27 04:07:13](https://github.com/leanprover-community/mathlib/commit/906a88b)
feat(data/quot): primed quotient funcs on `mk` ([#12204](https://github.com/leanprover-community/mathlib/pull/12204))
#### Estimated changes
Modified src/data/quot.lean
- \+ *lemma* quotient.map'_mk



## [2022-02-27 02:45:05](https://github.com/leanprover-community/mathlib/commit/4afb8d2)
feat(set_theory/ordinal_arithmetic): Added missing theorems for `lsub` and `blsub` ([#12318](https://github.com/leanprover-community/mathlib/pull/12318))
These are the analogs of `lt_sup` and `lt_bsup`, respectively.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.lt_blsub_iff
- \+ *theorem* ordinal.lt_lsub_iff



## [2022-02-27 02:45:04](https://github.com/leanprover-community/mathlib/commit/bb9539c)
chore(set_theory/ordinal): Minor golf in `card` ([#12298](https://github.com/leanprover-community/mathlib/pull/12298))
This was suggested by @b-mehta.
#### Estimated changes
Modified src/set_theory/ordinal.lean




## [2022-02-27 02:45:02](https://github.com/leanprover-community/mathlib/commit/b4f87d9)
feat(analysis/normed_space): add `normed_space 𝕜 (uniform_space.completion E)` ([#12148](https://github.com/leanprover-community/mathlib/pull/12148))
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* lipschitz_with_smul

Added src/analysis/normed_space/completion.lean
- \+ *lemma* uniform_space.completion.coe_to_complL
- \+ *lemma* uniform_space.completion.coe_to_complₗᵢ
- \+ *lemma* uniform_space.completion.norm_to_complL
- \+ *def* uniform_space.completion.to_complL
- \+ *def* uniform_space.completion.to_complₗᵢ

Added src/topology/algebra/uniform_mul_action.lean
- \+ *lemma* uniform_continuous.const_smul
- \+ *lemma* uniform_space.completion.coe_smul

Modified src/topology/uniform_space/completion.lean
- \+ *lemma* uniform_space.completion.ext'



## [2022-02-27 01:14:05](https://github.com/leanprover-community/mathlib/commit/abf5dfc)
refactor(category_theory/eq_to_hom): conjugation by eq_to_hom same as heq ([#12025](https://github.com/leanprover-community/mathlib/pull/12025))
Xu Junyan provided this lemma for showing that `heq` gives the same as conjugation by `eq_to_hom` for equality of functor maps. I refactored `hext` using this result.
Then I added a bunch of lemmas for how `heq` interacts with composition of functors and `functor.map` applied to composition of morphisms
#### Estimated changes
Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* category_theory.functor.conj_eq_to_hom_iff_heq
- \+ *lemma* category_theory.functor.hcongr_hom
- \+ *lemma* category_theory.functor.map_comp_heq'
- \+ *lemma* category_theory.functor.map_comp_heq
- \+ *lemma* category_theory.functor.postcomp_map_heq'
- \+ *lemma* category_theory.functor.postcomp_map_heq
- \+ *lemma* category_theory.functor.precomp_map_heq



## [2022-02-27 01:14:04](https://github.com/leanprover-community/mathlib/commit/1fe9708)
feat(group_theory/nilpotent): is_nilpotent_of_product_of_sylow_group ([#11834](https://github.com/leanprover-community/mathlib/pull/11834))
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *theorem* is_nilpotent_of_product_of_sylow_group
- \+/\- *lemma* is_p_group.is_nilpotent
- \+ *lemma* nilpotent_of_mul_equiv



## [2022-02-26 23:31:58](https://github.com/leanprover-community/mathlib/commit/add068d)
chore(linear_algebra/orientation): split into 2 files ([#12302](https://github.com/leanprover-community/mathlib/pull/12302))
Move parts that don't need multilinear maps to a new file.
#### Estimated changes
Modified src/linear_algebra/orientation.lean
- \- *lemma* eq_zero_of_same_ray_self_neg
- \- *lemma* equiv_iff_same_ray
- \- *lemma* equivalence_same_ray
- \- *lemma* module.ray.ind
- \- *lemma* module.ray.linear_equiv_smul_eq_map
- \- *def* module.ray.map
- \- *lemma* module.ray.map_apply
- \- *lemma* module.ray.map_refl
- \- *lemma* module.ray.map_symm
- \- *lemma* module.ray.ne_neg_self
- \- *def* module.ray.some_ray_vector
- \- *lemma* module.ray.some_ray_vector_ray
- \- *def* module.ray.some_vector
- \- *lemma* module.ray.some_vector_ne_zero
- \- *lemma* module.ray.some_vector_ray
- \- *lemma* module.ray.units_smul_of_neg
- \- *lemma* module.ray.units_smul_of_pos
- \- *def* module.ray
- \- *lemma* ray_eq_iff
- \- *lemma* ray_neg
- \- *lemma* ray_pos_smul
- \- *lemma* ray_vector.coe_neg
- \- *lemma* ray_vector.equiv_neg_iff
- \- *def* ray_vector.map_linear_equiv
- \- *def* ray_vector.same_ray_setoid
- \- *def* ray_vector
- \- *lemma* same_ray.map
- \- *lemma* same_ray.neg
- \- *lemma* same_ray.pos_smul_left
- \- *lemma* same_ray.pos_smul_right
- \- *lemma* same_ray.refl
- \- *lemma* same_ray.smul
- \- *lemma* same_ray.symm
- \- *lemma* same_ray.trans
- \- *def* same_ray
- \- *lemma* same_ray_comm
- \- *lemma* same_ray_iff_mem_orbit
- \- *lemma* same_ray_map_iff
- \- *lemma* same_ray_neg_iff
- \- *lemma* same_ray_neg_smul_left_iff
- \- *lemma* same_ray_neg_smul_right_iff
- \- *lemma* same_ray_neg_swap
- \- *lemma* same_ray_of_mem_orbit
- \- *lemma* same_ray_pos_smul_left
- \- *lemma* same_ray_pos_smul_right
- \- *def* same_ray_setoid
- \- *lemma* same_ray_setoid_eq_orbit_rel
- \- *lemma* same_ray_smul_left_iff
- \- *lemma* same_ray_smul_right_iff
- \- *lemma* smul_ray_of_ne_zero
- \- *lemma* units_inv_smul
- \- *lemma* units_smul_eq_neg_iff
- \- *lemma* units_smul_eq_self_iff

Added src/linear_algebra/ray.lean
- \+ *lemma* eq_zero_of_same_ray_self_neg
- \+ *lemma* equiv_iff_same_ray
- \+ *lemma* equivalence_same_ray
- \+ *lemma* module.ray.ind
- \+ *lemma* module.ray.linear_equiv_smul_eq_map
- \+ *def* module.ray.map
- \+ *lemma* module.ray.map_apply
- \+ *lemma* module.ray.map_refl
- \+ *lemma* module.ray.map_symm
- \+ *lemma* module.ray.ne_neg_self
- \+ *def* module.ray.some_ray_vector
- \+ *lemma* module.ray.some_ray_vector_ray
- \+ *def* module.ray.some_vector
- \+ *lemma* module.ray.some_vector_ne_zero
- \+ *lemma* module.ray.some_vector_ray
- \+ *lemma* module.ray.units_smul_of_neg
- \+ *lemma* module.ray.units_smul_of_pos
- \+ *def* module.ray
- \+ *lemma* ray_eq_iff
- \+ *lemma* ray_neg
- \+ *lemma* ray_pos_smul
- \+ *lemma* ray_vector.coe_neg
- \+ *lemma* ray_vector.equiv_neg_iff
- \+ *def* ray_vector.map_linear_equiv
- \+ *def* ray_vector.same_ray_setoid
- \+ *def* ray_vector
- \+ *lemma* same_ray.map
- \+ *lemma* same_ray.neg
- \+ *lemma* same_ray.pos_smul_left
- \+ *lemma* same_ray.pos_smul_right
- \+ *lemma* same_ray.refl
- \+ *lemma* same_ray.smul
- \+ *lemma* same_ray.symm
- \+ *lemma* same_ray.trans
- \+ *def* same_ray
- \+ *lemma* same_ray_comm
- \+ *lemma* same_ray_iff_mem_orbit
- \+ *lemma* same_ray_map_iff
- \+ *lemma* same_ray_neg_iff
- \+ *lemma* same_ray_neg_smul_left_iff
- \+ *lemma* same_ray_neg_smul_right_iff
- \+ *lemma* same_ray_neg_swap
- \+ *lemma* same_ray_of_mem_orbit
- \+ *lemma* same_ray_pos_smul_left
- \+ *lemma* same_ray_pos_smul_right
- \+ *def* same_ray_setoid
- \+ *lemma* same_ray_setoid_eq_orbit_rel
- \+ *lemma* same_ray_smul_left_iff
- \+ *lemma* same_ray_smul_right_iff
- \+ *lemma* smul_ray_of_ne_zero
- \+ *lemma* units_inv_smul
- \+ *lemma* units_smul_eq_neg_iff
- \+ *lemma* units_smul_eq_self_iff



## [2022-02-26 23:31:57](https://github.com/leanprover-community/mathlib/commit/188b371)
feat(algebra/category/GroupWithZero): The category of groups with zero ([#12278](https://github.com/leanprover-community/mathlib/pull/12278))
Define `GroupWithZero`, the category of groups with zero with monoid with zero homs.
#### Estimated changes
Added src/algebra/category/GroupWithZero.lean
- \+ *def* GroupWithZero.iso.mk
- \+ *def* GroupWithZero.of
- \+ *def* GroupWithZero

Modified src/data/equiv/mul_add.lean




## [2022-02-26 23:31:55](https://github.com/leanprover-community/mathlib/commit/163d1a6)
feat(category_theory/idempotents): idempotent completeness and functor categories ([#12270](https://github.com/leanprover-community/mathlib/pull/12270))
#### Estimated changes
Added src/category_theory/idempotents/functor_categories.lean
- \+ *def* category_theory.idempotents.karoubi_functor_category_embedding.map
- \+ *def* category_theory.idempotents.karoubi_functor_category_embedding.obj
- \+ *def* category_theory.idempotents.karoubi_functor_category_embedding
- \+ *lemma* category_theory.idempotents.to_karoubi_comp_karoubi_functor_category_embedding

Added src/category_theory/idempotents/simplicial_object.lean




## [2022-02-26 23:31:53](https://github.com/leanprover-community/mathlib/commit/817b4c4)
feat(order/category/BoundedLattice): The category of bounded lattices ([#12257](https://github.com/leanprover-community/mathlib/pull/12257))
Define `BoundedLattice`, the category of bounded lattices with bounded lattice homs.
#### Estimated changes
Added src/order/category/BoundedLattice.lean
- \+ *def* BoundedLattice.dual
- \+ *def* BoundedLattice.dual_equiv
- \+ *lemma* BoundedLattice.forget_Lattice_PartialOrder_eq_forget_BoundedOrder_PartialOrder
- \+ *def* BoundedLattice.iso.mk
- \+ *def* BoundedLattice.of
- \+ *structure* BoundedLattice
- \+ *lemma* BoundedLattice_dual_comp_forget_to_BoundedOrder
- \+ *lemma* BoundedLattice_dual_comp_forget_to_Lattice

Modified src/order/hom/lattice.lean




## [2022-02-26 22:03:39](https://github.com/leanprover-community/mathlib/commit/3d8c22f)
refactor(topology/compact_open): Remove `locally_compact_space` hypothesis in `continuous_map.t2_space` ([#12306](https://github.com/leanprover-community/mathlib/pull/12306))
This PR removes the `locally_compact_space` hypothesis in `continuous_map.t2_space`, at the cost of a longer proof.
#### Estimated changes
Modified src/topology/algebra/continuous_monoid_hom.lean


Modified src/topology/compact_open.lean




## [2022-02-26 20:55:45](https://github.com/leanprover-community/mathlib/commit/4cf0e60)
feat(category_theory/limits): generalize has_biproduct.of_has_product  ([#12116](https://github.com/leanprover-community/mathlib/pull/12116))
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.bicone_is_bilimit_of_colimit_cocone_of_is_colimit
- \+ *def* category_theory.limits.bicone_is_bilimit_of_limit_cone_of_is_limit
- \+ *lemma* category_theory.limits.binary_bicone.binary_cofan_inl_to_cocone
- \+ *lemma* category_theory.limits.binary_bicone.binary_cofan_inr_to_cocone
- \+ *lemma* category_theory.limits.binary_bicone.binary_fan_fst_to_cone
- \+ *lemma* category_theory.limits.binary_bicone.binary_fan_snd_to_cone
- \+ *def* category_theory.limits.binary_bicone.of_colimit_cocone
- \+ *def* category_theory.limits.binary_bicone.of_limit_cone
- \+ *def* category_theory.limits.binary_bicone_is_bilimit_of_colimit_cocone_of_is_colimit
- \+ *def* category_theory.limits.binary_bicone_is_bilimit_of_limit_cone_of_is_limit
- \+ *lemma* category_theory.limits.fst_of_is_colimit
- \+/\- *lemma* category_theory.limits.has_biproduct.of_has_coproduct
- \+/\- *lemma* category_theory.limits.has_biproduct.of_has_product
- \+ *lemma* category_theory.limits.inl_of_is_limit
- \+ *lemma* category_theory.limits.inr_of_is_limit
- \+ *def* category_theory.limits.is_bilimit_of_is_colimit
- \+ *def* category_theory.limits.is_bilimit_of_is_limit
- \+ *def* category_theory.limits.is_bilimit_of_total
- \+ *def* category_theory.limits.is_binary_bilimit_of_is_colimit
- \+ *def* category_theory.limits.is_binary_bilimit_of_is_limit
- \+ *def* category_theory.limits.is_binary_bilimit_of_total
- \+ *lemma* category_theory.limits.snd_of_is_colimit



## [2022-02-26 20:55:44](https://github.com/leanprover-community/mathlib/commit/09ba530)
feat(category_theory/limits): biproducts are unique up to iso ([#12114](https://github.com/leanprover-community/mathlib/pull/12114))
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* category_theory.limits.biprod.cone_point_unique_up_to_iso_hom
- \+ *lemma* category_theory.limits.biprod.cone_point_unique_up_to_iso_inv
- \+ *def* category_theory.limits.biprod.unique_up_to_iso
- \+ *lemma* category_theory.limits.biproduct.cone_point_unique_up_to_iso_hom
- \+ *lemma* category_theory.limits.biproduct.cone_point_unique_up_to_iso_inv
- \+ *def* category_theory.limits.biproduct.unique_up_to_iso



## [2022-02-26 20:23:50](https://github.com/leanprover-community/mathlib/commit/fe6ea3e)
feat(analysis/convex/integral): strict Jensen's inequality ([#11552](https://github.com/leanprover-community/mathlib/pull/11552))
#### Estimated changes
Modified src/analysis/convex/integral.lean
- \+ *lemma* convex.average_mem_interior_of_set
- \+ *lemma* measure_theory.integrable.ae_eq_const_or_exists_average_ne_compl
- \+ *lemma* strict_concave_on.ae_eq_const_or_lt_map_average
- \+ *lemma* strict_convex.ae_eq_const_or_average_mem_interior
- \+ *lemma* strict_convex.ae_eq_const_or_norm_integral_lt_of_norm_le_const
- \+ *lemma* strict_convex_on.ae_eq_const_or_map_average_lt



## [2022-02-26 19:39:04](https://github.com/leanprover-community/mathlib/commit/c8150cc)
feat(analysis/normed_space/add_torsor): `dist` and `line_map` ([#12265](https://github.com/leanprover-community/mathlib/pull/12265))
Add a few lemmas about the distance between `line_map p₁ p₂ c₁` and
`line_map p₁ p₂ c₂`.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* dist_left_line_map
- \+ *lemma* dist_line_map_left
- \+ *lemma* dist_line_map_line_map
- \+ *lemma* dist_line_map_right
- \+ *lemma* dist_right_line_map
- \+ *lemma* lipschitz_with_line_map



## [2022-02-26 16:53:59](https://github.com/leanprover-community/mathlib/commit/3b49fe2)
feat(algebra/star/pointwise, algebra/star/basic): add pointwise star, and a few convenience lemmas ([#12290](https://github.com/leanprover-community/mathlib/pull/12290))
This adds a star operation to sets in the pointwise locale and establishes the basic properties. The names and proofs were taken from the corresponding ones for `inv`. A few extras were added.
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+ *lemma* eq_star_iff_eq_star
- \+ *lemma* eq_star_of_eq_star
- \+ *lemma* star_eq_iff_star_eq

Added src/algebra/star/pointwise.lean
- \+ *lemma* set.Inter_star
- \+ *lemma* set.Union_star
- \+ *lemma* set.compl_star
- \+ *lemma* set.finite.star
- \+ *lemma* set.image_star
- \+ *lemma* set.inter_star
- \+ *lemma* set.mem_star
- \+ *lemma* set.nonempty.star
- \+ *lemma* set.nonempty_star
- \+ *lemma* set.star_empty
- \+ *lemma* set.star_mem_star
- \+ *lemma* set.star_preimage
- \+ *lemma* set.star_singleton
- \+ *lemma* set.star_subset
- \+ *lemma* set.star_subset_star
- \+ *lemma* set.star_univ
- \+ *lemma* set.union_star



## [2022-02-26 16:18:11](https://github.com/leanprover-community/mathlib/commit/87fc3ea)
feat(analysis/normed_space/star/spectrum): prove the spectrum of a unitary element in a C*-algebra is a subset of the unit sphere ([#12238](https://github.com/leanprover-community/mathlib/pull/12238))
The spectrum of a unitary element in a C*-algebra is a subset of the unit sphere in the scalar field. This will be used to show that the spectrum of selfadjoint elements is real-valued.
#### Estimated changes
Modified src/analysis/normed_space/star/spectrum.lean
- \+ *lemma* spectrum.subset_circle_of_unitary
- \+ *lemma* unitary.spectrum_subset_circle



## [2022-02-26 13:23:26](https://github.com/leanprover-community/mathlib/commit/0f1bc2c)
feat(topology,analysis): any function is continuous/differentiable on a subsingleton ([#12293](https://github.com/leanprover-community/mathlib/pull/12293))
Also add supporting lemmas about `is_o`/`is_O` and the `pure` filter
and drop an unneeded assumption in `asymptotics.is_o_const_const_iff`.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *theorem* asymptotics.is_O_const_const_iff
- \+ *lemma* asymptotics.is_O_pure
- \+ *theorem* asymptotics.is_O_with_pure
- \+/\- *theorem* asymptotics.is_o_const_const_iff
- \+ *lemma* asymptotics.is_o_pure

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* differentiable_on_empty
- \+ *lemma* differentiable_on_singleton
- \+/\- *lemma* has_fderiv_at_of_subsingleton
- \+ *lemma* has_fderiv_within_at_singleton
- \+ *lemma* set.subsingleton.differentiable_on

Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on_singleton
- \+ *lemma* set.subsingleton.continuous_on



## [2022-02-26 11:40:32](https://github.com/leanprover-community/mathlib/commit/bfc0584)
refactor(topology,analysis): use `maps_to` in lemmas like `continuous_on.comp` ([#12294](https://github.com/leanprover-community/mathlib/pull/12294))
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/normed_space/basic.lean


Modified src/data/set/function.lean
- \+/\- *theorem* set.maps_to.mono
- \+ *theorem* set.maps_to.mono_left
- \+ *theorem* set.maps_to.mono_right

Modified src/dynamics/omega_limit.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* model_with_corners.continuous_on_symm

Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/topology/continuous_on.lean


Modified src/topology/fiber_bundle.lean




## [2022-02-26 11:03:49](https://github.com/leanprover-community/mathlib/commit/d2d6f17)
feat(analysis/inner_product_space/spectrum): `has_eigenvalue_eigenvalues` ([#12304](https://github.com/leanprover-community/mathlib/pull/12304))
similar to the existing `has_eigenvector_eigenvector_basis`
#### Estimated changes
Modified src/analysis/inner_product_space/spectrum.lean
- \+ *lemma* inner_product_space.is_self_adjoint.has_eigenvalue_eigenvalues



## [2022-02-26 03:29:04](https://github.com/leanprover-community/mathlib/commit/d6a8e5d)
feat(topology/compact_open): `simp`-lemmas for `compact_open.gen` ([#12267](https://github.com/leanprover-community/mathlib/pull/12267))
This PR adds some basic `simp`-lemmas for `compact_open.gen`.
#### Estimated changes
Modified src/topology/compact_open.lean
- \+ *lemma* continuous_map.gen_empty
- \+ *lemma* continuous_map.gen_inter
- \+ *lemma* continuous_map.gen_union
- \+ *lemma* continuous_map.gen_univ



## [2022-02-26 03:29:03](https://github.com/leanprover-community/mathlib/commit/7201c3b)
feat(category_theory/limits): more opposite-related transformations of cones ([#12165](https://github.com/leanprover-community/mathlib/pull/12165))
#### Estimated changes
Modified src/category_theory/limits/cones.lean
- \+ *def* category_theory.limits.cocone_of_cone_right_op
- \+ *def* category_theory.limits.cocone_of_cone_unop
- \+ *def* category_theory.limits.cocone_right_op_of_cone
- \+ *def* category_theory.limits.cocone_unop_of_cone
- \+ *def* category_theory.limits.cone_of_cocone_right_op
- \+ *def* category_theory.limits.cone_of_cocone_unop
- \+ *def* category_theory.limits.cone_right_op_of_cocone
- \+ *def* category_theory.limits.cone_unop_of_cocone

Modified src/category_theory/limits/opposites.lean


Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean




## [2022-02-26 02:44:14](https://github.com/leanprover-community/mathlib/commit/43fb516)
doc(analysis/normed_space): fixed normed_star_monoid doc-string ([#12296](https://github.com/leanprover-community/mathlib/pull/12296))
#### Estimated changes
Modified src/analysis/normed_space/star/basic.lean




## [2022-02-25 22:23:16](https://github.com/leanprover-community/mathlib/commit/05d8188)
feat(group_theory/torsion): define torsion groups ([#11850](https://github.com/leanprover-community/mathlib/pull/11850))
I grepped for torsion group and didn't find anything -- hopefully adding this makes sense here.
#### Estimated changes
Modified src/group_theory/exponent.lean
- \+/\- *lemma* monoid.exponent_eq_zero_iff
- \+ *lemma* monoid.exponent_exists_iff_ne_zero

Modified src/group_theory/order_of_element.lean
- \+ *lemma* is_of_fin_order.quotient
- \+ *lemma* is_of_fin_order_iff_coe

Added src/group_theory/torsion.lean
- \+ *lemma* exponent_exists.is_torsion
- \+ *lemma* is_torsion.exponent_exists
- \+ *lemma* is_torsion.quotient_group
- \+ *lemma* is_torsion.subgroup
- \+ *lemma* is_torsion_of_fintype
- \+ *def* monoid.is_torsion



## [2022-02-25 20:13:56](https://github.com/leanprover-community/mathlib/commit/3cc9ac4)
feat(analysis/normed_space/finite_dimension): add a lemma about `inf_dist` ([#12282](https://github.com/leanprover-community/mathlib/pull/12282))
Add a version of `exists_mem_frontier_inf_dist_compl_eq_dist` for a
compact set in a real normed space. This version does not assume that
the ambient space is finite dimensional.
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean
- \+/\- *theorem* finite_dimensional_of_is_compact_closed_ball
- \+ *theorem* finite_dimensional_of_is_compact_closed_ball₀
- \+ *lemma* is_compact.exists_mem_frontier_inf_dist_compl_eq_dist

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* metric.inf_dist_zero_of_mem_closure



## [2022-02-25 18:50:04](https://github.com/leanprover-community/mathlib/commit/c127fc3)
chore(measure_theory/decomposition/lebesgue): tidy a proof ([#12274](https://github.com/leanprover-community/mathlib/pull/12274))
There's no need to go through `set_integral_re_add_im` when all we need is `integral_re`.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* is_R_or_C.im_eq_complex_im
- \+ *lemma* is_R_or_C.re_eq_complex_re

Modified src/measure_theory/decomposition/lebesgue.lean




## [2022-02-25 16:56:48](https://github.com/leanprover-community/mathlib/commit/6653544)
feat(topology/algebra/order/extr): extr on closure ([#12281](https://github.com/leanprover-community/mathlib/pull/12281))
Prove `is_max_on.closure` etc
#### Estimated changes
Added src/topology/algebra/order/extr_closure.lean




## [2022-02-25 10:18:16](https://github.com/leanprover-community/mathlib/commit/8c485a4)
feat(order/filter/extr): add `is_*_on.comp_maps_to` ([#12280](https://github.com/leanprover-community/mathlib/pull/12280))
#### Estimated changes
Modified src/order/filter/extr.lean
- \+ *lemma* is_extr_on.comp_maps_to
- \+ *lemma* is_max_on.comp_maps_to
- \+ *lemma* is_min_on.comp_maps_to



## [2022-02-25 07:39:47](https://github.com/leanprover-community/mathlib/commit/c1443d6)
feat(ring_theory/localization): random lemmata for edge cases ([#12146](https://github.com/leanprover-community/mathlib/pull/12146))
#### Estimated changes
Modified src/logic/unique.lean
- \+ *lemma* unique.bijective

Modified src/ring_theory/localization/basic.lean


Modified src/ring_theory/localization/fraction_ring.lean




## [2022-02-25 07:07:50](https://github.com/leanprover-community/mathlib/commit/dae1dfe)
feat(topology/spectral/hom): Spectral maps ([#12228](https://github.com/leanprover-community/mathlib/pull/12228))
Define spectral maps in three ways:
* `is_spectral_map`, the unbundled predicate
* `spectral_map`, the bundled type
* `spectral_map_class`, the hom class
The design for `is_spectral_map` matches `continuous`. The design for `spectral_map` and `spectral_map_class` follows the hom refactor.
#### Estimated changes
Added src/topology/spectral/hom.lean
- \+ *lemma* is_compact.preimage_of_open
- \+ *lemma* is_spectral_map.comp
- \+ *lemma* is_spectral_map.continuous
- \+ *structure* is_spectral_map
- \+ *lemma* is_spectral_map_id
- \+ *lemma* spectral_map.cancel_left
- \+ *lemma* spectral_map.cancel_right
- \+ *lemma* spectral_map.coe_comp
- \+ *lemma* spectral_map.coe_comp_continuous_map
- \+ *lemma* spectral_map.coe_id
- \+ *def* spectral_map.comp
- \+ *lemma* spectral_map.comp_apply
- \+ *lemma* spectral_map.comp_assoc
- \+ *lemma* spectral_map.comp_id
- \+ *lemma* spectral_map.ext
- \+ *lemma* spectral_map.id_apply
- \+ *lemma* spectral_map.id_comp
- \+ *def* spectral_map.to_continuous_map
- \+ *lemma* spectral_map.to_fun_eq_coe
- \+ *structure* spectral_map



## [2022-02-25 05:25:18](https://github.com/leanprover-community/mathlib/commit/f2fdef6)
feat(order/partition/equipartition): Equipartitions ([#12023](https://github.com/leanprover-community/mathlib/pull/12023))
Define `finpartition.is_equipartition`, a predicate for saying that the parts of a `finpartition` of a `finset` are all the same size up to a difference of `1`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.subsingleton_of_subset_singleton

Modified src/data/set/equitable.lean
- \+ *lemma* finset.equitable_on.le
- \+ *lemma* finset.equitable_on.le_add_one
- \+/\- *lemma* finset.equitable_on_iff
- \+/\- *lemma* finset.equitable_on_iff_le_le_add_one

Added src/order/partition/equipartition.lean
- \+ *lemma* finpartition.bot_is_equipartition
- \+ *lemma* finpartition.indiscrete_is_equipartition
- \+ *lemma* finpartition.is_equipartition.average_le_card_part
- \+ *lemma* finpartition.is_equipartition.card_part_le_average_add_one
- \+ *def* finpartition.is_equipartition
- \+ *lemma* finpartition.is_equipartition_iff_card_parts_eq_average
- \+ *lemma* finpartition.top_is_equipartition
- \+ *lemma* set.subsingleton.is_equipartition

Modified src/order/partition/finpartition.lean
- \+ *lemma* finpartition.parts_top_subset
- \+ *lemma* finpartition.parts_top_subsingleton



## [2022-02-25 03:05:10](https://github.com/leanprover-community/mathlib/commit/605ea9f)
feat(algebra/symmetrized): Define the symmetrization of a ring ([#11399](https://github.com/leanprover-community/mathlib/pull/11399))
A commutative multiplication on a real or complex space can be constructed from any multiplication by
"symmetrisation" i.e
```
a∘b = 1/2(ab+ba).
```
The approach taken here is inspired by `algebra.opposites`.
Previously submitted as part of [#11073](https://github.com/leanprover-community/mathlib/pull/11073).
Will be used in https://github.com/leanprover-community/mathlib/pull/11401
#### Estimated changes
Modified docs/references.bib


Added src/algebra/symmetrized.lean
- \+ *lemma* sym_alg.inv_of_sym
- \+ *lemma* sym_alg.mul_comm
- \+ *lemma* sym_alg.mul_def
- \+ *def* sym_alg.sym
- \+ *lemma* sym_alg.sym_add
- \+ *lemma* sym_alg.sym_bijective
- \+ *lemma* sym_alg.sym_comp_unsym
- \+ *lemma* sym_alg.sym_eq_one_iff
- \+ *def* sym_alg.sym_equiv
- \+ *lemma* sym_alg.sym_inj
- \+ *lemma* sym_alg.sym_injective
- \+ *lemma* sym_alg.sym_inv
- \+ *lemma* sym_alg.sym_mul_self
- \+ *lemma* sym_alg.sym_mul_sym
- \+ *lemma* sym_alg.sym_ne_one_iff
- \+ *lemma* sym_alg.sym_neg
- \+ *lemma* sym_alg.sym_one
- \+ *lemma* sym_alg.sym_smul
- \+ *lemma* sym_alg.sym_sub
- \+ *lemma* sym_alg.sym_surjective
- \+ *lemma* sym_alg.sym_unsym
- \+ *def* sym_alg.unsym
- \+ *lemma* sym_alg.unsym_add
- \+ *lemma* sym_alg.unsym_bijective
- \+ *lemma* sym_alg.unsym_comp_sym
- \+ *lemma* sym_alg.unsym_eq_one_iff
- \+ *lemma* sym_alg.unsym_inj
- \+ *lemma* sym_alg.unsym_injective
- \+ *lemma* sym_alg.unsym_inv
- \+ *lemma* sym_alg.unsym_mul
- \+ *lemma* sym_alg.unsym_mul_self
- \+ *lemma* sym_alg.unsym_ne_one_iff
- \+ *lemma* sym_alg.unsym_neg
- \+ *lemma* sym_alg.unsym_one
- \+ *lemma* sym_alg.unsym_smul
- \+ *lemma* sym_alg.unsym_sub
- \+ *lemma* sym_alg.unsym_surjective
- \+ *lemma* sym_alg.unsym_sym
- \+ *def* sym_alg



## [2022-02-24 20:01:42](https://github.com/leanprover-community/mathlib/commit/f7518db)
chore(topology/continuous_function/bounded): add an is_central_scalar instance ([#12272](https://github.com/leanprover-community/mathlib/pull/12272))
This is only possible very recently now that `𝕜ᵐᵒᵖ` has a metric space instance.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean




## [2022-02-24 20:01:41](https://github.com/leanprover-community/mathlib/commit/feb5473)
chore(*): update to 3.40.0c ([#12212](https://github.com/leanprover-community/mathlib/pull/12212))
#### Estimated changes
Modified leanpkg.toml


Modified src/analysis/asymptotics/asymptotic_equivalent.lean


Modified src/combinatorics/configuration.lean




## [2022-02-24 18:24:37](https://github.com/leanprover-community/mathlib/commit/d3d3701)
feat(analysis/mean_inequalities): AM and GM are equal on a constant tuple ([#12179](https://github.com/leanprover-community/mathlib/pull/12179))
The converse is also true, but I have not gotten around to proving it.
#### Estimated changes
Modified src/analysis/mean_inequalities.lean
- \+ *theorem* real.arith_mean_weighted_of_constant
- \+ *theorem* real.geom_mean_eq_arith_mean_weighted_of_constant
- \+ *theorem* real.geom_mean_weighted_of_constant

Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* real.rpow_add'
- \+/\- *lemma* real.rpow_add
- \+ *lemma* real.rpow_add_of_nonneg
- \+ *lemma* real.rpow_sum_of_nonneg
- \+ *lemma* real.rpow_sum_of_pos

Modified src/data/finset/basic.lean
- \+ *lemma* finset.filter_nonempty_iff
- \+ *lemma* finset.forall_mem_cons
- \+ *lemma* finset.mem_of_mem_filter



## [2022-02-24 16:20:33](https://github.com/leanprover-community/mathlib/commit/d620395)
feat(topology/algebra/group): homeomorphisms for div ([#12251](https://github.com/leanprover-community/mathlib/pull/12251))
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *def* homeomorph.div_left
- \+ *def* homeomorph.div_right



## [2022-02-24 16:20:32](https://github.com/leanprover-community/mathlib/commit/ed9f73c)
feat(order/conditionally_complete_lattice.lean): two new lemmas ([#12250](https://github.com/leanprover-community/mathlib/pull/12250))
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* cinfi_set_le
- \+ *lemma* le_csupr_set



## [2022-02-24 14:39:01](https://github.com/leanprover-community/mathlib/commit/0840629)
test(instance_diamonds): verify that restrict_scalars produces no diamonds on the complex numbers ([#12273](https://github.com/leanprover-community/mathlib/pull/12273))
There is already a comment on `complex.module` that indicates an intentional solution to this diamond.
#### Estimated changes
Modified test/instance_diamonds.lean




## [2022-02-24 14:38:59](https://github.com/leanprover-community/mathlib/commit/a0d2c43)
feat(algebra/punit_instances): mul_semiring_action ([#12271](https://github.com/leanprover-community/mathlib/pull/12271))
The timeouts mentioned in the file appear to no longer occur.
#### Estimated changes
Modified src/algebra/punit_instances.lean




## [2022-02-24 14:38:57](https://github.com/leanprover-community/mathlib/commit/9dca6f4)
feat(topology/metric_space/lipschitz): add `set.maps_to` lemmas ([#12266](https://github.com/leanprover-community/mathlib/pull/12266))
#### Estimated changes
Modified src/topology/metric_space/lipschitz.lean
- \+/\- *lemma* lipschitz_with.bounded_image
- \+/\- *lemma* lipschitz_with.diam_image_le
- \+ *lemma* lipschitz_with.dist_le_mul_of_le
- \+ *lemma* lipschitz_with.dist_lt_mul_of_lt
- \+ *lemma* lipschitz_with.edist_le_mul_of_le
- \+ *lemma* lipschitz_with.edist_lt_mul_of_lt
- \+ *lemma* lipschitz_with.maps_to_ball
- \+ *lemma* lipschitz_with.maps_to_closed_ball
- \+ *lemma* lipschitz_with.maps_to_emetric_ball
- \+ *lemma* lipschitz_with.maps_to_emetric_closed_ball
- \+/\- *lemma* lipschitz_with.nndist_le



## [2022-02-24 14:38:55](https://github.com/leanprover-community/mathlib/commit/d011bf2)
chore(measure_theory/function/uniform_integrable): replace `ℕ` by a type verifying enough assumptions ([#12242](https://github.com/leanprover-community/mathlib/pull/12242))
This PR does not generalize the results of the `uniform_integrable` file much, but using a generic type instead of `ℕ` makes clear where we need assumptions like `encodable`.
#### Estimated changes
Modified src/measure_theory/function/uniform_integrable.lean
- \+/\- *lemma* measure_theory.egorov.measure_inter_not_convergent_seq_eq_zero
- \+/\- *lemma* measure_theory.egorov.measure_not_convergent_seq_tendsto_zero
- \+/\- *lemma* measure_theory.egorov.mem_not_convergent_seq_iff
- \+/\- *def* measure_theory.egorov.not_convergent_seq
- \+/\- *lemma* measure_theory.egorov.not_convergent_seq_antitone
- \+/\- *lemma* measure_theory.egorov.not_convergent_seq_measurable_set



## [2022-02-24 14:38:54](https://github.com/leanprover-community/mathlib/commit/34cfcd0)
feat(probability/stopping): generalize `is_stopping_time.measurable_set_lt` and variants beyond `ℕ` ([#12240](https://github.com/leanprover-community/mathlib/pull/12240))
The lemma `is_stopping_time.measurable_set_lt` and the similar results for gt, ge and eq were written for stopping times with value in nat. We generalize those results to linear orders with the order topology.
#### Estimated changes
Modified src/order/bounds.lean
- \+ *lemma* exists_glb_Ioi
- \+ *lemma* exists_lub_Iio
- \+ *lemma* glb_Ioi_eq_self_or_Ioi_eq_Ici
- \+ *lemma* le_glb_Ioi
- \+ *lemma* lub_Iio_eq_self_or_Iio_eq_Iic
- \+ *lemma* lub_Iio_le

Modified src/probability/stopping.lean
- \+ *lemma* measure_theory.filtration.const_apply
- \+/\- *lemma* measure_theory.is_stopping_time.add_const
- \+/\- *lemma* measure_theory.is_stopping_time.measurable_set_eq
- \+/\- *lemma* measure_theory.is_stopping_time.measurable_set_eq_le
- \+/\- *lemma* measure_theory.is_stopping_time.measurable_set_ge
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_gt
- \+/\- *lemma* measure_theory.is_stopping_time.measurable_set_le
- \+/\- *lemma* measure_theory.is_stopping_time.measurable_set_lt
- \+/\- *lemma* measure_theory.is_stopping_time.measurable_set_lt_le
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_lt_of_is_lub
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_lt_of_pred
- \+/\- *def* measure_theory.is_stopping_time
- \+/\- *lemma* measure_theory.is_stopping_time_const
- \+/\- *lemma* measure_theory.is_stopping_time_of_measurable_set_eq
- \+/\- *lemma* measure_theory.measurable_set_of_filtration



## [2022-02-24 12:56:59](https://github.com/leanprover-community/mathlib/commit/79887c9)
feat(measure_theory/group/prod): generalize topological groups to measurable groups ([#11933](https://github.com/leanprover-community/mathlib/pull/11933))
* This fixes the gap in `[Halmos]` that I mentioned in `measure_theory.group.prod`
* Thanks to @sgouezel for giving me the proof to fill that gap.
* A text proof to fill the gap is [here](https://math.stackexchange.com/a/4387664/463377)
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* set.mul_indicator_image

Modified src/measure_theory/group/measure.lean


Modified src/measure_theory/group/prod.lean
- \+ *lemma* measure_theory.absolutely_continuous_of_is_mul_left_invariant
- \+ *lemma* measure_theory.ae_measure_preimage_mul_right_lt_top
- \+ *lemma* measure_theory.ae_measure_preimage_mul_right_lt_top_of_ne_zero
- \+ *lemma* measure_theory.measure_eq_div_smul
- \+/\- *lemma* measure_theory.measure_lintegral_div_measure
- \+ *lemma* measure_theory.measure_mul_lintegral_eq
- \+/\- *lemma* measure_theory.measure_mul_measure_eq

Modified src/measure_theory/measure/haar.lean


Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measurable_equiv.sigma_finite_map
- \+ *lemma* measure_theory.ae_of_forall_measure_lt_top_ae_restrict'



## [2022-02-24 12:56:58](https://github.com/leanprover-community/mathlib/commit/8429ec9)
feat(topology/vector_bundle): `topological_vector_prebundle` ([#8154](https://github.com/leanprover-community/mathlib/pull/8154))
In this PR we implement a new standard construction for topological vector bundles: namely a structure that permits to define a vector bundle when trivializations are given as local equivalences but there is not yet a topology on the total space. The total space is hence given a topology in such a way that there is a vector bundle structure for which the local equivalences
are also local homeomorphism and hence local trivializations.
#### Estimated changes
Modified src/data/bundle.lean
- \+/\- *def* bundle.proj

Modified src/data/set/function.lean
- \+ *lemma* set.restrict_comp_cod_restrict

Modified src/topology/constructions.lean
- \+ *lemma* continuous.cod_restrict
- \+ *lemma* inducing.of_cod_restrict
- \+ *lemma* inducing_coe

Modified src/topology/fiber_bundle.lean


Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.continuous_iff_continuous_comp_left

Modified src/topology/vector_bundle.lean
- \+ *structure* topological_vector_bundle.pretrivialization
- \+ *def* topological_vector_bundle.trivialization.to_pretrivialization
- \+ *lemma* topological_vector_prebundle.continuous_total_space_mk
- \+ *lemma* topological_vector_prebundle.inducing_total_space_mk_of_inducing_comp
- \+ *lemma* topological_vector_prebundle.mem_trivialization_at_source
- \+ *def* topological_vector_prebundle.to_topological_fiber_prebundle
- \+ *lemma* topological_vector_prebundle.to_topological_vector_bundle
- \+ *lemma* topological_vector_prebundle.total_space_mk_preimage_source
- \+ *def* topological_vector_prebundle.total_space_topology
- \+ *def* topological_vector_prebundle.trivialization_at
- \+ *structure* topological_vector_prebundle



## [2022-02-24 11:57:32](https://github.com/leanprover-community/mathlib/commit/76b1e01)
feat(data/equiv/option): option_congr ([#12263](https://github.com/leanprover-community/mathlib/pull/12263))
This is a universe-polymorphic version of the existing `equiv_functor.map_equiv option`.
#### Estimated changes
Modified src/combinatorics/derangements/basic.lean


Modified src/data/equiv/option.lean
- \+ *def* equiv.option_congr
- \+ *lemma* equiv.option_congr_eq_equiv_function_map_equiv
- \+ *lemma* equiv.option_congr_injective
- \+ *lemma* equiv.option_congr_refl
- \+ *lemma* equiv.option_congr_symm
- \+ *lemma* equiv.option_congr_trans
- \- *lemma* equiv.remove_none_map_equiv
- \+ *lemma* equiv.remove_none_option_congr

Modified src/group_theory/perm/option.lean
- \+ *lemma* equiv.option_congr_one
- \+ *lemma* equiv.option_congr_sign
- \+ *lemma* equiv.option_congr_swap
- \- *lemma* equiv_functor.map_equiv_option_injective
- \- *lemma* equiv_functor.option.map_none
- \- *lemma* equiv_functor.option.sign
- \- *lemma* map_equiv_option_one
- \- *lemma* map_equiv_option_refl
- \- *lemma* map_equiv_option_swap



## [2022-02-24 11:57:31](https://github.com/leanprover-community/mathlib/commit/b8b1b57)
chore(geometry/euclidean): split repetitive proof ([#12209](https://github.com/leanprover-community/mathlib/pull/12209))
This PR is part of the subobject refactor [#11545](https://github.com/leanprover-community/mathlib/pull/11545), fixing a timeout caused by some expensive defeq checks.
I introduce a new definition `simplex.orthogonal_projection_span s := orthogonal_projection (affine_span ℝ (set.range s.points))`, and extract a couple of its properties from (repetitive) parts of proofs in `circumcenter.lean`, especially `eq_or_eq_reflection_of_dist_eq`. This makes the latter proof noticeably faster, especially after commit [#11750](https://github.com/leanprover-community/mathlib/pull/11750).
#### Estimated changes
Modified src/geometry/euclidean/circumcenter.lean
- \+ *lemma* affine.simplex.coe_orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \+ *lemma* affine.simplex.dist_circumcenter_sq_eq_sq_sub_circumradius
- \+ *lemma* affine.simplex.dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq
- \+ *def* affine.simplex.orthogonal_projection_span
- \+ *lemma* affine.simplex.orthogonal_projection_vadd_smul_vsub_orthogonal_projection



## [2022-02-24 10:42:14](https://github.com/leanprover-community/mathlib/commit/3d97cfb)
feat(ring_theory/ideal,dedekind_domain): lemmas on `I ≤ I^e` and `I < I^e` ([#12185](https://github.com/leanprover-community/mathlib/pull/12185))
#### Estimated changes
Modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* ideal.exists_mem_pow_not_mem_pow_succ
- \+ *lemma* ideal.pow_lt_self
- \+ *lemma* ideal.strict_anti_pow

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.pow_le_self



## [2022-02-24 08:26:23](https://github.com/leanprover-community/mathlib/commit/9eb78a3)
feat(measure_theory/function/ae_eq_fun): generalize scalar actions ([#12248](https://github.com/leanprover-community/mathlib/pull/12248))
This provides a more general `has_scalar` instance, along with `mul_action`, `distrib_mul_action`, `module`, `is_scalar_tower`, `smul_comm_class`, and `is_central_scalar` instances.
#### Estimated changes
Modified src/measure_theory/function/ae_eq_fun.lean
- \+ *def* measure_theory.ae_eq_fun.to_germ_monoid_hom



## [2022-02-24 04:27:02](https://github.com/leanprover-community/mathlib/commit/f6a7ad9)
feat(measure_theory/integral/average): define `measure_theory.average` ([#12128](https://github.com/leanprover-community/mathlib/pull/12128))
And use it to formulate Jensen's inequality. Also add Jensen's inequality for concave functions.
#### Estimated changes
Modified src/analysis/convex/integral.lean
- \+ *lemma* concave_on.average_mem_hypograph
- \+ *lemma* concave_on.le_map_average
- \+ *lemma* concave_on.le_map_integral
- \+ *lemma* concave_on.le_map_set_average
- \+ *lemma* concave_on.set_average_mem_hypograph
- \+ *lemma* convex.average_mem
- \+ *lemma* convex.set_average_mem
- \- *lemma* convex.smul_integral_mem
- \+ *lemma* convex_on.average_mem_epigraph
- \+ *lemma* convex_on.map_average_le
- \+ *lemma* convex_on.map_set_average_le
- \- *lemma* convex_on.map_smul_integral_le
- \+ *lemma* convex_on.set_average_mem_epigraph

Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable.to_average

Added src/measure_theory/integral/average.lean
- \+ *lemma* measure_theory.average_add_measure
- \+ *lemma* measure_theory.average_congr
- \+ *lemma* measure_theory.average_def'
- \+ *lemma* measure_theory.average_def
- \+ *lemma* measure_theory.average_eq_integral
- \+ *lemma* measure_theory.average_mem_open_segment_compl_self
- \+ *lemma* measure_theory.average_neg
- \+ *lemma* measure_theory.average_pair
- \+ *lemma* measure_theory.average_union
- \+ *lemma* measure_theory.average_union_mem_open_segment
- \+ *lemma* measure_theory.average_union_mem_segment
- \+ *lemma* measure_theory.average_zero
- \+ *lemma* measure_theory.average_zero_measure
- \+ *lemma* measure_theory.measure_smul_average
- \+ *lemma* measure_theory.measure_smul_set_average
- \+ *lemma* measure_theory.set_average_eq

Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.tendsto_integral_approx_on_of_measurable

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.is_probability_measure_smul



## [2022-02-24 03:44:56](https://github.com/leanprover-community/mathlib/commit/f3ee462)
chore(category_theory/adjunction/opposites): Forgotten `category_theory` namespace ([#12256](https://github.com/leanprover-community/mathlib/pull/12256))
The forgotten `category_theory` namespace means that dot notation doesn't work on `category_theory.adjunction`.
#### Estimated changes
Modified src/category_theory/adjunction/opposites.lean
- \- *def* adjunction.adjoint_of_op_adjoint_op
- \- *def* adjunction.adjoint_of_unop_adjoint_unop
- \- *def* adjunction.adjoint_op_of_adjoint_unop
- \- *def* adjunction.adjoint_unop_of_adjoint_op
- \- *lemma* adjunction.hom_equiv_left_adjoint_uniq_hom_app
- \- *lemma* adjunction.hom_equiv_symm_right_adjoint_uniq_hom_app
- \- *def* adjunction.left_adjoint_uniq
- \- *lemma* adjunction.left_adjoint_uniq_hom_app_counit
- \- *lemma* adjunction.left_adjoint_uniq_hom_counit
- \- *lemma* adjunction.left_adjoint_uniq_inv_app
- \- *lemma* adjunction.left_adjoint_uniq_refl
- \- *lemma* adjunction.left_adjoint_uniq_trans
- \- *lemma* adjunction.left_adjoint_uniq_trans_app
- \- *def* adjunction.left_adjoints_coyoneda_equiv
- \- *def* adjunction.nat_iso_of_left_adjoint_nat_iso
- \- *def* adjunction.nat_iso_of_right_adjoint_nat_iso
- \- *def* adjunction.op_adjoint_of_unop_adjoint
- \- *def* adjunction.op_adjoint_op_of_adjoint
- \- *def* adjunction.right_adjoint_uniq
- \- *lemma* adjunction.right_adjoint_uniq_hom_app_counit
- \- *lemma* adjunction.right_adjoint_uniq_hom_counit
- \- *lemma* adjunction.right_adjoint_uniq_inv_app
- \- *lemma* adjunction.right_adjoint_uniq_refl
- \- *lemma* adjunction.right_adjoint_uniq_trans
- \- *lemma* adjunction.right_adjoint_uniq_trans_app
- \- *lemma* adjunction.unit_left_adjoint_uniq_hom
- \- *lemma* adjunction.unit_left_adjoint_uniq_hom_app
- \- *lemma* adjunction.unit_right_adjoint_uniq_hom
- \- *lemma* adjunction.unit_right_adjoint_uniq_hom_app
- \- *def* adjunction.unop_adjoint_of_op_adjoint
- \- *def* adjunction.unop_adjoint_unop_of_adjoint
- \+ *def* category_theory.adjunction.adjoint_of_op_adjoint_op
- \+ *def* category_theory.adjunction.adjoint_of_unop_adjoint_unop
- \+ *def* category_theory.adjunction.adjoint_op_of_adjoint_unop
- \+ *def* category_theory.adjunction.adjoint_unop_of_adjoint_op
- \+ *lemma* category_theory.adjunction.hom_equiv_left_adjoint_uniq_hom_app
- \+ *lemma* category_theory.adjunction.hom_equiv_symm_right_adjoint_uniq_hom_app
- \+ *def* category_theory.adjunction.left_adjoint_uniq
- \+ *lemma* category_theory.adjunction.left_adjoint_uniq_hom_app_counit
- \+ *lemma* category_theory.adjunction.left_adjoint_uniq_hom_counit
- \+ *lemma* category_theory.adjunction.left_adjoint_uniq_inv_app
- \+ *lemma* category_theory.adjunction.left_adjoint_uniq_refl
- \+ *lemma* category_theory.adjunction.left_adjoint_uniq_trans
- \+ *lemma* category_theory.adjunction.left_adjoint_uniq_trans_app
- \+ *def* category_theory.adjunction.left_adjoints_coyoneda_equiv
- \+ *def* category_theory.adjunction.nat_iso_of_left_adjoint_nat_iso
- \+ *def* category_theory.adjunction.nat_iso_of_right_adjoint_nat_iso
- \+ *def* category_theory.adjunction.op_adjoint_of_unop_adjoint
- \+ *def* category_theory.adjunction.op_adjoint_op_of_adjoint
- \+ *def* category_theory.adjunction.right_adjoint_uniq
- \+ *lemma* category_theory.adjunction.right_adjoint_uniq_hom_app_counit
- \+ *lemma* category_theory.adjunction.right_adjoint_uniq_hom_counit
- \+ *lemma* category_theory.adjunction.right_adjoint_uniq_inv_app
- \+ *lemma* category_theory.adjunction.right_adjoint_uniq_refl
- \+ *lemma* category_theory.adjunction.right_adjoint_uniq_trans
- \+ *lemma* category_theory.adjunction.right_adjoint_uniq_trans_app
- \+ *lemma* category_theory.adjunction.unit_left_adjoint_uniq_hom
- \+ *lemma* category_theory.adjunction.unit_left_adjoint_uniq_hom_app
- \+ *lemma* category_theory.adjunction.unit_right_adjoint_uniq_hom
- \+ *lemma* category_theory.adjunction.unit_right_adjoint_uniq_hom_app
- \+ *def* category_theory.adjunction.unop_adjoint_of_op_adjoint
- \+ *def* category_theory.adjunction.unop_adjoint_unop_of_adjoint



## [2022-02-24 02:51:27](https://github.com/leanprover-community/mathlib/commit/ed55593)
feat(topology/metric_space/basic): add a few lemmas ([#12259](https://github.com/leanprover-community/mathlib/pull/12259))
Add `ne_of_mem_sphere`, `subsingleton_closed_ball`, and `metric.subsingleton_sphere`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.ne_of_mem_sphere
- \+ *lemma* metric.subsingleton_closed_ball
- \+ *lemma* metric.subsingleton_sphere



## [2022-02-24 01:18:43](https://github.com/leanprover-community/mathlib/commit/158550d)
feat(algebra/module/basic): add `smul_right_inj` ([#12252](https://github.com/leanprover-community/mathlib/pull/12252))
Also golf the proof of `smul_right_injective` by reusing
`add_monoid_hom.injective_iff`.
#### Estimated changes
Modified src/algebra/module/basic.lean
- \+ *lemma* smul_right_inj



## [2022-02-24 01:18:42](https://github.com/leanprover-community/mathlib/commit/2939c77)
feat(topology/metric_space): multiplicative opposites inherit the same `(pseudo_?)(e?)metric` and `uniform_space` ([#12120](https://github.com/leanprover-community/mathlib/pull/12120))
This puts the "obvious" metric on the opposite type such that `dist (op x) (op y) = dist x y`.
This also merges `subtype.pseudo_dist_eq` and `subtype.dist_eq` as the latter was a special case of the former.
#### Estimated changes
Modified src/measure_theory/function/simple_func_dense.lean


Modified src/topology/metric_space/algebra.lean


Modified src/topology/metric_space/basic.lean
- \+ *theorem* mul_opposite.dist_op
- \+ *theorem* mul_opposite.dist_unop
- \+ *theorem* mul_opposite.nndist_op
- \+ *theorem* mul_opposite.nndist_unop
- \+ *theorem* subtype.nndist_eq
- \- *theorem* subtype.pseudo_dist_eq

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* mul_opposite.edist_op
- \+ *theorem* mul_opposite.edist_unop

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* mul_opposite.uniform_continuous_op
- \+ *lemma* mul_opposite.uniform_continuous_unop
- \+ *lemma* uniformity_mul_opposite



## [2022-02-24 00:25:00](https://github.com/leanprover-community/mathlib/commit/890338d)
feat(analysis/normed_space/basic): use weaker assumptions ([#12260](https://github.com/leanprover-community/mathlib/pull/12260))
Assume `r ≠ 0` instead of `0 < r` in `interior_closed_ball` and `frontier_closed_ball`.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+/\- *theorem* frontier_closed_ball
- \+/\- *theorem* interior_closed_ball



## [2022-02-24 00:24:57](https://github.com/leanprover-community/mathlib/commit/620af85)
refactor(topology/instances): put `ℕ`, `ℤ`, and `ℚ` in separate files ([#12207](https://github.com/leanprover-community/mathlib/pull/12207))
The goal here is to make `metric_space ℕ` and `metric_space ℤ` available earlier, so that I can state `has_bounded_smul ℕ A` somewhere reasonable.
No lemmas have been added, deleted, or changed here - they've just been moved out of `topology/instances/real` and into 
`topology/instances/{nat,int,rat,real}`.
The resulting import structure is:
* `rat_lemmas` → `rat`
* `rat` → {`real`, `int`, `nat`}
* `real` → {`int`}
* `nat` → {`int`}
#### Estimated changes
Modified src/analysis/normed_space/basic.lean


Added src/topology/instances/int.lean
- \+ *theorem* int.ball_eq_Ioo
- \+ *theorem* int.closed_ball_eq_Icc
- \+ *lemma* int.closed_embedding_coe_real
- \+ *lemma* int.cocompact_eq
- \+ *lemma* int.cofinite_eq
- \+ *theorem* int.dist_cast_real
- \+ *theorem* int.dist_eq
- \+ *lemma* int.pairwise_one_le_dist
- \+ *theorem* int.preimage_ball
- \+ *theorem* int.preimage_closed_ball
- \+ *lemma* int.uniform_embedding_coe_real

Added src/topology/instances/nat.lean
- \+ *theorem* nat.closed_ball_eq_Icc
- \+ *lemma* nat.closed_embedding_coe_real
- \+ *theorem* nat.dist_cast_real
- \+ *lemma* nat.dist_coe_int
- \+ *theorem* nat.dist_eq
- \+ *lemma* nat.pairwise_one_le_dist
- \+ *theorem* nat.preimage_ball
- \+ *theorem* nat.preimage_closed_ball
- \+ *lemma* nat.uniform_embedding_coe_real

Added src/topology/instances/rat.lean
- \+ *lemma* int.closed_embedding_coe_rat
- \+ *theorem* int.dist_cast_rat
- \+ *lemma* int.uniform_embedding_coe_rat
- \+ *lemma* nat.closed_embedding_coe_rat
- \+ *theorem* nat.dist_cast_rat
- \+ *lemma* nat.uniform_embedding_coe_rat
- \+ *theorem* rat.continuous_coe_real
- \+ *lemma* rat.continuous_mul
- \+ *theorem* rat.dense_embedding_coe_real
- \+ *lemma* rat.dist_cast
- \+ *theorem* rat.dist_eq
- \+ *theorem* rat.embedding_coe_real
- \+ *lemma* rat.totally_bounded_Icc
- \+ *lemma* rat.uniform_continuous_abs
- \+ *theorem* rat.uniform_continuous_add
- \+ *theorem* rat.uniform_continuous_coe_real
- \+ *theorem* rat.uniform_continuous_neg
- \+ *theorem* rat.uniform_embedding_coe_real

Modified src/topology/instances/real.lean
- \- *theorem* int.ball_eq_Ioo
- \- *theorem* int.closed_ball_eq_Icc
- \- *lemma* int.closed_embedding_coe_rat
- \- *lemma* int.closed_embedding_coe_real
- \- *lemma* int.cocompact_eq
- \- *lemma* int.cofinite_eq
- \- *theorem* int.dist_cast_rat
- \- *theorem* int.dist_cast_real
- \- *theorem* int.dist_eq
- \- *lemma* int.pairwise_one_le_dist
- \- *theorem* int.preimage_ball
- \- *theorem* int.preimage_closed_ball
- \- *lemma* int.uniform_embedding_coe_rat
- \- *lemma* int.uniform_embedding_coe_real
- \- *theorem* nat.closed_ball_eq_Icc
- \- *lemma* nat.closed_embedding_coe_rat
- \- *lemma* nat.closed_embedding_coe_real
- \- *theorem* nat.dist_cast_rat
- \- *theorem* nat.dist_cast_real
- \- *lemma* nat.dist_coe_int
- \- *theorem* nat.dist_eq
- \- *lemma* nat.pairwise_one_le_dist
- \- *theorem* nat.preimage_ball
- \- *theorem* nat.preimage_closed_ball
- \- *lemma* nat.uniform_embedding_coe_rat
- \- *lemma* nat.uniform_embedding_coe_real
- \- *theorem* rat.continuous_coe_real
- \- *lemma* rat.continuous_mul
- \- *theorem* rat.dense_embedding_coe_real
- \- *lemma* rat.dist_cast
- \- *theorem* rat.dist_eq
- \- *theorem* rat.embedding_coe_real
- \- *lemma* rat.totally_bounded_Icc
- \- *lemma* rat.uniform_continuous_abs
- \- *theorem* rat.uniform_continuous_add
- \- *theorem* rat.uniform_continuous_coe_real
- \- *theorem* rat.uniform_continuous_neg
- \- *theorem* rat.uniform_embedding_coe_real

Modified src/topology/instances/real_vector_space.lean


Modified src/topology/uniform_space/compare_reals.lean




## [2022-02-23 22:56:45](https://github.com/leanprover-community/mathlib/commit/eae6ae3)
feat(algebra/associated): add decidable instances ([#12230](https://github.com/leanprover-community/mathlib/pull/12230))
Makes equality and divisibility decidable in `associates`, given that divisibility is decidable in the general case.
#### Estimated changes
Modified src/algebra/associated.lean




## [2022-02-23 21:42:45](https://github.com/leanprover-community/mathlib/commit/2c74921)
feat(data/pfun): A new induction on pfun.fix ([#12109](https://github.com/leanprover-community/mathlib/pull/12109))
A new lemma that lets you prove predicates given `b ∈ f.fix a` if `f` preserves the predicate, and it holds for values which `f` maps to `b`.
#### Estimated changes
Modified src/data/pfun.lean
- \+ *def* pfun.fix_induction'



## [2022-02-23 20:58:29](https://github.com/leanprover-community/mathlib/commit/9b333b2)
feat(topology/algebra/continuous_monoid_hom): `to_continuous_map` is a `closed_embedding` ([#12217](https://github.com/leanprover-community/mathlib/pull/12217))
This PR proves that `to_continuous_map : continuous_monoid_hom A B → C(A, B)` is a `closed_embedding`. This will be useful for showing that the Pontryagin dual is locally compact.
#### Estimated changes
Modified src/topology/algebra/continuous_monoid_hom.lean
- \+ *lemma* continuous_monoid_hom.is_closed_embedding



## [2022-02-23 17:43:01](https://github.com/leanprover-community/mathlib/commit/f04ad9a)
feat(analysis/normed_space/star/spectrum): prove the spectral radius of a selfadjoint element in a C*-algebra is its norm. ([#12211](https://github.com/leanprover-community/mathlib/pull/12211))
This establishes that the spectral radius of a selfadjoint element in a C*-algebra is its (nn)norm using the Gelfand formula for the spectral radius. The same theorem for normal elements can be proven using this once normal elements are defined in mathlib.
#### Estimated changes
Modified src/analysis/normed_space/star/basic.lean
- \+ *lemma* cstar_ring.nnnorm_star_mul_self
- \+ *lemma* nnnorm_pow_two_pow_of_self_adjoint
- \+ *lemma* self_adjoint.nnnorm_pow_two_pow

Added src/analysis/normed_space/star/spectrum.lean
- \+ *lemma* self_adjoint.coe_spectral_radius_eq_nnnorm
- \+ *lemma* spectral_radius_eq_nnnorm_of_self_adjoint



## [2022-02-23 16:03:57](https://github.com/leanprover-community/mathlib/commit/b72cca4)
chore(geometry/manifold/algebra/smooth_functions): golf module instance ([#12247](https://github.com/leanprover-community/mathlib/pull/12247))
#### Estimated changes
Modified src/geometry/manifold/algebra/smooth_functions.lean




## [2022-02-23 16:03:56](https://github.com/leanprover-community/mathlib/commit/3e2df83)
docs(order/order_iso_nat): Added note on `exists_increasing_or_nonincreasing_subseq` ([#12239](https://github.com/leanprover-community/mathlib/pull/12239))
#### Estimated changes
Modified src/order/order_iso_nat.lean




## [2022-02-23 16:03:55](https://github.com/leanprover-community/mathlib/commit/162d060)
feat(measure_theory/function/strongly_measurable): more basic properties of `strongly_measurable` ([#12164](https://github.com/leanprover-community/mathlib/pull/12164))
#### Estimated changes
Modified src/algebra/support.lean
- \+ *lemma* function.support_const_smul_of_ne_zero

Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measurable_of_tendsto_ennreal'
- \+ *lemma* measurable_of_tendsto_ennreal

Modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* measure_theory.ae_fin_strongly_measurable.ae_eq_mk
- \+ *lemma* measure_theory.ae_fin_strongly_measurable.fin_strongly_measurable_mk
- \+ *lemma* measure_theory.ae_fin_strongly_measurable_zero
- \+/\- *lemma* measure_theory.fin_strongly_measurable.ae_fin_strongly_measurable
- \+/\- *lemma* measure_theory.fin_strongly_measurable.exists_set_sigma_finite
- \+ *lemma* measure_theory.fin_strongly_measurable_zero
- \+ *lemma* measure_theory.simple_func.strongly_measurable
- \+/\- *def* measure_theory.strongly_measurable.approx
- \+ *lemma* measure_theory.strongly_measurable_const
- \+ *lemma* measure_theory.strongly_measurable_id

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.simple_func.coe_inf
- \+ *lemma* measure_theory.simple_func.coe_sup



## [2022-02-23 16:03:54](https://github.com/leanprover-community/mathlib/commit/3fe20d4)
feat(ring_theory/localization): add mk' lemmas ([#12081](https://github.com/leanprover-community/mathlib/pull/12081))
#### Estimated changes
Modified src/field_theory/ratfunc.lean


Modified src/ring_theory/localization/basic.lean
- \+ *lemma* is_localization.mk'_zero
- \+ *lemma* is_localization.ne_zero_of_mk'_ne_zero

Modified src/ring_theory/localization/fraction_ring.lean
- \+ *lemma* is_fraction_ring.mk'_eq_one_iff_eq
- \+ *lemma* is_fraction_ring.mk'_eq_zero_iff_eq_zero



## [2022-02-23 14:40:03](https://github.com/leanprover-community/mathlib/commit/0d5bed0)
feat(ring_theory/graded_algebra): definitions and basic operations of homogeneous ideal ([#10784](https://github.com/leanprover-community/mathlib/pull/10784))
This defines homogeneous ideals (`homogeneous_ideal`) of a graded algebra.
#### Estimated changes
Modified src/algebra/graded_monoid.lean
- \+ *lemma* set_like.is_homogeneous_coe

Added src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+ *lemma* homogeneous_ideal.coe_Inf
- \+ *lemma* homogeneous_ideal.coe_Sup
- \+ *lemma* homogeneous_ideal.coe_add
- \+ *lemma* homogeneous_ideal.coe_bot
- \+ *lemma* homogeneous_ideal.coe_inf
- \+ *lemma* homogeneous_ideal.coe_infi
- \+ *lemma* homogeneous_ideal.coe_mul
- \+ *lemma* homogeneous_ideal.coe_sup
- \+ *lemma* homogeneous_ideal.coe_supr
- \+ *lemma* homogeneous_ideal.coe_top
- \+ *lemma* homogeneous_ideal.eq_bot_iff
- \+ *lemma* homogeneous_ideal.eq_top_iff
- \+ *lemma* homogeneous_ideal.homogeneous_core_coe_eq_self
- \+ *lemma* homogeneous_ideal.homogeneous_hull_coe_eq_self
- \+ *abbreviation* homogeneous_ideal
- \+ *lemma* ideal.coe_homogeneous_core_le
- \+ *lemma* ideal.coe_homogeneous_hull_eq_supr
- \+ *def* ideal.homogeneous_core'
- \+ *lemma* ideal.homogeneous_core'_eq_Sup
- \+ *lemma* ideal.homogeneous_core'_le
- \+ *lemma* ideal.homogeneous_core'_mono
- \+ *lemma* ideal.homogeneous_core.gc
- \+ *def* ideal.homogeneous_core.gi
- \+ *def* ideal.homogeneous_core
- \+ *lemma* ideal.homogeneous_core_eq_Sup
- \+ *lemma* ideal.homogeneous_core_mono
- \+ *lemma* ideal.homogeneous_hull.gc
- \+ *def* ideal.homogeneous_hull.gi
- \+ *def* ideal.homogeneous_hull
- \+ *lemma* ideal.homogeneous_hull_eq_Inf
- \+ *lemma* ideal.homogeneous_hull_eq_supr
- \+ *lemma* ideal.homogeneous_hull_mono
- \+ *lemma* ideal.is_homogeneous.Inf
- \+ *lemma* ideal.is_homogeneous.Sup
- \+ *lemma* ideal.is_homogeneous.bot
- \+ *lemma* ideal.is_homogeneous.coe_homogeneous_core_eq_self
- \+ *lemma* ideal.is_homogeneous.homogeneous_hull_eq_self
- \+ *lemma* ideal.is_homogeneous.iff_eq
- \+ *lemma* ideal.is_homogeneous.iff_exists
- \+ *lemma* ideal.is_homogeneous.inf
- \+ *lemma* ideal.is_homogeneous.mul
- \+ *lemma* ideal.is_homogeneous.sup
- \+ *lemma* ideal.is_homogeneous.top
- \+ *def* ideal.is_homogeneous
- \+ *lemma* ideal.is_homogeneous_iff_forall_subset
- \+ *lemma* ideal.is_homogeneous_iff_subset_Inter
- \+ *lemma* ideal.is_homogeneous_span
- \+ *lemma* ideal.le_coe_homogeneous_hull
- \+ *lemma* ideal.mul_homogeneous_element_mem_of_mem

Modified src/ring_theory/ideal/basic.lean
- \+ *lemma* ideal.mem_span
- \+ *lemma* ideal.span_Union
- \+ *lemma* ideal.span_empty
- \+ *lemma* ideal.span_union
- \+ *lemma* ideal.span_univ
- \+ *lemma* ideal.sum_mem



## [2022-02-23 13:18:22](https://github.com/leanprover-community/mathlib/commit/e167efa)
chore(topology/instances/rat): rename to rat_lemmas ([#12246](https://github.com/leanprover-community/mathlib/pull/12246))
This is to make room for the changes in [#12207](https://github.com/leanprover-community/mathlib/pull/12207), which claim `topology.instances.rat` for more basic results. This has to be in a separate commit to keep the history reasonable.
#### Estimated changes
Renamed src/topology/instances/rat.lean to src/topology/instances/rat_lemmas.lean




## [2022-02-23 13:18:20](https://github.com/leanprover-community/mathlib/commit/c526789)
feat(set_theory/ordinal_arithmetic): `is_normal.eq_iff_zero_and_succ` ([#12222](https://github.com/leanprover-community/mathlib/pull/12222))
Two normal functions are equal iff they're equal at `0` and successor ordinals. This is used for a few lemmas in [#12202](https://github.com/leanprover-community/mathlib/pull/12202).
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.is_normal.eq_iff_zero_and_succ



## [2022-02-23 13:18:19](https://github.com/leanprover-community/mathlib/commit/7de8137)
feat(topology/order/hom): Continuous order homomorphisms ([#12012](https://github.com/leanprover-community/mathlib/pull/12012))
Define continuous monotone functions, aka continuous order homomorphisms, aka Priestley homomorphisms, with notation `α →Co β`.
#### Estimated changes
Modified src/topology/continuous_function/basic.lean


Added src/topology/order/hom/basic.lean
- \+ *lemma* continuous_order_hom.cancel_left
- \+ *lemma* continuous_order_hom.cancel_right
- \+ *lemma* continuous_order_hom.coe_comp
- \+ *lemma* continuous_order_hom.coe_id
- \+ *def* continuous_order_hom.comp
- \+ *lemma* continuous_order_hom.comp_apply
- \+ *lemma* continuous_order_hom.comp_assoc
- \+ *lemma* continuous_order_hom.comp_id
- \+ *lemma* continuous_order_hom.ext
- \+ *lemma* continuous_order_hom.id_apply
- \+ *lemma* continuous_order_hom.id_comp
- \+ *def* continuous_order_hom.to_continuous_map
- \+ *lemma* continuous_order_hom.to_fun_eq_coe
- \+ *structure* continuous_order_hom



## [2022-02-23 12:32:53](https://github.com/leanprover-community/mathlib/commit/b0fbd91)
feat(measure_theory/measure): generalize scalar actions ([#12187](https://github.com/leanprover-community/mathlib/pull/12187))
As a result of this change, many smul lemmas now also apply to `nat` and `nnreal`, which allows some lemmas to be removed.
#### Estimated changes
Modified src/measure_theory/covering/differentiation.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/integral/set_to_l1.lean


Modified src/measure_theory/measure/haar.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* ae_measurable.smul_measure
- \+/\- *lemma* measure_theory.ae_smul_measure
- \- *theorem* measure_theory.measure.coe_nnreal_smul
- \+/\- *theorem* measure_theory.measure.coe_smul
- \+/\- *theorem* measure_theory.measure.smul_apply
- \+/\- *theorem* measure_theory.measure.smul_to_outer_measure

Modified src/measure_theory/measure/outer_measure.lean
- \+ *def* measure_theory.outer_measure.coe_fn_add_monoid_hom
- \+/\- *lemma* measure_theory.outer_measure.coe_smul
- \+/\- *lemma* measure_theory.outer_measure.smul_apply
- \+/\- *theorem* measure_theory.outer_measure.smul_supr
- \+/\- *theorem* measure_theory.outer_measure.trim_smul

Modified src/measure_theory/measure/regular.lean


Modified src/measure_theory/measure/vector_measure.lean


Modified src/probability/independence.lean




## [2022-02-23 12:32:52](https://github.com/leanprover-community/mathlib/commit/d01b55f)
split(analysis/functional/gauge): Split off `analysis.seminorm` ([#12054](https://github.com/leanprover-community/mathlib/pull/12054))
Move the Minkowski functional to a new file `analysis.convex.gauge`.
#### Estimated changes
Added src/analysis/convex/gauge.lean
- \+ *lemma* absorbent.gauge_set_nonempty
- \+ *lemma* balanced.star_convex
- \+ *lemma* convex.gauge_le
- \+ *lemma* exists_lt_of_gauge_lt
- \+ *def* gauge
- \+ *lemma* gauge_add_le
- \+ *lemma* gauge_ball
- \+ *lemma* gauge_def'
- \+ *lemma* gauge_def
- \+ *lemma* gauge_empty
- \+ *lemma* gauge_le_eq
- \+ *lemma* gauge_le_of_mem
- \+ *lemma* gauge_le_one_of_mem
- \+ *lemma* gauge_lt_eq'
- \+ *lemma* gauge_lt_eq
- \+ *lemma* gauge_lt_of_mem_smul
- \+ *lemma* gauge_lt_one_eq_self_of_open
- \+ *lemma* gauge_lt_one_of_mem_of_open
- \+ *lemma* gauge_lt_one_subset_self
- \+ *lemma* gauge_mono
- \+ *lemma* gauge_neg
- \+ *lemma* gauge_nonneg
- \+ *lemma* gauge_of_subset_zero
- \+ *def* gauge_seminorm
- \+ *lemma* gauge_seminorm_lt_one_of_open
- \+ *lemma* gauge_smul
- \+ *lemma* gauge_smul_left
- \+ *lemma* gauge_smul_left_of_nonneg
- \+ *lemma* gauge_smul_of_nonneg
- \+ *lemma* gauge_unit_ball
- \+ *lemma* gauge_zero'
- \+ *lemma* gauge_zero
- \+ *lemma* interior_subset_gauge_lt_one
- \+ *lemma* le_gauge_of_not_mem
- \+ *lemma* mul_gauge_le_norm
- \+ *lemma* one_le_gauge_of_not_mem
- \+ *lemma* self_subset_gauge_le_one
- \+ *lemma* seminorm.gauge_seminorm_ball
- \+ *lemma* smul_unit_ball

Modified src/analysis/seminorm.lean
- \- *lemma* absorbent.gauge_set_nonempty
- \- *lemma* balanced.star_convex
- \- *lemma* convex.gauge_le
- \- *lemma* exists_lt_of_gauge_lt
- \- *def* gauge
- \- *lemma* gauge_add_le
- \- *lemma* gauge_ball
- \- *lemma* gauge_def'
- \- *lemma* gauge_def
- \- *lemma* gauge_empty
- \- *lemma* gauge_le_eq
- \- *lemma* gauge_le_of_mem
- \- *lemma* gauge_le_one_of_mem
- \- *lemma* gauge_lt_eq'
- \- *lemma* gauge_lt_eq
- \- *lemma* gauge_lt_of_mem_smul
- \- *lemma* gauge_lt_one_eq_self_of_open
- \- *lemma* gauge_lt_one_of_mem_of_open
- \- *lemma* gauge_lt_one_subset_self
- \- *lemma* gauge_mono
- \- *lemma* gauge_neg
- \- *lemma* gauge_nonneg
- \- *lemma* gauge_of_subset_zero
- \- *def* gauge_seminorm
- \- *lemma* gauge_seminorm_lt_one_of_open
- \- *lemma* gauge_smul
- \- *lemma* gauge_smul_left
- \- *lemma* gauge_smul_left_of_nonneg
- \- *lemma* gauge_smul_of_nonneg
- \- *lemma* gauge_unit_ball
- \- *lemma* gauge_zero'
- \- *lemma* gauge_zero
- \- *lemma* interior_subset_gauge_lt_one
- \- *lemma* le_gauge_of_not_mem
- \- *lemma* mul_gauge_le_norm
- \- *lemma* one_le_gauge_of_not_mem
- \- *lemma* self_subset_gauge_le_one
- \- *lemma* seminorm.gauge_seminorm_ball
- \- *lemma* smul_unit_ball



## [2022-02-23 10:50:57](https://github.com/leanprover-community/mathlib/commit/6179707)
feat(ring_theory/unique_factorization_domain): add count_self ([#12074](https://github.com/leanprover-community/mathlib/pull/12074))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+/\- *theorem* multiset.count_singleton_self

Modified src/ring_theory/unique_factorization_domain.lean
- \+ *theorem* associates.count_self
- \+ *theorem* associates.factors_self



## [2022-02-23 10:50:56](https://github.com/leanprover-community/mathlib/commit/6f1d90d)
feat(algebra/order/monoid_lemmas_gt_zero): introduce the type of positive elements and prove some lemmas ([#11833](https://github.com/leanprover-community/mathlib/pull/11833))
This PR continues the `order` refactor.  Here I start working with the type of positive elements of a type with zero and lt.  Combining `covariant_` and `contravariant_classes` where the "acting" type is the type of positive elements, we can formulate the condition that "multiplication by positive elements is monotone" and variants.
I also prove some initial lemmas, just to give a flavour of the API.
More such lemmas will come in subsequent PRs (see for instance [#11782](https://github.com/leanprover-community/mathlib/pull/11782) for a few more lemmas).  After that, I will start simplifying existing lemmas, by weakening their assumptions.
#### Estimated changes
Added src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* zero_lt.lt_of_mul_lt_mul_left'
- \+ *lemma* zero_lt.lt_of_mul_lt_mul_right'
- \+ *lemma* zero_lt.mul_lt_mul_iff_left
- \+ *lemma* zero_lt.mul_lt_mul_iff_right
- \+ *lemma* zero_lt.mul_lt_mul_left'
- \+ *lemma* zero_lt.mul_lt_mul_right'
- \+ *abbreviation* zero_lt.mul_pos_mono
- \+ *abbreviation* zero_lt.mul_pos_mono_rev
- \+ *abbreviation* zero_lt.mul_pos_reflect_lt
- \+ *abbreviation* zero_lt.mul_pos_strict_mono
- \+ *abbreviation* zero_lt.pos_mul_mono
- \+ *abbreviation* zero_lt.pos_mul_mono_rev
- \+ *abbreviation* zero_lt.pos_mul_reflect_lt
- \+ *abbreviation* zero_lt.pos_mul_strict_mono



## [2022-02-23 09:39:52](https://github.com/leanprover-community/mathlib/commit/3e77124)
refactor(topology/{separation,subset_properties}): use `set.subsingleton` ([#12232](https://github.com/leanprover-community/mathlib/pull/12232))
Use `set.subsingleton s` instead of `_root_.subsingleton s` in `is_preirreducible_iff_subsingleton` and `is_preirreducible_of_subsingleton`, rename the latter to `set.subsingleton.is_preirreducible`.
#### Estimated changes
Modified src/topology/separation.lean


Modified src/topology/sober.lean


Modified src/topology/subset_properties.lean
- \- *lemma* is_preirreducible_of_subsingleton
- \+ *lemma* set.subsingleton.is_preirreducible



## [2022-02-23 09:39:50](https://github.com/leanprover-community/mathlib/commit/dc9b8be)
feat(analysis/normed_space/linear_isometry): add lemmas to `linear_isometry_equiv` ([#12218](https://github.com/leanprover-community/mathlib/pull/12218))
Added two API lemmas to `linear_isometry_equiv` that I need elsewhere.
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.trans_apply



## [2022-02-23 09:39:49](https://github.com/leanprover-community/mathlib/commit/f44ed74)
feat(ring_theory/ideal/over): `S/p` is noetherian over `R/p` if `S` is over `R` ([#12183](https://github.com/leanprover-community/mathlib/pull/12183))
#### Estimated changes
Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/ideal/quotient.lean
- \+ *lemma* ideal.quotient.subsingleton_iff



## [2022-02-23 08:16:08](https://github.com/leanprover-community/mathlib/commit/515eefa)
fix(algebra/star/basic): more type classes that should be props ([#12235](https://github.com/leanprover-community/mathlib/pull/12235))
#### Estimated changes
Modified src/algebra/star/basic.lean




## [2022-02-23 08:16:07](https://github.com/leanprover-community/mathlib/commit/98bcabb)
feat(group_theory/perm): add lemmas for cycles of permutations ([#11955](https://github.com/leanprover-community/mathlib/pull/11955))
`nodup_powers_of_cycle_of` : shows that the the iterates of an element in the support give rise to a nodup list
`cycle_is_cycle_of` : asserts that a given cycle c in `f. cycle_factors_finset` is `f.cycle_of a` if c a \neq a
`equiv.perm.sign_of_cycle_type` : new formula for the sign of a permutations in terms of its cycle_type — It is simpler to use (just uses number of cycles and size of support) than the earlier lemma which is renamed as equiv.perm.sign_of_cycle_type'  (it could be deleted). I made one modification to make the file compile, but I need to check compatibility with the other ones.
#### Estimated changes
Modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* equiv.perm.sign_of_cycle_type'
- \+/\- *lemma* equiv.perm.sign_of_cycle_type

Modified src/group_theory/perm/cycles.lean
- \+ *lemma* equiv.perm.cycle_is_cycle_of
- \+ *lemma* equiv.perm.is_cycle_cycle_of_iff

Modified src/group_theory/specific_groups/alternating.lean




## [2022-02-23 07:46:35](https://github.com/leanprover-community/mathlib/commit/0eed60e)
feat(number_theory/cyclotomic/discriminant): discriminant of a p-th cyclotomic field ([#11804](https://github.com/leanprover-community/mathlib/pull/11804))
We compute the discriminant of a p-th cyclotomic field.
From flt-regular.
- [x] depends on: [#11786](https://github.com/leanprover-community/mathlib/pull/11786)
#### Estimated changes
Added src/number_theory/cyclotomic/discriminant.lean
- \+ *lemma* is_cyclotomic_extension.discr_odd_prime

Modified src/number_theory/cyclotomic/primitive_roots.lean
- \- *lemma* is_cyclotomic_extension.is_prime_pow.norm_zeta_sub_one
- \+ *lemma* is_cyclotomic_extension.is_prime_pow_norm_zeta_sub_one
- \- *lemma* is_cyclotomic_extension.prime_ne_two.norm_zeta_sub_one
- \+ *lemma* is_cyclotomic_extension.prime_ne_two_norm_zeta_sub_one
- \- *lemma* is_cyclotomic_extension.prime_ne_two_pow.norm_zeta_sub_one
- \+ *lemma* is_cyclotomic_extension.prime_ne_two_pow_norm_zeta_sub_one
- \- *lemma* is_cyclotomic_extension.two_pow.norm_zeta_sub_one
- \+ *lemma* is_cyclotomic_extension.two_pow_norm_zeta_sub_one
- \- *lemma* is_primitive_root.prime_ne_two_pow.sub_one_norm
- \+ *lemma* is_primitive_root.prime_ne_two_pow_sub_one_norm
- \- *lemma* is_primitive_root.sub_one_norm.is_prime_pow
- \- *lemma* is_primitive_root.sub_one_norm.pow_two
- \- *lemma* is_primitive_root.sub_one_norm.prime
- \+ *lemma* is_primitive_root.sub_one_norm_is_prime_pow
- \+ *lemma* is_primitive_root.sub_one_norm_pow_two
- \+ *lemma* is_primitive_root.sub_one_norm_prime

Modified src/ring_theory/discriminant.lean
- \+ *lemma* algebra.discr_power_basis_eq_norm
- \+ *lemma* algebra.discr_power_basis_eq_prod''
- \+ *lemma* algebra.discr_power_basis_eq_prod'
- \- *lemma* algebra.of_power_basis_eq_norm
- \- *lemma* algebra.of_power_basis_eq_prod''
- \- *lemma* algebra.of_power_basis_eq_prod'

Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one



## [2022-02-23 05:24:19](https://github.com/leanprover-community/mathlib/commit/257bddf)
feat(algebra/algebra/spectrum): add spectral mapping for inverses ([#12219](https://github.com/leanprover-community/mathlib/pull/12219))
Given a unit `a` in an algebra `A` over a field `𝕜`, the equality `(spectrum 𝕜 a)⁻¹ = spectrum 𝕜 a⁻¹` holds.
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean
- \+ *lemma* spectrum.inv_mem_iff
- \+ *lemma* spectrum.inv_mem_resolvent_set
- \+ *lemma* spectrum.ne_zero_of_mem_of_unit
- \+ *lemma* spectrum.zero_mem_resolvent_set_of_unit



## [2022-02-23 04:31:26](https://github.com/leanprover-community/mathlib/commit/e77675d)
fix(analysis/normed_space/star/basic): make prop type classes props ([#12233](https://github.com/leanprover-community/mathlib/pull/12233))
The type classes `normed_star_monoid` and `cstar_ring` are now properly declared as prop.
#### Estimated changes
Modified src/analysis/normed_space/star/basic.lean




## [2022-02-23 04:01:36](https://github.com/leanprover-community/mathlib/commit/264dd7f)
feat(model_theory/basic): Language operations ([#12129](https://github.com/leanprover-community/mathlib/pull/12129))
Defines language homomorphisms with `first_order.language.Lhom`
Defines the sum of two languages with `first_order.language.sum`
Defines `first_order.language.with_constants`, a language with added constants, abbreviated `L[[A]]`.
Defines a `L[[A]].Structure` on `M` when `A : set M`.
(Some of this code comes from the Flypitch project)
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *def* first_order.language.Lhom.add_constants
- \+ *def* first_order.language.Lhom.comp
- \+ *lemma* first_order.language.Lhom.comp_id
- \+ *def* first_order.language.Lhom.constants_on_map
- \+ *lemma* first_order.language.Lhom.id_comp
- \+ *lemma* first_order.language.Lhom.map_constants_comp_with_constants
- \+ *def* first_order.language.Lhom.sum_elim
- \+ *def* first_order.language.Lhom.sum_map
- \+ *structure* first_order.language.Lhom
- \+ *def* first_order.language.Lhom_trim_empty_constants
- \+ *def* first_order.language.Lhom_with_constants
- \+ *def* first_order.language.Lhom_with_constants_map
- \- *def* first_order.language.const
- \+ *def* first_order.language.constants_on.Structure
- \+ *def* first_order.language.constants_on
- \+ *lemma* first_order.language.constants_on_constants
- \+ *def* first_order.language.constants_on_functions
- \+ *lemma* first_order.language.constants_on_map_is_expansion_on
- \- *lemma* first_order.language.embedding.map_const
- \+ *lemma* first_order.language.embedding.map_constants
- \- *lemma* first_order.language.equiv.map_const
- \+ *lemma* first_order.language.equiv.map_constants
- \- *lemma* first_order.language.fun_map_eq_coe_const
- \+ *lemma* first_order.language.fun_map_eq_coe_constants
- \+ *lemma* first_order.language.fun_map_sum_inl
- \+ *lemma* first_order.language.fun_map_sum_inr
- \- *lemma* first_order.language.hom.map_const
- \+ *lemma* first_order.language.hom.map_constants
- \+/\- *lemma* first_order.language.nonempty_of_nonempty_constants
- \+ *lemma* first_order.language.rel_map_sum_inl
- \+ *lemma* first_order.language.rel_map_sum_inr
- \+ *def* first_order.language.symbols
- \+ *def* first_order.language.with_constants

Modified src/model_theory/elementary_maps.lean
- \- *lemma* first_order.language.elementary_embedding.map_const
- \+ *lemma* first_order.language.elementary_embedding.map_constants

Modified src/model_theory/substructures.lean
- \- *lemma* first_order.language.substructure.const_mem
- \+ *lemma* first_order.language.substructure.constants_mem

Modified src/model_theory/terms_and_formulas.lean




## [2022-02-23 00:45:57](https://github.com/leanprover-community/mathlib/commit/7cc4eb9)
doc(number_theory/padics/*): typo in references ([#12229](https://github.com/leanprover-community/mathlib/pull/12229))
Fix typos in a reference.
#### Estimated changes
Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/padics/padic_norm.lean


Modified src/number_theory/padics/padic_numbers.lean




## [2022-02-23 00:45:56](https://github.com/leanprover-community/mathlib/commit/4238868)
chore(analysis): rename times_cont_diff ([#12227](https://github.com/leanprover-community/mathlib/pull/12227))
This replaces `times_cont_diff` by `cont_diff` everywhere, and the same for `times_cont_mdiff`. There is no change at all in content.
See https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/times_cont_diff.20name
#### Estimated changes
Modified docs/overview.yaml


Modified docs/undergrad.yaml


Modified src/algebra/group/to_additive.lean


Modified src/analysis/calculus/affine_map.lean
- \+ *lemma* continuous_affine_map.cont_diff
- \- *lemma* continuous_affine_map.times_cont_diff

Renamed src/analysis/calculus/times_cont_diff.lean to src/analysis/calculus/cont_diff.lean
- \+ *lemma* cont_diff.add
- \+ *lemma* cont_diff.comp
- \+ *lemma* cont_diff.comp_cont_diff_at
- \+ *lemma* cont_diff.comp_cont_diff_on
- \+ *lemma* cont_diff.comp_cont_diff_within_at
- \+ *lemma* cont_diff.comp_continuous_linear_map
- \+ *lemma* cont_diff.cont_diff_at
- \+ *lemma* cont_diff.cont_diff_fderiv_apply
- \+ *lemma* cont_diff.cont_diff_on
- \+ *lemma* cont_diff.cont_diff_within_at
- \+ *lemma* cont_diff.continuous
- \+ *lemma* cont_diff.continuous_fderiv
- \+ *lemma* cont_diff.continuous_fderiv_apply
- \+ *lemma* cont_diff.continuous_linear_map_comp
- \+ *lemma* cont_diff.differentiable
- \+ *lemma* cont_diff.div
- \+ *lemma* cont_diff.div_const
- \+ *lemma* cont_diff.has_strict_deriv_at
- \+ *lemma* cont_diff.has_strict_fderiv_at
- \+ *lemma* cont_diff.inv
- \+ *lemma* cont_diff.mul
- \+ *lemma* cont_diff.neg
- \+ *lemma* cont_diff.of_le
- \+ *lemma* cont_diff.pow
- \+ *lemma* cont_diff.prod
- \+ *lemma* cont_diff.prod_map
- \+ *lemma* cont_diff.restrict_scalars
- \+ *lemma* cont_diff.smul
- \+ *lemma* cont_diff.sub
- \+ *lemma* cont_diff.sum
- \+ *lemma* cont_diff_add
- \+ *lemma* cont_diff_all_iff_nat
- \+ *lemma* cont_diff_at.add
- \+ *lemma* cont_diff_at.comp
- \+ *lemma* cont_diff_at.comp_cont_diff_within_at
- \+ *lemma* cont_diff_at.congr_of_eventually_eq
- \+ *lemma* cont_diff_at.cont_diff_within_at
- \+ *lemma* cont_diff_at.continuous_at
- \+ *lemma* cont_diff_at.continuous_linear_map_comp
- \+ *lemma* cont_diff_at.differentiable_at
- \+ *lemma* cont_diff_at.div
- \+ *lemma* cont_diff_at.div_const
- \+ *lemma* cont_diff_at.exists_lipschitz_on_with
- \+ *lemma* cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt
- \+ *lemma* cont_diff_at.has_strict_deriv_at'
- \+ *lemma* cont_diff_at.has_strict_deriv_at
- \+ *lemma* cont_diff_at.has_strict_fderiv_at'
- \+ *lemma* cont_diff_at.has_strict_fderiv_at
- \+ *lemma* cont_diff_at.inv
- \+ *lemma* cont_diff_at.mul
- \+ *lemma* cont_diff_at.neg
- \+ *lemma* cont_diff_at.of_le
- \+ *lemma* cont_diff_at.pow
- \+ *lemma* cont_diff_at.prod
- \+ *lemma* cont_diff_at.prod_map'
- \+ *lemma* cont_diff_at.prod_map
- \+ *lemma* cont_diff_at.restrict_scalars
- \+ *lemma* cont_diff_at.smul
- \+ *lemma* cont_diff_at.sub
- \+ *lemma* cont_diff_at.sum
- \+ *def* cont_diff_at
- \+ *lemma* cont_diff_at_const
- \+ *lemma* cont_diff_at_fst
- \+ *lemma* cont_diff_at_id
- \+ *lemma* cont_diff_at_inv
- \+ *lemma* cont_diff_at_map_inverse
- \+ *lemma* cont_diff_at_of_subsingleton
- \+ *lemma* cont_diff_at_pi
- \+ *lemma* cont_diff_at_ring_inverse
- \+ *lemma* cont_diff_at_snd
- \+ *theorem* cont_diff_at_succ_iff_has_fderiv_at
- \+ *lemma* cont_diff_at_top
- \+ *lemma* cont_diff_at_zero
- \+ *lemma* cont_diff_const
- \+ *lemma* cont_diff_fst
- \+ *lemma* cont_diff_id
- \+ *lemma* cont_diff_iff_cont_diff_at
- \+ *lemma* cont_diff_iff_continuous_differentiable
- \+ *lemma* cont_diff_mul
- \+ *lemma* cont_diff_neg
- \+ *lemma* cont_diff_of_differentiable_iterated_fderiv
- \+ *lemma* cont_diff_of_subsingleton
- \+ *lemma* cont_diff_on.add
- \+ *lemma* cont_diff_on.comp'
- \+ *lemma* cont_diff_on.comp
- \+ *lemma* cont_diff_on.comp_continuous_linear_map
- \+ *lemma* cont_diff_on.congr
- \+ *lemma* cont_diff_on.congr_mono
- \+ *lemma* cont_diff_on.cont_diff_within_at
- \+ *lemma* cont_diff_on.continuous_linear_map_comp
- \+ *lemma* cont_diff_on.continuous_on
- \+ *lemma* cont_diff_on.continuous_on_deriv_of_open
- \+ *lemma* cont_diff_on.continuous_on_deriv_within
- \+ *lemma* cont_diff_on.continuous_on_fderiv_of_open
- \+ *lemma* cont_diff_on.continuous_on_fderiv_within
- \+ *lemma* cont_diff_on.continuous_on_fderiv_within_apply
- \+ *lemma* cont_diff_on.continuous_on_iterated_fderiv_within
- \+ *lemma* cont_diff_on.deriv_of_open
- \+ *lemma* cont_diff_on.deriv_within
- \+ *lemma* cont_diff_on.differentiable_on
- \+ *lemma* cont_diff_on.differentiable_on_iterated_fderiv_within
- \+ *lemma* cont_diff_on.div
- \+ *lemma* cont_diff_on.div_const
- \+ *lemma* cont_diff_on.fderiv_of_open
- \+ *lemma* cont_diff_on.fderiv_within
- \+ *theorem* cont_diff_on.ftaylor_series_within
- \+ *lemma* cont_diff_on.inv
- \+ *lemma* cont_diff_on.mono
- \+ *lemma* cont_diff_on.mul
- \+ *lemma* cont_diff_on.neg
- \+ *lemma* cont_diff_on.of_le
- \+ *lemma* cont_diff_on.pow
- \+ *lemma* cont_diff_on.prod
- \+ *lemma* cont_diff_on.prod_map
- \+ *lemma* cont_diff_on.restrict_scalars
- \+ *lemma* cont_diff_on.smul
- \+ *lemma* cont_diff_on.sub
- \+ *lemma* cont_diff_on.sum
- \+ *lemma* cont_diff_on_all_iff_nat
- \+ *lemma* cont_diff_on_congr
- \+ *lemma* cont_diff_on_const
- \+ *lemma* cont_diff_on_fderiv_within_apply
- \+ *lemma* cont_diff_on_fst
- \+ *lemma* cont_diff_on_id
- \+ *lemma* cont_diff_on_iff_continuous_on_differentiable_on
- \+ *lemma* cont_diff_on_iff_forall_nat_le
- \+ *theorem* cont_diff_on_iff_ftaylor_series
- \+ *lemma* cont_diff_on_inv
- \+ *lemma* cont_diff_on_of_continuous_on_differentiable_on
- \+ *lemma* cont_diff_on_of_differentiable_on
- \+ *lemma* cont_diff_on_of_locally_cont_diff_on
- \+ *lemma* cont_diff_on_of_subsingleton
- \+ *lemma* cont_diff_on_pi
- \+ *lemma* cont_diff_on_snd
- \+ *theorem* cont_diff_on_succ_iff_deriv_of_open
- \+ *theorem* cont_diff_on_succ_iff_deriv_within
- \+ *theorem* cont_diff_on_succ_iff_fderiv_of_open
- \+ *theorem* cont_diff_on_succ_iff_fderiv_within
- \+ *theorem* cont_diff_on_succ_iff_has_fderiv_within_at
- \+ *lemma* cont_diff_on_top
- \+ *theorem* cont_diff_on_top_iff_deriv_of_open
- \+ *theorem* cont_diff_on_top_iff_deriv_within
- \+ *theorem* cont_diff_on_top_iff_fderiv_of_open
- \+ *theorem* cont_diff_on_top_iff_fderiv_within
- \+ *theorem* cont_diff_on_univ
- \+ *lemma* cont_diff_on_zero
- \+ *lemma* cont_diff_pi
- \+ *lemma* cont_diff_prod_assoc
- \+ *lemma* cont_diff_prod_assoc_symm
- \+ *lemma* cont_diff_smul
- \+ *lemma* cont_diff_snd
- \+ *theorem* cont_diff_succ_iff_deriv
- \+ *theorem* cont_diff_succ_iff_fderiv
- \+ *lemma* cont_diff_top
- \+ *theorem* cont_diff_top_iff_fderiv
- \+ *lemma* cont_diff_within_at.add
- \+ *lemma* cont_diff_within_at.comp'
- \+ *lemma* cont_diff_within_at.comp
- \+ *lemma* cont_diff_within_at.comp_continuous_linear_map
- \+ *lemma* cont_diff_within_at.congr'
- \+ *lemma* cont_diff_within_at.congr
- \+ *lemma* cont_diff_within_at.congr_nhds
- \+ *lemma* cont_diff_within_at.congr_of_eventually_eq'
- \+ *lemma* cont_diff_within_at.congr_of_eventually_eq
- \+ *lemma* cont_diff_within_at.cont_diff_at
- \+ *lemma* cont_diff_within_at.cont_diff_on
- \+ *lemma* cont_diff_within_at.continuous_linear_map_comp
- \+ *lemma* cont_diff_within_at.continuous_within_at
- \+ *lemma* cont_diff_within_at.differentiable_within_at'
- \+ *lemma* cont_diff_within_at.differentiable_within_at
- \+ *lemma* cont_diff_within_at.div
- \+ *lemma* cont_diff_within_at.div_const
- \+ *lemma* cont_diff_within_at.exists_lipschitz_on_with
- \+ *lemma* cont_diff_within_at.inv
- \+ *lemma* cont_diff_within_at.mono
- \+ *lemma* cont_diff_within_at.mono_of_mem
- \+ *lemma* cont_diff_within_at.mul
- \+ *lemma* cont_diff_within_at.neg
- \+ *lemma* cont_diff_within_at.of_le
- \+ *lemma* cont_diff_within_at.pow
- \+ *lemma* cont_diff_within_at.prod
- \+ *lemma* cont_diff_within_at.prod_map'
- \+ *lemma* cont_diff_within_at.prod_map
- \+ *lemma* cont_diff_within_at.restrict_scalars
- \+ *lemma* cont_diff_within_at.smul
- \+ *lemma* cont_diff_within_at.sub
- \+ *lemma* cont_diff_within_at.sum
- \+ *def* cont_diff_within_at
- \+ *lemma* cont_diff_within_at_congr_nhds
- \+ *lemma* cont_diff_within_at_const
- \+ *lemma* cont_diff_within_at_fst
- \+ *lemma* cont_diff_within_at_id
- \+ *lemma* cont_diff_within_at_iff_forall_nat_le
- \+ *lemma* cont_diff_within_at_inter'
- \+ *lemma* cont_diff_within_at_inter
- \+ *lemma* cont_diff_within_at_nat
- \+ *lemma* cont_diff_within_at_of_subsingleton
- \+ *lemma* cont_diff_within_at_pi
- \+ *lemma* cont_diff_within_at_snd
- \+ *theorem* cont_diff_within_at_succ_iff_has_fderiv_within_at
- \+ *lemma* cont_diff_within_at_top
- \+ *theorem* cont_diff_within_at_univ
- \+ *lemma* cont_diff_within_at_zero
- \+ *lemma* cont_diff_zero
- \+ *lemma* cont_diff_zero_fun
- \+ *lemma* continuous_linear_equiv.comp_cont_diff_on_iff
- \+ *lemma* continuous_linear_equiv.comp_cont_diff_within_at_iff
- \- *lemma* continuous_linear_equiv.comp_times_cont_diff_on_iff
- \- *lemma* continuous_linear_equiv.comp_times_cont_diff_within_at_iff
- \+ *lemma* continuous_linear_equiv.cont_diff
- \+ *lemma* continuous_linear_equiv.cont_diff_on_comp_iff
- \+ *lemma* continuous_linear_equiv.cont_diff_within_at_comp_iff
- \- *lemma* continuous_linear_equiv.times_cont_diff
- \- *lemma* continuous_linear_equiv.times_cont_diff_on_comp_iff
- \- *lemma* continuous_linear_equiv.times_cont_diff_within_at_comp_iff
- \+ *lemma* continuous_linear_map.cont_diff
- \- *lemma* continuous_linear_map.times_cont_diff
- \+ *lemma* filter.eventually_eq.cont_diff_within_at_iff
- \- *lemma* filter.eventually_eq.times_cont_diff_within_at_iff
- \+ *lemma* is_bounded_bilinear_map.cont_diff
- \- *lemma* is_bounded_bilinear_map.times_cont_diff
- \+ *lemma* is_bounded_linear_map.cont_diff
- \- *lemma* is_bounded_linear_map.times_cont_diff
- \+ *lemma* linear_isometry.cont_diff
- \- *lemma* linear_isometry.times_cont_diff
- \+ *lemma* linear_isometry_equiv.cont_diff
- \- *lemma* linear_isometry_equiv.times_cont_diff
- \+ *theorem* local_homeomorph.cont_diff_at_symm
- \+ *theorem* local_homeomorph.cont_diff_at_symm_deriv
- \- *theorem* local_homeomorph.times_cont_diff_at_symm
- \- *theorem* local_homeomorph.times_cont_diff_at_symm_deriv
- \- *lemma* times_cont_diff.add
- \- *lemma* times_cont_diff.comp
- \- *lemma* times_cont_diff.comp_continuous_linear_map
- \- *lemma* times_cont_diff.comp_times_cont_diff_at
- \- *lemma* times_cont_diff.comp_times_cont_diff_on
- \- *lemma* times_cont_diff.comp_times_cont_diff_within_at
- \- *lemma* times_cont_diff.continuous
- \- *lemma* times_cont_diff.continuous_fderiv
- \- *lemma* times_cont_diff.continuous_fderiv_apply
- \- *lemma* times_cont_diff.continuous_linear_map_comp
- \- *lemma* times_cont_diff.differentiable
- \- *lemma* times_cont_diff.div
- \- *lemma* times_cont_diff.div_const
- \- *lemma* times_cont_diff.has_strict_deriv_at
- \- *lemma* times_cont_diff.has_strict_fderiv_at
- \- *lemma* times_cont_diff.inv
- \- *lemma* times_cont_diff.mul
- \- *lemma* times_cont_diff.neg
- \- *lemma* times_cont_diff.of_le
- \- *lemma* times_cont_diff.pow
- \- *lemma* times_cont_diff.prod
- \- *lemma* times_cont_diff.prod_map
- \- *lemma* times_cont_diff.restrict_scalars
- \- *lemma* times_cont_diff.smul
- \- *lemma* times_cont_diff.sub
- \- *lemma* times_cont_diff.sum
- \- *lemma* times_cont_diff.times_cont_diff_at
- \- *lemma* times_cont_diff.times_cont_diff_fderiv_apply
- \- *lemma* times_cont_diff.times_cont_diff_on
- \- *lemma* times_cont_diff.times_cont_diff_within_at
- \- *lemma* times_cont_diff_add
- \- *lemma* times_cont_diff_all_iff_nat
- \- *lemma* times_cont_diff_at.add
- \- *lemma* times_cont_diff_at.comp
- \- *lemma* times_cont_diff_at.comp_times_cont_diff_within_at
- \- *lemma* times_cont_diff_at.congr_of_eventually_eq
- \- *lemma* times_cont_diff_at.continuous_at
- \- *lemma* times_cont_diff_at.continuous_linear_map_comp
- \- *lemma* times_cont_diff_at.differentiable_at
- \- *lemma* times_cont_diff_at.div
- \- *lemma* times_cont_diff_at.div_const
- \- *lemma* times_cont_diff_at.exists_lipschitz_on_with
- \- *lemma* times_cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt
- \- *lemma* times_cont_diff_at.has_strict_deriv_at'
- \- *lemma* times_cont_diff_at.has_strict_deriv_at
- \- *lemma* times_cont_diff_at.has_strict_fderiv_at'
- \- *lemma* times_cont_diff_at.has_strict_fderiv_at
- \- *lemma* times_cont_diff_at.inv
- \- *lemma* times_cont_diff_at.mul
- \- *lemma* times_cont_diff_at.neg
- \- *lemma* times_cont_diff_at.of_le
- \- *lemma* times_cont_diff_at.pow
- \- *lemma* times_cont_diff_at.prod
- \- *lemma* times_cont_diff_at.prod_map'
- \- *lemma* times_cont_diff_at.prod_map
- \- *lemma* times_cont_diff_at.restrict_scalars
- \- *lemma* times_cont_diff_at.smul
- \- *lemma* times_cont_diff_at.sub
- \- *lemma* times_cont_diff_at.sum
- \- *lemma* times_cont_diff_at.times_cont_diff_within_at
- \- *def* times_cont_diff_at
- \- *lemma* times_cont_diff_at_const
- \- *lemma* times_cont_diff_at_fst
- \- *lemma* times_cont_diff_at_id
- \- *lemma* times_cont_diff_at_inv
- \- *lemma* times_cont_diff_at_map_inverse
- \- *lemma* times_cont_diff_at_of_subsingleton
- \- *lemma* times_cont_diff_at_pi
- \- *lemma* times_cont_diff_at_ring_inverse
- \- *lemma* times_cont_diff_at_snd
- \- *theorem* times_cont_diff_at_succ_iff_has_fderiv_at
- \- *lemma* times_cont_diff_at_top
- \- *lemma* times_cont_diff_at_zero
- \- *lemma* times_cont_diff_const
- \- *lemma* times_cont_diff_fst
- \- *lemma* times_cont_diff_id
- \- *lemma* times_cont_diff_iff_continuous_differentiable
- \- *lemma* times_cont_diff_iff_times_cont_diff_at
- \- *lemma* times_cont_diff_mul
- \- *lemma* times_cont_diff_neg
- \- *lemma* times_cont_diff_of_differentiable_iterated_fderiv
- \- *lemma* times_cont_diff_of_subsingleton
- \- *lemma* times_cont_diff_on.add
- \- *lemma* times_cont_diff_on.comp'
- \- *lemma* times_cont_diff_on.comp
- \- *lemma* times_cont_diff_on.comp_continuous_linear_map
- \- *lemma* times_cont_diff_on.congr
- \- *lemma* times_cont_diff_on.congr_mono
- \- *lemma* times_cont_diff_on.continuous_linear_map_comp
- \- *lemma* times_cont_diff_on.continuous_on
- \- *lemma* times_cont_diff_on.continuous_on_deriv_of_open
- \- *lemma* times_cont_diff_on.continuous_on_deriv_within
- \- *lemma* times_cont_diff_on.continuous_on_fderiv_of_open
- \- *lemma* times_cont_diff_on.continuous_on_fderiv_within
- \- *lemma* times_cont_diff_on.continuous_on_fderiv_within_apply
- \- *lemma* times_cont_diff_on.continuous_on_iterated_fderiv_within
- \- *lemma* times_cont_diff_on.deriv_of_open
- \- *lemma* times_cont_diff_on.deriv_within
- \- *lemma* times_cont_diff_on.differentiable_on
- \- *lemma* times_cont_diff_on.differentiable_on_iterated_fderiv_within
- \- *lemma* times_cont_diff_on.div
- \- *lemma* times_cont_diff_on.div_const
- \- *lemma* times_cont_diff_on.fderiv_of_open
- \- *lemma* times_cont_diff_on.fderiv_within
- \- *theorem* times_cont_diff_on.ftaylor_series_within
- \- *lemma* times_cont_diff_on.inv
- \- *lemma* times_cont_diff_on.mono
- \- *lemma* times_cont_diff_on.mul
- \- *lemma* times_cont_diff_on.neg
- \- *lemma* times_cont_diff_on.of_le
- \- *lemma* times_cont_diff_on.pow
- \- *lemma* times_cont_diff_on.prod
- \- *lemma* times_cont_diff_on.prod_map
- \- *lemma* times_cont_diff_on.restrict_scalars
- \- *lemma* times_cont_diff_on.smul
- \- *lemma* times_cont_diff_on.sub
- \- *lemma* times_cont_diff_on.sum
- \- *lemma* times_cont_diff_on.times_cont_diff_within_at
- \- *lemma* times_cont_diff_on_all_iff_nat
- \- *lemma* times_cont_diff_on_congr
- \- *lemma* times_cont_diff_on_const
- \- *lemma* times_cont_diff_on_fderiv_within_apply
- \- *lemma* times_cont_diff_on_fst
- \- *lemma* times_cont_diff_on_id
- \- *lemma* times_cont_diff_on_iff_continuous_on_differentiable_on
- \- *lemma* times_cont_diff_on_iff_forall_nat_le
- \- *theorem* times_cont_diff_on_iff_ftaylor_series
- \- *lemma* times_cont_diff_on_inv
- \- *lemma* times_cont_diff_on_of_continuous_on_differentiable_on
- \- *lemma* times_cont_diff_on_of_differentiable_on
- \- *lemma* times_cont_diff_on_of_locally_times_cont_diff_on
- \- *lemma* times_cont_diff_on_of_subsingleton
- \- *lemma* times_cont_diff_on_pi
- \- *lemma* times_cont_diff_on_snd
- \- *theorem* times_cont_diff_on_succ_iff_deriv_of_open
- \- *theorem* times_cont_diff_on_succ_iff_deriv_within
- \- *theorem* times_cont_diff_on_succ_iff_fderiv_of_open
- \- *theorem* times_cont_diff_on_succ_iff_fderiv_within
- \- *theorem* times_cont_diff_on_succ_iff_has_fderiv_within_at
- \- *lemma* times_cont_diff_on_top
- \- *theorem* times_cont_diff_on_top_iff_deriv_of_open
- \- *theorem* times_cont_diff_on_top_iff_deriv_within
- \- *theorem* times_cont_diff_on_top_iff_fderiv_of_open
- \- *theorem* times_cont_diff_on_top_iff_fderiv_within
- \- *theorem* times_cont_diff_on_univ
- \- *lemma* times_cont_diff_on_zero
- \- *lemma* times_cont_diff_pi
- \- *lemma* times_cont_diff_prod_assoc
- \- *lemma* times_cont_diff_prod_assoc_symm
- \- *lemma* times_cont_diff_smul
- \- *lemma* times_cont_diff_snd
- \- *theorem* times_cont_diff_succ_iff_deriv
- \- *theorem* times_cont_diff_succ_iff_fderiv
- \- *lemma* times_cont_diff_top
- \- *theorem* times_cont_diff_top_iff_fderiv
- \- *lemma* times_cont_diff_within_at.add
- \- *lemma* times_cont_diff_within_at.comp'
- \- *lemma* times_cont_diff_within_at.comp
- \- *lemma* times_cont_diff_within_at.comp_continuous_linear_map
- \- *lemma* times_cont_diff_within_at.congr'
- \- *lemma* times_cont_diff_within_at.congr
- \- *lemma* times_cont_diff_within_at.congr_nhds
- \- *lemma* times_cont_diff_within_at.congr_of_eventually_eq'
- \- *lemma* times_cont_diff_within_at.congr_of_eventually_eq
- \- *lemma* times_cont_diff_within_at.continuous_linear_map_comp
- \- *lemma* times_cont_diff_within_at.continuous_within_at
- \- *lemma* times_cont_diff_within_at.differentiable_within_at'
- \- *lemma* times_cont_diff_within_at.differentiable_within_at
- \- *lemma* times_cont_diff_within_at.div
- \- *lemma* times_cont_diff_within_at.div_const
- \- *lemma* times_cont_diff_within_at.exists_lipschitz_on_with
- \- *lemma* times_cont_diff_within_at.inv
- \- *lemma* times_cont_diff_within_at.mono
- \- *lemma* times_cont_diff_within_at.mono_of_mem
- \- *lemma* times_cont_diff_within_at.mul
- \- *lemma* times_cont_diff_within_at.neg
- \- *lemma* times_cont_diff_within_at.of_le
- \- *lemma* times_cont_diff_within_at.pow
- \- *lemma* times_cont_diff_within_at.prod
- \- *lemma* times_cont_diff_within_at.prod_map'
- \- *lemma* times_cont_diff_within_at.prod_map
- \- *lemma* times_cont_diff_within_at.restrict_scalars
- \- *lemma* times_cont_diff_within_at.smul
- \- *lemma* times_cont_diff_within_at.sub
- \- *lemma* times_cont_diff_within_at.sum
- \- *lemma* times_cont_diff_within_at.times_cont_diff_at
- \- *lemma* times_cont_diff_within_at.times_cont_diff_on
- \- *def* times_cont_diff_within_at
- \- *lemma* times_cont_diff_within_at_congr_nhds
- \- *lemma* times_cont_diff_within_at_const
- \- *lemma* times_cont_diff_within_at_fst
- \- *lemma* times_cont_diff_within_at_id
- \- *lemma* times_cont_diff_within_at_iff_forall_nat_le
- \- *lemma* times_cont_diff_within_at_inter'
- \- *lemma* times_cont_diff_within_at_inter
- \- *lemma* times_cont_diff_within_at_nat
- \- *lemma* times_cont_diff_within_at_of_subsingleton
- \- *lemma* times_cont_diff_within_at_pi
- \- *lemma* times_cont_diff_within_at_snd
- \- *theorem* times_cont_diff_within_at_succ_iff_has_fderiv_within_at
- \- *lemma* times_cont_diff_within_at_top
- \- *theorem* times_cont_diff_within_at_univ
- \- *lemma* times_cont_diff_within_at_zero
- \- *lemma* times_cont_diff_zero
- \- *lemma* times_cont_diff_zero_fun

Modified src/analysis/calculus/formal_multilinear_series.lean


Modified src/analysis/calculus/inverse.lean
- \+ *lemma* cont_diff_at.image_mem_to_local_homeomorph_target
- \+ *def* cont_diff_at.local_inverse
- \+ *lemma* cont_diff_at.local_inverse_apply_image
- \+ *lemma* cont_diff_at.mem_to_local_homeomorph_source
- \+ *def* cont_diff_at.to_local_homeomorph
- \+ *lemma* cont_diff_at.to_local_homeomorph_coe
- \+ *lemma* cont_diff_at.to_local_inverse
- \- *lemma* times_cont_diff_at.image_mem_to_local_homeomorph_target
- \- *def* times_cont_diff_at.local_inverse
- \- *lemma* times_cont_diff_at.local_inverse_apply_image
- \- *lemma* times_cont_diff_at.mem_to_local_homeomorph_source
- \- *def* times_cont_diff_at.to_local_homeomorph
- \- *lemma* times_cont_diff_at.to_local_homeomorph_coe
- \- *lemma* times_cont_diff_at.to_local_inverse

Modified src/analysis/calculus/iterated_deriv.lean
- \+ *lemma* cont_diff.continuous_iterated_deriv
- \+ *lemma* cont_diff.differentiable_iterated_deriv
- \+ *lemma* cont_diff_iff_iterated_deriv
- \+ *lemma* cont_diff_of_differentiable_iterated_deriv
- \+ *lemma* cont_diff_on.continuous_on_iterated_deriv_within
- \+ *lemma* cont_diff_on.differentiable_on_iterated_deriv_within
- \+ *lemma* cont_diff_on_iff_continuous_on_differentiable_on_deriv
- \+ *lemma* cont_diff_on_of_continuous_on_differentiable_on_deriv
- \+ *lemma* cont_diff_on_of_differentiable_on_deriv
- \- *lemma* times_cont_diff.continuous_iterated_deriv
- \- *lemma* times_cont_diff.differentiable_iterated_deriv
- \- *lemma* times_cont_diff_iff_iterated_deriv
- \- *lemma* times_cont_diff_of_differentiable_iterated_deriv
- \- *lemma* times_cont_diff_on.continuous_on_iterated_deriv_within
- \- *lemma* times_cont_diff_on.differentiable_on_iterated_deriv_within
- \- *lemma* times_cont_diff_on_iff_continuous_on_differentiable_on_deriv
- \- *lemma* times_cont_diff_on_of_continuous_on_differentiable_on_deriv
- \- *lemma* times_cont_diff_on_of_differentiable_on_deriv

Modified src/analysis/calculus/specific_functions.lean
- \+ *lemma* cont_diff_bump.R_pos
- \+ *lemma* cont_diff_bump.coe_eq_comp
- \+ *lemma* cont_diff_bump.eventually_eq_one
- \+ *lemma* cont_diff_bump.eventually_eq_one_of_mem_ball
- \+ *lemma* cont_diff_bump.exists_closure_subset
- \+ *lemma* cont_diff_bump.exists_tsupport_subset
- \+ *lemma* cont_diff_bump.le_one
- \+ *lemma* cont_diff_bump.lt_one_of_lt_dist
- \+ *lemma* cont_diff_bump.nonneg
- \+ *lemma* cont_diff_bump.one_of_mem_closed_ball
- \+ *lemma* cont_diff_bump.pos_of_mem_ball
- \+ *lemma* cont_diff_bump.support_eq
- \+ *def* cont_diff_bump.to_fun
- \+ *lemma* cont_diff_bump.tsupport_eq
- \+ *lemma* cont_diff_bump.zero_of_le_dist
- \+ *structure* cont_diff_bump
- \+ *lemma* cont_diff_bump_of_inner.R_pos
- \+ *lemma* cont_diff_bump_of_inner.eventually_eq_one
- \+ *lemma* cont_diff_bump_of_inner.eventually_eq_one_of_mem_ball
- \+ *lemma* cont_diff_bump_of_inner.le_one
- \+ *lemma* cont_diff_bump_of_inner.lt_one_of_lt_dist
- \+ *lemma* cont_diff_bump_of_inner.nonneg
- \+ *lemma* cont_diff_bump_of_inner.one_of_mem_closed_ball
- \+ *lemma* cont_diff_bump_of_inner.pos_of_mem_ball
- \+ *lemma* cont_diff_bump_of_inner.support_eq
- \+ *def* cont_diff_bump_of_inner.to_fun
- \+ *lemma* cont_diff_bump_of_inner.zero_of_le_dist
- \+ *structure* cont_diff_bump_of_inner
- \+ *lemma* exists_cont_diff_bump_function_of_mem_nhds
- \- *lemma* exists_times_cont_diff_bump_function_of_mem_nhds
- \- *lemma* times_cont_diff_bump.R_pos
- \- *lemma* times_cont_diff_bump.coe_eq_comp
- \- *lemma* times_cont_diff_bump.eventually_eq_one
- \- *lemma* times_cont_diff_bump.eventually_eq_one_of_mem_ball
- \- *lemma* times_cont_diff_bump.exists_closure_subset
- \- *lemma* times_cont_diff_bump.exists_tsupport_subset
- \- *lemma* times_cont_diff_bump.le_one
- \- *lemma* times_cont_diff_bump.lt_one_of_lt_dist
- \- *lemma* times_cont_diff_bump.nonneg
- \- *lemma* times_cont_diff_bump.one_of_mem_closed_ball
- \- *lemma* times_cont_diff_bump.pos_of_mem_ball
- \- *lemma* times_cont_diff_bump.support_eq
- \- *def* times_cont_diff_bump.to_fun
- \- *lemma* times_cont_diff_bump.tsupport_eq
- \- *lemma* times_cont_diff_bump.zero_of_le_dist
- \- *structure* times_cont_diff_bump
- \- *lemma* times_cont_diff_bump_of_inner.R_pos
- \- *lemma* times_cont_diff_bump_of_inner.eventually_eq_one
- \- *lemma* times_cont_diff_bump_of_inner.eventually_eq_one_of_mem_ball
- \- *lemma* times_cont_diff_bump_of_inner.le_one
- \- *lemma* times_cont_diff_bump_of_inner.lt_one_of_lt_dist
- \- *lemma* times_cont_diff_bump_of_inner.nonneg
- \- *lemma* times_cont_diff_bump_of_inner.one_of_mem_closed_ball
- \- *lemma* times_cont_diff_bump_of_inner.pos_of_mem_ball
- \- *lemma* times_cont_diff_bump_of_inner.support_eq
- \- *def* times_cont_diff_bump_of_inner.to_fun
- \- *lemma* times_cont_diff_bump_of_inner.zero_of_le_dist
- \- *structure* times_cont_diff_bump_of_inner

Modified src/analysis/complex/real_deriv.lean
- \+ *theorem* cont_diff.real_of_complex
- \+ *theorem* cont_diff_at.real_of_complex
- \- *theorem* times_cont_diff.real_of_complex
- \- *theorem* times_cont_diff_at.real_of_complex

Modified src/analysis/inner_product_space/calculus.lean
- \+ *lemma* cont_diff.dist
- \+ *lemma* cont_diff.inner
- \+ *lemma* cont_diff.norm
- \+ *lemma* cont_diff.norm_sq
- \+ *lemma* cont_diff_at.dist
- \+ *lemma* cont_diff_at.inner
- \+ *lemma* cont_diff_at.norm
- \+ *lemma* cont_diff_at.norm_sq
- \+ *lemma* cont_diff_at_inner
- \+ *lemma* cont_diff_at_norm
- \+ *lemma* cont_diff_inner
- \+ *lemma* cont_diff_norm_sq
- \+ *lemma* cont_diff_on.dist
- \+ *lemma* cont_diff_on.inner
- \+ *lemma* cont_diff_on.norm
- \+ *lemma* cont_diff_on.norm_sq
- \+ *lemma* cont_diff_within_at.dist
- \+ *lemma* cont_diff_within_at.inner
- \+ *lemma* cont_diff_within_at.norm
- \+ *lemma* cont_diff_within_at.norm_sq
- \- *lemma* times_cont_diff.dist
- \- *lemma* times_cont_diff.inner
- \- *lemma* times_cont_diff.norm
- \- *lemma* times_cont_diff.norm_sq
- \- *lemma* times_cont_diff_at.dist
- \- *lemma* times_cont_diff_at.inner
- \- *lemma* times_cont_diff_at.norm
- \- *lemma* times_cont_diff_at.norm_sq
- \- *lemma* times_cont_diff_at_inner
- \- *lemma* times_cont_diff_at_norm
- \- *lemma* times_cont_diff_inner
- \- *lemma* times_cont_diff_norm_sq
- \- *lemma* times_cont_diff_on.dist
- \- *lemma* times_cont_diff_on.inner
- \- *lemma* times_cont_diff_on.norm
- \- *lemma* times_cont_diff_on.norm_sq
- \- *lemma* times_cont_diff_within_at.dist
- \- *lemma* times_cont_diff_within_at.inner
- \- *lemma* times_cont_diff_within_at.norm
- \- *lemma* times_cont_diff_within_at.norm_sq

Modified src/analysis/inner_product_space/euclidean_dist.lean
- \+ *lemma* cont_diff.euclidean_dist
- \- *lemma* times_cont_diff.euclidean_dist

Modified src/analysis/special_functions/complex/log_deriv.lean
- \+ *lemma* complex.cont_diff_at_log
- \- *lemma* complex.times_cont_diff_at_log

Modified src/analysis/special_functions/exp_deriv.lean
- \+ *lemma* complex.cont_diff_exp
- \- *lemma* complex.times_cont_diff_exp
- \+ *lemma* cont_diff.cexp
- \+ *lemma* cont_diff.exp
- \+ *lemma* cont_diff_at.cexp
- \+ *lemma* cont_diff_at.exp
- \+ *lemma* cont_diff_on.cexp
- \+ *lemma* cont_diff_on.exp
- \+ *lemma* cont_diff_within_at.cexp
- \+ *lemma* cont_diff_within_at.exp
- \+ *lemma* real.cont_diff_exp
- \- *lemma* real.times_cont_diff_exp
- \- *lemma* times_cont_diff.cexp
- \- *lemma* times_cont_diff.exp
- \- *lemma* times_cont_diff_at.cexp
- \- *lemma* times_cont_diff_at.exp
- \- *lemma* times_cont_diff_on.cexp
- \- *lemma* times_cont_diff_on.exp
- \- *lemma* times_cont_diff_within_at.cexp
- \- *lemma* times_cont_diff_within_at.exp

Modified src/analysis/special_functions/log_deriv.lean
- \+ *lemma* cont_diff.log
- \+ *lemma* cont_diff_at.log
- \+ *lemma* cont_diff_on.log
- \+ *lemma* cont_diff_within_at.log
- \+ *lemma* real.cont_diff_at_log
- \+ *lemma* real.cont_diff_on_log
- \- *lemma* real.times_cont_diff_at_log
- \- *lemma* real.times_cont_diff_on_log
- \- *lemma* times_cont_diff.log
- \- *lemma* times_cont_diff_at.log
- \- *lemma* times_cont_diff_on.log
- \- *lemma* times_cont_diff_within_at.log

Modified src/analysis/special_functions/pow_deriv.lean
- \+ *lemma* cont_diff.rpow
- \+ *lemma* cont_diff.rpow_const_of_le
- \+ *lemma* cont_diff.rpow_const_of_ne
- \+ *lemma* cont_diff_at.rpow
- \+ *lemma* cont_diff_at.rpow_const_of_le
- \+ *lemma* cont_diff_at.rpow_const_of_ne
- \+ *lemma* cont_diff_on.rpow
- \+ *lemma* cont_diff_on.rpow_const_of_le
- \+ *lemma* cont_diff_on.rpow_const_of_ne
- \+ *lemma* cont_diff_within_at.rpow
- \+ *lemma* cont_diff_within_at.rpow_const_of_le
- \+ *lemma* cont_diff_within_at.rpow_const_of_ne
- \+ *lemma* real.cont_diff_at_rpow_const
- \+ *lemma* real.cont_diff_at_rpow_const_of_le
- \+ *lemma* real.cont_diff_at_rpow_const_of_ne
- \+ *lemma* real.cont_diff_at_rpow_of_ne
- \+ *lemma* real.cont_diff_rpow_const_of_le
- \- *lemma* real.times_cont_diff_at_rpow_const
- \- *lemma* real.times_cont_diff_at_rpow_const_of_le
- \- *lemma* real.times_cont_diff_at_rpow_const_of_ne
- \- *lemma* real.times_cont_diff_at_rpow_of_ne
- \- *lemma* real.times_cont_diff_rpow_const_of_le
- \- *lemma* times_cont_diff.rpow
- \- *lemma* times_cont_diff.rpow_const_of_le
- \- *lemma* times_cont_diff.rpow_const_of_ne
- \- *lemma* times_cont_diff_at.rpow
- \- *lemma* times_cont_diff_at.rpow_const_of_le
- \- *lemma* times_cont_diff_at.rpow_const_of_ne
- \- *lemma* times_cont_diff_on.rpow
- \- *lemma* times_cont_diff_on.rpow_const_of_le
- \- *lemma* times_cont_diff_on.rpow_const_of_ne
- \- *lemma* times_cont_diff_within_at.rpow
- \- *lemma* times_cont_diff_within_at.rpow_const_of_le
- \- *lemma* times_cont_diff_within_at.rpow_const_of_ne

Modified src/analysis/special_functions/sqrt.lean
- \+ *lemma* cont_diff.sqrt
- \+ *lemma* cont_diff_at.sqrt
- \+ *lemma* cont_diff_on.sqrt
- \+ *lemma* cont_diff_within_at.sqrt
- \+ *lemma* real.cont_diff_at_sqrt
- \- *lemma* real.times_cont_diff_at_sqrt
- \- *lemma* times_cont_diff.sqrt
- \- *lemma* times_cont_diff_at.sqrt
- \- *lemma* times_cont_diff_on.sqrt
- \- *lemma* times_cont_diff_within_at.sqrt

Modified src/analysis/special_functions/trigonometric/arctan_deriv.lean
- \+ *lemma* cont_diff.arctan
- \+ *lemma* cont_diff_at.arctan
- \+ *lemma* cont_diff_on.arctan
- \+ *lemma* cont_diff_within_at.arctan
- \+ *lemma* real.cont_diff_arctan
- \+ *lemma* real.cont_diff_at_tan
- \- *lemma* real.times_cont_diff_arctan
- \- *lemma* real.times_cont_diff_at_tan
- \- *lemma* times_cont_diff.arctan
- \- *lemma* times_cont_diff_at.arctan
- \- *lemma* times_cont_diff_on.arctan
- \- *lemma* times_cont_diff_within_at.arctan

Modified src/analysis/special_functions/trigonometric/complex_deriv.lean
- \+ *lemma* complex.cont_diff_at_tan
- \- *lemma* complex.times_cont_diff_at_tan

Modified src/analysis/special_functions/trigonometric/deriv.lean
- \+ *lemma* complex.cont_diff_cos
- \+ *lemma* complex.cont_diff_cosh
- \+ *lemma* complex.cont_diff_sin
- \+ *lemma* complex.cont_diff_sinh
- \- *lemma* complex.times_cont_diff_cos
- \- *lemma* complex.times_cont_diff_cosh
- \- *lemma* complex.times_cont_diff_sin
- \- *lemma* complex.times_cont_diff_sinh
- \+ *lemma* cont_diff.ccos
- \+ *lemma* cont_diff.ccosh
- \+ *lemma* cont_diff.cos
- \+ *lemma* cont_diff.cosh
- \+ *lemma* cont_diff.csin
- \+ *lemma* cont_diff.csinh
- \+ *lemma* cont_diff.sin
- \+ *lemma* cont_diff.sinh
- \+ *lemma* cont_diff_at.ccos
- \+ *lemma* cont_diff_at.ccosh
- \+ *lemma* cont_diff_at.cos
- \+ *lemma* cont_diff_at.cosh
- \+ *lemma* cont_diff_at.csin
- \+ *lemma* cont_diff_at.csinh
- \+ *lemma* cont_diff_at.sin
- \+ *lemma* cont_diff_at.sinh
- \+ *lemma* cont_diff_on.ccos
- \+ *lemma* cont_diff_on.ccosh
- \+ *lemma* cont_diff_on.cos
- \+ *lemma* cont_diff_on.cosh
- \+ *lemma* cont_diff_on.csin
- \+ *lemma* cont_diff_on.csinh
- \+ *lemma* cont_diff_on.sin
- \+ *lemma* cont_diff_on.sinh
- \+ *lemma* cont_diff_within_at.ccos
- \+ *lemma* cont_diff_within_at.ccosh
- \+ *lemma* cont_diff_within_at.cos
- \+ *lemma* cont_diff_within_at.cosh
- \+ *lemma* cont_diff_within_at.csin
- \+ *lemma* cont_diff_within_at.csinh
- \+ *lemma* cont_diff_within_at.sin
- \+ *lemma* cont_diff_within_at.sinh
- \+ *lemma* real.cont_diff_cos
- \+ *lemma* real.cont_diff_cosh
- \+ *lemma* real.cont_diff_sin
- \+ *lemma* real.cont_diff_sinh
- \- *lemma* real.times_cont_diff_cos
- \- *lemma* real.times_cont_diff_cosh
- \- *lemma* real.times_cont_diff_sin
- \- *lemma* real.times_cont_diff_sinh
- \- *lemma* times_cont_diff.ccos
- \- *lemma* times_cont_diff.ccosh
- \- *lemma* times_cont_diff.cos
- \- *lemma* times_cont_diff.cosh
- \- *lemma* times_cont_diff.csin
- \- *lemma* times_cont_diff.csinh
- \- *lemma* times_cont_diff.sin
- \- *lemma* times_cont_diff.sinh
- \- *lemma* times_cont_diff_at.ccos
- \- *lemma* times_cont_diff_at.ccosh
- \- *lemma* times_cont_diff_at.cos
- \- *lemma* times_cont_diff_at.cosh
- \- *lemma* times_cont_diff_at.csin
- \- *lemma* times_cont_diff_at.csinh
- \- *lemma* times_cont_diff_at.sin
- \- *lemma* times_cont_diff_at.sinh
- \- *lemma* times_cont_diff_on.ccos
- \- *lemma* times_cont_diff_on.ccosh
- \- *lemma* times_cont_diff_on.cos
- \- *lemma* times_cont_diff_on.cosh
- \- *lemma* times_cont_diff_on.csin
- \- *lemma* times_cont_diff_on.csinh
- \- *lemma* times_cont_diff_on.sin
- \- *lemma* times_cont_diff_on.sinh
- \- *lemma* times_cont_diff_within_at.ccos
- \- *lemma* times_cont_diff_within_at.ccosh
- \- *lemma* times_cont_diff_within_at.cos
- \- *lemma* times_cont_diff_within_at.cosh
- \- *lemma* times_cont_diff_within_at.csin
- \- *lemma* times_cont_diff_within_at.csinh
- \- *lemma* times_cont_diff_within_at.sin
- \- *lemma* times_cont_diff_within_at.sinh

Modified src/analysis/special_functions/trigonometric/inverse_deriv.lean
- \+ *lemma* real.cont_diff_at_arccos
- \+ *lemma* real.cont_diff_at_arccos_iff
- \+ *lemma* real.cont_diff_at_arcsin
- \+ *lemma* real.cont_diff_at_arcsin_iff
- \+ *lemma* real.cont_diff_on_arccos
- \+ *lemma* real.cont_diff_on_arcsin
- \- *lemma* real.times_cont_diff_at_arccos
- \- *lemma* real.times_cont_diff_at_arccos_iff
- \- *lemma* real.times_cont_diff_at_arcsin
- \- *lemma* real.times_cont_diff_at_arcsin_iff
- \- *lemma* real.times_cont_diff_on_arccos
- \- *lemma* real.times_cont_diff_on_arcsin

Modified src/geometry/manifold/algebra/left_invariant_derivation.lean


Modified src/geometry/manifold/algebra/lie_group.lean


Modified src/geometry/manifold/algebra/monoid.lean


Modified src/geometry/manifold/algebra/smooth_functions.lean


Modified src/geometry/manifold/algebra/structures.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/bump_function.lean
- \+/\- *lemma* smooth_bump_function.R_pos
- \+/\- *structure* smooth_bump_function

Renamed src/geometry/manifold/times_cont_mdiff.lean to src/geometry/manifold/cont_mdiff.lean
- \+ *lemma* basic_smooth_bundle_core.cont_mdiff_at_proj
- \+ *lemma* basic_smooth_bundle_core.cont_mdiff_on_proj
- \+ *lemma* basic_smooth_bundle_core.cont_mdiff_proj
- \+ *lemma* basic_smooth_bundle_core.cont_mdiff_within_at_proj
- \- *lemma* basic_smooth_bundle_core.times_cont_mdiff_at_proj
- \- *lemma* basic_smooth_bundle_core.times_cont_mdiff_on_proj
- \- *lemma* basic_smooth_bundle_core.times_cont_mdiff_proj
- \- *lemma* basic_smooth_bundle_core.times_cont_mdiff_within_at_proj
- \+ *lemma* cont_diff_within_at_local_invariant_prop
- \+ *lemma* cont_diff_within_at_local_invariant_prop_id
- \+ *lemma* cont_diff_within_at_local_invariant_prop_mono
- \+ *def* cont_diff_within_at_prop
- \+ *lemma* cont_mdiff.comp
- \+ *lemma* cont_mdiff.comp_cont_mdiff_on
- \+ *lemma* cont_mdiff.cont_mdiff_at
- \+ *lemma* cont_mdiff.cont_mdiff_on
- \+ *theorem* cont_mdiff.cont_mdiff_tangent_map
- \+ *lemma* cont_mdiff.continuous
- \+ *theorem* cont_mdiff.continuous_tangent_map
- \+ *lemma* cont_mdiff.mdifferentiable
- \+ *lemma* cont_mdiff.of_le
- \+ *lemma* cont_mdiff.of_succ
- \+ *lemma* cont_mdiff.prod_map
- \+ *lemma* cont_mdiff.prod_mk
- \+ *lemma* cont_mdiff.prod_mk_space
- \+ *lemma* cont_mdiff.smooth
- \+ *def* cont_mdiff
- \+ *lemma* cont_mdiff_at.comp
- \+ *lemma* cont_mdiff_at.comp_cont_mdiff_within_at
- \+ *lemma* cont_mdiff_at.congr_of_eventually_eq
- \+ *lemma* cont_mdiff_at.cont_mdiff_within_at
- \+ *lemma* cont_mdiff_at.continuous_at
- \+ *lemma* cont_mdiff_at.mdifferentiable_at
- \+ *lemma* cont_mdiff_at.of_le
- \+ *lemma* cont_mdiff_at.of_succ
- \+ *lemma* cont_mdiff_at.prod_map'
- \+ *lemma* cont_mdiff_at.prod_map
- \+ *lemma* cont_mdiff_at.prod_mk
- \+ *lemma* cont_mdiff_at.prod_mk_space
- \+ *lemma* cont_mdiff_at.smooth_at
- \+ *def* cont_mdiff_at
- \+ *lemma* cont_mdiff_at_const
- \+ *lemma* cont_mdiff_at_ext_chart_at'
- \+ *lemma* cont_mdiff_at_ext_chart_at
- \+ *lemma* cont_mdiff_at_fst
- \+ *lemma* cont_mdiff_at_id
- \+ *lemma* cont_mdiff_at_iff_cont_diff_at
- \+ *lemma* cont_mdiff_at_iff_cont_mdiff_on_nhds
- \+ *lemma* cont_mdiff_at_one
- \+ *lemma* cont_mdiff_at_pi_space
- \+ *lemma* cont_mdiff_at_snd
- \+ *lemma* cont_mdiff_at_top
- \+ *lemma* cont_mdiff_const
- \+ *lemma* cont_mdiff_fst
- \+ *lemma* cont_mdiff_id
- \+ *lemma* cont_mdiff_iff
- \+ *lemma* cont_mdiff_iff_cont_diff
- \+ *lemma* cont_mdiff_iff_target
- \+ *lemma* cont_mdiff_of_locally_cont_mdiff_on
- \+ *lemma* cont_mdiff_of_support
- \+ *lemma* cont_mdiff_on.comp'
- \+ *lemma* cont_mdiff_on.comp
- \+ *lemma* cont_mdiff_on.congr
- \+ *theorem* cont_mdiff_on.cont_mdiff_on_tangent_map_within
- \+ *lemma* cont_mdiff_on.cont_mdiff_on_tangent_map_within_aux
- \+ *lemma* cont_mdiff_on.continuous_on
- \+ *theorem* cont_mdiff_on.continuous_on_tangent_map_within
- \+ *lemma* cont_mdiff_on.continuous_on_tangent_map_within_aux
- \+ *lemma* cont_mdiff_on.mdifferentiable_on
- \+ *lemma* cont_mdiff_on.mono
- \+ *lemma* cont_mdiff_on.of_le
- \+ *lemma* cont_mdiff_on.of_succ
- \+ *lemma* cont_mdiff_on.prod_map
- \+ *lemma* cont_mdiff_on.prod_mk
- \+ *lemma* cont_mdiff_on.prod_mk_space
- \+ *lemma* cont_mdiff_on.smooth_on
- \+ *def* cont_mdiff_on
- \+ *lemma* cont_mdiff_on_chart
- \+ *lemma* cont_mdiff_on_chart_symm
- \+ *lemma* cont_mdiff_on_congr
- \+ *lemma* cont_mdiff_on_const
- \+ *lemma* cont_mdiff_on_ext_chart_at
- \+ *lemma* cont_mdiff_on_fst
- \+ *lemma* cont_mdiff_on_id
- \+ *lemma* cont_mdiff_on_iff
- \+ *lemma* cont_mdiff_on_iff_cont_diff_on
- \+ *lemma* cont_mdiff_on_iff_target
- \+ *lemma* cont_mdiff_on_of_locally_cont_mdiff_on
- \+ *lemma* cont_mdiff_on_of_mem_maximal_atlas
- \+ *lemma* cont_mdiff_on_one
- \+ *lemma* cont_mdiff_on_pi_space
- \+ *lemma* cont_mdiff_on_snd
- \+ *lemma* cont_mdiff_on_symm_of_mem_maximal_atlas
- \+ *lemma* cont_mdiff_on_top
- \+ *lemma* cont_mdiff_on_univ
- \+ *lemma* cont_mdiff_one
- \+ *lemma* cont_mdiff_pi_space
- \+ *lemma* cont_mdiff_snd
- \+ *lemma* cont_mdiff_top
- \+ *lemma* cont_mdiff_within_at.comp'
- \+ *lemma* cont_mdiff_within_at.comp
- \+ *lemma* cont_mdiff_within_at.congr
- \+ *lemma* cont_mdiff_within_at.congr_of_eventually_eq
- \+ *lemma* cont_mdiff_within_at.cont_mdiff_at
- \+ *lemma* cont_mdiff_within_at.continuous_within_at
- \+ *lemma* cont_mdiff_within_at.mdifferentiable_within_at
- \+ *lemma* cont_mdiff_within_at.mono
- \+ *lemma* cont_mdiff_within_at.of_le
- \+ *lemma* cont_mdiff_within_at.of_succ
- \+ *lemma* cont_mdiff_within_at.prod_map'
- \+ *lemma* cont_mdiff_within_at.prod_map
- \+ *lemma* cont_mdiff_within_at.prod_mk
- \+ *lemma* cont_mdiff_within_at.prod_mk_space
- \+ *lemma* cont_mdiff_within_at.smooth_within_at
- \+ *def* cont_mdiff_within_at
- \+ *lemma* cont_mdiff_within_at_congr
- \+ *lemma* cont_mdiff_within_at_const
- \+ *lemma* cont_mdiff_within_at_fst
- \+ *lemma* cont_mdiff_within_at_id
- \+ *lemma* cont_mdiff_within_at_iff''
- \+ *lemma* cont_mdiff_within_at_iff'
- \+ *lemma* cont_mdiff_within_at_iff
- \+ *lemma* cont_mdiff_within_at_iff_cont_diff_within_at
- \+ *lemma* cont_mdiff_within_at_iff_cont_mdiff_on_nhds
- \+ *lemma* cont_mdiff_within_at_iff_nat
- \+ *lemma* cont_mdiff_within_at_iff_target
- \+ *lemma* cont_mdiff_within_at_inter'
- \+ *lemma* cont_mdiff_within_at_inter
- \+ *lemma* cont_mdiff_within_at_one
- \+ *lemma* cont_mdiff_within_at_pi_space
- \+ *lemma* cont_mdiff_within_at_snd
- \+ *lemma* cont_mdiff_within_at_top
- \+ *lemma* cont_mdiff_within_at_univ
- \+ *lemma* continuous_linear_map.cont_mdiff
- \- *lemma* continuous_linear_map.times_cont_mdiff
- \+ *lemma* filter.eventually_eq.cont_mdiff_at_iff
- \+ *lemma* filter.eventually_eq.cont_mdiff_within_at_iff
- \- *lemma* filter.eventually_eq.times_cont_mdiff_at_iff
- \- *lemma* filter.eventually_eq.times_cont_mdiff_within_at_iff
- \+ *lemma* smooth.cont_mdiff
- \- *lemma* smooth.times_cont_mdiff
- \+/\- *def* smooth
- \+ *lemma* smooth_at.cont_mdiff_at
- \- *lemma* smooth_at.times_cont_mdiff_at
- \+/\- *def* smooth_at
- \+/\- *lemma* smooth_at_id
- \+/\- *lemma* smooth_const
- \+/\- *lemma* smooth_id
- \+ *lemma* smooth_on.cont_mdiff_on
- \- *lemma* smooth_on.times_cont_mdiff_on
- \+/\- *def* smooth_on
- \+/\- *lemma* smooth_on_id
- \+ *lemma* smooth_within_at.cont_mdiff_within_at
- \- *lemma* smooth_within_at.times_cont_mdiff_within_at
- \+/\- *lemma* smooth_within_at_id
- \+ *lemma* tangent_bundle.cont_mdiff_at_proj
- \+ *lemma* tangent_bundle.cont_mdiff_on_proj
- \+ *lemma* tangent_bundle.cont_mdiff_proj
- \+ *lemma* tangent_bundle.cont_mdiff_within_at_proj
- \- *lemma* tangent_bundle.times_cont_mdiff_at_proj
- \- *lemma* tangent_bundle.times_cont_mdiff_on_proj
- \- *lemma* tangent_bundle.times_cont_mdiff_proj
- \- *lemma* tangent_bundle.times_cont_mdiff_within_at_proj
- \- *lemma* times_cont_diff_within_at_local_invariant_prop
- \- *lemma* times_cont_diff_within_at_local_invariant_prop_id
- \- *lemma* times_cont_diff_within_at_local_invariant_prop_mono
- \- *def* times_cont_diff_within_at_prop
- \- *lemma* times_cont_mdiff.comp
- \- *lemma* times_cont_mdiff.comp_times_cont_mdiff_on
- \- *lemma* times_cont_mdiff.continuous
- \- *theorem* times_cont_mdiff.continuous_tangent_map
- \- *lemma* times_cont_mdiff.mdifferentiable
- \- *lemma* times_cont_mdiff.of_le
- \- *lemma* times_cont_mdiff.of_succ
- \- *lemma* times_cont_mdiff.prod_map
- \- *lemma* times_cont_mdiff.prod_mk
- \- *lemma* times_cont_mdiff.prod_mk_space
- \- *lemma* times_cont_mdiff.smooth
- \- *lemma* times_cont_mdiff.times_cont_mdiff_at
- \- *lemma* times_cont_mdiff.times_cont_mdiff_on
- \- *theorem* times_cont_mdiff.times_cont_mdiff_tangent_map
- \- *def* times_cont_mdiff
- \- *lemma* times_cont_mdiff_at.comp
- \- *lemma* times_cont_mdiff_at.comp_times_cont_mdiff_within_at
- \- *lemma* times_cont_mdiff_at.congr_of_eventually_eq
- \- *lemma* times_cont_mdiff_at.continuous_at
- \- *lemma* times_cont_mdiff_at.mdifferentiable_at
- \- *lemma* times_cont_mdiff_at.of_le
- \- *lemma* times_cont_mdiff_at.of_succ
- \- *lemma* times_cont_mdiff_at.prod_map'
- \- *lemma* times_cont_mdiff_at.prod_map
- \- *lemma* times_cont_mdiff_at.prod_mk
- \- *lemma* times_cont_mdiff_at.prod_mk_space
- \- *lemma* times_cont_mdiff_at.smooth_at
- \- *lemma* times_cont_mdiff_at.times_cont_mdiff_within_at
- \- *def* times_cont_mdiff_at
- \- *lemma* times_cont_mdiff_at_const
- \- *lemma* times_cont_mdiff_at_ext_chart_at'
- \- *lemma* times_cont_mdiff_at_ext_chart_at
- \- *lemma* times_cont_mdiff_at_fst
- \- *lemma* times_cont_mdiff_at_id
- \- *lemma* times_cont_mdiff_at_iff_times_cont_diff_at
- \- *lemma* times_cont_mdiff_at_iff_times_cont_mdiff_on_nhds
- \- *lemma* times_cont_mdiff_at_one
- \- *lemma* times_cont_mdiff_at_pi_space
- \- *lemma* times_cont_mdiff_at_snd
- \- *lemma* times_cont_mdiff_at_top
- \- *lemma* times_cont_mdiff_const
- \- *lemma* times_cont_mdiff_fst
- \- *lemma* times_cont_mdiff_id
- \- *lemma* times_cont_mdiff_iff
- \- *lemma* times_cont_mdiff_iff_target
- \- *lemma* times_cont_mdiff_iff_times_cont_diff
- \- *lemma* times_cont_mdiff_of_locally_times_cont_mdiff_on
- \- *lemma* times_cont_mdiff_of_support
- \- *lemma* times_cont_mdiff_on.comp'
- \- *lemma* times_cont_mdiff_on.comp
- \- *lemma* times_cont_mdiff_on.congr
- \- *lemma* times_cont_mdiff_on.continuous_on
- \- *theorem* times_cont_mdiff_on.continuous_on_tangent_map_within
- \- *lemma* times_cont_mdiff_on.continuous_on_tangent_map_within_aux
- \- *lemma* times_cont_mdiff_on.mdifferentiable_on
- \- *lemma* times_cont_mdiff_on.mono
- \- *lemma* times_cont_mdiff_on.of_le
- \- *lemma* times_cont_mdiff_on.of_succ
- \- *lemma* times_cont_mdiff_on.prod_map
- \- *lemma* times_cont_mdiff_on.prod_mk
- \- *lemma* times_cont_mdiff_on.prod_mk_space
- \- *lemma* times_cont_mdiff_on.smooth_on
- \- *theorem* times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within
- \- *lemma* times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within_aux
- \- *def* times_cont_mdiff_on
- \- *lemma* times_cont_mdiff_on_chart
- \- *lemma* times_cont_mdiff_on_chart_symm
- \- *lemma* times_cont_mdiff_on_congr
- \- *lemma* times_cont_mdiff_on_const
- \- *lemma* times_cont_mdiff_on_ext_chart_at
- \- *lemma* times_cont_mdiff_on_fst
- \- *lemma* times_cont_mdiff_on_id
- \- *lemma* times_cont_mdiff_on_iff
- \- *lemma* times_cont_mdiff_on_iff_target
- \- *lemma* times_cont_mdiff_on_iff_times_cont_diff_on
- \- *lemma* times_cont_mdiff_on_of_locally_times_cont_mdiff_on
- \- *lemma* times_cont_mdiff_on_of_mem_maximal_atlas
- \- *lemma* times_cont_mdiff_on_one
- \- *lemma* times_cont_mdiff_on_pi_space
- \- *lemma* times_cont_mdiff_on_snd
- \- *lemma* times_cont_mdiff_on_symm_of_mem_maximal_atlas
- \- *lemma* times_cont_mdiff_on_top
- \- *lemma* times_cont_mdiff_on_univ
- \- *lemma* times_cont_mdiff_one
- \- *lemma* times_cont_mdiff_pi_space
- \- *lemma* times_cont_mdiff_snd
- \- *lemma* times_cont_mdiff_top
- \- *lemma* times_cont_mdiff_within_at.comp'
- \- *lemma* times_cont_mdiff_within_at.comp
- \- *lemma* times_cont_mdiff_within_at.congr
- \- *lemma* times_cont_mdiff_within_at.congr_of_eventually_eq
- \- *lemma* times_cont_mdiff_within_at.continuous_within_at
- \- *lemma* times_cont_mdiff_within_at.mdifferentiable_within_at
- \- *lemma* times_cont_mdiff_within_at.mono
- \- *lemma* times_cont_mdiff_within_at.of_le
- \- *lemma* times_cont_mdiff_within_at.of_succ
- \- *lemma* times_cont_mdiff_within_at.prod_map'
- \- *lemma* times_cont_mdiff_within_at.prod_map
- \- *lemma* times_cont_mdiff_within_at.prod_mk
- \- *lemma* times_cont_mdiff_within_at.prod_mk_space
- \- *lemma* times_cont_mdiff_within_at.smooth_within_at
- \- *lemma* times_cont_mdiff_within_at.times_cont_mdiff_at
- \- *def* times_cont_mdiff_within_at
- \- *lemma* times_cont_mdiff_within_at_congr
- \- *lemma* times_cont_mdiff_within_at_const
- \- *lemma* times_cont_mdiff_within_at_fst
- \- *lemma* times_cont_mdiff_within_at_id
- \- *lemma* times_cont_mdiff_within_at_iff''
- \- *lemma* times_cont_mdiff_within_at_iff'
- \- *lemma* times_cont_mdiff_within_at_iff
- \- *lemma* times_cont_mdiff_within_at_iff_nat
- \- *lemma* times_cont_mdiff_within_at_iff_target
- \- *lemma* times_cont_mdiff_within_at_iff_times_cont_diff_within_at
- \- *lemma* times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds
- \- *lemma* times_cont_mdiff_within_at_inter'
- \- *lemma* times_cont_mdiff_within_at_inter
- \- *lemma* times_cont_mdiff_within_at_one
- \- *lemma* times_cont_mdiff_within_at_pi_space
- \- *lemma* times_cont_mdiff_within_at_snd
- \- *lemma* times_cont_mdiff_within_at_top
- \- *lemma* times_cont_mdiff_within_at_univ

Renamed src/geometry/manifold/times_cont_mdiff_map.lean to src/geometry/manifold/cont_mdiff_map.lean
- \+ *lemma* cont_mdiff_map.coe_fn_mk
- \+ *lemma* cont_mdiff_map.coe_inj
- \+ *def* cont_mdiff_map.comp
- \+ *lemma* cont_mdiff_map.comp_apply
- \+ *def* cont_mdiff_map.const
- \+ *theorem* cont_mdiff_map.ext
- \+ *def* cont_mdiff_map.id
- \+ *structure* cont_mdiff_map
- \+/\- *def* smooth_map
- \- *lemma* times_cont_mdiff_map.coe_fn_mk
- \- *lemma* times_cont_mdiff_map.coe_inj
- \- *def* times_cont_mdiff_map.comp
- \- *lemma* times_cont_mdiff_map.comp_apply
- \- *def* times_cont_mdiff_map.const
- \- *theorem* times_cont_mdiff_map.ext
- \- *def* times_cont_mdiff_map.id
- \- *structure* times_cont_mdiff_map

Modified src/geometry/manifold/derivation_bundle.lean


Modified src/geometry/manifold/diffeomorph.lean
- \+ *lemma* diffeomorph.cont_mdiff_at_comp_diffeomorph_iff
- \+ *lemma* diffeomorph.cont_mdiff_at_diffeomorph_comp_iff
- \+ *lemma* diffeomorph.cont_mdiff_at_trans_diffeomorph_left
- \+ *lemma* diffeomorph.cont_mdiff_at_trans_diffeomorph_right
- \+ *lemma* diffeomorph.cont_mdiff_comp_diffeomorph_iff
- \+ *lemma* diffeomorph.cont_mdiff_diffeomorph_comp_iff
- \+ *lemma* diffeomorph.cont_mdiff_on_comp_diffeomorph_iff
- \+ *lemma* diffeomorph.cont_mdiff_on_diffeomorph_comp_iff
- \+ *lemma* diffeomorph.cont_mdiff_on_trans_diffeomorph_left
- \+ *lemma* diffeomorph.cont_mdiff_on_trans_diffeomorph_right
- \+ *lemma* diffeomorph.cont_mdiff_trans_diffeomorph_left
- \+ *lemma* diffeomorph.cont_mdiff_trans_diffeomorph_right
- \+ *lemma* diffeomorph.cont_mdiff_within_at_comp_diffeomorph_iff
- \+ *lemma* diffeomorph.cont_mdiff_within_at_diffeomorph_comp_iff
- \+ *lemma* diffeomorph.cont_mdiff_within_at_trans_diffeomorph_left
- \+ *lemma* diffeomorph.cont_mdiff_within_at_trans_diffeomorph_right
- \- *lemma* diffeomorph.times_cont_mdiff_at_comp_diffeomorph_iff
- \- *lemma* diffeomorph.times_cont_mdiff_at_diffeomorph_comp_iff
- \- *lemma* diffeomorph.times_cont_mdiff_at_trans_diffeomorph_left
- \- *lemma* diffeomorph.times_cont_mdiff_at_trans_diffeomorph_right
- \- *lemma* diffeomorph.times_cont_mdiff_comp_diffeomorph_iff
- \- *lemma* diffeomorph.times_cont_mdiff_diffeomorph_comp_iff
- \- *lemma* diffeomorph.times_cont_mdiff_on_comp_diffeomorph_iff
- \- *lemma* diffeomorph.times_cont_mdiff_on_diffeomorph_comp_iff
- \- *lemma* diffeomorph.times_cont_mdiff_on_trans_diffeomorph_left
- \- *lemma* diffeomorph.times_cont_mdiff_on_trans_diffeomorph_right
- \- *lemma* diffeomorph.times_cont_mdiff_trans_diffeomorph_left
- \- *lemma* diffeomorph.times_cont_mdiff_trans_diffeomorph_right
- \- *lemma* diffeomorph.times_cont_mdiff_within_at_comp_diffeomorph_iff
- \- *lemma* diffeomorph.times_cont_mdiff_within_at_diffeomorph_comp_iff
- \- *lemma* diffeomorph.times_cont_mdiff_within_at_trans_diffeomorph_left
- \- *lemma* diffeomorph.times_cont_mdiff_within_at_trans_diffeomorph_right

Modified src/geometry/manifold/instances/real.lean


Modified src/geometry/manifold/instances/sphere.lean
- \+ *lemma* cont_diff_on_stereo_to_fun
- \+ *lemma* cont_diff_stereo_inv_fun_aux
- \+ *lemma* cont_mdiff.cod_restrict_sphere
- \+ *lemma* cont_mdiff_coe_sphere
- \+ *lemma* cont_mdiff_exp_map_circle
- \+ *lemma* cont_mdiff_neg_sphere
- \- *lemma* times_cont_diff_on_stereo_to_fun
- \- *lemma* times_cont_diff_stereo_inv_fun_aux
- \- *lemma* times_cont_mdiff.cod_restrict_sphere
- \- *lemma* times_cont_mdiff_coe_sphere
- \- *lemma* times_cont_mdiff_exp_map_circle
- \- *lemma* times_cont_mdiff_neg_sphere

Modified src/geometry/manifold/instances/units_of_normed_algebra.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/partition_of_unity.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *def* cont_diff_groupoid
- \+ *lemma* cont_diff_groupoid_le
- \+ *lemma* cont_diff_groupoid_prod
- \+ *lemma* cont_diff_groupoid_zero_eq
- \+ *lemma* of_set_mem_cont_diff_groupoid
- \- *lemma* of_set_mem_times_cont_diff_groupoid
- \+/\- *def* smooth_manifold_with_corners.maximal_atlas
- \+ *lemma* smooth_manifold_with_corners_of_cont_diff_on
- \- *lemma* smooth_manifold_with_corners_of_times_cont_diff_on
- \+ *lemma* symm_trans_mem_cont_diff_groupoid
- \- *lemma* symm_trans_mem_times_cont_diff_groupoid
- \- *def* times_cont_diff_groupoid
- \- *lemma* times_cont_diff_groupoid_le
- \- *lemma* times_cont_diff_groupoid_prod
- \- *lemma* times_cont_diff_groupoid_zero_eq

Modified src/geometry/manifold/whitney_embedding.lean


Modified src/measure_theory/integral/circle_integral.lean


Modified src/topology/metric_space/hausdorff_dimension.lean
- \+ *lemma* cont_diff.dense_compl_range_of_finrank_lt_finrank
- \+ *lemma* cont_diff.dimH_range_le
- \+ *lemma* cont_diff_on.dense_compl_image_of_dimH_lt_finrank
- \+ *lemma* cont_diff_on.dimH_image_le
- \- *lemma* times_cont_diff.dense_compl_range_of_finrank_lt_finrank
- \- *lemma* times_cont_diff.dimH_range_le
- \- *lemma* times_cont_diff_on.dense_compl_image_of_dimH_lt_finrank
- \- *lemma* times_cont_diff_on.dimH_image_le



## [2022-02-23 00:45:54](https://github.com/leanprover-community/mathlib/commit/541a1a0)
refactor(combinatorics/simple_graph/{basic,degree_sum}): move darts from degree_sum to basic ([#12195](https://github.com/leanprover-community/mathlib/pull/12195))
This also changes `simple_graph.dart` to extend `prod`, so that darts are even closer to being an ordered pair.
Since this touches the module docstrings, they are updated to use fully qualified names.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* simple_graph.adj.symm
- \+ *def* simple_graph.dart.edge
- \+ *lemma* simple_graph.dart.edge_mem
- \+ *lemma* simple_graph.dart.edge_mk
- \+ *lemma* simple_graph.dart.edge_symm
- \+ *def* simple_graph.dart.symm
- \+ *lemma* simple_graph.dart.symm_involutive
- \+ *lemma* simple_graph.dart.symm_mk
- \+ *lemma* simple_graph.dart.symm_ne
- \+ *lemma* simple_graph.dart.symm_symm
- \+ *structure* simple_graph.dart
- \+ *lemma* simple_graph.dart_edge_eq_iff
- \+ *def* simple_graph.dart_of_neighbor_set
- \+ *lemma* simple_graph.dart_of_neighbor_set_injective

Modified src/combinatorics/simple_graph/degree_sum.lean
- \- *def* simple_graph.dart.edge
- \- *lemma* simple_graph.dart.edge_mem
- \- *def* simple_graph.dart.rev
- \- *lemma* simple_graph.dart.rev_edge
- \- *lemma* simple_graph.dart.rev_involutive
- \- *lemma* simple_graph.dart.rev_ne
- \- *lemma* simple_graph.dart.rev_rev
- \- *structure* simple_graph.dart
- \- *lemma* simple_graph.dart_edge_eq_iff
- \- *def* simple_graph.dart_of_neighbor_set
- \- *lemma* simple_graph.dart_of_neighbor_set_injective

Modified src/data/sym/sym2.lean
- \+ *lemma* sym2.mk_eq_mk_iff
- \+ *lemma* sym2.mk_prod_swap_eq



## [2022-02-23 00:45:53](https://github.com/leanprover-community/mathlib/commit/f6ec999)
feat(ring_theory/localization): add a fintype instance ([#12150](https://github.com/leanprover-community/mathlib/pull/12150))
#### Estimated changes
Modified src/ring_theory/localization/basic.lean




## [2022-02-22 22:49:03](https://github.com/leanprover-community/mathlib/commit/e89222a)
feat(algebra/module,linear_algebra): some `restrict_scalars` lemmas ([#12181](https://github.com/leanprover-community/mathlib/pull/12181))
 * add `linear_map.coe_restrict_scalars` (demoting `linear_map.restrict_scalars_apply` from `simp` lemma)
 * add `submodule.restrict_scalars_eq_top_iff`
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *lemma* linear_map.coe_restrict_scalars
- \+ *lemma* linear_map.restrict_scalars_apply

Modified src/algebra/module/submodule_lattice.lean
- \+ *lemma* submodule.restrict_scalars_eq_bot_iff
- \+ *lemma* submodule.restrict_scalars_eq_top_iff



## [2022-02-22 22:49:02](https://github.com/leanprover-community/mathlib/commit/2ab3e2f)
feat(algebra/group/{hom,prod}): has_mul and mul_hom.prod ([#12110](https://github.com/leanprover-community/mathlib/pull/12110))
Ported over from `monoid_hom`.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* mul_hom.comp_mul
- \+ *lemma* mul_hom.mul_apply
- \+ *lemma* mul_hom.mul_comp

Modified src/algebra/group/pi.lean
- \+ *lemma* mul_hom.coe_mul

Modified src/algebra/group/prod.lean
- \+ *lemma* mul_hom.coe_fst
- \+ *lemma* mul_hom.coe_prod
- \+ *lemma* mul_hom.coe_prod_map
- \+ *lemma* mul_hom.coe_snd
- \+ *lemma* mul_hom.comp_coprod
- \+ *def* mul_hom.coprod
- \+ *lemma* mul_hom.coprod_apply
- \+ *def* mul_hom.fst
- \+ *lemma* mul_hom.fst_comp_prod
- \+ *lemma* mul_hom.prod_apply
- \+ *lemma* mul_hom.prod_comp_prod_map
- \+ *def* mul_hom.prod_map
- \+ *lemma* mul_hom.prod_map_def
- \+ *lemma* mul_hom.prod_unique
- \+ *def* mul_hom.snd
- \+ *lemma* mul_hom.snd_comp_prod



## [2022-02-22 22:49:01](https://github.com/leanprover-community/mathlib/commit/18d1bdf)
feat(topology/algebra/group): add subgroup lemmas ([#12026](https://github.com/leanprover-community/mathlib/pull/12026))
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* inv_mem_connected_component_one
- \+ *lemma* mul_mem_connected_component_one
- \+ *def* subgroup.connected_component_of_one
- \+ *lemma* subgroup.is_normal_topological_closure
- \+ *lemma* topological_group.continuous_conj



## [2022-02-22 22:49:00](https://github.com/leanprover-community/mathlib/commit/b60b790)
feat(topology/algebra/group): add continuity lemmas ([#11975](https://github.com/leanprover-community/mathlib/pull/11975))
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* uniform_group.uniform_continuous_iff_open_ker



## [2022-02-22 21:10:39](https://github.com/leanprover-community/mathlib/commit/64c8d21)
feat(set_theory/ordinal): `Inf_empty` ([#12226](https://github.com/leanprover-community/mathlib/pull/12226))
The docs mention that `Inf Ø` is defined as `0`. We prove that this is indeed the case.
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *theorem* ordinal.Inf_empty



## [2022-02-22 21:10:38](https://github.com/leanprover-community/mathlib/commit/d990681)
docs(set_theory/ordinal): Remove mention of `omin` from docs ([#12224](https://github.com/leanprover-community/mathlib/pull/12224))
[#11867](https://github.com/leanprover-community/mathlib/pull/11867) replaced `omin` by `Inf`. We remove all mentions of it from the docs.
#### Estimated changes
Modified src/set_theory/ordinal.lean




## [2022-02-22 21:10:37](https://github.com/leanprover-community/mathlib/commit/f7b6f42)
feat(set_theory/ordinal_arithmetic): `out_nonempty_iff_ne_zero` ([#12223](https://github.com/leanprover-community/mathlib/pull/12223))
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *theorem* ordinal.out_nonempty_iff_ne_zero



## [2022-02-22 21:10:36](https://github.com/leanprover-community/mathlib/commit/e50ebde)
chore(analysis/specific_limits): simplify proof of `cauchy_series_of_le_geometric` ([#12215](https://github.com/leanprover-community/mathlib/pull/12215))
This lemma is identical to the one above except over `range (n + 1)`
instead of `range n`. Perhaps it could be removed entirely? I'm not sure what the policy is on breaking changes.
#### Estimated changes
Modified src/analysis/specific_limits.lean




## [2022-02-22 21:10:34](https://github.com/leanprover-community/mathlib/commit/48ddfd5)
chore(linear_algebra/basic): golf `linear_equiv.smul_of_unit` ([#12190](https://github.com/leanprover-community/mathlib/pull/12190))
This already exists more generally as `distrib_mul_action.to_linear_equiv`.
The name is probably more discoverable and it needs fewer arguments, so I've left it around for now.
#### Estimated changes
Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/finite_dimensional.lean




## [2022-02-22 20:21:17](https://github.com/leanprover-community/mathlib/commit/6bb8f22)
refactor(model_theory/terms_and_formulas): Improvements to basics of first-order formulas ([#12091](https://github.com/leanprover-community/mathlib/pull/12091))
Improves the simp set of lemmas related to `realize_bounded_formula` and `realize_formula`, so that they simplify higher-level definitions directly, and keep bounded formulas and formulas separate.
Generalizes relabelling of bounded formulas.
Defines `close_with_exists` and `close_with_forall` to quantify bounded formulas into closed formulas.
Defines `bd_iff` and `iff`.
#### Estimated changes
Modified src/model_theory/basic.lean


Modified src/model_theory/definability.lean


Modified src/model_theory/direct_limit.lean


Modified src/model_theory/elementary_maps.lean
- \+/\- *lemma* first_order.language.elementary_embedding.map_formula
- \- *lemma* first_order.language.realize_bounded_formula_top
- \+/\- *lemma* first_order.language.realize_term_substructure
- \+ *lemma* first_order.language.substructure.realize_bounded_formula_top
- \+ *lemma* first_order.language.substructure.realize_formula_top

Modified src/model_theory/quotients.lean
- \- *lemma* first_order.language.realize_term_quotient_mk
- \+ *lemma* first_order.language.term.realize_quotient_mk

Modified src/model_theory/terms_and_formulas.lean
- \- *lemma* first_order.language.Theory.imp_semantically_equivalent_not_sup
- \- *lemma* first_order.language.Theory.inf_semantically_equivalent_not_sup_not
- \+/\- *def* first_order.language.Theory.is_finitely_satisfiable
- \+/\- *lemma* first_order.language.Theory.is_satisfiable.is_finitely_satisfiable
- \+/\- *lemma* first_order.language.Theory.is_satisfiable.mono
- \+/\- *def* first_order.language.Theory.is_satisfiable.some_model
- \+/\- *lemma* first_order.language.Theory.is_satisfiable.some_model_models
- \+/\- *def* first_order.language.Theory.is_satisfiable
- \+/\- *lemma* first_order.language.Theory.model.is_satisfiable
- \+/\- *def* first_order.language.Theory.models_bounded_formula
- \+/\- *lemma* first_order.language.Theory.models_formula_iff
- \+/\- *lemma* first_order.language.Theory.models_sentence_iff
- \+ *lemma* first_order.language.Theory.semantically_equivalent.realize_bd_iff
- \- *lemma* first_order.language.Theory.semantically_equivalent.realize_eq
- \+ *lemma* first_order.language.Theory.semantically_equivalent.realize_iff
- \+ *lemma* first_order.language.Theory.semantically_equivalent.some_model_realize_bd_iff
- \- *lemma* first_order.language.Theory.semantically_equivalent.some_model_realize_eq
- \+ *lemma* first_order.language.Theory.semantically_equivalent.some_model_realize_iff
- \- *lemma* first_order.language.Theory.semantically_equivalent_not_not
- \- *lemma* first_order.language.Theory.sup_semantically_equivalent_not_inf_not
- \- *def* first_order.language.bd_not
- \+ *def* first_order.language.bounded_formula.alls
- \+ *def* first_order.language.bounded_formula.exs
- \+ *lemma* first_order.language.bounded_formula.imp_semantically_equivalent_not_sup
- \+ *lemma* first_order.language.bounded_formula.inf_semantically_equivalent_not_sup_not
- \+ *def* first_order.language.bounded_formula.realize
- \+ *lemma* first_order.language.bounded_formula.realize_all
- \+ *lemma* first_order.language.bounded_formula.realize_alls
- \+ *lemma* first_order.language.bounded_formula.realize_bd_equal
- \+ *lemma* first_order.language.bounded_formula.realize_bot
- \+ *lemma* first_order.language.bounded_formula.realize_ex
- \+ *lemma* first_order.language.bounded_formula.realize_exs
- \+ *lemma* first_order.language.bounded_formula.realize_iff
- \+ *lemma* first_order.language.bounded_formula.realize_imp
- \+ *lemma* first_order.language.bounded_formula.realize_inf
- \+ *lemma* first_order.language.bounded_formula.realize_not
- \+ *lemma* first_order.language.bounded_formula.realize_rel
- \+ *lemma* first_order.language.bounded_formula.realize_relabel
- \+ *lemma* first_order.language.bounded_formula.realize_sup
- \+ *lemma* first_order.language.bounded_formula.realize_top
- \+/\- *def* first_order.language.bounded_formula.relabel
- \+ *def* first_order.language.bounded_formula.relabel_aux
- \+ *lemma* first_order.language.bounded_formula.semantically_equivalent_not_not
- \+ *lemma* first_order.language.bounded_formula.sum_elim_comp_relabel_aux
- \+ *lemma* first_order.language.bounded_formula.sup_semantically_equivalent_not_inf_not
- \+/\- *inductive* first_order.language.bounded_formula
- \+/\- *lemma* first_order.language.embedding.realize_term
- \+/\- *lemma* first_order.language.equiv.realize_bounded_formula
- \+ *lemma* first_order.language.equiv.realize_formula
- \+/\- *lemma* first_order.language.equiv.realize_term
- \- *def* first_order.language.formula.equal
- \+ *lemma* first_order.language.formula.imp_semantically_equivalent_not_sup
- \+ *lemma* first_order.language.formula.inf_semantically_equivalent_not_sup_not
- \+ *def* first_order.language.formula.realize
- \+ *lemma* first_order.language.formula.realize_bot
- \+ *lemma* first_order.language.formula.realize_equal
- \+ *lemma* first_order.language.formula.realize_graph
- \+ *lemma* first_order.language.formula.realize_iff
- \+ *lemma* first_order.language.formula.realize_imp
- \+ *lemma* first_order.language.formula.realize_inf
- \+ *lemma* first_order.language.formula.realize_not
- \+ *lemma* first_order.language.formula.realize_rel
- \+ *lemma* first_order.language.formula.realize_relabel
- \+ *lemma* first_order.language.formula.realize_sup
- \+ *lemma* first_order.language.formula.realize_top
- \+ *def* first_order.language.formula.relabel
- \+ *lemma* first_order.language.formula.semantically_equivalent_not_not
- \+ *lemma* first_order.language.formula.sup_semantically_equivalent_not_inf_not
- \+/\- *def* first_order.language.formula
- \+/\- *lemma* first_order.language.hom.realize_term
- \- *def* first_order.language.realize_bounded_formula
- \- *lemma* first_order.language.realize_bounded_formula_relabel
- \- *lemma* first_order.language.realize_equal
- \- *def* first_order.language.realize_formula
- \- *lemma* first_order.language.realize_formula_equiv
- \- *lemma* first_order.language.realize_formula_relabel
- \- *lemma* first_order.language.realize_graph
- \- *lemma* first_order.language.realize_imp
- \- *lemma* first_order.language.realize_inf
- \- *lemma* first_order.language.realize_not
- \- *def* first_order.language.realize_term
- \- *lemma* first_order.language.realize_term_relabel
- \+ *def* first_order.language.relations.bounded_formula
- \+ *def* first_order.language.relations.formula
- \+/\- *def* first_order.language.sentence
- \+ *def* first_order.language.term.bd_equal
- \+ *def* first_order.language.term.equal
- \+ *def* first_order.language.term.realize
- \+ *lemma* first_order.language.term.realize_relabel
- \+/\- *def* first_order.language.term.relabel
- \+/\- *inductive* first_order.language.term



## [2022-02-22 18:15:35](https://github.com/leanprover-community/mathlib/commit/d054fca)
feat(/analysis/inner_product_space/pi_L2): `inner_matrix_row_row` ([#12177](https://github.com/leanprover-community/mathlib/pull/12177))
The inner product between rows/columns of matrices.
#### Estimated changes
Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* inner_matrix_col_col
- \+ *lemma* inner_matrix_row_row



## [2022-02-22 18:15:34](https://github.com/leanprover-community/mathlib/commit/d0c37a1)
feat(analysis/inner_product_space/adjoint): is_self_adjoint_iff_inner… ([#12113](https://github.com/leanprover-community/mathlib/pull/12113))
…_map_self_real
A linear operator on a complex inner product space is self-adjoint
precisely when ⟪T v, v⟫ is real for all v.  I am interested in learning
style improvements!
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* inner_map_polarization'
- \+ *lemma* inner_product_space.is_self_adjoint_iff_inner_map_self_real



## [2022-02-22 18:15:32](https://github.com/leanprover-community/mathlib/commit/8f16001)
chore(*): rename `erase_dup` to `dedup` ([#12057](https://github.com/leanprover-community/mathlib/pull/12057))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean


Modified src/algebra/gcd_monoid/multiset.lean
- \+ *lemma* multiset.gcd_dedup
- \- *lemma* multiset.gcd_erase_dup
- \+ *lemma* multiset.lcm_dedup
- \- *lemma* multiset.lcm_erase_dup

Modified src/algebra/squarefree.lean


Modified src/data/fin_enum.lean


Modified src/data/finset/basic.lean
- \+ *theorem* finset.dedup_eq_self
- \- *theorem* finset.erase_dup_eq_self
- \+/\- *theorem* finset.image_val
- \+/\- *theorem* finset.insert_val'
- \+/\- *lemma* list.mem_to_finset
- \+ *lemma* list.to_finset_eq_iff_perm_dedup
- \- *lemma* list.to_finset_eq_iff_perm_erase_dup
- \+/\- *theorem* list.to_finset_val
- \+/\- *lemma* multiset.mem_to_finset
- \+/\- *def* multiset.to_finset
- \+/\- *theorem* multiset.to_finset_val

Modified src/data/finset/card.lean
- \+/\- *lemma* list.card_to_finset
- \+/\- *lemma* multiset.card_to_finset
- \+/\- *lemma* multiset.to_finset_card_le

Modified src/data/finset/noncomm_prod.lean


Modified src/data/finset/pi.lean


Modified src/data/list/alist.lean


Added src/data/list/dedup.lean
- \+ *theorem* list.dedup_append
- \+ *theorem* list.dedup_cons_of_mem'
- \+ *theorem* list.dedup_cons_of_mem
- \+ *theorem* list.dedup_cons_of_not_mem'
- \+ *theorem* list.dedup_cons_of_not_mem
- \+ *theorem* list.dedup_eq_self
- \+ *theorem* list.dedup_idempotent
- \+ *theorem* list.dedup_nil
- \+ *theorem* list.dedup_sublist
- \+ *theorem* list.dedup_subset
- \+ *theorem* list.mem_dedup
- \+ *theorem* list.nodup_dedup
- \+ *theorem* list.subset_dedup

Modified src/data/list/default.lean


Modified src/data/list/defs.lean
- \+ *def* list.dedup
- \- *def* list.erase_dup

Deleted src/data/list/erase_dup.lean
- \- *theorem* list.erase_dup_append
- \- *theorem* list.erase_dup_cons_of_mem'
- \- *theorem* list.erase_dup_cons_of_mem
- \- *theorem* list.erase_dup_cons_of_not_mem'
- \- *theorem* list.erase_dup_cons_of_not_mem
- \- *theorem* list.erase_dup_eq_self
- \- *theorem* list.erase_dup_idempotent
- \- *theorem* list.erase_dup_nil
- \- *theorem* list.erase_dup_sublist
- \- *theorem* list.erase_dup_subset
- \- *theorem* list.mem_erase_dup
- \- *theorem* list.nodup_erase_dup
- \- *theorem* list.subset_erase_dup

Modified src/data/list/perm.lean
- \+ *theorem* list.perm.dedup
- \- *theorem* list.perm.erase_dup

Modified src/data/list/sigma.lean
- \+ *def* list.dedupkeys
- \+ *lemma* list.dedupkeys_cons
- \- *def* list.erase_dupkeys
- \- *lemma* list.erase_dupkeys_cons
- \+ *lemma* list.lookup_dedupkeys
- \- *lemma* list.lookup_erase_dupkeys
- \+ *lemma* list.nodupkeys_dedupkeys
- \- *lemma* list.nodupkeys_erase_dupkeys
- \+ *lemma* list.sizeof_dedupkeys
- \- *lemma* list.sizeof_erase_dupkeys

Added src/data/multiset/dedup.lean
- \+ *theorem* multiset.coe_dedup
- \+ *def* multiset.dedup
- \+ *theorem* multiset.dedup_cons_of_mem
- \+ *theorem* multiset.dedup_cons_of_not_mem
- \+ *theorem* multiset.dedup_eq_self
- \+ *theorem* multiset.dedup_eq_zero
- \+ *theorem* multiset.dedup_ext
- \+ *theorem* multiset.dedup_le
- \+ *theorem* multiset.dedup_map_dedup_eq
- \+ *lemma* multiset.dedup_nsmul
- \+ *theorem* multiset.dedup_singleton
- \+ *theorem* multiset.dedup_subset'
- \+ *theorem* multiset.dedup_subset
- \+ *theorem* multiset.dedup_zero
- \+ *theorem* multiset.le_dedup
- \+ *theorem* multiset.mem_dedup
- \+ *lemma* multiset.nodup.le_dedup_iff_le
- \+ *lemma* multiset.nodup.le_nsmul_iff_le
- \+ *theorem* multiset.nodup_dedup
- \+ *theorem* multiset.subset_dedup'
- \+ *theorem* multiset.subset_dedup

Modified src/data/multiset/default.lean


Deleted src/data/multiset/erase_dup.lean
- \- *theorem* multiset.coe_erase_dup
- \- *def* multiset.erase_dup
- \- *theorem* multiset.erase_dup_cons_of_mem
- \- *theorem* multiset.erase_dup_cons_of_not_mem
- \- *theorem* multiset.erase_dup_eq_self
- \- *theorem* multiset.erase_dup_eq_zero
- \- *theorem* multiset.erase_dup_ext
- \- *theorem* multiset.erase_dup_le
- \- *theorem* multiset.erase_dup_map_erase_dup_eq
- \- *lemma* multiset.erase_dup_nsmul
- \- *theorem* multiset.erase_dup_singleton
- \- *theorem* multiset.erase_dup_subset'
- \- *theorem* multiset.erase_dup_subset
- \- *theorem* multiset.erase_dup_zero
- \- *theorem* multiset.le_erase_dup
- \- *theorem* multiset.mem_erase_dup
- \- *lemma* multiset.nodup.le_erase_dup_iff_le
- \- *lemma* multiset.nodup.le_nsmul_iff_le
- \- *theorem* multiset.nodup_erase_dup
- \- *theorem* multiset.subset_erase_dup'
- \- *theorem* multiset.subset_erase_dup

Modified src/data/multiset/finset_ops.lean
- \+ *theorem* multiset.dedup_add
- \+ *theorem* multiset.dedup_cons
- \- *theorem* multiset.erase_dup_add
- \- *theorem* multiset.erase_dup_cons

Modified src/data/multiset/fold.lean
- \+ *theorem* multiset.fold_dedup_idem
- \- *theorem* multiset.fold_erase_dup_idem
- \+ *theorem* multiset.le_smul_dedup
- \- *theorem* multiset.le_smul_erase_dup

Modified src/data/multiset/lattice.lean
- \+ *lemma* multiset.inf_dedup
- \- *lemma* multiset.inf_erase_dup
- \+ *lemma* multiset.sup_dedup
- \- *lemma* multiset.sup_erase_dup

Modified src/data/multiset/locally_finite.lean


Modified src/data/nat/interval.lean


Modified src/field_theory/finite/basic.lean


Modified src/group_theory/perm/concrete_cycle.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/perm/list.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/ring_theory/norm.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/trace.lean


Modified src/tactic/core.lean


Modified src/tactic/simps.lean


Modified src/tactic/where.lean


Modified src/testing/slim_check/functions.lean




## [2022-02-22 18:15:31](https://github.com/leanprover-community/mathlib/commit/35ef770)
refactor(topology/compacts): Turn into structures, use `set_like`, cleanup ([#12035](https://github.com/leanprover-community/mathlib/pull/12035))
* Change `closeds`, `compacts`, `nonempty_compacts`, `positive_compacts` from `subtype` to `structure`
* Use `set_like`
* Add missing instances
  * the `lattice` and `bounded_order` instances for `closeds`
  * the `bounded_order` instance for `compacts`
  * the `semilattice_sup` and `order_top` instances for `nonempty_compacts` 
  * the `inhabited`, `semilattice_sup` and `order_top` instances for `positive_compacts`
* kill `positive_compacts_univ` in favor of `⊤` using the new `order_top` instance
* rename `nonempty_positive_compacts` to `positive_compacts.nonempty`
* sectioning the file
#### Estimated changes
Modified src/analysis/fourier.lean
- \+/\- *def* haar_circle

Modified src/measure_theory/measure/content.lean
- \+/\- *def* measure_theory.content.inner_content
- \+/\- *lemma* measure_theory.content.inner_content_le
- \+/\- *lemma* measure_theory.content.le_inner_content
- \+/\- *lemma* measure_theory.content.le_outer_measure_compacts
- \+/\- *lemma* measure_theory.content.mono
- \+/\- *lemma* measure_theory.content.outer_measure_interior_compacts
- \+/\- *lemma* measure_theory.content.sup_disjoint

Modified src/measure_theory/measure/haar.lean
- \+/\- *lemma* measure_theory.measure.haar.chaar_mem_haar_product
- \+/\- *lemma* measure_theory.measure.haar.chaar_mono
- \+/\- *lemma* measure_theory.measure.haar.chaar_self
- \+/\- *lemma* measure_theory.measure.haar.haar_content_self
- \+/\- *def* measure_theory.measure.haar.prehaar
- \+/\- *lemma* measure_theory.measure.haar.prehaar_empty
- \+/\- *lemma* measure_theory.measure.haar.prehaar_mem_haar_product
- \+/\- *def* measure_theory.measure.haar
- \+/\- *lemma* measure_theory.measure.haar_measure_self

Modified src/measure_theory/measure/haar_lebesgue.lean
- \- *def* topological_space.positive_compacts.Icc01
- \- *def* topological_space.positive_compacts.pi_Icc01

Modified src/measure_theory/measure/haar_quotient.lean


Modified src/topology/algebra/group.lean


Modified src/topology/compacts.lean
- \+ *lemma* topological_space.closeds.closed
- \+ *lemma* topological_space.closeds.coe_bot
- \+ *lemma* topological_space.closeds.coe_inf
- \+ *lemma* topological_space.closeds.coe_mk
- \+ *lemma* topological_space.closeds.coe_sup
- \+ *lemma* topological_space.closeds.coe_top
- \+ *structure* topological_space.closeds
- \- *def* topological_space.closeds
- \- *lemma* topological_space.compacts.bot_val
- \+ *lemma* topological_space.compacts.coe_bot
- \+ *lemma* topological_space.compacts.coe_finset_sup
- \+ *lemma* topological_space.compacts.coe_inf
- \+ *lemma* topological_space.compacts.coe_map
- \+ *lemma* topological_space.compacts.coe_mk
- \+ *lemma* topological_space.compacts.coe_sup
- \+ *lemma* topological_space.compacts.coe_top
- \+ *lemma* topological_space.compacts.compact
- \- *lemma* topological_space.compacts.finset_sup_val
- \- *lemma* topological_space.compacts.map_val
- \- *lemma* topological_space.compacts.sup_val
- \+ *structure* topological_space.compacts
- \- *def* topological_space.compacts
- \+ *lemma* topological_space.nonempty_compacts.coe_mk
- \+ *lemma* topological_space.nonempty_compacts.coe_sup
- \+ *lemma* topological_space.nonempty_compacts.coe_top
- \+ *lemma* topological_space.nonempty_compacts.compact
- \+/\- *def* topological_space.nonempty_compacts.to_closeds
- \+ *structure* topological_space.nonempty_compacts
- \- *def* topological_space.nonempty_compacts
- \+ *lemma* topological_space.positive_compacts.coe_mk
- \+ *lemma* topological_space.positive_compacts.coe_sup
- \+ *lemma* topological_space.positive_compacts.coe_top
- \+ *lemma* topological_space.positive_compacts.compact
- \+ *lemma* topological_space.positive_compacts.interior_nonempty
- \+ *def* topological_space.positive_compacts.to_nonempty_compacts
- \- *def* topological_space.positive_compacts:
- \+ *structure* topological_space.positive_compacts
- \- *def* topological_space.positive_compacts_univ
- \- *lemma* topological_space.positive_compacts_univ_val

Modified src/topology/metric_space/closeds.lean
- \+/\- *lemma* emetric.closeds.edist_eq
- \+/\- *lemma* metric.lipschitz_inf_dist
- \+/\- *lemma* metric.lipschitz_inf_dist_set

Modified src/topology/metric_space/gromov_hausdorff.lean
- \+ *def* Gromov_Hausdorff.GH_space.rep
- \+/\- *lemma* Gromov_Hausdorff.GH_space.to_GH_space_rep
- \+/\- *lemma* Gromov_Hausdorff.dist_GH_dist
- \+/\- *lemma* Gromov_Hausdorff.eq_to_GH_space

Modified src/topology/metric_space/kuratowski.lean




## [2022-02-22 15:16:21](https://github.com/leanprover-community/mathlib/commit/71da192)
chore(ring_theory/graded_algebra/basic): remove commutativity requirement ([#12208](https://github.com/leanprover-community/mathlib/pull/12208))
This wasn't used
#### Estimated changes
Modified src/ring_theory/graded_algebra/basic.lean




## [2022-02-22 15:16:20](https://github.com/leanprover-community/mathlib/commit/f0401b9)
chore(ring_theory): split `localization.lean` and `dedekind_domain.lean` ([#12206](https://github.com/leanprover-community/mathlib/pull/12206))
These files were rather long and had hundreds-deep dependency graphs. I split them into smaller files with less imports, so that they are easier to build and modify.
Proof nothing was lost:
```bash
$ cat src/ring_theory/localization/*.lean | sort | comm -23 <(sort src/ring_theory/localization.lean) - | grep -E 'lemma|theorem|def|instance|class'
$ cat src/ring_theory/dedekind_domain/*.lean | sort | comm -23 <(sort src/ring_theory/dedekind_domain.lean) - | grep -E 'lemma|theorem|def|instance|class'
giving three equivalent definitions (TODO: and shows that they are equivalent).
```
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Splitting.20.60localization.2Elean.60.20and.20.60dedekind_domain.2Elean
#### Estimated changes
Modified src/algebra/category/CommRing/instances.lean


Modified src/algebra/char_p/algebra.lean


Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/prime_spectrum/basic.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/field_theory/ratfunc.lean


Modified src/linear_algebra/matrix/to_linear_equiv.lean


Modified src/number_theory/class_number/finite.lean


Modified src/number_theory/function_field.lean


Modified src/number_theory/number_field.lean


Modified src/ring_theory/class_group.lean


Added src/ring_theory/dedekind_domain/basic.lean
- \+ *lemma* is_dedekind_domain_iff
- \+ *lemma* ring.dimension_le_one.integral_closure
- \+ *lemma* ring.dimension_le_one.is_integral_closure
- \+ *lemma* ring.dimension_le_one.principal_ideal_ring
- \+ *def* ring.dimension_le_one

Added src/ring_theory/dedekind_domain/dvr.lean
- \+ *structure* is_dedekind_domain_dvr

Renamed src/ring_theory/dedekind_domain.lean to src/ring_theory/dedekind_domain/ideal.lean
- \- *lemma* exists_integral_multiples
- \- *lemma* finite_dimensional.exists_is_basis_integral
- \- *lemma* integral_closure.is_dedekind_domain
- \- *lemma* integral_closure.is_noetherian_ring
- \- *lemma* integral_closure_le_span_dual_basis
- \- *structure* is_dedekind_domain_dvr
- \- *lemma* is_dedekind_domain_iff
- \- *lemma* is_integral_closure.is_dedekind_domain
- \- *lemma* is_integral_closure.is_noetherian_ring
- \- *lemma* is_integral_closure.range_le_span_dual_basis
- \- *lemma* ring.dimension_le_one.integral_closure
- \- *lemma* ring.dimension_le_one.is_integral_closure
- \- *lemma* ring.dimension_le_one.principal_ideal_ring
- \- *def* ring.dimension_le_one

Added src/ring_theory/dedekind_domain/integral_closure.lean
- \+ *lemma* exists_integral_multiples
- \+ *lemma* finite_dimensional.exists_is_basis_integral
- \+ *lemma* integral_closure.is_dedekind_domain
- \+ *lemma* integral_closure.is_noetherian_ring
- \+ *lemma* integral_closure_le_span_dual_basis
- \+ *lemma* is_integral_closure.is_dedekind_domain
- \+ *lemma* is_integral_closure.is_noetherian_ring
- \+ *lemma* is_integral_closure.range_le_span_dual_basis

Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/ideal/over.lean


Modified src/ring_theory/integrally_closed.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/laurent_series.lean


Modified src/ring_theory/local_properties.lean


Deleted src/ring_theory/localization.lean
- \- *lemma* algebra_map_mk'
- \- *lemma* fraction_ring.mk_eq_div
- \- *def* fraction_ring
- \- *def* ideal.prime_compl
- \- *lemma* integral_closure.is_fraction_ring_of_algebraic
- \- *lemma* integral_closure.is_fraction_ring_of_finite_extension
- \- *lemma* is_fraction_ring.coe_submodule_injective
- \- *lemma* is_fraction_ring.coe_submodule_is_principal
- \- *lemma* is_fraction_ring.coe_submodule_le_coe_submodule
- \- *lemma* is_fraction_ring.coe_submodule_strict_mono
- \- *lemma* is_fraction_ring.comap_is_algebraic_iff
- \- *lemma* is_fraction_ring.div_surjective
- \- *lemma* is_fraction_ring.eq_zero_of_num_eq_zero
- \- *lemma* is_fraction_ring.exists_reduced_fraction
- \- *lemma* is_fraction_ring.integer_normalization_eq_zero_iff
- \- *lemma* is_fraction_ring.is_algebraic_iff'
- \- *lemma* is_fraction_ring.is_algebraic_iff
- \- *lemma* is_fraction_ring.is_fraction_ring_iff_of_base_ring_equiv
- \- *lemma* is_fraction_ring.is_fraction_ring_of_is_domain_of_is_localization
- \- *lemma* is_fraction_ring.is_fraction_ring_of_is_localization
- \- *lemma* is_fraction_ring.is_integer_of_is_unit_denom
- \- *lemma* is_fraction_ring.is_unit_denom_of_num_eq_zero
- \- *lemma* is_fraction_ring.is_unit_map_of_injective
- \- *lemma* is_fraction_ring.lift_algebra_map
- \- *lemma* is_fraction_ring.lift_mk'
- \- *lemma* is_fraction_ring.mk'_eq_div
- \- *lemma* is_fraction_ring.mk'_mk_eq_div
- \- *lemma* is_fraction_ring.mk'_num_denom
- \- *lemma* is_fraction_ring.nontrivial
- \- *lemma* is_fraction_ring.num_denom_reduced
- \- *lemma* is_fraction_ring.num_mul_denom_eq_num_iff_eq'
- \- *lemma* is_fraction_ring.num_mul_denom_eq_num_iff_eq
- \- *lemma* is_fraction_ring.num_mul_denom_eq_num_mul_denom_iff_eq
- \- *lemma* is_fraction_ring.to_map_eq_zero_iff
- \- *abbreviation* is_fraction_ring
- \- *lemma* is_integral_closure.is_fraction_ring_of_algebraic
- \- *lemma* is_integral_closure.is_fraction_ring_of_finite_extension
- \- *lemma* is_integral_localization'
- \- *theorem* is_integral_localization
- \- *theorem* is_integral_localization_at_leading_coeff
- \- *lemma* is_localization.alg_equiv_mk'
- \- *lemma* is_localization.alg_equiv_symm_mk'
- \- *def* is_localization.at_one
- \- *lemma* is_localization.at_prime.is_unit_mk'_iff
- \- *lemma* is_localization.at_prime.is_unit_to_map_iff
- \- *theorem* is_localization.at_prime.local_ring
- \- *lemma* is_localization.at_prime.mk'_mem_maximal_iff
- \- *lemma* is_localization.at_prime.to_map_mem_maximal_iff
- \- *def* is_localization.at_unit
- \- *def* is_localization.at_units
- \- *lemma* is_localization.away.away_map.lift_comp
- \- *lemma* is_localization.away.away_map.lift_eq
- \- *def* is_localization.away.map
- \- *abbreviation* is_localization.away
- \- *def* is_localization.coe_submodule
- \- *lemma* is_localization.coe_submodule_bot
- \- *lemma* is_localization.coe_submodule_fg
- \- *lemma* is_localization.coe_submodule_injective
- \- *lemma* is_localization.coe_submodule_is_principal
- \- *lemma* is_localization.coe_submodule_le_coe_submodule
- \- *lemma* is_localization.coe_submodule_mono
- \- *lemma* is_localization.coe_submodule_mul
- \- *lemma* is_localization.coe_submodule_span
- \- *lemma* is_localization.coe_submodule_span_singleton
- \- *lemma* is_localization.coe_submodule_strict_mono
- \- *lemma* is_localization.coe_submodule_sup
- \- *lemma* is_localization.coe_submodule_top
- \- *lemma* is_localization.coeff_integer_normalization_mem_support
- \- *lemma* is_localization.coeff_integer_normalization_of_not_mem_support
- \- *theorem* is_localization.comap_map_of_is_prime_disjoint
- \- *def* is_localization.common_denom
- \- *def* is_localization.common_denom_of_finset
- \- *lemma* is_localization.eq_iff_eq
- \- *theorem* is_localization.eq_mk'_iff_mul_eq
- \- *lemma* is_localization.eq_of_eq
- \- *lemma* is_localization.eq_zero_of_fst_eq_zero
- \- *abbreviation* is_localization.equiv_inv_submonoid
- \- *lemma* is_localization.exist_integer_multiples
- \- *lemma* is_localization.exist_integer_multiples_of_finset
- \- *lemma* is_localization.exist_integer_multiples_of_fintype
- \- *lemma* is_localization.exists_integer_multiple'
- \- *lemma* is_localization.exists_integer_multiple
- \- *lemma* is_localization.finite_type_of_monoid_fg
- \- *def* is_localization.finset_integer_multiple
- \- *lemma* is_localization.finset_integer_multiple_image
- \- *def* is_localization.integer_multiple
- \- *lemma* is_localization.integer_normalization_aeval_eq_zero
- \- *lemma* is_localization.integer_normalization_coeff
- \- *lemma* is_localization.integer_normalization_eval₂_eq_zero
- \- *lemma* is_localization.integer_normalization_map_to_map
- \- *lemma* is_localization.integer_normalization_spec
- \- *def* is_localization.inv_submonoid
- \- *theorem* is_localization.is_domain_localization
- \- *theorem* is_localization.is_domain_of_le_non_zero_divisors
- \- *def* is_localization.is_integer
- \- *lemma* is_localization.is_integer_add
- \- *lemma* is_localization.is_integer_mul
- \- *lemma* is_localization.is_integer_one
- \- *lemma* is_localization.is_integer_smul
- \- *lemma* is_localization.is_integer_zero
- \- *lemma* is_localization.is_localization_iff_of_alg_equiv
- \- *lemma* is_localization.is_localization_iff_of_base_ring_equiv
- \- *lemma* is_localization.is_localization_iff_of_ring_equiv
- \- *lemma* is_localization.is_localization_is_localization_at_prime_is_localization
- \- *lemma* is_localization.is_localization_of_alg_equiv
- \- *lemma* is_localization.is_localization_of_base_ring_equiv
- \- *lemma* is_localization.is_localization_of_is_exists_mul_mem
- \- *lemma* is_localization.is_localization_of_submonoid_le
- \- *lemma* is_localization.is_noetherian_ring
- \- *lemma* is_localization.is_prime_iff_is_prime_disjoint
- \- *lemma* is_localization.is_prime_of_is_prime_disjoint
- \- *lemma* is_localization.is_unit_comp
- \- *lemma* is_localization.lift_comp
- \- *lemma* is_localization.lift_eq
- \- *lemma* is_localization.lift_eq_iff
- \- *lemma* is_localization.lift_id
- \- *lemma* is_localization.lift_injective_iff
- \- *lemma* is_localization.lift_mk'
- \- *lemma* is_localization.lift_mk'_spec
- \- *lemma* is_localization.lift_of_comp
- \- *lemma* is_localization.lift_surjective_iff
- \- *lemma* is_localization.lift_unique
- \- *def* is_localization.localization_algebra_of_submonoid_le
- \- *lemma* is_localization.localization_is_scalar_tower_of_submonoid_le
- \- *def* is_localization.localization_localization_at_prime_iso_localization
- \- *lemma* is_localization.localization_localization_eq_iff_exists
- \- *lemma* is_localization.localization_localization_is_localization
- \- *lemma* is_localization.localization_localization_is_localization_of_has_all_units
- \- *lemma* is_localization.localization_localization_map_units
- \- *def* is_localization.localization_localization_submodule
- \- *lemma* is_localization.localization_localization_surj
- \- *theorem* is_localization.map_comap
- \- *lemma* is_localization.map_comp
- \- *lemma* is_localization.map_comp_map
- \- *lemma* is_localization.map_eq
- \- *lemma* is_localization.map_eq_zero_iff
- \- *lemma* is_localization.map_id
- \- *lemma* is_localization.map_injective_of_injective
- \- *lemma* is_localization.map_integer_multiple
- \- *lemma* is_localization.map_left_cancel
- \- *lemma* is_localization.map_map
- \- *lemma* is_localization.map_mk'
- \- *lemma* is_localization.map_non_zero_divisors_le
- \- *lemma* is_localization.map_right_cancel
- \- *lemma* is_localization.map_smul
- \- *lemma* is_localization.map_unique
- \- *lemma* is_localization.mem_coe_submodule
- \- *lemma* is_localization.mem_inv_submonoid_iff_exists_mk'
- \- *lemma* is_localization.mem_localization_localization_submodule
- \- *theorem* is_localization.mem_map_algebra_map_iff
- \- *lemma* is_localization.mk'_add
- \- *lemma* is_localization.mk'_eq_iff_eq
- \- *theorem* is_localization.mk'_eq_iff_eq_mul
- \- *lemma* is_localization.mk'_eq_iff_mk'_eq
- \- *lemma* is_localization.mk'_eq_mul_mk'_one
- \- *lemma* is_localization.mk'_eq_of_eq
- \- *lemma* is_localization.mk'_eq_zero_iff
- \- *lemma* is_localization.mk'_mem_iff
- \- *lemma* is_localization.mk'_mul
- \- *lemma* is_localization.mk'_mul_cancel_left
- \- *lemma* is_localization.mk'_mul_cancel_right
- \- *lemma* is_localization.mk'_mul_mk'_eq_one'
- \- *lemma* is_localization.mk'_mul_mk'_eq_one
- \- *lemma* is_localization.mk'_one
- \- *lemma* is_localization.mk'_sec
- \- *lemma* is_localization.mk'_self''
- \- *lemma* is_localization.mk'_self'
- \- *lemma* is_localization.mk'_self
- \- *lemma* is_localization.mk'_spec'
- \- *lemma* is_localization.mk'_spec'_mk
- \- *lemma* is_localization.mk'_spec
- \- *lemma* is_localization.mk'_spec_mk
- \- *lemma* is_localization.mk'_surjective
- \- *lemma* is_localization.monoid_hom_ext
- \- *lemma* is_localization.mul_mk'_eq_mk'_of_mul
- \- *lemma* is_localization.mul_to_inv_submonoid
- \- *lemma* is_localization.non_zero_divisors_le_comap
- \- *lemma* is_localization.of_le
- \- *def* is_localization.order_embedding
- \- *def* is_localization.order_iso_of_prime
- \- *lemma* is_localization.ring_equiv_of_ring_equiv_eq
- \- *lemma* is_localization.ring_equiv_of_ring_equiv_eq_map
- \- *lemma* is_localization.ring_equiv_of_ring_equiv_mk'
- \- *lemma* is_localization.ring_hom_ext
- \- *lemma* is_localization.sec_spec'
- \- *lemma* is_localization.sec_spec
- \- *lemma* is_localization.smul_to_inv_submonoid
- \- *lemma* is_localization.span_inv_submonoid
- \- *lemma* is_localization.submonoid_map_le_is_unit
- \- *lemma* is_localization.surj'
- \- *lemma* is_localization.surjective_quotient_map_of_maximal_of_localization
- \- *def* is_localization.to_inv_submonoid
- \- *lemma* is_localization.to_inv_submonoid_eq_mk'
- \- *lemma* is_localization.to_inv_submonoid_mul
- \- *lemma* is_localization.to_inv_submonoid_surjective
- \- *def* is_localization.to_localization_map
- \- *lemma* is_localization.to_localization_map_sec
- \- *lemma* is_localization.to_localization_map_to_map
- \- *lemma* is_localization.to_localization_map_to_map_apply
- \- *lemma* is_localization.to_map_eq_zero_iff
- \- *lemma* localization.add_mk
- \- *lemma* localization.add_mk_self
- \- *lemma* localization.alg_equiv_mk'
- \- *lemma* localization.alg_equiv_mk
- \- *lemma* localization.alg_equiv_symm_mk'
- \- *lemma* localization.alg_equiv_symm_mk
- \- *lemma* localization.at_prime.comap_maximal_ideal
- \- *lemma* localization.at_prime.map_eq_maximal_ideal
- \- *abbreviation* localization.away_lift
- \- *abbreviation* localization.away_map
- \- *lemma* localization.le_comap_prime_compl_iff
- \- *lemma* localization.lift_on_zero
- \- *lemma* localization.local_ring_hom_comp
- \- *lemma* localization.local_ring_hom_id
- \- *lemma* localization.local_ring_hom_mk'
- \- *lemma* localization.local_ring_hom_to_map
- \- *lemma* localization.local_ring_hom_unique
- \- *lemma* localization.mk_eq_mk'
- \- *lemma* localization.mk_eq_mk'_apply
- \- *lemma* localization.mk_one_eq_algebra_map
- \- *lemma* localization.mk_zero
- \- *lemma* localization.monoid_of_eq_algebra_map
- \- *lemma* localization.neg_mk
- \- *lemma* localization.to_localization_map_eq_monoid_of
- \- *lemma* localization_algebra_injective
- \- *lemma* localization_map_bijective_of_field
- \- *lemma* ring_hom.is_integral_elem_localization_at_leading_coeff

Added src/ring_theory/localization/at_prime.lean
- \+ *def* ideal.prime_compl
- \+ *lemma* is_localization.at_prime.is_unit_mk'_iff
- \+ *lemma* is_localization.at_prime.is_unit_to_map_iff
- \+ *theorem* is_localization.at_prime.local_ring
- \+ *lemma* is_localization.at_prime.mk'_mem_maximal_iff
- \+ *lemma* is_localization.at_prime.to_map_mem_maximal_iff
- \+ *lemma* localization.at_prime.comap_maximal_ideal
- \+ *lemma* localization.at_prime.map_eq_maximal_ideal
- \+ *lemma* localization.le_comap_prime_compl_iff
- \+ *lemma* localization.local_ring_hom_comp
- \+ *lemma* localization.local_ring_hom_id
- \+ *lemma* localization.local_ring_hom_mk'
- \+ *lemma* localization.local_ring_hom_to_map
- \+ *lemma* localization.local_ring_hom_unique

Added src/ring_theory/localization/away.lean
- \+ *def* is_localization.at_one
- \+ *def* is_localization.at_unit
- \+ *def* is_localization.at_units
- \+ *lemma* is_localization.away.away_map.lift_comp
- \+ *lemma* is_localization.away.away_map.lift_eq
- \+ *def* is_localization.away.map
- \+ *abbreviation* is_localization.away
- \+ *abbreviation* localization.away_lift
- \+ *abbreviation* localization.away_map

Added src/ring_theory/localization/basic.lean
- \+ *lemma* algebra_map_mk'
- \+ *lemma* is_localization.alg_equiv_mk'
- \+ *lemma* is_localization.alg_equiv_symm_mk'
- \+ *lemma* is_localization.eq_iff_eq
- \+ *theorem* is_localization.eq_mk'_iff_mul_eq
- \+ *lemma* is_localization.eq_of_eq
- \+ *lemma* is_localization.eq_zero_of_fst_eq_zero
- \+ *theorem* is_localization.is_domain_localization
- \+ *theorem* is_localization.is_domain_of_le_non_zero_divisors
- \+ *lemma* is_localization.is_localization_iff_of_alg_equiv
- \+ *lemma* is_localization.is_localization_iff_of_base_ring_equiv
- \+ *lemma* is_localization.is_localization_iff_of_ring_equiv
- \+ *lemma* is_localization.is_localization_of_alg_equiv
- \+ *lemma* is_localization.is_localization_of_base_ring_equiv
- \+ *lemma* is_localization.is_unit_comp
- \+ *lemma* is_localization.lift_comp
- \+ *lemma* is_localization.lift_eq
- \+ *lemma* is_localization.lift_eq_iff
- \+ *lemma* is_localization.lift_id
- \+ *lemma* is_localization.lift_injective_iff
- \+ *lemma* is_localization.lift_mk'
- \+ *lemma* is_localization.lift_mk'_spec
- \+ *lemma* is_localization.lift_of_comp
- \+ *lemma* is_localization.lift_surjective_iff
- \+ *lemma* is_localization.lift_unique
- \+ *lemma* is_localization.map_comp
- \+ *lemma* is_localization.map_comp_map
- \+ *lemma* is_localization.map_eq
- \+ *lemma* is_localization.map_eq_zero_iff
- \+ *lemma* is_localization.map_id
- \+ *lemma* is_localization.map_injective_of_injective
- \+ *lemma* is_localization.map_left_cancel
- \+ *lemma* is_localization.map_map
- \+ *lemma* is_localization.map_mk'
- \+ *lemma* is_localization.map_non_zero_divisors_le
- \+ *lemma* is_localization.map_right_cancel
- \+ *lemma* is_localization.map_smul
- \+ *lemma* is_localization.map_unique
- \+ *lemma* is_localization.mk'_add
- \+ *lemma* is_localization.mk'_eq_iff_eq
- \+ *theorem* is_localization.mk'_eq_iff_eq_mul
- \+ *lemma* is_localization.mk'_eq_iff_mk'_eq
- \+ *lemma* is_localization.mk'_eq_mul_mk'_one
- \+ *lemma* is_localization.mk'_eq_of_eq
- \+ *lemma* is_localization.mk'_eq_zero_iff
- \+ *lemma* is_localization.mk'_mem_iff
- \+ *lemma* is_localization.mk'_mul
- \+ *lemma* is_localization.mk'_mul_cancel_left
- \+ *lemma* is_localization.mk'_mul_cancel_right
- \+ *lemma* is_localization.mk'_mul_mk'_eq_one'
- \+ *lemma* is_localization.mk'_mul_mk'_eq_one
- \+ *lemma* is_localization.mk'_one
- \+ *lemma* is_localization.mk'_sec
- \+ *lemma* is_localization.mk'_self''
- \+ *lemma* is_localization.mk'_self'
- \+ *lemma* is_localization.mk'_self
- \+ *lemma* is_localization.mk'_spec'
- \+ *lemma* is_localization.mk'_spec'_mk
- \+ *lemma* is_localization.mk'_spec
- \+ *lemma* is_localization.mk'_spec_mk
- \+ *lemma* is_localization.mk'_surjective
- \+ *lemma* is_localization.monoid_hom_ext
- \+ *lemma* is_localization.mul_mk'_eq_mk'_of_mul
- \+ *lemma* is_localization.non_zero_divisors_le_comap
- \+ *lemma* is_localization.of_le
- \+ *lemma* is_localization.ring_equiv_of_ring_equiv_eq
- \+ *lemma* is_localization.ring_equiv_of_ring_equiv_eq_map
- \+ *lemma* is_localization.ring_equiv_of_ring_equiv_mk'
- \+ *lemma* is_localization.ring_hom_ext
- \+ *lemma* is_localization.sec_spec'
- \+ *lemma* is_localization.sec_spec
- \+ *def* is_localization.to_localization_map
- \+ *lemma* is_localization.to_localization_map_sec
- \+ *lemma* is_localization.to_localization_map_to_map
- \+ *lemma* is_localization.to_localization_map_to_map_apply
- \+ *lemma* is_localization.to_map_eq_zero_iff
- \+ *lemma* localization.add_mk
- \+ *lemma* localization.add_mk_self
- \+ *lemma* localization.alg_equiv_mk'
- \+ *lemma* localization.alg_equiv_mk
- \+ *lemma* localization.alg_equiv_symm_mk'
- \+ *lemma* localization.alg_equiv_symm_mk
- \+ *lemma* localization.lift_on_zero
- \+ *lemma* localization.mk_eq_mk'
- \+ *lemma* localization.mk_eq_mk'_apply
- \+ *lemma* localization.mk_one_eq_algebra_map
- \+ *lemma* localization.mk_zero
- \+ *lemma* localization.monoid_of_eq_algebra_map
- \+ *lemma* localization.neg_mk
- \+ *lemma* localization.to_localization_map_eq_monoid_of
- \+ *lemma* localization_algebra_injective
- \+ *lemma* localization_map_bijective_of_field

Added src/ring_theory/localization/fraction_ring.lean
- \+ *lemma* fraction_ring.mk_eq_div
- \+ *def* fraction_ring
- \+ *lemma* is_fraction_ring.div_surjective
- \+ *lemma* is_fraction_ring.is_fraction_ring_iff_of_base_ring_equiv
- \+ *lemma* is_fraction_ring.is_unit_map_of_injective
- \+ *lemma* is_fraction_ring.lift_algebra_map
- \+ *lemma* is_fraction_ring.lift_mk'
- \+ *lemma* is_fraction_ring.mk'_eq_div
- \+ *lemma* is_fraction_ring.mk'_mk_eq_div
- \+ *lemma* is_fraction_ring.nontrivial
- \+ *lemma* is_fraction_ring.to_map_eq_zero_iff
- \+ *abbreviation* is_fraction_ring

Added src/ring_theory/localization/ideal.lean
- \+ *theorem* is_localization.comap_map_of_is_prime_disjoint
- \+ *lemma* is_localization.is_prime_iff_is_prime_disjoint
- \+ *lemma* is_localization.is_prime_of_is_prime_disjoint
- \+ *theorem* is_localization.map_comap
- \+ *theorem* is_localization.mem_map_algebra_map_iff
- \+ *def* is_localization.order_embedding
- \+ *def* is_localization.order_iso_of_prime
- \+ *lemma* is_localization.surjective_quotient_map_of_maximal_of_localization

Added src/ring_theory/localization/integer.lean
- \+ *def* is_localization.common_denom
- \+ *def* is_localization.common_denom_of_finset
- \+ *lemma* is_localization.exist_integer_multiples
- \+ *lemma* is_localization.exist_integer_multiples_of_finset
- \+ *lemma* is_localization.exist_integer_multiples_of_fintype
- \+ *lemma* is_localization.exists_integer_multiple'
- \+ *lemma* is_localization.exists_integer_multiple
- \+ *def* is_localization.finset_integer_multiple
- \+ *lemma* is_localization.finset_integer_multiple_image
- \+ *def* is_localization.integer_multiple
- \+ *def* is_localization.is_integer
- \+ *lemma* is_localization.is_integer_add
- \+ *lemma* is_localization.is_integer_mul
- \+ *lemma* is_localization.is_integer_one
- \+ *lemma* is_localization.is_integer_smul
- \+ *lemma* is_localization.is_integer_zero
- \+ *lemma* is_localization.map_integer_multiple

Added src/ring_theory/localization/integral.lean
- \+ *lemma* integral_closure.is_fraction_ring_of_algebraic
- \+ *lemma* integral_closure.is_fraction_ring_of_finite_extension
- \+ *lemma* is_fraction_ring.comap_is_algebraic_iff
- \+ *lemma* is_fraction_ring.integer_normalization_eq_zero_iff
- \+ *lemma* is_fraction_ring.is_algebraic_iff'
- \+ *lemma* is_fraction_ring.is_algebraic_iff
- \+ *lemma* is_integral_closure.is_fraction_ring_of_algebraic
- \+ *lemma* is_integral_closure.is_fraction_ring_of_finite_extension
- \+ *lemma* is_integral_localization'
- \+ *theorem* is_integral_localization
- \+ *theorem* is_integral_localization_at_leading_coeff
- \+ *lemma* is_localization.coeff_integer_normalization_mem_support
- \+ *lemma* is_localization.coeff_integer_normalization_of_not_mem_support
- \+ *lemma* is_localization.integer_normalization_aeval_eq_zero
- \+ *lemma* is_localization.integer_normalization_coeff
- \+ *lemma* is_localization.integer_normalization_eval₂_eq_zero
- \+ *lemma* is_localization.integer_normalization_map_to_map
- \+ *lemma* is_localization.integer_normalization_spec
- \+ *lemma* ring_hom.is_integral_elem_localization_at_leading_coeff

Added src/ring_theory/localization/inv_submonoid.lean
- \+ *abbreviation* is_localization.equiv_inv_submonoid
- \+ *lemma* is_localization.finite_type_of_monoid_fg
- \+ *def* is_localization.inv_submonoid
- \+ *lemma* is_localization.mem_inv_submonoid_iff_exists_mk'
- \+ *lemma* is_localization.mul_to_inv_submonoid
- \+ *lemma* is_localization.smul_to_inv_submonoid
- \+ *lemma* is_localization.span_inv_submonoid
- \+ *lemma* is_localization.submonoid_map_le_is_unit
- \+ *lemma* is_localization.surj'
- \+ *def* is_localization.to_inv_submonoid
- \+ *lemma* is_localization.to_inv_submonoid_eq_mk'
- \+ *lemma* is_localization.to_inv_submonoid_mul
- \+ *lemma* is_localization.to_inv_submonoid_surjective

Added src/ring_theory/localization/localization_localization.lean
- \+ *lemma* is_fraction_ring.is_fraction_ring_of_is_domain_of_is_localization
- \+ *lemma* is_fraction_ring.is_fraction_ring_of_is_localization
- \+ *lemma* is_localization.is_localization_is_localization_at_prime_is_localization
- \+ *lemma* is_localization.is_localization_of_is_exists_mul_mem
- \+ *lemma* is_localization.is_localization_of_submonoid_le
- \+ *def* is_localization.localization_algebra_of_submonoid_le
- \+ *lemma* is_localization.localization_is_scalar_tower_of_submonoid_le
- \+ *def* is_localization.localization_localization_at_prime_iso_localization
- \+ *lemma* is_localization.localization_localization_eq_iff_exists
- \+ *lemma* is_localization.localization_localization_is_localization
- \+ *lemma* is_localization.localization_localization_is_localization_of_has_all_units
- \+ *lemma* is_localization.localization_localization_map_units
- \+ *def* is_localization.localization_localization_submodule
- \+ *lemma* is_localization.localization_localization_surj
- \+ *lemma* is_localization.mem_localization_localization_submodule

Added src/ring_theory/localization/num_denom.lean
- \+ *lemma* is_fraction_ring.eq_zero_of_num_eq_zero
- \+ *lemma* is_fraction_ring.exists_reduced_fraction
- \+ *lemma* is_fraction_ring.is_integer_of_is_unit_denom
- \+ *lemma* is_fraction_ring.is_unit_denom_of_num_eq_zero
- \+ *lemma* is_fraction_ring.mk'_num_denom
- \+ *lemma* is_fraction_ring.num_denom_reduced
- \+ *lemma* is_fraction_ring.num_mul_denom_eq_num_iff_eq'
- \+ *lemma* is_fraction_ring.num_mul_denom_eq_num_iff_eq
- \+ *lemma* is_fraction_ring.num_mul_denom_eq_num_mul_denom_iff_eq

Added src/ring_theory/localization/submodule.lean
- \+ *lemma* is_fraction_ring.coe_submodule_injective
- \+ *lemma* is_fraction_ring.coe_submodule_is_principal
- \+ *lemma* is_fraction_ring.coe_submodule_le_coe_submodule
- \+ *lemma* is_fraction_ring.coe_submodule_strict_mono
- \+ *def* is_localization.coe_submodule
- \+ *lemma* is_localization.coe_submodule_bot
- \+ *lemma* is_localization.coe_submodule_fg
- \+ *lemma* is_localization.coe_submodule_injective
- \+ *lemma* is_localization.coe_submodule_is_principal
- \+ *lemma* is_localization.coe_submodule_le_coe_submodule
- \+ *lemma* is_localization.coe_submodule_mono
- \+ *lemma* is_localization.coe_submodule_mul
- \+ *lemma* is_localization.coe_submodule_span
- \+ *lemma* is_localization.coe_submodule_span_singleton
- \+ *lemma* is_localization.coe_submodule_strict_mono
- \+ *lemma* is_localization.coe_submodule_sup
- \+ *lemma* is_localization.coe_submodule_top
- \+ *lemma* is_localization.is_noetherian_ring
- \+ *lemma* is_localization.mem_coe_submodule

Modified src/ring_theory/perfection.lean


Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean


Modified src/ring_theory/polynomial/rational_root.lean


Modified src/set_theory/surreal/dyadic.lean


Modified src/topology/algebra/localization.lean




## [2022-02-22 15:16:19](https://github.com/leanprover-community/mathlib/commit/deb5046)
feat(mv_polynomial/basic): monomial_eq_monomial_iff ([#12198](https://github.com/leanprover-community/mathlib/pull/12198))
#### Estimated changes
Modified src/data/mv_polynomial/basic.lean
- \+ *lemma* mv_polynomial.monomial_eq_monomial_iff



## [2022-02-22 15:16:18](https://github.com/leanprover-community/mathlib/commit/8b09b0e)
feat(measure_theory/group/arithmetic): add `has_measurable_smul.op` and `has_measurable_smul₂.op` ([#12196](https://github.com/leanprover-community/mathlib/pull/12196))
This matches the naming of `has_continuous_smul.op`.
#### Estimated changes
Modified src/measure_theory/group/arithmetic.lean




## [2022-02-22 15:16:17](https://github.com/leanprover-community/mathlib/commit/79c5de9)
feat(ring_theory/ideal/operations): remove unneeded assumptions from `smul_induction_on` ([#12193](https://github.com/leanprover-community/mathlib/pull/12193))
#### Estimated changes
Modified src/linear_algebra/adic_completion.lean


Modified src/ring_theory/ideal/operations.lean




## [2022-02-22 15:16:15](https://github.com/leanprover-community/mathlib/commit/f6d397f)
feat(order/hom/basic): `order_iso_class` ([#12157](https://github.com/leanprover-community/mathlib/pull/12157))
Define `order_iso_class`, following the hom refactor. Also add a few missing lemmas.
#### Estimated changes
Modified src/data/equiv/basic.lean


Modified src/linear_algebra/basic.lean
- \- *theorem* linear_map.map_le_map_iff

Modified src/linear_algebra/quotient.lean


Modified src/order/hom/basic.lean
- \+ *lemma* order_iso.ext
- \+ *lemma* order_iso.to_fun_eq_coe



## [2022-02-22 15:16:14](https://github.com/leanprover-community/mathlib/commit/4c6b0de)
feat(topology/bases): disjoint unions of second-countable spaces are second-countable ([#12061](https://github.com/leanprover-community/mathlib/pull/12061))
#### Estimated changes
Modified src/topology/bases.lean
- \+ *lemma* is_topological_basis_singletons
- \+ *lemma* topological_space.is_topological_basis.is_open_iff
- \+ *lemma* topological_space.is_topological_basis.sigma
- \+ *lemma* topological_space.is_topological_basis.sum

Modified src/topology/constructions.lean
- \+ *lemma* closed_embedding_inl
- \+ *lemma* closed_embedding_inr
- \+ *lemma* is_closed_range_inl
- \+ *lemma* is_closed_range_inr

Modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.mono_dom
- \+ *lemma* continuous_on.mono_rng

Modified src/topology/homeomorph.lean
- \+ *def* equiv.to_homeomorph_of_inducing

Modified src/topology/order.lean
- \+ *lemma* continuous_id_of_le



## [2022-02-22 13:18:00](https://github.com/leanprover-community/mathlib/commit/8413f07)
feat(topology/support): define topological support and compactly supported functions ([#11923](https://github.com/leanprover-community/mathlib/pull/11923))
* Also add some variants of the extreme value theorem.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/analysis/calculus/specific_functions.lean
- \- *lemma* times_cont_diff_bump.closure_support_eq
- \- *lemma* times_cont_diff_bump.compact_closure_support
- \- *lemma* times_cont_diff_bump.exists_closure_support_subset
- \+ *lemma* times_cont_diff_bump.exists_tsupport_subset
- \+ *lemma* times_cont_diff_bump.tsupport_eq

Modified src/analysis/normed/group/basic.lean
- \+ *lemma* continuous.bounded_above_of_compact_support
- \+ *lemma* has_compact_support_norm_iff

Modified src/geometry/manifold/bump_function.lean
- \- *lemma* smooth_bump_function.closure_support_mem_nhds
- \- *lemma* smooth_bump_function.closure_support_subset_chart_at_source
- \- *lemma* smooth_bump_function.closure_support_subset_ext_chart_at_source
- \- *lemma* smooth_bump_function.closure_support_subset_symm_image_closed_ball
- \- *lemma* smooth_bump_function.compact_closure_support
- \- *lemma* smooth_bump_function.nhds_basis_closure_support
- \+ *lemma* smooth_bump_function.nhds_basis_tsupport
- \+ *lemma* smooth_bump_function.tsupport_mem_nhds
- \+ *lemma* smooth_bump_function.tsupport_subset_chart_at_source
- \+ *lemma* smooth_bump_function.tsupport_subset_ext_chart_at_source
- \+ *lemma* smooth_bump_function.tsupport_subset_symm_image_closed_ball

Modified src/geometry/manifold/partition_of_unity.lean


Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/measure_theory/integral/integrable_on.lean
- \- *lemma* continuous.integrable_of_compact_closure_support
- \+ *lemma* continuous.integrable_of_has_compact_support

Modified src/topology/algebra/order/compact.lean
- \+ *lemma* continuous.bdd_above_range_of_has_compact_mul_support
- \+ *lemma* continuous.bdd_below_range_of_has_compact_mul_support
- \+ *lemma* continuous.exists_forall_ge'
- \+ *lemma* continuous.exists_forall_ge_of_has_compact_mul_support
- \+ *lemma* continuous.exists_forall_le'
- \+/\- *lemma* continuous.exists_forall_le
- \+ *lemma* continuous.exists_forall_le_of_has_compact_mul_support
- \+ *lemma* is_compact.bdd_above_image
- \+ *lemma* is_compact.bdd_below_image

Modified src/topology/homeomorph.lean
- \+ *lemma* has_compact_mul_support.comp_homeomorph

Modified src/topology/partition_of_unity.lean


Added src/topology/support.lean
- \+ *lemma* exists_compact_iff_has_compact_mul_support
- \+ *lemma* has_compact_mul_support.comp_closed_embedding
- \+ *lemma* has_compact_mul_support.comp_left
- \+ *lemma* has_compact_mul_support.comp₂_left
- \+ *lemma* has_compact_mul_support.intro
- \+ *lemma* has_compact_mul_support.is_compact
- \+ *lemma* has_compact_mul_support.mono'
- \+ *lemma* has_compact_mul_support.mono
- \+ *lemma* has_compact_mul_support.mul
- \+ *def* has_compact_mul_support
- \+ *lemma* has_compact_mul_support_comp_left
- \+ *lemma* has_compact_mul_support_def
- \+ *lemma* has_compact_mul_support_iff_eventually_eq
- \+ *lemma* has_compact_support.mul_left
- \+ *lemma* has_compact_support.mul_right
- \+ *lemma* has_compact_support.smul_left'
- \+ *lemma* has_compact_support.smul_left
- \+ *lemma* has_compact_support.smul_right
- \+ *lemma* image_eq_zero_of_nmem_mul_tsupport
- \+ *lemma* is_closed_mul_tsupport
- \+ *def* mul_tsupport
- \+ *lemma* mul_tsupport_eq_empty_iff
- \+ *lemma* not_mem_closure_mul_support_iff_eventually_eq
- \+ *lemma* subset_mul_tsupport



## [2022-02-22 10:50:40](https://github.com/leanprover-community/mathlib/commit/80591d6)
feat(order/hom/lattice): Finitary join-/meet-preserving maps ([#12149](https://github.com/leanprover-community/mathlib/pull/12149))
Define `sup_bot_hom`, `inf_top_hom` and their associated class.
#### Estimated changes
Modified src/order/bounded_order.lean
- \+ *def* bounded_order.lift
- \+ *def* order_bot.lift
- \+ *def* order_top.lift

Modified src/order/complete_lattice.lean
- \- *def* bounded_order.lift
- \- *def* order_bot.lift
- \- *def* order_top.lift

Modified src/order/hom/lattice.lean
- \+ *def* bounded_lattice_hom.to_inf_top_hom
- \+ *def* bounded_lattice_hom.to_sup_bot_hom
- \+ *lemma* inf_hom.bot_apply
- \+ *lemma* inf_hom.coe_bot
- \+ *lemma* inf_hom.coe_top
- \+ *lemma* inf_hom.top_apply
- \+ *lemma* inf_top_hom.cancel_left
- \+ *lemma* inf_top_hom.cancel_right
- \+ *lemma* inf_top_hom.coe_comp
- \+ *lemma* inf_top_hom.coe_id
- \+ *lemma* inf_top_hom.coe_inf
- \+ *lemma* inf_top_hom.coe_top
- \+ *def* inf_top_hom.comp
- \+ *lemma* inf_top_hom.comp_apply
- \+ *lemma* inf_top_hom.comp_assoc
- \+ *lemma* inf_top_hom.comp_id
- \+ *lemma* inf_top_hom.ext
- \+ *lemma* inf_top_hom.id_apply
- \+ *lemma* inf_top_hom.id_comp
- \+ *lemma* inf_top_hom.inf_apply
- \+ *lemma* inf_top_hom.to_fun_eq_coe
- \+ *def* inf_top_hom.to_top_hom
- \+ *lemma* inf_top_hom.top_apply
- \+ *structure* inf_top_hom
- \+ *lemma* map_finset_inf
- \+ *lemma* map_finset_sup
- \+ *lemma* sup_bot_hom.bot_apply
- \+ *lemma* sup_bot_hom.cancel_left
- \+ *lemma* sup_bot_hom.cancel_right
- \+ *lemma* sup_bot_hom.coe_bot
- \+ *lemma* sup_bot_hom.coe_comp
- \+ *lemma* sup_bot_hom.coe_id
- \+ *lemma* sup_bot_hom.coe_sup
- \+ *def* sup_bot_hom.comp
- \+ *lemma* sup_bot_hom.comp_apply
- \+ *lemma* sup_bot_hom.comp_assoc
- \+ *lemma* sup_bot_hom.comp_id
- \+ *lemma* sup_bot_hom.ext
- \+ *lemma* sup_bot_hom.id_apply
- \+ *lemma* sup_bot_hom.id_comp
- \+ *lemma* sup_bot_hom.sup_apply
- \+ *def* sup_bot_hom.to_bot_hom
- \+ *lemma* sup_bot_hom.to_fun_eq_coe
- \+ *structure* sup_bot_hom
- \+ *lemma* sup_hom.bot_apply
- \+ *lemma* sup_hom.coe_bot
- \+ *lemma* sup_hom.coe_top
- \+/\- *lemma* sup_hom.sup_apply
- \+ *lemma* sup_hom.top_apply



## [2022-02-22 10:50:39](https://github.com/leanprover-community/mathlib/commit/68efb10)
refactor(topology/*): Hom classes for continuous maps/homs ([#11909](https://github.com/leanprover-community/mathlib/pull/11909))
Add
* `continuous_map_class`
* `bounded_continuous_map_class`
* `continuous_monoid_hom_class`
* `continuous_add_monoid_hom_class`
* `continuous_map.homotopy_class`
to follow the `fun_like` design. Deprecate lemmas accordingly.
Also rename a few fields to match the convention in the rest of the library.
#### Estimated changes
Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+/\- *lemma* prime_spectrum.comap_id

Modified src/topology/algebra/continuous_monoid_hom.lean
- \+/\- *def* continuous_monoid_hom.mk'
- \+ *def* continuous_monoid_hom.to_continuous_map
- \+ *lemma* continuous_monoid_hom.to_continuous_map_injective
- \+/\- *structure* continuous_monoid_hom

Modified src/topology/category/CompHaus/default.lean


Modified src/topology/compact_open.lean
- \+/\- *lemma* continuous_map.coe_const'
- \+/\- *lemma* continuous_map.continuous_const'

Modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* continuous_map.coe_mul
- \+/\- *lemma* continuous_map.coe_one
- \+/\- *lemma* continuous_map.one_comp

Modified src/topology/continuous_function/basic.lean
- \+ *lemma* continuous_map.cancel_left
- \+ *lemma* continuous_map.cancel_right
- \+ *lemma* continuous_map.coe_comp
- \+ *lemma* continuous_map.coe_const
- \+ *lemma* continuous_map.coe_id
- \+/\- *lemma* continuous_map.comp_apply
- \+ *lemma* continuous_map.comp_assoc
- \- *lemma* continuous_map.comp_coe
- \+ *lemma* continuous_map.comp_const
- \+/\- *lemma* continuous_map.comp_id
- \+/\- *def* continuous_map.const
- \+/\- *lemma* continuous_map.const_apply
- \- *lemma* continuous_map.const_coe
- \+ *lemma* continuous_map.const_comp
- \+/\- *lemma* continuous_map.continuous_set_coe
- \+ *lemma* continuous_map.ext
- \- *theorem* continuous_map.ext
- \- *lemma* continuous_map.ext_iff
- \- *def* continuous_map.id
- \+/\- *lemma* continuous_map.id_apply
- \- *lemma* continuous_map.id_coe
- \+/\- *lemma* continuous_map.id_comp
- \+/\- *structure* continuous_map
- \+ *lemma* map_continuous_at
- \+ *lemma* map_continuous_within_at

Modified src/topology/continuous_function/bounded.lean
- \- *lemma* bounded_continuous_function.coe_injective
- \+/\- *lemma* bounded_continuous_function.ext
- \- *lemma* bounded_continuous_function.ext_iff
- \+/\- *lemma* bounded_continuous_function.forall_coe_one_iff_one
- \+/\- *def* bounded_continuous_function.restrict

Modified src/topology/continuous_function/polynomial.lean


Modified src/topology/continuous_function/stone_weierstrass.lean


Modified src/topology/homotopy/basic.lean
- \+/\- *lemma* continuous_map.homotopy.apply_one
- \+/\- *lemma* continuous_map.homotopy.apply_zero
- \- *lemma* continuous_map.homotopy.coe_fn_injective
- \+/\- *lemma* continuous_map.homotopy.ext
- \+/\- *lemma* continuous_map.homotopy_with.apply_one
- \+/\- *lemma* continuous_map.homotopy_with.apply_zero

Modified src/topology/homotopy/equiv.lean


Modified src/topology/homotopy/fundamental_groupoid.lean


Modified src/topology/homotopy/path.lean


Modified src/topology/homotopy/product.lean
- \+/\- *def* continuous_map.homotopy.pi

Modified src/topology/opens.lean
- \+/\- *lemma* topological_space.opens.comap_id

Modified src/topology/tietze_extension.lean




## [2022-02-22 10:50:38](https://github.com/leanprover-community/mathlib/commit/247943a)
feat(analysis/seminorm): add inf ([#11791](https://github.com/leanprover-community/mathlib/pull/11791))
Define the infimum of seminorms.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* seminorm.inf_apply
- \+ *lemma* seminorm.le_insert'
- \+ *lemma* seminorm.le_insert
- \+ *lemma* seminorm.smul_inf

Modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* csupr_mul_csupr_le
- \+ *lemma* csupr_mul_le
- \+ *lemma* le_cinfi_mul
- \+ *lemma* le_cinfi_mul_cinfi
- \+ *lemma* le_mul_cinfi
- \+ *lemma* mul_csupr_le



## [2022-02-22 10:10:32](https://github.com/leanprover-community/mathlib/commit/9a7ed8c)
chore(algebra/lie/engel): speed up proof of Engel's theorem slightly ([#12205](https://github.com/leanprover-community/mathlib/pull/12205))
Local measurements using `set_option profiler true` are noisy but indicate
that this speeds up elaboration of `lie_algebra.is_engelian_of_is_noetherian`
by about 20% from about 10s to about 8s.
#### Estimated changes
Modified src/algebra/lie/engel.lean




## [2022-02-22 03:09:07](https://github.com/leanprover-community/mathlib/commit/cb45da2)
feat(category_theory/limits): is_bilimit ([#12108](https://github.com/leanprover-community/mathlib/pull/12108))
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *structure* category_theory.limits.bicone.is_bilimit
- \+ *def* category_theory.limits.bicone.of_colimit_cocone
- \+ *def* category_theory.limits.bicone.of_limit_cone
- \+ *def* category_theory.limits.bicone.to_binary_bicone_is_bilimit
- \+/\- *def* category_theory.limits.bicone.to_binary_bicone_is_colimit
- \+/\- *def* category_theory.limits.bicone.to_binary_bicone_is_limit
- \+ *lemma* category_theory.limits.bicone.ι_of_is_limit
- \+ *lemma* category_theory.limits.bicone.π_of_is_colimit
- \+/\- *lemma* category_theory.limits.bicone_ι_π_ne
- \+ *structure* category_theory.limits.binary_bicone.is_bilimit
- \+ *def* category_theory.limits.binary_bicone.to_bicone
- \+ *def* category_theory.limits.binary_bicone.to_bicone_is_bilimit
- \+ *def* category_theory.limits.binary_bicone.to_bicone_is_colimit
- \+ *def* category_theory.limits.binary_bicone.to_bicone_is_limit
- \+ *def* category_theory.limits.binary_biproduct.is_bilimit
- \+ *def* category_theory.limits.biproduct.is_bilimit



## [2022-02-22 00:37:45](https://github.com/leanprover-community/mathlib/commit/e16e093)
feat(analysis/specific_limits): dirichlet and alternating series tests  ([#11908](https://github.com/leanprover-community/mathlib/pull/11908))
Adds [Dirichlet's test](https://en.wikipedia.org/wiki/Dirichlet%27s_test) along with the [alternating series test](https://en.wikipedia.org/wiki/Alternating_series_test) as a special case of the former. For the curious, [Nick Bingham's course notes](https://www.ma.imperial.ac.uk/~bin06/M2PM3-Complex-Analysis/m2pm3abeldir.pdf) give some more context on Dirichlet's test. It's somewhat obscure.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/algebra/big_operators/intervals.lean


Modified src/analysis/normed/group/infinite_sum.lean
- \+ *lemma* cauchy_seq_range_of_norm_bounded

Modified src/analysis/specific_limits.lean
- \+ *theorem* antitone.cauchy_seq_alternating_series_of_tendsto_zero
- \+ *theorem* antitone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded
- \+ *theorem* antitone.tendsto_alternating_series_of_tendsto_zero
- \+ *theorem* monotone.cauchy_seq_alternating_series_of_tendsto_zero
- \+ *theorem* monotone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded
- \+ *theorem* monotone.tendsto_alternating_series_of_tendsto_zero
- \+ *lemma* norm_sum_neg_one_pow_le

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *def* sequentially_complete.set_seq



## [2022-02-21 23:46:54](https://github.com/leanprover-community/mathlib/commit/d77e91f)
perf(geometry/euclidean): speed up proof on the edge of timing out ([#12191](https://github.com/leanprover-community/mathlib/pull/12191))
#### Estimated changes
Modified src/geometry/euclidean/oriented_angle.lean




## [2022-02-21 23:46:53](https://github.com/leanprover-community/mathlib/commit/22464cf)
feat(analysis/normed_space/basic): `norm_matrix_lt_iff` ([#12151](https://github.com/leanprover-community/mathlib/pull/12151))
A strict variant of `norm_matrix_le_iff`, using `pi_norm_lt_iff`
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_matrix_lt_iff



## [2022-02-21 22:53:11](https://github.com/leanprover-community/mathlib/commit/eb5c5ed)
feat(measure_theory/integral/set_integral): Bochner integral with respect to a measure with density ([#12123](https://github.com/leanprover-community/mathlib/pull/12123))
This PR shows that `∫ a, g a ∂(μ.with_density (λ x, f x)) = ∫ a, f a • g a ∂μ`. (This fact is already available for the Lebesgue integral, not for the Bochner integral.)
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* continuous_on.measurable_piecewise

Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable_with_density_iff_integrable_coe_smul
- \+ *lemma* measure_theory.integrable_with_density_iff_integrable_coe_smul₀
- \+/\- *lemma* measure_theory.integrable_with_density_iff_integrable_smul
- \+ *lemma* measure_theory.integrable_with_density_iff_integrable_smul₀
- \+ *lemma* measure_theory.mem_ℒ1_smul_of_L1_with_density
- \+ *lemma* measure_theory.with_density_smul_li_apply

Modified src/measure_theory/group/measure.lean


Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* integral_with_density_eq_integral_smul
- \+ *lemma* integral_with_density_eq_integral_smul₀
- \+ *lemma* set_integral_with_density_eq_set_integral_smul
- \+ *lemma* set_integral_with_density_eq_set_integral_smul₀



## [2022-02-21 22:24:46](https://github.com/leanprover-community/mathlib/commit/8aa26b2)
feat(tactic/linear_combination): improve error messages and degenerate case ([#12062](https://github.com/leanprover-community/mathlib/pull/12062))
This threads the expected type of the combination from the target throughout the tactic call.
If no hypotheses are given to combine, the behavior is effectively to just call the normalization tactic.
closes [#11990](https://github.com/leanprover-community/mathlib/pull/11990)
#### Estimated changes
Modified src/tactic/linear_combination.lean


Modified test/linear_combination.lean




## [2022-02-21 21:06:38](https://github.com/leanprover-community/mathlib/commit/2971f3d)
feat(algebra/star/self_adjoint): remove commutativity hypothesis from `has_pow (self_adjoint R)` ([#12188](https://github.com/leanprover-community/mathlib/pull/12188))
This was put in the wrong section. Powers of selfadjoint elements are still selfadjoint.
#### Estimated changes
Modified src/algebra/star/self_adjoint.lean




## [2022-02-21 21:06:37](https://github.com/leanprover-community/mathlib/commit/a607820)
feat(category_theory/equivalence): if two functors F and G are isomorphic, F is an equivalence iff G is ([#12162](https://github.com/leanprover-community/mathlib/pull/12162))
#### Estimated changes
Modified src/category_theory/equivalence.lean
- \+ *def* category_theory.is_equivalence.cancel_comp_left
- \+ *def* category_theory.is_equivalence.cancel_comp_right
- \+ *def* category_theory.is_equivalence.equiv_of_iso
- \+ *def* category_theory.is_equivalence.of_iso
- \+ *lemma* category_theory.is_equivalence.of_iso_refl
- \+ *lemma* category_theory.is_equivalence.of_iso_trans



## [2022-02-21 21:06:35](https://github.com/leanprover-community/mathlib/commit/9a17b55)
feat(analysis/normed_space/basic): `norm_entry_le_entrywise_sup_norm` ([#12159](https://github.com/leanprover-community/mathlib/pull/12159))
The entries of a matrix are at most the entrywise sup norm.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* matrix.norm_entry_le_entrywise_sup_norm



## [2022-02-21 19:14:30](https://github.com/leanprover-community/mathlib/commit/1cfbcc6)
feat(algebra/ring/ulift): add a `field` instance ([#12141](https://github.com/leanprover-community/mathlib/pull/12141))
#### Estimated changes
Modified src/algebra/group/ulift.lean


Modified src/algebra/ring/ulift.lean




## [2022-02-21 16:41:40](https://github.com/leanprover-community/mathlib/commit/e3d3681)
feat(analysis/inner_product_space/spectrum): `pos_nonneg_eigenvalues` ([#12161](https://github.com/leanprover-community/mathlib/pull/12161))
If T is a positive self-adjoint operator, then its eigenvalues are
nonnegative.  Maybe there should be a definition of "positive operator",
and maybe this should be generalized.  Guidance appreciated!
#### Estimated changes
Modified src/analysis/inner_product_space/spectrum.lean
- \+ *lemma* eigenvalue_nonneg_of_nonneg
- \+ *lemma* eigenvalue_pos_of_pos
- \+ *lemma* inner_product_apply_eigenvector



## [2022-02-21 15:30:08](https://github.com/leanprover-community/mathlib/commit/02dc6f2)
feat(probability/stopping): filtrations are a complete lattice ([#12169](https://github.com/leanprover-community/mathlib/pull/12169))
#### Estimated changes
Modified src/probability/stopping.lean
- \- *def* measure_theory.const_filtration
- \+ *lemma* measure_theory.filtration.Inf_def
- \+ *lemma* measure_theory.filtration.Sup_def
- \+ *lemma* measure_theory.filtration.coe_fn_inf
- \+ *lemma* measure_theory.filtration.coe_fn_sup
- \+ *def* measure_theory.filtration.const



## [2022-02-21 15:30:07](https://github.com/leanprover-community/mathlib/commit/9ed7179)
refactor(*): move normed field lemmas into root namespace ([#12163](https://github.com/leanprover-community/mathlib/pull/12163))
This takes the normed field lemmas given in `analysis.normed_space.basic` and moves them from the `normed_field` namespace into the root namespace.
This PR moves these lemmas and definitions: `norm_mul`, `nnnorm_mul`, `norm_hom`, `nnnorm_hom`, `norm_pow`, `nnnorm_pow`, `norm_prod`, `nnnorm_prod`, `norm_div`, `nnnorm_div`, `norm_inv`, `nnnorm_inv`, `norm_zpow`, `nnnorm_zpow`.
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/asymptotics/specific_asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/cauchy_integral.lean


Modified src/analysis/complex/conformal.lean


Modified src/analysis/normed_space/add_torsor.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnnorm_div
- \+ *def* nnnorm_hom
- \+ *lemma* nnnorm_inv
- \+ *lemma* nnnorm_mul
- \+ *lemma* nnnorm_pow
- \+ *lemma* nnnorm_prod
- \+ *lemma* nnnorm_zpow
- \+ *lemma* norm_div
- \+ *def* norm_hom
- \+ *lemma* norm_inv
- \+ *lemma* norm_mul
- \+ *lemma* norm_pow
- \+ *lemma* norm_prod
- \+ *lemma* norm_zpow
- \- *lemma* normed_field.nnnorm_div
- \- *def* normed_field.nnnorm_hom
- \- *lemma* normed_field.nnnorm_inv
- \- *lemma* normed_field.nnnorm_mul
- \- *lemma* normed_field.nnnorm_pow
- \- *lemma* normed_field.nnnorm_prod
- \- *lemma* normed_field.nnnorm_zpow
- \- *lemma* normed_field.norm_div
- \- *def* normed_field.norm_hom
- \- *lemma* normed_field.norm_inv
- \- *lemma* normed_field.norm_mul
- \- *lemma* normed_field.norm_pow
- \- *lemma* normed_field.norm_prod
- \- *lemma* normed_field.norm_zpow

Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/enorm.lean


Modified src/analysis/normed_space/extend.lean


Modified src/analysis/normed_space/is_R_or_C.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/ordered.lean


Modified src/analysis/normed_space/pointwise.lean


Modified src/analysis/normed_space/spectrum.lean


Modified src/analysis/normed_space/star/basic.lean


Modified src/analysis/special_functions/exp.lean


Modified src/analysis/special_functions/exp_deriv.lean


Modified src/analysis/special_functions/trigonometric/complex_deriv.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/number_theory/padics/hensel.lean


Modified src/number_theory/padics/padic_numbers.lean


Modified src/topology/metric_space/cau_seq_filter.lean




## [2022-02-21 15:30:06](https://github.com/leanprover-community/mathlib/commit/95d22b5)
feat(geometry/euclidean/oriented_angle): oriented angles and rotations ([#12106](https://github.com/leanprover-community/mathlib/pull/12106))
Define oriented angles and rotations in a real inner product space,
with respect to a choice of orthonormal basis indexed by `fin 2`, and
prove various lemmas about them, including that the definition depends
only on the orientation associated with the basis, and geometrical
results such as pons asinorum, "angle at center of a circle equals
twice angle at circumference" and "angles in same segment are equal" /
"opposite angles of a cyclic quadrilateral add to π" (these last two
being the same result for oriented angles mod π).
#### Estimated changes
Added src/geometry/euclidean/oriented_angle.lean
- \+ *def* orthonormal.conj_lie
- \+ *lemma* orthonormal.conj_lie_symm
- \+ *lemma* orthonormal.det_conj_lie
- \+ *lemma* orthonormal.det_rotation
- \+ *lemma* orthonormal.eq_iff_norm_eq_and_oangle_eq_zero
- \+ *lemma* orthonormal.eq_iff_norm_eq_of_oangle_eq_zero
- \+ *lemma* orthonormal.eq_iff_oangle_eq_zero_of_norm_eq
- \+ *lemma* orthonormal.eq_rotation_self_iff
- \+ *lemma* orthonormal.eq_rotation_self_iff_angle_eq_zero
- \+ *lemma* orthonormal.exists_linear_isometry_equiv_eq
- \+ *lemma* orthonormal.exists_linear_isometry_equiv_eq_of_det_neg
- \+ *lemma* orthonormal.exists_linear_isometry_equiv_eq_of_det_pos
- \+ *lemma* orthonormal.exists_linear_isometry_equiv_map_eq_of_orientation_eq
- \+ *lemma* orthonormal.exists_linear_isometry_equiv_map_eq_of_orientation_eq_neg
- \+ *lemma* orthonormal.linear_equiv_det_conj_lie
- \+ *lemma* orthonormal.linear_equiv_det_rotation
- \+ *def* orthonormal.oangle
- \+ *lemma* orthonormal.oangle_add
- \+ *lemma* orthonormal.oangle_add_cyc3
- \+ *lemma* orthonormal.oangle_add_cyc3_neg_left
- \+ *lemma* orthonormal.oangle_add_cyc3_neg_right
- \+ *lemma* orthonormal.oangle_add_oangle_rev
- \+ *lemma* orthonormal.oangle_add_oangle_rev_neg_left
- \+ *lemma* orthonormal.oangle_add_oangle_rev_neg_right
- \+ *lemma* orthonormal.oangle_add_swap
- \+ *lemma* orthonormal.oangle_conj_lie
- \+ *lemma* orthonormal.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero
- \+ *lemma* orthonormal.oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero
- \+ *lemma* orthonormal.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
- \+ *lemma* orthonormal.oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero
- \+ *lemma* orthonormal.oangle_eq_neg_of_orientation_eq_neg
- \+ *lemma* orthonormal.oangle_eq_of_orientation_eq
- \+ *lemma* orthonormal.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq
- \+ *lemma* orthonormal.oangle_eq_two_zsmul_oangle_sub_of_norm_eq
- \+ *lemma* orthonormal.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real
- \+ *lemma* orthonormal.oangle_map
- \+ *lemma* orthonormal.oangle_neg_left
- \+ *lemma* orthonormal.oangle_neg_left_eq_neg_right
- \+ *lemma* orthonormal.oangle_neg_neg
- \+ *lemma* orthonormal.oangle_neg_right
- \+ *lemma* orthonormal.oangle_neg_self_left
- \+ *lemma* orthonormal.oangle_neg_self_right
- \+ *lemma* orthonormal.oangle_rev
- \+ *lemma* orthonormal.oangle_rotation
- \+ *lemma* orthonormal.oangle_rotation_left
- \+ *lemma* orthonormal.oangle_rotation_oangle_left
- \+ *lemma* orthonormal.oangle_rotation_oangle_right
- \+ *lemma* orthonormal.oangle_rotation_right
- \+ *lemma* orthonormal.oangle_rotation_self_left
- \+ *lemma* orthonormal.oangle_rotation_self_right
- \+ *lemma* orthonormal.oangle_self
- \+ *lemma* orthonormal.oangle_smul_left_of_neg
- \+ *lemma* orthonormal.oangle_smul_left_of_pos
- \+ *lemma* orthonormal.oangle_smul_left_self_of_nonneg
- \+ *lemma* orthonormal.oangle_smul_right_of_neg
- \+ *lemma* orthonormal.oangle_smul_right_of_pos
- \+ *lemma* orthonormal.oangle_smul_right_self_of_nonneg
- \+ *lemma* orthonormal.oangle_smul_smul_self_of_nonneg
- \+ *lemma* orthonormal.oangle_sub_eq_oangle_sub_rev_of_norm_eq
- \+ *lemma* orthonormal.oangle_sub_left
- \+ *lemma* orthonormal.oangle_sub_right
- \+ *lemma* orthonormal.oangle_zero_left
- \+ *lemma* orthonormal.oangle_zero_right
- \+ *def* orthonormal.rotation
- \+ *lemma* orthonormal.rotation_eq_of_orientation_eq
- \+ *lemma* orthonormal.rotation_eq_rotation_neg_of_orientation_eq_neg
- \+ *lemma* orthonormal.rotation_eq_self_iff
- \+ *lemma* orthonormal.rotation_eq_self_iff_angle_eq_zero
- \+ *lemma* orthonormal.rotation_oangle_eq_iff_norm_eq
- \+ *lemma* orthonormal.rotation_pi
- \+ *lemma* orthonormal.rotation_symm
- \+ *lemma* orthonormal.rotation_trans
- \+ *lemma* orthonormal.rotation_zero
- \+ *lemma* orthonormal.two_zsmul_oangle_neg_left
- \+ *lemma* orthonormal.two_zsmul_oangle_neg_right
- \+ *lemma* orthonormal.two_zsmul_oangle_neg_self_left
- \+ *lemma* orthonormal.two_zsmul_oangle_neg_self_right
- \+ *lemma* orthonormal.two_zsmul_oangle_smul_left_of_ne_zero
- \+ *lemma* orthonormal.two_zsmul_oangle_smul_left_self
- \+ *lemma* orthonormal.two_zsmul_oangle_smul_right_of_ne_zero
- \+ *lemma* orthonormal.two_zsmul_oangle_smul_right_self
- \+ *lemma* orthonormal.two_zsmul_oangle_smul_smul_self
- \+ *lemma* orthonormal.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq



## [2022-02-21 15:30:04](https://github.com/leanprover-community/mathlib/commit/6db1577)
feat(category_theory/preadditive): separators in preadditive categories ([#11884](https://github.com/leanprover-community/mathlib/pull/11884))
#### Estimated changes
Modified src/category_theory/generator.lean
- \+/\- *lemma* category_theory.is_codetecting_op_iff
- \+/\- *lemma* category_theory.is_codetector_def
- \+/\- *lemma* category_theory.is_codetector_iff_reflects_isomorphisms_yoneda_obj
- \+/\- *lemma* category_theory.is_coseparator_def
- \+/\- *lemma* category_theory.is_coseparator_iff_faithful_yoneda_obj
- \+/\- *lemma* category_theory.is_detecting_iff_is_separating
- \+/\- *lemma* category_theory.is_detecting_op_iff
- \+/\- *lemma* category_theory.is_detecting_unop_iff
- \+/\- *lemma* category_theory.is_detector_def
- \+/\- *lemma* category_theory.is_detector_iff_reflects_isomorphisms_coyoneda_obj
- \+/\- *lemma* category_theory.is_separating_op_iff
- \+/\- *lemma* category_theory.is_separator_def
- \+/\- *lemma* category_theory.is_separator_iff_faithful_coyoneda_obj

Added src/category_theory/preadditive/generator.lean
- \+ *lemma* category_theory.is_coseparator_iff_faithful_preadditive_yoneda
- \+ *lemma* category_theory.is_coseparator_iff_faithful_preadditive_yoneda_obj
- \+ *lemma* category_theory.is_separator_iff_faithful_preadditive_coyoneda
- \+ *lemma* category_theory.is_separator_iff_faithful_preadditive_coyoneda_obj
- \+ *lemma* category_theory.preadditive.is_coseparating_iff
- \+ *lemma* category_theory.preadditive.is_coseparator_iff
- \+ *lemma* category_theory.preadditive.is_separating_iff
- \+ *lemma* category_theory.preadditive.is_separator_iff



## [2022-02-21 13:33:45](https://github.com/leanprover-community/mathlib/commit/3ad7395)
chore(topology/algebra/infinite_sum): reference Cauchy criterion in docs ([#12172](https://github.com/leanprover-community/mathlib/pull/12172))
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean




## [2022-02-21 13:33:44](https://github.com/leanprover-community/mathlib/commit/634dfc8)
feat(order/*): Missing order lifting instances ([#12154](https://github.com/leanprover-community/mathlib/pull/12154))
Add a few missing pullbacks of order instances.
#### Estimated changes
Modified src/order/boolean_algebra.lean


Modified src/order/complete_boolean_algebra.lean
- \+ *lemma* binfi_sup_eq
- \- *theorem* binfi_sup_eq
- \+ *lemma* sup_binfi_eq
- \- *theorem* sup_binfi_eq

Modified src/order/complete_lattice.lean
- \+ *def* bounded_order.lift
- \+ *def* order_bot.lift
- \+ *def* order_top.lift



## [2022-02-21 13:33:43](https://github.com/leanprover-community/mathlib/commit/2f33463)
feat(group_theory/free_product): is_free_group_free_product_of_is_free_group ([#12125](https://github.com/leanprover-community/mathlib/pull/12125))
#### Estimated changes
Modified src/group_theory/free_product.lean




## [2022-02-21 11:38:07](https://github.com/leanprover-community/mathlib/commit/7c6678a)
doc(topology/dense_embedding): fix markdown ([#12180](https://github.com/leanprover-community/mathlib/pull/12180))
Right now it just renders as "γ -f→ α g↓ ↓e δ -h→ β"
#### Estimated changes
Modified src/topology/dense_embedding.lean




## [2022-02-21 11:38:06](https://github.com/leanprover-community/mathlib/commit/f66a5dd)
chore(data/set/basic): add a few lemmas and a `@[simp]` attribute ([#12176](https://github.com/leanprover-community/mathlib/pull/12176))
* rename `set.exists_eq_singleton_iff_nonempty_unique_mem` to `set.exists_eq_singleton_iff_nonempty_subsingleton`, use `set.subsingleton` in the statement;
* add `@[simp]` to `set.subset_compl_singleton_iff`;
* add `set.diff_diff_right_self`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.diff_diff_right_self
- \+ *lemma* set.exists_eq_singleton_iff_nonempty_subsingleton
- \- *lemma* set.exists_eq_singleton_iff_nonempty_unique_mem
- \+/\- *lemma* set.subset_compl_singleton_iff

Modified src/group_theory/complement.lean


Modified src/topology/separation.lean


Modified src/topology/subset_properties.lean




## [2022-02-21 11:38:05](https://github.com/leanprover-community/mathlib/commit/0eb5e2d)
feat(topology/algebra): if a subobject is commutative, then so is its topological closure ([#12170](https://github.com/leanprover-community/mathlib/pull/12170))
We prove that if a submonoid (or subgroup, subsemiring, subring, subalgebra, and the additive versions where applicable) is commutative, then so is its topological closure.
#### Estimated changes
Modified src/topology/algebra/algebra.lean
- \+ *def* subalgebra.comm_ring_topological_closure
- \+ *def* subalgebra.comm_semiring_topological_closure

Modified src/topology/algebra/group.lean
- \+ *def* subgroup.comm_group_topological_closure

Modified src/topology/algebra/monoid.lean
- \+ *def* submonoid.comm_monoid_topological_closure

Modified src/topology/algebra/ring.lean
- \+ *def* subring.comm_ring_topological_closure
- \+ *def* subsemiring.comm_semiring_topological_closure



## [2022-02-21 11:38:04](https://github.com/leanprover-community/mathlib/commit/56dbb60)
feat(category_theory/opposites): nat_trans.remove_unop ([#12147](https://github.com/leanprover-community/mathlib/pull/12147))
#### Estimated changes
Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.nat_trans.remove_left_op_id
- \+ *lemma* category_theory.nat_trans.remove_right_op_id
- \+ *lemma* category_theory.nat_trans.remove_unop_id



## [2022-02-21 11:38:02](https://github.com/leanprover-community/mathlib/commit/b3b5e35)
chore(data/nat/prime): slightly golf proof of mem_factors ([#12143](https://github.com/leanprover-community/mathlib/pull/12143))
#### Estimated changes
Modified src/data/nat/prime.lean




## [2022-02-21 11:38:01](https://github.com/leanprover-community/mathlib/commit/afcc7e7)
feat(data/nat/prime): move nat.prime_iff_prime_int; add int.prime_two/three ([#12133](https://github.com/leanprover-community/mathlib/pull/12133))
I found it useful to have these results with somewhat lighter imports.
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* int.prime_three
- \+ *lemma* int.prime_two
- \+ *lemma* nat.prime_iff_prime_int

Modified src/ring_theory/int/basic.lean
- \- *lemma* nat.prime_iff_prime_int



## [2022-02-21 11:38:00](https://github.com/leanprover-community/mathlib/commit/37019db)
feat(topology/algebra/{group,monoid}): nat and int scalar multiplication is continuous ([#12124](https://github.com/leanprover-community/mathlib/pull/12124))
These instances allow a diamond to appear in the scalar action on `continuous_affine_map`s, which we fix at the same time.
#### Estimated changes
Modified src/topology/algebra/continuous_affine_map.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* continuous_map.pow_comp



## [2022-02-21 11:37:58](https://github.com/leanprover-community/mathlib/commit/72252b3)
feat(analysis/inner_product_space/projection): norm_sq_eq_sum_norm_sq… ([#12096](https://github.com/leanprover-community/mathlib/pull/12096))
…_projection
The Pythagorean theorem for an orthogonal projection onto a submodule S.
I am sure that there are some style changes that could/should be made!
#### Estimated changes
Modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* norm_sq_eq_add_norm_sq_projection



## [2022-02-21 11:37:57](https://github.com/leanprover-community/mathlib/commit/271c323)
feat(order/filter): prod_assoc ([#12002](https://github.com/leanprover-community/mathlib/pull/12002))
map (prod_assoc α β γ) ((f ×ᶠ g) ×ᶠ h) = f ×ᶠ (g ×ᶠ h)
with two tiny supporting lemmas
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.comp_equiv
- \+ *lemma* filter.has_basis.comp_of_surjective
- \+ *lemma* filter.prod_assoc

Modified src/order/filter/basic.lean
- \+ *lemma* filter.comap_equiv_symm
- \+ *lemma* filter.map_equiv_symm



## [2022-02-21 11:37:56](https://github.com/leanprover-community/mathlib/commit/d8d2f54)
feat(group_theory/nilpotent): n-ary products of nilpotent group ([#11829](https://github.com/leanprover-community/mathlib/pull/11829))
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* is_nilpotent_pi_of_bounded_class
- \+ *lemma* lower_central_series_pi_le
- \+ *lemma* lower_central_series_pi_of_fintype
- \+ *lemma* nilpotency_class_pi



## [2022-02-21 10:14:55](https://github.com/leanprover-community/mathlib/commit/e966efc)
chore(topology/constructions): golf a proof ([#12174](https://github.com/leanprover-community/mathlib/pull/12174))
#### Estimated changes
Modified src/topology/constructions.lean




## [2022-02-21 10:14:54](https://github.com/leanprover-community/mathlib/commit/d0fa7a8)
chore(category_theory/limits): make fin_category_opposite an instance ([#12153](https://github.com/leanprover-community/mathlib/pull/12153))
#### Estimated changes
Modified src/category_theory/fin_category.lean
- \- *def* category_theory.fin_category_opposite

Modified src/category_theory/limits/opposites.lean




## [2022-02-21 09:47:15](https://github.com/leanprover-community/mathlib/commit/b04851f)
chore(tactic): fix tactic doc tags ([#12131](https://github.com/leanprover-community/mathlib/pull/12131))
#### Estimated changes
Modified src/tactic/linear_combination.lean


Modified src/tactic/rewrite_search/frontend.lean




## [2022-02-21 08:48:32](https://github.com/leanprover-community/mathlib/commit/8b93d3a)
feat(measure_theory/function/lp_space): generalize some `integrable` lemmas to `mem_ℒp` ([#11231](https://github.com/leanprover-community/mathlib/pull/11231))
I would like to define integrable as `mem_ℒp` for `p = 1` and remove the `has_finite_integral` prop. But first we need to generalize everything we have about `integrable` to `mem_ℒp`. This is one step towards that goal.
#### Estimated changes
Modified src/measure_theory/function/ess_sup.lean
- \+ *lemma* ess_sup_comp_le_ess_sup_map_measure
- \+ *lemma* ess_sup_map_measure
- \+ *lemma* ess_sup_map_measure_of_measurable
- \+ *lemma* measurable_embedding.ess_sup_map_measure

Modified src/measure_theory/function/l1_space.lean


Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* measurable_embedding.mem_ℒp_map_measure_iff
- \+ *lemma* measurable_embedding.snorm_ess_sup_map_measure
- \+ *lemma* measurable_embedding.snorm_map_measure
- \+ *lemma* measurable_equiv.mem_ℒp_map_measure_iff
- \+ *lemma* measure_theory.mem_ℒp.left_of_add_measure
- \+ *lemma* measure_theory.mem_ℒp.right_of_add_measure
- \+ *lemma* measure_theory.mem_ℒp.smul_measure
- \+ *lemma* measure_theory.mem_ℒp_map_measure_iff
- \+ *lemma* measure_theory.snorm_ess_sup_map_measure
- \+ *lemma* measure_theory.snorm_le_add_measure_left
- \+ *lemma* measure_theory.snorm_le_add_measure_right
- \+ *lemma* measure_theory.snorm_map_measure
- \+ *lemma* measure_theory.snorm_one_add_measure



## [2022-02-21 08:00:52](https://github.com/leanprover-community/mathlib/commit/e60e1f2)
feat(data/real/pointwise): mul distributes over `infi` and `supr` ([#12105](https://github.com/leanprover-community/mathlib/pull/12105))
#### Estimated changes
Modified src/data/real/pointwise.lean
- \+ *lemma* real.infi_mul_of_nonneg
- \+ *lemma* real.infi_mul_of_nonpos
- \+ *lemma* real.mul_infi_of_nonneg
- \+ *lemma* real.mul_infi_of_nonpos
- \+ *lemma* real.mul_supr_of_nonneg
- \+ *lemma* real.mul_supr_of_nonpos
- \+ *lemma* real.smul_infi_of_nonneg
- \+ *lemma* real.smul_infi_of_nonpos
- \+ *lemma* real.smul_supr_of_nonneg
- \+ *lemma* real.smul_supr_of_nonpos
- \+ *lemma* real.supr_mul_of_nonneg
- \+ *lemma* real.supr_mul_of_nonpos



## [2022-02-21 00:51:52](https://github.com/leanprover-community/mathlib/commit/6298a43)
feat(analysis/seminorm): smul_sup ([#12103](https://github.com/leanprover-community/mathlib/pull/12103))
The `have : real.smul_max` local proof doesn't feel very general, so I've left it as a `have` rather than promoting it to a lemma.
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* seminorm.smul_sup
- \+ *lemma* seminorm.sup_apply



## [2022-02-21 00:51:51](https://github.com/leanprover-community/mathlib/commit/6ecd7ab)
feat(topology/continuous_function/bounded): generalize scalar action ([#12098](https://github.com/leanprover-community/mathlib/pull/12098))
This also makes the scalar action computable
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean




## [2022-02-20 23:53:46](https://github.com/leanprover-community/mathlib/commit/6ae1b70)
feat(topology/uniform_space/cauchy): add `cauchy_seq.comp_injective` ([#11986](https://github.com/leanprover-community/mathlib/pull/11986))
API changes:
- add `filter.at_top_le_cofinite`;
- add `function.injective.nat_tendsto_at_top`;
- add `cauchy_seq.comp_injective`, `function.bijective.cauchy_seq_comp_iff`.
#### Estimated changes
Modified src/order/filter/cofinite.lean
- \+ *lemma* at_top_le_cofinite
- \+ *lemma* function.injective.nat_tendsto_at_top
- \+/\- *lemma* function.injective.tendsto_cofinite

Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_seq.comp_injective
- \+ *lemma* function.bijective.cauchy_seq_comp_iff



## [2022-02-20 22:01:51](https://github.com/leanprover-community/mathlib/commit/7e1ef9f)
feat(ring_theory/witt_vector): assorted facts about Witt vectors over char p rings ([#12093](https://github.com/leanprover-community/mathlib/pull/12093))
#### Estimated changes
Modified src/ring_theory/witt_vector/frobenius.lean
- \+ *lemma* witt_vector.frobenius_bijective

Modified src/ring_theory/witt_vector/identities.lean
- \+ *lemma* witt_vector.fraction_ring.p_nonzero
- \+ *lemma* witt_vector.p_nonzero



## [2022-02-20 14:25:15](https://github.com/leanprover-community/mathlib/commit/334fb89)
feat(algebra/order/ring): add three_ne_zero and four_ne_zero ([#12142](https://github.com/leanprover-community/mathlib/pull/12142))
#### Estimated changes
Modified src/algebra/order/ring.lean
- \+ *lemma* four_ne_zero
- \+ *lemma* three_ne_zero



## [2022-02-20 09:43:13](https://github.com/leanprover-community/mathlib/commit/6c6e142)
chore(data/nat/factorization): Reorder lemmas and some minor golfing ([#12144](https://github.com/leanprover-community/mathlib/pull/12144))
Some minor housework on this file, reordering and regrouping lemmas, adding and editing a few docstrings and section headers, and golfing a few proofs.
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+/\- *lemma* nat.pos_of_mem_factorization
- \+/\- *lemma* nat.prime_of_mem_factorization
- \- *def* nat.rec_on_pos_prime_coprime
- \+ *def* nat.rec_on_pos_prime_pos_coprime



## [2022-02-20 01:22:26](https://github.com/leanprover-community/mathlib/commit/55c9cff)
chore(data/nat/prime): slightly weaken assumption in nat.exists_prime_and_dvd ([#12156](https://github.com/leanprover-community/mathlib/pull/12156))
It is vacuously true for zero, as everything divides zero.
#### Estimated changes
Modified src/algebra/squarefree.lean


Modified src/data/nat/prime.lean
- \+/\- *theorem* nat.exists_prime_and_dvd

Modified src/data/pnat/prime.lean
- \+/\- *lemma* pnat.exists_prime_and_dvd

Modified src/ring_theory/int/basic.lean
- \+/\- *lemma* int.exists_prime_and_dvd



## [2022-02-20 00:00:55](https://github.com/leanprover-community/mathlib/commit/fa603fe)
feat(order/category/FinPartialOrder): The category of finite partial orders ([#11997](https://github.com/leanprover-community/mathlib/pull/11997))
Define `FinPartialOrder`, the category of finite partial orders with monotone functions.
#### Estimated changes
Added src/order/category/FinPartialOrder.lean
- \+ *def* FinPartialOrder.dual
- \+ *def* FinPartialOrder.dual_equiv
- \+ *def* FinPartialOrder.iso.mk
- \+ *def* FinPartialOrder.of
- \+ *structure* FinPartialOrder
- \+ *lemma* FinPartialOrder_dual_comp_forget_to_PartialOrder



## [2022-02-19 22:26:11](https://github.com/leanprover-community/mathlib/commit/5611533)
feat(analysis/normed_space/star/complex): real and imaginary part of an element of a star module ([#11811](https://github.com/leanprover-community/mathlib/pull/11811))
We introduce the real and imaginary parts of an element of a star module, and show that elements of the type can be decomposed into these two parts in the obvious way.
#### Estimated changes
Modified src/algebra/invertible.lean
- \+ *lemma* inv_of_two_add_inv_of_two

Modified src/algebra/module/basic.lean
- \+ *lemma* inv_of_two_smul_add_inv_of_two_smul

Modified src/algebra/star/module.lean
- \+ *def* self_adjoint.submodule
- \+ *def* self_adjoint_part
- \+ *def* skew_adjoint.submodule
- \+ *def* skew_adjoint_part
- \+ *def* star_module.decompose_prod_adjoint
- \+ *lemma* star_module.self_adjoint_part_add_skew_adjoint_part

Modified src/analysis/normed_space/exponential.lean


Added src/analysis/normed_space/star/complex.lean
- \+ *def* star_module.mul_neg_I_lin
- \+ *lemma* star_module.re_add_im

Modified src/analysis/special_functions/exponential.lean


Modified src/data/complex/basic.lean
- \+ *lemma* complex.conj_inv
- \+/\- *lemma* complex.star_def

Modified src/data/complex/is_R_or_C.lean
- \- *lemma* is_R_or_C.char_zero_R_or_C
- \+ *lemma* is_R_or_C.conj_inv
- \+ *lemma* is_R_or_C.star_def

Modified src/data/complex/module.lean




## [2022-02-19 21:14:08](https://github.com/leanprover-community/mathlib/commit/3777543)
feat(category_theory/isomorphism): two lemmas is_iso.of_iso_comp_left/right on isomorphisms ([#12056](https://github.com/leanprover-community/mathlib/pull/12056))
#### Estimated changes
Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.is_iso.of_is_iso_comp_left
- \+ *lemma* category_theory.is_iso.of_is_iso_comp_right
- \+ *lemma* category_theory.is_iso.of_is_iso_fac_left
- \+ *lemma* category_theory.is_iso.of_is_iso_fac_right



## [2022-02-19 19:27:37](https://github.com/leanprover-community/mathlib/commit/bc63071)
feat(algebra/is_prime_pow): dot notation for nat.prime ([#12145](https://github.com/leanprover-community/mathlib/pull/12145))
#### Estimated changes
Modified src/algebra/is_prime_pow.lean
- \+ *lemma* nat.prime.is_prime_pow



## [2022-02-19 19:27:36](https://github.com/leanprover-community/mathlib/commit/628e8fb)
doc(group_theory/coset): Mention "Lagrange's theorem" ([#12137](https://github.com/leanprover-community/mathlib/pull/12137))
Suggested here: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.E2.9C.94.20Lagrange's.20Theorem.20.28Group.20theory.29/near/272469211
#### Estimated changes
Modified src/group_theory/coset.lean




## [2022-02-19 18:23:35](https://github.com/leanprover-community/mathlib/commit/e88badb)
feat(analysis/inner_product_space/pi_L2): Orthonormal basis ([#12060](https://github.com/leanprover-community/mathlib/pull/12060))
Added the structure orthonormal_basis and basic associated API
Renamed the previous definition orthonormal_basis in analysis/inner_product_space/projection to std_orthonormal_basis
#### Estimated changes
Modified src/analysis/inner_product_space/orientation.lean


Modified src/analysis/inner_product_space/pi_L2.lean
- \- *lemma* basis.coe_isometry_euclidean_of_orthonormal
- \- *lemma* basis.coe_isometry_euclidean_of_orthonormal_symm
- \+ *lemma* basis.coe_to_orthonormal_basis
- \+ *lemma* basis.coe_to_orthonormal_basis_repr
- \+ *lemma* basis.coe_to_orthonormal_basis_repr_symm
- \- *def* basis.isometry_euclidean_of_orthonormal
- \+ *lemma* basis.to_basis_to_orthonormal_basis
- \+ *def* basis.to_orthonormal_basis
- \+ *lemma* euclidean_space.inner_single_left
- \+ *lemma* euclidean_space.inner_single_right
- \+ *def* euclidean_space.single
- \+ *theorem* euclidean_space.single_apply
- \+ *structure* orthonormal_basis

Modified src/analysis/inner_product_space/projection.lean
- \- *lemma* coe_orthonormal_basis
- \+ *lemma* coe_std_orthonormal_basis
- \- *def* fin_orthonormal_basis
- \- *lemma* fin_orthonormal_basis_orthonormal
- \+ *def* fin_std_orthonormal_basis
- \+ *lemma* fin_std_orthonormal_basis_orthonormal
- \- *def* orthonormal_basis
- \- *lemma* orthonormal_basis_orthonormal
- \+ *def* std_orthonormal_basis
- \+ *lemma* std_orthonormal_basis_orthonormal

Modified src/analysis/inner_product_space/spectrum.lean


Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.of_equiv_fun_equiv_fun



## [2022-02-19 07:54:42](https://github.com/leanprover-community/mathlib/commit/518b5d2)
chore(topology/bases): golf a proof ([#12127](https://github.com/leanprover-community/mathlib/pull/12127))
Also add `function.injective_iff_pairwise_ne`.
#### Estimated changes
Modified src/data/set/pairwise.lean
- \+ *lemma* function.injective_iff_pairwise_ne

Modified src/topology/bases.lean


Modified src/topology/dense_embedding.lean
- \- *lemma* dense_inducing.preconnected_space



## [2022-02-18 21:46:45](https://github.com/leanprover-community/mathlib/commit/213e2ed)
feat(algebra/group/pi): add pi.nsmul_apply ([#12122](https://github.com/leanprover-community/mathlib/pull/12122))
via to_additive
#### Estimated changes
Modified src/algebra/group/pi.lean
- \+/\- *lemma* pi.pow_apply



## [2022-02-18 21:46:43](https://github.com/leanprover-community/mathlib/commit/b3d0944)
feat(tactic/swap_var): name juggling, a weaker wlog ([#12006](https://github.com/leanprover-community/mathlib/pull/12006))
#### Estimated changes
Added src/tactic/swap_var.lean


Added test/swap_var.lean




## [2022-02-18 19:52:47](https://github.com/leanprover-community/mathlib/commit/5f46dd0)
fix(category_theory/limits): improve inaccurate docstrings ([#12130](https://github.com/leanprover-community/mathlib/pull/12130))
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean




## [2022-02-18 19:52:46](https://github.com/leanprover-community/mathlib/commit/7b6c407)
feat(number_theory/divisors): add `prod_div_divisors` and `sum_div_divisors` ([#12087](https://github.com/leanprover-community/mathlib/pull/12087))
Adds lemma `prod_div_divisors : ∏ d in n.divisors, f (n/d) = n.divisors.prod f` and `sum_div_divisors`.
Also proves `image_div_divisors_eq_divisors : image (λ (x : ℕ), n / x) n.divisors = n.divisors`
and `div_eq_iff_eq_of_dvd_dvd : n / x = n / y ↔ x = y` (where `n ≠ 0` and `x ∣ n` and `y ∣ n`)
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.div_eq_iff_eq_of_dvd_dvd

Modified src/number_theory/divisors.lean
- \+ *lemma* nat.image_div_divisors_eq_divisors
- \+ *lemma* nat.prod_div_divisors



## [2022-02-18 19:52:44](https://github.com/leanprover-community/mathlib/commit/33179f7)
refactor(topology/metric_space/completion): change namespace ([#12077](https://github.com/leanprover-community/mathlib/pull/12077))
Move lemmas about metric on `uniform_space.completion` from `metric.completion` namespace to `uniform_space.completion`.
#### Estimated changes
Modified src/analysis/normed/group/completion.lean


Modified src/topology/metric_space/completion.lean
- \- *lemma* metric.completion.coe_isometry
- \+ *lemma* uniform_space.completion.coe_isometry

Modified src/topology/metric_space/gromov_hausdorff.lean




## [2022-02-18 19:52:43](https://github.com/leanprover-community/mathlib/commit/18c3e3f)
feat(data/nat/fib): add that `fib` is sum of `nat.choose` along antidiagonal ([#12063](https://github.com/leanprover-community/mathlib/pull/12063))
#### Estimated changes
Modified src/data/nat/fib.lean
- \+ *lemma* nat.fib_succ_eq_sum_choose



## [2022-02-18 19:21:11](https://github.com/leanprover-community/mathlib/commit/ffc2bdf)
refactor(group_theory/abelianization): Define `commutator` in terms of `general_commutator` ([#11949](https://github.com/leanprover-community/mathlib/pull/11949))
It seems reasonable to define `commutator` in terms of `general_commutator`.
#### Estimated changes
Modified src/group_theory/abelianization.lean
- \+ *lemma* commutator_def
- \+ *lemma* commutator_eq_closure
- \+ *lemma* commutator_eq_normal_closure

Modified src/group_theory/nilpotent.lean
- \+/\- *lemma* lower_central_series_one

Modified src/group_theory/solvable.lean
- \- *lemma* commutator_def'
- \- *lemma* general_commutator_eq_commutator



## [2022-02-18 18:09:38](https://github.com/leanprover-community/mathlib/commit/018c728)
refactor(ring_theory/fractional_ideal): rename lemmas for dot notation, add coe_pow ([#12080](https://github.com/leanprover-community/mathlib/pull/12080))
This replaces `fractional_ideal.fractional_mul` with `is_fractional.mul` and likewise for the other operations. The bundling was a distraction for the content of the lemmas anyway.
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.coe_pow
- \- *lemma* fractional_ideal.fractional_inf
- \- *lemma* fractional_ideal.fractional_map
- \- *lemma* fractional_ideal.fractional_mul
- \- *lemma* fractional_ideal.fractional_sup
- \+ *lemma* is_fractional.div_of_nonzero
- \+ *lemma* is_fractional.inf_right
- \+ *lemma* is_fractional.map
- \+ *lemma* is_fractional.mul
- \+ *lemma* is_fractional.pow
- \+ *lemma* is_fractional.sup



## [2022-02-18 18:09:37](https://github.com/leanprover-community/mathlib/commit/bcf8a6e)
feat(ring_theory/fractional_ideal): add coe_ideal lemmas ([#12073](https://github.com/leanprover-community/mathlib/pull/12073))
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.coe_ideal_finprod
- \+ *lemma* fractional_ideal.coe_ideal_pow



## [2022-02-18 16:58:17](https://github.com/leanprover-community/mathlib/commit/98643bc)
feat(algebra/big_operators/intervals): summation by parts ([#11814](https://github.com/leanprover-community/mathlib/pull/11814))
Add the "summation by parts" identity over intervals of natural numbers, as well as some helper lemmas.
#### Estimated changes
Modified src/algebra/big_operators/intervals.lean
- \+ *lemma* finset.prod_Ico_add'
- \+ *lemma* finset.prod_Ico_div_bot
- \+ *lemma* finset.prod_Ico_succ_div_top
- \+ *lemma* finset.prod_range_succ_div_prod
- \+ *lemma* finset.prod_range_succ_div_top
- \- *lemma* finset.sum_Ico_add
- \+ *theorem* finset.sum_Ico_by_parts
- \+ *lemma* finset.sum_range_by_parts



## [2022-02-18 15:07:45](https://github.com/leanprover-community/mathlib/commit/3ca16d0)
feat(data/equiv): define `ring_equiv_class` ([#11977](https://github.com/leanprover-community/mathlib/pull/11977))
This PR applies the morphism class pattern to `ring_equiv`, producing a new `ring_equiv_class` extending `mul_equiv_class` and `add_equiv_class`. It also provides a `ring_equiv_class` instance for `alg_equiv`s.
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \- *lemma* alg_equiv.bijective
- \+/\- *lemma* alg_equiv.ext
- \- *lemma* alg_equiv.ext_iff
- \- *lemma* alg_equiv.injective
- \- *lemma* alg_equiv.map_add
- \- *lemma* alg_equiv.map_mul
- \- *lemma* alg_equiv.map_neg
- \- *lemma* alg_equiv.map_one
- \- *lemma* alg_equiv.map_pow
- \- *lemma* alg_equiv.map_sub
- \- *lemma* alg_equiv.map_zero
- \- *lemma* alg_equiv.surjective

Modified src/algebra/ring/basic.lean
- \+ *lemma* ring_hom.coe_coe

Modified src/data/equiv/ring.lean
- \+/\- *lemma* ring_equiv.ext
- \- *lemma* ring_equiv.ext_iff
- \- *lemma* ring_equiv.map_add
- \- *lemma* ring_equiv.map_eq_one_iff
- \- *lemma* ring_equiv.map_eq_zero_iff
- \- *lemma* ring_equiv.map_mul
- \+/\- *lemma* ring_equiv.map_ne_one_iff
- \+/\- *lemma* ring_equiv.map_ne_zero_iff
- \- *lemma* ring_equiv.map_neg
- \- *lemma* ring_equiv.map_one
- \- *lemma* ring_equiv.map_pow
- \- *lemma* ring_equiv.map_sub
- \- *lemma* ring_equiv.map_zero

Modified src/data/mv_polynomial/equiv.lean


Modified src/ring_theory/algebraic_independent.lean


Modified src/ring_theory/finiteness.lean




## [2022-02-18 14:37:42](https://github.com/leanprover-community/mathlib/commit/223f149)
chore(algebra/star/self_adjoint): extract a lemma from `has_scalar` ([#12121](https://github.com/leanprover-community/mathlib/pull/12121))
#### Estimated changes
Modified src/algebra/star/self_adjoint.lean
- \+ *lemma* self_adjoint.smul_mem
- \+ *lemma* skew_adjoint.smul_mem



## [2022-02-18 13:41:21](https://github.com/leanprover-community/mathlib/commit/aed97e0)
doc(analysis/normed/group/basic): add docstring explaining the "insert" name ([#12100](https://github.com/leanprover-community/mathlib/pull/12100))
#### Estimated changes
Modified src/analysis/normed/group/basic.lean




## [2022-02-18 12:57:33](https://github.com/leanprover-community/mathlib/commit/3e6439c)
fix(category_theory/limits/shapes/images): make class a Prop ([#12119](https://github.com/leanprover-community/mathlib/pull/12119))
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean




## [2022-02-18 11:05:58](https://github.com/leanprover-community/mathlib/commit/33b4e73)
refactor(topology/algebra): reorder imports ([#12089](https://github.com/leanprover-community/mathlib/pull/12089))
* move `mul_opposite.topological_space` and `units.topological_space` to a new file;
* import `mul_action` in `monoid`, not vice versa.
With this order of imports, we can reuse results about `has_continuous_smul` in lemmas about topological monoids.
#### Estimated changes
Modified src/analysis/convex/strict.lean


Added src/topology/algebra/constructions.lean
- \+ *lemma* mul_opposite.continuous_op
- \+ *lemma* mul_opposite.continuous_unop
- \+ *def* mul_opposite.op_homeomorph
- \+ *lemma* units.continuous_coe
- \+ *lemma* units.continuous_embed_product

Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean
- \- *lemma* mul_opposite.continuous_op
- \- *lemma* mul_opposite.continuous_unop
- \- *lemma* units.continuous_coe
- \- *lemma* units.continuous_embed_product

Modified src/topology/algebra/mul_action.lean




## [2022-02-18 07:37:58](https://github.com/leanprover-community/mathlib/commit/77f264f)
feat(data/finset/basic): add lemma `filter_eq_empty_iff` ([#12104](https://github.com/leanprover-community/mathlib/pull/12104))
Add `filter_eq_empty_iff : (s.filter p = ∅) ↔ ∀ x ∈ s, ¬ p x`
We already have the right-to-left direction of this in `filter_false_of_mem`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.filter_eq_empty_iff



## [2022-02-18 05:49:20](https://github.com/leanprover-community/mathlib/commit/bb1b56c)
feat(algebra/indicator_function): smul lemmas for functions ([#12059](https://github.com/leanprover-community/mathlib/pull/12059))
And a few basic lemmas in `set/basic`.
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* set.indicator_const_smul
- \+ *lemma* set.indicator_const_smul_apply
- \+/\- *lemma* set.indicator_smul
- \+/\- *lemma* set.indicator_smul_apply

Modified src/analysis/box_integral/integrability.lean


Modified src/data/finsupp/basic.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.compl_range_inl
- \+ *lemma* set.compl_range_inr

Modified src/logic/nonempty.lean
- \+ *lemma* function.surjective.nonempty



## [2022-02-18 04:52:16](https://github.com/leanprover-community/mathlib/commit/17b3357)
feat(topology/algebra): generalize `has_continuous_smul` arguments to `has_continuous_const_smul` ([#11999](https://github.com/leanprover-community/mathlib/pull/11999))
This changes the majority of the downstream call-sites of the `const_smul` lemmas to only need the weaker typeclass.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/cauchy_integral.lean


Modified src/analysis/convex/strict.lean
- \+/\- *lemma* strict_convex.affinity
- \+/\- *lemma* strict_convex.smul

Modified src/analysis/convex/topology.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *def* continuous_linear_map.prodₗᵢ

Modified src/dynamics/minimal.lean
- \+/\- *lemma* is_compact.exists_finite_cover_smul
- \+/\- *lemma* is_minimal_iff_closed_smul_invariant

Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/function/ae_eq_fun.lean


Modified src/measure_theory/group/action.lean


Modified src/measure_theory/measure/complex.lean


Modified src/measure_theory/measure/vector_measure.lean
- \+/\- *lemma* measure_theory.vector_measure.absolutely_continuous.smul
- \+/\- *lemma* measure_theory.vector_measure.mutually_singular.smul_left
- \+/\- *lemma* measure_theory.vector_measure.mutually_singular.smul_right

Modified src/topology/algebra/affine.lean


Modified src/topology/algebra/const_mul_action.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module/basic.lean


Modified src/topology/algebra/module/multilinear.lean


Modified src/topology/algebra/module/weak_dual.lean


Modified src/topology/continuous_function/locally_constant.lean
- \+/\- *def* locally_constant.to_continuous_map_alg_hom
- \+/\- *def* locally_constant.to_continuous_map_linear_map



## [2022-02-18 02:05:51](https://github.com/leanprover-community/mathlib/commit/b757206)
feat(linear_algebra/finite_dimensional): finrank_range_of_inj ([#12067](https://github.com/leanprover-community/mathlib/pull/12067))
The dimensions of the domain and range of an injective linear map are
equal.
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *theorem* linear_equiv.finrank_eq
- \+/\- *lemma* linear_equiv.finrank_map_eq
- \+ *lemma* linear_map.finrank_range_of_inj



## [2022-02-18 00:52:54](https://github.com/leanprover-community/mathlib/commit/59a183a)
feat(data/finset/locally_finite): add Ico_subset_Ico_union_Ico ([#11710](https://github.com/leanprover-community/mathlib/pull/11710))
This lemma extends the result for `set`s to `finset`s.
#### Estimated changes
Modified src/data/finset/locally_finite.lean
- \+ *lemma* finset.Ico_subset_Ico_union_Ico



## [2022-02-17 22:59:24](https://github.com/leanprover-community/mathlib/commit/e93996c)
feat(topology/instances/discrete): instances for the discrete topology ([#11349](https://github.com/leanprover-community/mathlib/pull/11349))
Prove `first_countable_topology`, `second_countable_topology` and `order_topology` for the discrete topology under appropriate conditions like `encodable`, or being a linear order with `pred` and `succ`. These instances give in particular `second_countable_topology ℕ` and `order_topology ℕ`
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.is_countably_generated_pure

Modified src/order/succ_pred/basic.lean
- \+ *lemma* pred_order.Ici_eq_Ioi_pred'
- \+ *lemma* pred_order.Ici_eq_Ioi_pred
- \+ *lemma* pred_order.Iio_eq_Iic_pred'
- \+ *lemma* pred_order.Iio_eq_Iic_pred
- \+ *lemma* pred_order.le_pred_iff_of_not_is_min
- \+ *lemma* pred_order.pred_lt_iff_of_not_is_min
- \+ *lemma* pred_order.pred_lt_of_not_is_min
- \+ *lemma* succ_order.Iic_eq_Iio_succ'
- \+ *lemma* succ_order.Iic_eq_Iio_succ
- \+ *lemma* succ_order.Ioi_eq_Ici_succ'
- \+ *lemma* succ_order.Ioi_eq_Ici_succ
- \+ *lemma* succ_order.lt_succ_iff_of_not_is_max
- \+ *lemma* succ_order.lt_succ_of_not_is_max
- \+ *lemma* succ_order.succ_le_iff_of_not_is_max

Modified src/topology/bases.lean


Added src/topology/instances/discrete.lean


Modified src/topology/order.lean
- \+ *lemma* topological_space.is_open_generate_from_of_mem



## [2022-02-17 21:50:25](https://github.com/leanprover-community/mathlib/commit/6089f08)
feat(data/nat/totient): add Euler's product formula for totient function ([#11332](https://github.com/leanprover-community/mathlib/pull/11332))
Proving four versions of Euler's product formula for the totient function `φ`:
* `totient_eq_prod_factorization :  φ n = n.factorization.prod (λ p k, p ^ (k - 1) * (p - 1))`
* `totient_mul_prod_factors : φ n * ∏ p in n.factors.to_finset, p = n * ∏ p in n.factors.to_finset, (p - 1)`
* `totient_eq_div_factors_mul : φ n = n / (∏ p in n.factors.to_finset, p) * (∏ p in n.factors.to_finset, (p - 1))`
* `totient_eq_mul_prod_factors : (φ n : ℚ) = n * ∏ p in n.factors.to_finset, (1 - p⁻¹)`
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.prod_factorization_eq_prod_factors

Modified src/data/nat/prime.lean
- \+ *lemma* nat.pos_of_mem_factors

Modified src/data/nat/totient.lean
- \+ *theorem* nat.totient_eq_div_factors_mul
- \+ *theorem* nat.totient_eq_mul_prod_factors
- \+ *theorem* nat.totient_eq_prod_factorization
- \+ *theorem* nat.totient_mul_prod_factors



## [2022-02-17 21:06:46](https://github.com/leanprover-community/mathlib/commit/19534b2)
feat(analysis/inner_product_space/basic) : `inner_map_self_eq_zero` ([#12065](https://github.com/leanprover-community/mathlib/pull/12065))
The main result here is:  If ⟪T x, x⟫_C = 0 for all x, then T = 0.
The proof uses a polarization identity.  Note that this is false
with R in place of C.  I am confident that my use of ring_nf is
not optimal, but I hope to learn from the cleanup process!
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* inner_map_polarization
- \+ *lemma* inner_map_self_eq_zero



## [2022-02-17 22:00:06+01:00](https://github.com/leanprover-community/mathlib/commit/8b6901b)
Revert "feat(category_theory/limits): is_bilimit"
This reverts commit 8edfa75d79ad70c88dbae01ab6166dd8b1fd2ba0.
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \- *structure* category_theory.limits.bicone.is_bilimit
- \- *def* category_theory.limits.bicone.of_colimit_cocone
- \- *def* category_theory.limits.bicone.of_limit_cone
- \- *def* category_theory.limits.bicone.to_binary_bicone_is_bilimit
- \+/\- *def* category_theory.limits.bicone.to_binary_bicone_is_colimit
- \+/\- *def* category_theory.limits.bicone.to_binary_bicone_is_limit
- \- *lemma* category_theory.limits.bicone.ι_of_is_limit
- \- *lemma* category_theory.limits.bicone.π_of_is_colimit
- \+/\- *lemma* category_theory.limits.bicone_ι_π_ne
- \- *structure* category_theory.limits.binary_bicone.is_bilimit
- \- *def* category_theory.limits.binary_bicone.to_bicone
- \- *def* category_theory.limits.binary_bicone.to_bicone_is_bilimit
- \- *def* category_theory.limits.binary_bicone.to_bicone_is_colimit
- \- *def* category_theory.limits.binary_bicone.to_bicone_is_limit
- \- *def* category_theory.limits.binary_biproduct.is_bilimit
- \- *def* category_theory.limits.biproduct.is_bilimit



## [2022-02-17 21:56:42+01:00](https://github.com/leanprover-community/mathlib/commit/8edfa75)
feat(category_theory/limits): is_bilimit
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *structure* category_theory.limits.bicone.is_bilimit
- \+ *def* category_theory.limits.bicone.of_colimit_cocone
- \+ *def* category_theory.limits.bicone.of_limit_cone
- \+ *def* category_theory.limits.bicone.to_binary_bicone_is_bilimit
- \+/\- *def* category_theory.limits.bicone.to_binary_bicone_is_colimit
- \+/\- *def* category_theory.limits.bicone.to_binary_bicone_is_limit
- \+ *lemma* category_theory.limits.bicone.ι_of_is_limit
- \+ *lemma* category_theory.limits.bicone.π_of_is_colimit
- \+/\- *lemma* category_theory.limits.bicone_ι_π_ne
- \+ *structure* category_theory.limits.binary_bicone.is_bilimit
- \+ *def* category_theory.limits.binary_bicone.to_bicone
- \+ *def* category_theory.limits.binary_bicone.to_bicone_is_bilimit
- \+ *def* category_theory.limits.binary_bicone.to_bicone_is_colimit
- \+ *def* category_theory.limits.binary_bicone.to_bicone_is_limit
- \+ *def* category_theory.limits.binary_biproduct.is_bilimit
- \+ *def* category_theory.limits.biproduct.is_bilimit



## [2022-02-17 19:35:15](https://github.com/leanprover-community/mathlib/commit/aacc36c)
feat(group_theory/commensurable): Definition and lemmas about commensurability. ([#9545](https://github.com/leanprover-community/mathlib/pull/9545))
This defines commensurability for subgroups, proves this defines a transitive relation and then defines the commensurator subgroup. In doing so it also needs some lemmas about indices of subgroups and the definition of the conjugate of a subgroup by an element of the parent group.
#### Estimated changes
Added src/group_theory/commensurable.lean
- \+ *lemma* commensurable.comm
- \+ *lemma* commensurable.commensurable_conj
- \+ *lemma* commensurable.commensurable_inv
- \+ *def* commensurable.commensurator'
- \+ *lemma* commensurable.commensurator'_mem_iff
- \+ *def* commensurable.commensurator
- \+ *lemma* commensurable.commensurator_mem_iff
- \+ *lemma* commensurable.eq
- \+ *lemma* commensurable.equivalence
- \+ *def* commensurable.quot_conj_equiv
- \+ *lemma* commensurable.symm
- \+ *lemma* commensurable.trans
- \+ *def* commensurable



## [2022-02-17 18:46:15](https://github.com/leanprover-community/mathlib/commit/8575f59)
feat(category_theory/limits): preservation of zero morphisms ([#12068](https://github.com/leanprover-community/mathlib/pull/12068))
#### Estimated changes
Modified src/category_theory/differential_object.lean


Added src/category_theory/limits/preserves/shapes/zero.lean
- \+ *def* category_theory.functor.map_zero_object
- \+ *lemma* category_theory.functor.preserves_zero_morphisms_of_map_zero_object

Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* category_theory.limits.initial_iso_is_initial
- \+ *def* category_theory.limits.terminal_iso_is_terminal

Modified src/category_theory/limits/shapes/zero.lean
- \- *lemma* category_theory.limits.equivalence_preserves_zero_morphisms
- \+ *def* category_theory.limits.has_zero_object.zero_iso_initial
- \+ *lemma* category_theory.limits.has_zero_object.zero_iso_initial_hom
- \+ *lemma* category_theory.limits.has_zero_object.zero_iso_initial_inv
- \+ *def* category_theory.limits.has_zero_object.zero_iso_is_initial
- \+ *lemma* category_theory.limits.has_zero_object.zero_iso_is_initial_hom
- \+ *lemma* category_theory.limits.has_zero_object.zero_iso_is_initial_inv
- \+ *def* category_theory.limits.has_zero_object.zero_iso_is_terminal
- \+ *lemma* category_theory.limits.has_zero_object.zero_iso_is_terminal_hom
- \+ *lemma* category_theory.limits.has_zero_object.zero_iso_is_terminal_inv
- \+ *def* category_theory.limits.has_zero_object.zero_iso_terminal
- \+ *lemma* category_theory.limits.has_zero_object.zero_iso_terminal_hom
- \+ *lemma* category_theory.limits.has_zero_object.zero_iso_terminal_inv
- \- *lemma* category_theory.limits.is_equivalence_preserves_zero_morphisms

Modified src/category_theory/preadditive/additive_functor.lean
- \- *lemma* category_theory.functor.map_zero
- \- *def* category_theory.functor.map_zero_object

Modified src/category_theory/shift.lean




## [2022-02-17 17:02:32](https://github.com/leanprover-community/mathlib/commit/c9e8c64)
chore(*): update to lean 3.39.2c ([#12102](https://github.com/leanprover-community/mathlib/pull/12102))
#### Estimated changes
Modified leanpkg.toml




## [2022-02-17 17:02:31](https://github.com/leanprover-community/mathlib/commit/dcb2826)
feat(order/filter/basic): add eventually_eq.(smul/const_smul/sup/inf) ([#12101](https://github.com/leanprover-community/mathlib/pull/12101))
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.eventually_eq.const_smul
- \+ *lemma* filter.eventually_eq.inf
- \+ *lemma* filter.eventually_eq.smul
- \+ *lemma* filter.eventually_eq.sup



## [2022-02-17 15:34:44](https://github.com/leanprover-community/mathlib/commit/307711e)
feat(group_theory/general_commutator): subgroup.pi commutes with the general_commutator ([#11825](https://github.com/leanprover-community/mathlib/pull/11825))
#### Estimated changes
Modified src/group_theory/general_commutator.lean
- \+ *lemma* general_commutator_pi_pi_le
- \+ *lemma* general_commutator_pi_pi_of_fintype

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.le_pi_iff
- \+ *lemma* subgroup.pi_eq_bot_iff
- \+ *lemma* subgroup.pi_le_iff
- \+ *lemma* subgroup.pi_mem_of_single_mem
- \+ *lemma* subgroup.pi_mem_of_single_mem_aux
- \+ *lemma* subgroup.single_mem_pi



## [2022-02-17 13:10:49](https://github.com/leanprover-community/mathlib/commit/b54f44f)
feat(data/matrix/notation): expansions of matrix multiplication for 2x2 and 3x3 ([#12088](https://github.com/leanprover-community/mathlib/pull/12088))
A clever way to generalize this would be to make a recursivedefinition of `mul` and `one` that's defeq to the desired `![...]` result and prove that's equal to the usual definition, but that doesn't help with actually writing the lemma statement, which is the tedious bit.
#### Estimated changes
Modified src/data/matrix/notation.lean
- \+ *lemma* matrix.mul_fin_three
- \+ *lemma* matrix.mul_fin_two
- \+ *lemma* matrix.one_fin_three
- \+ *lemma* matrix.one_fin_two



## [2022-02-17 12:16:09](https://github.com/leanprover-community/mathlib/commit/eb8d58d)
fix(topology/algebra/basic): remove duplicate lemma ([#12097](https://github.com/leanprover-community/mathlib/pull/12097))
This lemma duplicates the lemma of the same name in the root namespace, and should not be in this namespace in the first place.
The other half of [#12072](https://github.com/leanprover-community/mathlib/pull/12072), now that the dependent PR is merged.
#### Estimated changes
Modified src/topology/algebra/module/basic.lean
- \- *lemma* continuous_linear_map.continuous.zsmul
- \- *lemma* continuous_linear_map.continuous_zsmul



## [2022-02-17 12:16:07](https://github.com/leanprover-community/mathlib/commit/4afd667)
feat(measure_theory/integral): add `integral_sum_measure` ([#12090](https://github.com/leanprover-community/mathlib/pull/12090))
Also add supporting lemmas about finite and infinite sums of measures.
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean
- \- *lemma* integrable_zero_measure
- \+ *theorem* measure_theory.integrable_finset_sum_measure
- \+ *lemma* measure_theory.integrable_zero_measure

Modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* measure_theory.is_fundamental_domain.pairwise_ae_disjoint_of_ac

Modified src/measure_theory/integral/bochner.lean
- \+ *theorem* measure_theory.has_sum_integral_measure
- \+ *theorem* measure_theory.integral_finset_sum_measure
- \+ *theorem* measure_theory.integral_sum_measure
- \+ *lemma* measure_theory.nndist_integral_add_measure_le_lintegral

Modified src/measure_theory/integral/lebesgue.lean
- \+ *theorem* measure_theory.has_sum_lintegral_measure
- \+ *lemma* measure_theory.lintegral_finset_sum_measure

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.has_sum_integral_Union_ae
- \- *lemma* measure_theory.has_sum_integral_Union_of_null_inter
- \+ *lemma* measure_theory.integral_Union_ae
- \- *lemma* measure_theory.integral_Union_of_null_inter

Modified src/measure_theory/measure/measure_space.lean
- \+ *def* measure_theory.measure.coe_add_hom
- \+ *lemma* measure_theory.measure.coe_finset_sum
- \+ *theorem* measure_theory.measure.finset_sum_apply
- \+ *lemma* measure_theory.measure.sum_add_sum_compl
- \+ *lemma* measure_theory.measure.sum_coe_finset
- \+ *lemma* measure_theory.measure.sum_fintype



## [2022-02-17 11:20:26](https://github.com/leanprover-community/mathlib/commit/20cf3ca)
feat(ring_theory/discriminant): add discr_eq_discr_of_to_matrix_coeff_is_integral ([#11994](https://github.com/leanprover-community/mathlib/pull/11994))
We add `discr_eq_discr_of_to_matrix_coeff_is_integral`: if `b` and `b'` are `ℚ`-basis of a number field `K` such that
`∀ i j, is_integral ℤ (b.to_matrix b' i j)` and `∀ i j, is_integral ℤ (b'.to_matrix b i j` then
`discr ℚ b = discr ℚ b'`.
#### Estimated changes
Modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* basis.to_matrix_map_vec_mul

Modified src/ring_theory/discriminant.lean
- \+ *lemma* algebra.discr_eq_discr_of_to_matrix_coeff_is_integral
- \+ *lemma* algebra.discr_reindex

Modified src/ring_theory/trace.lean
- \+ *lemma* algebra.trace_matrix_reindex



## [2022-02-17 10:43:57](https://github.com/leanprover-community/mathlib/commit/614758e)
feat(order/category/DistribLattice): The category of distributive lattices ([#12092](https://github.com/leanprover-community/mathlib/pull/12092))
Define `DistribLattice`, the category of distributive lattices.
#### Estimated changes
Added src/order/category/DistribLattice.lean
- \+ *def* DistribLattice.dual
- \+ *def* DistribLattice.dual_equiv
- \+ *def* DistribLattice.iso.mk
- \+ *def* DistribLattice.of
- \+ *def* DistribLattice
- \+ *lemma* DistribLattice_dual_comp_forget_to_Lattice

Modified src/order/category/Lattice.lean




## [2022-02-17 10:00:32](https://github.com/leanprover-community/mathlib/commit/58a3720)
feat(analysis/inner_product_space/pi_L2): `complex.isometry_of_orthonormal` ([#11970](https://github.com/leanprover-community/mathlib/pull/11970))
Add a definition for the isometry between `ℂ` and a two-dimensional
real inner product space given by a basis, and an associated `simp`
lemma for how this relates to `basis.map`.
This definition is just the composition of two existing definitions,
`complex.isometry_euclidean` and (the inverse of)
`basis.isometry_euclidean_of_orthonormal`.  However, it's still useful
to have it as a single definition when using it to define and prove
basic properties of oriented angles (in an oriented two-dimensional
real inner product space), to keep definitions and terms in proofs
simpler and to avoid tactics such as `simp` or `rw` rearranging things
inside this definition when not wanted (almost everything just needs
to use some isometry between these two spaces without caring about the
details of how it's defined, so it seems best to use a single `def`
for this isometry, and on the rare occasions where the details of how
it's defined matter, prove specific lemmas about the required
properties).
#### Estimated changes
Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *def* complex.isometry_of_orthonormal
- \+ *lemma* complex.isometry_of_orthonormal_apply
- \+ *lemma* complex.isometry_of_orthonormal_symm_apply
- \+ *lemma* complex.map_isometry_of_orthonormal



## [2022-02-17 07:43:58](https://github.com/leanprover-community/mathlib/commit/a355d88)
feat(topology/metric_space/gluing): metric space structure on sigma types ([#11965](https://github.com/leanprover-community/mathlib/pull/11965))
We define a (noncanonical) metric space structure on sigma types (aka arbitrary disjoint unions), as follows. Each piece is isometrically embedded in the union, while for `x` and `y` in different pieces their distance is `dist x x0 + 1 + dist y0 y`, where `x0` and `y0` are basepoints in the respective parts. This is *not* registered as an instance.
This definition was already there for sum types (aka disjoint union of two pieces). We also fix this existing definition to avoid `inhabited` assumptions.
#### Estimated changes
Modified src/topology/metric_space/gluing.lean
- \+ *lemma* metric.isometry_inl
- \+ *lemma* metric.isometry_inr
- \- *lemma* metric.isometry_on_inl
- \- *lemma* metric.isometry_on_inr
- \+ *lemma* metric.sigma.dist_ne
- \+ *lemma* metric.sigma.dist_same
- \+ *lemma* metric.sigma.fst_eq_of_dist_lt_one
- \+ *def* metric.sigma.has_dist
- \+ *lemma* metric.sigma.isometry_mk
- \+ *lemma* metric.sigma.one_le_dist_of_ne
- \+/\- *lemma* metric.sum.dist_eq_glue_dist

Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* is_complete_Union_separated



## [2022-02-17 06:05:54](https://github.com/leanprover-community/mathlib/commit/09960ea)
feat(algebra/group_power/basic): `two_zsmul` ([#12094](https://github.com/leanprover-community/mathlib/pull/12094))
Mark `zpow_two` with `@[to_additive two_zsmul]`.  I see no apparent
reason for this result not to use `to_additive`, and I found I had a
use for the additive version.
#### Estimated changes
Modified src/algebra/group_power/basic.lean




## [2022-02-17 05:32:27](https://github.com/leanprover-community/mathlib/commit/1831d85)
feat(category_theory/limits): Preserves epi of preserves pushout. ([#12084](https://github.com/leanprover-community/mathlib/pull/12084))
#### Estimated changes
Modified src/category_theory/limits/constructions/epi_mono.lean
- \+ *lemma* category_theory.reflects_epi



## [2022-02-17 00:34:41](https://github.com/leanprover-community/mathlib/commit/84f12be)
chore(algebra/star/self_adjoint): improve definitional unfolding of pow and div ([#12085](https://github.com/leanprover-community/mathlib/pull/12085))
#### Estimated changes
Modified src/algebra/star/self_adjoint.lean
- \+ *lemma* self_adjoint.coe_div
- \+/\- *lemma* self_adjoint.coe_inv
- \+/\- *lemma* self_adjoint.coe_mul
- \+/\- *lemma* self_adjoint.coe_one
- \+ *lemma* self_adjoint.coe_pow
- \+ *lemma* self_adjoint.coe_zpow



## [2022-02-17 00:34:40](https://github.com/leanprover-community/mathlib/commit/834fd30)
feat(topology/continuous_function/algebra): generalize algebra instances ([#12055](https://github.com/leanprover-community/mathlib/pull/12055))
This adds:
* some missing instances in the algebra hierarchy (`comm_semigroup`, `mul_one_class`, `mul_zero_class`, `monoid_with_zero`, `comm_monoid_with_zero`, `comm_semiring`).
* finer-grained scalar action instances, notably none of which require `topological_space R` any more, as they only need `has_continuous_const_smul R M` instead of `has_continuous_smul R M`.
* continuity lemmas about `zpow` on groups and `zsmul` on additive groups (copied directly from the lemmas about `pow` on monoids), which are used to avoid diamonds in the int-action. In order to make room for these, the lemmas about `zpow` on groups with zero have been renamed to `zpow₀`, which is consistent with how the similar clash with `inv` is solved.
* a few lemmas about `mk_of_compact` since an existing proof was broken by `refl` closing the goal earlier than before.
#### Estimated changes
Modified src/analysis/fourier.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/analysis/specific_limits.lean


Modified src/measure_theory/integral/circle_integral.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* continuous.zpow
- \+ *lemma* continuous_at.zpow
- \+ *lemma* continuous_at_zpow
- \+ *lemma* continuous_on.zpow
- \+ *lemma* continuous_on_zpow
- \+ *lemma* continuous_within_at.zpow
- \+ *lemma* continuous_zpow
- \+ *lemma* filter.tendsto.zpow

Modified src/topology/algebra/group_with_zero.lean
- \- *lemma* continuous.zpow
- \+ *lemma* continuous.zpow₀
- \- *lemma* continuous_at.zpow
- \+ *lemma* continuous_at.zpow₀
- \- *lemma* continuous_at_zpow
- \+ *lemma* continuous_at_zpow₀
- \- *lemma* continuous_on.zpow
- \+ *lemma* continuous_on.zpow₀
- \- *lemma* continuous_on_zpow
- \+ *lemma* continuous_on_zpow₀
- \- *lemma* continuous_within_at.zpow
- \+ *lemma* continuous_within_at.zpow₀
- \- *lemma* filter.tendsto.zpow
- \+ *lemma* filter.tendsto.zpow₀

Modified src/topology/category/Top/basic.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* continuous_map.coe_div
- \+/\- *lemma* continuous_map.coe_inv
- \+/\- *lemma* continuous_map.coe_one
- \+/\- *lemma* continuous_map.coe_pow
- \+/\- *lemma* continuous_map.coe_smul
- \+ *lemma* continuous_map.coe_zpow
- \+/\- *lemma* continuous_map.div_comp
- \+/\- *lemma* continuous_map.inv_comp
- \+/\- *lemma* continuous_map.mul_comp
- \+/\- *lemma* continuous_map.one_comp
- \+/\- *lemma* continuous_map.pow_comp
- \+/\- *lemma* continuous_map.smul_apply
- \+/\- *lemma* continuous_map.smul_comp
- \+ *lemma* continuous_map.zpow_comp

Modified src/topology/continuous_function/basic.lean
- \- *lemma* continuous_map.coe_inj
- \+ *lemma* continuous_map.coe_injective

Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.mk_of_compact_add
- \+ *lemma* bounded_continuous_function.mk_of_compact_neg
- \+ *lemma* bounded_continuous_function.mk_of_compact_one
- \+ *lemma* bounded_continuous_function.mk_of_compact_sub

Modified src/topology/continuous_function/compact.lean


Modified src/topology/tietze_extension.lean




## [2022-02-17 00:34:39](https://github.com/leanprover-community/mathlib/commit/27df8a0)
feat(topology/instances/rat): some facts about topology on `rat` ([#11832](https://github.com/leanprover-community/mathlib/pull/11832))
* `ℚ` is a totally disconnected space;
* `cocompact  ℚ` is not a countably generated filter;
* hence, `alexandroff  ℚ` is not a first countable topological space.
#### Estimated changes
Modified src/topology/dense_embedding.lean
- \+ *lemma* dense_inducing.interior_compact_eq_empty

Added src/topology/instances/rat.lean
- \+ *lemma* rat.dense_compl_compact
- \+ *lemma* rat.interior_compact_eq_empty
- \+ *lemma* rat.not_countably_generated_cocompact
- \+ *lemma* rat.not_countably_generated_nhds_infty_alexandroff
- \+ *lemma* rat.not_first_countable_topology_alexandroff
- \+ *lemma* rat.not_second_countable_topology_alexandroff



## [2022-02-16 22:44:23](https://github.com/leanprover-community/mathlib/commit/7dae87f)
feat(topology/metric_space/basic): ext lemmas for metric spaces ([#12070](https://github.com/leanprover-community/mathlib/pull/12070))
Also add a few results in `metric_space.basic`:
* A decreasing intersection of closed sets with diameter tending to `0` is nonempty in a complete space
* new constructions of metric spaces by pulling back structures (and adjusting definitional equalities)
* fixing `metric_space empty` and `metric_space punit` to make sure the uniform structure is definitionally the right one.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.eq_top_of_ne_bot

Modified src/topology/metric_space/basic.lean
- \+ *lemma* cauchy_seq_of_le_tendsto_0'
- \+ *lemma* dense.exists_dist_lt
- \+ *lemma* dense_range.exists_dist_lt
- \+ *def* embedding.comap_metric_space
- \+ *lemma* is_complete.nonempty_Inter_of_nonempty_bInter
- \+ *lemma* metric.nonempty_Inter_of_nonempty_bInter
- \+ *lemma* metric_space.ext
- \+ *def* metric_space.replace_topology
- \+ *lemma* metric_space.replace_topology_eq
- \+ *lemma* metric_space.replace_uniformity_eq
- \+ *lemma* pseudo_metric_space.ext
- \+ *lemma* pseudo_metric_space.replace_uniformity_eq
- \+/\- *def* uniform_embedding.comap_metric_space

Modified src/topology/uniform_space/basic.lean




## [2022-02-16 22:44:22](https://github.com/leanprover-community/mathlib/commit/5db1ae4)
feat(analysis/specific_limits): useful specializations of some lemmas ([#12069](https://github.com/leanprover-community/mathlib/pull/12069))
#### Estimated changes
Modified src/algebra/group_power/order.lean
- \+ *lemma* pow_le_pow_iff

Modified src/analysis/normed/group/basic.lean
- \+ *lemma* antilipschitz_with.le_mul_norm_sub

Modified src/analysis/specific_limits.lean
- \+ *lemma* summable_geometric_two_encode
- \+ *lemma* tendsto_pow_const_mul_const_pow_of_lt_one
- \+ *lemma* tendsto_self_mul_const_pow_of_abs_lt_one
- \+ *lemma* tendsto_self_mul_const_pow_of_lt_one



## [2022-02-16 22:44:21](https://github.com/leanprover-community/mathlib/commit/1bf4181)
feat(data/equiv/{basic,mul_equiv)}: add Pi_subsingleton ([#12040](https://github.com/leanprover-community/mathlib/pull/12040))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* equiv.Pi_subsingleton

Modified src/data/equiv/mul_add.lean
- \+ *def* mul_equiv.Pi_subsingleton



## [2022-02-16 22:44:20](https://github.com/leanprover-community/mathlib/commit/b2aaece)
feat(field_theory/is_alg_closed): alg closed and char p implies perfect ([#12037](https://github.com/leanprover-community/mathlib/pull/12037))
#### Estimated changes
Modified src/field_theory/is_alg_closed/basic.lean


Modified src/field_theory/perfect_closure.lean




## [2022-02-16 21:09:23](https://github.com/leanprover-community/mathlib/commit/bd67e85)
feat(algebra/char_p/basic): add ring_char_of_prime_eq_zero ([#12024](https://github.com/leanprover-community/mathlib/pull/12024))
The characteristic of a ring is `p` if `p` is a prime and `p = 0` in the ring.
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+ *lemma* char_p.ring_char_of_prime_eq_zero



## [2022-02-16 21:09:22](https://github.com/leanprover-community/mathlib/commit/0fe91d0)
feat(data/part): Instance lemmas ([#12001](https://github.com/leanprover-community/mathlib/pull/12001))
Lemmas about `part` instances, proved by `tidy`
#### Estimated changes
Modified src/data/part.lean
- \+ *lemma* part.append_mem_append
- \+ *lemma* part.div_mem_div
- \+ *lemma* part.inter_mem_inter
- \+ *lemma* part.inv_mem_inv
- \+ *lemma* part.inv_some
- \+ *lemma* part.mod_mem_mod
- \+ *lemma* part.mul_mem_mul
- \+ *lemma* part.one_mem_one
- \+ *lemma* part.sdiff_mem_sdiff
- \+ *lemma* part.some_append_some
- \+ *lemma* part.some_div_some
- \+ *lemma* part.some_inter_some
- \+ *lemma* part.some_mod_some
- \+ *lemma* part.some_mul_some
- \+ *lemma* part.some_sdiff_some
- \+ *lemma* part.some_union_some
- \+ *lemma* part.union_mem_union



## [2022-02-16 19:16:09](https://github.com/leanprover-community/mathlib/commit/b395a67)
chore(data/finsupp/pointwise): golf using injective lemmas ([#12086](https://github.com/leanprover-community/mathlib/pull/12086))
#### Estimated changes
Modified src/data/finsupp/pointwise.lean
- \+ *lemma* finsupp.coe_mul
- \- *lemma* finsupp.coe_pointwise_module
- \+ *lemma* finsupp.coe_pointwise_smul



## [2022-02-16 19:16:08](https://github.com/leanprover-community/mathlib/commit/0ab9b5f)
chore(topology/continuous_function/bounded): golf algebra instances ([#12082](https://github.com/leanprover-community/mathlib/pull/12082))
Using the `function.injective.*` lemmas saves a lot of proofs.
This also adds a few missing lemmas about `one` that were already present for `zero`.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean
- \+ *lemma* bounded_continuous_function.coe_one
- \- *lemma* bounded_continuous_function.coe_zero
- \+ *lemma* bounded_continuous_function.forall_coe_one_iff_one
- \- *lemma* bounded_continuous_function.forall_coe_zero_iff_zero
- \+ *lemma* bounded_continuous_function.one_comp_continuous
- \- *lemma* bounded_continuous_function.zero_comp_continuous



## [2022-02-16 19:16:06](https://github.com/leanprover-community/mathlib/commit/d86ce02)
chore(ring_theory/fractional_ideal): golf ([#12076](https://github.com/leanprover-community/mathlib/pull/12076))
#### Estimated changes
Modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* fractional_ideal.coe_inf
- \+ *lemma* fractional_ideal.coe_sup



## [2022-02-16 19:16:04](https://github.com/leanprover-community/mathlib/commit/15c6eee)
feat(logic/basic): Better congruence lemmas for `or`, `or_or_or_comm` ([#12004](https://github.com/leanprover-community/mathlib/pull/12004))
Prove `or_congr_left` and `or_congr_right` and rename the existing `or_congr_left`/`or_congr_right` to `or_congr_left'`/`or_congr_right'` to match the `and` lemmas. Also prove `or_rotate`, `or.rotate`, `or_or_or_comm` based on `and` again.
#### Estimated changes
Modified src/data/fin/basic.lean


Modified src/data/set/basic.lean


Modified src/logic/basic.lean
- \+ *lemma* Exists₂.imp
- \+/\- *lemma* and.rotate
- \+ *lemma* and_rotate
- \+ *lemma* forall₂_imp
- \+ *lemma* or.rotate
- \+ *lemma* or_congr_left'
- \+ *lemma* or_congr_left
- \- *theorem* or_congr_left
- \+ *lemma* or_congr_right'
- \+ *lemma* or_congr_right
- \- *theorem* or_congr_right
- \+ *lemma* or_or_or_comm
- \+ *lemma* or_rotate



## [2022-02-16 19:16:03](https://github.com/leanprover-community/mathlib/commit/5e3d465)
feat(category_theory/category/PartialFun): The category of types with partial functions ([#11866](https://github.com/leanprover-community/mathlib/pull/11866))
Define `PartialFun`, the category of types with partial functions, and show its equivalence with `Pointed`.
#### Estimated changes
Added src/category_theory/category/PartialFun.lean
- \+ *def* PartialFun.iso.mk
- \+ *def* PartialFun.of
- \+ *def* PartialFun
- \+ *def* Pointed_to_PartialFun
- \+ *def* Type_to_PartialFun

Modified src/category_theory/category/Pointed.lean
- \+ *def* Pointed.iso.mk

Modified src/data/subtype.lean
- \+/\- *lemma* exists_eq_subtype_mk_iff
- \+/\- *lemma* exists_subtype_mk_eq_iff
- \+ *lemma* subtype.coe_inj
- \+ *lemma* subtype.coe_injective
- \- *theorem* subtype.coe_injective
- \+ *lemma* subtype.val_inj
- \+ *lemma* subtype.val_injective
- \- *theorem* subtype.val_injective



## [2022-02-16 17:16:29](https://github.com/leanprover-community/mathlib/commit/3c78d00)
docs(group_theory/semidirect_product): fix typo in module docs ([#12083](https://github.com/leanprover-community/mathlib/pull/12083))
#### Estimated changes
Modified src/group_theory/semidirect_product.lean




## [2022-02-16 17:16:27](https://github.com/leanprover-community/mathlib/commit/3107a83)
feat(algebra/char_p/basic): Generalize `frobenius_inj`. ([#12079](https://github.com/leanprover-community/mathlib/pull/12079))
#### Estimated changes
Modified src/algebra/char_p/basic.lean
- \+/\- *theorem* frobenius_inj



## [2022-02-16 17:16:26](https://github.com/leanprover-community/mathlib/commit/0eb160a)
feat(data/finset/basic): When `insert` is injective and other lemmas ([#11982](https://github.com/leanprover-community/mathlib/pull/11982))
* `insert`/`cons` lemmas for `finset` and `multiset`
* `has_ssubset` instance for `multiset`
* `finset.sdiff_nonempty`
* `disjoint.of_image_finset`, `finset.disjoint_image`, `finset.disjoint_map`
* `finset.exists_eq_insert_iff`
* `mem` lemmas
* change `pred` to `- 1` into the statement of `finset.card_erase_of_mem`
#### Estimated changes
Modified src/combinatorics/derangements/finite.lean


Modified src/combinatorics/set_family/shadow.lean


Modified src/combinatorics/simple_graph/basic.lean


Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/data/finset/basic.lean
- \+ *lemma* disjoint.forall_ne_finset
- \+ *lemma* disjoint.of_image_finset
- \+ *lemma* finset.cons_subset
- \+ *lemma* finset.disjoint_image
- \+ *lemma* finset.disjoint_map
- \+ *lemma* finset.eq_of_not_mem_of_mem_insert
- \+ *lemma* finset.insert_inj
- \+ *lemma* finset.insert_inj_on
- \+ *lemma* finset.sdiff_nonempty
- \+ *lemma* finset.ssubset_cons
- \+ *lemma* finset.ssubset_iff_exists_cons_subset
- \+ *lemma* finset.subset_cons

Modified src/data/finset/card.lean
- \+/\- *lemma* finset.card_eq_succ
- \+/\- *lemma* finset.card_erase_eq_ite
- \+/\- *lemma* finset.card_erase_of_mem
- \+ *lemma* finset.exists_eq_insert_iff

Modified src/data/finset/powerset.lean


Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.cons_subset_cons
- \+ *lemma* multiset.ssubset_cons
- \+ *lemma* multiset.subset_cons

Modified src/data/nat/totient.lean


Modified src/data/polynomial/erase_lead.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.eq_of_not_mem_of_mem_insert
- \+ *lemma* set.insert_inj
- \+ *lemma* set.mem_of_mem_insert_of_ne
- \- *theorem* set.mem_of_mem_insert_of_ne

Modified src/data/set/finite.lean


Modified src/data/set/function.lean
- \+ *lemma* function.insert_inj_on

Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/lagrange.lean


Modified src/logic/basic.lean
- \+ *lemma* has_mem.mem.ne_of_not_mem'
- \+ *lemma* has_mem.mem.ne_of_not_mem
- \+ *lemma* ne_of_mem_of_not_mem'
- \+ *lemma* ne_of_mem_of_not_mem
- \- *theorem* ne_of_mem_of_not_mem



## [2022-02-16 17:16:25](https://github.com/leanprover-community/mathlib/commit/6bcb12c)
feat(order/antisymmetrization): Turning a preorder into a partial order ([#11728](https://github.com/leanprover-community/mathlib/pull/11728))
Define `antisymmetrization`, the quotient of a preorder by the "less than both ways" relation. This effectively turns a preorder into a partial order, and this operation is functorial as shown by the new `Preorder_to_PartialOrder`.
#### Estimated changes
Modified src/data/quot.lean


Added src/order/antisymmetrization.lean
- \+ *lemma* antisymm_rel.image
- \+ *def* antisymm_rel.setoid
- \+ *lemma* antisymm_rel.symm
- \+ *lemma* antisymm_rel.trans
- \+ *def* antisymm_rel
- \+ *lemma* antisymm_rel_iff_eq
- \+ *lemma* antisymm_rel_refl
- \+ *lemma* antisymm_rel_swap
- \+ *def* antisymmetrization
- \+ *lemma* of_antisymmetrization_le_of_antisymmetrization_iff
- \+ *lemma* of_antisymmetrization_lt_of_antisymmetrization_iff
- \+ *lemma* order_hom.antisymmetrization_apply
- \+ *lemma* order_hom.antisymmetrization_apply_mk
- \+ *lemma* order_hom.coe_antisymmetrization
- \+ *def* order_hom.to_antisymmetrization
- \+ *def* order_iso.dual_antisymmetrization
- \+ *lemma* order_iso.dual_antisymmetrization_apply
- \+ *lemma* order_iso.dual_antisymmetrization_symm_apply
- \+ *def* to_antisymmetrization
- \+ *lemma* to_antisymmetrization_le_to_antisymmetrization_iff
- \+ *lemma* to_antisymmetrization_lt_to_antisymmetrization_iff
- \+ *lemma* to_antisymmetrization_mono
- \+ *lemma* to_antisymmetrization_of_antisymmetrization

Modified src/order/category/PartialOrder.lean
- \+ *def* Preorder_to_PartialOrder
- \+ *def* Preorder_to_PartialOrder_comp_to_dual_iso_to_dual_comp_Preorder_to_PartialOrder
- \+ *def* Preorder_to_PartialOrder_forget_adjunction

Modified src/order/rel_classes.lean
- \+/\- *lemma* antisymm'
- \+ *lemma* antisymm_iff



## [2022-02-16 16:11:48](https://github.com/leanprover-community/mathlib/commit/8a286af)
chore(topology/algebra/mul_action): rename type variables ([#12020](https://github.com/leanprover-community/mathlib/pull/12020))
#### Estimated changes
Modified src/topology/algebra/mul_action.lean
- \+/\- *lemma* filter.tendsto.smul
- \+/\- *lemma* filter.tendsto.smul_const
- \+/\- *lemma* has_continuous_smul_Inf
- \+/\- *lemma* has_continuous_smul_inf
- \+/\- *lemma* has_continuous_smul_infi



## [2022-02-16 14:23:54](https://github.com/leanprover-community/mathlib/commit/e815675)
chore(topology/algebra/module/basic): remove two duplicate lemmas ([#12072](https://github.com/leanprover-community/mathlib/pull/12072))
`continuous_linear_map.continuous_nsmul` is nothing to do with `continuous_linear_map`s, and is the same as `continuous_nsmul`, but the latter doesn't require commutativity. There is no reason to keep the former.
This lemma was added in [#7084](https://github.com/leanprover-community/mathlib/pull/7084), but probably got missed due to how large that PR had to be.
We can't remove `continuous_linear_map.continuous_zsmul` until [#12055](https://github.com/leanprover-community/mathlib/pull/12055) is merged, as there is currently no `continuous_zsmul` in the root namespace.
#### Estimated changes
Modified src/topology/algebra/module/basic.lean
- \- *lemma* continuous_linear_map.continuous.nsmul
- \- *lemma* continuous_linear_map.continuous_nsmul



## [2022-02-16 14:23:53](https://github.com/leanprover-community/mathlib/commit/a26d17f)
feat(mv_polynomial/supported): restrict_to_vars ([#12043](https://github.com/leanprover-community/mathlib/pull/12043))
#### Estimated changes
Modified src/data/mv_polynomial/supported.lean
- \+ *lemma* mv_polynomial.exists_restrict_to_vars



## [2022-02-16 14:23:52](https://github.com/leanprover-community/mathlib/commit/62297cf)
feat(analysis/complex/cauchy_integral, analysis/analytic/basic): entire functions have power series with infinite radius of convergence ([#11948](https://github.com/leanprover-community/mathlib/pull/11948))
This proves that a formal multilinear series `p` which represents a function `f : 𝕜 → E` on a ball of every positive radius, then `p` represents `f` on a ball of infinite radius. Consequently, it is shown that if `f : ℂ → E` is differentiable everywhere, then `cauchy_power_series f z R` represents `f` as a power series centered at `z` in the entirety of `ℂ`, regardless of `R` (assuming `0 < R`).
- [x] depends on: [#11896](https://github.com/leanprover-community/mathlib/pull/11896)
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+ *theorem* has_fpower_series_on_ball.r_eq_top_of_exists

Modified src/analysis/complex/cauchy_integral.lean




## [2022-02-16 13:36:23](https://github.com/leanprover-community/mathlib/commit/22fdf47)
chore(linear_algebra/affine_space/affine_map,topology/algebra/continuous_affine_map): generalized scalar instances ([#11978](https://github.com/leanprover-community/mathlib/pull/11978))
The main result here is that `distrib_mul_action`s are available on affine maps to a module, inherited from their codomain.
This fixes a diamond in the `int`-action that was already present for `int`-affine maps, and prevents the new `nat`-action introducing a diamond.
This also removes the requirement for `R` to be a `topological_space` in the scalar action for `continuous_affine_map` by using `has_continuous_const_smul` instead of `has_continuous_smul`.
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_map.lean
- \+/\- *lemma* affine_map.coe_smul
- \+/\- *lemma* affine_map.smul_linear
- \+/\- *def* affine_map.to_const_prod_linear_map

Modified src/topology/algebra/continuous_affine_map.lean
- \+/\- *lemma* continuous_affine_map.coe_smul
- \+/\- *lemma* continuous_affine_map.smul_apply



## [2022-02-16 11:53:41](https://github.com/leanprover-community/mathlib/commit/32beebb)
feat(algebra/order/monoid): add simp lemmas ([#12030](https://github.com/leanprover-community/mathlib/pull/12030))
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+ *lemma* additive.of_mul_le
- \+ *lemma* additive.of_mul_lt
- \+ *lemma* additive.to_mul_le
- \+ *lemma* additive.to_mul_lt
- \+ *lemma* multiplicative.of_add_le
- \+ *lemma* multiplicative.of_add_lt
- \+ *lemma* multiplicative.to_add_le
- \+ *lemma* multiplicative.to_add_lt



## [2022-02-16 11:53:40](https://github.com/leanprover-community/mathlib/commit/7542119)
refactor(algebra/group/basic): add extra typeclasses for negation ([#11960](https://github.com/leanprover-community/mathlib/pull/11960))
The new typeclasses are:
* `has_involutive_inv R`, stating that `(r⁻¹)⁻¹ = r`  
  (instances: `group`, `group_with_zero`, `ennreal`, `set`, `submonoid`)
* `has_involutive_neg R`, stating that `- -r = r`
  (instances: `add_group`, `ereal`, `module.ray`, `ray_vector`, `set`, `add_submonoid`, `jordan_decomposition`)
* `has_distrib_neg R`, stating that `-a * b = a * -b = -(a * b)`
  (instances: `ring`, `units`, `unitary`, `special_linear_group`, `GL_pos`)
While the original motivation only concerned the two `neg` typeclasses, the `to_additive` machinery forced the introduction of `has_involutive_inv`, which turned out to be used in more places than expected.
Adding these typeclases removes a large number of specialized `units R` lemmas as the lemmas about `R` now match themselves. A surprising number of lemmas elsewhere in the library can also be removed. The removed lemmas are:
* Lemmas about `units` (replaced by `units.has_distrib_neg`):
  * `units.neg_one_pow_eq_or`
  * `units.neg_pow`
  * `units.neg_pow_bit0`
  * `units.neg_pow_bit1`
  * `units.neg_sq`
  * `units.neg_inv` (now `inv_neg'` for arbitrary groups with distributive negation)
  * `units.neg_neg`
  * `units.neg_mul`
  * `units.mul_neg`
  * `units.neg_mul_eq_neg_mul`
  * `units.neg_mul_eq_mul_neg`
  * `units.neg_mul_neg`
  * `units.neg_eq_neg_one_mul`
  * `units.mul_neg_one`
  * `units.neg_one_mul`
  * `semiconj_by.units_neg_right`
  * `semiconj_by.units_neg_right_iff`
  * `semiconj_by.units_neg_left`
  * `semiconj_by.units_neg_left_iff`
  * `semiconj_by.units_neg_one_right`
  * `semiconj_by.units_neg_one_left`
  * `commute.units_neg_right`
  * `commute.units_neg_right_iff`
  * `commute.units_neg_left`
  * `commute.units_neg_left_iff`
  * `commute.units_neg_one_right`
  * `commute.units_neg_one_left`
* Lemmas about groups with zero (replaced by `group_with_zero.to_has_involutive_neg`):
  * `inv_inv₀`
  * `inv_involutive₀`
  * `inv_injective₀`
  * `inv_eq_iff` (now shared with the `inv_eq_iff_inv_eq` group lemma)
  * `eq_inv_iff` (now shared with the `eq_inv_iff_eq_inv` group lemma)
  * `equiv.inv₀`
  * `measurable_equiv.inv₀`
* Lemmas about `ereal` (replaced by `ereal.has_involutive_neg`):
  * `ereal.neg_neg`
  * `ereal.neg_inj`
  * `ereal.neg_eq_neg_iff`
  * `ereal.neg_eq_iff_neg_eq`
* Lemmas about `ennreal` (replaced by `ennreal.has_involutive_inv`):
  * `ereal.inv_inv`
  * `ereal.inv_involutive`
  * `ereal.inv_bijective`
  * `ereal.inv_eq_inv`
* Other lemmas:
  * `ray_vector.neg_neg`
  * `module.ray.neg_neg`
  * `module.ray.neg_involutive`
  * `module.ray.eq_neg_iff_eq_neg`
  * `set.inv_inv`
  * `set.neg_neg`
  * `submonoid.inv_inv`
  * `add_submonoid.neg_neg`
As a bonus, this provides the group `unitary R`  with a negation operator and all the lemmas listed for `units` above.
For now this doesn't attempt to unify `units.neg_smul` and `neg_smul`.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+/\- *theorem* inv_eq_iff_inv_eq
- \+/\- *theorem* inv_inj

Modified src/algebra/group/defs.lean


Modified src/algebra/group_power/basic.lean
- \- *theorem* units.neg_one_pow_eq_or
- \- *theorem* units.neg_pow
- \- *theorem* units.neg_pow_bit0
- \- *theorem* units.neg_pow_bit1
- \- *lemma* units.neg_sq

Modified src/algebra/group_with_zero/basic.lean
- \- *lemma* eq_inv_iff
- \- *lemma* inv_eq_iff
- \- *lemma* inv_injective₀
- \- *lemma* inv_inj₀
- \- *lemma* inv_involutive₀
- \- *lemma* inv_inv₀

Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/order/field.lean


Modified src/algebra/order/with_zero.lean


Modified src/algebra/periodic.lean


Modified src/algebra/pointwise.lean
- \+/\- *lemma* set.finite.inv
- \+/\- *lemma* set.image_inv
- \+/\- *lemma* set.inv_mem_inv
- \+/\- *lemma* set.inv_singleton
- \+/\- *lemma* set.inv_subset
- \+/\- *lemma* set.inv_subset_inv
- \+/\- *lemma* set.nonempty.inv
- \+/\- *lemma* set.nonempty_inv

Modified src/algebra/quandle.lean


Modified src/algebra/ring/basic.lean
- \- *theorem* commute.units_neg_left
- \- *theorem* commute.units_neg_left_iff
- \- *theorem* commute.units_neg_one_left
- \- *theorem* commute.units_neg_one_right
- \- *theorem* commute.units_neg_right
- \- *theorem* commute.units_neg_right_iff
- \+ *lemma* inv_neg'
- \- *lemma* semiconj_by.units_neg_left
- \- *lemma* semiconj_by.units_neg_left_iff
- \- *lemma* semiconj_by.units_neg_one_left
- \- *lemma* semiconj_by.units_neg_one_right
- \- *lemma* semiconj_by.units_neg_right
- \- *lemma* semiconj_by.units_neg_right_iff
- \- *lemma* units.mul_neg_one
- \- *lemma* units.neg_mul_eq_mul_neg
- \- *lemma* units.neg_mul_eq_neg_mul
- \- *lemma* units.neg_one_mul

Modified src/algebra/star/unitary.lean
- \+ *lemma* unitary.coe_neg

Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/asymptotics/superpolynomial_decay.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/lhopital.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/units.lean


Modified src/analysis/seminorm.lean


Modified src/analysis/special_functions/log_deriv.lean


Modified src/analysis/specific_limits.lean


Modified src/data/equiv/mul_add.lean
- \- *lemma* equiv.inv_symm₀

Modified src/data/real/conjugate_exponents.lean


Modified src/data/real/ennreal.lean
- \- *lemma* ennreal.inv_bijective
- \- *lemma* ennreal.inv_eq_inv
- \- *lemma* ennreal.inv_inv
- \- *lemma* ennreal.inv_involutive

Modified src/data/real/ereal.lean
- \- *theorem* ereal.neg_eq_iff_neg_eq
- \- *theorem* ereal.neg_eq_neg_iff
- \- *theorem* ereal.neg_inj

Modified src/data/real/golden_ratio.lean


Modified src/data/real/hyperreal.lean
- \+/\- *lemma* hyperreal.inv_epsilon_eq_omega

Modified src/data/real/irrational.lean


Modified src/data/real/nnreal.lean


Modified src/data/set/intervals/image_preimage.lean


Modified src/data/set/intervals/unordered_interval.lean


Modified src/field_theory/finite/basic.lean


Modified src/field_theory/ratfunc.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/pointwise.lean


Modified src/linear_algebra/affine_space/ordered.lean


Modified src/linear_algebra/alternating.lean


Modified src/linear_algebra/general_linear_group.lean


Modified src/linear_algebra/orientation.lean
- \- *lemma* module.ray.neg_involutive

Modified src/linear_algebra/special_linear_group.lean


Modified src/measure_theory/decomposition/jordan.lean


Modified src/measure_theory/group/arithmetic.lean


Modified src/measure_theory/group/measurable_equiv.lean
- \+/\- *def* measurable_equiv.inv
- \- *def* measurable_equiv.inv₀
- \+/\- *lemma* measurable_equiv.symm_inv
- \- *lemma* measurable_equiv.symm_inv₀

Modified src/measure_theory/group/prod.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/mean_inequalities.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/number_theory/l_series.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/padics/padic_numbers.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/tactic/norm_num.lean


Modified src/topology/instances/ennreal.lean




## [2022-02-16 11:53:38](https://github.com/leanprover-community/mathlib/commit/d24792c)
feat(model_theory/terms_and_formulas): Define satisfiability and semantic equivalence of formulas ([#11928](https://github.com/leanprover-community/mathlib/pull/11928))
Defines satisfiability of theories
Provides a default model of a satisfiable theory
Defines semantic (logical) equivalence of formulas
#### Estimated changes
Modified src/model_theory/basic.lean
- \- *def* first_order.language.empty
- \+ *lemma* first_order.language.nonempty_of_nonempty_constants

Modified src/model_theory/definability.lean


Modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* first_order.language.Theory.imp_semantically_equivalent_not_sup
- \+ *lemma* first_order.language.Theory.inf_semantically_equivalent_not_sup_not
- \+ *def* first_order.language.Theory.is_finitely_satisfiable
- \+ *lemma* first_order.language.Theory.is_satisfiable.is_finitely_satisfiable
- \+ *lemma* first_order.language.Theory.is_satisfiable.mono
- \+ *def* first_order.language.Theory.is_satisfiable.some_model
- \+ *lemma* first_order.language.Theory.is_satisfiable.some_model_models
- \+ *def* first_order.language.Theory.is_satisfiable
- \+ *lemma* first_order.language.Theory.model.is_satisfiable
- \+ *lemma* first_order.language.Theory.model.mono
- \+ *def* first_order.language.Theory.model
- \+ *def* first_order.language.Theory.models_bounded_formula
- \+ *lemma* first_order.language.Theory.models_formula_iff
- \+ *lemma* first_order.language.Theory.models_sentence_iff
- \+ *lemma* first_order.language.Theory.semantically_equivalent.realize_eq
- \+ *lemma* first_order.language.Theory.semantically_equivalent.some_model_realize_eq
- \+ *def* first_order.language.Theory.semantically_equivalent
- \+ *lemma* first_order.language.Theory.semantically_equivalent_not_not
- \+ *def* first_order.language.Theory.semantically_equivalent_setoid
- \+ *lemma* first_order.language.Theory.sup_semantically_equivalent_not_inf_not
- \+ *def* first_order.language.Theory
- \+/\- *def* first_order.language.bd_not
- \+ *lemma* first_order.language.realize_imp
- \+ *lemma* first_order.language.realize_inf
- \- *def* first_order.language.theory



## [2022-02-16 11:19:27](https://github.com/leanprover-community/mathlib/commit/6dfb24c)
feat(algebra/star/self_adjoint): define skew-adjoint elements of a star additive group ([#12013](https://github.com/leanprover-community/mathlib/pull/12013))
This defines the skew-adjoint elements of a star additive group, as the additive subgroup that satisfies `star x = -x`. The development is analogous to that of `self_adjoint`.
#### Estimated changes
Modified src/algebra/star/self_adjoint.lean
- \+ *lemma* skew_adjoint.bit0_mem
- \+ *lemma* skew_adjoint.coe_smul
- \+ *lemma* skew_adjoint.conjugate'
- \+ *lemma* skew_adjoint.conjugate
- \+ *lemma* skew_adjoint.mem_iff
- \+ *lemma* skew_adjoint.star_coe_eq
- \+ *def* skew_adjoint



## [2022-02-16 09:30:11](https://github.com/leanprover-community/mathlib/commit/06e6b35)
feat(analysis/special_functions/trigonometric/angle): `coe_pi_add_coe_pi` ([#12064](https://github.com/leanprover-community/mathlib/pull/12064))
Add another `simp` lemma to those expressing in different ways that 2π
is zero as a `real.angle`.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* real.angle.coe_pi_add_coe_pi



## [2022-02-16 07:45:37](https://github.com/leanprover-community/mathlib/commit/daf2989)
feat(algebra/big_operators): formula for product of sums to n+1 ([#12042](https://github.com/leanprover-community/mathlib/pull/12042))
#### Estimated changes
Modified src/algebra/big_operators/ring.lean
- \+ *lemma* finset.sum_range_succ_mul_sum_range_succ



## [2022-02-16 07:16:02](https://github.com/leanprover-community/mathlib/commit/6a09cd0)
chore(topology/uniform_space): use weaker TC assumptions ([#12066](https://github.com/leanprover-community/mathlib/pull/12066))
We don't need `[uniform_space β]` to prove
`uniform_space.completion.ext`.
#### Estimated changes
Modified src/topology/uniform_space/abstract_completion.lean


Modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* uniform_space.completion.ext



## [2022-02-15 20:57:33](https://github.com/leanprover-community/mathlib/commit/eeb2956)
feat(topology/algebra): relax some `Type*` assumptions to `Sort*` ([#12058](https://github.com/leanprover-community/mathlib/pull/12058))
When working on [#11720](https://github.com/leanprover-community/mathlib/pull/11720) I forgot that we have to deal with Prop-indexed infimums quite often, so this PR fixes that.
#### Estimated changes
Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/mul_action.lean




## [2022-02-15 19:34:16](https://github.com/leanprover-community/mathlib/commit/b0fe972)
feat (analysis/normed_space/spectrum): prove Gelfand's formula for the spectral radius ([#11916](https://github.com/leanprover-community/mathlib/pull/11916))
This establishes Gelfand's formula for the spectral radius in a complex Banach algebra `A`, namely that the sequence of n-th roots of the norms of n-th powers of any element tends to its spectral radius. Some results which hold in more generality concerning the function `z ↦ ring.inverse (1 - z • a)` are also given. In particular, this function is differentiable on the disk with radius the reciprocal of the spectral radius, and it has a power series on the ball with radius equal to the reciprocal of the norm of `a : A`.
Currently, the version of Gelfand's formula which appears here includes an assumption that `A` is second countable, which won't hold in general unless `A` is separable. This is not a true (i.e., mathematical) limitation, but a consequence of the current implementation of Bochner integrals in mathlib (which are an essential feature in the proof of Gelfand's formula because of its use of the Cauchy integral formula). When Bochner integrals are refactored, this type class assumption can be dropped.
- [x] depends on: [#11869](https://github.com/leanprover-community/mathlib/pull/11869)
- [x] depends on: [#11896](https://github.com/leanprover-community/mathlib/pull/11896) 
- [x] depends on: [#11915](https://github.com/leanprover-community/mathlib/pull/11915)
#### Estimated changes
Modified src/analysis/normed_space/spectrum.lean
- \+ *theorem* spectrum.differentiable_on_inverse_one_sub_smul
- \+ *lemma* spectrum.has_fpower_series_on_ball_inverse_one_sub_smul
- \+ *lemma* spectrum.is_unit_one_sub_smul_of_lt_inv_radius
- \+ *lemma* spectrum.limsup_pow_nnnorm_pow_one_div_le_spectral_radius
- \+ *lemma* spectrum.mem_resolvent_set_of_spectral_radius_lt
- \+ *theorem* spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius
- \+ *theorem* spectrum.pow_norm_pow_one_div_tendsto_nhds_spectral_radius



## [2022-02-15 19:34:15](https://github.com/leanprover-community/mathlib/commit/d76ac2e)
feat(category_theory): separators and detectors ([#11880](https://github.com/leanprover-community/mathlib/pull/11880))
#### Estimated changes
Modified src/category_theory/balanced.lean
- \+ *lemma* category_theory.balanced_opposite

Added src/category_theory/generator.lean
- \+ *lemma* category_theory.groupoid_of_is_codetecting_empty
- \+ *lemma* category_theory.groupoid_of_is_detecting_empty
- \+ *lemma* category_theory.is_codetecting.is_coseparating
- \+ *lemma* category_theory.is_codetecting.mono
- \+ *def* category_theory.is_codetecting
- \+ *lemma* category_theory.is_codetecting_empty_of_groupoid
- \+ *lemma* category_theory.is_codetecting_iff_is_coseparating
- \+ *lemma* category_theory.is_codetecting_op_iff
- \+ *lemma* category_theory.is_codetecting_unop_iff
- \+ *lemma* category_theory.is_codetector.def
- \+ *lemma* category_theory.is_codetector.is_coseparator
- \+ *def* category_theory.is_codetector
- \+ *lemma* category_theory.is_codetector_def
- \+ *lemma* category_theory.is_codetector_iff_reflects_isomorphisms_yoneda_obj
- \+ *lemma* category_theory.is_codetector_op_iff
- \+ *lemma* category_theory.is_codetector_unop_iff
- \+ *lemma* category_theory.is_coseparating.is_codetecting
- \+ *lemma* category_theory.is_coseparating.mono
- \+ *def* category_theory.is_coseparating
- \+ *lemma* category_theory.is_coseparating_empty_of_thin
- \+ *lemma* category_theory.is_coseparating_op_iff
- \+ *lemma* category_theory.is_coseparating_unop_iff
- \+ *lemma* category_theory.is_coseparator.def
- \+ *def* category_theory.is_coseparator
- \+ *lemma* category_theory.is_coseparator_def
- \+ *lemma* category_theory.is_coseparator_iff_faithful_yoneda_obj
- \+ *lemma* category_theory.is_coseparator_op_iff
- \+ *lemma* category_theory.is_coseparator_unop_iff
- \+ *lemma* category_theory.is_cospearator.is_codetector
- \+ *lemma* category_theory.is_detecting.is_separating
- \+ *lemma* category_theory.is_detecting.mono
- \+ *def* category_theory.is_detecting
- \+ *lemma* category_theory.is_detecting_empty_of_groupoid
- \+ *lemma* category_theory.is_detecting_iff_is_separating
- \+ *lemma* category_theory.is_detecting_op_iff
- \+ *lemma* category_theory.is_detecting_unop_iff
- \+ *lemma* category_theory.is_detector.def
- \+ *lemma* category_theory.is_detector.is_separator
- \+ *def* category_theory.is_detector
- \+ *lemma* category_theory.is_detector_def
- \+ *lemma* category_theory.is_detector_iff_reflects_isomorphisms_coyoneda_obj
- \+ *lemma* category_theory.is_detector_op_iff
- \+ *lemma* category_theory.is_detector_unop_iff
- \+ *lemma* category_theory.is_separating.is_detecting
- \+ *lemma* category_theory.is_separating.mono
- \+ *def* category_theory.is_separating
- \+ *lemma* category_theory.is_separating_empty_of_thin
- \+ *lemma* category_theory.is_separating_op_iff
- \+ *lemma* category_theory.is_separating_unop_iff
- \+ *lemma* category_theory.is_separator.def
- \+ *lemma* category_theory.is_separator.is_detector
- \+ *def* category_theory.is_separator
- \+ *lemma* category_theory.is_separator_def
- \+ *lemma* category_theory.is_separator_iff_faithful_coyoneda_obj
- \+ *lemma* category_theory.is_separator_op_iff
- \+ *lemma* category_theory.is_separator_unop_iff
- \+ *lemma* category_theory.thin_of_is_coseparating_empty
- \+ *lemma* category_theory.thin_of_is_separating_empty

Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/opposites.lean
- \+ *lemma* category_theory.is_iso_op_iff
- \+ *lemma* category_theory.is_iso_unop_iff
- \+/\- *lemma* category_theory.op_inv
- \+ *lemma* category_theory.unop_inv



## [2022-02-15 19:04:10](https://github.com/leanprover-community/mathlib/commit/ff2c9dc)
feat(combinatorics/simple_graph/connectivity): add functions to split walks and to create paths ([#11095](https://github.com/leanprover-community/mathlib/pull/11095))
This is chunk 3 of [#8737](https://github.com/leanprover-community/mathlib/pull/8737). Introduces `take_until` and `drop_until` to split walks at a vertex, `rotate` to rotate cycles, and `to_path` to remove internal redundancy from a walk to create a path with the same endpoints.
This also defines a bundled `path` type for `is_path` since `G.path u v` is a useful type.
#### Estimated changes
Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *abbreviation* simple_graph.path
- \+ *def* simple_graph.walk.bypass
- \+ *lemma* simple_graph.walk.bypass_is_path
- \+ *lemma* simple_graph.walk.count_edges_take_until_le_one
- \+ *lemma* simple_graph.walk.count_support_take_until_eq_one
- \+ *def* simple_graph.walk.drop_until
- \+ *lemma* simple_graph.walk.edges_bypass_subset
- \+ *lemma* simple_graph.walk.edges_drop_until_subset
- \+ *lemma* simple_graph.walk.edges_take_until_subset
- \+ *lemma* simple_graph.walk.edges_to_path_subset
- \+ *lemma* simple_graph.walk.is_circuit.rotate
- \+ *lemma* simple_graph.walk.is_cycle.rotate
- \+ *lemma* simple_graph.walk.is_path.drop_until
- \+ *lemma* simple_graph.walk.is_path.take_until
- \+ *lemma* simple_graph.walk.is_trail.drop_until
- \+ *lemma* simple_graph.walk.is_trail.rotate
- \+ *lemma* simple_graph.walk.is_trail.take_until
- \+ *lemma* simple_graph.walk.length_bypass_le
- \+ *lemma* simple_graph.walk.length_drop_until_le
- \+ *lemma* simple_graph.walk.length_take_until_le
- \+ *lemma* simple_graph.walk.mem_support_nil_iff
- \+ *def* simple_graph.walk.rotate
- \+ *lemma* simple_graph.walk.rotate_edges
- \+ *lemma* simple_graph.walk.support_bypass_subset
- \+ *lemma* simple_graph.walk.support_drop_until_subset
- \+ *lemma* simple_graph.walk.support_rotate
- \+ *lemma* simple_graph.walk.support_take_until_subset
- \+ *lemma* simple_graph.walk.support_to_path_subset
- \+ *lemma* simple_graph.walk.take_spec
- \+ *def* simple_graph.walk.take_until
- \+ *def* simple_graph.walk.to_path



## [2022-02-15 17:47:31](https://github.com/leanprover-community/mathlib/commit/5027b28)
move(data/nat/choose/bounds): Move from `combinatorics.choose.bounds` ([#12051](https://github.com/leanprover-community/mathlib/pull/12051))
This file fits better with all other files about `nat.choose`. My bad for originally proposing it goes alone under `combinatorics`.
#### Estimated changes
Renamed src/combinatorics/choose/bounds.lean to src/data/nat/choose/bounds.lean




## [2022-02-15 17:47:30](https://github.com/leanprover-community/mathlib/commit/52aaf17)
feat(data/{list,multiset,finset}/nat_antidiagonal): add lemmas to remove elements from head and tail of antidiagonal ([#12028](https://github.com/leanprover-community/mathlib/pull/12028))
Also lowered `finset.nat.map_swap_antidiagonal` down to `list` through `multiset`.
#### Estimated changes
Modified src/data/finset/nat_antidiagonal.lean
- \+ *lemma* finset.nat.antidiagonal_succ'
- \+ *lemma* finset.nat.antidiagonal_succ_succ'

Modified src/data/list/nat_antidiagonal.lean
- \+ *lemma* list.nat.antidiagonal_succ'
- \+ *lemma* list.nat.antidiagonal_succ_succ'
- \+ *lemma* list.nat.map_swap_antidiagonal

Modified src/data/multiset/nat_antidiagonal.lean
- \+ *lemma* multiset.nat.antidiagonal_succ'
- \+ *lemma* multiset.nat.antidiagonal_succ_succ'
- \+ *lemma* multiset.nat.map_swap_antidiagonal



## [2022-02-15 15:53:29](https://github.com/leanprover-community/mathlib/commit/c0c673a)
feat(data/equiv,logic/embedding): add `can_lift` instances ([#12049](https://github.com/leanprover-community/mathlib/pull/12049))
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+/\- *lemma* equiv.of_bijective_apply_symm_apply
- \+/\- *lemma* equiv.of_bijective_symm_apply_apply

Modified src/logic/embedding.lean




## [2022-02-15 15:52:59](https://github.com/leanprover-community/mathlib/commit/c686fcc)
feat(analysis/specific_limits): add `tendsto_zero_smul_of_tendsto_zero_of_bounded` ([#12039](https://github.com/leanprover-community/mathlib/pull/12039))
#### Estimated changes
Modified src/analysis/specific_limits.lean
- \+ *lemma* normed_field.tendsto_zero_smul_of_tendsto_zero_of_bounded



## [2022-02-15 15:52:56](https://github.com/leanprover-community/mathlib/commit/6e64492)
feat(ring_theory/multiplicity): Equality of `factorization`, `multiplicity`, and `padic_val_nat` ([#12033](https://github.com/leanprover-community/mathlib/pull/12033))
Proves `multiplicity_eq_factorization : multiplicity p n = n.factorization p` for prime `p` and `n ≠ 0` and uses this to golf the proof of `padic_val_nat_eq_factorization : padic_val_nat p n = n.factorization p`.
#### Estimated changes
Modified src/number_theory/padics/padic_norm.lean
- \+/\- *lemma* padic_val_nat_eq_factorization

Modified src/ring_theory/multiplicity.lean
- \+ *lemma* multiplicity_eq_factorization



## [2022-02-15 15:52:53](https://github.com/leanprover-community/mathlib/commit/9307f5b)
feat(topology/order/lattice): add a consequence of the continuity of sup/inf ([#12003](https://github.com/leanprover-community/mathlib/pull/12003))
Prove this lemma and its `inf` counterpart:
```lean
lemma filter.tendsto.sup_right_nhds {ι β} [topological_space β] [has_sup β] [has_continuous_sup β]
  {l : filter ι} {f g : ι → β} {x y : β} (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (f ⊔ g) l (𝓝 (x ⊔ y))
```
The name is `sup_right_nhds` because `sup` already exists, and is about a supremum over the filters on the left in the tendsto.
The proofs of `tendsto_prod_iff'` and `prod.tendsto_iff` were written by  Patrick Massot.
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.tendsto_prod_iff'

Modified src/topology/constructions.lean
- \+ *lemma* prod.tendsto_iff

Modified src/topology/order/lattice.lean
- \+ *lemma* filter.tendsto.inf_right_nhds'
- \+ *lemma* filter.tendsto.inf_right_nhds
- \+ *lemma* filter.tendsto.sup_right_nhds'
- \+ *lemma* filter.tendsto.sup_right_nhds



## [2022-02-15 15:52:52](https://github.com/leanprover-community/mathlib/commit/60b77a7)
feat(analysis/special_functions/complex/circle): `real.angle.exp_map_circle` lemmas ([#11969](https://github.com/leanprover-community/mathlib/pull/11969))
Add four more `simp` lemmas about `real.angle.exp_map_circle`:
`exp_map_circle_zero`, `exp_map_circle_neg`, `exp_map_circle_add` and
`arg_exp_map_circle`.
#### Estimated changes
Modified src/analysis/special_functions/complex/circle.lean
- \+ *lemma* real.angle.arg_exp_map_circle
- \+ *lemma* real.angle.exp_map_circle_add
- \+ *lemma* real.angle.exp_map_circle_neg
- \+ *lemma* real.angle.exp_map_circle_zero



## [2022-02-15 15:52:49](https://github.com/leanprover-community/mathlib/commit/0c33309)
feat(number_theory/zsqrtd/basic): add some lemmas ([#11964](https://github.com/leanprover-community/mathlib/pull/11964))
#### Estimated changes
Modified src/number_theory/zsqrtd/basic.lean
- \+ *lemma* zsqrtd.coe_int_dvd_coe_int
- \+/\- *lemma* zsqrtd.coe_int_dvd_iff
- \+ *lemma* zsqrtd.coprime_of_dvd_coprime
- \+ *lemma* zsqrtd.exists_coprime_of_gcd_pos
- \+ *lemma* zsqrtd.gcd_eq_zero_iff
- \+ *lemma* zsqrtd.gcd_pos_iff
- \+ *theorem* zsqrtd.smul_im
- \+ *theorem* zsqrtd.smul_re



## [2022-02-15 15:52:48](https://github.com/leanprover-community/mathlib/commit/3d1354c)
feat(set_theory/ordinal_arithmetic): Suprema of functions with the same range are equal ([#11910](https://github.com/leanprover-community/mathlib/pull/11910))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.blsub_eq_of_brange_eq
- \+ *theorem* ordinal.blsub_le_of_brange_subset
- \+ *def* ordinal.brange
- \+ *theorem* ordinal.brange_bfamily_of_family'
- \+ *theorem* ordinal.brange_bfamily_of_family
- \+ *theorem* ordinal.bsup_eq_of_brange_eq
- \+ *theorem* ordinal.bsup_le_of_brange_subset
- \+ *theorem* ordinal.lsub_eq_of_range_eq
- \+ *theorem* ordinal.lsub_le_of_range_subset
- \+ *theorem* ordinal.mem_brange
- \+ *theorem* ordinal.mem_brange_self
- \+ *theorem* ordinal.range_family_of_bfamily'
- \+ *theorem* ordinal.range_family_of_bfamily
- \+ *theorem* ordinal.sup_eq_of_range_eq
- \+/\- *theorem* ordinal.sup_eq_sup
- \+ *theorem* ordinal.sup_le_of_range_subset



## [2022-02-15 15:52:46](https://github.com/leanprover-community/mathlib/commit/721bace)
refactor(set_theory/ordinal_arithmetic): `omin` → `Inf` ([#11867](https://github.com/leanprover-community/mathlib/pull/11867))
We remove the redundant `omin` in favor of `Inf`. We also introduce a `conditionally_complete_linear_order_bot` instance on `cardinals`, and golf a particularly messy proof.
#### Estimated changes
Modified src/set_theory/cardinal.lean
- \+ *def* cardinal.min
- \+ *def* cardinal.out_mk_equiv
- \+ *def* cardinal.powerlt
- \+ *def* cardinal.succ
- \+ *def* cardinal.sup
- \+ *def* cardinal.to_enat
- \+ *def* cardinal.to_nat

Modified src/set_theory/cardinal_ordinal.lean
- \+/\- *theorem* cardinal.ord_aleph'_eq_enum_card
- \+/\- *theorem* cardinal.ord_aleph_eq_enum_card

Modified src/set_theory/game/nim.lean


Modified src/set_theory/ordinal.lean
- \- *lemma* ordinal.Inf_eq_omin
- \- *lemma* ordinal.Inf_mem
- \- *theorem* ordinal.le_omin
- \- *theorem* ordinal.not_lt_omin
- \- *def* ordinal.omin
- \- *theorem* ordinal.omin_le
- \- *theorem* ordinal.omin_mem

Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.blsub_le_enum_ord
- \+/\- *theorem* ordinal.deriv_eq_enum_fp
- \+/\- *lemma* ordinal.div_def
- \+ *theorem* ordinal.div_nonempty
- \+/\- *theorem* ordinal.div_zero
- \+/\- *def* ordinal.enum_ord.order_iso
- \+/\- *theorem* ordinal.enum_ord.strict_mono
- \+/\- *theorem* ordinal.enum_ord.surjective
- \+/\- *def* ordinal.enum_ord
- \- *lemma* ordinal.enum_ord_def'_H
- \+ *theorem* ordinal.enum_ord_def'_nonempty
- \- *lemma* ordinal.enum_ord_def_H
- \+ *lemma* ordinal.enum_ord_def_nonempty
- \+/\- *theorem* ordinal.enum_ord_mem
- \+/\- *theorem* ordinal.enum_ord_range
- \+ *theorem* ordinal.enum_ord_succ_le
- \+ *theorem* ordinal.enum_ord_zero
- \+ *theorem* ordinal.enum_ord_zero_le
- \+/\- *theorem* ordinal.eq_enum_ord
- \+/\- *theorem* ordinal.log_def
- \+ *theorem* ordinal.log_nonempty
- \+ *theorem* ordinal.sub_nonempty
- \+/\- *theorem* ordinal.succ_log_def
- \+/\- *def* ordinal.sup
- \+ *theorem* ordinal.sup_nonempty



## [2022-02-15 15:52:45](https://github.com/leanprover-community/mathlib/commit/9acc1d4)
feat(model_theory/finitely_generated): Finitely generated and countably generated (sub)structures ([#11857](https://github.com/leanprover-community/mathlib/pull/11857))
Defines `substructure.fg` and `Structure.fg` to indicate when (sub)structures are finitely generated
Defines `substructure.cg` and `Structure.cg` to indicate when (sub)structures are countably generated
#### Estimated changes
Added src/model_theory/finitely_generated.lean
- \+ *lemma* first_order.language.Structure.cg.map_of_surjective
- \+ *lemma* first_order.language.Structure.cg.range
- \+ *lemma* first_order.language.Structure.cg_def
- \+ *lemma* first_order.language.Structure.cg_iff
- \+ *lemma* first_order.language.Structure.fg.map_of_surjective
- \+ *lemma* first_order.language.Structure.fg.range
- \+ *lemma* first_order.language.Structure.fg_def
- \+ *lemma* first_order.language.Structure.fg_iff
- \+ *lemma* first_order.language.equiv.cg_iff
- \+ *lemma* first_order.language.equiv.fg_iff
- \+ *theorem* first_order.language.substructure.cg.map
- \+ *theorem* first_order.language.substructure.cg.of_map_embedding
- \+ *def* first_order.language.substructure.cg
- \+ *theorem* first_order.language.substructure.cg_bot
- \+ *theorem* first_order.language.substructure.cg_closure
- \+ *theorem* first_order.language.substructure.cg_closure_singleton
- \+ *theorem* first_order.language.substructure.cg_def
- \+ *lemma* first_order.language.substructure.cg_iff_Structure_cg
- \+ *lemma* first_order.language.substructure.cg_iff_empty_or_exists_nat_generating_family
- \+ *theorem* first_order.language.substructure.cg_sup
- \+ *theorem* first_order.language.substructure.fg.cg
- \+ *theorem* first_order.language.substructure.fg.map
- \+ *theorem* first_order.language.substructure.fg.of_map_embedding
- \+ *def* first_order.language.substructure.fg
- \+ *theorem* first_order.language.substructure.fg_bot
- \+ *theorem* first_order.language.substructure.fg_closure
- \+ *theorem* first_order.language.substructure.fg_closure_singleton
- \+ *theorem* first_order.language.substructure.fg_def
- \+ *lemma* first_order.language.substructure.fg_iff_Structure_fg
- \+ *lemma* first_order.language.substructure.fg_iff_exists_fin_generating_family
- \+ *theorem* first_order.language.substructure.fg_sup



## [2022-02-15 15:52:44](https://github.com/leanprover-community/mathlib/commit/41dd6d8)
feat(data/nat/modeq): add modeq and dvd lemmas from Apostol Chapter 5 ([#11787](https://github.com/leanprover-community/mathlib/pull/11787))
Various lemmas about `modeq` from Chapter 5 of Apostol (1976) Introduction to Analytic Number Theory:
* `mul_left_iff` and `mul_right_iff`: Apostol, Theorem 5.3
* `dvd_iff_of_modeq_of_dvd`: Apostol, Theorem 5.5
* `gcd_eq_of_modeq`: Apostol, Theorem 5.6
* `eq_of_modeq_of_abs_lt`: Apostol, Theorem 5.7
* `modeq_cancel_left_div_gcd`: Apostol, Theorem 5.4; plus other cancellation lemmas following from this.
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* int.eq_zero_of_abs_lt_dvd

Modified src/data/nat/modeq.lean
- \+ *lemma* nat.modeq.dvd_iff_of_modeq_of_dvd
- \+ *lemma* nat.modeq.eq_of_modeq_of_abs_lt
- \+ *lemma* nat.modeq.gcd_eq_of_modeq
- \+ *lemma* nat.modeq.modeq_cancel_left_div_gcd'
- \+ *lemma* nat.modeq.modeq_cancel_left_div_gcd
- \+ *lemma* nat.modeq.modeq_cancel_left_of_coprime
- \+ *lemma* nat.modeq.modeq_cancel_right_div_gcd'
- \+ *lemma* nat.modeq.modeq_cancel_right_div_gcd
- \+ *lemma* nat.modeq.modeq_cancel_right_of_coprime



## [2022-02-15 14:39:56](https://github.com/leanprover-community/mathlib/commit/b0508f3)
feat(topology/uniform/uniform_embedding): a sum of two complete spaces is complete ([#11971](https://github.com/leanprover-community/mathlib/pull/11971))
#### Estimated changes
Modified src/topology/uniform_space/basic.lean
- \+ *lemma* discrete_topology_of_discrete_uniformity
- \+/\- *def* uniform_space.replace_topology

Modified src/topology/uniform_space/uniform_embedding.lean
- \+ *def* embedding.comap_uniform_space
- \+ *lemma* embedding.to_uniform_embedding
- \+ *theorem* uniform_embedding_inl
- \+ *theorem* uniform_embedding_inr



## [2022-02-15 14:39:55](https://github.com/leanprover-community/mathlib/commit/77ca1ed)
feat(order/category/Lattice): The category of lattices ([#11968](https://github.com/leanprover-community/mathlib/pull/11968))
Define `Lattice`, the category of lattices with lattice homs.
#### Estimated changes
Modified src/category_theory/concrete_category/bundled_hom.lean


Added src/order/category/Lattice.lean
- \+ *def* Lattice.dual
- \+ *def* Lattice.dual_equiv
- \+ *def* Lattice.iso.mk
- \+ *def* Lattice.of
- \+ *def* Lattice
- \+ *lemma* Lattice_dual_comp_forget_to_PartialOrder

Modified src/order/category/LinearOrder.lean
- \+ *def* LinearOrder.dual
- \- *def* LinearOrder.to_dual
- \+ *lemma* LinearOrder_dual_comp_forget_to_Lattice
- \- *lemma* LinearOrder_dual_equiv_comp_forget_to_PartialOrder

Modified src/order/hom/lattice.lean




## [2022-02-15 12:59:13](https://github.com/leanprover-community/mathlib/commit/5bcffd9)
feat(number_theory/cyclotomic/zeta): add lemmas ([#11786](https://github.com/leanprover-community/mathlib/pull/11786))
Lemmas about the norm of `ζ - 1`.
From flt-regular.
- [x] depends on: [#11941](https://github.com/leanprover-community/mathlib/pull/11941)
#### Estimated changes
Modified src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* is_cyclotomic_extension.is_prime_pow.norm_zeta_sub_one
- \+ *lemma* is_cyclotomic_extension.norm_zeta_eq_one
- \+ *lemma* is_cyclotomic_extension.prime_ne_two.norm_zeta_sub_one
- \+ *lemma* is_cyclotomic_extension.prime_ne_two_pow.norm_zeta_sub_one
- \+ *lemma* is_cyclotomic_extension.two_pow.norm_zeta_sub_one
- \+ *lemma* is_primitive_root.prime_ne_two_pow.sub_one_norm
- \+ *lemma* is_primitive_root.sub_one_norm.is_prime_pow
- \+ *lemma* is_primitive_root.sub_one_norm.pow_two
- \+ *lemma* is_primitive_root.sub_one_norm.prime
- \+/\- *lemma* is_primitive_root.sub_one_norm_eq_eval_cyclotomic



## [2022-02-15 12:59:12](https://github.com/leanprover-community/mathlib/commit/a2d7b55)
feat(order/complete_boolean_algebra): Frames ([#11709](https://github.com/leanprover-community/mathlib/pull/11709))
Define the order theoretic `order.frame` and `order.coframe` and insert them between `complete_lattice` and `complete_distrib_lattice`.
#### Estimated changes
Modified docs/references.bib


Modified src/data/set/prod.lean
- \+ *lemma* set.image_prod_mk_subset_prod_left
- \+ *lemma* set.image_prod_mk_subset_prod_right

Modified src/order/complete_boolean_algebra.lean
- \+ *lemma* Sup_inf_Sup
- \- *theorem* Sup_inf_Sup
- \+ *lemma* Sup_inf_eq
- \- *theorem* Sup_inf_eq
- \+ *lemma* binfi_sup_binfi
- \+ *lemma* bsupr_inf_bsupr
- \+ *lemma* bsupr_inf_eq
- \- *theorem* bsupr_inf_eq
- \+ *lemma* inf_Sup_eq
- \- *theorem* inf_Sup_eq
- \+ *lemma* inf_bsupr_eq
- \- *theorem* inf_bsupr_eq
- \+ *lemma* inf_supr_eq
- \- *theorem* inf_supr_eq
- \+ *lemma* infi_sup_infi
- \+ *lemma* supr_inf_eq
- \- *theorem* supr_inf_eq
- \+ *lemma* supr_inf_supr

Modified src/order/copy.lean
- \+ *def* coframe.copy
- \+ *def* frame.copy



## [2022-02-15 12:30:09](https://github.com/leanprover-community/mathlib/commit/440e6b3)
feat(topology/algebra/module/locally_convex): define locally convex spaces ([#11859](https://github.com/leanprover-community/mathlib/pull/11859))
#### Estimated changes
Modified src/analysis/seminorm.lean
- \+ *lemma* normed_space.to_locally_convex_space'
- \+ *lemma* seminorm.with_seminorms.to_locally_convex_space

Added src/topology/algebra/module/locally_convex.lean
- \+ *lemma* locally_convex_space.convex_basis_zero
- \+ *lemma* locally_convex_space.of_bases
- \+ *lemma* locally_convex_space.of_basis_zero
- \+ *lemma* locally_convex_space_iff
- \+ *lemma* locally_convex_space_iff_exists_convex_subset
- \+ *lemma* locally_convex_space_iff_exists_convex_subset_zero
- \+ *lemma* locally_convex_space_iff_zero



## [2022-02-15 11:12:39](https://github.com/leanprover-community/mathlib/commit/c5578f9)
feat(group_theory/nilpotent): products of nilpotent groups ([#11827](https://github.com/leanprover-community/mathlib/pull/11827))
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* lower_central_series_prod
- \+ *lemma* nilpotency_class_prod



## [2022-02-15 08:27:11](https://github.com/leanprover-community/mathlib/commit/f12b3d9)
feat(topology/algebra): weaken typeclasses to only require `has_continuous_const_smul` ([#11995](https://github.com/leanprover-community/mathlib/pull/11995))
This changes all the continuity-based `const_smul` lemmas to only require `has_continuous_const_smul` rather than `has_continuous_smul`. It does not attempt to  propagate the changes out of this file.
Four new instances are added in `const_mul_action.lean` for `has_continuous_const_smul`: `mul_opposite`, `prod`, `pi`, and `units`; all copied from the corresponding `has_continuous_smul` instance in `mul_action.lean`.
Presumably these lemmas existed before this typeclass did.
At any rate, the connection was less obvious until the rename a few days ago in [#11940](https://github.com/leanprover-community/mathlib/pull/11940).
#### Estimated changes
Modified src/topology/algebra/const_mul_action.lean
- \+ *lemma* continuous.const_smul
- \+ *lemma* continuous_at.const_smul
- \+ *lemma* continuous_at_const_smul_iff
- \+ *lemma* continuous_at_const_smul_iff₀
- \+ *lemma* continuous_const_smul_iff
- \+ *lemma* continuous_const_smul_iff₀
- \+ *lemma* continuous_on.const_smul
- \+ *lemma* continuous_on_const_smul_iff
- \+ *lemma* continuous_on_const_smul_iff₀
- \+ *lemma* continuous_within_at.const_smul
- \+ *lemma* continuous_within_at_const_smul_iff
- \+ *lemma* continuous_within_at_const_smul_iff₀
- \+ *lemma* filter.tendsto.const_smul
- \+/\- *def* homeomorph.smul
- \- *def* homeomorph.vadd
- \+ *lemma* interior_smul₀
- \+ *lemma* is_closed.smul
- \+ *lemma* is_closed_map_smul
- \+ *lemma* is_closed_map_smul_of_ne_zero
- \+ *lemma* is_closed_map_smul₀
- \+ *lemma* is_open.smul
- \+ *lemma* is_open.smul₀
- \+ *lemma* is_open_map_smul
- \+ *lemma* is_open_map_smul₀
- \+ *lemma* is_unit.continuous_at_const_smul_iff
- \+ *lemma* is_unit.continuous_const_smul_iff
- \+ *lemma* is_unit.continuous_on_const_smul_iff
- \+ *lemma* is_unit.continuous_within_at_const_smul_iff
- \+ *lemma* is_unit.is_closed_map_smul
- \+ *lemma* is_unit.is_open_map_smul
- \+ *lemma* is_unit.tendsto_const_smul_iff
- \+ *lemma* smul_closure_orbit_subset
- \+ *lemma* smul_closure_subset
- \+ *lemma* tendsto_const_smul_iff
- \+ *lemma* tendsto_const_smul_iff₀

Modified src/topology/algebra/mul_action.lean
- \- *lemma* continuous.const_smul
- \- *lemma* continuous_at.const_smul
- \- *lemma* continuous_at_const_smul_iff
- \- *lemma* continuous_at_const_smul_iff₀
- \- *lemma* continuous_const_smul_iff
- \- *lemma* continuous_const_smul_iff₀
- \- *lemma* continuous_on.const_smul
- \- *lemma* continuous_on_const_smul_iff
- \- *lemma* continuous_on_const_smul_iff₀
- \- *lemma* continuous_within_at.const_smul
- \- *lemma* continuous_within_at_const_smul_iff
- \- *lemma* continuous_within_at_const_smul_iff₀
- \- *lemma* filter.tendsto.const_smul
- \- *lemma* interior_smul₀
- \- *lemma* is_closed.smul
- \- *lemma* is_closed_map_smul
- \- *lemma* is_closed_map_smul_of_ne_zero
- \- *lemma* is_closed_map_smul₀
- \- *lemma* is_open.smul
- \- *lemma* is_open.smul₀
- \- *lemma* is_open_map_smul
- \- *lemma* is_open_map_smul₀
- \- *lemma* is_unit.continuous_at_const_smul_iff
- \- *lemma* is_unit.continuous_const_smul_iff
- \- *lemma* is_unit.continuous_on_const_smul_iff
- \- *lemma* is_unit.continuous_within_at_const_smul_iff
- \- *lemma* is_unit.is_closed_map_smul
- \- *lemma* is_unit.is_open_map_smul
- \- *lemma* is_unit.tendsto_const_smul_iff
- \- *lemma* smul_closure_orbit_subset
- \- *lemma* smul_closure_subset
- \- *lemma* tendsto_const_smul_iff
- \- *lemma* tendsto_const_smul_iff₀



## [2022-02-15 06:34:35](https://github.com/leanprover-community/mathlib/commit/f1334b9)
chore(category_theory/triangulated/rotate): optimizing some proofs ([#12031](https://github.com/leanprover-community/mathlib/pull/12031))
Removes some non-terminal `simp`s; replaces some `simp`s by `simp only [...]` and `rw`.
Compilation time dropped from 1m40s to 1m05s on my machine.
#### Estimated changes
Modified src/category_theory/triangulated/rotate.lean




## [2022-02-15 05:21:51](https://github.com/leanprover-community/mathlib/commit/4c76eac)
chore(probability_theory/*): Rename folder  ([#11989](https://github.com/leanprover-community/mathlib/pull/11989))
Rename `probability_theory` to `probability`.
#### Estimated changes
Renamed src/probability_theory/density.lean to src/probability/density.lean


Renamed src/probability_theory/independence.lean to src/probability/independence.lean


Renamed src/probability_theory/integration.lean to src/probability/integration.lean


Renamed src/probability_theory/martingale.lean to src/probability/martingale.lean


Renamed src/probability_theory/notation.lean to src/probability/notation.lean


Renamed src/probability_theory/stopping.lean to src/probability/stopping.lean




## [2022-02-15 02:51:23](https://github.com/leanprover-community/mathlib/commit/430faa9)
chore(scripts): update nolints.txt ([#12048](https://github.com/leanprover-community/mathlib/pull/12048))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2022-02-15 02:21:36](https://github.com/leanprover-community/mathlib/commit/a1283d0)
feat(analysis/inner_product_space/adjoint): `is_self_adjoint_iff_eq_a… ([#12047](https://github.com/leanprover-community/mathlib/pull/12047))
…djoint`
A self-adjoint linear map is equal to its adjoint.
#### Estimated changes
Modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* linear_map.is_self_adjoint_iff_eq_adjoint



## [2022-02-15 01:27:49](https://github.com/leanprover-community/mathlib/commit/92ac8ff)
feat(analysis/special_functions/complex/arg): `arg_coe_angle_eq_iff` ([#12017](https://github.com/leanprover-community/mathlib/pull/12017))
Add a lemma that `arg` of two numbers coerced to `real.angle` is equal
if and only if `arg` is equal.
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.arg_coe_angle_eq_iff



## [2022-02-14 23:41:27](https://github.com/leanprover-community/mathlib/commit/5dc720d)
chore(number_theory/padics/padic_norm): golf `prod_pow_prime_padic_val_nat` ([#12034](https://github.com/leanprover-community/mathlib/pull/12034))
A todo comment said "this proof can probably be golfed with `factorization` stuff"; it turns out that indeed it can be. :)
#### Estimated changes
Modified src/number_theory/padics/padic_norm.lean




## [2022-02-14 21:58:15](https://github.com/leanprover-community/mathlib/commit/f9bac45)
chore(category_theory/linear/yoneda): Removing some slow uses of `obviously` ([#11979](https://github.com/leanprover-community/mathlib/pull/11979))
Providing explicit proofs for `map_id'` and `map_comp'` rather than leaving them for `obviously` (and hence `tidy`) to fill in.
Suggested by Kevin Buzzard in [this Zulip comment](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60tidy.60.20in.20mathlib.20proofs/near/271474418).
(These are temporary changes until `obviously` can be tweaked to do this more quickly)
#### Estimated changes
Modified src/category_theory/linear/yoneda.lean




## [2022-02-14 21:58:14](https://github.com/leanprover-community/mathlib/commit/efdce09)
refactor(topology/constructions): turn `cofinite_topology` into a type synonym ([#11967](https://github.com/leanprover-community/mathlib/pull/11967))
Instead of `cofinite_topology α : topological_space α`, define
`cofinite_topology α := α` with an instance
`topological_space (cofinite_topology α) := (old definition)`.
This way we can talk about cofinite topology without using `@` all
over the place.
Also move `homeo_of_equiv_compact_to_t2.t1_counterexample` to
`topology.alexandroff` and prove it for `alexandroff ℕ` and
`cofinite_topology (alexandroff ℕ)`.
#### Estimated changes
Modified src/topology/alexandroff.lean
- \+ *lemma* alexandroff.not_continuous_cofinite_topology_of_symm
- \+ *lemma* continuous.homeo_of_equiv_compact_to_t2.t1_counterexample

Modified src/topology/constructions.lean
- \+ *lemma* cofinite_topology.is_closed_iff
- \+ *lemma* cofinite_topology.is_open_iff'
- \+ *lemma* cofinite_topology.is_open_iff
- \+ *lemma* cofinite_topology.mem_nhds_iff
- \+ *lemma* cofinite_topology.nhds_eq
- \+ *def* cofinite_topology.of
- \+/\- *def* cofinite_topology
- \- *lemma* mem_nhds_cofinite
- \- *lemma* nhds_cofinite

Modified src/topology/homeomorph.lean
- \- *lemma* continuous.homeo_of_equiv_compact_to_t2.t1_counterexample

Modified src/topology/separation.lean
- \+ *lemma* cofinite_topology.continuous_of
- \+ *lemma* t1_space_iff_continuous_cofinite_of
- \- *lemma* t1_space_iff_le_cofinite
- \+/\- *lemma* t1_space_tfae



## [2022-02-14 21:58:13](https://github.com/leanprover-community/mathlib/commit/ec11e5f)
feat(algebra/covariant_and_contravariant): covariance and monotonicity ([#11815](https://github.com/leanprover-community/mathlib/pull/11815))
Some simple lemmas about monotonicity and covariant operators. Proves things like `monotone f → monotone (λ n, f (3 + n))` by library search.
#### Estimated changes
Modified src/algebra/covariant_and_contravariant.lean
- \+ *lemma* antitone.covariant_of_const'
- \+ *lemma* antitone.covariant_of_const
- \+ *lemma* covariant.monotone_of_const
- \+ *lemma* monotone.covariant_of_const'
- \+ *lemma* monotone.covariant_of_const



## [2022-02-14 20:17:46](https://github.com/leanprover-community/mathlib/commit/4ba8334)
doc(number_theory/cyclotomic/gal): fix typo ([#12038](https://github.com/leanprover-community/mathlib/pull/12038))
#### Estimated changes
Modified src/number_theory/cyclotomic/gal.lean




## [2022-02-14 20:17:44](https://github.com/leanprover-community/mathlib/commit/263833c)
feat(data/nat/factorization): add `le_of_mem_factorization` ([#12032](https://github.com/leanprover-community/mathlib/pull/12032))
`le_of_mem_factors`: every factor of `n` is `≤ n`
`le_of_mem_factorization`: everything in `n.factorization.support` is `≤ n`
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.le_of_mem_factorization

Modified src/data/nat/prime.lean
- \+ *lemma* nat.le_of_mem_factors



## [2022-02-14 20:17:42](https://github.com/leanprover-community/mathlib/commit/1a3c069)
chore(data/equiv/set): more lemmas about prod ([#12022](https://github.com/leanprover-community/mathlib/pull/12022))
Note we don't need the `symm` lemmas for `prod.comm`, since `prod.comm` is involutive
#### Estimated changes
Modified src/data/equiv/set.lean
- \+ *lemma* equiv.prod_assoc_image
- \+ *lemma* equiv.prod_assoc_symm_image
- \+ *lemma* equiv.prod_assoc_symm_preimage
- \+ *lemma* equiv.prod_comm_image
- \+ *lemma* equiv.prod_comm_preimage



## [2022-02-14 18:40:35](https://github.com/leanprover-community/mathlib/commit/583ea58)
feat(data/list/big_operators): add `list.prod_map_mul` ([#12029](https://github.com/leanprover-community/mathlib/pull/12029))
This is an analogue of the corresponding lemma `multiset.prod_map_mul`.
#### Estimated changes
Modified src/data/list/big_operators.lean
- \+ *lemma* list.prod_map_mul



## [2022-02-14 14:46:55](https://github.com/leanprover-community/mathlib/commit/199e8ca)
feat(algebra/star/self_adjoint): generalize scalar action instances ([#12021](https://github.com/leanprover-community/mathlib/pull/12021))
The `distrib_mul_action` instance did not require the underlying space to be a module.
#### Estimated changes
Modified src/algebra/star/self_adjoint.lean
- \+/\- *lemma* self_adjoint.coe_smul



## [2022-02-14 14:46:54](https://github.com/leanprover-community/mathlib/commit/5166aaa)
feat(analysis/normed_space/linear_isometry): `trans_one`, `one_trans`, `refl_mul`, `mul_refl` ([#12016](https://github.com/leanprover-community/mathlib/pull/12016))
Add variants of the `linear_isometry_equiv.trans_refl` and
`linear_isometry_equiv.refl_trans` `simp` lemmas where `refl` is given
as `1`.  (`one_def` isn't a `simp` lemma in either direction, since
either `refl` or `1` could be the appropriate simplest form depending
on the context, but it seems clear these expressions involving `trans`
with `1` are still appropriate to simplify.)
Also add corresponding `refl_mul` and `mul_refl`.
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* linear_isometry_equiv.mul_refl
- \+ *lemma* linear_isometry_equiv.one_trans
- \+ *lemma* linear_isometry_equiv.refl_mul
- \+ *lemma* linear_isometry_equiv.trans_one



## [2022-02-14 12:13:11](https://github.com/leanprover-community/mathlib/commit/d33792e)
feat(data/nat/factorization): add lemma `factorization_gcd` ([#11605](https://github.com/leanprover-community/mathlib/pull/11605))
For positive `a` and `b`, `(gcd a b).factorization = a.factorization ⊓ b.factorization`; i.e. the power of prime `p` in `gcd a b` is the minimum of its powers in `a` and `b`.  This is Theorem 1.12 in Apostol (1976) Introduction to Analytic Number Theory.
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.factorization_gcd



## [2022-02-14 10:22:27](https://github.com/leanprover-community/mathlib/commit/132ea05)
docs(computability/partrec_code): add docs ([#11929](https://github.com/leanprover-community/mathlib/pull/11929))
#### Estimated changes
Modified src/computability/partrec_code.lean




## [2022-02-14 10:22:26](https://github.com/leanprover-community/mathlib/commit/dce5dd4)
feat(order/well_founded, set_theory/ordinal_arithmetic): `eq_strict_mono_iff_eq_range` ([#11882](https://github.com/leanprover-community/mathlib/pull/11882))
Two strict monotonic functions with well-founded domains are equal iff their ranges are. We use this to golf `eq_enum_ord`.
#### Estimated changes
Modified src/order/well_founded.lean
- \+ *theorem* well_founded.eq_strict_mono_iff_eq_range

Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.eq_enum_ord



## [2022-02-14 08:41:45](https://github.com/leanprover-community/mathlib/commit/a87d431)
feat(topology/algebra): add `@[to_additive]` to some lemmas ([#12018](https://github.com/leanprover-community/mathlib/pull/12018))
* rename `embed_product` to `units.embed_product`, add `add_units.embed_product`;
* add additive versions to lemmas about topology on `units M`;
* add `add_opposite.topological_space` and `add_opposite.has_continuous_add`;
* move `continuous_op` and `continuous_unop` to the `mul_opposite` namespace, add additive versions.
#### Estimated changes
Modified src/algebra/group/prod.lean
- \- *def* embed_product
- \+ *def* units.embed_product

Modified src/topology/algebra/group.lean


Modified src/topology/algebra/monoid.lean
- \- *lemma* continuous_op
- \- *lemma* continuous_unop
- \+ *lemma* mul_opposite.continuous_op
- \+ *lemma* mul_opposite.continuous_unop
- \+/\- *lemma* units.continuous_coe
- \+/\- *lemma* units.continuous_embed_product

Modified src/topology/algebra/mul_action.lean




## [2022-02-14 08:04:35](https://github.com/leanprover-community/mathlib/commit/2ceacc1)
feat(measure_theory/measure): more lemmas about `null_measurable_set`s ([#12019](https://github.com/leanprover-community/mathlib/pull/12019))
#### Estimated changes
Modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* measure_theory.is_fundamental_domain.null_measurable_set_smul

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.measure.restrict_Union_ae
- \+ *lemma* measure_theory.measure.restrict_apply₀'
- \+ *lemma* measure_theory.measure.restrict_restrict₀'
- \+ *lemma* measure_theory.measure.restrict_restrict₀



## [2022-02-14 07:20:08](https://github.com/leanprover-community/mathlib/commit/25ebf41)
chore(analysis): move some code ([#12008](https://github.com/leanprover-community/mathlib/pull/12008))
Move the code that doesn't rely on `normed_space` from
`analysis.normed_space.add_torsor` to
`analysis.normed.group.add_torsor`.
#### Estimated changes
Added src/analysis/normed/group/add_torsor.lean
- \+ *lemma* continuous.vsub
- \+ *lemma* continuous_at.vsub
- \+ *lemma* continuous_vsub
- \+ *lemma* continuous_within_at.vsub
- \+ *lemma* dist_eq_norm_vsub
- \+ *lemma* dist_vadd_cancel_left
- \+ *lemma* dist_vadd_cancel_right
- \+ *lemma* dist_vadd_left
- \+ *lemma* dist_vadd_right
- \+ *lemma* dist_vadd_vadd_le
- \+ *lemma* dist_vsub_cancel_left
- \+ *lemma* dist_vsub_cancel_right
- \+ *lemma* dist_vsub_vsub_le
- \+ *lemma* edist_vadd_vadd_le
- \+ *lemma* edist_vsub_vsub_le
- \+ *lemma* filter.tendsto.line_map
- \+ *lemma* filter.tendsto.midpoint
- \+ *lemma* filter.tendsto.vsub
- \+ *def* isometric.const_vadd
- \+ *def* isometric.const_vsub
- \+ *def* isometric.vadd_const
- \+ *lemma* lipschitz_with.vadd
- \+ *lemma* lipschitz_with.vsub
- \+ *def* metric_space_of_normed_group_of_add_torsor
- \+ *lemma* nndist_vadd_vadd_le
- \+ *lemma* nndist_vsub_vsub_le
- \+ *def* pseudo_metric_space_of_normed_group_of_add_torsor
- \+ *lemma* uniform_continuous_vadd
- \+ *lemma* uniform_continuous_vsub
- \+ *lemma* vadd_ball
- \+ *lemma* vadd_closed_ball
- \+ *lemma* vadd_sphere

Modified src/analysis/normed_space/add_torsor.lean
- \- *lemma* continuous.vsub
- \- *lemma* continuous_at.vsub
- \- *lemma* continuous_vsub
- \- *lemma* continuous_within_at.vsub
- \- *lemma* dist_eq_norm_vsub
- \- *lemma* dist_vadd_cancel_left
- \- *lemma* dist_vadd_cancel_right
- \- *lemma* dist_vadd_left
- \- *lemma* dist_vadd_right
- \- *lemma* dist_vadd_vadd_le
- \- *lemma* dist_vsub_cancel_left
- \- *lemma* dist_vsub_cancel_right
- \- *lemma* dist_vsub_vsub_le
- \- *lemma* edist_vadd_vadd_le
- \- *lemma* edist_vsub_vsub_le
- \- *lemma* filter.tendsto.line_map
- \- *lemma* filter.tendsto.midpoint
- \- *lemma* filter.tendsto.vsub
- \- *def* isometric.const_vadd
- \- *def* isometric.const_vsub
- \- *def* isometric.vadd_const
- \- *lemma* lipschitz_with.vadd
- \- *lemma* lipschitz_with.vsub
- \- *def* metric_space_of_normed_group_of_add_torsor
- \- *lemma* nndist_vadd_vadd_le
- \- *lemma* nndist_vsub_vsub_le
- \- *def* pseudo_metric_space_of_normed_group_of_add_torsor
- \- *lemma* uniform_continuous_vadd
- \- *lemma* uniform_continuous_vsub
- \- *lemma* vadd_ball
- \- *lemma* vadd_closed_ball
- \- *lemma* vadd_sphere



## [2022-02-14 06:18:50](https://github.com/leanprover-community/mathlib/commit/26fd61c)
feat(analysis/complex/isometry): `rotation_trans` ([#12015](https://github.com/leanprover-community/mathlib/pull/12015))
Add a `simp` lemma about the composition of two rotations.
#### Estimated changes
Modified src/analysis/complex/isometry.lean
- \+ *lemma* rotation_trans



## [2022-02-14 06:18:49](https://github.com/leanprover-community/mathlib/commit/77dfac2)
feat(order/filter/bases): basis of infimum of filters ([#11855](https://github.com/leanprover-community/mathlib/pull/11855))
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis_infi

Modified src/order/filter/pi.lean
- \+ *lemma* filter.has_basis_pi



## [2022-02-14 04:42:39](https://github.com/leanprover-community/mathlib/commit/6550cba)
feat(order/partition/finpartition): Finite partitions ([#9795](https://github.com/leanprover-community/mathlib/pull/9795))
This defines finite partitions along with quite a few constructions,
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+/\- *lemma* finset.disjoint_sup_left
- \+/\- *lemma* finset.disjoint_sup_right
- \+/\- *lemma* finset.inf_sup_distrib_left
- \+/\- *lemma* finset.inf_sup_distrib_right
- \+/\- *lemma* finset.sup_inf_distrib_left
- \+/\- *lemma* finset.sup_inf_distrib_right

Modified src/data/finset/prod.lean
- \+ *lemma* finset.mk_mem_product

Modified src/data/set/pairwise.lean
- \+ *lemma* set.pairwise_disjoint.eq_of_le

Modified src/data/setoid/partition.lean


Added src/order/partition/finpartition.lean
- \+ *def* finpartition.atomise
- \+ *lemma* finpartition.atomise_empty
- \+ *def* finpartition.avoid
- \+ *lemma* finpartition.bUnion_filter_atomise
- \+ *lemma* finpartition.bUnion_parts
- \+ *def* finpartition.bind
- \+ *lemma* finpartition.card_atomise_le
- \+ *lemma* finpartition.card_bind
- \+ *lemma* finpartition.card_bot
- \+ *lemma* finpartition.card_extend
- \+ *lemma* finpartition.card_mono
- \+ *lemma* finpartition.card_parts_le_card
- \+ *def* finpartition.copy
- \+ *lemma* finpartition.default_eq_empty
- \+ *lemma* finpartition.exists_le_of_le
- \+ *lemma* finpartition.exists_mem
- \+ *def* finpartition.extend
- \+ *def* finpartition.indiscrete
- \+ *lemma* finpartition.mem_atomise
- \+ *lemma* finpartition.mem_bind
- \+ *lemma* finpartition.mem_bot_iff
- \+ *lemma* finpartition.ne_bot
- \+ *lemma* finpartition.nonempty_of_mem_parts
- \+ *def* finpartition.of_erase
- \+ *def* finpartition.of_subset
- \+ *lemma* finpartition.parts_bot
- \+ *lemma* finpartition.parts_eq_empty_iff
- \+ *lemma* finpartition.parts_inf
- \+ *lemma* finpartition.parts_nonempty
- \+ *lemma* finpartition.parts_nonempty_iff
- \+ *lemma* finpartition.sum_card_parts
- \+ *structure* finpartition
- \+ *def* is_atom.unique_finpartition

Modified src/order/sup_indep.lean




## [2022-02-13 20:36:13](https://github.com/leanprover-community/mathlib/commit/f91a32d)
feat(data/nat/factorization): add lemma `prod_prime_factors_dvd` ([#11572](https://github.com/leanprover-community/mathlib/pull/11572))
For all `n : ℕ`, the product of the set of prime factors of `n` divides `n`, 
i.e. `(∏ (p : ℕ) in n.factors.to_finset, p) ∣ n`
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* multiset.to_finset_prod_dvd_prod

Modified src/data/nat/factorization.lean
- \+ *lemma* nat.prod_prime_factors_dvd



## [2022-02-13 17:37:37](https://github.com/leanprover-community/mathlib/commit/b08dc17)
chore(number_theory/dioph): fix docs ([#12011](https://github.com/leanprover-community/mathlib/pull/12011))
#### Estimated changes
Modified src/number_theory/dioph.lean




## [2022-02-12 22:55:33](https://github.com/leanprover-community/mathlib/commit/af1355c)
chore(measure_theory/integral/lebesgue): use to_additive when declaring instances and basic lemmas about simple functions ([#12000](https://github.com/leanprover-community/mathlib/pull/12000))
I also grouped similar lemmas together and added one or two missing ones.
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \- *lemma* measure_theory.simple_func.add_apply
- \- *lemma* measure_theory.simple_func.add_eq_map₂
- \- *lemma* measure_theory.simple_func.coe_add
- \+ *lemma* measure_theory.simple_func.coe_div
- \+ *lemma* measure_theory.simple_func.coe_inv
- \+/\- *lemma* measure_theory.simple_func.coe_mul
- \- *lemma* measure_theory.simple_func.coe_neg
- \+ *lemma* measure_theory.simple_func.coe_one
- \- *lemma* measure_theory.simple_func.coe_sub
- \- *lemma* measure_theory.simple_func.coe_zero
- \+ *lemma* measure_theory.simple_func.const_one
- \- *lemma* measure_theory.simple_func.const_zero
- \+ *lemma* measure_theory.simple_func.div_apply
- \+ *lemma* measure_theory.simple_func.inf_apply
- \+ *lemma* measure_theory.simple_func.inv_apply
- \- *theorem* measure_theory.simple_func.map_add
- \+ *theorem* measure_theory.simple_func.map_mul
- \+/\- *lemma* measure_theory.simple_func.mul_apply
- \+/\- *lemma* measure_theory.simple_func.mul_eq_map₂
- \+ *lemma* measure_theory.simple_func.range_one
- \- *lemma* measure_theory.simple_func.range_zero
- \- *lemma* measure_theory.simple_func.sub_apply
- \+/\- *lemma* measure_theory.simple_func.sup_eq_map₂



## [2022-02-12 21:57:51](https://github.com/leanprover-community/mathlib/commit/4b217ea)
chore(topology/algebra): rename file to match renamed lemmas ([#11996](https://github.com/leanprover-community/mathlib/pull/11996))
[#11940](https://github.com/leanprover-community/mathlib/pull/11940) renamed the lemmas from `continuous_smul₂` to `continuous_const_smul`, so this renames the file from `mul_action2` to `const_mul_action` accordingly.
#### Estimated changes
Renamed src/topology/algebra/mul_action2.lean to src/topology/algebra/const_mul_action.lean


Modified src/topology/algebra/mul_action.lean




## [2022-02-12 19:33:32](https://github.com/leanprover-community/mathlib/commit/4a4a3a9)
chore(data/finset/basic): Golf and compress ([#11987](https://github.com/leanprover-community/mathlib/pull/11987))
* Move the `lattice` instance earlier so that it can be used to prove lemmas
* Golf proofs
* Compress statements within the style guidelines
#### Estimated changes
Modified src/data/finset/basic.lean
- \+/\- *lemma* equiv.finset_congr_refl
- \+/\- *lemma* equiv.finset_congr_symm
- \+ *lemma* finset.bUnion_congr
- \- *theorem* finset.bUnion_congr
- \+/\- *lemma* finset.bUnion_mono
- \+/\- *lemma* finset.bUnion_singleton_eq_self
- \+/\- *lemma* finset.bUnion_subset_bUnion_of_subset_left
- \+/\- *lemma* finset.coe_eq_empty
- \+/\- *lemma* finset.coe_to_list
- \+/\- *def* finset.cons
- \+/\- *lemma* finset.cons_subset_cons
- \+ *lemma* finset.cons_val
- \- *theorem* finset.cons_val
- \+ *lemma* finset.disj_union_eq_union
- \- *theorem* finset.disj_union_eq_union
- \+/\- *lemma* finset.disjoint_bUnion_left
- \+/\- *lemma* finset.disjoint_bUnion_right
- \+/\- *lemma* finset.disjoint_filter
- \+/\- *lemma* finset.disjoint_filter_filter
- \+/\- *lemma* finset.disjoint_iff_disjoint_coe
- \+ *lemma* finset.disjoint_iff_inter_eq_empty
- \- *theorem* finset.disjoint_iff_inter_eq_empty
- \+ *lemma* finset.disjoint_iff_ne
- \- *theorem* finset.disjoint_iff_ne
- \+ *lemma* finset.disjoint_insert_left
- \- *theorem* finset.disjoint_insert_left
- \+ *lemma* finset.disjoint_insert_right
- \- *theorem* finset.disjoint_insert_right
- \+ *lemma* finset.disjoint_left
- \- *theorem* finset.disjoint_left
- \+ *lemma* finset.disjoint_of_subset_left
- \- *theorem* finset.disjoint_of_subset_left
- \+ *lemma* finset.disjoint_of_subset_right
- \- *theorem* finset.disjoint_of_subset_right
- \+ *lemma* finset.disjoint_right
- \- *theorem* finset.disjoint_right
- \+/\- *lemma* finset.disjoint_sdiff
- \+/\- *lemma* finset.disjoint_self_iff_empty
- \+/\- *lemma* finset.disjoint_singleton
- \+ *lemma* finset.disjoint_singleton_left
- \- *theorem* finset.disjoint_singleton_left
- \+ *lemma* finset.disjoint_singleton_right
- \- *theorem* finset.disjoint_singleton_right
- \+ *lemma* finset.disjoint_union_left
- \- *theorem* finset.disjoint_union_left
- \+ *lemma* finset.disjoint_union_right
- \- *theorem* finset.disjoint_union_right
- \+ *lemma* finset.disjoint_val
- \- *theorem* finset.disjoint_val
- \+ *lemma* finset.empty_inter
- \- *theorem* finset.empty_inter
- \+/\- *lemma* finset.empty_sdiff
- \+ *lemma* finset.eq_empty_of_forall_not_mem
- \- *theorem* finset.eq_empty_of_forall_not_mem
- \+/\- *lemma* finset.eq_of_mem_of_not_mem_erase
- \+ *lemma* finset.eq_of_mem_singleton
- \- *theorem* finset.eq_of_mem_singleton
- \+/\- *lemma* finset.erase_inj
- \+/\- *lemma* finset.erase_inj_on
- \+ *lemma* finset.exists_mem_insert
- \- *theorem* finset.exists_mem_insert
- \+/\- *lemma* finset.filter_eq
- \+/\- *lemma* finset.filter_ne'
- \+/\- *lemma* finset.filter_ne
- \+ *lemma* finset.forall_mem_insert
- \- *theorem* finset.forall_mem_insert
- \+ *lemma* finset.forall_mem_union
- \- *theorem* finset.forall_mem_union
- \+ *lemma* finset.image_id
- \- *theorem* finset.image_id
- \+ *lemma* finset.image_inter
- \- *theorem* finset.image_inter
- \+ *lemma* finset.image_subset_iff
- \- *theorem* finset.image_subset_iff
- \+ *lemma* finset.inf_eq_inter
- \- *theorem* finset.inf_eq_inter
- \+ *lemma* finset.insert_eq_of_mem
- \- *theorem* finset.insert_eq_of_mem
- \+/\- *lemma* finset.insert_sdiff_of_mem
- \+ *lemma* finset.insert_subset
- \- *theorem* finset.insert_subset
- \+ *lemma* finset.insert_union_distrib
- \- *theorem* finset.insert_union_distrib
- \+ *lemma* finset.inter_empty
- \- *theorem* finset.inter_empty
- \+ *lemma* finset.inter_eq_left_iff_subset
- \- *theorem* finset.inter_eq_left_iff_subset
- \+ *lemma* finset.inter_eq_right_iff_subset
- \- *theorem* finset.inter_eq_right_iff_subset
- \+ *lemma* finset.inter_sdiff
- \- *theorem* finset.inter_sdiff
- \+ *lemma* finset.inter_self
- \- *theorem* finset.inter_self
- \+/\- *lemma* finset.inter_subset_inter_left
- \+/\- *lemma* finset.inter_subset_inter_right
- \+ *lemma* finset.inter_val
- \- *theorem* finset.inter_val
- \+/\- *lemma* finset.left_eq_union_iff_subset
- \+ *lemma* finset.map_insert
- \- *theorem* finset.map_insert
- \+/\- *lemma* finset.map_subtype_subset
- \+ *lemma* finset.mem_bUnion
- \- *theorem* finset.mem_bUnion
- \+ *lemma* finset.mem_cons
- \- *theorem* finset.mem_cons
- \+/\- *lemma* finset.mem_cons_self
- \+ *lemma* finset.mem_erase_of_ne_of_mem
- \- *theorem* finset.mem_erase_of_ne_of_mem
- \+/\- *lemma* finset.mem_image_const
- \+/\- *lemma* finset.mem_image_const_self
- \+ *lemma* finset.mem_insert
- \- *theorem* finset.mem_insert
- \+ *lemma* finset.mem_insert_of_mem
- \- *theorem* finset.mem_insert_of_mem
- \+ *lemma* finset.mem_map'
- \- *theorem* finset.mem_map'
- \+ *lemma* finset.mem_map_equiv
- \- *theorem* finset.mem_map_equiv
- \+ *lemma* finset.mem_map_of_mem
- \- *theorem* finset.mem_map_of_mem
- \+ *lemma* finset.mem_of_mem_erase
- \- *theorem* finset.mem_of_mem_erase
- \+ *lemma* finset.mem_of_mem_insert_of_ne
- \- *theorem* finset.mem_of_mem_insert_of_ne
- \+/\- *lemma* finset.mem_range_le
- \+ *lemma* finset.mem_union
- \- *theorem* finset.mem_union
- \+ *lemma* finset.mem_union_left
- \- *theorem* finset.mem_union_left
- \+ *lemma* finset.mem_union_right
- \- *theorem* finset.mem_union_right
- \+ *lemma* finset.mk_cons
- \- *theorem* finset.mk_cons
- \+/\- *lemma* finset.monotone_filter_left
- \+/\- *lemma* finset.ne_insert_of_not_mem
- \+ *lemma* finset.ne_of_mem_erase
- \- *theorem* finset.ne_of_mem_erase
- \+/\- *lemma* finset.nonempty.bUnion
- \- *lemma* finset.nonempty.image
- \+/\- *lemma* finset.nonempty.image_iff
- \+ *lemma* finset.nonempty_cons
- \- *theorem* finset.nonempty_cons
- \+/\- *lemma* finset.not_disjoint_iff
- \+ *lemma* finset.not_mem_union
- \- *theorem* finset.not_mem_union
- \+/\- *def* finset.piecewise
- \+/\- *lemma* finset.piecewise_coe
- \+/\- *lemma* finset.piecewise_empty
- \+/\- *lemma* finset.piecewise_eq_of_mem
- \+/\- *lemma* finset.piecewise_insert
- \+/\- *lemma* finset.piecewise_insert_of_ne
- \+/\- *lemma* finset.piecewise_insert_self
- \+ *lemma* finset.range_add_one
- \- *theorem* finset.range_add_one
- \+/\- *lemma* finset.right_eq_union_iff_subset
- \+/\- *lemma* finset.sdiff_disjoint
- \+ *lemma* finset.sdiff_empty
- \- *theorem* finset.sdiff_empty
- \+ *lemma* finset.sdiff_eq_self
- \- *theorem* finset.sdiff_eq_self
- \+/\- *lemma* finset.sdiff_eq_self_iff_disjoint
- \+/\- *lemma* finset.sdiff_eq_self_of_disjoint
- \+/\- *lemma* finset.sdiff_erase
- \+/\- *lemma* finset.sdiff_idem
- \+/\- *lemma* finset.sdiff_insert_of_not_mem
- \+ *lemma* finset.sdiff_inter_distrib_right
- \- *theorem* finset.sdiff_inter_distrib_right
- \+ *lemma* finset.sdiff_inter_self
- \- *theorem* finset.sdiff_inter_self
- \+ *lemma* finset.sdiff_inter_self_left
- \- *theorem* finset.sdiff_inter_self_left
- \+ *lemma* finset.sdiff_inter_self_right
- \- *theorem* finset.sdiff_inter_self_right
- \+/\- *lemma* finset.sdiff_sdiff_self_left
- \+ *lemma* finset.sdiff_self
- \- *theorem* finset.sdiff_self
- \+/\- *lemma* finset.sdiff_ssubset
- \+/\- *lemma* finset.sdiff_subset
- \+ *lemma* finset.sdiff_subset_sdiff
- \- *theorem* finset.sdiff_subset_sdiff
- \+/\- *lemma* finset.sdiff_union_distrib
- \+/\- *lemma* finset.sdiff_union_inter
- \+/\- *lemma* finset.singleton_subset_iff
- \+/\- *lemma* finset.singleton_subset_set_iff
- \+/\- *lemma* finset.ssubset_iff
- \+/\- *lemma* finset.ssubset_insert
- \+/\- *lemma* finset.subset_bUnion_of_mem
- \+/\- *lemma* finset.subset_image_iff
- \+ *lemma* finset.subset_insert
- \- *theorem* finset.subset_insert
- \+ *lemma* finset.subset_inter
- \- *theorem* finset.subset_inter
- \+/\- *lemma* finset.subset_inter_iff
- \+ *lemma* finset.subset_singleton_iff'
- \+ *lemma* finset.sup_eq_union
- \- *theorem* finset.sup_eq_union
- \+/\- *lemma* finset.to_list_empty
- \+ *lemma* finset.union_assoc
- \- *theorem* finset.union_assoc
- \+ *lemma* finset.union_comm
- \- *theorem* finset.union_comm
- \+/\- *lemma* finset.union_eq_left_iff_subset
- \+/\- *lemma* finset.union_eq_right_iff_subset
- \+ *lemma* finset.union_idempotent
- \- *theorem* finset.union_idempotent
- \+ *lemma* finset.union_left_comm
- \- *theorem* finset.union_left_comm
- \+ *lemma* finset.union_right_comm
- \- *theorem* finset.union_right_comm
- \+/\- *lemma* finset.union_sdiff_distrib
- \+ *lemma* finset.union_sdiff_of_subset
- \- *theorem* finset.union_sdiff_of_subset
- \+/\- *lemma* finset.union_sdiff_self
- \+ *lemma* finset.union_subset
- \- *theorem* finset.union_subset
- \+/\- *lemma* finset.union_subset_iff
- \+ *lemma* finset.union_subset_left
- \- *theorem* finset.union_subset_left
- \+ *lemma* finset.union_subset_right
- \- *theorem* finset.union_subset_right
- \+/\- *lemma* finset.union_subset_union
- \+ *lemma* finset.union_val
- \- *theorem* finset.union_val
- \+ *lemma* finset.union_val_nd
- \- *theorem* finset.union_val_nd
- \+/\- *lemma* finset.val_le_iff_val_subset
- \+/\- *lemma* function.injective.mem_finset_image
- \+/\- *lemma* list.disjoint_to_finset_iff_disjoint
- \+ *lemma* list.mem_to_finset
- \- *theorem* list.mem_to_finset
- \+/\- *lemma* list.perm_of_nodup_nodup_to_finset_eq
- \+/\- *lemma* list.to_finset.ext
- \+/\- *lemma* list.to_finset_append
- \+ *lemma* list.to_finset_cons
- \- *theorem* list.to_finset_cons
- \+ *lemma* list.to_finset_eq
- \- *theorem* list.to_finset_eq
- \+/\- *lemma* list.to_finset_eq_empty_iff
- \+/\- *lemma* list.to_finset_eq_iff_perm_erase_dup
- \+/\- *lemma* list.to_finset_eq_of_perm
- \+ *lemma* list.to_finset_nil
- \- *theorem* list.to_finset_nil
- \+/\- *lemma* list.to_finset_repeat_of_ne_zero
- \+/\- *lemma* list.to_finset_reverse
- \+ *lemma* multiset.mem_to_finset
- \- *theorem* multiset.mem_to_finset
- \+/\- *lemma* multiset.to_finset_add
- \+/\- *lemma* multiset.to_finset_inter
- \+/\- *lemma* multiset.to_finset_singleton
- \+/\- *lemma* multiset.to_finset_subset
- \+/\- *lemma* multiset.to_finset_union
- \+/\- *lemma* multiset.to_finset_zero



## [2022-02-12 18:45:31](https://github.com/leanprover-community/mathlib/commit/5f70cd9)
chore(measure_theory/function/ae_eq_fun): replace topological assumptions by measurability assumptions ([#11981](https://github.com/leanprover-community/mathlib/pull/11981))
Since the introduction of the `has_measurable_*` typeclasses, the topological assumptions in that file are only used to derive the measurability assumptions. This PR removes that step.
#### Estimated changes
Modified src/measure_theory/function/ae_eq_fun.lean




## [2022-02-12 17:23:47](https://github.com/leanprover-community/mathlib/commit/b72300f)
feat(group_theory/sylow): all max groups normal imply sylow normal ([#11841](https://github.com/leanprover-community/mathlib/pull/11841))
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.normal_of_all_max_subgroups_normal



## [2022-02-12 16:17:52](https://github.com/leanprover-community/mathlib/commit/06e7f76)
feat(analysis/analytic/basic): add uniqueness results for power series ([#11896](https://github.com/leanprover-community/mathlib/pull/11896))
This establishes that if a function has two power series representations on balls of positive radius, then the corresponding formal multilinear series are equal; this is only for the one-dimensional case (i.e., for functions from the scalar field). Consequently, one may exchange the radius of convergence between these power series.
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+ *lemma* asymptotics.is_O.continuous_multilinear_map_apply_eq_zero
- \+ *lemma* has_fpower_series_at.apply_eq_zero
- \+ *theorem* has_fpower_series_at.eq_formal_multilinear_series
- \+ *lemma* has_fpower_series_at.eq_zero
- \+ *theorem* has_fpower_series_on_ball.exchange_radius



## [2022-02-12 09:20:49](https://github.com/leanprover-community/mathlib/commit/91cc4ae)
feat(order/category/BoundedOrder): The category of bounded orders ([#11961](https://github.com/leanprover-community/mathlib/pull/11961))
Define `BoundedOrder`, the category of bounded orders with bounded order homs along with its forgetful functors to `PartialOrder` and `Bipointed`.
#### Estimated changes
Added src/order/category/BoundedOrder.lean
- \+ *def* BoundedOrder.dual
- \+ *def* BoundedOrder.dual_equiv
- \+ *def* BoundedOrder.iso.mk
- \+ *def* BoundedOrder.of
- \+ *structure* BoundedOrder
- \+ *lemma* BoundedOrder_dual_comp_forget_to_Bipointed
- \+ *lemma* BoundedOrder_dual_comp_forget_to_PartialOrder

Modified src/order/category/PartialOrder.lean
- \- *lemma* PartialOrder_dual_equiv_comp_forget_to_Preorder
- \+ *lemma* PartialOrder_to_dual_comp_forget_to_Preorder

Modified src/order/hom/bounded.lean




## [2022-02-12 08:07:28](https://github.com/leanprover-community/mathlib/commit/1b5f8c2)
chore(topology/algebra/ordered/*): Rename folder ([#11988](https://github.com/leanprover-community/mathlib/pull/11988))
Rename `topology.algebra.ordered` to `topology.algebra.order` to match `order`, `algebra.order`, `topology.order`.
#### Estimated changes
Modified src/algebra/continued_fractions/computation/approximation_corollaries.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/asymptotics/superpolynomial_decay.lean


Modified src/analysis/box_integral/box/basic.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/convex/strict.lean


Modified src/analysis/normed/group/basic.lean


Modified src/analysis/normed_space/lp_space.lean


Modified src/analysis/special_functions/trigonometric/inverse.lean


Modified src/data/real/sqrt.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/topology/algebra/floor_ring.lean


Modified src/topology/algebra/infinite_sum.lean


Renamed src/topology/algebra/ordered/basic.lean to src/topology/algebra/order/basic.lean


Renamed src/topology/algebra/ordered/compact.lean to src/topology/algebra/order/compact.lean


Renamed src/topology/algebra/ordered/extend_from.lean to src/topology/algebra/order/extend_from.lean


Renamed src/topology/algebra/ordered/intermediate_value.lean to src/topology/algebra/order/intermediate_value.lean


Renamed src/topology/algebra/ordered/left_right.lean to src/topology/algebra/order/left_right.lean


Renamed src/topology/algebra/ordered/liminf_limsup.lean to src/topology/algebra/order/liminf_limsup.lean


Renamed src/topology/algebra/ordered/monotone_continuity.lean to src/topology/algebra/order/monotone_continuity.lean


Renamed src/topology/algebra/ordered/monotone_convergence.lean to src/topology/algebra/order/monotone_convergence.lean


Renamed src/topology/algebra/ordered/proj_Icc.lean to src/topology/algebra/order/proj_Icc.lean


Modified src/topology/algebra/with_zero_topology.lean


Modified src/topology/continuous_function/ordered.lean


Modified src/topology/fiber_bundle.lean


Modified src/topology/homotopy/basic.lean


Modified src/topology/instances/ereal.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/order/lattice.lean


Modified src/topology/path_connected.lean


Modified src/topology/tietze_extension.lean




## [2022-02-12 08:07:27](https://github.com/leanprover-community/mathlib/commit/7bebee6)
chore(category_theory/monad/equiv_mon): Removing some slow uses of `obviously` ([#11980](https://github.com/leanprover-community/mathlib/pull/11980))
Providing explicit proofs for various fields rather than leaving them for `obviously` (and hence `tidy`) to fill in.
Follow-up to this suggestion by Kevin Buzzard in [this Zulip comment](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60tidy.60.20in.20mathlib.20proofs/near/271474418).
(These are temporary changes until `obviously` can be tweaked to do this more quickly)
#### Estimated changes
Modified src/category_theory/monad/equiv_mon.lean




## [2022-02-12 08:07:25](https://github.com/leanprover-community/mathlib/commit/71e9006)
chore(topology/algebra/module/multilinear): relax typeclass arguments ([#11972](https://github.com/leanprover-community/mathlib/pull/11972))
Previously `module R' (continuous_multilinear_map A M₁ M₂)` required `algebra R' A`, but now it only requires `smul_comm_class A R' M₂`.
The old instance required (modulo argument reordering):
```lean
def continuous_multilinear_map.module {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [decidable_eq ι]
  [Π i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [Π i, topological_space (M₁ i)]
  [topological_space M₂] [has_continuous_add M₂] 
  {R' : Type u_1} {A : Type u_2} [comm_semiring R'] [semiring A] [topological_space R']
  [Π i, module A (M₁ i)]  [module A M₂] [module R' M₂] [has_continuous_smul R' M₂]
  [algebra R' A] [is_scalar_tower R' A M₂] :
    module R' (continuous_multilinear_map A M₁ M₂)
```
while the new one requires
```lean
def continuous_multilinear_map.module {ι : Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [decidable_eq ι]
  [Π i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [Π i, topological_space (M₁ i)]
  [topological_space M₂] [has_continuous_add M₂]
  {R' : Type u_1} {A : Type u_2} [semiring R'] [semiring A] [topological_space R']  -- note: `R'` not commutative any more
  [Π i, module A (M₁ i)] [module A M₂] [module R' M₂] [has_continuous_smul R' M₂]
  [smul_comm_class A R' M₂] :  -- note: `R'` needs no action at all on `A`
    module R' (continuous_multilinear_map A M₁ M₂)
```
This change also adds intermediate `mul_action` and `distrib_mul_action` instances which apply in weaker situations.
As a result of this weakening, the typeclass arguments to `continuous_multilinear_map.to_normed_space` can also be weakened, and a weird instance workaround can be removed.
#### Estimated changes
Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/topology/algebra/module/multilinear.lean
- \+ *lemma* continuous_multilinear_map.to_multilinear_map_zero



## [2022-02-12 08:07:23](https://github.com/leanprover-community/mathlib/commit/822244f)
refactor(measure_theory/group/basic): rename and split ([#11952](https://github.com/leanprover-community/mathlib/pull/11952))
* Rename `measure_theory/group/basic` -> `measure_theory/group/measure`. It was not the bottom file in this folder in the import hierarchy (arithmetic is below it).
* Split off some results to `measure_theory/group/integration`. This reduces imports in some files, and makes the organization more clear. Furthermore, I will add some integrability results and more integrals in a follow-up PR.
* Prove a general instance `pi.is_mul_left_invariant`
* Remove lemmas specifically about `volume` on `real` in favor on the general lemmas.
```lean
real.map_volume_add_left -> map_add_left_eq_self
real.map_volume_pi_add_left -> map_add_left_eq_self
real.volume_preimage_add_left -> measure_preimage_add
real.volume_pi_preimage_add_left -> measure_preimage_add
real.map_volume_add_right -> map_add_right_eq_self 
real.volume_preimage_add_right -> measure_preimage_add_right
```
#### Estimated changes
Modified src/analysis/box_integral/integrability.lean


Modified src/analysis/fourier.lean


Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/group/arithmetic.lean


Added src/measure_theory/group/integration.lean
- \+ *lemma* measure_theory.integral_mul_left_eq_self
- \+ *lemma* measure_theory.integral_mul_right_eq_self
- \+ *lemma* measure_theory.integral_zero_of_mul_left_eq_neg
- \+ *lemma* measure_theory.integral_zero_of_mul_right_eq_neg
- \+ *lemma* measure_theory.lintegral_eq_zero_of_is_mul_left_invariant
- \+ *lemma* measure_theory.lintegral_mul_left_eq_self
- \+ *lemma* measure_theory.lintegral_mul_right_eq_self

Renamed src/measure_theory/group/basic.lean to src/measure_theory/group/measure.lean
- \- *lemma* measure_theory.lintegral_eq_zero_of_is_mul_left_invariant
- \- *lemma* measure_theory.lintegral_mul_left_eq_self
- \- *lemma* measure_theory.lintegral_mul_right_eq_self

Modified src/measure_theory/group/prod.lean


Modified src/measure_theory/integral/bochner.lean
- \- *lemma* measure_theory.integral_mul_left_eq_self
- \- *lemma* measure_theory.integral_mul_right_eq_self
- \- *lemma* measure_theory.integral_zero_of_mul_left_eq_neg
- \- *lemma* measure_theory.integral_zero_of_mul_right_eq_neg

Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/periodic.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/measure_theory/measure/lebesgue.lean
- \- *lemma* real.map_volume_add_left
- \- *lemma* real.map_volume_add_right
- \- *lemma* real.map_volume_pi_add_left
- \- *lemma* real.volume_pi_preimage_add_left
- \- *lemma* real.volume_preimage_add_left
- \- *lemma* real.volume_preimage_add_right

Modified src/number_theory/liouville/measure.lean




## [2022-02-12 07:11:55](https://github.com/leanprover-community/mathlib/commit/60d3233)
feat(topology/instances/real): metric space structure on nat ([#11963](https://github.com/leanprover-community/mathlib/pull/11963))
Mostly copied from the already existing int version.
#### Estimated changes
Modified src/algebra/order/floor.lean
- \+ *lemma* nat.preimage_Icc
- \+ *lemma* nat.preimage_Ici
- \+ *lemma* nat.preimage_Ico
- \+ *lemma* nat.preimage_Iic
- \+ *lemma* nat.preimage_Iio
- \+ *lemma* nat.preimage_Ioc
- \+ *lemma* nat.preimage_Ioi
- \+ *lemma* nat.preimage_Ioo

Modified src/topology/instances/real.lean
- \+ *theorem* nat.closed_ball_eq_Icc
- \+ *lemma* nat.closed_embedding_coe_rat
- \+ *lemma* nat.closed_embedding_coe_real
- \+ *theorem* nat.dist_cast_rat
- \+ *theorem* nat.dist_cast_real
- \+ *lemma* nat.dist_coe_int
- \+ *theorem* nat.dist_eq
- \+ *lemma* nat.pairwise_one_le_dist
- \+ *theorem* nat.preimage_ball
- \+ *theorem* nat.preimage_closed_ball
- \+ *lemma* nat.uniform_embedding_coe_rat
- \+ *lemma* nat.uniform_embedding_coe_real



## [2022-02-12 02:46:24](https://github.com/leanprover-community/mathlib/commit/dff8393)
feat(tactic/lint): add unprintable tactic linter ([#11725](https://github.com/leanprover-community/mathlib/pull/11725))
This linter will banish the recurring issue of tactics for which `param_desc` fails, leaving a nasty error message in hovers.
#### Estimated changes
Modified src/ring_theory/witt_vector/init_tail.lean


Modified src/tactic/interactive.lean


Modified src/tactic/itauto.lean


Modified src/tactic/linear_combination.lean


Modified src/tactic/lint/default.lean


Modified src/tactic/lint/misc.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/push_neg.lean


Modified src/tactic/squeeze.lean




## [2022-02-12 00:03:02](https://github.com/leanprover-community/mathlib/commit/227293b)
feat(category_theory/category/Twop): The category of two-pointed types ([#11844](https://github.com/leanprover-community/mathlib/pull/11844))
Define `Twop`, the category of two-pointed types. Also add `Pointed_to_Bipointed` and remove the erroneous TODOs.
#### Estimated changes
Modified src/category_theory/category/Bipointed.lean
- \+ *def* Pointed_to_Bipointed
- \+ *def* Pointed_to_Bipointed_comp_Bipointed_to_Pointed_fst
- \+ *def* Pointed_to_Bipointed_comp_Bipointed_to_Pointed_snd
- \- *lemma* Pointed_to_Bipointed_fst_comp
- \+ *lemma* Pointed_to_Bipointed_fst_comp_swap
- \- *lemma* Pointed_to_Bipointed_snd_comp
- \+ *lemma* Pointed_to_Bipointed_snd_comp_swap

Modified src/category_theory/category/Pointed.lean


Added src/category_theory/category/Twop.lean
- \+ *def* Pointed_to_Twop_fst
- \+ *lemma* Pointed_to_Twop_fst_comp_forget_to_Bipointed
- \+ *lemma* Pointed_to_Twop_fst_comp_swap
- \+ *def* Pointed_to_Twop_fst_forget_comp_Bipointed_to_Pointed_fst_adjunction
- \+ *def* Pointed_to_Twop_snd
- \+ *lemma* Pointed_to_Twop_snd_comp_forget_to_Bipointed
- \+ *lemma* Pointed_to_Twop_snd_comp_swap
- \+ *def* Pointed_to_Twop_snd_forget_comp_Bipointed_to_Pointed_snd_adjunction
- \+ *def* Twop.of
- \+ *def* Twop.swap
- \+ *def* Twop.swap_equiv
- \+ *lemma* Twop.swap_equiv_symm
- \+ *def* Twop.to_Bipointed
- \+ *structure* Twop
- \+ *lemma* Twop_swap_comp_forget_to_Bipointed



## [2022-02-11 21:25:20](https://github.com/leanprover-community/mathlib/commit/788240c)
chore(order/cover): Rename `covers` to `covby` ([#11984](https://github.com/leanprover-community/mathlib/pull/11984))
This matches the way it is written. `a ⋖ b` means that `b` covers `a`, that is `a` is covered by `b`.
#### Estimated changes
Modified src/order/atoms.lean
- \+ *lemma* bot_covby_iff
- \+ *lemma* bot_covby_top
- \- *lemma* bot_covers_iff
- \- *lemma* bot_covers_top
- \+ *lemma* covby_top_iff
- \- *lemma* covers_top_iff

Modified src/order/cover.lean
- \+ *lemma* apply_covby_apply_iff
- \- *lemma* apply_covers_apply_iff
- \+ *lemma* covby.Icc_eq
- \+ *lemma* covby.Ico_eq
- \+ *lemma* covby.Ioc_eq
- \+ *lemma* covby.Ioo_eq
- \+ *lemma* covby.image
- \+ *lemma* covby.le
- \+ *lemma* covby.lt
- \+ *lemma* covby.ne'
- \+ *lemma* covby.of_image
- \+ *def* covby
- \- *lemma* covers.Icc_eq
- \- *lemma* covers.Ico_eq
- \- *lemma* covers.Ioc_eq
- \- *lemma* covers.Ioo_eq
- \- *lemma* covers.image
- \- *lemma* covers.le
- \- *lemma* covers.lt
- \- *lemma* covers.ne'
- \- *lemma* covers.of_image
- \- *def* covers
- \+ *lemma* densely_ordered_iff_forall_not_covby
- \- *lemma* densely_ordered_iff_forall_not_covers
- \+ *lemma* not_covby
- \+ *lemma* not_covby_iff
- \- *lemma* not_covers
- \- *lemma* not_covers_iff
- \+ *lemma* of_dual_covby_of_dual_iff
- \- *lemma* of_dual_covers_of_dual_iff
- \+ *lemma* to_dual_covby_to_dual_iff
- \- *lemma* to_dual_covers_to_dual_iff

Modified src/order/succ_pred/basic.lean
- \+ *lemma* covby.pred_eq
- \+ *lemma* covby.succ_eq
- \+ *lemma* covby_iff_pred_eq
- \+ *lemma* covby_iff_succ_eq
- \- *lemma* covers.pred_eq
- \- *lemma* covers.succ_eq
- \- *lemma* covers_iff_pred_eq
- \- *lemma* covers_iff_succ_eq
- \+ *lemma* pred_order.pred_covby
- \+ *lemma* pred_order.pred_covby_of_nonempty_Iio
- \- *lemma* pred_order.pred_covers
- \- *lemma* pred_order.pred_covers_of_nonempty_Iio
- \+/\- *lemma* pred_succ
- \+ *lemma* succ_order.covby_succ
- \+ *lemma* succ_order.covby_succ_of_nonempty_Ioi
- \- *lemma* succ_order.covers_succ
- \- *lemma* succ_order.covers_succ_of_nonempty_Ioi
- \+/\- *lemma* succ_pred



## [2022-02-11 19:49:06](https://github.com/leanprover-community/mathlib/commit/3fcb738)
doc(data/finset/basic): correct some function names ([#11983](https://github.com/leanprover-community/mathlib/pull/11983))
#### Estimated changes
Modified src/data/finset/basic.lean




## [2022-02-11 19:49:04](https://github.com/leanprover-community/mathlib/commit/515ce79)
refactor(data/nat/factorization): Use factorization instead of factors.count ([#11384](https://github.com/leanprover-community/mathlib/pull/11384))
Refactor to use `factorization` over `factors.count`, and adjust lemmas to be stated in terms of the former instead.
#### Estimated changes
Modified src/algebra/is_prime_pow.lean


Modified src/data/nat/factorization.lean
- \- *lemma* nat.div_factorization_eq_tsub_of_dvd
- \+ *lemma* nat.dvd_of_mem_factorization
- \+ *lemma* nat.eq_of_factorization_eq
- \+ *lemma* nat.factorization_div
- \- *lemma* nat.factorization_eq_count
- \+ *lemma* nat.factorization_eq_of_coprime_left
- \+ *lemma* nat.factorization_eq_of_coprime_right
- \+ *lemma* nat.factorization_le_factorization_mul_left
- \+ *lemma* nat.factorization_le_factorization_mul_right
- \+ *lemma* nat.factorization_mul_apply_of_coprime
- \+/\- *lemma* nat.factorization_pow
- \+/\- *lemma* nat.factorization_zero
- \+ *lemma* nat.factors_count_eq
- \+/\- *lemma* nat.pow_factorization_dvd
- \+ *lemma* nat.pow_succ_factorization_not_dvd
- \+ *lemma* nat.prime.factorization_pos_of_dvd
- \+/\- *lemma* nat.prime.factorization_pow
- \+ *def* nat.rec_on_mul
- \+ *def* nat.rec_on_pos_prime_coprime
- \+ *def* nat.rec_on_prime_coprime
- \+ *def* nat.rec_on_prime_pow
- \+/\- *lemma* nat.support_factorization

Deleted src/data/nat/mul_ind.lean
- \- *def* nat.rec_on_mul
- \- *def* nat.rec_on_pos_prime_coprime
- \- *def* nat.rec_on_prime_coprime
- \- *def* nat.rec_on_prime_pow

Modified src/data/nat/prime.lean
- \- *lemma* nat.count_factors_mul_of_coprime
- \- *lemma* nat.count_factors_mul_of_pos
- \- *lemma* nat.eq_of_count_factors_eq
- \+/\- *lemma* nat.eq_of_perm_factors
- \- *lemma* nat.factors_count_eq_of_coprime_left
- \- *lemma* nat.factors_count_eq_of_coprime_right
- \- *lemma* nat.factors_count_pow
- \- *lemma* nat.le_factors_count_mul_left
- \- *lemma* nat.le_factors_count_mul_right
- \+/\- *lemma* nat.mem_factors_iff_dvd
- \+/\- *lemma* nat.mem_factors_mul_left
- \+/\- *lemma* nat.mem_factors_mul_of_coprime
- \+/\- *lemma* nat.mem_factors_mul_right
- \+ *lemma* nat.perm_factors_mul
- \- *lemma* nat.perm_factors_mul_of_pos
- \- *lemma* nat.pow_factors_count_dvd
- \+/\- *lemma* nat.prod_factors

Modified src/data/pnat/factors.lean


Modified src/group_theory/exponent.lean
- \+ *lemma* nat.prime.exists_order_of_eq_pow_factorization_exponent
- \- *lemma* nat.prime.exists_order_of_eq_pow_padic_val_nat_exponent

Modified src/group_theory/p_group.lean


Modified src/group_theory/sylow.lean


Modified src/number_theory/arithmetic_function.lean


Modified src/number_theory/padics/padic_norm.lean
- \+ *lemma* padic_val_nat_eq_factorization
- \- *lemma* padic_val_nat_eq_factors_count

Modified src/ring_theory/int/basic.lean




## [2022-02-11 18:25:43](https://github.com/leanprover-community/mathlib/commit/da76d21)
feat(measure_theory/measure/haar_quotient): Pushforward of Haar measure is Haar ([#11593](https://github.com/leanprover-community/mathlib/pull/11593))
For `G` a topological group with discrete subgroup `Γ`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. When `Γ` is normal (and under other certain suitable conditions), we show that this measure is the Haar measure on the quotient group `G ⧸ Γ`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *def* subgroup.opposite
- \+ *def* subgroup.opposite_equiv
- \+ *lemma* subgroup.smul_opposite_image_mul_preimage
- \+ *lemma* subgroup.smul_opposite_mul

Modified src/measure_theory/group/arithmetic.lean
- \+ *lemma* measurable_mul_op
- \+ *lemma* measurable_mul_unop
- \- *lemma* measurable_op
- \- *lemma* measurable_unop

Modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* measure_theory.is_fundamental_domain.measure_set_eq

Added src/measure_theory/measure/haar_quotient.lean
- \+ *lemma* measure_theory.is_fundamental_domain.is_mul_left_invariant_map
- \+ *lemma* measure_theory.is_fundamental_domain.map_restrict_quotient
- \+ *lemma* measure_theory.is_fundamental_domain.smul
- \+ *lemma* measure_theory.is_fundamental_domain.smul_invariant_measure_map
- \+ *lemma* subgroup.smul_invariant_measure



## [2022-02-11 15:45:40](https://github.com/leanprover-community/mathlib/commit/edefc11)
feat(number_theory/number_field/basic) : the ring of integers of a number field is not a field  ([#11956](https://github.com/leanprover-community/mathlib/pull/11956))
#### Estimated changes
Modified src/data/int/char_zero.lean
- \+ *lemma* ring_hom.injective_int

Modified src/number_theory/number_field.lean
- \+ *lemma* int.not_is_field
- \+ *lemma* number_field.ring_of_integers.not_is_field



## [2022-02-11 13:10:47](https://github.com/leanprover-community/mathlib/commit/1b78b4d)
feat(measure_theory/function/ae_eq_of_integral): remove a few unnecessary `@` ([#11974](https://github.com/leanprover-community/mathlib/pull/11974))
Those `@` were necessary at the time, but `measurable_set.inter` changed and they can now be removed.
#### Estimated changes
Modified src/measure_theory/function/ae_eq_of_integral.lean




## [2022-02-11 13:10:46](https://github.com/leanprover-community/mathlib/commit/114752c)
fix(algebra/monoid_algebra/basic): remove an instance that forms a diamond ([#11918](https://github.com/leanprover-community/mathlib/pull/11918))
This turns `monoid_algebra.comap_distrib_mul_action_self` from an instance to a def.
This also adds some tests to prove that this diamond exists.
Note that this diamond is not just non-defeq, it's also just plain not equal.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Schur's.20lemma/near/270990004)
#### Estimated changes
Modified src/algebra/monoid_algebra/basic.lean
- \+ *def* monoid_algebra.comap_distrib_mul_action_self

Modified src/data/finsupp/basic.lean


Modified test/instance_diamonds.lean




## [2022-02-11 11:23:57](https://github.com/leanprover-community/mathlib/commit/492393b)
feat(model_theory/direct_limit): Direct limits of first-order structures ([#11789](https://github.com/leanprover-community/mathlib/pull/11789))
Constructs the direct limit of a directed system of first-order embeddings
#### Estimated changes
Modified src/data/fintype/order.lean
- \+ *theorem* directed.fintype_le
- \+ *lemma* fintype.bdd_above_range
- \+ *lemma* fintype.exists_le

Modified src/data/quot.lean
- \+ *lemma* quotient.lift_comp_mk

Added src/model_theory/direct_limit.lean
- \+ *lemma* first_order.language.direct_limit.comp_unify
- \+ *lemma* first_order.language.direct_limit.equiv_iff
- \+ *theorem* first_order.language.direct_limit.exists_of
- \+ *lemma* first_order.language.direct_limit.exists_quotient_mk_sigma_mk_eq
- \+ *lemma* first_order.language.direct_limit.exists_unify_eq
- \+ *lemma* first_order.language.direct_limit.fun_map_equiv_unify
- \+ *lemma* first_order.language.direct_limit.fun_map_quotient_mk_sigma_mk
- \+ *lemma* first_order.language.direct_limit.fun_map_unify_equiv
- \+ *lemma* first_order.language.direct_limit.lift_of
- \+ *lemma* first_order.language.direct_limit.lift_quotient_mk_sigma_mk
- \+ *theorem* first_order.language.direct_limit.lift_unique
- \+ *lemma* first_order.language.direct_limit.of_apply
- \+ *lemma* first_order.language.direct_limit.of_f
- \+ *lemma* first_order.language.direct_limit.rel_map_equiv_unify
- \+ *lemma* first_order.language.direct_limit.rel_map_quotient_mk_sigma_mk
- \+ *lemma* first_order.language.direct_limit.rel_map_unify_equiv
- \+ *def* first_order.language.direct_limit.setoid
- \+ *def* first_order.language.direct_limit.unify
- \+ *lemma* first_order.language.direct_limit.unify_sigma_mk_self
- \+ *def* first_order.language.direct_limit
- \+ *lemma* first_order.language.directed_system.map_map
- \+ *lemma* first_order.language.directed_system.map_self

Modified src/model_theory/quotients.lean
- \+ *lemma* first_order.language.rel_map_quotient_mk



## [2022-02-11 07:37:33](https://github.com/leanprover-community/mathlib/commit/024aef0)
feat(data/pi): provide `pi.mul_single` ([#11849](https://github.com/leanprover-community/mathlib/pull/11849))
the additive version was previously called `pi.single`, to this requires refactoring existing code.
#### Estimated changes
Modified src/algebra/group/pi.lean
- \- *def* add_monoid_hom.single
- \+ *def* monoid_hom.single
- \+ *def* one_hom.single
- \+ *lemma* pi.mul_single_inv
- \+ *lemma* pi.mul_single_mul
- \- *lemma* pi.single_add
- \+ *lemma* pi.single_div
- \- *lemma* pi.single_neg
- \- *lemma* pi.single_sub
- \+ *lemma* pi.update_eq_div_mul_single
- \- *lemma* pi.update_eq_sub_add_single
- \- *def* zero_hom.single

Modified src/algebra/group/to_additive.lean


Modified src/data/pi.lean
- \+ *lemma* pi.apply_mul_single
- \+ *lemma* pi.apply_mul_single₂
- \- *lemma* pi.apply_single
- \- *lemma* pi.apply_single₂
- \+ *def* pi.mul_single
- \+ *lemma* pi.mul_single_apply
- \+ *lemma* pi.mul_single_comm
- \+ *lemma* pi.mul_single_eq_of_ne'
- \+ *lemma* pi.mul_single_eq_of_ne
- \+ *lemma* pi.mul_single_eq_same
- \+ *lemma* pi.mul_single_inj
- \+ *lemma* pi.mul_single_injective
- \+ *lemma* pi.mul_single_one
- \+ *lemma* pi.mul_single_op
- \+ *lemma* pi.mul_single_op₂
- \- *def* pi.single
- \- *lemma* pi.single_apply
- \- *lemma* pi.single_comm
- \- *lemma* pi.single_eq_of_ne'
- \- *lemma* pi.single_eq_of_ne
- \- *lemma* pi.single_eq_same
- \- *lemma* pi.single_inj
- \- *lemma* pi.single_injective
- \- *lemma* pi.single_op
- \- *lemma* pi.single_op₂
- \- *lemma* pi.single_zero
- \+ *lemma* subsingleton.pi_mul_single_eq
- \- *lemma* subsingleton.pi_single_eq



## [2022-02-11 03:15:15](https://github.com/leanprover-community/mathlib/commit/8c60a92)
fix(ring_theory/algebraic): prove a diamond exists and remove the instances ([#11935](https://github.com/leanprover-community/mathlib/pull/11935))
It seems nothing used these instances anyway.
#### Estimated changes
Modified src/ring_theory/algebraic.lean
- \+ *def* polynomial.has_scalar_pi

Modified test/instance_diamonds.lean




## [2022-02-11 01:36:55](https://github.com/leanprover-community/mathlib/commit/fbfdff7)
chore(data/real/ennreal, topology/instances/ennreal): change name of the order isomorphism for `inv` ([#11959](https://github.com/leanprover-community/mathlib/pull/11959))
On [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/naming.20defs/near/271228611) it was decided that the name should be changed from `ennreal.inv_order_iso` to `order_iso.inv_ennreal` in order to better accord with the rest of the library.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \- *def* ennreal.inv_order_iso
- \- *lemma* ennreal.inv_order_iso_symm_apply
- \+ *def* order_iso.inv_ennreal
- \+ *lemma* order_iso.inv_ennreal_symm_apply

Modified src/topology/instances/ennreal.lean




## [2022-02-11 01:36:54](https://github.com/leanprover-community/mathlib/commit/ae14f6a)
chore(algebra/star): generalize star_bit0, add star_inv_of ([#11951](https://github.com/leanprover-community/mathlib/pull/11951))
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+/\- *lemma* star_bit0
- \+/\- *lemma* star_bit1
- \+ *lemma* star_inv_of



## [2022-02-11 01:36:53](https://github.com/leanprover-community/mathlib/commit/0227820)
feat(topology/algebra/group): added (right/left)_coset_(open/closed) ([#11876](https://github.com/leanprover-community/mathlib/pull/11876))
Added lemmas saying that, in a topological group, cosets of an open (resp. closed) set are open (resp. closed).
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* is_closed.left_coset
- \+ *lemma* is_closed.right_coset
- \+ *lemma* is_open.left_coset
- \+ *lemma* is_open.right_coset



## [2022-02-11 01:36:52](https://github.com/leanprover-community/mathlib/commit/7351358)
refactor(order/well_founded, set_theory/ordinal_arithmetic): Fix namespace in `self_le_of_strict_mono` ([#11871](https://github.com/leanprover-community/mathlib/pull/11871))
This places `self_le_of_strict_mono` in the `well_founded` namespace. We also rename `is_normal.le_self` to `is_normal.self_le` .
#### Estimated changes
Modified src/order/well_founded.lean
- \- *theorem* function.well_founded.self_le_of_strict_mono
- \+ *theorem* well_founded.self_le_of_strict_mono

Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.is_normal.le_self
- \+ *theorem* ordinal.is_normal.self_le

Modified src/set_theory/principal.lean




## [2022-02-10 23:42:58](https://github.com/leanprover-community/mathlib/commit/4a5728f)
chore(number_theory/cyclotomic/zeta): generalize to primitive roots ([#11941](https://github.com/leanprover-community/mathlib/pull/11941))
This was done as `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ)) = zeta p ℚ ℚ(ζₚ)` is independent of Lean's type theory. Allows far more flexibility with results.
#### Estimated changes
Modified src/number_theory/cyclotomic/gal.lean
- \- *lemma* is_cyclotomic_extension.aut_to_pow_injective
- \+ *lemma* is_cyclotomic_extension.from_zeta_aut_spec
- \+ *lemma* is_primitive_root.aut_to_pow_injective
- \- *lemma* is_primitive_root.from_zeta_aut_spec

Added src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* is_cyclotomic_extension.finrank
- \+ *lemma* is_cyclotomic_extension.zeta_pow
- \+ *lemma* is_cyclotomic_extension.zeta_primitive_root
- \+ *lemma* is_cyclotomic_extension.zeta_spec'
- \+ *lemma* is_cyclotomic_extension.zeta_spec
- \+ *lemma* is_primitive_root.norm_eq_one
- \+ *lemma* is_primitive_root.sub_one_norm_eq_eval_cyclotomic

Deleted src/number_theory/cyclotomic/zeta.lean
- \- *lemma* is_cyclotomic_extension.finrank
- \- *lemma* is_cyclotomic_extension.norm_zeta_eq_one
- \- *lemma* is_cyclotomic_extension.norm_zeta_sub_one_eq_eval_cyclotomic
- \- *def* is_cyclotomic_extension.zeta.embeddings_equiv_primitive_roots
- \- *def* is_cyclotomic_extension.zeta.power_basis
- \- *lemma* is_cyclotomic_extension.zeta.power_basis_gen_minpoly
- \- *def* is_cyclotomic_extension.zeta
- \- *lemma* is_cyclotomic_extension.zeta_minpoly
- \- *lemma* is_cyclotomic_extension.zeta_pow
- \- *lemma* is_cyclotomic_extension.zeta_primitive_root
- \- *lemma* is_cyclotomic_extension.zeta_spec'
- \- *lemma* is_cyclotomic_extension.zeta_spec



## [2022-02-10 23:42:56](https://github.com/leanprover-community/mathlib/commit/d487230)
feat(algebra/big_operators): add prod_multiset_count_of_subset ([#11919](https://github.com/leanprover-community/mathlib/pull/11919))
Inspired by [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
Co-Authored-By: Bhavik Mehta <bhavikmehta8@gmail.com>
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_multiset_count_of_subset



## [2022-02-10 20:44:00](https://github.com/leanprover-community/mathlib/commit/fb41da9)
feat(algebra/module/basic): turn implications into iffs ([#11937](https://github.com/leanprover-community/mathlib/pull/11937))
* Turn the following implications into `iff`, rename them accordingly, and make the type arguments explicit (`M` has to be explicit when using it in `rw`, otherwise one will have unsolved type-class arguments)
```
eq_zero_of_two_nsmul_eq_zero -> two_nsmul_eq_zero
eq_zero_of_eq_neg -> self_eq_neg
ne_neg_of_ne_zero -> self_ne_neg
```
* Also add two variants
* Generalize `ne_neg_iff_ne_zero` to work in modules over a ring
#### Estimated changes
Modified src/algebra/module/basic.lean
- \- *lemma* eq_zero_of_eq_neg
- \- *lemma* eq_zero_of_two_nsmul_eq_zero
- \- *lemma* ne_neg_of_ne_zero
- \+ *lemma* neg_eq_self
- \+ *lemma* neg_ne_self
- \+ *lemma* self_eq_neg
- \+ *lemma* self_ne_neg
- \+ *lemma* two_nsmul_eq_zero

Modified src/analysis/normed_space/basic.lean


Modified src/measure_theory/integral/bochner.lean




## [2022-02-10 20:43:58](https://github.com/leanprover-community/mathlib/commit/0929387)
feat(group_theory/group_action/defs): add ext attributes ([#11936](https://github.com/leanprover-community/mathlib/pull/11936))
This adds `ext` attributes to `has_scalar`, `mul_action`, `distrib_mul_action`, `mul_distrib_mul_action`, and `module`.
The `ext` and `ext_iff` lemmas were eventually generated by `category_theory/preadditive/schur.lean` anyway - we may as well generate them much earlier.
The generated lemmas are slightly uglier than the `module_ext` we already have, but it doesn't really seem worth the trouble of writing out the "nice" versions when the `ext` tactic cleans up the mess for us anyway.
#### Estimated changes
Modified src/algebra/group/defs.lean


Modified src/algebra/module/basic.lean
- \+ *lemma* module.ext'
- \- *lemma* module_ext

Modified src/category_theory/preadditive/schur.lean


Modified src/group_theory/group_action/defs.lean


Modified src/number_theory/number_field.lean




## [2022-02-10 20:43:57](https://github.com/leanprover-community/mathlib/commit/007d660)
feat(analysis/inner_product_space/pi_L2): `map_isometry_euclidean_of_orthonormal` ([#11907](https://github.com/leanprover-community/mathlib/pull/11907))
Add a lemma giving the result of `isometry_euclidean_of_orthonormal`
when applied to an orthonormal basis obtained from another orthonormal
basis with `basis.map`.
#### Estimated changes
Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* basis.map_isometry_euclidean_of_orthonormal



## [2022-02-10 20:43:56](https://github.com/leanprover-community/mathlib/commit/923923f)
feat(analysis/special_functions/complex/arg): `arg_mul`, `arg_div` lemmas ([#11903](https://github.com/leanprover-community/mathlib/pull/11903))
Add lemmas about `(arg (x * y) : real.angle)` and `(arg (x / y) : real.angle)`,
along with preparatory lemmas that are like those such as
`arg_mul_cos_add_sin_mul_I` but either don't require the real argument
to be in `Ioc (-π) π` or that take a `real.angle` argument.
I didn't add any lemmas about `arg (x * y)` or `arg (x / y)` as a
real; if such lemmas prove useful in future, it might make sense to
deduce them from the `real.angle` versions.
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.arg_cos_add_sin_mul_I_coe_angle
- \+ *lemma* complex.arg_cos_add_sin_mul_I_eq_mul_fract
- \+ *lemma* complex.arg_cos_add_sin_mul_I_sub
- \+ *lemma* complex.arg_div_coe_angle
- \+ *lemma* complex.arg_mul_coe_angle
- \+ *lemma* complex.arg_mul_cos_add_sin_mul_I_coe_angle
- \+ *lemma* complex.arg_mul_cos_add_sin_mul_I_eq_mul_fract
- \+ *lemma* complex.arg_mul_cos_add_sin_mul_I_sub



## [2022-02-10 20:43:55](https://github.com/leanprover-community/mathlib/commit/1141703)
feat(group_theory/group_action/sub_mul_action): orbit and stabilizer lemmas ([#11899](https://github.com/leanprover-community/mathlib/pull/11899))
Feat: add lemmas for stabilizer and orbit for sub_mul_action
#### Estimated changes
Modified src/group_theory/group_action/sub_mul_action.lean
- \+ *lemma* sub_mul_action.coe_image_orbit
- \+ *lemma* sub_mul_action.stabilizer_of_sub_mul.submonoid
- \+ *lemma* sub_mul_action.stabilizer_of_sub_mul



## [2022-02-10 18:46:21](https://github.com/leanprover-community/mathlib/commit/de70722)
chore(algebra/punit_instances): all actions on punit are central ([#11953](https://github.com/leanprover-community/mathlib/pull/11953))
#### Estimated changes
Modified src/algebra/punit_instances.lean




## [2022-02-10 18:46:20](https://github.com/leanprover-community/mathlib/commit/779d836)
feat(category_theory): variants of Yoneda are fully faithful ([#11950](https://github.com/leanprover-community/mathlib/pull/11950))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean
- \+ *lemma* Module.forget₂_map
- \+ *lemma* Module.forget₂_obj
- \+ *lemma* Module.forget₂_obj_Module_of

Modified src/category_theory/linear/yoneda.lean


Modified src/category_theory/preadditive/yoneda.lean


Modified src/category_theory/whiskering.lean




## [2022-02-10 18:46:19](https://github.com/leanprover-community/mathlib/commit/8012445)
feat(group_theory/subgroup/basic): `subgroup.map_le_map_iff_of_injective` ([#11947](https://github.com/leanprover-community/mathlib/pull/11947))
If `f` is injective, then `H.map f ≤ K.map f ↔ H ≤ K`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.map_le_map_iff_of_injective



## [2022-02-10 18:46:18](https://github.com/leanprover-community/mathlib/commit/c28dc84)
feat(topology/subset_properties): more facts about compact sets ([#11939](https://github.com/leanprover-community/mathlib/pull/11939))
* add `tendsto.is_compact_insert_range_of_cocompact`, `tendsto.is_compact_insert_range_of_cofinite`, and `tendsto.is_compact_insert_range`;
* reuse the former in `alexandroff.compact_space`;
* rename `finite_of_is_compact_of_discrete` to `is_compact.finite_of_discrete`, add `is_compact_iff_finite`;
* add `cocompact_le_cofinite`, `cocompact_eq_cofinite`;
* add `int.cofinite_eq`, add `@[simp]` to `nat.cofinite_eq`;
* add `set.insert_none_range_some`;
* move `is_compact.image_of_continuous_on` and `is_compact_image` up;
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.insert_none_range_some

Modified src/topology/alexandroff.lean


Modified src/topology/instances/real.lean
- \+ *lemma* int.cofinite_eq

Modified src/topology/locally_constant/basic.lean


Modified src/topology/subset_properties.lean
- \+ *lemma* filter.cocompact_eq_cofinite
- \+ *lemma* filter.cocompact_le_cofinite
- \+ *lemma* filter.tendsto.is_compact_insert_range
- \+ *lemma* filter.tendsto.is_compact_insert_range_of_cocompact
- \+ *lemma* filter.tendsto.is_compact_insert_range_of_cofinite
- \- *lemma* finite_of_is_compact_of_discrete
- \+ *lemma* is_compact.finite_of_discrete
- \+ *lemma* is_compact_iff_finite
- \+ *lemma* nat.cocompact_eq



## [2022-02-10 17:14:10](https://github.com/leanprover-community/mathlib/commit/45ab382)
chore(field_theory/galois): make `intermediate_field.fixing_subgroup_equiv` computable ([#11938](https://github.com/leanprover-community/mathlib/pull/11938))
This also golfs and generalizes some results to reuse infrastructure from elsewhere.
In particular, this generalizes:
* `intermediate_field.fixed_field` to `fixed_points.intermediate_field`, where the latter matches the API of `fixed_points.subfield`
* `intermediate_field.fixing_subgroup` to `fixing_subgroup` and `fixing_submonoid`
This removes `open_locale classical` in favor of ensuring the lemmas take in the necessary decidable / fintype arguments.
#### Estimated changes
Modified src/field_theory/fixed.lean


Modified src/field_theory/galois.lean
- \+ *def* fixed_points.intermediate_field
- \+ *def* fixing_subgroup
- \+ *def* fixing_submonoid
- \+/\- *lemma* intermediate_field.finrank_fixed_field_eq_card
- \+/\- *lemma* is_galois.card_fixing_subgroup_eq_finrank

Modified src/field_theory/krull_topology.lean




## [2022-02-10 13:11:46](https://github.com/leanprover-community/mathlib/commit/a86277a)
feat(category_theory/limits): epi equalizer implies equal ([#11873](https://github.com/leanprover-community/mathlib/pull/11873))
#### Estimated changes
Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.eq_of_epi_equalizer
- \+ *lemma* category_theory.limits.eq_of_epi_fork_ι
- \+ *lemma* category_theory.limits.eq_of_mono_coequalizer
- \+ *lemma* category_theory.limits.eq_of_mono_cofork_π



## [2022-02-10 13:11:45](https://github.com/leanprover-community/mathlib/commit/20ef909)
feat(data/part): add instances ([#11868](https://github.com/leanprover-community/mathlib/pull/11868))
Add common instances for `part \alpha` to be inherited from `\alpha`. Spun off of [#11046](https://github.com/leanprover-community/mathlib/pull/11046)
#### Estimated changes
Modified src/computability/halting.lean


Modified src/data/part.lean




## [2022-02-10 13:11:42](https://github.com/leanprover-community/mathlib/commit/3b9dc08)
feat(analysis/complex): add the Cauchy-Goursat theorem for an annulus ([#11864](https://github.com/leanprover-community/mathlib/pull/11864))
#### Estimated changes
Modified src/analysis/complex/cauchy_integral.lean
- \+ *lemma* complex.circle_integral_eq_of_differentiable_on_annulus_off_countable

Modified src/measure_theory/integral/circle_integral.lean
- \+ *lemma* circle_integral.integral_sub_inv_smul_sub_smul
- \+ *lemma* set.countable.preimage_circle_map

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* set.countable.ae_not_mem



## [2022-02-10 13:11:41](https://github.com/leanprover-community/mathlib/commit/efa3157)
feat(order/conditionally_complete_lattice): `cInf_le` variant without redundant assumption ([#11863](https://github.com/leanprover-community/mathlib/pull/11863))
We prove `cInf_le'` on a `conditionally_complete_linear_order_bot`. We no longer need the boundedness assumption.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* cInf_le'
- \+ *theorem* le_cInf_iff''



## [2022-02-10 13:11:40](https://github.com/leanprover-community/mathlib/commit/66d9cc1)
feat(number_theory/cyclotomic/gal): the Galois group of K(ζₙ) ([#11808](https://github.com/leanprover-community/mathlib/pull/11808))
from flt-regular!
#### Estimated changes
Added src/number_theory/cyclotomic/gal.lean
- \+ *lemma* is_cyclotomic_extension.aut_to_pow_injective
- \+ *lemma* is_primitive_root.from_zeta_aut_spec

Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* is_primitive_root.aut_to_pow_spec



## [2022-02-10 13:11:39](https://github.com/leanprover-community/mathlib/commit/1373d54)
feat(group_theory/nilpotent): add nilpotent implies normalizer condition ([#11586](https://github.com/leanprover-community/mathlib/pull/11586))
#### Estimated changes
Modified src/group_theory/nilpotent.lean
- \+ *lemma* normalizer_condition_of_is_nilpotent

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.map_top_of_surjective



## [2022-02-10 13:11:37](https://github.com/leanprover-community/mathlib/commit/c3f6fce)
feat(algebra/group_power/basic): add lemmas about pow and neg on units ([#11447](https://github.com/leanprover-community/mathlib/pull/11447))
In future we might want to add a typeclass for monoids with a well-behaved negation operator to avoid needing to repeat these lemmas. Such a typeclass would also apply to the `unitary` submonoid too.
#### Estimated changes
Modified src/algebra/group/units_hom.lean
- \+ *lemma* units.coe_pow
- \+ *lemma* units.coe_zpow

Modified src/algebra/group_power/basic.lean
- \+ *lemma* units.eq_or_eq_neg_of_sq_eq_sq
- \+ *theorem* units.neg_one_pow_eq_or
- \+ *theorem* units.neg_pow
- \+ *theorem* units.neg_pow_bit0
- \+ *theorem* units.neg_pow_bit1
- \+ *lemma* units.neg_sq

Modified src/algebra/group_power/lemmas.lean
- \- *lemma* units.coe_pow
- \- *lemma* units.coe_zpow

Modified src/algebra/ring/basic.lean
- \+ *theorem* commute.units_neg_left
- \+ *theorem* commute.units_neg_left_iff
- \+ *theorem* commute.units_neg_one_left
- \+ *theorem* commute.units_neg_one_right
- \+ *theorem* commute.units_neg_right
- \+ *theorem* commute.units_neg_right_iff
- \+ *lemma* semiconj_by.units_neg_left
- \+ *lemma* semiconj_by.units_neg_left_iff
- \+ *lemma* semiconj_by.units_neg_one_left
- \+ *lemma* semiconj_by.units_neg_one_right
- \+ *lemma* semiconj_by.units_neg_right
- \+ *lemma* semiconj_by.units_neg_right_iff
- \+ *lemma* units.mul_neg_one
- \+ *lemma* units.neg_mul_eq_mul_neg
- \+ *lemma* units.neg_mul_eq_neg_mul
- \+ *lemma* units.neg_one_mul



## [2022-02-10 13:11:36](https://github.com/leanprover-community/mathlib/commit/c3d8782)
feat(category_theory/bicategory/functor_bicategory): bicategory structure on oplax functors ([#11405](https://github.com/leanprover-community/mathlib/pull/11405))
This PR defines a bicategory structure on the oplax functors between bicategories.
#### Estimated changes
Added src/category_theory/bicategory/functor_bicategory.lean
- \+ *def* category_theory.oplax_nat_trans.associator
- \+ *def* category_theory.oplax_nat_trans.left_unitor
- \+ *def* category_theory.oplax_nat_trans.right_unitor
- \+ *def* category_theory.oplax_nat_trans.whisker_left
- \+ *def* category_theory.oplax_nat_trans.whisker_right



## [2022-02-10 10:46:35](https://github.com/leanprover-community/mathlib/commit/da164c6)
feat (category_theory/karoubi_karoubi) : idempotence of karoubi ([#11931](https://github.com/leanprover-community/mathlib/pull/11931))
In this file, we construct the equivalence of categories
`karoubi_karoubi.equivalence C : karoubi C ≌ karoubi (karoubi C)` for any category `C`.
#### Estimated changes
Added src/category_theory/idempotents/karoubi_karoubi.lean
- \+ *def* category_theory.idempotents.karoubi_karoubi.counit_iso
- \+ *def* category_theory.idempotents.karoubi_karoubi.equivalence
- \+ *def* category_theory.idempotents.karoubi_karoubi.inverse
- \+ *def* category_theory.idempotents.karoubi_karoubi.unit_iso



## [2022-02-10 10:46:34](https://github.com/leanprover-community/mathlib/commit/0490977)
feat(algebra/lie/engel): add proof of Engel's theorem ([#11922](https://github.com/leanprover-community/mathlib/pull/11922))
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/lie/cartan_subalgebra.lean
- \+ *lemma* lie_subalgebra.lie_mem_sup_of_mem_normalizer

Added src/algebra/lie/engel.lean
- \+ *lemma* function.surjective.is_engelian
- \+ *lemma* lie_algebra.exists_engelian_lie_subalgebra_of_lt_normalizer
- \+ *def* lie_algebra.is_engelian
- \+ *lemma* lie_algebra.is_engelian_of_is_noetherian
- \+ *lemma* lie_algebra.is_engelian_of_subsingleton
- \+ *lemma* lie_algebra.is_nilpotent_iff_forall
- \+ *lemma* lie_equiv.is_engelian_iff
- \+ *lemma* lie_module.is_nilpotent_iff_forall
- \+ *lemma* lie_submodule.exists_smul_add_of_span_sup_eq_top
- \+ *lemma* lie_submodule.is_nilpotent_of_is_nilpotent_span_sup_eq_top
- \+ *lemma* lie_submodule.lcs_le_lcs_of_is_nilpotent_span_sup_eq_top
- \+ *lemma* lie_submodule.lie_top_eq_of_span_sup_eq_top

Modified src/algebra/lie/of_associative.lean
- \+ *lemma* lie_subalgebra.to_endomorphism_eq
- \+ *lemma* lie_subalgebra.to_endomorphism_mk
- \+ *lemma* lie_submodule.coe_map_to_endomorphism_le

Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_subalgebra.subsingleton_bot

Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.injective_subtype

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.span_sup
- \+ *lemma* submodule.sup_span



## [2022-02-10 10:46:32](https://github.com/leanprover-community/mathlib/commit/f32fda7)
feat(set_theory/ordinal_arithmetic): More `lsub` and `blsub` lemmas ([#11848](https://github.com/leanprover-community/mathlib/pull/11848))
We prove variants of `sup_typein`, which serve as analogs for `blsub_id`. We also prove `sup_eq_lsub_or_sup_succ_eq_lsub`, which combines `sup_le_lsub` and `lsub_le_sup_succ`.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.blsub_id
- \+ *theorem* ordinal.bsup_eq_blsub_or_succ_bsup_eq_blsub
- \- *theorem* ordinal.bsup_id
- \+ *theorem* ordinal.bsup_id_limit
- \+ *theorem* ordinal.bsup_id_succ
- \+ *theorem* ordinal.lsub_typein
- \+ *theorem* ordinal.sup_eq_lsub_or_sup_succ_eq_lsub
- \+ *theorem* ordinal.sup_typein_limit
- \+ *theorem* ordinal.sup_typein_succ



## [2022-02-10 10:46:31](https://github.com/leanprover-community/mathlib/commit/b7360f9)
feat(group_theory/general_commutator): subgroup.prod commutes with the general_commutator ([#11818](https://github.com/leanprover-community/mathlib/pull/11818))
#### Estimated changes
Modified src/group_theory/general_commutator.lean
- \+ *lemma* general_commutator_prod_prod
- \+ *lemma* map_general_commutator



## [2022-02-10 10:46:28](https://github.com/leanprover-community/mathlib/commit/6afaf36)
feat(algebra/order/hom/ring): Ordered semiring/ring homomorphisms ([#11634](https://github.com/leanprover-community/mathlib/pull/11634))
Define `order_ring_hom` with notation `→+*o` along with its hom class.
#### Estimated changes
Modified src/algebra/order/hom/monoid.lean
- \+/\- *structure* order_add_monoid_hom
- \+/\- *structure* order_monoid_hom
- \+/\- *lemma* order_monoid_with_zero_hom.coe_monoid_with_zero_hom
- \+/\- *lemma* order_monoid_with_zero_hom.coe_order_monoid_hom
- \+/\- *structure* order_monoid_with_zero_hom

Added src/algebra/order/hom/ring.lean
- \+ *lemma* order_ring_hom.cancel_left
- \+ *lemma* order_ring_hom.cancel_right
- \+ *lemma* order_ring_hom.coe_coe_order_add_monoid_hom
- \+ *lemma* order_ring_hom.coe_coe_order_monoid_with_zero_hom
- \+ *lemma* order_ring_hom.coe_coe_ring_hom
- \+ *lemma* order_ring_hom.coe_comp
- \+ *lemma* order_ring_hom.coe_id
- \+ *lemma* order_ring_hom.coe_order_add_monoid_hom_apply
- \+ *lemma* order_ring_hom.coe_order_add_monoid_hom_id
- \+ *lemma* order_ring_hom.coe_order_monoid_with_zero_hom_apply
- \+ *lemma* order_ring_hom.coe_order_monoid_with_zero_hom_id
- \+ *lemma* order_ring_hom.coe_ring_hom_apply
- \+ *lemma* order_ring_hom.coe_ring_hom_id
- \+ *lemma* order_ring_hom.comp_apply
- \+ *lemma* order_ring_hom.comp_assoc
- \+ *lemma* order_ring_hom.comp_id
- \+ *lemma* order_ring_hom.ext
- \+ *lemma* order_ring_hom.id_apply
- \+ *lemma* order_ring_hom.id_comp
- \+ *lemma* order_ring_hom.to_fun_eq_coe
- \+ *def* order_ring_hom.to_order_add_monoid_hom
- \+ *lemma* order_ring_hom.to_order_add_monoid_hom_eq_coe
- \+ *def* order_ring_hom.to_order_monoid_with_zero_hom
- \+ *lemma* order_ring_hom.to_order_monoid_with_zero_hom_eq_coe
- \+ *lemma* order_ring_hom.to_ring_hom_eq_coe
- \+ *structure* order_ring_hom

Modified src/algebra/ring/basic.lean
- \+ *def* ring_hom.copy



## [2022-02-10 09:27:23](https://github.com/leanprover-community/mathlib/commit/8f5fd26)
feat(data/nat/factorization): bijection between positive nats and finsupps over primes ([#11440](https://github.com/leanprover-community/mathlib/pull/11440))
Proof that for any finsupp `f : ℕ →₀ ℕ` whose support is in the primes, `f = (f.prod pow).factorization`, and hence that the positive natural numbers are bijective with finsupps `ℕ →₀ ℕ` with support in the primes.
#### Estimated changes
Modified src/algebra/big_operators/finsupp.lean
- \+ *lemma* nat.prod_pow_pos_of_zero_not_mem_support

Modified src/data/nat/factorization.lean
- \+ *lemma* nat.eq_factorization_iff
- \+ *def* nat.factorization_equiv
- \+ *lemma* nat.factorization_equiv_apply
- \+ *lemma* nat.factorization_equiv_inv_apply
- \+ *lemma* nat.prod_pow_factorization_eq_self



## [2022-02-10 09:27:22](https://github.com/leanprover-community/mathlib/commit/0aa0bc8)
feat(set_theory/ordinal_arithmetic): The derivative of addition ([#11270](https://github.com/leanprover-community/mathlib/pull/11270))
We prove that the derivative of `(+) a` evaluated at `b` is given by `a * ω + b`.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.add_eq_right_iff_mul_omega_le
- \+ *theorem* ordinal.add_le_right_iff_mul_omega_le
- \+ *theorem* ordinal.deriv_add_eq_mul_omega_add
- \+/\- *def* ordinal.family_of_bfamily
- \+/\- *theorem* ordinal.family_of_bfamily_enum
- \+ *theorem* ordinal.is_normal.apply_eq_self_iff_deriv
- \+/\- *theorem* ordinal.is_normal.deriv_fp
- \- *theorem* ordinal.is_normal.fp_iff_deriv'
- \- *theorem* ordinal.is_normal.fp_iff_deriv
- \+ *theorem* ordinal.is_normal.le_iff_deriv
- \+ *theorem* ordinal.is_normal.le_iff_eq
- \+/\- *theorem* ordinal.is_normal.le_nfp
- \+/\- *theorem* ordinal.is_normal.nfp_fp
- \- *theorem* ordinal.is_normal.nfp_le
- \+/\- *theorem* ordinal.is_normal.nfp_le_fp
- \+ *theorem* ordinal.mul_one_add
- \+ *theorem* ordinal.nfp_add_eq_mul_omega
- \+ *theorem* ordinal.nfp_add_zero
- \+/\- *theorem* ordinal.nfp_eq_self
- \+/\- *theorem* ordinal.sup_add_nat
- \+/\- *theorem* ordinal.sup_mul_nat
- \+/\- *theorem* ordinal.sup_nat_cast



## [2022-02-10 08:34:06](https://github.com/leanprover-community/mathlib/commit/e60ca6b)
feat(data/real/ennreal): `inv` is an `order_iso` to the order dual and lemmas for `supr, infi` ([#11869](https://github.com/leanprover-community/mathlib/pull/11869))
Establishes that `inv` is an order isomorphism to the order dual. We then provide some convenience lemmas which guarantee that `inv` switches `supr` and `infi` and hence also switches `limsup` and `liminf`.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *def* ennreal.inv_order_iso
- \+ *lemma* ennreal.inv_order_iso_symm_apply

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.inv_liminf
- \+ *lemma* ennreal.inv_limsup
- \+ *lemma* ennreal.inv_map_infi
- \+ *lemma* ennreal.inv_map_supr



## [2022-02-10 08:34:05](https://github.com/leanprover-community/mathlib/commit/b7e72ea)
feat(measure_theory/probability_mass_function): Measure calculations for additional pmf constructions ([#11858](https://github.com/leanprover-community/mathlib/pull/11858))
This PR adds calculations of the measures of sets under various `pmf` constructions.
#### Estimated changes
Modified src/measure_theory/probability_mass_function/constructions.lean
- \+ *lemma* pmf.mem_support_uniform_of_fintype
- \- *lemma* pmf.mem_support_uniform_of_fintype_iff
- \+/\- *lemma* pmf.support_uniform_of_fintype
- \+ *lemma* pmf.to_measure_map_apply
- \+ *lemma* pmf.to_measure_of_finset_apply
- \+ *lemma* pmf.to_measure_of_fintype_apply
- \+ *lemma* pmf.to_measure_of_multiset_apply
- \+ *lemma* pmf.to_measure_uniform_of_finset_apply
- \+ *lemma* pmf.to_measure_uniform_of_fintype_apply
- \+ *lemma* pmf.to_outer_measure_map_apply
- \+ *lemma* pmf.to_outer_measure_of_finset_apply
- \+ *lemma* pmf.to_outer_measure_of_fintype_apply
- \+ *lemma* pmf.to_outer_measure_of_multiset_apply
- \+ *lemma* pmf.to_outer_measure_uniform_of_finset_apply
- \+ *lemma* pmf.to_outer_measure_uniform_of_fintype_apply

Modified src/measure_theory/probability_mass_function/monad.lean
- \+/\- *lemma* pmf.to_measure_bind_apply
- \+/\- *lemma* pmf.to_measure_bind_on_support_apply
- \+/\- *lemma* pmf.to_measure_pure_apply
- \+/\- *lemma* pmf.to_outer_measure_bind_apply
- \+/\- *lemma* pmf.to_outer_measure_bind_on_support_apply
- \+/\- *lemma* pmf.to_outer_measure_pure_apply



## [2022-02-10 08:04:04](https://github.com/leanprover-community/mathlib/commit/e9a1893)
chore(tactic/default): import `linear_combination` ([#11942](https://github.com/leanprover-community/mathlib/pull/11942))
#### Estimated changes
Modified src/tactic/default.lean




## [2022-02-10 03:40:32](https://github.com/leanprover-community/mathlib/commit/ea0e458)
refactor(topology/algebra/mul_action2): rename type classes ([#11940](https://github.com/leanprover-community/mathlib/pull/11940))
Rename `has_continuous_smul₂` and `has_continuous_vadd₂` to
`has_continuous_const_smul` and `has_continuous_const_vadd`,
respectively.
#### Estimated changes
Modified src/topology/algebra/group.lean


Modified src/topology/algebra/mul_action.lean


Modified src/topology/algebra/mul_action2.lean
- \+/\- *lemma* is_open_map_quotient_mk_mul



## [2022-02-09 23:10:35](https://github.com/leanprover-community/mathlib/commit/4e8d8fa)
feat(order/hom/bounded): Bounded order homomorphisms ([#11806](https://github.com/leanprover-community/mathlib/pull/11806))
Define `bounded_order_hom` in `order.hom.bounded` and move `top_hom`, `bot_hom` there.
#### Estimated changes
Modified src/order/hom/basic.lean


Added src/order/hom/bounded.lean
- \+ *lemma* bot_hom.bot_apply
- \+ *lemma* bot_hom.cancel_left
- \+ *lemma* bot_hom.cancel_right
- \+ *lemma* bot_hom.coe_bot
- \+ *lemma* bot_hom.coe_comp
- \+ *lemma* bot_hom.coe_id
- \+ *lemma* bot_hom.coe_inf
- \+ *lemma* bot_hom.coe_sup
- \+ *def* bot_hom.comp
- \+ *lemma* bot_hom.comp_apply
- \+ *lemma* bot_hom.comp_assoc
- \+ *lemma* bot_hom.comp_id
- \+ *lemma* bot_hom.ext
- \+ *lemma* bot_hom.id_apply
- \+ *lemma* bot_hom.id_comp
- \+ *lemma* bot_hom.inf_apply
- \+ *lemma* bot_hom.sup_apply
- \+ *lemma* bot_hom.to_fun_eq_coe
- \+ *structure* bot_hom
- \+ *lemma* bounded_order_hom.cancel_left
- \+ *lemma* bounded_order_hom.cancel_right
- \+ *lemma* bounded_order_hom.coe_comp
- \+ *lemma* bounded_order_hom.coe_comp_bot_hom
- \+ *lemma* bounded_order_hom.coe_comp_order_hom
- \+ *lemma* bounded_order_hom.coe_comp_top_hom
- \+ *lemma* bounded_order_hom.coe_id
- \+ *def* bounded_order_hom.comp
- \+ *lemma* bounded_order_hom.comp_apply
- \+ *lemma* bounded_order_hom.comp_assoc
- \+ *lemma* bounded_order_hom.comp_id
- \+ *lemma* bounded_order_hom.ext
- \+ *lemma* bounded_order_hom.id_apply
- \+ *lemma* bounded_order_hom.id_comp
- \+ *def* bounded_order_hom.to_bot_hom
- \+ *lemma* bounded_order_hom.to_fun_eq_coe
- \+ *def* bounded_order_hom.to_top_hom
- \+ *structure* bounded_order_hom
- \+ *lemma* top_hom.cancel_left
- \+ *lemma* top_hom.cancel_right
- \+ *lemma* top_hom.coe_comp
- \+ *lemma* top_hom.coe_id
- \+ *lemma* top_hom.coe_inf
- \+ *lemma* top_hom.coe_sup
- \+ *lemma* top_hom.coe_top
- \+ *def* top_hom.comp
- \+ *lemma* top_hom.comp_apply
- \+ *lemma* top_hom.comp_assoc
- \+ *lemma* top_hom.comp_id
- \+ *lemma* top_hom.ext
- \+ *lemma* top_hom.id_apply
- \+ *lemma* top_hom.id_comp
- \+ *lemma* top_hom.inf_apply
- \+ *lemma* top_hom.sup_apply
- \+ *lemma* top_hom.to_fun_eq_coe
- \+ *lemma* top_hom.top_apply
- \+ *structure* top_hom

Modified src/order/hom/lattice.lean
- \- *lemma* bot_hom.bot_apply
- \- *lemma* bot_hom.cancel_left
- \- *lemma* bot_hom.cancel_right
- \- *lemma* bot_hom.coe_bot
- \- *lemma* bot_hom.coe_comp
- \- *lemma* bot_hom.coe_id
- \- *lemma* bot_hom.coe_inf
- \- *lemma* bot_hom.coe_sup
- \- *def* bot_hom.comp
- \- *lemma* bot_hom.comp_apply
- \- *lemma* bot_hom.comp_assoc
- \- *lemma* bot_hom.comp_id
- \- *lemma* bot_hom.ext
- \- *lemma* bot_hom.id_apply
- \- *lemma* bot_hom.id_comp
- \- *lemma* bot_hom.inf_apply
- \- *lemma* bot_hom.sup_apply
- \- *lemma* bot_hom.to_fun_eq_coe
- \- *structure* bot_hom
- \- *def* bounded_lattice_hom.to_bot_hom
- \+ *def* bounded_lattice_hom.to_bounded_order_hom
- \- *def* bounded_lattice_hom.to_top_hom
- \+/\- *lemma* inf_hom.cancel_left
- \+/\- *lemma* inf_hom.cancel_right
- \+/\- *lemma* lattice_hom.cancel_left
- \+/\- *lemma* lattice_hom.cancel_right
- \+/\- *lemma* sup_hom.cancel_left
- \+/\- *lemma* sup_hom.cancel_right
- \- *lemma* top_hom.cancel_left
- \- *lemma* top_hom.cancel_right
- \- *lemma* top_hom.coe_comp
- \- *lemma* top_hom.coe_id
- \- *lemma* top_hom.coe_inf
- \- *lemma* top_hom.coe_sup
- \- *lemma* top_hom.coe_top
- \- *def* top_hom.comp
- \- *lemma* top_hom.comp_apply
- \- *lemma* top_hom.comp_assoc
- \- *lemma* top_hom.comp_id
- \- *lemma* top_hom.ext
- \- *lemma* top_hom.id_apply
- \- *lemma* top_hom.id_comp
- \- *lemma* top_hom.inf_apply
- \- *lemma* top_hom.sup_apply
- \- *lemma* top_hom.to_fun_eq_coe
- \- *lemma* top_hom.top_apply
- \- *structure* top_hom



## [2022-02-09 21:35:24](https://github.com/leanprover-community/mathlib/commit/4691159)
doc(algebra/group/hom_instances): Fix spellings ([#11943](https://github.com/leanprover-community/mathlib/pull/11943))
Fixes spelling mistakes introduced by [#11843](https://github.com/leanprover-community/mathlib/pull/11843)
#### Estimated changes
Modified src/algebra/group/hom_instances.lean




## [2022-02-09 20:38:41](https://github.com/leanprover-community/mathlib/commit/352e064)
feat(topology/uniform_space/cauchy): add a few lemmas ([#11912](https://github.com/leanprover-community/mathlib/pull/11912))
#### Estimated changes
Modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy.ultrafilter_of
- \+ *lemma* complete_space_iff_ultrafilter
- \- *lemma* is_compact.is_complete
- \+ *lemma* is_complete_iff_cluster_pt
- \+ *lemma* is_complete_iff_ultrafilter'
- \+ *lemma* is_complete_iff_ultrafilter



## [2022-02-09 18:57:12](https://github.com/leanprover-community/mathlib/commit/2b9aca7)
feat(topology): a few more results about compact sets ([#11905](https://github.com/leanprover-community/mathlib/pull/11905))
* Also a few lemmas about sets and `mul_support`.
#### Estimated changes
Modified src/algebra/support.lean
- \+ *lemma* function.disjoint_mul_support_iff
- \+ *lemma* function.mul_support_disjoint_iff

Modified src/data/set/basic.lean
- \+ *lemma* set.compl_ne_univ
- \+ *lemma* set.not_mem_compl_iff

Modified src/topology/algebra/group.lean
- \+ *lemma* is_compact.inv

Modified src/topology/algebra/monoid.lean
- \+ *lemma* is_compact.mul

Modified src/topology/separation.lean
- \+ *lemma* exists_compact_superset_iff



## [2022-02-09 18:57:10](https://github.com/leanprover-community/mathlib/commit/b8fb8e5)
feat(set_theory/ordinal_arithmetic): `le_one_iff` ([#11847](https://github.com/leanprover-community/mathlib/pull/11847))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.le_one_iff



## [2022-02-09 18:57:09](https://github.com/leanprover-community/mathlib/commit/2726e23)
feat(algebra.group.hom_instances): Define left and right multiplication operators ([#11843](https://github.com/leanprover-community/mathlib/pull/11843))
Defines left and right multiplication operators on non unital, non associative semirings.
Suggested by @ocfnash for [#11073](https://github.com/leanprover-community/mathlib/pull/11073)
#### Estimated changes
Modified src/algebra/group/hom_instances.lean
- \+ *def* add_monoid.End.mul_left
- \+ *def* add_monoid.End.mul_right



## [2022-02-09 17:14:15](https://github.com/leanprover-community/mathlib/commit/5008de8)
feat(order): some properties about monotone predicates ([#11904](https://github.com/leanprover-community/mathlib/pull/11904))
* We prove that some predicates are monotone/antitone w.r.t. some order. The proofs are all trivial.
* We prove 2 `iff` statements depending on the hypothesis that a certain predicate is (anti)mono: `exists_ge_and_iff_exists` and `filter.exists_mem_and_iff`)
* The former is used to prove `bdd_above_iff_exists_ge`, the latter will be used in a later PR.
#### Estimated changes
Modified src/order/bounded_order.lean
- \+ *lemma* antitone.ball
- \+ *lemma* antitone.forall
- \+ *lemma* antitone_le
- \+ *lemma* antitone_lt
- \+ *lemma* exists_ge_and_iff_exists
- \+ *lemma* exists_le_and_iff_exists
- \+ *lemma* monotone.ball
- \+ *lemma* monotone.forall
- \+ *lemma* monotone_le
- \+ *lemma* monotone_lt

Modified src/order/bounds.lean
- \+ *lemma* bdd_above.exists_ge
- \+ *lemma* bdd_above_def
- \+ *lemma* bdd_above_iff_exists_ge
- \+ *lemma* bdd_below.exists_le
- \+ *lemma* bdd_below_def
- \+ *lemma* bdd_below_iff_exists_le

Modified src/order/filter/basic.lean
- \+ *lemma* filter.exists_mem_and_iff

Modified src/topology/continuous_on.lean
- \+ *lemma* antitone_continuous_on



## [2022-02-09 17:14:14](https://github.com/leanprover-community/mathlib/commit/d3cdcd8)
feat(order/filter/basic): add lemma `le_prod_map_fst_snd` ([#11901](https://github.com/leanprover-community/mathlib/pull/11901))
A lemma relating filters on products and the filter-product of the projections. This lemma is particularly useful when proving the continuity of a function on a product space using filters.
Discussion: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Some.20missing.20prod.20stuff
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* filter.le_prod_map_fst_snd



## [2022-02-09 17:14:12](https://github.com/leanprover-community/mathlib/commit/9648ce2)
chore(data/pi): add pi.prod and use elsewhere ([#11877](https://github.com/leanprover-community/mathlib/pull/11877))
`pi.prod` is the function that underlies `add_monoid_hom.prod`, `linear_map.prod`, etc.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Some.20missing.20prod.20stuff/near/270851797)
#### Estimated changes
Modified archive/sensitivity.lean


Modified src/algebra/big_operators/basic.lean
- \+ *lemma* monoid_hom.coe_finset_prod
- \- *lemma* monoid_hom.coe_prod

Modified src/algebra/direct_sum/ring.lean


Modified src/algebra/group/prod.lean
- \+ *lemma* monoid_hom.coe_prod

Modified src/algebra/triv_sq_zero_ext.lean


Modified src/data/dfinsupp/basic.lean


Modified src/data/finsupp/basic.lean


Modified src/data/pi.lean
- \+ *lemma* pi.prod_fst_snd
- \+ *lemma* pi.prod_snd_fst

Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/prod.lean
- \+ *lemma* linear_map.coe_prod

Modified src/topology/algebra/group.lean




## [2022-02-09 15:50:47](https://github.com/leanprover-community/mathlib/commit/ca2450f)
feat(order/atoms): finite orders are (co)atomic ([#11930](https://github.com/leanprover-community/mathlib/pull/11930))
#### Estimated changes
Modified src/order/atoms.lean


Modified src/order/minimal.lean




## [2022-02-09 14:10:33](https://github.com/leanprover-community/mathlib/commit/c882753)
chore(algebra/tropical/basic): remove 3 instances ([#11920](https://github.com/leanprover-community/mathlib/pull/11920))
The three removed instances are
* `covariant_swap_add` (exists since addition is commutative and the non-swapped version is proved);
* `covariant_add_lt` (as is, this is a copy of `covariant_add` -- judging from the name, it could have been intended to have a `(<)`, but with `(<)` it is false, see below);
* `covariant_swap_add_lt` (exists since addition is commutative and the non-swapped version is proved).
Here is a proof that the second instance with `(<)` is false:
```lean
lemma not_cov_lt : ¬ covariant_class (tropical ℕ) (tropical ℕ) (+) (<) :=
begin
  refine λ h, (lt_irrefl (trop 0) _),
  cases h,
  have : trop 0 < trop 1 := show 0 < 1, from zero_lt_one,
  calc trop 0 = trop 0 + trop 0 : (trop 0).add_self.symm
          ... < trop 0 + trop 1 : h _ this
          ... = trop 0          : add_eq_left this.le,
end
```
#### Estimated changes
Modified src/algebra/tropical/basic.lean




## [2022-02-09 11:36:35](https://github.com/leanprover-community/mathlib/commit/fea68aa)
chore(data/fintype/basic): documenting elaboration bug ([#11247](https://github.com/leanprover-community/mathlib/pull/11247))
Simplifying an expression and documenting an elaboration bug that it was avoiding.
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+/\- *lemma* set.to_finset_univ



## [2022-02-09 09:56:15](https://github.com/leanprover-community/mathlib/commit/3aa5b8a)
refactor(algebra/ring/basic): rename lemmas about `a*(-b)` and `(-a)*b` ([#11925](https://github.com/leanprover-community/mathlib/pull/11925))
This renames:
* `(- a) * b = - (a * b)` from `neg_mul_eq_neg_mul_symm` to `neg_mul`
* `a * (-b) = - (a * b)` from `mul_neg_eq_neg_mul_symm` to `mul_neg`
The new names are much easier to find when compared with `sub_mul`, `mul_sub` etc, and match the existing namespaced names under `units` and `matrix`.
This also replaces rewrites by `← neg_mul_eq_neg_mul` with `neg_mul` and rewrites by `← neg_mul_eq_mul_neg` with `mul_neg`.
To avoid clashes, the names in the `matrix` namespace are now `protected`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/mul_neg.2C.20neg_mul/near/233638226)
#### Estimated changes
Modified src/algebra/field/basic.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group_power/basic.lean


Modified src/algebra/order/field.lean


Modified src/algebra/order/ring.lean


Modified src/algebra/quaternion.lean


Modified src/algebra/quaternion_basis.lean


Modified src/algebra/ring/basic.lean
- \+ *lemma* mul_neg
- \- *lemma* mul_neg_eq_neg_mul_symm
- \+ *lemma* neg_mul
- \- *lemma* neg_mul_eq_neg_mul_symm

Modified src/algebra/star/chsh.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/algebraic_topology/alternating_face_map_complex.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/lhopital.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/inner_product_space/basic.lean


Modified src/analysis/normed_space/extend.lean


Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/units.lean


Modified src/analysis/special_functions/complex/log.lean


Modified src/analysis/special_functions/integrals.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/complex/is_R_or_C.lean


Modified src/data/int/basic.lean


Modified src/data/int/gcd.lean


Modified src/data/int/modeq.lean


Modified src/data/matrix/basic.lean
- \- *theorem* matrix.mul_neg
- \- *theorem* matrix.neg_mul

Modified src/data/polynomial/field_division.lean


Modified src/data/rat/basic.lean


Modified src/field_theory/ratfunc.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/specific_groups/quaternion.lean


Modified src/linear_algebra/adic_completion.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/matrix/determinant.lean


Modified src/linear_algebra/orientation.lean


Modified src/linear_algebra/quadratic_form/basic.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/modular.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/ring_theory/coprime/basic.lean


Modified src/ring_theory/henselian.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/jacobson_ideal.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/polynomial/cyclotomic/basic.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/tactic/noncomm_ring.lean


Modified src/tactic/omega/int/preterm.lean


Modified src/tactic/ring.lean


Modified src/topology/continuous_function/polynomial.lean


Modified test/matrix.lean




## [2022-02-09 08:51:48](https://github.com/leanprover-community/mathlib/commit/4e17e08)
feat(data/complex/basic): re-im set product ([#11770](https://github.com/leanprover-community/mathlib/pull/11770))
`set.re_im_prod s t` (notation: `s ×ℂ t`) is the product of a set on the real axis and a set on the
imaginary axis of the complex plane.
#### Estimated changes
Modified src/analysis/complex/cauchy_integral.lean


Modified src/analysis/complex/re_im_topology.lean
- \- *lemma* complex.closure_preimage_re_inter_preimage_im
- \+ *lemma* complex.closure_re_prod_im
- \- *lemma* complex.frontier_preimage_re_inter_preimage_im
- \+ *lemma* complex.frontier_re_prod_im
- \- *lemma* complex.interior_preimage_re_inter_preimage_im
- \+ *lemma* complex.interior_re_prod_im
- \+/\- *lemma* is_open.re_prod_im

Modified src/data/complex/basic.lean
- \+ *def* set.re_prod_im



## [2022-02-09 07:16:44](https://github.com/leanprover-community/mathlib/commit/78c3975)
feat(category_theory/pseudoabelian/basic): basic facts and contructions about pseudoabelian categories ([#11817](https://github.com/leanprover-community/mathlib/pull/11817))
#### Estimated changes
Added src/category_theory/idempotents/basic.lean
- \+ *lemma* category_theory.idempotents.equivalence.is_idempotent_complete
- \+ *lemma* category_theory.idempotents.idempotence_of_id_sub_idempotent
- \+ *lemma* category_theory.idempotents.is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent
- \+ *lemma* category_theory.idempotents.is_idempotent_complete_iff_idempotents_have_kernels
- \+ *lemma* category_theory.idempotents.is_idempotent_complete_iff_of_equivalence
- \+ *lemma* category_theory.idempotents.is_idempotent_complete_iff_opposite
- \+ *lemma* category_theory.idempotents.is_idempotent_complete_of_is_idempotent_complete_opposite
- \+ *lemma* category_theory.idempotents.split_iff_of_iso
- \+ *lemma* category_theory.idempotents.split_imp_of_iso

Added src/category_theory/idempotents/karoubi.lean
- \+ *lemma* category_theory.idempotents.karoubi.coe_X
- \+ *lemma* category_theory.idempotents.karoubi.coe_p
- \+ *lemma* category_theory.idempotents.karoubi.comp
- \+ *lemma* category_theory.idempotents.karoubi.comp_p
- \+ *lemma* category_theory.idempotents.karoubi.comp_proof
- \+ *lemma* category_theory.idempotents.karoubi.decomp_id
- \+ *def* category_theory.idempotents.karoubi.decomp_id_i
- \+ *lemma* category_theory.idempotents.karoubi.decomp_id_i_naturality
- \+ *lemma* category_theory.idempotents.karoubi.decomp_id_i_to_karoubi
- \+ *def* category_theory.idempotents.karoubi.decomp_id_p
- \+ *lemma* category_theory.idempotents.karoubi.decomp_id_p_naturality
- \+ *lemma* category_theory.idempotents.karoubi.decomp_id_p_to_karoubi
- \+ *lemma* category_theory.idempotents.karoubi.decomp_p
- \+ *lemma* category_theory.idempotents.karoubi.eq_to_hom_f
- \+ *lemma* category_theory.idempotents.karoubi.ext
- \+ *structure* category_theory.idempotents.karoubi.hom
- \+ *lemma* category_theory.idempotents.karoubi.hom_eq_zero_iff
- \+ *lemma* category_theory.idempotents.karoubi.hom_ext
- \+ *lemma* category_theory.idempotents.karoubi.id_eq
- \+ *def* category_theory.idempotents.karoubi.inclusion_hom
- \+ *lemma* category_theory.idempotents.karoubi.p_comm
- \+ *lemma* category_theory.idempotents.karoubi.p_comp
- \+ *lemma* category_theory.idempotents.karoubi.sum_hom
- \+ *structure* category_theory.idempotents.karoubi
- \+ *def* category_theory.idempotents.to_karoubi
- \+ *def* category_theory.idempotents.to_karoubi_is_equivalence

Modified src/category_theory/preadditive/default.lean
- \+ *lemma* category_theory.preadditive.has_kernel_of_has_equalizer



## [2022-02-08 22:14:40](https://github.com/leanprover-community/mathlib/commit/56db7ed)
feat(analysis/normed_space/basic): add lemmas `nnnorm_mul_le` and `nnnorm_pow_succ_le` ([#11915](https://github.com/leanprover-community/mathlib/pull/11915))
Adds two convenience lemmas for `nnnorm`, submultiplicativity of `nnnorm` for semi-normed rings and the corresponding extension to powers. We only allow successors so as not to incur the `norm_one_class` type class constraint.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnnorm_mul_le
- \+ *lemma* nnnorm_pow_le'
- \+ *lemma* nnnorm_pow_le
- \+/\- *lemma* norm_pow_le'
- \+/\- *lemma* norm_pow_le



## [2022-02-08 21:07:37](https://github.com/leanprover-community/mathlib/commit/a3d6b43)
feat(topology/algebra/uniform_group): `cauchy_seq.const_mul` and friends ([#11917](https://github.com/leanprover-community/mathlib/pull/11917))
A Cauchy sequence multiplied by a constant (including `-1`) remains a Cauchy sequence.
#### Estimated changes
Modified src/topology/algebra/uniform_group.lean
- \+ *lemma* cauchy_seq.const_mul
- \+ *lemma* cauchy_seq.inv
- \+ *lemma* cauchy_seq.mul_const

Modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* cauchy_seq_const



## [2022-02-08 19:01:57](https://github.com/leanprover-community/mathlib/commit/4545e31)
feat(model_theory/substructures): More operations on substructures ([#11906](https://github.com/leanprover-community/mathlib/pull/11906))
Defines the substructure `first_order.language.hom.range`.
Defines the homomorphisms `first_order.language.hom.dom_restrict` and `first_order.language.hom.cod_restrict`, and the embeddings `first_order.language.embedding.dom_restrict`, `first_order.language.embedding.cod_restrict` which restrict the domain or codomain of a first-order hom or embedding to a substructure.
Defines the embedding `first_order.language.substructure.inclusion` between nested substructures.
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.embedding.comp_to_hom

Modified src/model_theory/substructures.lean
- \+ *def* first_order.language.embedding.cod_restrict
- \+ *theorem* first_order.language.embedding.cod_restrict_apply
- \+ *lemma* first_order.language.embedding.comp_cod_restrict
- \+ *def* first_order.language.embedding.dom_restrict
- \+ *lemma* first_order.language.embedding.dom_restrict_apply
- \+ *lemma* first_order.language.embedding.equiv_range_apply
- \+ *lemma* first_order.language.embedding.substructure_equiv_map_apply
- \+ *lemma* first_order.language.embedding.subtype_comp_cod_restrict
- \+ *lemma* first_order.language.equiv.to_hom_range
- \+ *def* first_order.language.hom.cod_restrict
- \+ *lemma* first_order.language.hom.comp_cod_restrict
- \+ *def* first_order.language.hom.dom_restrict
- \+ *lemma* first_order.language.hom.map_le_range
- \+ *theorem* first_order.language.hom.mem_range
- \+ *theorem* first_order.language.hom.mem_range_self
- \+ *def* first_order.language.hom.range
- \+ *theorem* first_order.language.hom.range_coe
- \+ *theorem* first_order.language.hom.range_comp
- \+ *theorem* first_order.language.hom.range_comp_le_range
- \+ *lemma* first_order.language.hom.range_eq_map
- \+ *theorem* first_order.language.hom.range_eq_top
- \+ *theorem* first_order.language.hom.range_id
- \+ *lemma* first_order.language.hom.range_le_iff_comap
- \+ *lemma* first_order.language.hom.subtype_comp_cod_restrict
- \+ *lemma* first_order.language.substructure.closure_image
- \+ *lemma* first_order.language.substructure.coe_inclusion
- \+ *def* first_order.language.substructure.inclusion
- \+ *lemma* first_order.language.substructure.map_closure
- \+ *lemma* first_order.language.substructure.range_subtype



## [2022-02-08 17:19:13](https://github.com/leanprover-community/mathlib/commit/1ae8304)
chore(*): update to lean 3.39.1c ([#11926](https://github.com/leanprover-community/mathlib/pull/11926))
#### Estimated changes
Modified leanpkg.toml




## [2022-02-08 13:50:04](https://github.com/leanprover-community/mathlib/commit/b1269b0)
chore(algebra/order/ring): add a few aliases ([#11911](https://github.com/leanprover-community/mathlib/pull/11911))
Add aliases `one_pos`, `two_pos`, `three_pos`, and `four_pos`.
We used to have (some of) these lemmas. They were removed during one of cleanups but it doesn't hurt to have aliases.
#### Estimated changes
Modified src/algebra/order/ring.lean


Modified src/data/list/basic.lean




## [2022-02-08 12:43:42](https://github.com/leanprover-community/mathlib/commit/85d9f21)
feat(*): localized `R[X]` notation for `polynomial R` ([#11895](https://github.com/leanprover-community/mathlib/pull/11895))
I did not change `polynomial (complex_term_here taking args)` in many places because I thought it would be more confusing. Also, in some files that prove things about polynomials incidentally, I also did not include the notation and change the files.
#### Estimated changes
Modified archive/100-theorems-list/16_abel_ruffini.lean


Modified src/algebra/algebra/spectrum.lean
- \+/\- *lemma* spectrum.exists_mem_of_not_is_unit_aeval_prod
- \+/\- *theorem* spectrum.map_polynomial_aeval_of_degree_pos
- \+/\- *theorem* spectrum.map_polynomial_aeval_of_nonempty
- \+/\- *theorem* spectrum.subset_polynomial_aeval

Modified src/algebra/cubic_discriminant.lean
- \+/\- *def* cubic.equiv
- \+/\- *def* cubic.to_poly

Modified src/algebra/linear_recurrence.lean
- \+/\- *def* linear_recurrence.char_poly

Modified src/algebra/polynomial/big_operators.lean
- \+/\- *lemma* polynomial.coeff_list_prod_of_nat_degree_le
- \+/\- *lemma* polynomial.coeff_prod_of_nat_degree_le
- \+/\- *lemma* polynomial.degree_list_prod_le
- \+/\- *lemma* polynomial.degree_list_sum_le
- \+/\- *lemma* polynomial.nat_degree_list_prod_le
- \+/\- *lemma* polynomial.nat_degree_list_sum_le
- \+/\- *lemma* polynomial.nat_degree_multiset_prod
- \+/\- *lemma* polynomial.nat_degree_multiset_sum_le
- \+/\- *lemma* polynomial.nat_degree_sum_le

Modified src/algebra/polynomial/group_ring_action.lean
- \+/\- *theorem* polynomial.eval_smul'
- \+/\- *lemma* polynomial.smul_X
- \+/\- *theorem* polynomial.smul_eval
- \+/\- *theorem* polynomial.smul_eval_smul

Modified src/algebraic_geometry/prime_spectrum/is_open_comap_C.lean
- \+/\- *lemma* algebraic_geometry.polynomial.comap_C_mem_image_of_Df

Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/local_extr.lean
- \+/\- *lemma* polynomial.card_root_set_le_derivative

Modified src/analysis/special_functions/polynomials.lean


Modified src/data/mv_polynomial/equiv.lean
- \+/\- *def* mv_polynomial.option_equiv_right
- \+/\- *def* mv_polynomial.punit_alg_equiv

Modified src/data/polynomial/algebra_map.lean
- \+/\- *lemma* polynomial.adjoin_X
- \+/\- *def* polynomial.aeval
- \+/\- *lemma* polynomial.aeval_X
- \+/\- *theorem* polynomial.aeval_X_left
- \+/\- *lemma* polynomial.aeval_X_pow
- \+/\- *theorem* polynomial.aeval_alg_equiv_apply
- \+/\- *theorem* polynomial.aeval_alg_hom_apply
- \+/\- *lemma* polynomial.aeval_algebra_map_apply
- \+/\- *theorem* polynomial.aeval_def
- \+/\- *lemma* polynomial.aeval_eq_sum_range'
- \+/\- *lemma* polynomial.aeval_eq_sum_range
- \+/\- *lemma* polynomial.aeval_fn_apply
- \+/\- *lemma* polynomial.aeval_nat_cast
- \+/\- *lemma* polynomial.aeval_one
- \+/\- *lemma* polynomial.aeval_sum
- \+/\- *def* polynomial.aeval_tower
- \+/\- *lemma* polynomial.aeval_tower_comp_C
- \+/\- *lemma* polynomial.aeval_zero
- \+/\- *lemma* polynomial.alg_hom_ext
- \+/\- *lemma* polynomial.coeff_zero_eq_aeval_zero'
- \+/\- *lemma* polynomial.coeff_zero_eq_aeval_zero
- \+/\- *lemma* polynomial.dvd_term_of_dvd_eval_of_dvd_terms
- \+/\- *lemma* polynomial.dvd_term_of_is_root_of_dvd_terms
- \+/\- *lemma* polynomial.eval_mul_X_sub_C
- \+/\- *theorem* polynomial.eval_unique
- \+/\- *lemma* polynomial.eval₂_int_cast_ring_hom_X
- \+/\- *lemma* polynomial.is_root_of_aeval_algebra_map_eq_zero
- \+/\- *def* polynomial.to_finsupp_iso_alg

Modified src/data/polynomial/basic.lean
- \+/\- *def* polynomial.C
- \+/\- *lemma* polynomial.C_eq_nat_cast
- \+/\- *def* polynomial.X
- \+/\- *lemma* polynomial.X_ne_zero
- \+/\- *lemma* polynomial.add_hom_ext'
- \+/\- *lemma* polynomial.add_hom_ext
- \+/\- *lemma* polynomial.add_to_finsupp
- \+/\- *def* polynomial.coeff
- \+/\- *lemma* polynomial.coeff_X
- \+/\- *lemma* polynomial.coeff_X_of_ne_one
- \+/\- *lemma* polynomial.coeff_X_one
- \+/\- *lemma* polynomial.coeff_X_zero
- \+/\- *lemma* polynomial.coeff_erase
- \+/\- *lemma* polynomial.coeff_neg
- \+/\- *lemma* polynomial.coeff_one_zero
- \+/\- *lemma* polynomial.coeff_sub
- \+/\- *lemma* polynomial.coeff_update
- \+/\- *lemma* polynomial.coeff_update_apply
- \+/\- *lemma* polynomial.coeff_update_ne
- \+/\- *lemma* polynomial.coeff_update_same
- \+/\- *lemma* polynomial.coeff_zero
- \+/\- *lemma* polynomial.commute_X
- \+/\- *lemma* polynomial.commute_X_pow
- \+/\- *lemma* polynomial.eq_zero_of_eq_zero
- \+/\- *lemma* polynomial.erase_ne
- \+/\- *lemma* polynomial.erase_same
- \+/\- *lemma* polynomial.erase_zero
- \+/\- *lemma* polynomial.exists_iff_exists_finsupp
- \+/\- *lemma* polynomial.ext
- \+/\- *theorem* polynomial.ext_iff
- \+/\- *lemma* polynomial.forall_iff_forall_finsupp
- \+/\- *lemma* polynomial.lhom_ext'
- \+/\- *def* polynomial.monomial
- \+/\- *lemma* polynomial.monomial_add_erase
- \+/\- *def* polynomial.monomial_fun
- \+/\- *lemma* polynomial.mul_to_finsupp
- \+/\- *lemma* polynomial.nat_cast_mul
- \+/\- *lemma* polynomial.neg_to_finsupp
- \+/\- *lemma* polynomial.one_to_finsupp
- \+/\- *def* polynomial.op_ring_equiv
- \+/\- *def* polynomial.sum
- \+/\- *lemma* polynomial.sum_add'
- \+/\- *lemma* polynomial.sum_add
- \+/\- *lemma* polynomial.sum_add_index
- \+/\- *lemma* polynomial.sum_def
- \+/\- *lemma* polynomial.sum_eq_of_subset
- \+/\- *lemma* polynomial.sum_smul_index
- \+/\- *def* polynomial.support
- \+/\- *lemma* polynomial.support_X
- \+/\- *lemma* polynomial.support_X_empty
- \+/\- *lemma* polynomial.support_X_pow
- \+/\- *lemma* polynomial.support_erase
- \+/\- *lemma* polynomial.support_neg
- \+/\- *lemma* polynomial.support_update
- \+/\- *lemma* polynomial.support_update_ne_zero
- \+/\- *lemma* polynomial.support_update_zero
- \+/\- *lemma* polynomial.support_zero
- \+/\- *def* polynomial.to_finsupp_iso
- \+/\- *def* polynomial.update
- \+/\- *lemma* polynomial.update_zero_eq_erase
- \+/\- *lemma* polynomial.zero_to_finsupp

Modified src/data/polynomial/cancel_leads.lean
- \+/\- *def* polynomial.cancel_leads
- \+/\- *lemma* polynomial.dvd_cancel_leads_of_dvd_of_dvd

Modified src/data/polynomial/cardinal.lean
- \+/\- *lemma* polynomial.cardinal_mk_le_max

Modified src/data/polynomial/coeff.lean
- \+/\- *lemma* polynomial.C_dvd_iff_dvd_coeff
- \+/\- *lemma* polynomial.C_mul'
- \+/\- *lemma* polynomial.coeff_C_mul
- \+/\- *lemma* polynomial.coeff_C_mul_X
- \+/\- *theorem* polynomial.coeff_X_mul
- \+/\- *lemma* polynomial.coeff_X_mul_zero
- \+/\- *lemma* polynomial.coeff_X_pow_mul'
- \+/\- *theorem* polynomial.coeff_X_pow_mul
- \+/\- *lemma* polynomial.coeff_add
- \+/\- *lemma* polynomial.coeff_bit0_mul
- \+/\- *lemma* polynomial.coeff_bit1_mul
- \+/\- *lemma* polynomial.coeff_mul
- \+/\- *lemma* polynomial.coeff_mul_C
- \+/\- *theorem* polynomial.coeff_mul_X
- \+/\- *lemma* polynomial.coeff_mul_X_pow'
- \+/\- *theorem* polynomial.coeff_mul_X_pow
- \+/\- *lemma* polynomial.coeff_mul_X_zero
- \+/\- *lemma* polynomial.coeff_one
- \+/\- *lemma* polynomial.coeff_smul
- \+/\- *lemma* polynomial.coeff_sum
- \+/\- *lemma* polynomial.finset_sum_coeff
- \+/\- *def* polynomial.lcoeff
- \+/\- *lemma* polynomial.lcoeff_apply
- \+/\- *theorem* polynomial.mul_X_pow_eq_zero
- \+/\- *lemma* polynomial.mul_coeff_zero
- \+/\- *lemma* polynomial.support_smul
- \+/\- *lemma* polynomial.update_eq_add_sub_coeff

Modified src/data/polynomial/degree/card_pow_degree.lean
- \+/\- *lemma* polynomial.card_pow_degree_apply
- \+/\- *lemma* polynomial.card_pow_degree_nonzero
- \+/\- *lemma* polynomial.card_pow_degree_zero

Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* polynomial.as_sum_range'
- \+/\- *lemma* polynomial.as_sum_range
- \+/\- *lemma* polynomial.as_sum_range_C_mul_X_pow
- \+/\- *lemma* polynomial.as_sum_support
- \+/\- *lemma* polynomial.as_sum_support_C_mul_X_pow
- \+/\- *lemma* polynomial.card_supp_le_succ_nat_degree
- \+/\- *lemma* polynomial.coeff_eq_zero_of_nat_degree_lt
- \+/\- *lemma* polynomial.coeff_mul_X_sub_C
- \+/\- *lemma* polynomial.coeff_mul_degree_add_degree
- \+/\- *lemma* polynomial.coeff_nat_degree_succ_eq_zero
- \+/\- *lemma* polynomial.coeff_pow_mul_nat_degree
- \+/\- *def* polynomial.degree
- \+/\- *lemma* polynomial.degree_X
- \+/\- *theorem* polynomial.degree_X_le
- \+/\- *lemma* polynomial.degree_X_pow
- \+/\- *theorem* polynomial.degree_X_pow_le
- \+/\- *lemma* polynomial.degree_add_le
- \+/\- *lemma* polynomial.degree_add_le_of_degree_le
- \+/\- *lemma* polynomial.degree_eq_iff_nat_degree_eq
- \+/\- *lemma* polynomial.degree_eq_iff_nat_degree_eq_of_pos
- \+/\- *lemma* polynomial.degree_erase_le
- \+/\- *theorem* polynomial.degree_le_iff_coeff_zero
- \+/\- *theorem* polynomial.degree_lt_iff_coeff_zero
- \+/\- *lemma* polynomial.degree_lt_wf
- \+/\- *lemma* polynomial.degree_mono
- \+/\- *lemma* polynomial.degree_mul_le
- \+/\- *lemma* polynomial.degree_neg
- \+/\- *lemma* polynomial.degree_one
- \+/\- *lemma* polynomial.degree_one_le
- \+/\- *lemma* polynomial.degree_pow
- \+/\- *lemma* polynomial.degree_pow_le
- \+/\- *lemma* polynomial.degree_smul_le
- \+/\- *lemma* polynomial.degree_sub_le
- \+/\- *lemma* polynomial.degree_sum_le
- \+/\- *lemma* polynomial.degree_update_le
- \+/\- *lemma* polynomial.degree_zero
- \+/\- *lemma* polynomial.ite_le_nat_degree_coeff
- \+/\- *def* polynomial.leading_coeff
- \+/\- *lemma* polynomial.leading_coeff_X
- \+/\- *lemma* polynomial.leading_coeff_X_pow
- \+/\- *def* polynomial.leading_coeff_hom
- \+/\- *lemma* polynomial.leading_coeff_hom_apply
- \+/\- *theorem* polynomial.leading_coeff_monic_mul
- \+/\- *lemma* polynomial.leading_coeff_mul
- \+/\- *theorem* polynomial.leading_coeff_mul_X
- \+/\- *theorem* polynomial.leading_coeff_mul_X_pow
- \+/\- *theorem* polynomial.leading_coeff_mul_monic
- \+/\- *lemma* polynomial.leading_coeff_one
- \+/\- *lemma* polynomial.leading_coeff_pow
- \+/\- *lemma* polynomial.leading_coeff_zero
- \+/\- *lemma* polynomial.monic.coeff_nat_degree
- \+/\- *lemma* polynomial.monic.leading_coeff
- \+/\- *lemma* polynomial.monic.ne_zero
- \+/\- *lemma* polynomial.monic.ne_zero_of_ne
- \+/\- *def* polynomial.monic
- \+/\- *lemma* polynomial.monic_X
- \+/\- *lemma* polynomial.monic_X_pow
- \+/\- *lemma* polynomial.monic_of_subsingleton
- \+/\- *lemma* polynomial.monic_one
- \+/\- *def* polynomial.nat_degree
- \+/\- *lemma* polynomial.nat_degree_X
- \+/\- *lemma* polynomial.nat_degree_X_le
- \+/\- *lemma* polynomial.nat_degree_X_pow
- \+/\- *lemma* polynomial.nat_degree_add_le
- \+/\- *lemma* polynomial.nat_degree_add_le_of_degree_le
- \+/\- *lemma* polynomial.nat_degree_eq_of_degree_eq
- \+/\- *lemma* polynomial.nat_degree_eq_of_degree_eq_some
- \+/\- *lemma* polynomial.nat_degree_int_cast
- \+/\- *lemma* polynomial.nat_degree_le_nat_degree
- \+/\- *lemma* polynomial.nat_degree_mul_le
- \+/\- *lemma* polynomial.nat_degree_nat_cast
- \+/\- *lemma* polynomial.nat_degree_neg
- \+/\- *lemma* polynomial.nat_degree_one
- \+/\- *lemma* polynomial.nat_degree_pow_le
- \+/\- *lemma* polynomial.nat_degree_smul_le
- \+/\- *lemma* polynomial.nat_degree_zero
- \+/\- *def* polynomial.next_coeff
- \+/\- *lemma* polynomial.next_coeff_of_pos_nat_degree
- \+/\- *theorem* polynomial.not_is_unit_X
- \+/\- *lemma* polynomial.subsingleton_of_monic_zero
- \+/\- *lemma* polynomial.sum_over_range'
- \+/\- *lemma* polynomial.sum_over_range
- \+/\- *lemma* polynomial.zero_le_degree_iff

Modified src/data/polynomial/degree/lemmas.lean
- \+/\- *lemma* polynomial.coe_lt_degree
- \+/\- *lemma* polynomial.degree_pos_of_eval₂_root
- \+/\- *lemma* polynomial.degree_pos_of_root
- \+/\- *lemma* polynomial.degree_sum_eq_of_disjoint
- \+/\- *lemma* polynomial.nat_degree_C_mul_le
- \+/\- *lemma* polynomial.nat_degree_add_coeff_mul
- \+/\- *lemma* polynomial.nat_degree_mul_C_le
- \+/\- *lemma* polynomial.nat_degree_pos_of_eval₂_root
- \+/\- *lemma* polynomial.nat_degree_sum_eq_of_disjoint

Modified src/data/polynomial/degree/trailing_degree.lean
- \+/\- *lemma* polynomial.coeff_eq_zero_of_lt_nat_trailing_degree
- \+/\- *lemma* polynomial.coeff_nat_trailing_degree_pred_eq_zero
- \+/\- *theorem* polynomial.le_trailing_degree_X
- \+/\- *def* polynomial.nat_trailing_degree
- \+/\- *lemma* polynomial.nat_trailing_degree_X
- \+/\- *lemma* polynomial.nat_trailing_degree_X_le
- \+/\- *lemma* polynomial.nat_trailing_degree_eq_of_trailing_degree_eq
- \+/\- *lemma* polynomial.nat_trailing_degree_eq_of_trailing_degree_eq_some
- \+/\- *lemma* polynomial.nat_trailing_degree_int_cast
- \+/\- *lemma* polynomial.nat_trailing_degree_le_nat_degree
- \+/\- *lemma* polynomial.nat_trailing_degree_mul_X_pow
- \+/\- *lemma* polynomial.nat_trailing_degree_nat_cast
- \+/\- *lemma* polynomial.nat_trailing_degree_neg
- \+/\- *lemma* polynomial.nat_trailing_degree_one
- \+/\- *lemma* polynomial.nat_trailing_degree_zero
- \+/\- *def* polynomial.next_coeff_up
- \+/\- *lemma* polynomial.next_coeff_up_of_pos_nat_trailing_degree
- \+/\- *def* polynomial.trailing_coeff
- \+/\- *lemma* polynomial.trailing_coeff_zero
- \+/\- *def* polynomial.trailing_degree
- \+/\- *lemma* polynomial.trailing_degree_X
- \+/\- *lemma* polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq
- \+/\- *lemma* polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos
- \+/\- *lemma* polynomial.trailing_degree_neg
- \+/\- *lemma* polynomial.trailing_degree_one
- \+/\- *lemma* polynomial.trailing_degree_one_le
- \+/\- *lemma* polynomial.trailing_degree_zero
- \+/\- *lemma* polynomial.trailing_monic.trailing_coeff
- \+/\- *def* polynomial.trailing_monic

Modified src/data/polynomial/denoms_clearable.lean
- \+/\- *lemma* denoms_clearable.add
- \+/\- *def* denoms_clearable
- \+/\- *lemma* one_le_pow_mul_abs_eval_div

Modified src/data/polynomial/derivative.lean
- \+/\- *lemma* polynomial.coeff_derivative
- \+/\- *lemma* polynomial.degree_derivative_eq
- \+/\- *theorem* polynomial.degree_derivative_le
- \+/\- *theorem* polynomial.degree_derivative_lt
- \+/\- *def* polynomial.derivative
- \+/\- *lemma* polynomial.derivative_C_mul
- \+/\- *lemma* polynomial.derivative_X
- \+/\- *lemma* polynomial.derivative_add
- \+/\- *lemma* polynomial.derivative_apply
- \+/\- *lemma* polynomial.derivative_bit0
- \+/\- *lemma* polynomial.derivative_bit1
- \+/\- *lemma* polynomial.derivative_cast_nat
- \+/\- *lemma* polynomial.derivative_comp
- \+/\- *lemma* polynomial.derivative_comp_one_sub_X
- \+/\- *lemma* polynomial.derivative_eval
- \+/\- *theorem* polynomial.derivative_eval₂_C
- \+/\- *def* polynomial.derivative_lhom
- \+/\- *theorem* polynomial.derivative_map
- \+/\- *lemma* polynomial.derivative_mul
- \+/\- *lemma* polynomial.derivative_neg
- \+/\- *lemma* polynomial.derivative_one
- \+/\- *theorem* polynomial.derivative_pow
- \+/\- *theorem* polynomial.derivative_pow_succ
- \+/\- *theorem* polynomial.derivative_prod
- \+/\- *lemma* polynomial.derivative_smul
- \+/\- *lemma* polynomial.derivative_sub
- \+/\- *lemma* polynomial.derivative_sum
- \+/\- *lemma* polynomial.derivative_zero
- \+/\- *lemma* polynomial.iterate_derivative_C_mul
- \+/\- *lemma* polynomial.iterate_derivative_add
- \+/\- *lemma* polynomial.iterate_derivative_cast_nat_mul
- \+/\- *lemma* polynomial.iterate_derivative_comp_one_sub_X
- \+/\- *theorem* polynomial.iterate_derivative_map
- \+/\- *lemma* polynomial.iterate_derivative_neg
- \+/\- *lemma* polynomial.iterate_derivative_smul
- \+/\- *lemma* polynomial.iterate_derivative_sub
- \+/\- *lemma* polynomial.iterate_derivative_zero
- \+/\- *lemma* polynomial.mem_support_derivative
- \+/\- *theorem* polynomial.nat_degree_derivative_lt
- \+/\- *theorem* polynomial.of_mem_support_derivative

Modified src/data/polynomial/div.lean
- \+/\- *theorem* polynomial.X_dvd_iff
- \+/\- *def* polynomial.decidable_dvd_monic
- \+/\- *lemma* polynomial.degree_div_by_monic_le
- \+/\- *lemma* polynomial.degree_div_by_monic_lt
- \+/\- *theorem* polynomial.degree_mod_by_monic_le
- \+/\- *lemma* polynomial.degree_mod_by_monic_lt
- \+/\- *def* polynomial.div_by_monic
- \+/\- *lemma* polynomial.div_by_monic_eq_of_not_monic
- \+/\- *lemma* polynomial.div_by_monic_one
- \+/\- *lemma* polynomial.div_by_monic_zero
- \+/\- *lemma* polynomial.div_mod_by_monic_unique
- \+/\- *theorem* polynomial.map_dvd_map
- \+/\- *def* polynomial.mod_by_monic
- \+/\- *lemma* polynomial.mod_by_monic_X
- \+/\- *lemma* polynomial.mod_by_monic_X_sub_C_eq_C_eval
- \+/\- *lemma* polynomial.mod_by_monic_add_div
- \+/\- *lemma* polynomial.mod_by_monic_eq_of_not_monic
- \+/\- *lemma* polynomial.mod_by_monic_eq_sub_mul_div
- \+/\- *lemma* polynomial.mod_by_monic_one
- \+/\- *lemma* polynomial.mod_by_monic_zero
- \+/\- *theorem* polynomial.nat_degree_div_by_monic
- \+/\- *lemma* polynomial.pow_root_multiplicity_dvd
- \+/\- *def* polynomial.root_multiplicity
- \+/\- *lemma* polynomial.root_multiplicity_eq_multiplicity
- \+/\- *lemma* polynomial.root_multiplicity_eq_zero
- \+/\- *lemma* polynomial.root_multiplicity_pos
- \+/\- *lemma* polynomial.zero_div_by_monic
- \+/\- *lemma* polynomial.zero_mod_by_monic

Modified src/data/polynomial/erase_lead.lean
- \+/\- *def* polynomial.erase_lead
- \+/\- *lemma* polynomial.erase_lead_X
- \+/\- *lemma* polynomial.erase_lead_X_pow
- \+/\- *lemma* polynomial.erase_lead_add_C_mul_X_pow
- \+/\- *lemma* polynomial.erase_lead_add_monomial_nat_degree_leading_coeff
- \+/\- *lemma* polynomial.erase_lead_nat_degree_lt_or_erase_lead_eq_zero
- \+/\- *lemma* polynomial.erase_lead_support
- \+/\- *lemma* polynomial.erase_lead_zero
- \+/\- *lemma* polynomial.induction_with_nat_degree_le
- \+/\- *lemma* polynomial.self_sub_C_mul_X_pow
- \+/\- *lemma* polynomial.self_sub_monomial_nat_degree_leading_coeff

Modified src/data/polynomial/eval.lean
- \+/\- *lemma* polynomial.bit0_comp
- \+/\- *lemma* polynomial.bit1_comp
- \+/\- *lemma* polynomial.cast_int_comp
- \+/\- *lemma* polynomial.coe_eval_ring_hom
- \+/\- *lemma* polynomial.coeff_zero_eq_eval_zero
- \+/\- *def* polynomial.comp
- \+/\- *lemma* polynomial.comp_assoc
- \+/\- *def* polynomial.comp_ring_hom
- \+/\- *lemma* polynomial.comp_zero
- \+/\- *lemma* polynomial.degree_map_le
- \+/\- *def* polynomial.eval
- \+/\- *lemma* polynomial.eval_eq_finset_sum'
- \+/\- *lemma* polynomial.eval_eq_finset_sum
- \+/\- *lemma* polynomial.eval_finset_sum
- \+/\- *lemma* polynomial.eval_int_cast
- \+/\- *lemma* polynomial.eval_list_prod
- \+/\- *lemma* polynomial.eval_multiset_prod
- \+/\- *lemma* polynomial.eval_nat_cast
- \+/\- *lemma* polynomial.eval_nat_cast_map
- \+/\- *lemma* polynomial.eval_nat_cast_mul
- \+/\- *lemma* polynomial.eval_neg
- \+/\- *lemma* polynomial.eval_one
- \+/\- *lemma* polynomial.eval_one_map
- \+/\- *lemma* polynomial.eval_prod
- \+/\- *def* polynomial.eval_ring_hom
- \+/\- *lemma* polynomial.eval_smul
- \+/\- *lemma* polynomial.eval_sub
- \+/\- *lemma* polynomial.eval_sum
- \+/\- *lemma* polynomial.eval_zero
- \+/\- *lemma* polynomial.eval_zero_map
- \+/\- *def* polynomial.eval₂
- \+/\- *def* polynomial.eval₂_add_monoid_hom
- \+/\- *lemma* polynomial.eval₂_eq_sum_range'
- \+/\- *lemma* polynomial.eval₂_finset_sum
- \+/\- *lemma* polynomial.eval₂_list_prod_noncomm
- \+/\- *lemma* polynomial.eval₂_mul_eq_zero_of_left
- \+/\- *lemma* polynomial.eval₂_mul_eq_zero_of_right
- \+/\- *lemma* polynomial.eval₂_nat_cast
- \+/\- *lemma* polynomial.eval₂_one
- \+/\- *def* polynomial.eval₂_ring_hom'
- \+/\- *def* polynomial.eval₂_ring_hom
- \+/\- *lemma* polynomial.eval₂_smul
- \+/\- *lemma* polynomial.eval₂_sum
- \+/\- *lemma* polynomial.eval₂_zero
- \+/\- *lemma* polynomial.is_root.dvd
- \+/\- *lemma* polynomial.is_root.map
- \+/\- *lemma* polynomial.is_root.of_map
- \+/\- *def* polynomial.is_root
- \+/\- *lemma* polynomial.is_root_map_iff
- \+/\- *def* polynomial.leval
- \+/\- *def* polynomial.map
- \+/\- *lemma* polynomial.map_comp
- \+/\- *def* polynomial.map_equiv
- \+/\- *lemma* polynomial.map_list_prod
- \+/\- *lemma* polynomial.map_multiset_prod
- \+/\- *lemma* polynomial.map_one
- \+/\- *lemma* polynomial.map_prod
- \+/\- *def* polynomial.map_ring_hom
- \+/\- *lemma* polynomial.map_ring_hom_id
- \+/\- *lemma* polynomial.map_sum
- \+/\- *lemma* polynomial.map_zero
- \+/\- *lemma* polynomial.mem_map_srange
- \+/\- *lemma* polynomial.mul_comp
- \+/\- *lemma* polynomial.nat_cast_comp
- \+/\- *lemma* polynomial.nat_cast_mul_comp
- \+/\- *lemma* polynomial.nat_degree_map_le
- \+/\- *lemma* polynomial.one_comp
- \+/\- *lemma* polynomial.pow_comp
- \+/\- *lemma* polynomial.prod_comp
- \+/\- *lemma* polynomial.root_mul_left_of_is_root
- \+/\- *lemma* polynomial.root_mul_right_of_is_root
- \+/\- *lemma* polynomial.support_map_subset
- \+/\- *lemma* polynomial.zero_comp
- \+/\- *lemma* polynomial.zero_is_root_of_coeff_zero_eq_zero

Modified src/data/polynomial/field_division.lean
- \+/\- *lemma* polynomial.coe_norm_unit
- \+/\- *lemma* polynomial.coe_norm_unit_of_ne_zero
- \+/\- *lemma* polynomial.coeff_inv_units
- \+/\- *lemma* polynomial.degree_div_le
- \+/\- *lemma* polynomial.degree_map
- \+/\- *lemma* polynomial.degree_mul_leading_coeff_inv
- \+/\- *def* polynomial.div
- \+/\- *lemma* polynomial.div_by_monic_eq_div
- \+/\- *lemma* polynomial.eval_gcd_eq_zero
- \+/\- *lemma* polynomial.eval₂_gcd_eq_zero
- \+/\- *theorem* polynomial.irreducible_of_monic
- \+/\- *lemma* polynomial.is_root_gcd_iff_is_root_left_right
- \+/\- *lemma* polynomial.leading_coeff_normalize
- \+/\- *theorem* polynomial.map_dvd_map'
- \+/\- *def* polynomial.mod
- \+/\- *lemma* polynomial.mod_X_sub_C_eq_C_eval
- \+/\- *lemma* polynomial.mod_by_monic_eq_mod
- \+/\- *lemma* polynomial.monic.normalize_eq_self
- \+/\- *theorem* polynomial.monic_map_iff
- \+/\- *lemma* polynomial.prod_multiset_X_sub_C_dvd
- \+/\- *lemma* polynomial.prod_multiset_root_eq_finset_root
- \+/\- *lemma* polynomial.root_gcd_iff_root_left_right
- \+/\- *lemma* polynomial.root_left_of_root_gcd
- \+/\- *lemma* polynomial.root_right_of_root_gcd
- \+/\- *lemma* polynomial.roots_C_mul
- \+/\- *lemma* polynomial.roots_normalize

Modified src/data/polynomial/hasse_deriv.lean
- \+/\- *def* polynomial.hasse_deriv
- \+/\- *lemma* polynomial.hasse_deriv_X
- \+/\- *lemma* polynomial.hasse_deriv_apply_one
- \+/\- *lemma* polynomial.hasse_deriv_eq_zero_of_lt_nat_degree
- \+/\- *lemma* polynomial.hasse_deriv_mul
- \+/\- *lemma* polynomial.nat_degree_hasse_deriv
- \+/\- *lemma* polynomial.nat_degree_hasse_deriv_le

Modified src/data/polynomial/identities.lean
- \+/\- *def* polynomial.binom_expansion
- \+/\- *def* polynomial.eval_sub_factor

Modified src/data/polynomial/induction.lean
- \+/\- *theorem* polynomial.coeff_monomial_mul
- \+/\- *theorem* polynomial.coeff_monomial_zero_mul
- \+/\- *theorem* polynomial.coeff_mul_monomial
- \+/\- *theorem* polynomial.coeff_mul_monomial_zero
- \+/\- *lemma* polynomial.sum_C_mul_X_eq
- \+/\- *lemma* polynomial.sum_monomial_eq

Modified src/data/polynomial/inductions.lean
- \+/\- *def* polynomial.div_X
- \+/\- *lemma* polynomial.div_X_mul_X_add
- \+/\- *lemma* polynomial.nat_degree_ne_zero_induction_on

Modified src/data/polynomial/integral_normalization.lean
- \+/\- *lemma* polynomial.integral_normalization_aeval_eq_zero
- \+/\- *lemma* polynomial.integral_normalization_coeff
- \+/\- *lemma* polynomial.integral_normalization_coeff_degree
- \+/\- *lemma* polynomial.integral_normalization_coeff_nat_degree
- \+/\- *lemma* polynomial.integral_normalization_coeff_ne_degree
- \+/\- *lemma* polynomial.integral_normalization_eval₂_eq_zero
- \+/\- *lemma* polynomial.integral_normalization_support
- \+/\- *lemma* polynomial.monic_integral_normalization
- \+/\- *lemma* polynomial.support_integral_normalization

Modified src/data/polynomial/iterated_deriv.lean
- \+/\- *def* polynomial.iterated_deriv
- \+/\- *lemma* polynomial.iterated_deriv_X
- \+/\- *lemma* polynomial.iterated_deriv_X_one
- \+/\- *lemma* polynomial.iterated_deriv_X_zero
- \+/\- *lemma* polynomial.iterated_deriv_one
- \+/\- *lemma* polynomial.iterated_deriv_one_zero
- \+/\- *lemma* polynomial.iterated_deriv_zero_left

Modified src/data/polynomial/lifts.lean
- \+/\- *lemma* polynomial.X_mem_lifts
- \+/\- *lemma* polynomial.X_pow_mem_lifts
- \+/\- *lemma* polynomial.base_mul_mem_lifts
- \+/\- *lemma* polynomial.erase_mem_lifts
- \+/\- *def* polynomial.lifts
- \+/\- *lemma* polynomial.lifts_and_degree_eq_and_monic
- \+/\- *lemma* polynomial.lifts_iff_coeff_lifts
- \+/\- *lemma* polynomial.lifts_iff_lifts_ring
- \+/\- *lemma* polynomial.lifts_iff_ring_hom_srange
- \+/\- *lemma* polynomial.lifts_iff_set_range
- \+/\- *def* polynomial.lifts_ring
- \+/\- *lemma* polynomial.map_alg_eq_map
- \+/\- *lemma* polynomial.mem_lifts
- \+/\- *lemma* polynomial.mem_lifts_and_degree_eq
- \+/\- *lemma* polynomial.smul_mem_lifts

Modified src/data/polynomial/mirror.lean
- \+/\- *lemma* polynomial.irreducible_of_mirror
- \+/\- *lemma* polynomial.mirror_X
- \+/\- *lemma* polynomial.mirror_mul_of_domain
- \+/\- *lemma* polynomial.mirror_neg
- \+/\- *lemma* polynomial.mirror_smul
- \+/\- *lemma* polynomial.mirror_zero

Modified src/data/polynomial/monic.lean
- \+/\- *lemma* polynomial.degree_map_eq_of_injective
- \+/\- *lemma* polynomial.is_unit_leading_coeff_mul_left_eq_zero_iff
- \+/\- *lemma* polynomial.is_unit_leading_coeff_mul_right_eq_zero_iff
- \+/\- *lemma* polynomial.leading_coeff_map'
- \+/\- *lemma* polynomial.leading_coeff_of_injective
- \+/\- *lemma* polynomial.monic.as_sum
- \+/\- *lemma* polynomial.monic.degree_le_zero_iff_eq_one
- \+/\- *lemma* polynomial.monic.degree_mul_comm
- \+/\- *lemma* polynomial.monic.is_regular
- \+/\- *lemma* polynomial.monic.mul_left_eq_zero_iff
- \+/\- *lemma* polynomial.monic.mul_left_ne_zero
- \+/\- *lemma* polynomial.monic.mul_nat_degree_lt_iff
- \+/\- *lemma* polynomial.monic.mul_right_eq_zero_iff
- \+/\- *lemma* polynomial.monic.mul_right_ne_zero
- \+/\- *lemma* polynomial.monic.nat_degree_eq_zero_iff_eq_one
- \+/\- *lemma* polynomial.monic.nat_degree_mul'
- \+/\- *lemma* polynomial.monic.nat_degree_mul
- \+/\- *lemma* polynomial.monic.nat_degree_mul_comm
- \+/\- *lemma* polynomial.monic.next_coeff_mul
- \+/\- *lemma* polynomial.monic.next_coeff_multiset_prod
- \+/\- *lemma* polynomial.monic.next_coeff_prod
- \+/\- *lemma* polynomial.monic_add_of_left
- \+/\- *lemma* polynomial.monic_add_of_right
- \+/\- *lemma* polynomial.monic_multiset_prod_of_monic
- \+/\- *lemma* polynomial.monic_of_injective
- \+/\- *lemma* polynomial.monic_prod_of_monic
- \+/\- *lemma* polynomial.monic_sub_of_left
- \+/\- *lemma* polynomial.monic_sub_of_right
- \+/\- *lemma* polynomial.nat_degree_map_eq_of_injective
- \+/\- *lemma* polynomial.next_coeff_map
- \+/\- *lemma* polynomial.not_monic_zero

Modified src/data/polynomial/monomial.lean
- \+/\- *lemma* polynomial.card_support_le_one_iff_monomial
- \+/\- *lemma* polynomial.ring_hom_ext'
- \+/\- *lemma* polynomial.ring_hom_ext

Modified src/data/polynomial/reverse.lean
- \+/\- *lemma* polynomial.coeff_one_reverse
- \+/\- *lemma* polynomial.coeff_reflect
- \+/\- *lemma* polynomial.coeff_reverse
- \+/\- *lemma* polynomial.coeff_zero_reverse
- \+/\- *lemma* polynomial.eval₂_reflect_eq_zero_iff
- \+/\- *lemma* polynomial.eval₂_reflect_mul_pow
- \+/\- *lemma* polynomial.eval₂_reverse_eq_zero_iff
- \+/\- *lemma* polynomial.eval₂_reverse_mul_pow
- \+/\- *lemma* polynomial.nat_degree_eq_reverse_nat_degree_add_nat_trailing_degree
- \+/\- *lemma* polynomial.reflect_C_mul
- \+/\- *lemma* polynomial.reflect_add
- \+/\- *lemma* polynomial.reflect_eq_zero_iff
- \+/\- *lemma* polynomial.reflect_monomial
- \+/\- *lemma* polynomial.reflect_neg
- \+/\- *lemma* polynomial.reflect_sub
- \+/\- *lemma* polynomial.reflect_support
- \+/\- *lemma* polynomial.reflect_zero
- \+/\- *lemma* polynomial.reverse_leading_coeff
- \+/\- *theorem* polynomial.reverse_mul
- \+/\- *lemma* polynomial.reverse_mul_of_domain
- \+/\- *lemma* polynomial.reverse_nat_degree
- \+/\- *lemma* polynomial.reverse_nat_degree_le
- \+/\- *lemma* polynomial.reverse_nat_trailing_degree
- \+/\- *lemma* polynomial.reverse_neg
- \+/\- *lemma* polynomial.reverse_trailing_coeff
- \+/\- *lemma* polynomial.reverse_zero
- \+/\- *lemma* polynomial.trailing_coeff_mul

Modified src/data/polynomial/ring_division.lean
- \+/\- *theorem* polynomial.card_le_degree_of_subset_roots
- \+/\- *lemma* polynomial.card_roots'
- \+/\- *lemma* polynomial.card_roots_sub_C'
- \+/\- *lemma* polynomial.card_roots_sub_C
- \+/\- *lemma* polynomial.coeff_coe_units_zero_ne_zero
- \+/\- *lemma* polynomial.count_roots
- \+/\- *lemma* polynomial.degree_coe_units
- \+/\- *lemma* polynomial.degree_le_mul_left
- \+/\- *lemma* polynomial.degree_pos_of_aeval_root
- \+/\- *lemma* polynomial.exists_max_root
- \+/\- *lemma* polynomial.exists_min_root
- \+/\- *lemma* polynomial.exists_multiset_roots
- \+/\- *lemma* polynomial.funext
- \+/\- *theorem* polynomial.irreducible_X
- \+/\- *theorem* polynomial.is_unit_iff
- \+/\- *lemma* polynomial.leading_coeff_div_by_monic_X_sub_C
- \+/\- *lemma* polynomial.mem_roots_sub_C
- \+/\- *lemma* polynomial.mod_by_monic_eq_of_dvd_sub
- \+/\- *lemma* polynomial.monic.irreducible_of_irreducible_map
- \+/\- *lemma* polynomial.nat_degree_coe_units
- \+/\- *theorem* polynomial.nat_degree_le_of_dvd
- \+/\- *lemma* polynomial.nat_degree_pos_of_aeval_root
- \+/\- *lemma* polynomial.nat_degree_pow
- \+/\- *theorem* polynomial.prime_X
- \+/\- *lemma* polynomial.root_multiplicity_add
- \+/\- *lemma* polynomial.root_multiplicity_mul
- \+/\- *lemma* polynomial.root_multiplicity_of_dvd
- \+/\- *def* polynomial.root_set
- \+/\- *lemma* polynomial.root_set_def
- \+/\- *lemma* polynomial.root_set_finite
- \+/\- *lemma* polynomial.roots_list_prod
- \+/\- *lemma* polynomial.roots_mul
- \+/\- *lemma* polynomial.roots_multiset_prod
- \+/\- *lemma* polynomial.roots_one
- \+/\- *lemma* polynomial.roots_prod
- \+/\- *lemma* polynomial.roots_smul_nonzero
- \+/\- *lemma* polynomial.roots_zero
- \+/\- *lemma* polynomial.units_coeff_zero_smul
- \+/\- *lemma* polynomial.zero_of_eval_zero

Modified src/data/polynomial/taylor.lean
- \+/\- *lemma* polynomial.eq_zero_of_hasse_deriv_eq_zero
- \+/\- *lemma* polynomial.nat_degree_taylor
- \+/\- *lemma* polynomial.sum_taylor_eq
- \+/\- *def* polynomial.taylor
- \+/\- *lemma* polynomial.taylor_eval
- \+/\- *lemma* polynomial.taylor_eval_sub
- \+/\- *lemma* polynomial.taylor_mul
- \+/\- *lemma* polynomial.taylor_one
- \+/\- *lemma* polynomial.taylor_taylor
- \+/\- *lemma* polynomial.taylor_zero

Modified src/field_theory/abel_ruffini.lean
- \+/\- *lemma* gal_X_is_solvable
- \+/\- *lemma* gal_X_pow_is_solvable
- \+/\- *lemma* gal_X_pow_sub_one_is_solvable
- \+/\- *lemma* gal_is_solvable_of_splits
- \+/\- *lemma* gal_is_solvable_tower
- \+/\- *lemma* gal_mul_is_solvable
- \+/\- *lemma* gal_one_is_solvable
- \+/\- *lemma* gal_prod_is_solvable
- \+/\- *lemma* gal_zero_is_solvable
- \+/\- *lemma* solvable_by_rad.is_solvable'

Modified src/field_theory/adjoin.lean
- \+/\- *lemma* power_basis.equiv_adjoin_simple_aeval
- \+/\- *lemma* power_basis.equiv_adjoin_simple_symm_aeval

Modified src/field_theory/finite/basic.lean
- \+/\- *lemma* finite_field.X_pow_card_sub_X_ne_zero
- \+/\- *lemma* finite_field.card_image_polynomial_eval
- \+/\- *lemma* finite_field.exists_root_sum_quadratic
- \+/\- *lemma* finite_field.expand_card
- \+/\- *lemma* finite_field.roots_X_pow_card_sub_X

Modified src/field_theory/finite/galois_field.lean


Modified src/field_theory/galois.lean


Modified src/field_theory/intermediate_field.lean


Modified src/field_theory/is_alg_closed/algebraic_closure.lean
- \+/\- *theorem* algebraic_closure.adjoin_monic.exists_root

Modified src/field_theory/is_alg_closed/basic.lean
- \+/\- *lemma* is_alg_closed.degree_eq_one_of_irreducible
- \+/\- *theorem* is_alg_closed.exists_root
- \+/\- *theorem* is_alg_closed.of_exists_root
- \+/\- *lemma* is_alg_closed.roots_eq_zero_iff

Modified src/field_theory/is_alg_closed/classification.lean


Modified src/field_theory/laurent.lean
- \+/\- *lemma* ratfunc.laurent_aux_of_fraction_ring_mk
- \+/\- *lemma* ratfunc.taylor_mem_non_zero_divisors

Modified src/field_theory/minpoly.lean
- \+/\- *lemma* minpoly.aeval_ne_zero_of_dvd_not_unit_minpoly
- \+/\- *lemma* minpoly.dvd
- \+/\- *lemma* minpoly.eq_of_irreducible
- \+/\- *lemma* minpoly.min
- \+/\- *lemma* minpoly.unique

Modified src/field_theory/normal.lean
- \+/\- *lemma* normal.of_is_splitting_field

Modified src/field_theory/polynomial_galois_group.lean
- \+/\- *lemma* polynomial.gal.card_complex_roots_eq_card_real_add_card_not_gal_inv
- \+/\- *lemma* polynomial.gal.mul_splits_in_splitting_field_of_mul
- \+/\- *lemma* polynomial.gal.splits_ℚ_ℂ

Modified src/field_theory/primitive_element.lean
- \+/\- *lemma* field.primitive_element_inf_aux_exists_c

Modified src/field_theory/ratfunc.lean
- \+/\- *def* ratfunc.X
- \+/\- *lemma* ratfunc.algebra_map_apply
- \+/\- *lemma* ratfunc.algebra_map_eq_zero_iff
- \+/\- *lemma* ratfunc.algebra_map_injective
- \+/\- *lemma* ratfunc.algebra_map_ne_zero
- \+/\- *lemma* ratfunc.coe_map_alg_hom_eq_coe_map
- \+/\- *lemma* ratfunc.coe_map_ring_hom_eq_coe_map
- \+/\- *def* ratfunc.denom
- \+/\- *lemma* ratfunc.denom_algebra_map
- \+/\- *lemma* ratfunc.denom_div
- \+/\- *lemma* ratfunc.denom_div_dvd
- \+/\- *lemma* ratfunc.denom_dvd
- \+/\- *lemma* ratfunc.div_smul
- \+/\- *lemma* ratfunc.eval_algebra_map
- \+/\- *lemma* ratfunc.lift_alg_hom_apply
- \+/\- *lemma* ratfunc.lift_alg_hom_apply_div
- \+/\- *lemma* ratfunc.lift_alg_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* ratfunc.lift_alg_hom_injective
- \+/\- *def* ratfunc.lift_monoid_with_zero_hom
- \+/\- *lemma* ratfunc.lift_monoid_with_zero_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* ratfunc.lift_monoid_with_zero_hom_injective
- \+/\- *lemma* ratfunc.lift_on'_div
- \+/\- *lemma* ratfunc.lift_on'_mk
- \+/\- *lemma* ratfunc.lift_on_condition_of_lift_on'_condition
- \+/\- *lemma* ratfunc.lift_on_div
- \+/\- *lemma* ratfunc.lift_on_mk
- \+/\- *lemma* ratfunc.lift_on_of_fraction_ring_mk
- \+/\- *def* ratfunc.lift_ring_hom
- \+/\- *lemma* ratfunc.lift_ring_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* ratfunc.lift_ring_hom_injective
- \+/\- *def* ratfunc.map
- \+/\- *def* ratfunc.map_alg_hom
- \+/\- *lemma* ratfunc.map_apply_of_fraction_ring_mk
- \+/\- *lemma* ratfunc.map_denom_ne_zero
- \+/\- *lemma* ratfunc.map_injective
- \+/\- *def* ratfunc.map_ring_hom
- \+/\- *lemma* ratfunc.mk_coe_def
- \+/\- *lemma* ratfunc.mk_def_of_mem
- \+/\- *lemma* ratfunc.mk_def_of_ne
- \+/\- *lemma* ratfunc.mk_eq_div'
- \+/\- *lemma* ratfunc.mk_eq_div
- \+/\- *lemma* ratfunc.mk_eq_localization_mk
- \+/\- *lemma* ratfunc.mk_eq_mk
- \+/\- *lemma* ratfunc.mk_one'
- \+/\- *lemma* ratfunc.mk_one
- \+/\- *lemma* ratfunc.mk_smul
- \+/\- *lemma* ratfunc.mk_zero
- \+/\- *def* ratfunc.num
- \+/\- *lemma* ratfunc.num_algebra_map
- \+/\- *def* ratfunc.num_denom
- \+/\- *lemma* ratfunc.num_denom_div
- \+/\- *lemma* ratfunc.num_div
- \+/\- *lemma* ratfunc.num_div_dvd
- \+/\- *lemma* ratfunc.num_dvd
- \+/\- *lemma* ratfunc.num_mul_eq_mul_denom_iff
- \+/\- *lemma* ratfunc.of_fraction_ring_add
- \+/\- *lemma* ratfunc.of_fraction_ring_algebra_map
- \+/\- *lemma* ratfunc.of_fraction_ring_div
- \+/\- *lemma* ratfunc.of_fraction_ring_inv
- \+/\- *lemma* ratfunc.of_fraction_ring_mk'
- \+/\- *lemma* ratfunc.of_fraction_ring_mul
- \+/\- *lemma* ratfunc.of_fraction_ring_neg
- \+/\- *lemma* ratfunc.of_fraction_ring_smul
- \+/\- *lemma* ratfunc.of_fraction_ring_sub
- \+/\- *def* ratfunc.to_fraction_ring_ring_equiv
- \+/\- *lemma* ratfunc.to_fraction_ring_smul

Modified src/field_theory/separable.lean
- \+/\- *theorem* irreducible.separable
- \+/\- *lemma* polynomial.card_root_set_eq_nat_degree
- \+/\- *lemma* polynomial.coe_expand
- \+/\- *theorem* polynomial.coeff_contract
- \+/\- *theorem* polynomial.coeff_expand
- \+/\- *theorem* polynomial.coeff_expand_mul'
- \+/\- *theorem* polynomial.coeff_expand_mul
- \+/\- *theorem* polynomial.contract_expand
- \+/\- *lemma* polynomial.count_roots_le_one
- \+/\- *theorem* polynomial.derivative_expand
- \+/\- *lemma* polynomial.eq_X_sub_C_of_separable_of_root_eq
- \+/\- *theorem* polynomial.exists_separable_of_irreducible
- \+/\- *theorem* polynomial.expand_char
- \+/\- *theorem* polynomial.expand_contract
- \+/\- *theorem* polynomial.expand_eq_C
- \+/\- *lemma* polynomial.expand_eq_sum
- \+/\- *theorem* polynomial.expand_eq_zero
- \+/\- *lemma* polynomial.expand_eval
- \+/\- *theorem* polynomial.expand_expand
- \+/\- *theorem* polynomial.expand_inj
- \+/\- *theorem* polynomial.expand_mul
- \+/\- *theorem* polynomial.expand_one
- \+/\- *theorem* polynomial.expand_pow
- \+/\- *theorem* polynomial.expand_zero
- \+/\- *lemma* polynomial.is_unit_of_self_mul_dvd_separable
- \+/\- *theorem* polynomial.is_unit_or_eq_zero_of_separable_expand
- \+/\- *theorem* polynomial.map_expand
- \+/\- *theorem* polynomial.map_expand_pow_char
- \+/\- *lemma* polynomial.monic.expand
- \+/\- *lemma* polynomial.multiplicity_le_one_of_separable
- \+/\- *theorem* polynomial.nat_degree_expand
- \+/\- *lemma* polynomial.nodup_roots
- \+/\- *lemma* polynomial.not_separable_zero
- \+/\- *theorem* polynomial.of_irreducible_expand
- \+/\- *theorem* polynomial.of_irreducible_expand_pow
- \+/\- *lemma* polynomial.root_multiplicity_le_one_of_separable
- \+/\- *lemma* polynomial.separable.is_coprime
- \+/\- *theorem* polynomial.separable.map
- \+/\- *lemma* polynomial.separable.mul
- \+/\- *lemma* polynomial.separable.of_dvd
- \+/\- *lemma* polynomial.separable.of_mul_left
- \+/\- *lemma* polynomial.separable.of_mul_right
- \+/\- *theorem* polynomial.separable.of_pow'
- \+/\- *theorem* polynomial.separable.of_pow
- \+/\- *lemma* polynomial.separable.squarefree
- \+/\- *def* polynomial.separable
- \+/\- *lemma* polynomial.separable_X
- \+/\- *lemma* polynomial.separable_def'
- \+/\- *lemma* polynomial.separable_def
- \+/\- *lemma* polynomial.separable_gcd_left
- \+/\- *lemma* polynomial.separable_gcd_right
- \+/\- *theorem* polynomial.separable_iff_derivative_ne_zero
- \+/\- *theorem* polynomial.separable_map
- \+/\- *lemma* polynomial.separable_of_subsingleton
- \+/\- *lemma* polynomial.separable_one
- \+/\- *theorem* polynomial.separable_or
- \+/\- *lemma* polynomial.separable_prod'
- \+/\- *lemma* polynomial.separable_prod
- \+/\- *theorem* polynomial.unique_separable_of_irreducible

Modified src/field_theory/separable_degree.lean
- \+/\- *def* polynomial.has_separable_contraction.contraction
- \+/\- *lemma* polynomial.has_separable_contraction.eq_degree
- \+/\- *def* polynomial.has_separable_contraction
- \+/\- *def* polynomial.is_separable_contraction

Modified src/field_theory/splitting_field.lean
- \+/\- *theorem* polynomial.X_sub_C_mul_remove_factor
- \+/\- *lemma* polynomial.aeval_root_derivative_of_splits
- \+/\- *lemma* polynomial.degree_eq_card_roots
- \+/\- *lemma* polynomial.degree_eq_one_of_irreducible_of_splits
- \+/\- *lemma* polynomial.eq_X_sub_C_of_splits_of_single_root
- \+/\- *lemma* polynomial.eq_prod_roots_of_monic_of_splits_id
- \+/\- *lemma* polynomial.eq_prod_roots_of_splits
- \+/\- *lemma* polynomial.eq_prod_roots_of_splits_id
- \+/\- *lemma* polynomial.exists_multiset_of_splits
- \+/\- *lemma* polynomial.exists_root_of_splits
- \+/\- *def* polynomial.factor
- \+/\- *theorem* polynomial.factor_dvd_of_degree_ne_zero
- \+/\- *theorem* polynomial.factor_dvd_of_nat_degree_ne_zero
- \+/\- *theorem* polynomial.factor_dvd_of_not_is_unit
- \+/\- *def* polynomial.is_splitting_field.alg_equiv
- \+/\- *theorem* polynomial.is_splitting_field.finite_dimensional
- \+/\- *def* polynomial.is_splitting_field.lift
- \+/\- *theorem* polynomial.is_splitting_field.mul
- \+/\- *theorem* polynomial.is_splitting_field.splits_iff
- \+/\- *theorem* polynomial.map_root_of_splits
- \+/\- *lemma* polynomial.nat_degree_eq_card_roots
- \+/\- *theorem* polynomial.nat_degree_remove_factor'
- \+/\- *theorem* polynomial.nat_degree_remove_factor
- \+/\- *lemma* polynomial.prod_roots_eq_coeff_zero_of_monic_of_split
- \+/\- *def* polynomial.remove_factor
- \+/\- *def* polynomial.root_of_splits
- \+/\- *theorem* polynomial.roots_map
- \+/\- *def* polynomial.splits
- \+/\- *lemma* polynomial.splits_comp_of_splits
- \+/\- *theorem* polynomial.splits_id_iff_splits
- \+/\- *lemma* polynomial.splits_iff_card_roots
- \+/\- *lemma* polynomial.splits_iff_exists_multiset
- \+/\- *lemma* polynomial.splits_map_iff
- \+/\- *lemma* polynomial.splits_mul
- \+/\- *theorem* polynomial.splits_mul_iff
- \+/\- *lemma* polynomial.splits_of_degree_eq_one
- \+/\- *lemma* polynomial.splits_of_degree_le_one
- \+/\- *lemma* polynomial.splits_of_exists_multiset
- \+/\- *theorem* polynomial.splits_of_is_unit
- \+/\- *lemma* polynomial.splits_of_nat_degree_eq_one
- \+/\- *lemma* polynomial.splits_of_nat_degree_le_one
- \+/\- *lemma* polynomial.splits_of_splits_gcd_left
- \+/\- *lemma* polynomial.splits_of_splits_gcd_right
- \+/\- *lemma* polynomial.splits_of_splits_id
- \+/\- *lemma* polynomial.splits_of_splits_mul
- \+/\- *lemma* polynomial.splits_of_splits_of_dvd
- \+/\- *lemma* polynomial.splits_pow
- \+/\- *theorem* polynomial.splits_prod
- \+/\- *theorem* polynomial.splits_prod_iff
- \+/\- *lemma* polynomial.splits_zero
- \+/\- *def* polynomial.splitting_field
- \+/\- *theorem* polynomial.splitting_field_aux.algebra_map_succ
- \+/\- *theorem* polynomial.splitting_field_aux.succ
- \+/\- *def* polynomial.splitting_field_aux
- \+/\- *lemma* polynomial.sum_roots_eq_next_coeff_of_monic_of_split

Modified src/linear_algebra/charpoly/basic.lean
- \+/\- *def* linear_map.charpoly

Modified src/linear_algebra/eigenspace.lean


Modified src/linear_algebra/lagrange.lean
- \+/\- *def* lagrange.basis
- \+/\- *theorem* lagrange.eq_interpolate
- \+/\- *theorem* lagrange.eq_interpolate_of_eval_eq
- \+/\- *theorem* lagrange.eq_of_eval_eq
- \+/\- *theorem* lagrange.eq_zero_of_eval_eq_zero
- \+/\- *def* lagrange.interpolate

Modified src/linear_algebra/matrix/adjugate.lean


Modified src/linear_algebra/matrix/charpoly/basic.lean
- \+/\- *def* charmatrix
- \+/\- *def* matrix.charpoly

Modified src/linear_algebra/matrix/charpoly/coeff.lean
- \+/\- *lemma* matrix.eval_det
- \+/\- *lemma* matrix.mat_poly_equiv_eval

Modified src/linear_algebra/matrix/polynomial.lean


Modified src/linear_algebra/smodeq.lean


Modified src/number_theory/bernoulli_polynomials.lean
- \+/\- *def* polynomial.bernoulli

Modified src/number_theory/class_number/admissible_card_pow_degree.lean
- \+/\- *lemma* polynomial.card_pow_degree_anti_archimedean
- \+/\- *lemma* polynomial.exists_approx_polynomial
- \+/\- *lemma* polynomial.exists_eq_polynomial

Modified src/number_theory/class_number/function_field.lean


Modified src/number_theory/function_field.lean
- \+/\- *def* function_field.ring_of_integers

Modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* adjoin_root.aeval_eq
- \+/\- *def* adjoin_root.equiv
- \+/\- *lemma* adjoin_root.eval₂_root
- \+/\- *lemma* adjoin_root.is_root_root
- \+/\- *lemma* adjoin_root.lift_hom_eq_alg_hom
- \+/\- *lemma* adjoin_root.lift_hom_mk
- \+/\- *lemma* adjoin_root.lift_mk
- \+/\- *def* adjoin_root.mk
- \+/\- *lemma* adjoin_root.mk_eq_mk
- \+/\- *lemma* adjoin_root.mod_by_monic_hom_mk
- \+/\- *def* adjoin_root

Modified src/ring_theory/algebraic.lean
- \+/\- *lemma* inv_eq_of_aeval_div_X_ne_zero
- \+/\- *lemma* inv_eq_of_root_of_coeff_zero_ne_zero
- \+/\- *lemma* subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero

Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/eisenstein_criterion.lean
- \+/\- *lemma* polynomial.eisenstein_criterion_aux.is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit
- \+/\- *lemma* polynomial.eisenstein_criterion_aux.map_eq_C_mul_X_pow_of_forall_coeff_mem
- \+/\- *theorem* polynomial.irreducible_of_eisenstein_criterion

Modified src/ring_theory/finiteness.lean
- \+/\- *lemma* module_polynomial_of_endo.is_scalar_tower
- \+/\- *def* module_polynomial_of_endo

Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* polynomial.algebra_map_hahn_series_apply

Modified src/ring_theory/henselian.lean


Modified src/ring_theory/ideal/over.lean
- \+/\- *lemma* ideal.coeff_zero_mem_comap_of_root_mem
- \+/\- *lemma* ideal.coeff_zero_mem_comap_of_root_mem_of_eval_mem
- \+/\- *lemma* ideal.exists_nonzero_mem_of_ne_bot
- \+/\- *lemma* ideal.injective_quotient_le_comap_map
- \+/\- *lemma* ideal.quotient_mk_maps_eq

Modified src/ring_theory/integral_closure.lean
- \+/\- *lemma* is_integral_trans_aux
- \+/\- *lemma* leading_coeff_smul_normalize_scale_roots
- \+/\- *def* normalize_scale_roots

Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/jacobson_ideal.lean


Modified src/ring_theory/laurent_series.lean
- \+ *lemma* power_series.coe_neg
- \+ *lemma* power_series.coe_sub

Modified src/ring_theory/localization.lean
- \+/\- *lemma* is_fraction_ring.integer_normalization_eq_zero_iff
- \+/\- *theorem* is_integral_localization_at_leading_coeff
- \+/\- *lemma* is_localization.coeff_integer_normalization_mem_support
- \+/\- *lemma* is_localization.coeff_integer_normalization_of_not_mem_support
- \+/\- *lemma* is_localization.integer_normalization_coeff
- \+/\- *lemma* is_localization.integer_normalization_eval₂_eq_zero
- \+/\- *lemma* is_localization.integer_normalization_map_to_map
- \+/\- *lemma* is_localization.integer_normalization_spec

Modified src/ring_theory/mv_polynomial/basic.lean


Modified src/ring_theory/polynomial/basic.lean
- \+/\- *def* ideal.degree_le
- \+/\- *lemma* ideal.eq_zero_of_polynomial_mem_map_range
- \+/\- *theorem* ideal.mem_map_C_iff
- \+/\- *def* ideal.of_polynomial
- \+/\- *lemma* ideal.polynomial_mem_ideal_of_coeff_mem_ideal
- \+/\- *lemma* ideal.polynomial_not_is_field
- \+/\- *lemma* ideal.polynomial_quotient_equiv_quotient_polynomial_map_mk
- \+/\- *lemma* ideal.polynomial_quotient_equiv_quotient_polynomial_symm_mk
- \+/\- *lemma* polynomial.coeff_mem_frange
- \+/\- *lemma* polynomial.coeff_of_subring
- \+/\- *theorem* polynomial.coeff_restriction'
- \+/\- *theorem* polynomial.coeff_restriction
- \+/\- *def* polynomial.degree_le
- \+/\- *def* polynomial.degree_lt
- \+/\- *theorem* polynomial.degree_restriction
- \+/\- *theorem* polynomial.eval₂_restriction
- \+/\- *def* polynomial.frange
- \+/\- *theorem* polynomial.frange_of_subring
- \+/\- *lemma* polynomial.frange_one
- \+/\- *lemma* polynomial.frange_zero
- \+/\- *theorem* polynomial.map_restriction
- \+/\- *theorem* polynomial.mem_degree_le
- \+/\- *theorem* polynomial.mem_degree_lt
- \+/\- *lemma* polynomial.mem_frange_iff
- \+/\- *lemma* polynomial.mem_ker_mod_by_monic
- \+/\- *theorem* polynomial.monic_restriction
- \+/\- *theorem* polynomial.nat_degree_restriction
- \+/\- *def* polynomial.of_subring
- \+/\- *def* polynomial.restriction
- \+/\- *theorem* polynomial.restriction_one
- \+/\- *theorem* polynomial.restriction_zero
- \+/\- *lemma* polynomial.sup_ker_aeval_le_ker_aeval_mul
- \+/\- *lemma* polynomial.support_restriction
- \+/\- *def* polynomial.to_subring
- \+/\- *theorem* polynomial.to_subring_one
- \+/\- *theorem* polynomial.to_subring_zero

Modified src/ring_theory/polynomial/bernstein.lean
- \+/\- *def* bernstein_polynomial

Modified src/ring_theory/polynomial/chebyshev.lean


Modified src/ring_theory/polynomial/content.lean
- \+/\- *lemma* polynomial.C_content_dvd
- \+/\- *def* polynomial.content
- \+/\- *lemma* polynomial.content_C_mul
- \+/\- *lemma* polynomial.content_X
- \+/\- *lemma* polynomial.content_X_mul
- \+/\- *lemma* polynomial.content_X_pow
- \+/\- *lemma* polynomial.content_dvd_coeff
- \+/\- *lemma* polynomial.content_eq_gcd_leading_coeff_content_erase_lead
- \+/\- *lemma* polynomial.content_eq_gcd_range_of_lt
- \+/\- *lemma* polynomial.content_eq_gcd_range_succ
- \+/\- *lemma* polynomial.content_eq_zero_iff
- \+/\- *theorem* polynomial.content_mul
- \+/\- *lemma* polynomial.content_mul_aux
- \+/\- *lemma* polynomial.content_one
- \+/\- *lemma* polynomial.content_prim_part
- \+/\- *lemma* polynomial.content_zero
- \+/\- *lemma* polynomial.degree_gcd_le_left
- \+/\- *lemma* polynomial.degree_gcd_le_right
- \+/\- *lemma* polynomial.dvd_content_iff_C_dvd
- \+/\- *lemma* polynomial.eq_C_content_mul_prim_part
- \+/\- *theorem* polynomial.exists_primitive_lcm_of_is_primitive
- \+/\- *lemma* polynomial.gcd_content_eq_of_dvd_sub
- \+/\- *lemma* polynomial.is_primitive.content_eq_one
- \+/\- *lemma* polynomial.is_primitive.dvd_prim_part_iff_dvd
- \+/\- *lemma* polynomial.is_primitive.is_primitive_of_dvd
- \+/\- *theorem* polynomial.is_primitive.mul
- \+/\- *lemma* polynomial.is_primitive.ne_zero
- \+/\- *lemma* polynomial.is_primitive.prim_part_eq
- \+/\- *def* polynomial.is_primitive
- \+/\- *lemma* polynomial.is_primitive_iff_content_eq_one
- \+/\- *lemma* polynomial.is_primitive_iff_is_unit_of_C_dvd
- \+/\- *lemma* polynomial.is_primitive_one
- \+/\- *lemma* polynomial.is_primitive_prim_part
- \+/\- *lemma* polynomial.monic.is_primitive
- \+/\- *lemma* polynomial.nat_degree_prim_part
- \+/\- *lemma* polynomial.normalize_content
- \+/\- *def* polynomial.prim_part
- \+/\- *lemma* polynomial.prim_part_dvd
- \+/\- *theorem* polynomial.prim_part_mul
- \+/\- *lemma* polynomial.prim_part_ne_zero
- \+/\- *lemma* polynomial.prim_part_zero

Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+/\- *def* polynomial.cyclotomic'
- \+/\- *def* polynomial.cyclotomic
- \+/\- *lemma* polynomial.int_cyclotomic_unique

Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/polynomial/eisenstein.lean
- \+/\- *structure* polynomial.is_eisenstein_at
- \+/\- *structure* polynomial.is_weakly_eisenstein_at

Modified src/ring_theory/polynomial/gauss_lemma.lean
- \+/\- *lemma* polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map
- \+/\- *lemma* polynomial.is_primitive.dvd_of_fraction_map_dvd_fraction_map
- \+/\- *lemma* polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast
- \+/\- *lemma* polynomial.is_primitive.is_unit_iff_is_unit_map

Modified src/ring_theory/polynomial/pochhammer.lean
- \+/\- *lemma* polynomial.mul_X_add_nat_cast_comp

Modified src/ring_theory/polynomial/rational_root.lean
- \+/\- *theorem* denom_dvd_of_is_root
- \+/\- *theorem* is_integer_of_is_root_of_monic
- \+/\- *theorem* num_dvd_of_is_root
- \+/\- *lemma* scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero

Modified src/ring_theory/polynomial/scale_roots.lean
- \+/\- *lemma* coeff_scale_roots
- \+/\- *lemma* coeff_scale_roots_nat_degree
- \+/\- *lemma* degree_scale_roots
- \+/\- *lemma* monic_scale_roots_iff
- \+/\- *lemma* nat_degree_scale_roots
- \+/\- *lemma* scale_roots_aeval_eq_zero
- \+/\- *lemma* scale_roots_eval₂_eq_zero
- \+/\- *lemma* scale_roots_ne_zero
- \+/\- *lemma* support_scale_roots_eq
- \+/\- *lemma* support_scale_roots_le

Modified src/ring_theory/polynomial/tower.lean
- \+/\- *theorem* is_scalar_tower.aeval_apply
- \+/\- *lemma* is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero
- \+/\- *lemma* is_scalar_tower.algebra_map_aeval
- \+/\- *lemma* subalgebra.aeval_coe

Modified src/ring_theory/polynomial/vieta.lean


Modified src/ring_theory/polynomial_algebra.lean
- \+/\- *lemma* mat_poly_equiv_smul_one
- \+/\- *def* poly_equiv_tensor.equiv
- \+/\- *def* poly_equiv_tensor.inv_fun
- \+/\- *lemma* poly_equiv_tensor.left_inv
- \+/\- *lemma* poly_equiv_tensor.right_inv
- \+/\- *def* poly_equiv_tensor.to_fun_alg_hom
- \+/\- *lemma* poly_equiv_tensor.to_fun_alg_hom_apply_tmul
- \+/\- *def* poly_equiv_tensor.to_fun_bilinear
- \+/\- *lemma* poly_equiv_tensor.to_fun_bilinear_apply_eq_sum
- \+/\- *def* poly_equiv_tensor.to_fun_linear
- \+/\- *lemma* poly_equiv_tensor.to_fun_linear_mul_tmul_mul
- \+/\- *lemma* poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_2
- \+/\- *lemma* poly_equiv_tensor.to_fun_linear_tmul_apply
- \+/\- *def* poly_equiv_tensor
- \+/\- *lemma* poly_equiv_tensor_apply
- \+/\- *lemma* poly_equiv_tensor_symm_apply_tmul

Modified src/ring_theory/power_basis.lean
- \+/\- *lemma* power_basis.dim_le_degree_of_root
- \+/\- *lemma* power_basis.dim_le_nat_degree_of_root
- \+/\- *lemma* power_basis.nat_degree_lt_nat_degree

Modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* mv_power_series.map_X
- \+/\- *lemma* polynomial.coe_injective
- \+/\- *lemma* polynomial.coe_one
- \+/\- *def* polynomial.coe_to_power_series.alg_hom
- \+/\- *def* polynomial.coe_to_power_series.ring_hom
- \+/\- *lemma* polynomial.coe_zero
- \+/\- *lemma* power_series.algebra_map_apply'
- \+/\- *def* power_series.trunc

Modified src/ring_theory/roots_of_unity.lean


Modified src/topology/algebra/polynomial.lean
- \+/\- *lemma* polynomial.exists_forall_norm_le
- \+/\- *lemma* polynomial.tendsto_norm_at_top

Modified src/topology/continuous_function/polynomial.lean
- \+/\- *lemma* polynomial.aeval_continuous_map_apply
- \+/\- *def* polynomial.to_continuous_map
- \+/\- *def* polynomial.to_continuous_map_alg_hom
- \+/\- *def* polynomial.to_continuous_map_on
- \+/\- *def* polynomial.to_continuous_map_on_alg_hom

Modified test/differentiable.lean


Modified test/instance_diamonds.lean


Modified test/library_search/ring_theory.lean




## [2022-02-08 09:20:10](https://github.com/leanprover-community/mathlib/commit/5932581)
feat(group_theory/submonoid/operations): prod_le_iff and le_prod_iff, also for groups and modules ([#11898](https://github.com/leanprover-community/mathlib/pull/11898))
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+ *lemma* submodule.to_add_subgroup_le
- \+ *lemma* submodule.to_add_submonoid_le

Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.le_prod_iff
- \+ *lemma* subgroup.map_one_eq_bot
- \+ *lemma* subgroup.prod_eq_bot_iff
- \+ *lemma* subgroup.prod_le_iff

Modified src/group_theory/submonoid/operations.lean
- \+ *lemma* monoid_hom.mker_inl
- \+ *lemma* monoid_hom.mker_inr
- \+ *lemma* submonoid.le_prod_iff
- \+ *lemma* submonoid.prod_eq_bot_iff
- \+ *lemma* submonoid.prod_eq_top_iff
- \+ *lemma* submonoid.prod_le_iff

Modified src/linear_algebra/prod.lean
- \+ *lemma* submodule.le_prod_iff
- \+ *lemma* submodule.prod_eq_bot_iff
- \+ *lemma* submodule.prod_eq_top_iff
- \+ *lemma* submodule.prod_le_iff

Modified src/order/galois_connection.lean
- \+ *lemma* galois_connection.le_iff_le



## [2022-02-08 08:51:03](https://github.com/leanprover-community/mathlib/commit/2b68801)
refactor(number_theory/bernoulli_polynomials): improve names ([#11805](https://github.com/leanprover-community/mathlib/pull/11805))
Cleanup the bernoulli_polynomials file
#### Estimated changes
Modified src/number_theory/bernoulli_polynomials.lean
- \- *lemma* bernoulli_poly.bernoulli_poly_eval_one
- \- *lemma* bernoulli_poly.bernoulli_poly_eval_zero
- \- *lemma* bernoulli_poly.bernoulli_poly_zero
- \- *theorem* bernoulli_poly.exp_bernoulli_poly'
- \- *theorem* bernoulli_poly.sum_bernoulli_poly
- \- *def* bernoulli_poly
- \- *lemma* bernoulli_poly_def
- \+ *def* polynomial.bernoulli
- \+ *lemma* polynomial.bernoulli_def
- \+ *lemma* polynomial.bernoulli_eval_one
- \+ *lemma* polynomial.bernoulli_eval_zero
- \+ *theorem* polynomial.bernoulli_generating_function
- \+ *lemma* polynomial.bernoulli_zero
- \+ *theorem* polynomial.sum_bernoulli



## [2022-02-08 04:53:51](https://github.com/leanprover-community/mathlib/commit/1077eb3)
feat(analysis/complex): a few lemmas about `dist` and `conj` ([#11913](https://github.com/leanprover-community/mathlib/pull/11913))
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.dist_conj_comm
- \+ *lemma* complex.dist_conj_conj
- \+ *lemma* complex.dist_conj_self
- \+ *lemma* complex.dist_self_conj



## [2022-02-07 20:25:46](https://github.com/leanprover-community/mathlib/commit/36d3b68)
feat(linear_algebra/basis): `basis.map_equiv_fun` ([#11888](https://github.com/leanprover-community/mathlib/pull/11888))
Add a `simp` lemma about the effect of `equiv_fun` for a basis
obtained with `basis.map`.
#### Estimated changes
Modified src/linear_algebra/basis.lean
- \+ *lemma* basis.map_equiv_fun



## [2022-02-07 19:33:57](https://github.com/leanprover-community/mathlib/commit/f94b0b3)
style(analysis/special_functions/trigonometric/angle): make types of `sin` and `cos` explicit ([#11902](https://github.com/leanprover-community/mathlib/pull/11902))
Give the types of the results of `real.angle.sin` and `real.angle.cos`
explicitly, as requested by @eric-wieser in [#11887](https://github.com/leanprover-community/mathlib/pull/11887).
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/angle.lean
- \+/\- *def* real.angle.cos
- \+/\- *def* real.angle.sin



## [2022-02-07 19:33:56](https://github.com/leanprover-community/mathlib/commit/9ceb3c2)
feat(topology/sheaf_condition): connect sheaves on sites and on spaces without has_products ([#11706](https://github.com/leanprover-community/mathlib/pull/11706))
As an application of [#11692](https://github.com/leanprover-community/mathlib/pull/11692), show that the is_sheaf_opens_le_cover sheaf condition on spaces is equivalent to is_sheaf on sites, thereby connecting sheaves on sites and on spaces without the value category has_products for the first time. (@justus-springer: you might want to take a look so as to determine whether and which of your work in [#9609](https://github.com/leanprover-community/mathlib/pull/9609) should be deprecated.) This could be seen as a step towards refactoring sheaves on spaces through sheaves on sites.
- [x] depends on: [#11692](https://github.com/leanprover-community/mathlib/pull/11692)
#### Estimated changes
Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean
- \+ *def* Top.presheaf.generate_equivalence_opens_le
- \+ *def* Top.presheaf.is_limit_opens_le_equiv_generate₁
- \+ *def* Top.presheaf.is_limit_opens_le_equiv_generate₂
- \+ *lemma* Top.presheaf.is_sheaf_sites_iff_is_sheaf_opens_le_cover
- \+ *def* Top.presheaf.whisker_iso_map_generate_cocone

Modified src/topology/sheaves/sheaf_condition/sites.lean
- \+ *lemma* Top.presheaf.covering_presieve_eq_self
- \+ *def* Top.presheaf.presieve_of_covering_aux



## [2022-02-07 17:28:22](https://github.com/leanprover-community/mathlib/commit/436966c)
chore(data/finsupp/basic): generalize comap_mul_action ([#11900](https://github.com/leanprover-community/mathlib/pull/11900))
This new definition is propoitionally equal to the old one in the presence of `[group G]` (all the previous `lemma`s continue to apply), but generalizes to `[monoid G]`.
This also removes `finsupp.comap_distrib_mul_action_self` as there is no need to have this as a separate definition.
#### Estimated changes
Modified src/algebra/monoid_algebra/basic.lean


Modified src/data/finsupp/basic.lean
- \- *def* finsupp.comap_distrib_mul_action_self
- \+/\- *lemma* finsupp.comap_smul_apply
- \+ *lemma* finsupp.comap_smul_def
- \+/\- *lemma* finsupp.comap_smul_single

Modified src/group_theory/group_action/defs.lean
- \+ *lemma* comp_smul_left
- \+ *lemma* one_smul_eq_id



## [2022-02-07 17:28:21](https://github.com/leanprover-community/mathlib/commit/7b91f00)
feat(algebra/big_operators/basic): add multiset.prod_sum ([#11885](https://github.com/leanprover-community/mathlib/pull/11885))
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* multiset.prod_sum



## [2022-02-07 15:42:07](https://github.com/leanprover-community/mathlib/commit/02c9d69)
feat(analysis/inner_product_space/basic): `orthonormal.map_linear_isometry_equiv` ([#11893](https://github.com/leanprover-community/mathlib/pull/11893))
Add a variant of `orthonormal.comp_linear_isometry_equiv` for the case
of an orthonormal basis mapped with `basis.map`.
If in future we get a bundled type of orthonormal bases with its own
`map` operation, this would no longer be a separate lemma, but until
then it's useful.
#### Estimated changes
Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* orthonormal.map_linear_isometry_equiv



## [2022-02-07 15:42:06](https://github.com/leanprover-community/mathlib/commit/c61ea33)
feat(analysis/complex/isometry): `rotation_symm` ([#11891](https://github.com/leanprover-community/mathlib/pull/11891))
Add a `simp` lemma that the inverse of `rotation` is rotation by the
inverse angle.
#### Estimated changes
Modified src/analysis/complex/isometry.lean
- \+ *lemma* rotation_symm



## [2022-02-07 15:42:04](https://github.com/leanprover-community/mathlib/commit/2364a09)
feat(analysis/complex/circle): `exp_map_circle_neg` ([#11889](https://github.com/leanprover-community/mathlib/pull/11889))
Add the lemma `exp_map_circle_neg`, similar to other lemmas for
`exp_map_circle` that are already present.
#### Estimated changes
Modified src/analysis/complex/circle.lean
- \+ *lemma* exp_map_circle_neg



## [2022-02-07 15:42:03](https://github.com/leanprover-community/mathlib/commit/99215e3)
feat(analysis/special_functions/trigonometric/angle): `sin`, `cos` ([#11887](https://github.com/leanprover-community/mathlib/pull/11887))
Add definitions of `sin` and `cos` that act on a `real.angle`.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *def* real.angle.cos
- \+ *lemma* real.angle.cos_coe
- \+ *def* real.angle.sin
- \+ *lemma* real.angle.sin_coe



## [2022-02-07 15:42:01](https://github.com/leanprover-community/mathlib/commit/98ef84e)
feat(analysis/special_functions/trigonometric/angle): `induction_on` ([#11886](https://github.com/leanprover-community/mathlib/pull/11886))
Add `real.angle.induction_on`, for use in deducing results for
`real.angle` from those for `ℝ`.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/angle.lean




## [2022-02-07 15:42:00](https://github.com/leanprover-community/mathlib/commit/26179cc)
feat(data/list): add some lemmas. ([#11879](https://github.com/leanprover-community/mathlib/pull/11879))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.filter_length_eq_length

Modified src/data/list/count.lean
- \+ *lemma* list.count_eq_length
- \+ *lemma* list.countp_eq_length



## [2022-02-07 15:41:58](https://github.com/leanprover-community/mathlib/commit/dcbb59c)
feat(category_theory/limits): is_limit.exists_unique ([#11875](https://github.com/leanprover-community/mathlib/pull/11875))
Yet another restatement of the limit property which is occasionally useful.
#### Estimated changes
Modified src/category_theory/limits/has_limits.lean
- \+ *lemma* category_theory.limits.colimit.exists_unique
- \+ *lemma* category_theory.limits.limit.exists_unique

Modified src/category_theory/limits/is_limit.lean
- \+ *lemma* category_theory.limits.is_colimit.exists_unique
- \+ *def* category_theory.limits.is_colimit.of_exists_unique
- \+ *lemma* category_theory.limits.is_limit.exists_unique
- \+ *def* category_theory.limits.is_limit.of_exists_unique

Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* category_theory.limits.coequalizer.exists_unique
- \+ *lemma* category_theory.limits.cofork.is_colimit.exists_unique
- \+ *def* category_theory.limits.cofork.is_colimit.of_exists_unique
- \+ *lemma* category_theory.limits.equalizer.exists_unique
- \+ *lemma* category_theory.limits.fork.is_limit.exists_unique
- \+ *def* category_theory.limits.fork.is_limit.of_exists_unique



## [2022-02-07 15:41:57](https://github.com/leanprover-community/mathlib/commit/556483f)
feat(category_theory/limits): (co)equalizers in the opposite category ([#11874](https://github.com/leanprover-community/mathlib/pull/11874))
#### Estimated changes
Modified src/category_theory/limits/opposites.lean
- \+ *lemma* category_theory.limits.has_coequalizers_opposite
- \+ *lemma* category_theory.limits.has_equalizers_opposite



## [2022-02-07 15:41:55](https://github.com/leanprover-community/mathlib/commit/7a2a546)
feat(data/set/opposite): the opposite of a set ([#11860](https://github.com/leanprover-community/mathlib/pull/11860))
#### Estimated changes
Added src/data/set/opposite.lean
- \+ *lemma* set.mem_op
- \+ *lemma* set.mem_unop
- \+ *def* set.op_equiv
- \+ *lemma* set.op_mem_op
- \+ *lemma* set.op_unop
- \+ *lemma* set.singleton_op
- \+ *lemma* set.singleton_op_unop
- \+ *lemma* set.singleton_unop
- \+ *lemma* set.singleton_unop_op
- \+ *lemma* set.unop_mem_unop
- \+ *lemma* set.unop_op



## [2022-02-07 15:41:54](https://github.com/leanprover-community/mathlib/commit/0354e56)
feat(order/complete_lattice): infi_le_iff ([#11810](https://github.com/leanprover-community/mathlib/pull/11810))
Add missing lemma `infi_le_iff {s : ι → α} : infi s ≤ a ↔ (∀ b, (∀ i, b ≤ s i) → b ≤ a)`
Also take the opportunity to restate `Inf_le_iff` to restore consistency with `le_Sup_iff` that was broken in [#10607](https://github.com/leanprover-community/mathlib/pull/10607) and move `le_supr_iff` close to `le_Sup_iff` and remove a couple of unneeded parentheses.
#### Estimated changes
Modified src/order/complete_lattice.lean
- \+/\- *theorem* Sup_le_iff
- \+ *lemma* infi_le_iff
- \+/\- *lemma* le_Sup_iff
- \+/\- *lemma* le_supr_iff
- \+/\- *theorem* supr_le_iff



## [2022-02-07 14:32:55](https://github.com/leanprover-community/mathlib/commit/a2f3f55)
chore(algebra/monoid_algebra): generalize lift_nc ([#11881](https://github.com/leanprover-community/mathlib/pull/11881))
The g argument does not need to be a bundled morphism here in the definition.
Instead, we require it be a bundled morphism only in the downstream lemmas, using the new typeclass machinery
#### Estimated changes
Modified src/algebra/monoid_algebra/basic.lean
- \+/\- *def* add_monoid_algebra.lift_nc
- \+/\- *lemma* add_monoid_algebra.lift_nc_mul
- \+/\- *lemma* add_monoid_algebra.lift_nc_one
- \+/\- *lemma* add_monoid_algebra.lift_nc_single
- \+/\- *def* monoid_algebra.lift_nc
- \+/\- *lemma* monoid_algebra.lift_nc_mul
- \+/\- *lemma* monoid_algebra.lift_nc_one
- \+/\- *lemma* monoid_algebra.lift_nc_single



## [2022-02-07 12:33:08](https://github.com/leanprover-community/mathlib/commit/04b9d28)
feat(data/pfun): Composition of partial functions ([#11865](https://github.com/leanprover-community/mathlib/pull/11865))
Define
* `pfun.id`: The identity as a partial function
* `pfun.comp`: Composition of partial functions
* `pfun.to_subtype`: Restrict the codomain of a function to a subtype and make it partial
#### Estimated changes
Modified src/data/part.lean
- \+ *lemma* part.bind_to_option
- \+ *lemma* part.dom.of_bind
- \+ *lemma* part.elim_to_option
- \+ *lemma* part.mem_mk_iff
- \+/\- *lemma* part.some_inj
- \+ *lemma* part.some_injective
- \+ *lemma* part.to_option_eq_none_iff

Modified src/data/pfun.lean
- \+ *lemma* part.bind_comp
- \+ *lemma* pfun.bind_apply
- \+ *lemma* pfun.coe_comp
- \+ *lemma* pfun.coe_id
- \+ *lemma* pfun.coe_injective
- \+ *def* pfun.comp
- \+ *lemma* pfun.comp_apply
- \+ *lemma* pfun.comp_assoc
- \+ *lemma* pfun.comp_id
- \+ *lemma* pfun.dom_coe
- \+ *lemma* pfun.dom_comp
- \+ *lemma* pfun.dom_to_subtype
- \+ *lemma* pfun.dom_to_subtype_apply_iff
- \+/\- *def* pfun.fn
- \+ *lemma* pfun.fn_apply
- \+ *lemma* pfun.id_apply
- \+ *lemma* pfun.id_comp
- \+/\- *lemma* pfun.mem_core
- \+ *lemma* pfun.mem_dom
- \- *theorem* pfun.mem_dom
- \+/\- *lemma* pfun.mem_preimage
- \+ *lemma* pfun.mem_to_subtype_iff
- \+ *lemma* pfun.preimage_comp
- \+ *def* pfun.to_subtype
- \+ *lemma* pfun.to_subtype_apply

Modified src/data/subtype.lean
- \+ *lemma* exists_eq_subtype_mk_iff
- \+ *lemma* exists_subtype_mk_eq_iff



## [2022-02-07 11:17:01](https://github.com/leanprover-community/mathlib/commit/0090891)
chore(model_theory/*): Split up model_theory/basic ([#11846](https://github.com/leanprover-community/mathlib/pull/11846))
Splits model_theory/basic into separate files: basic, substructures, terms_and_formulas, definability, quotients
Improves documentation throughout
#### Estimated changes
Modified src/model_theory/basic.lean
- \- *def* first_order.language.bd_not
- \- *def* first_order.language.bounded_formula.relabel
- \- *inductive* first_order.language.bounded_formula
- \- *lemma* first_order.language.closed_under.Inf
- \- *lemma* first_order.language.closed_under.inf
- \- *lemma* first_order.language.closed_under.inter
- \- *def* first_order.language.closed_under
- \- *lemma* first_order.language.closed_under_univ
- \- *lemma* first_order.language.definable_set.coe_bot
- \- *lemma* first_order.language.definable_set.coe_compl
- \- *lemma* first_order.language.definable_set.coe_inf
- \- *lemma* first_order.language.definable_set.coe_sup
- \- *lemma* first_order.language.definable_set.coe_top
- \- *lemma* first_order.language.definable_set.le_iff
- \- *lemma* first_order.language.definable_set.mem_compl
- \- *lemma* first_order.language.definable_set.mem_inf
- \- *lemma* first_order.language.definable_set.mem_sup
- \- *lemma* first_order.language.definable_set.mem_top
- \- *lemma* first_order.language.definable_set.not_mem_bot
- \- *def* first_order.language.definable_set
- \- *lemma* first_order.language.embedding.realize_term
- \- *lemma* first_order.language.equiv.realize_bounded_formula
- \- *lemma* first_order.language.equiv.realize_term
- \- *def* first_order.language.formula.equal
- \- *def* first_order.language.formula.graph
- \- *def* first_order.language.formula
- \- *lemma* first_order.language.fun_map_quotient_mk
- \- *def* first_order.language.hom.eq_locus
- \- *lemma* first_order.language.hom.eq_of_eq_on_dense
- \- *lemma* first_order.language.hom.eq_of_eq_on_top
- \- *lemma* first_order.language.hom.eq_on_closure
- \- *lemma* first_order.language.hom.realize_term
- \- *lemma* first_order.language.is_definable.compl
- \- *lemma* first_order.language.is_definable.inter
- \- *lemma* first_order.language.is_definable.sdiff
- \- *lemma* first_order.language.is_definable.union
- \- *structure* first_order.language.is_definable
- \- *lemma* first_order.language.is_definable_empty
- \- *lemma* first_order.language.is_definable_univ
- \- *def* first_order.language.realize_bounded_formula
- \- *lemma* first_order.language.realize_bounded_formula_relabel
- \- *lemma* first_order.language.realize_bounded_formula_top
- \- *lemma* first_order.language.realize_equal
- \- *def* first_order.language.realize_formula
- \- *lemma* first_order.language.realize_formula_equiv
- \- *lemma* first_order.language.realize_formula_relabel
- \- *lemma* first_order.language.realize_graph
- \- *lemma* first_order.language.realize_not
- \- *def* first_order.language.realize_sentence
- \- *def* first_order.language.realize_term
- \- *lemma* first_order.language.realize_term_quotient_mk
- \- *lemma* first_order.language.realize_term_relabel
- \- *lemma* first_order.language.realize_term_substructure
- \- *def* first_order.language.sentence
- \- *lemma* first_order.language.substructure.apply_coe_mem_map
- \- *lemma* first_order.language.substructure.closed
- \- *def* first_order.language.substructure.closure
- \- *lemma* first_order.language.substructure.closure_Union
- \- *lemma* first_order.language.substructure.closure_empty
- \- *lemma* first_order.language.substructure.closure_eq
- \- *lemma* first_order.language.substructure.closure_eq_of_le
- \- *lemma* first_order.language.substructure.closure_induction'
- \- *lemma* first_order.language.substructure.closure_induction
- \- *lemma* first_order.language.substructure.closure_le
- \- *lemma* first_order.language.substructure.closure_mono
- \- *lemma* first_order.language.substructure.closure_union
- \- *lemma* first_order.language.substructure.closure_univ
- \- *lemma* first_order.language.substructure.coe_Inf
- \- *lemma* first_order.language.substructure.coe_copy
- \- *lemma* first_order.language.substructure.coe_inf
- \- *lemma* first_order.language.substructure.coe_infi
- \- *theorem* first_order.language.substructure.coe_subtype
- \- *lemma* first_order.language.substructure.coe_top
- \- *lemma* first_order.language.substructure.coe_top_equiv
- \- *def* first_order.language.substructure.comap
- \- *lemma* first_order.language.substructure.comap_comap
- \- *lemma* first_order.language.substructure.comap_id
- \- *lemma* first_order.language.substructure.comap_inf
- \- *lemma* first_order.language.substructure.comap_inf_map_of_injective
- \- *lemma* first_order.language.substructure.comap_infi
- \- *lemma* first_order.language.substructure.comap_infi_map_of_injective
- \- *lemma* first_order.language.substructure.comap_injective_of_surjective
- \- *lemma* first_order.language.substructure.comap_le_comap_iff_of_surjective
- \- *lemma* first_order.language.substructure.comap_map_comap
- \- *lemma* first_order.language.substructure.comap_map_eq_of_injective
- \- *lemma* first_order.language.substructure.comap_strict_mono_of_surjective
- \- *lemma* first_order.language.substructure.comap_sup_map_of_injective
- \- *lemma* first_order.language.substructure.comap_supr_map_of_injective
- \- *lemma* first_order.language.substructure.comap_surjective_of_injective
- \- *lemma* first_order.language.substructure.comap_top
- \- *lemma* first_order.language.substructure.const_mem
- \- *lemma* first_order.language.substructure.copy_eq
- \- *lemma* first_order.language.substructure.dense_induction
- \- *theorem* first_order.language.substructure.ext
- \- *lemma* first_order.language.substructure.gc_map_comap
- \- *def* first_order.language.substructure.gci_map_comap
- \- *def* first_order.language.substructure.gi_map_comap
- \- *lemma* first_order.language.substructure.le_comap_map
- \- *lemma* first_order.language.substructure.le_comap_of_map_le
- \- *def* first_order.language.substructure.map
- \- *lemma* first_order.language.substructure.map_bot
- \- *lemma* first_order.language.substructure.map_comap_eq_of_surjective
- \- *lemma* first_order.language.substructure.map_comap_le
- \- *lemma* first_order.language.substructure.map_comap_map
- \- *lemma* first_order.language.substructure.map_id
- \- *lemma* first_order.language.substructure.map_inf_comap_of_surjective
- \- *lemma* first_order.language.substructure.map_infi_comap_of_surjective
- \- *lemma* first_order.language.substructure.map_injective_of_injective
- \- *lemma* first_order.language.substructure.map_le_iff_le_comap
- \- *lemma* first_order.language.substructure.map_le_map_iff_of_injective
- \- *lemma* first_order.language.substructure.map_le_of_le_comap
- \- *lemma* first_order.language.substructure.map_map
- \- *lemma* first_order.language.substructure.map_strict_mono_of_injective
- \- *lemma* first_order.language.substructure.map_sup
- \- *lemma* first_order.language.substructure.map_sup_comap_of_surjective
- \- *lemma* first_order.language.substructure.map_supr
- \- *lemma* first_order.language.substructure.map_supr_comap_of_surjective
- \- *lemma* first_order.language.substructure.map_surjective_of_surjective
- \- *lemma* first_order.language.substructure.mem_Inf
- \- *lemma* first_order.language.substructure.mem_carrier
- \- *lemma* first_order.language.substructure.mem_closure
- \- *lemma* first_order.language.substructure.mem_comap
- \- *lemma* first_order.language.substructure.mem_inf
- \- *lemma* first_order.language.substructure.mem_infi
- \- *lemma* first_order.language.substructure.mem_map
- \- *lemma* first_order.language.substructure.mem_map_of_mem
- \- *lemma* first_order.language.substructure.mem_top
- \- *lemma* first_order.language.substructure.monotone_comap
- \- *lemma* first_order.language.substructure.monotone_map
- \- *lemma* first_order.language.substructure.not_mem_of_not_mem_closure
- \- *def* first_order.language.substructure.simps.coe
- \- *lemma* first_order.language.substructure.subset_closure
- \- *def* first_order.language.substructure.subtype
- \- *def* first_order.language.substructure.top_equiv
- \- *structure* first_order.language.substructure
- \- *def* first_order.language.term.relabel
- \- *inductive* first_order.language.term
- \- *def* first_order.language.theory

Added src/model_theory/definability.lean
- \+ *lemma* first_order.language.definable_set.coe_bot
- \+ *lemma* first_order.language.definable_set.coe_compl
- \+ *lemma* first_order.language.definable_set.coe_inf
- \+ *lemma* first_order.language.definable_set.coe_sup
- \+ *lemma* first_order.language.definable_set.coe_top
- \+ *lemma* first_order.language.definable_set.le_iff
- \+ *lemma* first_order.language.definable_set.mem_compl
- \+ *lemma* first_order.language.definable_set.mem_inf
- \+ *lemma* first_order.language.definable_set.mem_sup
- \+ *lemma* first_order.language.definable_set.mem_top
- \+ *lemma* first_order.language.definable_set.not_mem_bot
- \+ *def* first_order.language.definable_set
- \+ *lemma* first_order.language.is_definable.compl
- \+ *lemma* first_order.language.is_definable.inter
- \+ *lemma* first_order.language.is_definable.sdiff
- \+ *lemma* first_order.language.is_definable.union
- \+ *structure* first_order.language.is_definable
- \+ *lemma* first_order.language.is_definable_empty
- \+ *lemma* first_order.language.is_definable_univ

Modified src/model_theory/elementary_maps.lean
- \+ *lemma* first_order.language.realize_bounded_formula_top
- \+ *lemma* first_order.language.realize_term_substructure

Added src/model_theory/quotients.lean
- \+ *lemma* first_order.language.fun_map_quotient_mk
- \+ *lemma* first_order.language.realize_term_quotient_mk

Added src/model_theory/substructures.lean
- \+ *lemma* first_order.language.closed_under.Inf
- \+ *lemma* first_order.language.closed_under.inf
- \+ *lemma* first_order.language.closed_under.inter
- \+ *def* first_order.language.closed_under
- \+ *lemma* first_order.language.closed_under_univ
- \+ *def* first_order.language.hom.eq_locus
- \+ *lemma* first_order.language.hom.eq_of_eq_on_dense
- \+ *lemma* first_order.language.hom.eq_of_eq_on_top
- \+ *lemma* first_order.language.hom.eq_on_closure
- \+ *lemma* first_order.language.substructure.apply_coe_mem_map
- \+ *lemma* first_order.language.substructure.closed
- \+ *def* first_order.language.substructure.closure
- \+ *lemma* first_order.language.substructure.closure_Union
- \+ *lemma* first_order.language.substructure.closure_empty
- \+ *lemma* first_order.language.substructure.closure_eq
- \+ *lemma* first_order.language.substructure.closure_eq_of_le
- \+ *lemma* first_order.language.substructure.closure_induction'
- \+ *lemma* first_order.language.substructure.closure_induction
- \+ *lemma* first_order.language.substructure.closure_le
- \+ *lemma* first_order.language.substructure.closure_mono
- \+ *lemma* first_order.language.substructure.closure_union
- \+ *lemma* first_order.language.substructure.closure_univ
- \+ *lemma* first_order.language.substructure.coe_Inf
- \+ *lemma* first_order.language.substructure.coe_copy
- \+ *lemma* first_order.language.substructure.coe_inf
- \+ *lemma* first_order.language.substructure.coe_infi
- \+ *theorem* first_order.language.substructure.coe_subtype
- \+ *lemma* first_order.language.substructure.coe_top
- \+ *lemma* first_order.language.substructure.coe_top_equiv
- \+ *def* first_order.language.substructure.comap
- \+ *lemma* first_order.language.substructure.comap_comap
- \+ *lemma* first_order.language.substructure.comap_id
- \+ *lemma* first_order.language.substructure.comap_inf
- \+ *lemma* first_order.language.substructure.comap_inf_map_of_injective
- \+ *lemma* first_order.language.substructure.comap_infi
- \+ *lemma* first_order.language.substructure.comap_infi_map_of_injective
- \+ *lemma* first_order.language.substructure.comap_injective_of_surjective
- \+ *lemma* first_order.language.substructure.comap_le_comap_iff_of_surjective
- \+ *lemma* first_order.language.substructure.comap_map_comap
- \+ *lemma* first_order.language.substructure.comap_map_eq_of_injective
- \+ *lemma* first_order.language.substructure.comap_strict_mono_of_surjective
- \+ *lemma* first_order.language.substructure.comap_sup_map_of_injective
- \+ *lemma* first_order.language.substructure.comap_supr_map_of_injective
- \+ *lemma* first_order.language.substructure.comap_surjective_of_injective
- \+ *lemma* first_order.language.substructure.comap_top
- \+ *lemma* first_order.language.substructure.const_mem
- \+ *lemma* first_order.language.substructure.copy_eq
- \+ *lemma* first_order.language.substructure.dense_induction
- \+ *theorem* first_order.language.substructure.ext
- \+ *lemma* first_order.language.substructure.gc_map_comap
- \+ *def* first_order.language.substructure.gci_map_comap
- \+ *def* first_order.language.substructure.gi_map_comap
- \+ *lemma* first_order.language.substructure.le_comap_map
- \+ *lemma* first_order.language.substructure.le_comap_of_map_le
- \+ *def* first_order.language.substructure.map
- \+ *lemma* first_order.language.substructure.map_bot
- \+ *lemma* first_order.language.substructure.map_comap_eq_of_surjective
- \+ *lemma* first_order.language.substructure.map_comap_le
- \+ *lemma* first_order.language.substructure.map_comap_map
- \+ *lemma* first_order.language.substructure.map_id
- \+ *lemma* first_order.language.substructure.map_inf_comap_of_surjective
- \+ *lemma* first_order.language.substructure.map_infi_comap_of_surjective
- \+ *lemma* first_order.language.substructure.map_injective_of_injective
- \+ *lemma* first_order.language.substructure.map_le_iff_le_comap
- \+ *lemma* first_order.language.substructure.map_le_map_iff_of_injective
- \+ *lemma* first_order.language.substructure.map_le_of_le_comap
- \+ *lemma* first_order.language.substructure.map_map
- \+ *lemma* first_order.language.substructure.map_strict_mono_of_injective
- \+ *lemma* first_order.language.substructure.map_sup
- \+ *lemma* first_order.language.substructure.map_sup_comap_of_surjective
- \+ *lemma* first_order.language.substructure.map_supr
- \+ *lemma* first_order.language.substructure.map_supr_comap_of_surjective
- \+ *lemma* first_order.language.substructure.map_surjective_of_surjective
- \+ *lemma* first_order.language.substructure.mem_Inf
- \+ *lemma* first_order.language.substructure.mem_carrier
- \+ *lemma* first_order.language.substructure.mem_closure
- \+ *lemma* first_order.language.substructure.mem_comap
- \+ *lemma* first_order.language.substructure.mem_inf
- \+ *lemma* first_order.language.substructure.mem_infi
- \+ *lemma* first_order.language.substructure.mem_map
- \+ *lemma* first_order.language.substructure.mem_map_of_mem
- \+ *lemma* first_order.language.substructure.mem_top
- \+ *lemma* first_order.language.substructure.monotone_comap
- \+ *lemma* first_order.language.substructure.monotone_map
- \+ *lemma* first_order.language.substructure.not_mem_of_not_mem_closure
- \+ *def* first_order.language.substructure.simps.coe
- \+ *lemma* first_order.language.substructure.subset_closure
- \+ *def* first_order.language.substructure.subtype
- \+ *def* first_order.language.substructure.top_equiv
- \+ *structure* first_order.language.substructure

Added src/model_theory/terms_and_formulas.lean
- \+ *def* first_order.language.bd_not
- \+ *def* first_order.language.bounded_formula.relabel
- \+ *inductive* first_order.language.bounded_formula
- \+ *lemma* first_order.language.embedding.realize_term
- \+ *lemma* first_order.language.equiv.realize_bounded_formula
- \+ *lemma* first_order.language.equiv.realize_term
- \+ *def* first_order.language.formula.equal
- \+ *def* first_order.language.formula.graph
- \+ *def* first_order.language.formula
- \+ *lemma* first_order.language.hom.realize_term
- \+ *def* first_order.language.realize_bounded_formula
- \+ *lemma* first_order.language.realize_bounded_formula_relabel
- \+ *lemma* first_order.language.realize_equal
- \+ *def* first_order.language.realize_formula
- \+ *lemma* first_order.language.realize_formula_equiv
- \+ *lemma* first_order.language.realize_formula_relabel
- \+ *lemma* first_order.language.realize_graph
- \+ *lemma* first_order.language.realize_not
- \+ *def* first_order.language.realize_sentence
- \+ *def* first_order.language.realize_term
- \+ *lemma* first_order.language.realize_term_relabel
- \+ *def* first_order.language.sentence
- \+ *def* first_order.language.term.relabel
- \+ *inductive* first_order.language.term
- \+ *def* first_order.language.theory



## [2022-02-07 10:17:41](https://github.com/leanprover-community/mathlib/commit/3c70566)
feat(analysis/normed_space/linear_isometry): `symm_trans` ([#11892](https://github.com/leanprover-community/mathlib/pull/11892))
Add a `simp` lemma `linear_isometry_equiv.symm_trans`, like
`coe_symm_trans` but without a coercion involved.  `coe_symm_trans`
can then be proved by `simp`, so stops being a `simp` lemma itself.
#### Estimated changes
Modified src/analysis/normed_space/linear_isometry.lean
- \+/\- *lemma* linear_isometry_equiv.coe_symm_trans
- \+ *lemma* linear_isometry_equiv.symm_trans



## [2022-02-07 08:33:33](https://github.com/leanprover-community/mathlib/commit/b1b09eb)
refactor(data/quot): Make more `setoid` arguments implicit ([#11824](https://github.com/leanprover-community/mathlib/pull/11824))
Currently, not all of the `quotient` API can be used with non-instance setoids. This fixes it by making a few `setoid` arguments explicit rather than instances.
#### Estimated changes
Modified src/data/quot.lean
- \+/\- *lemma* quotient.out_equiv_out
- \+/\- *lemma* quotient.out_inj

Modified src/group_theory/schur_zassenhaus.lean




## [2022-02-07 03:57:45](https://github.com/leanprover-community/mathlib/commit/25297ec)
feat(analysis/complex/basic): `conj_lie_symm` ([#11890](https://github.com/leanprover-community/mathlib/pull/11890))
Add a `simp` lemma that the inverse of `conj_lie` is `conj_lie`.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+ *lemma* complex.conj_lie_symm



## [2022-02-06 19:03:43](https://github.com/leanprover-community/mathlib/commit/e18972b)
feat(set_theory/ordinal_arithmetic): Suprema of empty families ([#11872](https://github.com/leanprover-community/mathlib/pull/11872))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \- *lemma* ordinal.blsub_eq_zero
- \+ *lemma* ordinal.blsub_zero
- \+ *theorem* ordinal.bsup_zero
- \+ *lemma* ordinal.lsub_empty
- \- *lemma* ordinal.lsub_eq_zero
- \+ *theorem* ordinal.sup_empty



## [2022-02-06 07:25:14](https://github.com/leanprover-community/mathlib/commit/24ebc5c)
feat(group_theory/sylow): the cardinality of a sylow group ([#11776](https://github.com/leanprover-community/mathlib/pull/11776))
#### Estimated changes
Modified src/algebra/is_prime_pow.lean


Modified src/data/nat/factorization.lean
- \+ *lemma* nat.prime.pow_dvd_iff_dvd_pow_factorization
- \+ *lemma* nat.prime.pow_dvd_iff_le_factorization
- \- *lemma* nat.prime_pow_dvd_iff_le_factorization

Modified src/group_theory/sylow.lean
- \+ *lemma* sylow.card_eq_multiplicity



## [2022-02-06 01:53:58](https://github.com/leanprover-community/mathlib/commit/4148990)
feat(set_theory/ordinal_arithmetic): Suprema and least strict upper bounds of constant families ([#11862](https://github.com/leanprover-community/mathlib/pull/11862))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.blsub_const
- \+ *theorem* ordinal.bsup_const
- \+ *theorem* ordinal.lsub_const
- \+ *theorem* ordinal.sup_const



## [2022-02-05 21:22:39](https://github.com/leanprover-community/mathlib/commit/6787a8d)
feat(category_theory): a hierarchy of balanced categories ([#11856](https://github.com/leanprover-community/mathlib/pull/11856))
#### Estimated changes
Modified src/algebra/category/Group/abelian.lean


Modified src/algebra/category/Module/abelian.lean


Modified src/category_theory/abelian/basic.lean
- \- *lemma* category_theory.abelian.is_iso_of_mono_of_epi
- \- *lemma* category_theory.abelian.strong_epi_of_epi
- \- *lemma* category_theory.abelian.strong_mono_of_mono

Modified src/category_theory/abelian/non_preadditive.lean
- \- *lemma* category_theory.non_preadditive_abelian.is_iso_of_mono_of_epi
- \- *lemma* category_theory.non_preadditive_abelian.strong_epi_of_epi

Modified src/category_theory/abelian/opposite.lean


Added src/category_theory/balanced.lean
- \+ *lemma* category_theory.is_iso_iff_mono_and_epi
- \+ *lemma* category_theory.is_iso_of_mono_of_epi

Modified src/category_theory/epi_mono.lean
- \+ *def* category_theory.split_epi_of_epi
- \+ *def* category_theory.split_mono_of_mono

Modified src/category_theory/limits/shapes/normal_mono.lean
- \+ *def* category_theory.normal_epi_of_epi
- \+ *def* category_theory.normal_mono_of_mono

Modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *def* category_theory.regular_epi_of_epi
- \+ *def* category_theory.regular_mono_of_mono

Modified src/category_theory/limits/shapes/strong_epi.lean
- \+ *lemma* category_theory.strong_epi_of_epi
- \+ *lemma* category_theory.strong_mono_of_mono

Modified src/category_theory/simple.lean


Modified src/category_theory/types.lean
- \+ *lemma* category_theory.injective_of_mono
- \+ *lemma* category_theory.surjective_of_epi



## [2022-02-05 19:40:29](https://github.com/leanprover-community/mathlib/commit/0f9c153)
feat(algebra/cubic_discriminant): basics of cubic polynomials and their discriminants ([#11483](https://github.com/leanprover-community/mathlib/pull/11483))
#### Estimated changes
Added src/algebra/cubic_discriminant.lean
- \+ *lemma* cubic.a_of_eq
- \+ *theorem* cubic.b_eq_three_roots
- \+ *lemma* cubic.b_of_eq
- \+ *theorem* cubic.c_eq_three_roots
- \+ *lemma* cubic.c_of_eq
- \+ *theorem* cubic.card_roots_le
- \+ *theorem* cubic.card_roots_of_disc_ne_zero
- \+ *lemma* cubic.coeff_gt_three
- \+ *lemma* cubic.coeff_one
- \+ *lemma* cubic.coeff_three
- \+ *lemma* cubic.coeff_two
- \+ *lemma* cubic.coeff_zero
- \+ *theorem* cubic.d_eq_three_roots
- \+ *lemma* cubic.d_of_eq
- \+ *lemma* cubic.degree
- \+ *lemma* cubic.degree_of_a_b_c_eq_zero
- \+ *lemma* cubic.degree_of_a_b_eq_zero
- \+ *lemma* cubic.degree_of_a_eq_zero
- \+ *lemma* cubic.degree_of_zero
- \+ *def* cubic.disc
- \+ *theorem* cubic.disc_eq_prod_three_roots
- \+ *theorem* cubic.disc_ne_zero_iff_roots_ne
- \+ *theorem* cubic.disc_ne_zero_iff_roots_nodup
- \+ *theorem* cubic.eq_prod_three_roots
- \+ *theorem* cubic.eq_sum_three_roots
- \+ *lemma* cubic.eq_zero_iff
- \+ *def* cubic.equiv
- \+ *lemma* cubic.leading_coeff
- \+ *lemma* cubic.leading_coeff_of_a_b_c_eq_zero
- \+ *lemma* cubic.leading_coeff_of_a_b_eq_zero
- \+ *lemma* cubic.leading_coeff_of_a_eq_zero
- \+ *def* cubic.map
- \+ *lemma* cubic.map_roots
- \+ *lemma* cubic.map_to_poly
- \+ *theorem* cubic.mem_roots_iff
- \+ *lemma* cubic.ne_zero
- \+ *lemma* cubic.ne_zero_of_a_ne_zero
- \+ *lemma* cubic.ne_zero_of_b_ne_zero
- \+ *lemma* cubic.ne_zero_of_c_ne_zero
- \+ *lemma* cubic.ne_zero_of_d_ne_zero
- \+ *lemma* cubic.of_a_b_c_eq_zero
- \+ *lemma* cubic.of_a_b_eq_zero
- \+ *lemma* cubic.of_a_eq_zero
- \+ *lemma* cubic.of_zero
- \+ *def* cubic.roots
- \+ *theorem* cubic.splits_iff_card_roots
- \+ *theorem* cubic.splits_iff_roots_eq_three
- \+ *def* cubic.to_poly
- \+ *lemma* cubic.to_poly_injective
- \+ *lemma* cubic.zero
- \+ *structure* cubic

Modified src/data/polynomial/coeff.lean
- \+/\- *lemma* polynomial.coeff_C_mul_X
- \+ *lemma* polynomial.coeff_C_mul_X_pow

Modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* polynomial.degree_C_lt
- \+ *lemma* polynomial.degree_C_lt_degree_C_mul_X
- \+ *lemma* polynomial.degree_C_mul_X
- \+ *lemma* polynomial.degree_add_le_of_degree_le
- \+ *lemma* polynomial.degree_cubic
- \+ *lemma* polynomial.degree_cubic_le
- \+ *lemma* polynomial.degree_cubic_lt
- \+ *lemma* polynomial.degree_linear
- \+ *lemma* polynomial.degree_linear_le
- \+ *lemma* polynomial.degree_linear_lt
- \+ *lemma* polynomial.degree_linear_lt_degree_C_mul_X_sq
- \+ *lemma* polynomial.degree_quadratic
- \+ *lemma* polynomial.degree_quadratic_le
- \+ *lemma* polynomial.degree_quadratic_lt
- \+ *lemma* polynomial.degree_quadratic_lt_degree_C_mul_X_cb
- \+ *lemma* polynomial.leading_coeff_C_mul_X
- \- *lemma* polynomial.leading_coeff_C_mul_X_add_C
- \+ *lemma* polynomial.leading_coeff_cubic
- \+ *lemma* polynomial.leading_coeff_linear
- \+ *lemma* polynomial.leading_coeff_quadratic
- \+ *lemma* polynomial.nat_degree_add_le_of_degree_le
- \+ *lemma* polynomial.nat_degree_cubic
- \+ *lemma* polynomial.nat_degree_cubic_le
- \+ *lemma* polynomial.nat_degree_linear
- \+ *lemma* polynomial.nat_degree_linear_le
- \+ *lemma* polynomial.nat_degree_quadratic
- \+ *lemma* polynomial.nat_degree_quadratic_le

Modified src/data/polynomial/eval.lean


Modified src/ring_theory/polynomial/vieta.lean


Modified src/ring_theory/power_series/basic.lean
- \- *lemma* power_series.coeff_C_mul_X
- \+ *lemma* power_series.coeff_C_mul_X_pow



## [2022-02-05 17:59:51](https://github.com/leanprover-community/mathlib/commit/39b1262)
feat(algebra/lie/nilpotent): nilpotency of Lie modules depends only on the Lie subalgebra of linear endomorphisms ([#11853](https://github.com/leanprover-community/mathlib/pull/11853))
#### Estimated changes
Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_algebra.is_nilpotent_range_ad_iff
- \+ *lemma* lie_hom.is_nilpotent_range
- \+ *lemma* lie_module.coe_lcs_range_to_endomorphism_eq
- \+ *lemma* lie_module.is_nilpotent_range_to_endomorphism_iff



## [2022-02-05 17:59:49](https://github.com/leanprover-community/mathlib/commit/b9d19ed)
feat(algebra/lie/nilpotent): nilpotency of Lie modules is preserved under surjective morphisms ([#11852](https://github.com/leanprover-community/mathlib/pull/11852))
#### Estimated changes
Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* equiv.lie_module_is_nilpotent_iff
- \+ *lemma* function.surjective.lie_module_is_nilpotent
- \+ *lemma* function.surjective.lie_module_lcs_map_eq
- \+ *lemma* lie_module.is_nilpotent_of_top_iff



## [2022-02-05 17:59:47](https://github.com/leanprover-community/mathlib/commit/9fcd1f2)
feat(algebra/lie/nilpotent): add lemma `lie_module.coe_lower_central_series_ideal_le` ([#11851](https://github.com/leanprover-community/mathlib/pull/11851))
#### Estimated changes
Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_module.coe_lower_central_series_ideal_le



## [2022-02-05 17:31:04](https://github.com/leanprover-community/mathlib/commit/df7c217)
feat(algebra/lie/nilpotent): add definition `lie_ideal.lcs` ([#11854](https://github.com/leanprover-community/mathlib/pull/11854))
This is extremely useful when proving a generalised version of Engel's lemma.
#### Estimated changes
Modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_ideal.coe_lcs_eq
- \+ *def* lie_ideal.lcs
- \+ *lemma* lie_ideal.lcs_succ
- \+ *lemma* lie_ideal.lcs_top
- \+ *lemma* lie_ideal.lcs_zero



## [2022-02-05 09:52:03](https://github.com/leanprover-community/mathlib/commit/9969321)
feat(measure_theory/probability_mass_function): Lemmas connecting `pmf.support` and `pmf.to_measure` ([#11842](https://github.com/leanprover-community/mathlib/pull/11842))
Add lemmas relating the support of a `pmf` to the measures of sets under the induced measure.
#### Estimated changes
Modified src/measure_theory/probability_mass_function/basic.lean
- \+/\- *lemma* pmf.to_measure_apply'
- \+/\- *lemma* pmf.to_measure_apply
- \+ *lemma* pmf.to_measure_apply_eq_of_inter_support_eq
- \+ *lemma* pmf.to_measure_apply_eq_one_iff
- \+/\- *lemma* pmf.to_measure_apply_eq_to_outer_measure_apply
- \+/\- *lemma* pmf.to_measure_apply_finset
- \+/\- *lemma* pmf.to_measure_apply_fintype
- \+ *lemma* pmf.to_measure_apply_inter_support
- \+/\- *lemma* pmf.to_measure_apply_of_finite
- \+ *lemma* pmf.to_measure_mono
- \+/\- *lemma* pmf.to_outer_measure_apply'
- \+/\- *lemma* pmf.to_outer_measure_apply
- \+ *lemma* pmf.to_outer_measure_apply_eq_of_inter_support_eq
- \+ *lemma* pmf.to_outer_measure_apply_eq_one_iff
- \+/\- *lemma* pmf.to_outer_measure_apply_eq_zero_iff
- \+/\- *lemma* pmf.to_outer_measure_apply_finset
- \+/\- *lemma* pmf.to_outer_measure_apply_fintype
- \+ *lemma* pmf.to_outer_measure_apply_inter_support
- \+/\- *lemma* pmf.to_outer_measure_apply_le_to_measure_apply
- \+ *lemma* pmf.to_outer_measure_mono



## [2022-02-05 09:52:01](https://github.com/leanprover-community/mathlib/commit/612ca40)
feat(data/finset): erase is empty iff ([#11838](https://github.com/leanprover-community/mathlib/pull/11838))
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.erase_eq_empty_iff



## [2022-02-05 09:52:00](https://github.com/leanprover-community/mathlib/commit/31f5688)
refactor(ring_theory/valuation/basic): `fun_like` design for `valuation` ([#11830](https://github.com/leanprover-community/mathlib/pull/11830))
Introduce `valuation_class`, the companion typeclass to `valuation`. Deprecate lemmas. Rename the field from `map_add'` to `map_add_le_max'` to avoid confusion with the eponymous field from `add_hom`.
#### Estimated changes
Modified src/ring_theory/perfection.lean


Modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* valuation.coe_coe
- \+/\- *lemma* valuation.ext
- \+/\- *lemma* valuation.ext_iff
- \+/\- *lemma* valuation.map_add
- \+ *lemma* valuation.to_fun_eq_coe

Modified src/topology/algebra/valued_field.lean




## [2022-02-05 09:51:59](https://github.com/leanprover-community/mathlib/commit/e78563c)
feat(ring_theory/power_series): reindex trunc of a power series to truncate below index n ([#10891](https://github.com/leanprover-community/mathlib/pull/10891))
Currently the definition of truncation of a univariate and multivariate power series truncates above the index, that is if we truncate a power series $\sum a_i x^i$ at index `n` the term $a_n x^n$ is included.
This makes it impossible to truncate the first monomial $x^0$ away as it is included with the smallest possible value of n, which causes some issues in applications (imagine if you could only pop elements of lists if the result was non-empty!).
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* mv_power_series.trunc_C
- \+/\- *lemma* mv_power_series.trunc_one
- \+/\- *lemma* power_series.trunc_C
- \+/\- *lemma* power_series.trunc_one



## [2022-02-05 08:16:33](https://github.com/leanprover-community/mathlib/commit/6b4e269)
chore(data/fintype/basic): rename some instances ([#11845](https://github.com/leanprover-community/mathlib/pull/11845))
Rename instances from `infinite.multiset.infinite` etc to
`multiset.infinite` etc; rename `infinite.set.infinite` to
`infinite.set` to avoid name clash.
Also add `option.infinite`.
#### Estimated changes
Modified src/data/fintype/basic.lean




## [2022-02-05 05:19:33](https://github.com/leanprover-community/mathlib/commit/b0d9761)
feat(ring_theory/hahn_series): add a map to power series and dickson's lemma ([#11836](https://github.com/leanprover-community/mathlib/pull/11836))
Add a ring equivalence between `hahn_series` and `mv_power_series` as discussed in https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/induction.20on.20an.20index.20type/near/269463528.
This required adding some partially well ordered lemmas that it seems go under the name Dickson's lemma.
This may be independently useful, a constructive version of this has been used in other provers, especially in connection to Grobner basis and commutative algebra type material.
#### Estimated changes
Added src/data/finsupp/pwo.lean
- \+ *lemma* finsupp.is_pwo

Modified src/order/well_founded_set.lean
- \+ *lemma* pi.is_pwo
- \+ *theorem* set.is_pwo.mono

Modified src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.coeff_to_mv_power_series
- \+ *lemma* hahn_series.coeff_to_mv_power_series_symm
- \+ *def* hahn_series.to_mv_power_series



## [2022-02-04 23:34:38](https://github.com/leanprover-community/mathlib/commit/bd7d034)
feat(ring_theory/nilpotent): add lemma `module.End.is_nilpotent_mapq` ([#11831](https://github.com/leanprover-community/mathlib/pull/11831))
Together with the other lemmas necessary for its proof.
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.le_comap_pow_of_le_comap

Modified src/linear_algebra/quotient.lean
- \+ *lemma* submodule.mapq_comp
- \+ *lemma* submodule.mapq_id
- \+ *lemma* submodule.mapq_pow
- \+ *lemma* submodule.mapq_zero

Modified src/ring_theory/nilpotent.lean
- \+ *lemma* module.End.is_nilpotent.mapq



## [2022-02-04 22:50:46](https://github.com/leanprover-community/mathlib/commit/b905eb6)
fix(group_theory/nilpotent): don’t unnecessarily `open_locale classical` ([#11779](https://github.com/leanprover-community/mathlib/pull/11779))
h/t @pechersky for noticing
#### Estimated changes
Modified src/group_theory/nilpotent.lean




## [2022-02-04 21:12:18](https://github.com/leanprover-community/mathlib/commit/b3b32c8)
feat(algebra/lie/quotient): first isomorphism theorem for morphisms of Lie algebras ([#11826](https://github.com/leanprover-community/mathlib/pull/11826))
#### Estimated changes
Modified src/algebra/lie/quotient.lean




## [2022-02-04 21:12:17](https://github.com/leanprover-community/mathlib/commit/292bf34)
feat(algebra/lie/ideal_operations): add lemma `lie_ideal_oper_eq_linear_span'` ([#11823](https://github.com/leanprover-community/mathlib/pull/11823))
It is useful to have this alternate form in situations where we have a hypothesis like `h : I = J` since we can then rewrite using `h` after applying this lemma.
An (admittedly brief) scan of the existing applications of `lie_ideal_oper_eq_linear_span` indicates that it's worth keeping both forms for convenience but I'm happy to dig deeper into this if requested.
#### Estimated changes
Modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_submodule.lie_ideal_oper_eq_linear_span'



## [2022-02-04 21:12:16](https://github.com/leanprover-community/mathlib/commit/fa20482)
feat(linear_algebra/basic): add minor lemmas, tweak `simp` attributes ([#11822](https://github.com/leanprover-community/mathlib/pull/11822))
#### Estimated changes
Modified src/algebra/module/submodule.lean
- \+/\- *lemma* submodule.coe_subtype
- \+/\- *theorem* submodule.subtype_apply

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* submodule.comap_id
- \+ *lemma* submodule.map_subtype_range_of_le
- \+ *lemma* submodule.map_subtype_span_singleton
- \+/\- *lemma* submodule.span_singleton_le_iff_mem



## [2022-02-04 21:12:15](https://github.com/leanprover-community/mathlib/commit/247504c)
feat(algebra/lie/cartan_subalgebra): add lemma `lie_subalgebra.exists_nested_lie_ideal_of_le_normalizer` ([#11820](https://github.com/leanprover-community/mathlib/pull/11820))
#### Estimated changes
Modified src/algebra/lie/cartan_subalgebra.lean
- \+ *lemma* lie_subalgebra.exists_nested_lie_ideal_of_le_normalizer
- \+/\- *lemma* lie_subalgebra.ideal_in_normalizer



## [2022-02-04 21:12:13](https://github.com/leanprover-community/mathlib/commit/a2fd0bd)
feat(algebra/lie/basic): define pull back of a Lie module along a morphism of Lie algebras. ([#11819](https://github.com/leanprover-community/mathlib/pull/11819))
#### Estimated changes
Modified src/algebra/lie/basic.lean
- \+ *def* lie_module.comp_lie_hom
- \+ *def* lie_ring_module.comp_lie_hom
- \+ *lemma* lie_ring_module.comp_lie_hom_apply



## [2022-02-04 21:12:12](https://github.com/leanprover-community/mathlib/commit/2e7efe9)
refactor(set_theory/ordinal_arithmetic): Change `α → Prop` to `set α` ([#11816](https://github.com/leanprover-community/mathlib/pull/11816))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* ordinal.is_normal.le_set'
- \+/\- *theorem* ordinal.is_normal.le_set
- \+/\- *theorem* ordinal.is_normal.sup



## [2022-02-04 21:12:11](https://github.com/leanprover-community/mathlib/commit/a741585)
chore(algebra/group): make `coe_norm_subgroup` and `submodule.norm_coe` consistent ([#11427](https://github.com/leanprover-community/mathlib/pull/11427))
The `simp` lemmas for norms in a subgroup and in a submodule disagreed: the first inserted a coercion to the larger group, the second deleted the coercion. Currently this is not a big deal, but it will become a real issue when defining `add_subgroup_class`. I want to make them consistent by pointing them in the same direction. The consensus in the [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Simp.20normal.20form.3A.20coe_norm_subgroup.2C.20submodule.2Enorm_coe) suggests `simp` should insert a coercion here, so I went with that.
After making the changes, a few places need extra `simp [submodule.coe_norm]` on the local hypotheses, but nothing major.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* add_subgroup.coe_norm
- \+ *lemma* add_subgroup.norm_coe
- \- *lemma* coe_norm_subgroup
- \+ *lemma* submodule.coe_norm
- \+/\- *lemma* submodule.norm_coe
- \- *lemma* submodule.norm_mk

Modified src/geometry/manifold/instances/sphere.lean


Modified src/measure_theory/function/simple_func_dense.lean




## [2022-02-04 20:39:46](https://github.com/leanprover-community/mathlib/commit/c3273aa)
feat(algebra/lie/subalgebra): add `lie_subalgebra.equiv_of_le` and `lie_subalgebra.equiv_range_of_injective` ([#11828](https://github.com/leanprover-community/mathlib/pull/11828))
#### Estimated changes
Modified src/algebra/lie/basic.lean


Modified src/algebra/lie/subalgebra.lean
- \+ *lemma* lie_hom.equiv_range_of_injective_apply
- \+ *lemma* lie_subalgebra.coe_of_le
- \+ *lemma* lie_subalgebra.equiv_of_le_apply



## [2022-02-04 18:53:26](https://github.com/leanprover-community/mathlib/commit/3c00e5d)
fix(algebra/Module/colimits): Change `comm_ring` to `ring`. ([#11837](https://github.com/leanprover-community/mathlib/pull/11837))
... despite the well-known fact that all rings are commutative.
#### Estimated changes
Modified src/algebra/category/Module/colimits.lean




## [2022-02-04 18:53:25](https://github.com/leanprover-community/mathlib/commit/5b3cd4a)
refactor(analysis/normed_space/add_torsor): Kill `seminormed_add_torsor` ([#11795](https://github.com/leanprover-community/mathlib/pull/11795))
Delete `normed_add_torsor` in favor of the equivalent `seminormed_add_torsor` and rename `seminormed_add_torsor` to `normed_add_torsor`.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean
- \+/\- *lemma* dist_eq_norm_vsub

Modified src/analysis/normed_space/affine_isometry.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/geometry/euclidean/basic.lean




## [2022-02-04 18:53:24](https://github.com/leanprover-community/mathlib/commit/aaaeeae)
feat(category_theory/category/{Pointed,Bipointed}): The categories of pointed/bipointed types ([#11777](https://github.com/leanprover-community/mathlib/pull/11777))
Define
* `Pointed`, the category of pointed types
* `Bipointed`, the category of bipointed types
* the forgetful functors from `Bipointed` to `Pointed` and from `Pointed` to `Type*`
* `Type_to_Pointed`, the functor from `Type*` to `Pointed` induced by `option`
* `Bipointed.swap_equiv` the equivalence between `Bipointed` and itself induced by `prod.swap` both ways.
#### Estimated changes
Added src/category_theory/category/Bipointed.lean
- \+ *def* Bipointed.hom.comp
- \+ *def* Bipointed.hom.id
- \+ *def* Bipointed.of
- \+ *def* Bipointed.swap
- \+ *def* Bipointed.swap_equiv
- \+ *lemma* Bipointed.swap_equiv_symm
- \+ *structure* Bipointed
- \+ *def* Bipointed_to_Pointed_fst
- \+ *lemma* Bipointed_to_Pointed_fst_comp_forget
- \+ *def* Bipointed_to_Pointed_snd
- \+ *lemma* Bipointed_to_Pointed_snd_comp_forget
- \+ *def* Pointed_to_Bipointed_fst
- \+ *def* Pointed_to_Bipointed_fst_Bipointed_to_Pointed_fst_adjunction
- \+ *lemma* Pointed_to_Bipointed_fst_comp
- \+ *def* Pointed_to_Bipointed_snd
- \+ *def* Pointed_to_Bipointed_snd_Bipointed_to_Pointed_snd_adjunction
- \+ *lemma* Pointed_to_Bipointed_snd_comp
- \+ *lemma* swap_comp_Bipointed_to_Pointed_fst
- \+ *lemma* swap_comp_Bipointed_to_Pointed_snd

Added src/category_theory/category/Pointed.lean
- \+ *def* Pointed.hom.comp
- \+ *def* Pointed.hom.id
- \+ *def* Pointed.of
- \+ *structure* Pointed
- \+ *def* Type_to_Pointed
- \+ *def* Type_to_Pointed_forget_adjunction



## [2022-02-04 17:10:26](https://github.com/leanprover-community/mathlib/commit/cedcf07)
chore(*): update to lean 3.39.0c ([#11821](https://github.com/leanprover-community/mathlib/pull/11821))
#### Estimated changes
Modified leanpkg.toml


Modified src/tactic/rewrite.lean
- \+ *def* tactic.id_tag.assoc_proof



## [2022-02-04 08:58:31](https://github.com/leanprover-community/mathlib/commit/049a1b2)
feat(group_theory/subgroup/basic): add pi subgroups ([#11801](https://github.com/leanprover-community/mathlib/pull/11801))
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.coe_pi
- \+ *lemma* subgroup.mem_pi
- \+ *def* subgroup.pi
- \+ *lemma* subgroup.pi_bot
- \+ *lemma* subgroup.pi_empty
- \+ *lemma* subgroup.pi_top
- \+ *def* submonoid.pi



## [2022-02-04 06:54:32](https://github.com/leanprover-community/mathlib/commit/46c48d7)
feat(logic/basic): add projection notation for iff ([#11803](https://github.com/leanprover-community/mathlib/pull/11803))
#### Estimated changes
Modified src/data/set/basic.lean


Modified src/logic/basic.lean
- \+/\- *theorem* and_congr_left'
- \+/\- *theorem* and_congr_right'
- \+ *lemma* iff.and
- \+ *lemma* iff.iff
- \+ *lemma* iff.imp
- \+ *lemma* iff.not
- \+ *lemma* iff.or
- \+/\- *theorem* or_congr_left
- \+/\- *theorem* or_congr_right

Modified src/tactic/lint/misc.lean




## [2022-02-04 02:33:18](https://github.com/leanprover-community/mathlib/commit/553cb9c)
fix(algebra/category/Module/colimits): Add some additional instances with permuted universe parameters ([#11812](https://github.com/leanprover-community/mathlib/pull/11812))
#### Estimated changes
Modified src/algebra/category/Module/colimits.lean




## [2022-02-04 02:33:17](https://github.com/leanprover-community/mathlib/commit/4cfc30e)
chore(*): use le_rfl instead of le_refl _ ([#11797](https://github.com/leanprover-community/mathlib/pull/11797))
#### Estimated changes
Modified src/algebra/algebra/operations.lean


Modified src/algebra/algebra/subalgebra.lean


Modified src/algebra/big_operators/order.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/indicator_function.lean


Modified src/algebra/lie/nilpotent.lean


Modified src/algebra/lie/submodule.lean


Modified src/algebra/order/archimedean.lean


Modified src/algebra/order/monoid.lean


Modified src/algebra/order/pi.lean


Modified src/algebra/order/ring.lean


Modified src/algebra/order/with_zero.lean


Modified src/algebra/tropical/basic.lean


Modified src/algebraic_topology/simplex_category.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/fderiv_measurable.lean


Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/calculus/inverse.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/inner_product_space/projection.lean


Modified src/analysis/normed/group/SemiNormedGroup/kernels.lean


Modified src/analysis/normed/group/basic.lean


Modified src/analysis/normed/group/infinite_sum.lean


Modified src/analysis/normed/group/quotient.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/enorm.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/special_functions/bernstein.lean


Modified src/analysis/specific_limits.lean


Modified src/category_theory/sites/closed.lean


Modified src/category_theory/sites/grothendieck.lean


Modified src/category_theory/sites/pretopology.lean


Modified src/category_theory/subobject/basic.lean


Modified src/combinatorics/composition.lean


Modified src/computability/language.lean


Modified src/computability/partrec_code.lean


Modified src/computability/turing_machine.lean


Modified src/control/lawful_fix.lean


Modified src/data/W/basic.lean


Modified src/data/W/cardinal.lean


Modified src/data/analysis/filter.lean


Modified src/data/buffer/parser/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/finset/lattice.lean


Modified src/data/fintype/basic.lean


Modified src/data/int/basic.lean


Modified src/data/list/min_max.lean


Modified src/data/list/rotate.lean


Modified src/data/multiset/finset_ops.lean


Modified src/data/multiset/lattice.lean


Modified src/data/mv_polynomial/cardinal.lean


Modified src/data/mv_polynomial/variables.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/cast.lean


Modified src/data/nat/choose/basic.lean


Modified src/data/nat/enat.lean


Modified src/data/nat/factorial/basic.lean


Modified src/data/nat/lattice.lean


Modified src/data/nat/pow.lean


Modified src/data/nat/prime.lean


Modified src/data/ordmap/ordnode.lean


Modified src/data/ordmap/ordset.lean


Modified src/data/polynomial/degree/definitions.lean


Modified src/data/polynomial/degree/trailing_degree.lean


Modified src/data/polynomial/eval.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/polynomial/inductions.lean


Modified src/data/polynomial/reverse.lean


Modified src/data/rbtree/basic.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/ereal.lean


Modified src/data/real/pi/bounds.lean


Modified src/data/real/pi/wallis.lean


Modified src/data/real/sqrt.lean


Modified src/data/set/intervals/disjoint.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/galois.lean


Modified src/field_theory/is_alg_closed/basic.lean


Modified src/field_theory/splitting_field.lean


Modified src/geometry/manifold/instances/real.lean


Modified src/geometry/manifold/times_cont_mdiff.lean


Modified src/group_theory/perm/support.lean


Modified src/group_theory/specific_groups/alternating.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/linear_algebra/adic_completion.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/dimension.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/isomorphisms.lean


Modified src/linear_algebra/linear_independent.lean


Modified src/linear_algebra/quotient.lean


Modified src/linear_algebra/std_basis.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/decomposition/unsigned_hahn.lean


Modified src/measure_theory/function/l1_space.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/integral/integrable_on.lean


Modified src/measure_theory/integral/integral_eq_improper.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/integral/vitali_caratheodory.lean


Modified src/measure_theory/measurable_space_def.lean


Modified src/measure_theory/measure/giry_monad.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/measure_theory/measure/outer_measure.lean


Modified src/measure_theory/measure/stieltjes.lean


Modified src/measure_theory/measure/vector_measure.lean


Modified src/measure_theory/pi_system.lean


Modified src/number_theory/class_number/finite.lean


Modified src/number_theory/padics/hensel.lean


Modified src/number_theory/padics/padic_numbers.lean


Modified src/number_theory/primorial.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/order/atoms.lean


Modified src/order/bounded_order.lean


Modified src/order/closure.lean


Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/at_top_bot.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/extr.lean


Modified src/order/filter/indicator_function.lean


Modified src/order/filter/lift.lean


Modified src/order/filter/ultrafilter.lean


Modified src/order/galois_connection.lean


Modified src/order/lattice.lean


Modified src/order/liminf_limsup.lean


Modified src/order/modular_lattice.lean


Modified src/order/monotone.lean


Modified src/order/omega_complete_partial_order.lean


Modified src/order/partial_sups.lean


Modified src/order/pilex.lean


Modified src/order/well_founded_set.lean


Modified src/order/zorn.lean


Modified src/probability_theory/stopping.lean


Modified src/ring_theory/artinian.lean


Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/ideal/operations.lean


Modified src/ring_theory/int/basic.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/nakayama.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/bernstein.lean


Modified src/ring_theory/power_series/basic.lean


Modified src/ring_theory/unique_factorization_domain.lean


Modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* add_valuation.supp_quot_supp
- \+/\- *lemma* valuation.supp_quot_supp

Modified src/set_theory/cardinal.lean


Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/ordinal_arithmetic.lean


Modified src/testing/slim_check/sampleable.lean


Modified src/topology/algebra/floor_ring.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered/intermediate_value.lean


Modified src/topology/algebra/ordered/monotone_convergence.lean


Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/continuous_function/bounded.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/list.lean


Modified src/topology/local_extr.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/contracting.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/lipschitz.lean


Modified src/topology/order.lean


Modified src/topology/path_connected.lean


Modified src/topology/semicontinuous.lean


Modified src/topology/separation.lean


Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean


Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean


Modified src/topology/stone_cech.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/separation.lean


Modified src/topology/vector_bundle.lean


Modified test/apply.lean


Modified test/monotonicity.lean




## [2022-02-04 02:03:42](https://github.com/leanprover-community/mathlib/commit/6dcad02)
feat(linear_algebra/lagrange): Add recurrence formula for Lagrange polynomials ([#11762](https://github.com/leanprover-community/mathlib/pull/11762))
I have also changed `interpolate` to take in a function `f : F → F` instead of `f : s → F`, since this makes the statement of the theorem nicer.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/linear_algebra/lagrange.lean
- \+ *theorem* lagrange.basis_singleton_self
- \+ *theorem* lagrange.degree_interpolate_erase
- \+ *theorem* lagrange.eq_interpolate_of_eval_eq
- \+/\- *theorem* lagrange.eval_interpolate
- \+ *theorem* lagrange.interpolate_eq_interpolate_erase_add
- \+ *theorem* lagrange.interpolate_eq_of_eval_eq
- \+ *theorem* lagrange.interpolate_singleton
- \+/\- *def* lagrange.linterpolate



## [2022-02-03 23:36:11](https://github.com/leanprover-community/mathlib/commit/853192c)
feat(topology/algebra): Inf and inducing preserve compatibility with algebraic structure ([#11720](https://github.com/leanprover-community/mathlib/pull/11720))
This partly duplicates @mariainesdff 's work on group topologies, but I'm using an unbundled approach which avoids defining a new `X_topology` structure for each interesting X.
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* topological_group_Inf
- \+ *lemma* topological_group_induced
- \+ *lemma* topological_group_inf
- \+ *lemma* topological_group_infi

Modified src/topology/algebra/module/basic.lean
- \+ *lemma* has_continuous_smul_induced

Modified src/topology/algebra/monoid.lean
- \+ *lemma* has_continuous_mul_Inf
- \+ *lemma* has_continuous_mul_induced
- \+ *lemma* has_continuous_mul_inf
- \+ *lemma* has_continuous_mul_infi

Modified src/topology/algebra/mul_action.lean
- \+ *lemma* has_continuous_smul_Inf
- \+ *lemma* has_continuous_smul_inf
- \+ *lemma* has_continuous_smul_infi



## [2022-02-03 18:39:52](https://github.com/leanprover-community/mathlib/commit/30a731c)
fix(algebra/category/Module/colimits): generalize universes ([#11802](https://github.com/leanprover-community/mathlib/pull/11802))
#### Estimated changes
Modified src/algebra/category/Module/colimits.lean
- \+/\- *lemma* Module.colimits.cocone_naturality_components
- \+/\- *def* Module.colimits.colimit_type



## [2022-02-03 18:39:51](https://github.com/leanprover-community/mathlib/commit/f2be0d2)
feat(polynomial/cyclotomic): irreducible cyclotomic polynomials are minimal polynomials ([#11796](https://github.com/leanprover-community/mathlib/pull/11796))
from flt-regular
#### Estimated changes
Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* is_primitive_root.minpoly_dvd_cyclotomic
- \+ *lemma* is_primitive_root.minpoly_eq_cyclotomic_of_irreducible
- \- *lemma* minpoly_dvd_cyclotomic



## [2022-02-03 16:59:03](https://github.com/leanprover-community/mathlib/commit/2c5f36c)
feat(data/finset/sort): an order embedding from fin ([#11800](https://github.com/leanprover-community/mathlib/pull/11800))
Given a set `s` of at least `k` element in a linear order, there is an order embedding from `fin k` whose image is contained in `s`.
#### Estimated changes
Modified src/data/finset/sort.lean
- \+ *def* finset.order_emb_of_card_le
- \+ *lemma* finset.order_emb_of_card_le_mem



## [2022-02-03 16:59:01](https://github.com/leanprover-community/mathlib/commit/25f0406)
fix(topology/connected): typos in docstrings ([#11798](https://github.com/leanprover-community/mathlib/pull/11798))
As pointed out by @YaelDillies
#### Estimated changes
Modified src/topology/connected.lean




## [2022-02-03 15:03:19](https://github.com/leanprover-community/mathlib/commit/a4d9581)
feat(algebra/group_power/order): add pow_bit0_pos_iff ([#11785](https://github.com/leanprover-community/mathlib/pull/11785))
#### Estimated changes
Modified src/algebra/group_power/order.lean
- \+ *theorem* pow_bit0_pos_iff
- \+ *theorem* sq_pos_iff



## [2022-02-03 14:17:31](https://github.com/leanprover-community/mathlib/commit/324d845)
feat(field_theory/krull_topology): defined Krull topology on Galois groups ([#11780](https://github.com/leanprover-community/mathlib/pull/11780))
#### Estimated changes
Added src/field_theory/krull_topology.lean
- \+ *lemma* finite_dimensional_sup
- \+ *def* finite_exts
- \+ *def* fixed_by_finite
- \+ *def* gal_basis
- \+ *def* gal_group_basis
- \+ *lemma* intermediate_field.finite_dimensional_bot
- \+ *lemma* intermediate_field.fixing_subgroup.antimono
- \+ *lemma* intermediate_field.fixing_subgroup.bot
- \+ *lemma* intermediate_field.map_id
- \+ *lemma* intermediate_field.map_mono
- \+ *lemma* mem_fixing_subgroup_iff
- \+ *lemma* mem_gal_basis_iff
- \+ *lemma* top_fixed_by_finite



## [2022-02-03 12:53:15](https://github.com/leanprover-community/mathlib/commit/d6e1c55)
chore(data/polynomial/monic): dedup `degree_map` ([#11792](https://github.com/leanprover-community/mathlib/pull/11792))
#### Estimated changes
Modified src/data/polynomial/monic.lean
- \- *lemma* polynomial.degree_map'
- \- *lemma* polynomial.nat_degree_map'
- \+ *lemma* polynomial.nat_degree_map_eq_of_injective

Modified src/field_theory/splitting_field.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/polynomial/gauss_lemma.lean




## [2022-02-03 12:53:14](https://github.com/leanprover-community/mathlib/commit/2f4f8ad)
feat(set_theory/principal): Principal ordinals are unbounded ([#11755](https://github.com/leanprover-community/mathlib/pull/11755))
Amazingly, this theorem requires no conditions on the operation.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.is_normal.lt_nfp
- \+ *theorem* ordinal.lt_nfp

Modified src/set_theory/principal.lean
- \+ *def* ordinal.blsub₂
- \+ *theorem* ordinal.lt_blsub₂
- \+ *theorem* ordinal.principal_nfp_blsub₂
- \+ *theorem* ordinal.unbounded_principal



## [2022-02-03 12:12:38](https://github.com/leanprover-community/mathlib/commit/50ee3d5)
feat(ring_theory/roots_of_unity): coe_injective ([#11793](https://github.com/leanprover-community/mathlib/pull/11793))
from flt-regular
#### Estimated changes
Modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* roots_of_unity.coe_injective



## [2022-02-03 11:20:19](https://github.com/leanprover-community/mathlib/commit/934f182)
feat(field_theory/is_alg_closed/classification): Classify algebraically closed fields ([#9370](https://github.com/leanprover-community/mathlib/pull/9370))
The main results here are that two algebraically closed fields with the same characteristic and the same cardinality of transcendence basis are isomorphic. The consequence of this is that two uncountable algebraically closed fields of the same cardinality and characteristic are isomorphic. This has applications in model theory, in particular the Lefschetz principle https://proofwiki.org/wiki/Lefschetz_Principle_(First-Order)
#### Estimated changes
Added src/field_theory/is_alg_closed/classification.lean
- \+ *lemma* algebra.is_algebraic.cardinal_mk_le_max
- \+ *lemma* algebra.is_algebraic.cardinal_mk_le_sigma_polynomial
- \+ *lemma* is_alg_closed.cardinal_eq_cardinal_transcendence_basis_of_omega_lt
- \+ *lemma* is_alg_closed.cardinal_le_max_transcendence_basis
- \+ *def* is_alg_closed.equiv_of_transcendence_basis
- \+ *lemma* is_alg_closed.is_alg_closure_of_transcendence_basis
- \+ *lemma* is_alg_closed.ring_equiv_of_cardinal_eq_of_char_eq
- \+ *lemma* is_alg_closed.ring_equiv_of_cardinal_eq_of_char_zero



## [2022-02-03 10:20:39](https://github.com/leanprover-community/mathlib/commit/e39f617)
feat(category_theory/linear): compatibility of linear Yoneda ([#11784](https://github.com/leanprover-community/mathlib/pull/11784))
#### Estimated changes
Modified src/category_theory/linear/yoneda.lean
- \+ *def* category_theory.linear_coyoneda
- \+ *lemma* category_theory.whiskering_linear_coyoneda
- \+ *lemma* category_theory.whiskering_linear_coyoneda₂
- \+ *lemma* category_theory.whiskering_linear_yoneda
- \+ *lemma* category_theory.whiskering_linear_yoneda₂



## [2022-02-03 10:20:38](https://github.com/leanprover-community/mathlib/commit/e61ce5d)
chore(category_theory/limits): dualize strong_epi ([#11783](https://github.com/leanprover-community/mathlib/pull/11783))
#### Estimated changes
Modified src/category_theory/abelian/basic.lean
- \+ *lemma* category_theory.abelian.strong_mono_of_mono

Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/strong_epi.lean
- \+ *lemma* category_theory.is_iso_of_epi_of_strong_mono
- \+ *lemma* category_theory.strong_mono_comp
- \+ *lemma* category_theory.strong_mono_of_strong_mono



## [2022-02-03 10:20:37](https://github.com/leanprover-community/mathlib/commit/93f2bdc)
feat(topology/algebra/ordered/monotone_convergence): add `antitone.{ge,le}_of_tendsto` ([#11754](https://github.com/leanprover-community/mathlib/pull/11754))
#### Estimated changes
Modified src/topology/algebra/ordered/monotone_convergence.lean
- \+ *lemma* antitone.ge_of_tendsto
- \+ *lemma* antitone.le_of_tendsto



## [2022-02-03 09:25:26](https://github.com/leanprover-community/mathlib/commit/a483158)
feat(topology/algebra/group): continuity of action of a group on its own coset space ([#11772](https://github.com/leanprover-community/mathlib/pull/11772))
Given a subgroup `Γ` of a topological group `G`, there is an induced scalar action of `G` on the coset space `G ⧸ Γ`, and there is also an induced topology on `G ⧸ Γ`.  We prove that this action is continuous in each variable, and, if the group `G` is locally compact, also jointly continuous.
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+ *lemma* quotient_group.continuous_smul₁

Modified src/topology/algebra/group_completion.lean


Modified src/topology/compact_open.lean
- \+ *lemma* quotient_map.continuous_lift_prod_left
- \+ *lemma* quotient_map.continuous_lift_prod_right



## [2022-02-03 04:55:55](https://github.com/leanprover-community/mathlib/commit/1816378)
chore(*): golf `by_contra, push_neg` to `by_contra'` ([#11768](https://github.com/leanprover-community/mathlib/pull/11768))
#### Estimated changes
Modified archive/imo/imo1972_b2.lean


Modified archive/imo/imo2008_q4.lean


Modified archive/imo/imo2013_q5.lean


Modified counterexamples/phillips.lean


Modified src/algebra/big_operators/finprod.lean


Modified src/algebraic_topology/simplex_category.lean


Modified src/analysis/convex/extrema.lean


Modified src/analysis/specific_limits.lean


Modified src/combinatorics/composition.lean


Modified src/data/fintype/basic.lean


Modified src/data/nat/nth.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/covering/besicovitch_vector_space.lean


Modified src/measure_theory/decomposition/signed_hahn.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/measure/hausdorff.lean


Modified src/measure_theory/measure/measure_space_def.lean


Modified src/number_theory/class_number/finite.lean


Modified src/order/extension.lean


Modified src/order/well_founded.lean


Modified src/ring_theory/polynomial/content.lean


Modified src/ring_theory/witt_vector/domain.lean


Modified src/topology/algebra/ordered/liminf_limsup.lean


Modified src/topology/metric_space/emetric_paracompact.lean




## [2022-02-03 04:21:08](https://github.com/leanprover-community/mathlib/commit/89a3c07)
feat(field_theory/laurent): Laurent expansions of rational functions ([#11199](https://github.com/leanprover-community/mathlib/pull/11199))
Also provide more API for `ratfunc`, lifting homomorphisms of (polynomial to polynomial) to (ratfunc to ratfunc).
#### Estimated changes
Added src/field_theory/laurent.lean
- \+ *def* ratfunc.laurent
- \+ *lemma* ratfunc.laurent_C
- \+ *lemma* ratfunc.laurent_X
- \+ *lemma* ratfunc.laurent_algebra_map
- \+ *lemma* ratfunc.laurent_at_zero
- \+ *def* ratfunc.laurent_aux
- \+ *lemma* ratfunc.laurent_aux_algebra_map
- \+ *lemma* ratfunc.laurent_aux_div
- \+ *lemma* ratfunc.laurent_aux_of_fraction_ring_mk
- \+ *lemma* ratfunc.laurent_div
- \+ *lemma* ratfunc.laurent_injective
- \+ *lemma* ratfunc.laurent_laurent
- \+ *lemma* ratfunc.taylor_mem_non_zero_divisors

Modified src/field_theory/ratfunc.lean
- \+ *lemma* ratfunc.coe_map_alg_hom_eq_coe_map
- \+ *lemma* ratfunc.coe_map_ring_hom_eq_coe_map
- \+/\- *lemma* ratfunc.div_smul
- \+/\- *lemma* ratfunc.lift_alg_hom_injective
- \+/\- *def* ratfunc.lift_monoid_with_zero_hom
- \+/\- *lemma* ratfunc.lift_monoid_with_zero_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* ratfunc.lift_monoid_with_zero_hom_injective
- \+/\- *def* ratfunc.lift_ring_hom
- \+/\- *lemma* ratfunc.lift_ring_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* ratfunc.lift_ring_hom_injective
- \+ *def* ratfunc.map
- \+ *def* ratfunc.map_alg_hom
- \+ *lemma* ratfunc.map_apply
- \+ *lemma* ratfunc.map_apply_div
- \+ *lemma* ratfunc.map_apply_div_ne_zero
- \+ *lemma* ratfunc.map_apply_of_fraction_ring_mk
- \+ *lemma* ratfunc.map_injective
- \+ *def* ratfunc.map_ring_hom

Modified src/ring_theory/hahn_series.lean
- \+ *lemma* hahn_series.single_eq_zero_iff



## [2022-02-02 21:05:56](https://github.com/leanprover-community/mathlib/commit/7f3590b)
feat(field_theory/minpoly): add a nontriviality lemma ([#11781](https://github.com/leanprover-community/mathlib/pull/11781))
#### Estimated changes
Modified src/field_theory/minpoly.lean
- \+ *lemma* minpoly.subsingleton



## [2022-02-02 20:04:39](https://github.com/leanprover-community/mathlib/commit/cdad110)
feat(tactic/equiv_rw): enhancing 'equiv_rw' ([#11730](https://github.com/leanprover-community/mathlib/pull/11730))
Expands the `equiv_rw` API by:
* Making it accept a list of equivalences instead of a single one, if intended
* Allowing multiple targets (closes [#2891](https://github.com/leanprover-community/mathlib/pull/2891))
Extra: some optimizations.
#### Estimated changes
Modified src/ring_theory/witt_vector/truncated.lean


Modified src/tactic/equiv_rw.lean


Modified src/topology/continuous_function/compact.lean


Modified test/equiv_rw.lean




## [2022-02-02 16:48:16](https://github.com/leanprover-community/mathlib/commit/41811cd)
feat(number_theory): von Mangoldt function ([#11727](https://github.com/leanprover-community/mathlib/pull/11727))
Defines the von Mangoldt function
#### Estimated changes
Modified src/algebra/is_prime_pow.lean
- \+ *lemma* is_prime_pow_pow_iff
- \+ *lemma* nat.coprime.is_prime_pow_dvd_mul
- \+ *lemma* nat.disjoint_divisors_filter_prime_pow
- \+ *lemma* nat.mul_divisors_filter_prime_pow

Modified src/number_theory/divisors.lean
- \+ *lemma* nat.prod_divisors_antidiagonal'
- \+ *lemma* nat.prod_divisors_antidiagonal

Added src/number_theory/von_mangoldt.lean
- \+ *lemma* nat.arithmetic_function.log_apply
- \+ *lemma* nat.arithmetic_function.log_mul_moebius_eq_von_mangoldt
- \+ *lemma* nat.arithmetic_function.moebius_mul_log_eq_von_mangoldt
- \+ *lemma* nat.arithmetic_function.sum_moebius_mul_log_eq
- \+ *lemma* nat.arithmetic_function.von_mangoldt_apply
- \+ *lemma* nat.arithmetic_function.von_mangoldt_apply_one
- \+ *lemma* nat.arithmetic_function.von_mangoldt_apply_pow
- \+ *lemma* nat.arithmetic_function.von_mangoldt_apply_prime
- \+ *lemma* nat.arithmetic_function.von_mangoldt_mul_zeta
- \+ *lemma* nat.arithmetic_function.von_mangoldt_nonneg
- \+ *lemma* nat.arithmetic_function.von_mangoldt_sum
- \+ *lemma* nat.arithmetic_function.zeta_mul_von_mangoldt



## [2022-02-02 16:48:15](https://github.com/leanprover-community/mathlib/commit/c235c61)
refactor(set_theory/ordinal_arithmetic): Simpler `bsup` definition ([#11386](https://github.com/leanprover-community/mathlib/pull/11386))
We also simplify some existing proofs.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *def* ordinal.bsup
- \+ *theorem* ordinal.comp_bfamily_of_family'
- \+ *theorem* ordinal.comp_bfamily_of_family
- \+ *theorem* ordinal.comp_family_of_bfamily'
- \+ *theorem* ordinal.comp_family_of_bfamily
- \+/\- *theorem* ordinal.lsub_eq_lsub
- \+/\- *theorem* ordinal.sup_eq_sup



## [2022-02-02 16:48:14](https://github.com/leanprover-community/mathlib/commit/4d0b398)
feat(topology/connected): Connectedness of unions of sets ([#10005](https://github.com/leanprover-community/mathlib/pull/10005))
* Add multiple results about when unions of sets are (pre)connected. In particular, the union of connected sets indexed by `ℕ` such that each set intersects the next is connected.
* Remove some `set.` prefixes in the file
* There are two minor fixes in other files, presumably caused by the fact that they now import `order.succ_pred`
* Co-authored by Floris van Doorn fpvdoorn@gmail.com
#### Estimated changes
Modified src/analysis/calculus/specific_functions.lean


Modified src/data/real/cardinality.lean


Modified src/data/set/lattice.lean
- \+ *lemma* set.nonempty_bUnion

Modified src/topology/connected.lean
- \+ *theorem* is_connected.Union_of_chain
- \+ *theorem* is_connected.Union_of_refl_trans_gen
- \+ *theorem* is_connected.bUnion_of_chain
- \+ *theorem* is_connected.bUnion_of_refl_trans_gen
- \+/\- *theorem* is_connected.subset_closure
- \+ *theorem* is_preconnected.Union_of_chain
- \+ *theorem* is_preconnected.Union_of_refl_trans_gen
- \+ *theorem* is_preconnected.bUnion_of_chain
- \+ *theorem* is_preconnected.bUnion_of_refl_trans_gen
- \+ *theorem* is_preconnected.sUnion_directed
- \+ *theorem* is_preconnected.union'



## [2022-02-02 14:51:44](https://github.com/leanprover-community/mathlib/commit/d6c002c)
feat(group_theory/p_group): finite p-groups with different p have coprime orders ([#11775](https://github.com/leanprover-community/mathlib/pull/11775))
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.coprime_card_of_ne



## [2022-02-02 14:51:43](https://github.com/leanprover-community/mathlib/commit/307a456)
refactor(set_theory/ordinal): Add `covariant_class` instances for ordinal addition and multiplication ([#11678](https://github.com/leanprover-community/mathlib/pull/11678))
This replaces the old `add_le_add_left`, `add_le_add_right`, `mul_le_mul_left`, `mul_le_mul_right` theorems.
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean


Modified src/set_theory/ordinal.lean
- \- *theorem* ordinal.add_le_add_left
- \- *theorem* ordinal.add_le_add_right

Modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* ordinal.add_le_add_iff_left
- \- *theorem* ordinal.add_lt_add_iff_left
- \- *theorem* ordinal.mul_le_mul
- \- *theorem* ordinal.mul_le_mul_left
- \- *theorem* ordinal.mul_le_mul_right

Modified src/set_theory/ordinal_notation.lean




## [2022-02-02 14:51:42](https://github.com/leanprover-community/mathlib/commit/cd1d839)
feat(order/rel_classes): Unbundled typeclass to state that two relations are the non strict and strict versions ([#11381](https://github.com/leanprover-community/mathlib/pull/11381))
This defines a Prop-valued mixin `is_nonstrict_strict_order α r s` to state `s a b ↔ r a b ∧ ¬ r b a`.
The idea is to allow dot notation for lemmas about the interaction of `⊆` and `⊂` (which currently do not have a `preorder`-like typeclass). Dot notation on each of them is already possible thanks to unbundled relation classes (which allow to state lemmas for both `set` and `finset`).
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.ssubset_def
- \+ *lemma* finset.subset_def
- \- *theorem* finset.subset_def
- \- *theorem* finset.subset_of_eq

Modified src/data/set/basic.lean
- \- *lemma* has_ssubset.ssubset.asymm
- \- *lemma* has_ssubset.ssubset.trans
- \- *lemma* has_subset.subset.antisymm
- \- *lemma* has_subset.subset.trans
- \- *theorem* set.eq_or_ssubset_of_subset
- \+ *lemma* set.ssubset_def
- \- *theorem* set.ssubset_def
- \- *lemma* set.ssubset_iff_subset_ne
- \- *lemma* set.ssubset_of_ssubset_of_subset
- \- *lemma* set.ssubset_of_subset_of_ssubset
- \+ *lemma* set.subset_def
- \- *theorem* set.subset_def

Modified src/order/rel_classes.lean
- \+ *lemma* antisymm'
- \+ *lemma* antisymm_of'
- \+ *lemma* eq_or_ssubset_of_subset
- \+ *lemma* ne_of_irrefl'
- \+/\- *lemma* ne_of_irrefl
- \+ *lemma* ne_of_not_subset
- \+ *lemma* ne_of_not_superset
- \+ *lemma* ne_of_ssubset
- \+ *lemma* ne_of_ssuperset
- \+ *lemma* not_ssubset_of_subset
- \+ *lemma* not_subset_of_ssubset
- \+ *lemma* right_iff_left_not_left
- \+ *lemma* right_iff_left_not_left_of
- \+ *lemma* ssubset_asymm
- \+ *lemma* ssubset_iff_subset_ne
- \+ *lemma* ssubset_iff_subset_not_subset
- \+ *lemma* ssubset_irrefl
- \+ *lemma* ssubset_irrfl
- \+ *lemma* ssubset_of_ne_of_subset
- \+ *lemma* ssubset_of_ssubset_of_subset
- \+ *lemma* ssubset_of_subset_not_subset
- \+ *lemma* ssubset_of_subset_of_ne
- \+ *lemma* ssubset_of_subset_of_ssubset
- \+ *lemma* ssubset_or_eq_of_subset
- \+ *lemma* ssubset_trans
- \+ *lemma* subset_antisymm
- \+ *lemma* subset_antisymm_iff
- \+ *lemma* subset_iff_ssubset_or_eq
- \+ *lemma* subset_of_eq
- \+ *lemma* subset_of_ssubset
- \+ *lemma* subset_refl
- \+ *lemma* subset_rfl
- \+ *lemma* subset_trans
- \+ *lemma* superset_antisymm
- \+ *lemma* superset_antisymm_iff
- \+ *lemma* superset_of_eq



## [2022-02-02 13:59:38](https://github.com/leanprover-community/mathlib/commit/d002769)
refactor(ring_theory): clean up `algebraic_iff_integral` ([#11773](https://github.com/leanprover-community/mathlib/pull/11773))
The definitions `is_algebraic_iff_integral`, `is_algebraic_iff_integral'` and `algebra.is_algebraic_of_finite` have always been annoying me, so I decided to fix that:
 * The name `is_algebraic_iff_integral'` doesn't explain how it differs from `is_algebraic_iff_integral` (namely that the whole algebra is algebraic, rather than one element), so I renamed it to `algebra.is_algebraic_iff_integral`.
 * The two `is_algebraic_iff_integral` lemmas have an unnecessarily explicit parameter `K`, so I made that implicit
 * `is_algebraic_of_finite` has no explicit parameters (so we always have to use type ascriptions), so I made them explicit
 * Half of the usages of `is_algebraic_of_finite` are of the form `is_algebraic_iff_integral.mp is_algebraic_of_finite`, even though `is_algebraic_of_finite` is proved as `is_algebraic_iff_integral.mpr (some_proof_that_it_is_integral)`, so I split it up into a part showing it is integral, that we can use directly.
As a result, I was able to golf a few proofs.
#### Estimated changes
Modified src/field_theory/abel_ruffini.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/is_alg_closed/algebraic_closure.lean


Modified src/field_theory/is_alg_closed/basic.lean


Modified src/field_theory/polynomial_galois_group.lean


Modified src/field_theory/separable.lean


Modified src/field_theory/splitting_field.lean


Modified src/number_theory/class_number/finite.lean


Modified src/number_theory/number_field.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebraic.lean
- \+ *lemma* algebra.is_integral_of_finite
- \- *lemma* is_algebraic_iff_is_integral'

Modified src/ring_theory/dedekind_domain.lean


Modified src/ring_theory/localization.lean




## [2022-02-02 13:59:37](https://github.com/leanprover-community/mathlib/commit/07d6d17)
refactor(field_theory/is_alg_closed/basic): Generalize alg closures to commutative rings ([#11703](https://github.com/leanprover-community/mathlib/pull/11703))
#### Estimated changes
Modified src/field_theory/is_alg_closed/basic.lean
- \+/\- *lemma* is_alg_closure.equiv_of_equiv_algebra_map
- \+/\- *lemma* is_alg_closure.equiv_of_equiv_comp_algebra_map
- \+/\- *lemma* is_alg_closure.equiv_of_equiv_symm_algebra_map
- \+/\- *lemma* is_alg_closure.equiv_of_equiv_symm_comp_algebra_map

Modified src/ring_theory/localization.lean




## [2022-02-02 12:30:43](https://github.com/leanprover-community/mathlib/commit/4db1f96)
chore(algebra/ne_zero): revert transitivity changes ([#11760](https://github.com/leanprover-community/mathlib/pull/11760))
The `trans` methods were a disaster for `flt-regular` - this reverts them unless a better solution can be found.
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean


Modified src/number_theory/cyclotomic/zeta.lean
- \+/\- *lemma* is_cyclotomic_extension.zeta_primitive_root



## [2022-02-02 12:30:42](https://github.com/leanprover-community/mathlib/commit/6c6fbe6)
feat(group_theory/subgroup/basic): normalizer condition implies max subgroups normal ([#11597](https://github.com/leanprover-community/mathlib/pull/11597))
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.normalizer_condition.normal_of_coatom



## [2022-02-02 10:56:10](https://github.com/leanprover-community/mathlib/commit/1ed19a9)
feat(group_theory/nilpotent): p-groups are nilpotent ([#11726](https://github.com/leanprover-community/mathlib/pull/11726))
#### Estimated changes
Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.induction_subsingleton_or_nontrivial

Modified src/group_theory/nilpotent.lean
- \+ *lemma* is_p_group.is_nilpotent
- \+ *lemma* of_quotient_center_nilpotent



## [2022-02-02 10:56:09](https://github.com/leanprover-community/mathlib/commit/c1d2860)
feat(measure_theory/probability_mass_function): Measures of sets under `pmf` monad operations ([#11613](https://github.com/leanprover-community/mathlib/pull/11613))
This PR adds explicit formulas for the measures of sets under `pmf.pure`, `pmf.bind`, and `pmf.bind_on_support`.
#### Estimated changes
Modified src/measure_theory/probability_mass_function/monad.lean
- \+/\- *lemma* pmf.bind_bind
- \+/\- *lemma* pmf.bind_pure
- \+/\- *lemma* pmf.coe_bind_apply
- \+/\- *lemma* pmf.pure_bind
- \+ *lemma* pmf.to_measure_bind_apply
- \+ *lemma* pmf.to_measure_bind_on_support_apply
- \+ *lemma* pmf.to_measure_pure_apply
- \+ *lemma* pmf.to_outer_measure_bind_apply
- \+ *lemma* pmf.to_outer_measure_bind_on_support_apply
- \+ *lemma* pmf.to_outer_measure_pure_apply



## [2022-02-02 10:56:08](https://github.com/leanprover-community/mathlib/commit/a687cbf)
feat(field_theory/intermediate_field, ring_theory/.., algebra/algebra… ([#11168](https://github.com/leanprover-community/mathlib/pull/11168))
If `E` is an subsemiring/subring/subalgebra/intermediate_field and e is an equivalence of the larger semiring/ring/algebra/field, then e induces an equivalence from E to E.map e. We define this equivalence.
#### Estimated changes
Modified src/algebra/algebra/subalgebra.lean
- \+ *def* alg_equiv.subalgebra_map

Modified src/field_theory/intermediate_field.lean
- \+ *def* intermediate_field.intermediate_field_map

Modified src/ring_theory/subring/basic.lean
- \+ *def* ring_equiv.subring_map

Modified src/ring_theory/subsemiring/basic.lean
- \+ *def* ring_equiv.subsemiring_map



## [2022-02-02 08:53:09](https://github.com/leanprover-community/mathlib/commit/d5d5784)
chore(ring_theory/power_basis): add `simps` ([#11766](https://github.com/leanprover-community/mathlib/pull/11766))
for flt-regular
#### Estimated changes
Modified src/ring_theory/power_basis.lean




## [2022-02-02 08:53:07](https://github.com/leanprover-community/mathlib/commit/2fdc151)
refactor(power_series/basic): generalize order to semirings ([#11765](https://github.com/leanprover-community/mathlib/pull/11765))
There are still some TODOs about generalizing statements downstream of this file.
#### Estimated changes
Modified src/data/finset/nat_antidiagonal.lean
- \+ *lemma* finset.nat.filter_fst_eq_antidiagonal
- \+ *lemma* finset.nat.filter_snd_eq_antidiagonal

Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* power_series.X_pow_order_dvd
- \+/\- *lemma* power_series.coeff_of_lt_order
- \+/\- *lemma* power_series.coeff_order
- \+ *lemma* power_series.exists_coeff_ne_zero_iff_ne_zero
- \+/\- *def* power_series.order
- \+ *lemma* power_series.order_eq_multiplicity_X
- \+ *lemma* power_series.order_finite_iff_ne_zero
- \- *lemma* power_series.order_finite_of_coeff_ne_zero
- \+/\- *lemma* power_series.order_le
- \+/\- *lemma* power_series.order_zero



## [2022-02-02 08:53:06](https://github.com/leanprover-community/mathlib/commit/a32b0d3)
feat(group_theory/p_group): p-groups with different p are disjoint ([#11752](https://github.com/leanprover-community/mathlib/pull/11752))
#### Estimated changes
Modified src/group_theory/p_group.lean
- \+ *lemma* is_p_group.disjoint_of_ne



## [2022-02-02 08:53:04](https://github.com/leanprover-community/mathlib/commit/664b5be)
feat(group_theory/subgroup/basic): add commute_of_normal_of_disjoint ([#11751](https://github.com/leanprover-community/mathlib/pull/11751))
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.commute_of_normal_of_disjoint



## [2022-02-02 08:53:03](https://github.com/leanprover-community/mathlib/commit/a6d70aa)
feat(order/category/*): `order_dual` as an equivalence of categories ([#11743](https://github.com/leanprover-community/mathlib/pull/11743))
For `whatever` a category of orders, define
* `whatever.iso_of_order_iso`: Turns an order isomorphism into an equivalence of objects inside `whatever`
* `whatever.to_dual`: `order_dual` as a functor from `whatever` to itself
* `whatever.dual_equiv`: The equivalence of categories between `whatever` and itself induced by `order_dual` both ways
* `order_iso.dual_dual`: The order isomorphism between `α` and `order_dual (order_dual α)`
#### Estimated changes
Modified src/data/fin/basic.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_lex
- \+ *lemma* fintype.card_order_dual

Modified src/order/category/LinearOrder.lean
- \+ *def* LinearOrder.dual_equiv
- \+ *def* LinearOrder.iso.mk
- \+ *def* LinearOrder.to_dual
- \+ *lemma* LinearOrder_dual_equiv_comp_forget_to_PartialOrder

Modified src/order/category/NonemptyFinLinOrd.lean
- \+ *def* NonemptyFinLinOrd.dual_equiv
- \+ *def* NonemptyFinLinOrd.iso.mk
- \+ *def* NonemptyFinLinOrd.to_dual
- \+ *lemma* NonemptyFinLinOrd_dual_equiv_comp_forget_to_LinearOrder

Modified src/order/category/PartialOrder.lean
- \+ *def* PartialOrder.dual_equiv
- \+ *def* PartialOrder.iso.mk
- \+ *def* PartialOrder.to_dual
- \+ *lemma* PartialOrder_dual_equiv_comp_forget_to_Preorder

Modified src/order/category/Preorder.lean
- \+ *def* Preorder.dual_equiv
- \+ *def* Preorder.iso.mk
- \+ *def* Preorder.to_dual

Modified src/order/hom/basic.lean
- \+ *lemma* order_iso.coe_dual_dual
- \+ *lemma* order_iso.coe_dual_dual_symm
- \+ *def* order_iso.dual_dual
- \+ *lemma* order_iso.dual_dual_apply
- \+ *lemma* order_iso.dual_dual_symm_apply



## [2022-02-02 07:21:06](https://github.com/leanprover-community/mathlib/commit/400dbb3)
refactor(ring_theory/non_zero_divisors): use fun_like ([#11764](https://github.com/leanprover-community/mathlib/pull/11764))
#### Estimated changes
Modified src/field_theory/ratfunc.lean


Modified src/number_theory/cyclotomic/basic.lean


Modified src/ring_theory/jacobson.lean


Modified src/ring_theory/laurent_series.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/non_zero_divisors.lean
- \+ *lemma* map_le_non_zero_divisors_of_injective
- \+ *lemma* map_mem_non_zero_divisors
- \+ *lemma* map_ne_zero_of_mem_non_zero_divisors
- \+ *lemma* mem_non_zero_divisors_of_ne_zero
- \- *lemma* monoid_with_zero_hom.map_le_non_zero_divisors_of_injective
- \- *lemma* monoid_with_zero_hom.map_mem_non_zero_divisors
- \- *lemma* monoid_with_zero_hom.map_ne_zero_of_mem_non_zero_divisors
- \+ *lemma* non_zero_divisors_le_comap_non_zero_divisors_of_injective
- \- *lemma* ring_hom.map_le_non_zero_divisors_of_injective
- \- *lemma* ring_hom.map_mem_non_zero_divisors
- \- *lemma* ring_hom.map_ne_zero_of_mem_non_zero_divisors

Modified src/ring_theory/polynomial/scale_roots.lean




## [2022-02-02 07:21:05](https://github.com/leanprover-community/mathlib/commit/c8fd7e3)
chore(measure_theory/covering/besicovitch): Weaker import ([#11763](https://github.com/leanprover-community/mathlib/pull/11763))
We relax the `set_theory.cardinal_ordinal` import to the weaker `set_theory.ordinal_arithmetic` import. We also fix some trivial spacing issues in the docs.
#### Estimated changes
Modified src/measure_theory/covering/besicovitch.lean




## [2022-02-02 07:21:04](https://github.com/leanprover-community/mathlib/commit/a18680a)
chore(topology/continuous_function/ordered): split from `continuous_function/basic` ([#11761](https://github.com/leanprover-community/mathlib/pull/11761))
Split material about orders out from `continuous_function/basic`, to move that file lower down the import hierarchy.
#### Estimated changes
Modified src/combinatorics/configuration.lean


Modified src/topology/continuous_function/algebra.lean


Modified src/topology/continuous_function/basic.lean
- \- *def* continuous_map.Icc_extend
- \- *def* continuous_map.abs
- \- *lemma* continuous_map.abs_apply
- \- *lemma* continuous_map.coe_Icc_extend
- \- *lemma* continuous_map.inf'_apply
- \- *lemma* continuous_map.inf'_coe
- \- *lemma* continuous_map.inf_apply
- \- *lemma* continuous_map.inf_coe
- \- *lemma* continuous_map.le_def
- \- *lemma* continuous_map.lt_def
- \- *lemma* continuous_map.sup'_apply
- \- *lemma* continuous_map.sup'_coe
- \- *lemma* continuous_map.sup_apply
- \- *lemma* continuous_map.sup_coe

Added src/topology/continuous_function/ordered.lean
- \+ *def* continuous_map.Icc_extend
- \+ *def* continuous_map.abs
- \+ *lemma* continuous_map.abs_apply
- \+ *lemma* continuous_map.coe_Icc_extend
- \+ *lemma* continuous_map.inf'_apply
- \+ *lemma* continuous_map.inf'_coe
- \+ *lemma* continuous_map.inf_apply
- \+ *lemma* continuous_map.inf_coe
- \+ *lemma* continuous_map.le_def
- \+ *lemma* continuous_map.lt_def
- \+ *lemma* continuous_map.sup'_apply
- \+ *lemma* continuous_map.sup'_coe
- \+ *lemma* continuous_map.sup_apply
- \+ *lemma* continuous_map.sup_coe

Modified src/topology/homotopy/basic.lean




## [2022-02-02 07:21:03](https://github.com/leanprover-community/mathlib/commit/366fd9b)
feat(analysis/special_functions): show (2 / π) * x ≤ sin x ([#11724](https://github.com/leanprover-community/mathlib/pull/11724))
I wasn't entirely sure where to put this - trigonometric/basic is too high on the import graph but here seems to work. 
This is a fairly weak inequality but it can sometimes turn out to be useful, and is important enough to be named!
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/complex.lean
- \+ *lemma* real.le_sin_mul
- \+ *lemma* real.lt_sin_mul
- \+ *lemma* real.mul_le_sin
- \+ *lemma* real.mul_lt_sin



## [2022-02-02 07:21:01](https://github.com/leanprover-community/mathlib/commit/5c4c1c0)
feat(topology/homotopy): Fundamental groupoid preserves products ([#11459](https://github.com/leanprover-community/mathlib/pull/11459))
#### Estimated changes
Modified src/category_theory/category/Groupoid.lean
- \+ *lemma* category_theory.Groupoid.hom_to_functor
- \+ *lemma* category_theory.Groupoid.pi_iso_pi_hom_π
- \+ *def* category_theory.Groupoid.pi_limit_cone
- \+ *abbreviation* category_theory.Groupoid.pi_limit_fan

Modified src/category_theory/discrete_category.lean
- \+ *def* category_theory.discrete.comp_nat_iso_discrete

Modified src/category_theory/groupoid.lean


Modified src/category_theory/pi/basic.lean
- \+ *lemma* category_theory.functor.eq_to_hom_proj
- \+ *def* category_theory.functor.pi'
- \+ *lemma* category_theory.functor.pi'_eval
- \+ *lemma* category_theory.functor.pi_ext

Modified src/category_theory/products/basic.lean
- \+ *def* category_theory.functor.prod'

Modified src/topology/homotopy/fundamental_groupoid.lean
- \+/\- *lemma* fundamental_groupoid.comp_eq
- \+ *def* fundamental_groupoid.from_path
- \+ *def* fundamental_groupoid.from_top
- \+ *lemma* fundamental_groupoid.id_eq_path_refl
- \+ *def* fundamental_groupoid.to_path
- \+ *def* fundamental_groupoid.to_top

Modified src/topology/homotopy/product.lean
- \+ *def* fundamental_groupoid_functor.cone_discrete_comp
- \+ *lemma* fundamental_groupoid_functor.cone_discrete_comp_obj_map_cone
- \+ *def* fundamental_groupoid_functor.pi_Top_to_pi_cone
- \+ *def* fundamental_groupoid_functor.pi_iso
- \+ *def* fundamental_groupoid_functor.pi_to_pi_Top
- \+ *def* fundamental_groupoid_functor.preserves_product
- \+ *def* fundamental_groupoid_functor.prod_iso
- \+ *def* fundamental_groupoid_functor.prod_to_prod_Top
- \+ *def* fundamental_groupoid_functor.proj
- \+ *def* fundamental_groupoid_functor.proj_left
- \+ *lemma* fundamental_groupoid_functor.proj_left_map
- \+ *lemma* fundamental_groupoid_functor.proj_map
- \+ *def* fundamental_groupoid_functor.proj_right
- \+ *lemma* fundamental_groupoid_functor.proj_right_map



## [2022-02-02 06:20:40](https://github.com/leanprover-community/mathlib/commit/fa86370)
chore(*): Golfed some random theorems ([#11769](https://github.com/leanprover-community/mathlib/pull/11769))
#### Estimated changes
Modified src/algebraic_geometry/properties.lean


Modified src/category_theory/simple.lean


Modified src/data/nat/log.lean


Modified src/ring_theory/discrete_valuation_ring.lean


Modified src/topology/subset_properties.lean




## [2022-02-02 05:25:14](https://github.com/leanprover-community/mathlib/commit/8ef783b)
feat(measure_theory/measure): drop more `measurable_set` args ([#11547](https://github.com/leanprover-community/mathlib/pull/11547))
Most notably, in `measure_Union_eq_supr`.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* bsupr_measure_Iic

Modified src/measure_theory/decomposition/unsigned_hahn.lean


Modified src/measure_theory/integral/lebesgue.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.ae_eq_of_subset_of_measure_ge
- \+ *lemma* measure_theory.bsupr_measure_Iic
- \+/\- *lemma* measure_theory.measure.ext_iff_of_Union_eq_univ
- \+/\- *lemma* measure_theory.measure.ext_iff_of_sUnion_eq_univ
- \+/\- *lemma* measure_theory.measure.restrict_Union_congr
- \+/\- *lemma* measure_theory.measure.restrict_bUnion_congr
- \+/\- *lemma* measure_theory.measure.restrict_finset_bUnion_congr
- \+/\- *lemma* measure_theory.measure.restrict_sUnion_congr
- \+/\- *lemma* measure_theory.measure.restrict_union_congr
- \+ *lemma* measure_theory.measure_Union_congr_of_subset
- \+/\- *lemma* measure_theory.measure_Union_eq_supr
- \+ *lemma* measure_theory.measure_Union_to_measurable
- \+ *lemma* measure_theory.measure_add_diff
- \+ *lemma* measure_theory.measure_bUnion_to_measurable
- \+ *lemma* measure_theory.measure_diff'
- \+ *lemma* measure_theory.measure_to_measurable_union
- \+ *lemma* measure_theory.measure_union_congr_of_subset
- \+ *lemma* measure_theory.measure_union_to_measurable
- \+/\- *lemma* measure_theory.tendsto_measure_Union

Modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* measure_theory.exists_measurable_superset₂

Modified src/measure_theory/measure/regular.lean
- \+/\- *lemma* measure_theory.measure.inner_regular.is_compact_is_closed
- \+/\- *lemma* measure_theory.measure.inner_regular.of_pseudo_emetric_space

Modified src/topology/metric_space/hausdorff_distance.lean




## [2022-02-02 02:57:46](https://github.com/leanprover-community/mathlib/commit/d68b480)
chore(linear_algebra): remove `bilinear_map` from imports in `pi` ([#11767](https://github.com/leanprover-community/mathlib/pull/11767))
Remove `bilinear_map` from imports in `pi`
#### Estimated changes
Modified src/linear_algebra/pi.lean




## [2022-02-01 20:41:27](https://github.com/leanprover-community/mathlib/commit/343cbd9)
feat(sites/sheaf): simple sheaf condition in terms of limit ([#11692](https://github.com/leanprover-community/mathlib/pull/11692))
+ Given a presheaf on a site, construct a simple cone for each sieve. The sheaf condition is equivalent to all these cones being limit cones for all covering sieves of the Grothendieck topology. This is made possible by a series of work that mostly removed universe restrictions on limits.
+ Given a sieve over X : C, the diagram of its associated cone is a functor from the full subcategory of the over category C/X consisting of the arrows in the sieve, constructed from the canonical cocone over `forget : over X ⥤ C` with cone point X, which is only now added to mathlib. This cone is simpler than the multifork cone in [`is_sheaf_iff_multifork`](https://leanprover-community.github.io/mathlib_docs/category_theory/sites/sheaf.html#category_theory.presheaf.is_sheaf_iff_multifork). The underlying type of this full subcategory is equivalent to [`grothendieck_topology.cover.arrow`](https://leanprover-community.github.io/mathlib_docs/category_theory/sites/grothendieck.html#category_theory.grothendieck_topology.cover.arrow).
+ This limit sheaf condition might be more convenient to use to do sheafification, which has been done by @adamtopaz using the multifork cone before universes are sufficiently generalized for limits, though I haven't thought about it in detail. It may not be worth refactoring sheafification in terms of this sheaf condition, but we might consider using this if we ever want to do sheafification for more general (e.g. non-concrete) value categories. [#11706](https://github.com/leanprover-community/mathlib/pull/11706) is another application.
This is based on a [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/universe.20restriction.20on.20limit/near/260732627) with @adamtopaz.
#### Estimated changes
Modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* category_theory.limits.is_initial_equiv_unique
- \+ *def* category_theory.limits.is_terminal_equiv_unique

Modified src/category_theory/over.lean
- \+ *def* category_theory.over.forget_cocone
- \+ *def* category_theory.under.forget_cone

Modified src/category_theory/sites/sheaf.lean
- \+ *def* category_theory.presheaf.cones_equiv_sieve_compatible_family
- \+ *def* category_theory.presheaf.hom_equiv_amalgamation
- \+ *lemma* category_theory.presheaf.is_limit_iff_is_sheaf_for
- \+ *lemma* category_theory.presheaf.is_limit_iff_is_sheaf_for_presieve
- \+ *lemma* category_theory.presheaf.is_separated_iff_subsingleton
- \+ *lemma* category_theory.presheaf.is_sheaf_iff_is_limit
- \+ *lemma* category_theory.presheaf.is_sheaf_iff_is_limit_pretopology
- \+ *lemma* category_theory.presheaf.subsingleton_iff_is_separated_for
- \+ *def* category_theory.presieve.family_of_elements.sieve_compatible.cone

Modified src/category_theory/sites/sheaf_of_types.lean
- \+/\- *lemma* category_theory.presieve.family_of_elements.compatible.sieve_extend

Modified src/category_theory/sites/sieves.lean
- \+ *abbreviation* category_theory.presieve.cocone
- \+ *abbreviation* category_theory.presieve.diagram

Modified src/category_theory/sites/spaces.lean
- \+ *lemma* opens.pretopology_of_grothendieck

Modified src/logic/unique.lean
- \+ *lemma* unique_iff_exists_unique
- \+ *lemma* unique_subtype_iff_exists_unique



## [2022-02-01 18:24:10](https://github.com/leanprover-community/mathlib/commit/ec61182)
feat(algebra/group_power): relate square equality and absolute value equality ([#11683](https://github.com/leanprover-community/mathlib/pull/11683))
#### Estimated changes
Modified src/algebra/group_power/order.lean
- \+ *lemma* one_le_sq_iff_one_le_abs
- \+ *lemma* one_lt_sq_iff_one_lt_abs
- \+ *lemma* sq_eq_one_iff
- \+ *lemma* sq_eq_sq_iff_abs_eq_abs
- \+ *lemma* sq_le_one_iff_abs_le_one
- \+ *lemma* sq_lt_one_iff_abs_lt_one
- \+/\- *theorem* sq_lt_sq
- \+ *lemma* sq_ne_one_iff

Modified src/analysis/inner_product_space/basic.lean




## [2022-02-01 12:46:25](https://github.com/leanprover-community/mathlib/commit/23e0e29)
chore(*): register global fact instances ([#11749](https://github.com/leanprover-community/mathlib/pull/11749))
We register globally some fact instances which are necessary for integration or euclidean spaces. And also the fact that 2 and 3 are prime. See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/euclidean_space.20error/near/269992165
#### Estimated changes
Modified src/algebra/char_p/two.lean


Modified src/analysis/fourier.lean


Modified src/analysis/inner_product_space/l2_space.lean


Modified src/analysis/inner_product_space/pi_L2.lean


Modified src/analysis/inner_product_space/spectrum.lean


Modified src/analysis/normed_space/pi_Lp.lean
- \- *lemma* fact_one_le_one_real
- \- *lemma* fact_one_le_two_real

Modified src/data/nat/prime.lean
- \- *lemma* nat.fact_prime_three
- \- *lemma* nat.fact_prime_two

Modified src/data/real/ennreal.lean
- \- *lemma* fact_one_le_one_ennreal
- \- *lemma* fact_one_le_top_ennreal
- \- *lemma* fact_one_le_two_ennreal

Modified src/geometry/manifold/instances/real.lean


Modified src/group_theory/order_of_element.lean


Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/function/l2_space.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/function/simple_func_dense.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/measure_theory/integral/set_to_l1.lean


Modified src/number_theory/quadratic_reciprocity.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/kuratowski.lean




## [2022-02-01 11:04:30](https://github.com/leanprover-community/mathlib/commit/2508cbd)
feat(model_theory/basic.lean): Elementary embeddings and elementary substructures ([#11089](https://github.com/leanprover-community/mathlib/pull/11089))
Defines elementary embeddings between structures
Defines when substructures are elementary
Provides lemmas about preservation of realizations of terms and formulas under various maps
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *def* first_order.language.bounded_formula.relabel
- \+ *lemma* first_order.language.embedding.realize_term
- \+ *structure* first_order.language.embedding
- \+ *lemma* first_order.language.equiv.apply_symm_apply
- \+ *lemma* first_order.language.equiv.realize_bounded_formula
- \+ *lemma* first_order.language.equiv.realize_term
- \+ *lemma* first_order.language.equiv.symm_apply_apply
- \+ *structure* first_order.language.equiv
- \+ *def* first_order.language.formula.equal
- \+ *def* first_order.language.formula.graph
- \+ *lemma* first_order.language.hom.realize_term
- \+ *structure* first_order.language.hom
- \+ *lemma* first_order.language.realize_bounded_formula_relabel
- \+ *lemma* first_order.language.realize_bounded_formula_top
- \+ *lemma* first_order.language.realize_equal
- \+ *lemma* first_order.language.realize_formula_equiv
- \+ *lemma* first_order.language.realize_formula_relabel
- \+ *lemma* first_order.language.realize_graph
- \+ *lemma* first_order.language.realize_term_relabel
- \+ *lemma* first_order.language.realize_term_substructure
- \+ *lemma* first_order.language.substructure.coe_top_equiv
- \+ *def* first_order.language.substructure.top_equiv
- \+ *def* first_order.language.term.relabel

Added src/model_theory/elementary_maps.lean
- \+ *lemma* first_order.language.elementary_embedding.coe_injective
- \+ *lemma* first_order.language.elementary_embedding.coe_to_embedding
- \+ *lemma* first_order.language.elementary_embedding.coe_to_hom
- \+ *def* first_order.language.elementary_embedding.comp
- \+ *lemma* first_order.language.elementary_embedding.comp_apply
- \+ *lemma* first_order.language.elementary_embedding.comp_assoc
- \+ *lemma* first_order.language.elementary_embedding.ext
- \+ *lemma* first_order.language.elementary_embedding.ext_iff
- \+ *lemma* first_order.language.elementary_embedding.injective
- \+ *lemma* first_order.language.elementary_embedding.map_const
- \+ *lemma* first_order.language.elementary_embedding.map_formula
- \+ *lemma* first_order.language.elementary_embedding.map_fun
- \+ *lemma* first_order.language.elementary_embedding.map_rel
- \+ *def* first_order.language.elementary_embedding.refl
- \+ *lemma* first_order.language.elementary_embedding.refl_apply
- \+ *def* first_order.language.elementary_embedding.to_embedding
- \+ *lemma* first_order.language.elementary_embedding.to_embedding_to_hom
- \+ *def* first_order.language.elementary_embedding.to_hom
- \+ *structure* first_order.language.elementary_embedding
- \+ *theorem* first_order.language.elementary_substructure.coe_subtype
- \+ *lemma* first_order.language.elementary_substructure.coe_top
- \+ *lemma* first_order.language.elementary_substructure.is_elementary
- \+ *lemma* first_order.language.elementary_substructure.mem_top
- \+ *def* first_order.language.elementary_substructure.subtype
- \+ *structure* first_order.language.elementary_substructure
- \+ *lemma* first_order.language.equiv.coe_to_elementary_embedding
- \+ *def* first_order.language.equiv.to_elementary_embedding
- \+ *lemma* first_order.language.equiv.to_elementary_embedding_to_embedding
- \+ *def* first_order.language.substructure.is_elementary



## [2022-02-01 10:02:45](https://github.com/leanprover-community/mathlib/commit/94a700f)
chore(set_theory/ordinal_arithmetic): Remove redundant explicit argument ([#11757](https://github.com/leanprover-community/mathlib/pull/11757))
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean




## [2022-02-01 10:02:44](https://github.com/leanprover-community/mathlib/commit/ca2a99d)
feat(set_theory/ordinal_arithmetic): Normal functions evaluated at `ω` ([#11687](https://github.com/leanprover-community/mathlib/pull/11687))
#### Estimated changes
Modified src/set_theory/ordinal.lean
- \+ *theorem* ordinal.eq_zero_or_pos

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.is_normal.apply_omega
- \+ *theorem* ordinal.sup_add_nat
- \+ *theorem* ordinal.sup_mul_nat
- \+ *theorem* ordinal.sup_nat_cast
- \+ *theorem* ordinal.sup_opow_nat



## [2022-02-01 09:01:20](https://github.com/leanprover-community/mathlib/commit/cbad62c)
feat(set_theory/{ordinal_arithmetic, cardinal_ordinal}): Ordinals aren't a small type ([#11756](https://github.com/leanprover-community/mathlib/pull/11756))
We substantially golf and extend some results previously in `cardinal_ordinal.lean`.
#### Estimated changes
Modified src/set_theory/cardinal_ordinal.lean
- \- *lemma* not_injective_of_ordinal
- \- *lemma* not_injective_of_ordinal_of_small

Modified src/set_theory/ordinal_arithmetic.lean
- \+ *lemma* not_injective_of_ordinal
- \+ *lemma* not_injective_of_ordinal_of_small
- \+ *theorem* not_small_ordinal
- \+ *lemma* not_surjective_of_ordinal
- \+ *lemma* not_surjective_of_ordinal_of_small
- \+ *theorem* ordinal.lsub_nmem_range



## [2022-02-01 08:32:51](https://github.com/leanprover-community/mathlib/commit/30dcd70)
feat(number_theory/cyclotomic/zeta): add lemmas ([#11753](https://github.com/leanprover-community/mathlib/pull/11753))
Various lemmas about `zeta`.
From flt-regular.
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean
- \+/\- *lemma* is_cyclotomic_extension.finite_dimensional
- \+ *lemma* is_cyclotomic_extension.is_galois

Modified src/number_theory/cyclotomic/zeta.lean
- \+ *lemma* is_cyclotomic_extension.finrank
- \+ *lemma* is_cyclotomic_extension.norm_zeta_eq_one
- \+ *lemma* is_cyclotomic_extension.norm_zeta_sub_one_eq_eval_cyclotomic
- \+/\- *def* is_cyclotomic_extension.zeta.embeddings_equiv_primitive_roots
- \+/\- *lemma* is_cyclotomic_extension.zeta_minpoly
- \+ *lemma* is_cyclotomic_extension.zeta_pow
- \+/\- *lemma* is_cyclotomic_extension.zeta_primitive_root



## [2022-02-01 07:42:44](https://github.com/leanprover-community/mathlib/commit/350ba8d)
feat(data/two_pointing): Two pointings of a type ([#11648](https://github.com/leanprover-community/mathlib/pull/11648))
Define `two_pointing α` as the type of two pointings of `α`. This is a Type-valued structure version of `nontrivial`.
#### Estimated changes
Added src/data/two_pointing.lean
- \+ *lemma* two_pointing.Prop_fst
- \+ *lemma* two_pointing.Prop_snd
- \+ *lemma* two_pointing.bool_fst
- \+ *lemma* two_pointing.bool_snd
- \+ *lemma* two_pointing.nonempty_two_pointing_iff
- \+ *def* two_pointing.pi
- \+ *lemma* two_pointing.pi_fst
- \+ *lemma* two_pointing.pi_snd
- \+ *def* two_pointing.prod
- \+ *lemma* two_pointing.prod_fst
- \+ *lemma* two_pointing.prod_snd
- \+ *lemma* two_pointing.snd_ne_fst
- \+ *lemma* two_pointing.sum_fst
- \+ *lemma* two_pointing.sum_snd
- \+ *def* two_pointing.swap
- \+ *lemma* two_pointing.swap_fst
- \+ *lemma* two_pointing.swap_snd
- \+ *lemma* two_pointing.swap_swap
- \+ *lemma* two_pointing.to_nontrivial
- \+ *structure* two_pointing



## [2022-02-01 06:40:21](https://github.com/leanprover-community/mathlib/commit/5582d84)
feat(ring_theory/localization): fraction rings of algebraic extensions are algebraic ([#11717](https://github.com/leanprover-community/mathlib/pull/11717))
#### Estimated changes
Modified src/ring_theory/algebraic.lean
- \+/\- *lemma* is_algebraic_algebra_map
- \+ *lemma* is_algebraic_algebra_map_of_is_algebraic
- \+ *lemma* is_algebraic_of_larger_base
- \+ *lemma* is_algebraic_of_larger_base_of_injective
- \+/\- *lemma* is_integral.is_algebraic

Modified src/ring_theory/localization.lean
- \+ *lemma* is_fraction_ring.is_algebraic_iff'



## [2022-02-01 02:13:10](https://github.com/leanprover-community/mathlib/commit/4b9f048)
feat(set_theory/principal): Define `principal` ordinals ([#11679](https://github.com/leanprover-community/mathlib/pull/11679))
An ordinal `o` is said to be principal or indecomposable under an operation when the set of ordinals less than it is closed under that operation. In standard mathematical usage, this term is almost exclusively used for additive and multiplicative principal ordinals.
For simplicity, we break usual convention and regard 0 as principal.
#### Estimated changes
Modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* ordinal.nfp_le

Added src/set_theory/principal.lean
- \+ *theorem* ordinal.nfp_le_of_principal
- \+ *theorem* ordinal.op_eq_self_of_principal
- \+ *theorem* ordinal.principal.iterate_lt
- \+ *def* ordinal.principal
- \+ *theorem* ordinal.principal_iff_principal_swap
- \+ *theorem* ordinal.principal_one_iff
- \+ *theorem* ordinal.principal_zero



## [2022-02-01 00:59:42](https://github.com/leanprover-community/mathlib/commit/e37daad)
feat(linear_algebra/sesquilinear_form): Add orthogonality properties ([#10992](https://github.com/leanprover-community/mathlib/pull/10992))
Generalize lemmas about orthogonality from bilinear forms to sesquilinear forms.
#### Estimated changes
Modified src/linear_algebra/bilinear_map.lean
- \+/\- *theorem* linear_map.map_smul₂

Modified src/linear_algebra/sesquilinear_form.lean
- \+ *def* linear_map.is_Ortho
- \+ *lemma* linear_map.is_Ortho_def
- \+/\- *def* linear_map.is_alt
- \+ *lemma* linear_map.is_compl_span_singleton_orthogonal
- \+/\- *def* linear_map.is_ortho
- \+/\- *lemma* linear_map.is_ortho_def
- \+/\- *lemma* linear_map.is_ortho_zero_left
- \+/\- *lemma* linear_map.is_ortho_zero_right
- \+/\- *def* linear_map.is_refl
- \+/\- *lemma* linear_map.is_symm.is_refl
- \+/\- *lemma* linear_map.is_symm.ortho_comm
- \+ *lemma* linear_map.linear_independent_of_is_Ortho
- \+/\- *lemma* linear_map.ortho_smul_left
- \+/\- *lemma* linear_map.ortho_smul_right
- \+ *lemma* linear_map.orthogonal_span_singleton_eq_to_lin_ker
- \+ *lemma* linear_map.span_singleton_inf_orthogonal_eq_bot
- \+ *lemma* linear_map.span_singleton_sup_orthogonal_eq_top
- \+ *lemma* submodule.le_orthogonal_bilin_orthogonal_bilin
- \+ *lemma* submodule.mem_orthogonal_bilin_iff
- \+ *def* submodule.orthogonal_bilin
- \+ *lemma* submodule.orthogonal_bilin_le



## [2022-02-01 00:08:19](https://github.com/leanprover-community/mathlib/commit/b52cb02)
feat(analysis/special_functions/{log, pow}): add log_base ([#11246](https://github.com/leanprover-community/mathlib/pull/11246))
Adds `real.logb`, the log base `b` of `x`, defined as `log x / log b`. Proves that this is related to `real.rpow`.
#### Estimated changes
Modified src/analysis/special_functions/log.lean
- \+/\- *lemma* real.log_le_log

Added src/analysis/special_functions/logb.lean
- \+ *lemma* real.eq_one_of_pos_of_logb_eq_zero
- \+ *lemma* real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_one
- \+ *lemma* real.le_logb_iff_rpow_le
- \+ *lemma* real.le_logb_iff_rpow_le_of_base_lt_one
- \+ *lemma* real.log_div_log
- \+ *lemma* real.logb_abs
- \+ *lemma* real.logb_div
- \+ *lemma* real.logb_eq_zero
- \+ *lemma* real.logb_inj_on_pos
- \+ *lemma* real.logb_inj_on_pos_of_base_lt_one
- \+ *lemma* real.logb_inv
- \+ *lemma* real.logb_le_iff_le_rpow
- \+ *lemma* real.logb_le_iff_le_rpow_of_base_lt_one
- \+ *lemma* real.logb_le_logb
- \+ *lemma* real.logb_le_logb_of_base_lt_one
- \+ *lemma* real.logb_lt_iff_lt_rpow
- \+ *lemma* real.logb_lt_iff_lt_rpow_of_base_lt_one
- \+ *lemma* real.logb_lt_logb
- \+ *lemma* real.logb_lt_logb_iff
- \+ *lemma* real.logb_lt_logb_iff_of_base_lt_one
- \+ *lemma* real.logb_lt_logb_of_base_lt_one
- \+ *lemma* real.logb_mul
- \+ *lemma* real.logb_ne_zero_of_pos_of_ne_one
- \+ *lemma* real.logb_ne_zero_of_pos_of_ne_one_of_base_lt_one
- \+ *lemma* real.logb_neg
- \+ *lemma* real.logb_neg_eq_logb
- \+ *lemma* real.logb_neg_iff
- \+ *lemma* real.logb_neg_iff_of_base_lt_one
- \+ *lemma* real.logb_neg_of_base_lt_one
- \+ *lemma* real.logb_nonneg
- \+ *lemma* real.logb_nonneg_iff
- \+ *lemma* real.logb_nonneg_iff_of_base_lt_one
- \+ *lemma* real.logb_nonneg_of_base_lt_one
- \+ *lemma* real.logb_nonpos
- \+ *lemma* real.logb_nonpos_iff'
- \+ *lemma* real.logb_nonpos_iff
- \+ *lemma* real.logb_nonpos_iff_of_base_lt_one
- \+ *lemma* real.logb_one
- \+ *lemma* real.logb_pos
- \+ *lemma* real.logb_pos_iff
- \+ *lemma* real.logb_pos_iff_of_base_lt_one
- \+ *lemma* real.logb_pos_of_base_lt_one
- \+ *lemma* real.logb_prod
- \+ *lemma* real.logb_rpow
- \+ *lemma* real.logb_surjective
- \+ *lemma* real.logb_zero
- \+ *lemma* real.lt_logb_iff_rpow_lt
- \+ *lemma* real.lt_logb_iff_rpow_lt_of_base_lt_one
- \+ *lemma* real.range_logb
- \+ *lemma* real.rpow_logb
- \+ *lemma* real.rpow_logb_eq_abs
- \+ *lemma* real.rpow_logb_of_neg
- \+ *lemma* real.strict_anti_on_logb
- \+ *lemma* real.strict_anti_on_logb_of_base_lt_one
- \+ *lemma* real.strict_mono_on_logb
- \+ *lemma* real.strict_mono_on_logb_of_base_lt_one
- \+ *lemma* real.surj_on_logb'
- \+ *lemma* real.surj_on_logb
- \+ *lemma* real.tendsto_logb_at_top
- \+ *lemma* real.tendsto_logb_at_top_of_base_lt_one

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* real.rpow_le_rpow_left_iff
- \+ *lemma* real.rpow_le_rpow_left_iff_of_base_lt_one
- \+ *lemma* real.rpow_lt_rpow_left_iff
- \+ *lemma* real.rpow_lt_rpow_left_iff_of_base_lt_one

