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
modified src/algebra/big_operators/finsupp.lean

modified src/data/finsupp/basic.lean
- \+/\- *lemma* prod_add_index
- \+/\- *lemma* prod_add_index'
- \+ *lemma* sum_hom_add_index
- \+ *lemma* prod_hom_add_index
- \+/\- *lemma* prod_add_index
- \- *lemma* sum_add_index'
- \+/\- *lemma* prod_add_index'
- \+/\- *def* lift_add_hom
- \+/\- *def* lift_add_hom

modified src/data/finsupp/multiset.lean

modified src/data/mv_polynomial/variables.lean

modified src/data/nat/factorization.lean

modified src/data/polynomial/basic.lean



## [2022-02-28 12:46:18](https://github.com/leanprover-community/mathlib/commit/1447c40)
refactor(group_theory/general_commutator): Rename `general_commutator` to `subgroup.commutator` ([#12308](https://github.com/leanprover-community/mathlib/pull/12308))
This PR renames `general_commutator` to `subgroup.commutator`.
I'll change the file name in a followup PR, so that this PR is easier to review.
(This is one of the several orthogonal changes from https://github.com/leanprover-community/mathlib/pull/12134)
#### Estimated changes
modified src/group_theory/abelianization.lean

modified src/group_theory/general_commutator.lean
- \+ *lemma* commutator_def
- \+ *lemma* commutator_mono
- \+ *lemma* commutator_def'
- \+ *lemma* commutator_le
- \+ *lemma* commutator_containment
- \+ *lemma* commutator_comm
- \+ *lemma* commutator_le_right
- \+ *lemma* commutator_le_left
- \+ *lemma* commutator_bot
- \+ *lemma* bot_commutator
- \+ *lemma* commutator_le_inf
- \+ *lemma* map_commutator
- \+ *lemma* commutator_prod_prod
- \+ *lemma* commutator_pi_pi_le
- \+ *lemma* commutator_pi_pi_of_fintype
- \- *lemma* general_commutator_def
- \- *lemma* general_commutator_mono
- \- *lemma* general_commutator_def'
- \- *lemma* general_commutator_le
- \- *lemma* general_commutator_containment
- \- *lemma* general_commutator_comm
- \- *lemma* general_commutator_le_right
- \- *lemma* general_commutator_le_left
- \- *lemma* general_commutator_bot
- \- *lemma* bot_general_commutator
- \- *lemma* general_commutator_le_inf
- \- *lemma* map_general_commutator
- \- *lemma* general_commutator_prod_prod
- \- *lemma* general_commutator_pi_pi_le
- \- *lemma* general_commutator_pi_pi_of_fintype

modified src/group_theory/nilpotent.lean

modified src/group_theory/solvable.lean



## [2022-02-28 12:46:17](https://github.com/leanprover-community/mathlib/commit/92cbcc3)
chore(algebra): move star_ring structure on free_algebra ([#12297](https://github.com/leanprover-community/mathlib/pull/12297))
There's no need to have `algebra.star.basic` imported transitively into pretty much everything, just to put the `star_ring` structure on `free_algebra`, so I've moved this construction to its own file.
(I was changing definitions in `algebra.star.basic` to allow for more non-unital structures, it recompiling was very painful because of this transitive dependence.)
#### Estimated changes
modified src/algebra/free_algebra.lean
- \- *lemma* star_ι
- \- *lemma* star_algebra_map
- \- *def* star_hom

modified src/algebra/free_monoid.lean
- \- *lemma* star_of
- \- *lemma* star_one

modified src/algebra/module/linear_map.lean

created src/algebra/star/free.lean
- \+ *lemma* star_of
- \+ *lemma* star_one
- \+ *lemma* star_ι
- \+ *lemma* star_algebra_map
- \+ *def* star_hom

modified src/data/nat/factorization.lean



## [2022-02-28 12:46:16](https://github.com/leanprover-community/mathlib/commit/9c71c0f)
feat(algebra/monoid_algebra/basic): add monomial_hom ([#12283](https://github.com/leanprover-community/mathlib/pull/12283))
Just adding one definition
#### Estimated changes
modified src/algebra/monoid_algebra/basic.lean
- \+ *def* single_hom
- \+ *def* single_hom



## [2022-02-28 12:46:15](https://github.com/leanprover-community/mathlib/commit/c7498d0)
feat(algebra/{group/with_one,order/monoid}): equivs for `with_zero` and `with_one` ([#12275](https://github.com/leanprover-community/mathlib/pull/12275))
This provides:
* `add_equiv.with_zero_congr : α ≃+ β → with_zero α ≃+ with_zero β`
* `mul_equiv.with_one_congr : α ≃* β → with_one α ≃* with_one β`
* `with_zero.to_mul_bot : with_zero (multiplicative α) ≃* multiplicative (with_bot α)`
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/with_zero.20.28multiplicative.20A.29.20.E2.89.83*.20multiplicative.20.28with_bot.20A.29/near/272980650)
#### Estimated changes
modified src/algebra/group/with_one.lean
- \+ *lemma* map_coe
- \+ *lemma* map_map
- \+/\- *lemma* map_comp
- \+ *lemma* _root_.mul_equiv.with_one_congr_refl
- \+ *lemma* _root_.mul_equiv.with_one_congr_symm
- \+ *lemma* _root_.mul_equiv.with_one_congr_trans
- \+/\- *lemma* map_comp
- \+ *def* _root_.mul_equiv.with_one_congr

modified src/algebra/order/monoid.lean
- \+ *lemma* to_mul_bot_zero
- \+ *lemma* to_mul_bot_coe
- \+ *lemma* to_mul_bot_symm_bot
- \+ *lemma* to_mul_bot_coe_of_add
- \+ *lemma* with_zero.to_mul_bot_strict_mono
- \+ *lemma* with_zero.to_mul_bot_le
- \+ *lemma* with_zero.to_mul_bot_lt
- \+ *def* to_mul_bot
- \- *def* ordered_add_comm_monoid



## [2022-02-28 12:46:14](https://github.com/leanprover-community/mathlib/commit/474aecb)
doc(algebra,data/fun_like): small morphism documentation improvements ([#11642](https://github.com/leanprover-community/mathlib/pull/11642))
 * The `fun_like` docs talked about a `to_fun` class, this doesn't exist (anymore).
 * Warn that `{one,mul,monoid,monoid_with_zero}_hom.{congr_fun,congr_arg,coe_inj,ext_iff}` has been superseded by `fun_like`.
Thanks to @YaelDillies for pointing out these issues.
#### Estimated changes
modified src/algebra/group/hom.lean
- \+/\- *lemma* one_hom.ext
- \+/\- *lemma* mul_hom.ext
- \+/\- *lemma* monoid_hom.ext
- \+/\- *lemma* monoid_with_zero_hom.ext
- \+/\- *lemma* one_hom.ext
- \+/\- *lemma* mul_hom.ext
- \+/\- *lemma* monoid_hom.ext
- \+/\- *lemma* monoid_with_zero_hom.ext

modified src/algebra/module/linear_map.lean

modified src/algebra/ring/basic.lean

modified src/analysis/normed_space/linear_isometry.lean

modified src/analysis/seminorm.lean

modified src/data/fun_like/basic.lean

modified src/ring_theory/derivation.lean



## [2022-02-28 12:16:38](https://github.com/leanprover-community/mathlib/commit/33c0a1c)
feat(ring_theory/dedekind_domain/ideal): add height_one_spectrum ([#12244](https://github.com/leanprover-community/mathlib/pull/12244))
#### Estimated changes
modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* height_one_spectrum.prime
- \+ *lemma* height_one_spectrum.irreducible
- \+ *lemma* height_one_spectrum.associates.irreducible



## [2022-02-28 10:33:37](https://github.com/leanprover-community/mathlib/commit/200c254)
feat(algebra/algebra,data/equiv/ring): `{ring,alg}_equiv.Pi_congr_right` ([#12289](https://github.com/leanprover-community/mathlib/pull/12289))
We extend `{add,mul}_equiv.Pi_congr_right` to rings and algebras.
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60ring_equiv.2EPi_congr_right.60
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+ *lemma* Pi_congr_right_refl
- \+ *lemma* Pi_congr_right_symm
- \+ *lemma* Pi_congr_right_trans
- \+ *def* Pi_congr_right

modified src/data/equiv/ring.lean
- \+ *lemma* Pi_congr_right_refl
- \+ *lemma* Pi_congr_right_symm
- \+ *lemma* Pi_congr_right_trans
- \+ *def* Pi_congr_right



## [2022-02-28 10:33:35](https://github.com/leanprover-community/mathlib/commit/e700d56)
feat(ring_theory/polynomial/eisenstein): add a technical lemma ([#11839](https://github.com/leanprover-community/mathlib/pull/11839))
A technical lemma about Eiseinstein minimal polynomials.
From flt-regular
#### Estimated changes
modified src/algebra/associated.lean
- \+ *lemma* prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd

modified src/data/nat/basic.lean
- \+ *lemma* le_add_pred_of_pos

modified src/data/polynomial/monic.lean
- \+ *lemma* nat_degree_map_of_monic
- \+ *lemma* degree_map_of_monic

modified src/ring_theory/integral_closure.lean
- \+ *lemma* is_integral_smul

modified src/ring_theory/polynomial/eisenstein.lean
- \+ *lemma* dvd_coeff_zero_of_aeval_eq_prime_smul_of_minpoly_is_eiseinstein_at



## [2022-02-28 10:33:34](https://github.com/leanprover-community/mathlib/commit/770a7ce)
feat(measure_theory/function/convergence_in_measure): Define convergence in measure ([#11774](https://github.com/leanprover-community/mathlib/pull/11774))
This PR defines convergence in measure and proves some properties about them. 
In particular, we prove that 
- convergence a.e. in a finite measure space implies convergence in measure
- convergence in measure implies there exists a subsequence that converges a.e.
- convergence in Lp implies convergence in measure
#### Estimated changes
modified docs/undergrad.yaml

modified src/analysis/specific_limits.lean
- \+ *lemma* tsum_geometric_inv_two
- \+ *lemma* tsum_geometric_inv_two_ge

modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* ae_measurable_of_tendsto_metric_ae
- \+ *lemma* ae_measurable_of_tendsto_metric_ae'
- \+/\- *lemma* ae_measurable_of_tendsto_metric_ae

created src/measure_theory/function/convergence_in_measure.lean
- \+ *lemma* tendsto_in_measure_iff_norm
- \+ *lemma* congr_left
- \+ *lemma* congr_right
- \+ *lemma* tendsto_in_measure_of_tendsto_ae_of_measurable
- \+ *lemma* tendsto_in_measure_of_tendsto_ae
- \+ *lemma* exists_nat_measure_lt_two_inv
- \+ *lemma* seq_tendsto_ae_seq_succ
- \+ *lemma* seq_tendsto_ae_seq_spec
- \+ *lemma* seq_tendsto_ae_seq_strict_mono
- \+ *lemma* tendsto_in_measure.exists_seq_tendsto_ae
- \+ *lemma* tendsto_in_measure.exists_seq_tendsto_in_measure_at_top
- \+ *lemma* tendsto_in_measure.exists_seq_tendsto_ae'
- \+ *lemma* tendsto_in_measure.ae_measurable
- \+ *lemma* tendsto_in_measure_of_tendsto_snorm_of_measurable
- \+ *lemma* tendsto_in_measure_of_tendsto_snorm_of_ne_top
- \+ *lemma* tendsto_in_measure_of_tendsto_snorm_top
- \+ *lemma* tendsto_in_measure_of_tendsto_snorm
- \+ *lemma* tendsto_in_measure_of_tendsto_Lp
- \+ *def* tendsto_in_measure
- \+ *def* seq_tendsto_ae_seq_aux
- \+ *def* seq_tendsto_ae_seq

modified src/measure_theory/function/l1_space.lean

modified src/measure_theory/integral/set_to_l1.lean

modified src/topology/instances/ennreal.lean



## [2022-02-28 10:33:33](https://github.com/leanprover-community/mathlib/commit/b25bad7)
feat(archive/100-theorems-list): Partition theorem ([#4259](https://github.com/leanprover-community/mathlib/pull/4259))
A proof of Euler's partition theorem, from the Freek list.
The proof is sorry-free but currently unpleasant, and some parts don't belong in `archive/`, so WIP for now.
#### Estimated changes
created archive/100-theorems-list/45_partition.lean
- \+ *lemma* mem_cut
- \+ *lemma* cut_equiv_antidiag
- \+ *lemma* cut_zero
- \+ *lemma* cut_empty_succ
- \+ *lemma* cut_insert
- \+ *lemma* coeff_prod_range
- \+ *lemma* coeff_indicator
- \+ *lemma* coeff_indicator_pos
- \+ *lemma* coeff_indicator_neg
- \+ *lemma* constant_coeff_indicator
- \+ *lemma* two_series
- \+ *lemma* num_series'
- \+ *lemma* partial_gf_prop
- \+ *lemma* partial_odd_gf_prop
- \+ *lemma* partial_distinct_gf_prop
- \+ *lemma* same_gf
- \+ *lemma* same_coeffs
- \+ *theorem* odd_gf_prop
- \+ *theorem* distinct_gf_prop
- \+ *theorem* partition_theorem
- \+ *def* partial_odd_gf
- \+ *def* partial_distinct_gf
- \+ *def* cut
- \+ *def* indicator_series
- \+ *def* mk_odd

modified docs/100.yaml

modified src/algebra/big_operators/basic.lean
- \+ *lemma* mem_sum

modified src/data/list/nat_antidiagonal.lean



## [2022-02-28 09:09:20](https://github.com/leanprover-community/mathlib/commit/dc72624)
chore(measure_theory/function/strongly_measurable): remove useless no_zero_divisors assumption ([#12353](https://github.com/leanprover-community/mathlib/pull/12353))
#### Estimated changes
modified src/algebra/support.lean
- \+ *lemma* support_mul_subset_left
- \+ *lemma* support_mul_subset_right

modified src/measure_theory/function/strongly_measurable.lean



## [2022-02-28 08:31:53](https://github.com/leanprover-community/mathlib/commit/58c20c1)
feat(measure_theory/group): add measures invariant under inversion/negation ([#11954](https://github.com/leanprover-community/mathlib/pull/11954))
* Define measures invariant under `inv` or `neg`
* Prove lemmas about measures invariant under `inv` similar to the lemmas about measures invariant under `mul`
* Also provide more `pi` instances in `arithmetic`.
* Rename some `integral_zero...` lemmas to `integral_eq_zero...`
* Reformulate `pi.is_mul_left_invariant_volume` using nondependent functions, so that type class inference can find it for `ι → ℝ`)
* Add some more integration lemmas, also for multiplication
#### Estimated changes
modified src/analysis/fourier.lean

modified src/measure_theory/constructions/pi.lean

modified src/measure_theory/function/l1_space.lean
- \+ *lemma* integrable.comp_measurable

modified src/measure_theory/group/arithmetic.lean

modified src/measure_theory/group/integration.lean
- \+ *lemma* integrable.comp_inv
- \+ *lemma* integral_inv_eq_self
- \+ *lemma* integral_eq_zero_of_mul_left_eq_neg
- \+ *lemma* integral_eq_zero_of_mul_right_eq_neg
- \+ *lemma* integrable.comp_mul_left
- \+ *lemma* integrable.comp_mul_right
- \+ *lemma* integrable.comp_div_right
- \+ *lemma* integrable.comp_div_left
- \+ *lemma* integral_div_left_eq_self
- \- *lemma* integral_zero_of_mul_left_eq_neg
- \- *lemma* integral_zero_of_mul_right_eq_neg

modified src/measure_theory/group/measure.lean
- \+ *lemma* map_div_right_eq_self
- \+ *lemma* inv_eq_self
- \+ *lemma* map_inv_eq_self
- \+ *lemma* measure_inv
- \+ *lemma* measure_preimage_inv
- \+ *lemma* map_div_left_eq_self
- \+ *lemma* map_mul_right_inv_eq_self

modified src/measure_theory/integral/bochner.lean
- \+ *lemma* integral_norm_eq_lintegral_nnnorm

modified src/measure_theory/measure/haar_lebesgue.lean

modified src/measure_theory/measure/lebesgue.lean
- \- *lemma* map_volume_neg

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* map_id'



## [2022-02-28 02:34:22](https://github.com/leanprover-community/mathlib/commit/f3a04ed)
feat(group_theory/subgroup/basic): Centralizer subgroup ([#11946](https://github.com/leanprover-community/mathlib/pull/11946))
This PR defines the centralizer subgroup, and provides a few basic lemmas.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* mem_centralizer_iff
- \+ *lemma* mem_centralizer_iff_commutator_eq_one
- \+ *lemma* centralizer_top
- \+ *def* centralizer

created src/group_theory/submonoid/centralizer.lean
- \+ *lemma* mem_centralizer_iff
- \+ *lemma* one_mem_centralizer
- \+ *lemma* zero_mem_centralizer
- \+ *lemma* mul_mem_centralizer
- \+ *lemma* inv_mem_centralizer
- \+ *lemma* add_mem_centralizer
- \+ *lemma* neg_mem_centralizer
- \+ *lemma* inv_mem_centralizer₀
- \+ *lemma* div_mem_centralizer
- \+ *lemma* div_mem_centralizer₀
- \+ *lemma* centralizer_subset
- \+ *lemma* centralizer_univ
- \+ *lemma* centralizer_eq_univ
- \+ *lemma* coe_centralizer
- \+ *lemma* mem_centralizer_iff
- \+ *lemma* centralizer_subset
- \+ *lemma* centralizer_univ
- \+ *def* centralizer
- \+ *def* centralizer



## [2022-02-27 23:09:46](https://github.com/leanprover-community/mathlib/commit/2f86b49)
doc(data/set_like/basic): tidy up docstring ([#12337](https://github.com/leanprover-community/mathlib/pull/12337))
Hopefully this makes the docstring slightly clearer.
#### Estimated changes
modified src/data/set_like/basic.lean



## [2022-02-27 23:09:45](https://github.com/leanprover-community/mathlib/commit/dfacfd3)
chore(linear_algebra/basic): make `linear_map.id_coe` elegible for `dsimp` ([#12334](https://github.com/leanprover-community/mathlib/pull/12334))
`dsimp` only considers lemmas which _are_ proved by `rfl`, not ones that just _could_ be.
#### Estimated changes
modified src/algebra/module/linear_map.lean
- \+/\- *lemma* id_coe
- \+/\- *lemma* id_coe

modified src/linear_algebra/finsupp.lean



## [2022-02-27 22:39:10](https://github.com/leanprover-community/mathlib/commit/f322fa0)
refactor(group_theory/solvable): Delete duplicate lemma ([#12307](https://github.com/leanprover-community/mathlib/pull/12307))
`map_commutator_eq_commutator_map` is a duplicate of `map_general_commutator`.
(This is one of the several orthogonal changes from [#12134](https://github.com/leanprover-community/mathlib/pull/12134))
#### Estimated changes
modified src/group_theory/solvable.lean
- \- *lemma* map_commutator_eq_commutator_map



## [2022-02-27 22:00:44](https://github.com/leanprover-community/mathlib/commit/7f52f94)
feat(analysis/complex): maximum modulus principle ([#12050](https://github.com/leanprover-community/mathlib/pull/12050))
#### Estimated changes
created src/analysis/complex/abs_max.lean
- \+ *lemma* norm_max_aux₁
- \+ *lemma* norm_max_aux₂
- \+ *lemma* norm_max_aux₃
- \+ *lemma* norm_eq_on_closed_ball_of_is_max_on
- \+ *lemma* norm_eq_norm_of_is_max_on_of_closed_ball_subset
- \+ *lemma* norm_eventually_eq_of_is_local_max
- \+ *lemma* is_open_set_of_mem_nhds_and_is_max_on_norm
- \+ *lemma* exists_mem_frontier_is_max_on_norm
- \+ *lemma* norm_le_of_forall_mem_frontier_norm_le
- \+ *lemma* eq_on_of_eq_on_frontier



## [2022-02-27 21:28:31](https://github.com/leanprover-community/mathlib/commit/b5faa34)
feat(analysis/complex/liouville): prove Liouville's theorem ([#12095](https://github.com/leanprover-community/mathlib/pull/12095))
#### Estimated changes
created src/analysis/complex/liouville.lean
- \+ *lemma* deriv_eq_smul_circle_integral
- \+ *lemma* norm_deriv_le_aux
- \+ *lemma* norm_deriv_le_of_forall_mem_sphere_norm_le
- \+ *lemma* liouville_theorem_aux
- \+ *lemma* apply_eq_apply_of_bounded
- \+ *lemma* exists_const_forall_eq_of_bounded
- \+ *lemma* exists_eq_const_of_bounded



## [2022-02-27 20:07:58](https://github.com/leanprover-community/mathlib/commit/a5ffb9b)
feat(analysis/special_functions): little o behaviour of exp/log at infinity ([#11840](https://github.com/leanprover-community/mathlib/pull/11840))
from the unit-fractions project
#### Estimated changes
modified src/analysis/special_functions/exp.lean
- \+/\- *lemma* tendsto_mul_exp_add_div_pow_at_top
- \+/\- *lemma* tendsto_div_pow_mul_exp_add_at_top
- \+ *lemma* is_o_pow_exp_at_top
- \+/\- *lemma* tendsto_mul_exp_add_div_pow_at_top
- \+/\- *lemma* tendsto_div_pow_mul_exp_add_at_top

modified src/analysis/special_functions/log.lean
- \+ *lemma* tendsto_pow_log_div_mul_add_at_top
- \+ *lemma* is_o_pow_log_id_at_top

modified src/analysis/special_functions/pow.lean



## [2022-02-27 16:32:35](https://github.com/leanprover-community/mathlib/commit/c4cf451)
fix(catgory_theory/limits): fix a typo ([#12341](https://github.com/leanprover-community/mathlib/pull/12341))
#### Estimated changes
modified src/category_theory/limits/preserves/shapes/zero.lean



## [2022-02-27 16:04:10](https://github.com/leanprover-community/mathlib/commit/8ef4331)
feat(ring_theory/witt_vector): Witt vectors are a DVR ([#12213](https://github.com/leanprover-community/mathlib/pull/12213))
This PR adds two connected files. `mul_coeff.lean` adds an auxiliary result that's used in a few places in [#12041](https://github.com/leanprover-community/mathlib/pull/12041) . One of these places is in `discrete_valuation_ring.lean`, which shows that Witt vectors over a perfect field form a DVR.
#### Estimated changes
created src/ring_theory/witt_vector/discrete_valuation_ring.lean
- \+ *lemma* coe_mk_unit
- \+ *lemma* is_unit_of_coeff_zero_ne_zero
- \+ *lemma* irreducible
- \+ *lemma* exists_eq_pow_p_mul
- \+ *lemma* exists_eq_pow_p_mul'
- \+ *def* succ_nth_val_units
- \+ *def* mk_unit

modified src/ring_theory/witt_vector/identities.lean
- \+ *lemma* coeff_p
- \+ *lemma* coeff_p_zero
- \+ *lemma* coeff_p_one
- \+/\- *lemma* p_nonzero
- \+/\- *lemma* p_nonzero

created src/ring_theory/witt_vector/mul_coeff.lean
- \+ *lemma* witt_poly_prod_vars
- \+ *lemma* witt_poly_prod_remainder_vars
- \+ *lemma* remainder_vars
- \+ *lemma* mul_poly_of_interest_aux1
- \+ *lemma* mul_poly_of_interest_aux2
- \+ *lemma* mul_poly_of_interest_aux3
- \+ *lemma* mul_poly_of_interest_aux4
- \+ *lemma* mul_poly_of_interest_aux5
- \+ *lemma* mul_poly_of_interest_vars
- \+ *lemma* poly_of_interest_vars_eq
- \+ *lemma* poly_of_interest_vars
- \+ *lemma* peval_poly_of_interest
- \+ *lemma* peval_poly_of_interest'
- \+ *lemma* nth_mul_coeff'
- \+ *lemma* nth_mul_coeff
- \+ *lemma* nth_remainder_spec
- \+ *def* witt_poly_prod
- \+ *def* witt_poly_prod_remainder
- \+ *def* remainder
- \+ *def* poly_of_interest
- \+ *def* nth_remainder



## [2022-02-27 15:35:55](https://github.com/leanprover-community/mathlib/commit/1dfb38d)
doc(imo*,algebra/continued_fractions/computation): change \minus to - ([#12338](https://github.com/leanprover-community/mathlib/pull/12338))
Change around 14 instances of a non-standard minus to `-`.
#### Estimated changes
modified archive/imo/imo1998_q2.lean

modified archive/imo/imo2005_q4.lean

modified archive/imo/imo2011_q5.lean

modified archive/imo/imo2019_q4.lean

modified src/algebra/continued_fractions/computation/basic.lean



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
modified src/geometry/euclidean/basic.lean

modified src/geometry/euclidean/oriented_angle.lean
- \+ *lemma* oangle_zero_left
- \+ *lemma* oangle_zero_right
- \+ *lemma* oangle_self
- \+ *lemma* oangle_rev
- \+ *lemma* oangle_add_oangle_rev
- \+ *lemma* oangle_neg_left
- \+ *lemma* oangle_neg_right
- \+ *lemma* two_zsmul_oangle_neg_left
- \+ *lemma* two_zsmul_oangle_neg_right
- \+ *lemma* oangle_neg_neg
- \+ *lemma* oangle_neg_left_eq_neg_right
- \+ *lemma* oangle_neg_self_left
- \+ *lemma* oangle_neg_self_right
- \+ *lemma* two_zsmul_oangle_neg_self_left
- \+ *lemma* two_zsmul_oangle_neg_self_right
- \+ *lemma* oangle_add_oangle_rev_neg_left
- \+ *lemma* oangle_add_oangle_rev_neg_right
- \+ *lemma* oangle_smul_left_of_pos
- \+ *lemma* oangle_smul_right_of_pos
- \+ *lemma* oangle_smul_left_of_neg
- \+ *lemma* oangle_smul_right_of_neg
- \+ *lemma* oangle_smul_left_self_of_nonneg
- \+ *lemma* oangle_smul_right_self_of_nonneg
- \+ *lemma* oangle_smul_smul_self_of_nonneg
- \+ *lemma* two_zsmul_oangle_smul_left_of_ne_zero
- \+ *lemma* two_zsmul_oangle_smul_right_of_ne_zero
- \+ *lemma* two_zsmul_oangle_smul_left_self
- \+ *lemma* two_zsmul_oangle_smul_right_self
- \+ *lemma* two_zsmul_oangle_smul_smul_self
- \+ *lemma* eq_iff_norm_eq_and_oangle_eq_zero
- \+ *lemma* eq_iff_oangle_eq_zero_of_norm_eq
- \+ *lemma* eq_iff_norm_eq_of_oangle_eq_zero
- \+ *lemma* oangle_add
- \+ *lemma* oangle_add_swap
- \+ *lemma* oangle_sub_left
- \+ *lemma* oangle_sub_right
- \+ *lemma* oangle_add_cyc3
- \+ *lemma* oangle_add_cyc3_neg_left
- \+ *lemma* oangle_add_cyc3_neg_right
- \+ *lemma* oangle_sub_eq_oangle_sub_rev_of_norm_eq
- \+ *lemma* oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq
- \+ *lemma* oangle_eq_two_zsmul_oangle_sub_of_norm_eq
- \+ *lemma* oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real
- \+ *lemma* two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq
- \+ *lemma* det_rotation
- \+ *lemma* linear_equiv_det_rotation
- \+ *lemma* rotation_symm
- \+ *lemma* rotation_zero
- \+ *lemma* rotation_pi
- \+ *lemma* rotation_trans
- \+ *lemma* oangle_rotation_left
- \+ *lemma* oangle_rotation_right
- \+ *lemma* oangle_rotation_self_left
- \+ *lemma* oangle_rotation_self_right
- \+ *lemma* oangle_rotation_oangle_left
- \+ *lemma* oangle_rotation_oangle_right
- \+ *lemma* oangle_rotation
- \+ *lemma* rotation_eq_self_iff_angle_eq_zero
- \+ *lemma* eq_rotation_self_iff_angle_eq_zero
- \+ *lemma* rotation_eq_self_iff
- \+ *lemma* eq_rotation_self_iff
- \+ *lemma* rotation_oangle_eq_iff_norm_eq
- \+ *lemma* oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero
- \+ *lemma* oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
- \+ *lemma* oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero
- \+ *lemma* oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero
- \+ *lemma* exists_linear_isometry_equiv_eq_of_det_pos
- \+ *lemma* oangle_map
- \+ *lemma* oangle_eq_basis_oangle
- \+ *lemma* oangle_neg_orientation_eq_neg
- \+ *lemma* rotation_eq_basis_rotation
- \+ *lemma* rotation_neg_orientation_eq_neg
- \+ *def* oangle
- \+ *def* rotation



## [2022-02-27 10:57:38](https://github.com/leanprover-community/mathlib/commit/77e76ee)
feat(data/list/basic): add last'_append and head'_append_of_ne_nil ([#12221](https://github.com/leanprover-community/mathlib/pull/12221))
we already have `head'_append` and `last'_append_of_ne_nil`, and users
might expect a symmetric API.
#### Estimated changes
modified src/data/list/basic.lean
- \+ *theorem* last'_append
- \+ *theorem* head'_append_of_ne_nil



## [2022-02-27 09:13:42](https://github.com/leanprover-community/mathlib/commit/b1c2d70)
feat(logic/function/basic): not_surjective_Type ([#12311](https://github.com/leanprover-community/mathlib/pull/12311))
#### Estimated changes
modified src/logic/function/basic.lean
- \+ *theorem* not_surjective_Type



## [2022-02-27 08:45:41](https://github.com/leanprover-community/mathlib/commit/7ae0b36)
chore(category_theory/idempotents): minor suggestions ([#12303](https://github.com/leanprover-community/mathlib/pull/12303))
@joelriou, here are some minor suggestions on your earlier Karoubi envelope work (I wasn't around when the PR went through.)
The two separate suggestions are some typos, and dropping some unnecessary proofs.
#### Estimated changes
modified src/category_theory/idempotents/basic.lean

modified src/category_theory/idempotents/karoubi.lean



## [2022-02-27 06:00:11](https://github.com/leanprover-community/mathlib/commit/07374a2)
feat(set_theory/cardinal): add three_le ([#12225](https://github.com/leanprover-community/mathlib/pull/12225))
#### Estimated changes
modified src/data/finset/card.lean
- \+ *lemma* le_card_sdiff

modified src/set_theory/cardinal.lean
- \+/\- *lemma* two_le_iff
- \+/\- *lemma* two_le_iff'
- \+ *lemma* exists_not_mem_of_length_le
- \+ *lemma* three_le
- \+/\- *lemma* two_le_iff
- \+/\- *lemma* two_le_iff'



## [2022-02-27 04:07:15](https://github.com/leanprover-community/mathlib/commit/86d686c)
feat(category_theory/category/Groupoid): Add coercion to sort ([#12324](https://github.com/leanprover-community/mathlib/pull/12324))
Use coercion to type instead of `.α`
#### Estimated changes
modified src/category_theory/category/Groupoid.lean
- \+ *lemma* coe_of

modified src/topology/homotopy/fundamental_groupoid.lean
- \+/\- *def* to_top
- \+/\- *def* from_top
- \+/\- *def* to_path
- \+/\- *def* to_top
- \+/\- *def* from_top
- \+/\- *def* to_path

modified src/topology/homotopy/product.lean
- \+/\- *lemma* proj_map
- \+/\- *lemma* proj_left_map
- \+/\- *lemma* proj_right_map
- \+/\- *lemma* proj_map
- \+/\- *lemma* proj_left_map
- \+/\- *lemma* proj_right_map
- \+/\- *def* proj
- \+/\- *def* pi_to_pi_Top
- \+/\- *def* pi_iso
- \+/\- *def* proj_left
- \+/\- *def* proj_right
- \+/\- *def* prod_to_prod_Top
- \+/\- *def* prod_iso
- \+/\- *def* proj
- \+/\- *def* pi_to_pi_Top
- \+/\- *def* pi_iso
- \+/\- *def* proj_left
- \+/\- *def* proj_right
- \+/\- *def* prod_to_prod_Top
- \+/\- *def* prod_iso



## [2022-02-27 04:07:14](https://github.com/leanprover-community/mathlib/commit/907e5ba)
fix(set_theory/ordinal_arithmetic): Fix universes ([#12320](https://github.com/leanprover-community/mathlib/pull/12320))
`lsub_le_of_range_subset` and `lsub_eq_of_range_eq` should have had 3 universes, but they had only two.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean



## [2022-02-27 04:07:13](https://github.com/leanprover-community/mathlib/commit/906a88b)
feat(data/quot): primed quotient funcs on `mk` ([#12204](https://github.com/leanprover-community/mathlib/pull/12204))
#### Estimated changes
modified src/data/quot.lean
- \+ *lemma* map'_mk



## [2022-02-27 02:45:05](https://github.com/leanprover-community/mathlib/commit/4afb8d2)
feat(set_theory/ordinal_arithmetic): Added missing theorems for `lsub` and `blsub` ([#12318](https://github.com/leanprover-community/mathlib/pull/12318))
These are the analogs of `lt_sup` and `lt_bsup`, respectively.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* lt_lsub_iff
- \+ *theorem* lt_blsub_iff



## [2022-02-27 02:45:04](https://github.com/leanprover-community/mathlib/commit/bb9539c)
chore(set_theory/ordinal): Minor golf in `card` ([#12298](https://github.com/leanprover-community/mathlib/pull/12298))
This was suggested by @b-mehta.
#### Estimated changes
modified src/set_theory/ordinal.lean



## [2022-02-27 02:45:02](https://github.com/leanprover-community/mathlib/commit/b4f87d9)
feat(analysis/normed_space): add `normed_space 𝕜 (uniform_space.completion E)` ([#12148](https://github.com/leanprover-community/mathlib/pull/12148))
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* lipschitz_with_smul

created src/analysis/normed_space/completion.lean
- \+ *lemma* coe_to_complₗᵢ
- \+ *lemma* coe_to_complL
- \+ *lemma* norm_to_complL
- \+ *def* to_complₗᵢ
- \+ *def* to_complL

created src/topology/algebra/uniform_mul_action.lean
- \+ *lemma* uniform_continuous.const_smul
- \+ *lemma* coe_smul

modified src/topology/uniform_space/completion.lean
- \+ *lemma* ext'



## [2022-02-27 01:14:05](https://github.com/leanprover-community/mathlib/commit/abf5dfc)
refactor(category_theory/eq_to_hom): conjugation by eq_to_hom same as heq ([#12025](https://github.com/leanprover-community/mathlib/pull/12025))
Xu Junyan provided this lemma for showing that `heq` gives the same as conjugation by `eq_to_hom` for equality of functor maps. I refactored `hext` using this result.
Then I added a bunch of lemmas for how `heq` interacts with composition of functors and `functor.map` applied to composition of morphisms
#### Estimated changes
modified src/category_theory/eq_to_hom.lean
- \+ *lemma* conj_eq_to_hom_iff_heq
- \+ *lemma* map_comp_heq
- \+ *lemma* map_comp_heq'
- \+ *lemma* precomp_map_heq
- \+ *lemma* postcomp_map_heq
- \+ *lemma* postcomp_map_heq'
- \+ *lemma* hcongr_hom



## [2022-02-27 01:14:04](https://github.com/leanprover-community/mathlib/commit/1fe9708)
feat(group_theory/nilpotent): is_nilpotent_of_product_of_sylow_group ([#11834](https://github.com/leanprover-community/mathlib/pull/11834))
#### Estimated changes
modified src/group_theory/nilpotent.lean
- \+ *lemma* nilpotent_of_mul_equiv
- \+/\- *lemma* is_p_group.is_nilpotent
- \+/\- *lemma* is_p_group.is_nilpotent
- \+ *theorem* is_nilpotent_of_product_of_sylow_group



## [2022-02-26 23:31:58](https://github.com/leanprover-community/mathlib/commit/add068d)
chore(linear_algebra/orientation): split into 2 files ([#12302](https://github.com/leanprover-community/mathlib/pull/12302))
Move parts that don't need multilinear maps to a new file.
#### Estimated changes
modified src/linear_algebra/orientation.lean
- \- *lemma* same_ray.refl
- \- *lemma* same_ray.symm
- \- *lemma* same_ray.trans
- \- *lemma* same_ray_comm
- \- *lemma* equivalence_same_ray
- \- *lemma* same_ray_pos_smul_right
- \- *lemma* same_ray.pos_smul_right
- \- *lemma* same_ray_pos_smul_left
- \- *lemma* same_ray.pos_smul_left
- \- *lemma* same_ray.map
- \- *lemma* same_ray_map_iff
- \- *lemma* same_ray.smul
- \- *lemma* equiv_iff_same_ray
- \- *lemma* module.ray.ind
- \- *lemma* ray_eq_iff
- \- *lemma* ray_pos_smul
- \- *lemma* module.ray.map_apply
- \- *lemma* module.ray.map_refl
- \- *lemma* module.ray.map_symm
- \- *lemma* module.ray.linear_equiv_smul_eq_map
- \- *lemma* smul_ray_of_ne_zero
- \- *lemma* units_smul_of_pos
- \- *lemma* some_ray_vector_ray
- \- *lemma* some_vector_ne_zero
- \- *lemma* some_vector_ray
- \- *lemma* same_ray.neg
- \- *lemma* same_ray_neg_iff
- \- *lemma* same_ray_neg_swap
- \- *lemma* eq_zero_of_same_ray_self_neg
- \- *lemma* coe_neg
- \- *lemma* equiv_neg_iff
- \- *lemma* ray_neg
- \- *lemma* ne_neg_self
- \- *lemma* units_smul_of_neg
- \- *lemma* same_ray_of_mem_orbit
- \- *lemma* units_inv_smul
- \- *lemma* same_ray_smul_right_iff
- \- *lemma* same_ray_smul_left_iff
- \- *lemma* same_ray_neg_smul_right_iff
- \- *lemma* same_ray_neg_smul_left_iff
- \- *lemma* units_smul_eq_self_iff
- \- *lemma* units_smul_eq_neg_iff
- \- *lemma* same_ray_iff_mem_orbit
- \- *lemma* same_ray_setoid_eq_orbit_rel
- \- *def* same_ray
- \- *def* same_ray_setoid
- \- *def* ray_vector
- \- *def* ray_vector.same_ray_setoid
- \- *def* module.ray
- \- *def* ray_vector.map_linear_equiv
- \- *def* module.ray.map
- \- *def* some_ray_vector
- \- *def* some_vector

created src/linear_algebra/ray.lean
- \+ *lemma* same_ray.refl
- \+ *lemma* same_ray.symm
- \+ *lemma* same_ray.trans
- \+ *lemma* same_ray_comm
- \+ *lemma* equivalence_same_ray
- \+ *lemma* same_ray_pos_smul_right
- \+ *lemma* same_ray.pos_smul_right
- \+ *lemma* same_ray_pos_smul_left
- \+ *lemma* same_ray.pos_smul_left
- \+ *lemma* same_ray.map
- \+ *lemma* same_ray_map_iff
- \+ *lemma* same_ray.smul
- \+ *lemma* equiv_iff_same_ray
- \+ *lemma* module.ray.ind
- \+ *lemma* ray_eq_iff
- \+ *lemma* ray_pos_smul
- \+ *lemma* module.ray.map_apply
- \+ *lemma* module.ray.map_refl
- \+ *lemma* module.ray.map_symm
- \+ *lemma* module.ray.linear_equiv_smul_eq_map
- \+ *lemma* smul_ray_of_ne_zero
- \+ *lemma* units_smul_of_pos
- \+ *lemma* some_ray_vector_ray
- \+ *lemma* some_vector_ne_zero
- \+ *lemma* some_vector_ray
- \+ *lemma* same_ray.neg
- \+ *lemma* same_ray_neg_iff
- \+ *lemma* same_ray_neg_swap
- \+ *lemma* eq_zero_of_same_ray_self_neg
- \+ *lemma* coe_neg
- \+ *lemma* equiv_neg_iff
- \+ *lemma* ray_neg
- \+ *lemma* ne_neg_self
- \+ *lemma* units_smul_of_neg
- \+ *lemma* same_ray_of_mem_orbit
- \+ *lemma* units_inv_smul
- \+ *lemma* same_ray_smul_right_iff
- \+ *lemma* same_ray_smul_left_iff
- \+ *lemma* same_ray_neg_smul_right_iff
- \+ *lemma* same_ray_neg_smul_left_iff
- \+ *lemma* units_smul_eq_self_iff
- \+ *lemma* units_smul_eq_neg_iff
- \+ *lemma* same_ray_iff_mem_orbit
- \+ *lemma* same_ray_setoid_eq_orbit_rel
- \+ *def* same_ray
- \+ *def* same_ray_setoid
- \+ *def* ray_vector
- \+ *def* ray_vector.same_ray_setoid
- \+ *def* module.ray
- \+ *def* ray_vector.map_linear_equiv
- \+ *def* module.ray.map
- \+ *def* some_ray_vector
- \+ *def* some_vector



## [2022-02-26 23:31:57](https://github.com/leanprover-community/mathlib/commit/188b371)
feat(algebra/category/GroupWithZero): The category of groups with zero ([#12278](https://github.com/leanprover-community/mathlib/pull/12278))
Define `GroupWithZero`, the category of groups with zero with monoid with zero homs.
#### Estimated changes
created src/algebra/category/GroupWithZero.lean
- \+ *def* GroupWithZero
- \+ *def* of
- \+ *def* iso.mk

modified src/data/equiv/mul_add.lean



## [2022-02-26 23:31:55](https://github.com/leanprover-community/mathlib/commit/163d1a6)
feat(category_theory/idempotents): idempotent completeness and functor categories ([#12270](https://github.com/leanprover-community/mathlib/pull/12270))
#### Estimated changes
created src/category_theory/idempotents/functor_categories.lean
- \+ *lemma* to_karoubi_comp_karoubi_functor_category_embedding
- \+ *def* obj
- \+ *def* map
- \+ *def* karoubi_functor_category_embedding

created src/category_theory/idempotents/simplicial_object.lean



## [2022-02-26 23:31:53](https://github.com/leanprover-community/mathlib/commit/817b4c4)
feat(order/category/BoundedLattice): The category of bounded lattices ([#12257](https://github.com/leanprover-community/mathlib/pull/12257))
Define `BoundedLattice`, the category of bounded lattices with bounded lattice homs.
#### Estimated changes
created src/order/category/BoundedLattice.lean
- \+ *lemma* forget_Lattice_PartialOrder_eq_forget_BoundedOrder_PartialOrder
- \+ *lemma* BoundedLattice_dual_comp_forget_to_Lattice
- \+ *lemma* BoundedLattice_dual_comp_forget_to_BoundedOrder
- \+ *def* of
- \+ *def* iso.mk
- \+ *def* dual
- \+ *def* dual_equiv

modified src/order/hom/lattice.lean



## [2022-02-26 22:03:39](https://github.com/leanprover-community/mathlib/commit/3d8c22f)
refactor(topology/compact_open): Remove `locally_compact_space` hypothesis in `continuous_map.t2_space` ([#12306](https://github.com/leanprover-community/mathlib/pull/12306))
This PR removes the `locally_compact_space` hypothesis in `continuous_map.t2_space`, at the cost of a longer proof.
#### Estimated changes
modified src/topology/algebra/continuous_monoid_hom.lean

modified src/topology/compact_open.lean



## [2022-02-26 20:55:45](https://github.com/leanprover-community/mathlib/commit/4cf0e60)
feat(category_theory/limits): generalize has_biproduct.of_has_product  ([#12116](https://github.com/leanprover-community/mathlib/pull/12116))
#### Estimated changes
modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* binary_fan_fst_to_cone
- \+ *lemma* binary_fan_snd_to_cone
- \+ *lemma* binary_cofan_inl_to_cocone
- \+ *lemma* binary_cofan_inr_to_cocone
- \+/\- *lemma* has_biproduct.of_has_product
- \+/\- *lemma* has_biproduct.of_has_coproduct
- \+ *lemma* inl_of_is_limit
- \+ *lemma* inr_of_is_limit
- \+ *lemma* fst_of_is_colimit
- \+ *lemma* snd_of_is_colimit
- \+/\- *lemma* has_biproduct.of_has_product
- \+/\- *lemma* has_biproduct.of_has_coproduct
- \+ *def* is_bilimit_of_total
- \+ *def* is_bilimit_of_is_limit
- \+ *def* bicone_is_bilimit_of_limit_cone_of_is_limit
- \+ *def* is_bilimit_of_is_colimit
- \+ *def* bicone_is_bilimit_of_colimit_cocone_of_is_colimit
- \+ *def* is_binary_bilimit_of_total
- \+ *def* binary_bicone.of_limit_cone
- \+ *def* is_binary_bilimit_of_is_limit
- \+ *def* binary_bicone_is_bilimit_of_limit_cone_of_is_limit
- \+ *def* binary_bicone.of_colimit_cocone
- \+ *def* is_binary_bilimit_of_is_colimit
- \+ *def* binary_bicone_is_bilimit_of_colimit_cocone_of_is_colimit



## [2022-02-26 20:55:44](https://github.com/leanprover-community/mathlib/commit/09ba530)
feat(category_theory/limits): biproducts are unique up to iso ([#12114](https://github.com/leanprover-community/mathlib/pull/12114))
#### Estimated changes
modified src/category_theory/limits/shapes/biproducts.lean
- \+ *lemma* biproduct.cone_point_unique_up_to_iso_hom
- \+ *lemma* biproduct.cone_point_unique_up_to_iso_inv
- \+ *lemma* biprod.cone_point_unique_up_to_iso_hom
- \+ *lemma* biprod.cone_point_unique_up_to_iso_inv
- \+ *def* biproduct.unique_up_to_iso
- \+ *def* biprod.unique_up_to_iso



## [2022-02-26 20:23:50](https://github.com/leanprover-community/mathlib/commit/fe6ea3e)
feat(analysis/convex/integral): strict Jensen's inequality ([#11552](https://github.com/leanprover-community/mathlib/pull/11552))
#### Estimated changes
modified src/analysis/convex/integral.lean
- \+ *lemma* measure_theory.integrable.ae_eq_const_or_exists_average_ne_compl
- \+ *lemma* convex.average_mem_interior_of_set
- \+ *lemma* strict_convex.ae_eq_const_or_average_mem_interior
- \+ *lemma* strict_convex_on.ae_eq_const_or_map_average_lt
- \+ *lemma* strict_concave_on.ae_eq_const_or_lt_map_average
- \+ *lemma* strict_convex.ae_eq_const_or_norm_integral_lt_of_norm_le_const



## [2022-02-26 19:39:04](https://github.com/leanprover-community/mathlib/commit/c8150cc)
feat(analysis/normed_space/add_torsor): `dist` and `line_map` ([#12265](https://github.com/leanprover-community/mathlib/pull/12265))
Add a few lemmas about the distance between `line_map p₁ p₂ c₁` and
`line_map p₁ p₂ c₂`.
#### Estimated changes
modified src/analysis/normed_space/add_torsor.lean
- \+ *lemma* dist_line_map_line_map
- \+ *lemma* lipschitz_with_line_map
- \+ *lemma* dist_line_map_left
- \+ *lemma* dist_left_line_map
- \+ *lemma* dist_line_map_right
- \+ *lemma* dist_right_line_map



## [2022-02-26 16:53:59](https://github.com/leanprover-community/mathlib/commit/3b49fe2)
feat(algebra/star/pointwise, algebra/star/basic): add pointwise star, and a few convenience lemmas ([#12290](https://github.com/leanprover-community/mathlib/pull/12290))
This adds a star operation to sets in the pointwise locale and establishes the basic properties. The names and proofs were taken from the corresponding ones for `inv`. A few extras were added.
#### Estimated changes
modified src/algebra/star/basic.lean
- \+ *lemma* eq_star_of_eq_star
- \+ *lemma* eq_star_iff_eq_star
- \+ *lemma* star_eq_iff_star_eq

created src/algebra/star/pointwise.lean
- \+ *lemma* star_empty
- \+ *lemma* star_univ
- \+ *lemma* nonempty_star
- \+ *lemma* nonempty.star
- \+ *lemma* mem_star
- \+ *lemma* star_mem_star
- \+ *lemma* star_preimage
- \+ *lemma* image_star
- \+ *lemma* inter_star
- \+ *lemma* union_star
- \+ *lemma* Inter_star
- \+ *lemma* Union_star
- \+ *lemma* compl_star
- \+ *lemma* star_subset_star
- \+ *lemma* star_subset
- \+ *lemma* finite.star
- \+ *lemma* star_singleton



## [2022-02-26 16:18:11](https://github.com/leanprover-community/mathlib/commit/87fc3ea)
feat(analysis/normed_space/star/spectrum): prove the spectrum of a unitary element in a C*-algebra is a subset of the unit sphere ([#12238](https://github.com/leanprover-community/mathlib/pull/12238))
The spectrum of a unitary element in a C*-algebra is a subset of the unit sphere in the scalar field. This will be used to show that the spectrum of selfadjoint elements is real-valued.
#### Estimated changes
modified src/analysis/normed_space/star/spectrum.lean
- \+ *lemma* unitary.spectrum_subset_circle
- \+ *lemma* spectrum.subset_circle_of_unitary



## [2022-02-26 13:23:26](https://github.com/leanprover-community/mathlib/commit/0f1bc2c)
feat(topology,analysis): any function is continuous/differentiable on a subsingleton ([#12293](https://github.com/leanprover-community/mathlib/pull/12293))
Also add supporting lemmas about `is_o`/`is_O` and the `pure` filter
and drop an unneeded assumption in `asymptotics.is_o_const_const_iff`.
#### Estimated changes
modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* is_O_pure
- \+ *lemma* is_o_pure
- \+ *theorem* is_O_with_pure
- \+ *theorem* is_O_const_const_iff
- \+/\- *theorem* is_o_const_const_iff
- \+/\- *theorem* is_o_const_const_iff

modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_fderiv_within_at_singleton
- \+/\- *lemma* has_fderiv_at_of_subsingleton
- \+ *lemma* differentiable_on_empty
- \+ *lemma* differentiable_on_singleton
- \+ *lemma* set.subsingleton.differentiable_on
- \+/\- *lemma* has_fderiv_at_of_subsingleton

modified src/analysis/calculus/fderiv_symmetric.lean

modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on_singleton
- \+ *lemma* set.subsingleton.continuous_on



## [2022-02-26 11:40:32](https://github.com/leanprover-community/mathlib/commit/bfc0584)
refactor(topology,analysis): use `maps_to` in lemmas like `continuous_on.comp` ([#12294](https://github.com/leanprover-community/mathlib/pull/12294))
#### Estimated changes
modified src/analysis/calculus/fderiv.lean

modified src/analysis/normed_space/basic.lean

modified src/data/set/function.lean
- \+/\- *theorem* maps_to.mono
- \+ *theorem* maps_to.mono_left
- \+ *theorem* maps_to.mono_right
- \+/\- *theorem* maps_to.mono

modified src/dynamics/omega_limit.lean

modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* continuous_on_symm

modified src/measure_theory/integral/divergence_theorem.lean

modified src/measure_theory/integral/interval_integral.lean

modified src/topology/continuous_on.lean

modified src/topology/fiber_bundle.lean



## [2022-02-26 11:03:49](https://github.com/leanprover-community/mathlib/commit/d2d6f17)
feat(analysis/inner_product_space/spectrum): `has_eigenvalue_eigenvalues` ([#12304](https://github.com/leanprover-community/mathlib/pull/12304))
similar to the existing `has_eigenvector_eigenvector_basis`
#### Estimated changes
modified src/analysis/inner_product_space/spectrum.lean
- \+ *lemma* has_eigenvalue_eigenvalues



## [2022-02-26 03:29:04](https://github.com/leanprover-community/mathlib/commit/d6a8e5d)
feat(topology/compact_open): `simp`-lemmas for `compact_open.gen` ([#12267](https://github.com/leanprover-community/mathlib/pull/12267))
This PR adds some basic `simp`-lemmas for `compact_open.gen`.
#### Estimated changes
modified src/topology/compact_open.lean
- \+ *lemma* gen_empty
- \+ *lemma* gen_univ
- \+ *lemma* gen_inter
- \+ *lemma* gen_union



## [2022-02-26 03:29:03](https://github.com/leanprover-community/mathlib/commit/7201c3b)
feat(category_theory/limits): more opposite-related transformations of cones ([#12165](https://github.com/leanprover-community/mathlib/pull/12165))
#### Estimated changes
modified src/category_theory/limits/cones.lean
- \+ *def* cone_of_cocone_right_op
- \+ *def* cocone_right_op_of_cone
- \+ *def* cocone_of_cone_right_op
- \+ *def* cone_right_op_of_cocone
- \+ *def* cone_of_cocone_unop
- \+ *def* cocone_unop_of_cone
- \+ *def* cocone_of_cone_unop
- \+ *def* cone_unop_of_cocone

modified src/category_theory/limits/opposites.lean

modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean



## [2022-02-26 02:44:14](https://github.com/leanprover-community/mathlib/commit/43fb516)
doc(analysis/normed_space): fixed normed_star_monoid doc-string ([#12296](https://github.com/leanprover-community/mathlib/pull/12296))
#### Estimated changes
modified src/analysis/normed_space/star/basic.lean



## [2022-02-25 22:23:16](https://github.com/leanprover-community/mathlib/commit/05d8188)
feat(group_theory/torsion): define torsion groups ([#11850](https://github.com/leanprover-community/mathlib/pull/11850))
I grepped for torsion group and didn't find anything -- hopefully adding this makes sense here.
#### Estimated changes
modified src/group_theory/exponent.lean
- \+ *lemma* exponent_exists_iff_ne_zero
- \+/\- *lemma* exponent_eq_zero_iff
- \+/\- *lemma* exponent_eq_zero_iff

modified src/group_theory/order_of_element.lean
- \+ *lemma* is_of_fin_order_iff_coe
- \+ *lemma* is_of_fin_order.quotient

created src/group_theory/torsion.lean
- \+ *lemma* is_torsion.subgroup
- \+ *lemma* is_torsion.quotient_group
- \+ *lemma* exponent_exists.is_torsion
- \+ *lemma* is_torsion.exponent_exists
- \+ *lemma* is_torsion_of_fintype
- \+ *def* is_torsion



## [2022-02-25 20:13:56](https://github.com/leanprover-community/mathlib/commit/3cc9ac4)
feat(analysis/normed_space/finite_dimension): add a lemma about `inf_dist` ([#12282](https://github.com/leanprover-community/mathlib/pull/12282))
Add a version of `exists_mem_frontier_inf_dist_compl_eq_dist` for a
compact set in a real normed space. This version does not assume that
the ambient space is finite dimensional.
#### Estimated changes
modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* is_compact.exists_mem_frontier_inf_dist_compl_eq_dist
- \+ *theorem* finite_dimensional_of_is_compact_closed_ball₀
- \+/\- *theorem* finite_dimensional_of_is_compact_closed_ball
- \+/\- *theorem* finite_dimensional_of_is_compact_closed_ball

modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* inf_dist_zero_of_mem_closure



## [2022-02-25 18:50:04](https://github.com/leanprover-community/mathlib/commit/c127fc3)
chore(measure_theory/decomposition/lebesgue): tidy a proof ([#12274](https://github.com/leanprover-community/mathlib/pull/12274))
There's no need to go through `set_integral_re_add_im` when all we need is `integral_re`.
#### Estimated changes
modified src/analysis/complex/basic.lean
- \+ *lemma* _root_.is_R_or_C.re_eq_complex_re
- \+ *lemma* _root_.is_R_or_C.im_eq_complex_im

modified src/measure_theory/decomposition/lebesgue.lean



## [2022-02-25 16:56:48](https://github.com/leanprover-community/mathlib/commit/6653544)
feat(topology/algebra/order/extr): extr on closure ([#12281](https://github.com/leanprover-community/mathlib/pull/12281))
Prove `is_max_on.closure` etc
#### Estimated changes
created src/topology/algebra/order/extr_closure.lean



## [2022-02-25 10:18:16](https://github.com/leanprover-community/mathlib/commit/8c485a4)
feat(order/filter/extr): add `is_*_on.comp_maps_to` ([#12280](https://github.com/leanprover-community/mathlib/pull/12280))
#### Estimated changes
modified src/order/filter/extr.lean
- \+ *lemma* is_min_on.comp_maps_to
- \+ *lemma* is_max_on.comp_maps_to
- \+ *lemma* is_extr_on.comp_maps_to



## [2022-02-25 07:39:47](https://github.com/leanprover-community/mathlib/commit/c1443d6)
feat(ring_theory/localization): random lemmata for edge cases ([#12146](https://github.com/leanprover-community/mathlib/pull/12146))
#### Estimated changes
modified src/logic/unique.lean
- \+ *lemma* unique.bijective

modified src/ring_theory/localization/basic.lean

modified src/ring_theory/localization/fraction_ring.lean



## [2022-02-25 07:07:50](https://github.com/leanprover-community/mathlib/commit/dae1dfe)
feat(topology/spectral/hom): Spectral maps ([#12228](https://github.com/leanprover-community/mathlib/pull/12228))
Define spectral maps in three ways:
* `is_spectral_map`, the unbundled predicate
* `spectral_map`, the bundled type
* `spectral_map_class`, the hom class
The design for `is_spectral_map` matches `continuous`. The design for `spectral_map` and `spectral_map_class` follows the hom refactor.
#### Estimated changes
created src/topology/spectral/hom.lean
- \+ *lemma* is_compact.preimage_of_open
- \+ *lemma* is_spectral_map.continuous
- \+ *lemma* is_spectral_map_id
- \+ *lemma* is_spectral_map.comp
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* coe_comp_continuous_map
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *def* to_continuous_map
- \+ *def* comp



## [2022-02-25 05:25:18](https://github.com/leanprover-community/mathlib/commit/f2fdef6)
feat(order/partition/equipartition): Equipartitions ([#12023](https://github.com/leanprover-community/mathlib/pull/12023))
Define `finpartition.is_equipartition`, a predicate for saying that the parts of a `finpartition` of a `finset` are all the same size up to a difference of `1`.
#### Estimated changes
modified src/data/set/basic.lean
- \+ *lemma* subsingleton_of_subset_singleton

modified src/data/set/equitable.lean
- \+/\- *lemma* equitable_on_iff_le_le_add_one
- \+ *lemma* equitable_on.le
- \+ *lemma* equitable_on.le_add_one
- \+/\- *lemma* equitable_on_iff
- \+/\- *lemma* equitable_on_iff_le_le_add_one
- \+/\- *lemma* equitable_on_iff

created src/order/partition/equipartition.lean
- \+ *lemma* is_equipartition_iff_card_parts_eq_average
- \+ *lemma* _root_.set.subsingleton.is_equipartition
- \+ *lemma* is_equipartition.average_le_card_part
- \+ *lemma* is_equipartition.card_part_le_average_add_one
- \+ *lemma* bot_is_equipartition
- \+ *lemma* top_is_equipartition
- \+ *lemma* indiscrete_is_equipartition
- \+ *def* is_equipartition

modified src/order/partition/finpartition.lean
- \+ *lemma* parts_top_subset
- \+ *lemma* parts_top_subsingleton



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
modified docs/references.bib

created src/algebra/symmetrized.lean
- \+ *lemma* unsym_sym
- \+ *lemma* sym_unsym
- \+ *lemma* sym_comp_unsym
- \+ *lemma* unsym_comp_sym
- \+ *lemma* sym_bijective
- \+ *lemma* unsym_bijective
- \+ *lemma* sym_injective
- \+ *lemma* sym_surjective
- \+ *lemma* unsym_injective
- \+ *lemma* unsym_surjective
- \+ *lemma* sym_inj
- \+ *lemma* unsym_inj
- \+ *lemma* sym_one
- \+ *lemma* unsym_one
- \+ *lemma* sym_add
- \+ *lemma* unsym_add
- \+ *lemma* sym_sub
- \+ *lemma* unsym_sub
- \+ *lemma* sym_neg
- \+ *lemma* unsym_neg
- \+ *lemma* mul_def
- \+ *lemma* unsym_mul
- \+ *lemma* sym_mul_sym
- \+ *lemma* sym_inv
- \+ *lemma* unsym_inv
- \+ *lemma* sym_smul
- \+ *lemma* unsym_smul
- \+ *lemma* unsym_eq_one_iff
- \+ *lemma* sym_eq_one_iff
- \+ *lemma* unsym_ne_one_iff
- \+ *lemma* sym_ne_one_iff
- \+ *lemma* inv_of_sym
- \+ *lemma* unsym_mul_self
- \+ *lemma* sym_mul_self
- \+ *lemma* mul_comm
- \+ *def* sym_alg
- \+ *def* sym
- \+ *def* unsym
- \+ *def* sym_equiv



## [2022-02-24 20:01:42](https://github.com/leanprover-community/mathlib/commit/f7518db)
chore(topology/continuous_function/bounded): add an is_central_scalar instance ([#12272](https://github.com/leanprover-community/mathlib/pull/12272))
This is only possible very recently now that `𝕜ᵐᵒᵖ` has a metric space instance.
#### Estimated changes
modified src/topology/continuous_function/bounded.lean



## [2022-02-24 20:01:41](https://github.com/leanprover-community/mathlib/commit/feb5473)
chore(*): update to 3.40.0c ([#12212](https://github.com/leanprover-community/mathlib/pull/12212))
#### Estimated changes
modified leanpkg.toml

modified src/analysis/asymptotics/asymptotic_equivalent.lean

modified src/combinatorics/configuration.lean



## [2022-02-24 18:24:37](https://github.com/leanprover-community/mathlib/commit/d3d3701)
feat(analysis/mean_inequalities): AM and GM are equal on a constant tuple ([#12179](https://github.com/leanprover-community/mathlib/pull/12179))
The converse is also true, but I have not gotten around to proving it.
#### Estimated changes
modified src/analysis/mean_inequalities.lean
- \+ *theorem* geom_mean_weighted_of_constant
- \+ *theorem* arith_mean_weighted_of_constant
- \+ *theorem* geom_mean_eq_arith_mean_weighted_of_constant

modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* rpow_add
- \+/\- *lemma* rpow_add'
- \+ *lemma* rpow_add_of_nonneg
- \+ *lemma* rpow_sum_of_pos
- \+ *lemma* rpow_sum_of_nonneg
- \+/\- *lemma* rpow_add
- \+/\- *lemma* rpow_add'

modified src/data/finset/basic.lean
- \+ *lemma* forall_mem_cons
- \+ *lemma* mem_of_mem_filter
- \+ *lemma* filter_nonempty_iff



## [2022-02-24 16:20:33](https://github.com/leanprover-community/mathlib/commit/d620395)
feat(topology/algebra/group): homeomorphisms for div ([#12251](https://github.com/leanprover-community/mathlib/pull/12251))
#### Estimated changes
modified src/topology/algebra/group.lean
- \+/\- *lemma* is_open_map_div_right
- \+/\- *lemma* is_closed_map_div_right
- \+/\- *lemma* is_open_map_div_right
- \+/\- *lemma* is_closed_map_div_right
- \+ *def* homeomorph.div_left
- \+ *def* homeomorph.div_right



## [2022-02-24 16:20:32](https://github.com/leanprover-community/mathlib/commit/ed9f73c)
feat(order/conditionally_complete_lattice.lean): two new lemmas ([#12250](https://github.com/leanprover-community/mathlib/pull/12250))
#### Estimated changes
modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* le_csupr_set
- \+ *lemma* cinfi_set_le



## [2022-02-24 14:39:01](https://github.com/leanprover-community/mathlib/commit/0840629)
test(instance_diamonds): verify that restrict_scalars produces no diamonds on the complex numbers ([#12273](https://github.com/leanprover-community/mathlib/pull/12273))
There is already a comment on `complex.module` that indicates an intentional solution to this diamond.
#### Estimated changes
modified test/instance_diamonds.lean



## [2022-02-24 14:38:59](https://github.com/leanprover-community/mathlib/commit/a0d2c43)
feat(algebra/punit_instances): mul_semiring_action ([#12271](https://github.com/leanprover-community/mathlib/pull/12271))
The timeouts mentioned in the file appear to no longer occur.
#### Estimated changes
modified src/algebra/punit_instances.lean



## [2022-02-24 14:38:57](https://github.com/leanprover-community/mathlib/commit/9dca6f4)
feat(topology/metric_space/lipschitz): add `set.maps_to` lemmas ([#12266](https://github.com/leanprover-community/mathlib/pull/12266))
#### Estimated changes
modified src/topology/metric_space/lipschitz.lean
- \+ *lemma* edist_le_mul_of_le
- \+ *lemma* edist_lt_mul_of_lt
- \+ *lemma* maps_to_emetric_closed_ball
- \+ *lemma* maps_to_emetric_ball
- \+/\- *lemma* nndist_le
- \+ *lemma* dist_le_mul_of_le
- \+ *lemma* maps_to_closed_ball
- \+ *lemma* dist_lt_mul_of_lt
- \+ *lemma* maps_to_ball
- \+/\- *lemma* bounded_image
- \+/\- *lemma* diam_image_le
- \+/\- *lemma* nndist_le
- \+/\- *lemma* bounded_image
- \+/\- *lemma* diam_image_le



## [2022-02-24 14:38:55](https://github.com/leanprover-community/mathlib/commit/d011bf2)
chore(measure_theory/function/uniform_integrable): replace `ℕ` by a type verifying enough assumptions ([#12242](https://github.com/leanprover-community/mathlib/pull/12242))
This PR does not generalize the results of the `uniform_integrable` file much, but using a generic type instead of `ℕ` makes clear where we need assumptions like `encodable`.
#### Estimated changes
modified src/measure_theory/function/uniform_integrable.lean
- \+/\- *lemma* mem_not_convergent_seq_iff
- \+/\- *lemma* not_convergent_seq_antitone
- \+/\- *lemma* measure_inter_not_convergent_seq_eq_zero
- \+/\- *lemma* not_convergent_seq_measurable_set
- \+/\- *lemma* measure_not_convergent_seq_tendsto_zero
- \+/\- *lemma* mem_not_convergent_seq_iff
- \+/\- *lemma* not_convergent_seq_antitone
- \+/\- *lemma* measure_inter_not_convergent_seq_eq_zero
- \+/\- *lemma* not_convergent_seq_measurable_set
- \+/\- *lemma* measure_not_convergent_seq_tendsto_zero
- \+/\- *def* not_convergent_seq
- \+/\- *def* not_convergent_seq



## [2022-02-24 14:38:54](https://github.com/leanprover-community/mathlib/commit/34cfcd0)
feat(probability/stopping): generalize `is_stopping_time.measurable_set_lt` and variants beyond `ℕ` ([#12240](https://github.com/leanprover-community/mathlib/pull/12240))
The lemma `is_stopping_time.measurable_set_lt` and the similar results for gt, ge and eq were written for stopping times with value in nat. We generalize those results to linear orders with the order topology.
#### Estimated changes
modified src/order/bounds.lean
- \+ *lemma* lub_Iio_le
- \+ *lemma* le_glb_Ioi
- \+ *lemma* lub_Iio_eq_self_or_Iio_eq_Iic
- \+ *lemma* glb_Ioi_eq_self_or_Ioi_eq_Ici
- \+ *lemma* exists_lub_Iio
- \+ *lemma* exists_glb_Ioi

modified src/probability/stopping.lean
- \+ *lemma* const_apply
- \+/\- *lemma* measurable_set_of_filtration
- \+/\- *lemma* is_stopping_time_const
- \+/\- *lemma* is_stopping_time.measurable_set_le
- \+ *lemma* is_stopping_time.measurable_set_lt_of_pred
- \+ *lemma* is_stopping_time.measurable_set_gt
- \+ *lemma* is_stopping_time.measurable_set_lt_of_is_lub
- \+/\- *lemma* is_stopping_time.measurable_set_lt
- \+/\- *lemma* is_stopping_time.measurable_set_ge
- \+/\- *lemma* is_stopping_time.measurable_set_eq
- \+/\- *lemma* is_stopping_time.measurable_set_eq_le
- \+/\- *lemma* is_stopping_time.measurable_set_lt_le
- \+/\- *lemma* is_stopping_time_of_measurable_set_eq
- \+/\- *lemma* add_const
- \+/\- *lemma* measurable_set_of_filtration
- \+/\- *lemma* is_stopping_time.measurable_set_le
- \+/\- *lemma* is_stopping_time.measurable_set_eq
- \+/\- *lemma* is_stopping_time.measurable_set_ge
- \+/\- *lemma* is_stopping_time.measurable_set_eq_le
- \+/\- *lemma* is_stopping_time.measurable_set_lt
- \+/\- *lemma* is_stopping_time.measurable_set_lt_le
- \+/\- *lemma* is_stopping_time_of_measurable_set_eq
- \+/\- *lemma* is_stopping_time_const
- \+/\- *lemma* add_const
- \+/\- *def* is_stopping_time
- \+/\- *def* is_stopping_time



## [2022-02-24 12:56:59](https://github.com/leanprover-community/mathlib/commit/79887c9)
feat(measure_theory/group/prod): generalize topological groups to measurable groups ([#11933](https://github.com/leanprover-community/mathlib/pull/11933))
* This fixes the gap in `[Halmos]` that I mentioned in `measure_theory.group.prod`
* Thanks to @sgouezel for giving me the proof to fill that gap.
* A text proof to fill the gap is [here](https://math.stackexchange.com/a/4387664/463377)
#### Estimated changes
modified src/algebra/indicator_function.lean
- \+ *lemma* mul_indicator_image

modified src/measure_theory/group/measure.lean

modified src/measure_theory/group/prod.lean
- \+/\- *lemma* measurable_measure_mul_right
- \+ *lemma* measure_mul_lintegral_eq
- \+ *lemma* absolutely_continuous_of_is_mul_left_invariant
- \+ *lemma* ae_measure_preimage_mul_right_lt_top
- \+ *lemma* ae_measure_preimage_mul_right_lt_top_of_ne_zero
- \+/\- *lemma* measure_lintegral_div_measure
- \+/\- *lemma* measure_mul_measure_eq
- \+ *lemma* measure_eq_div_smul
- \+/\- *lemma* measurable_measure_mul_right
- \+/\- *lemma* measure_lintegral_div_measure
- \+/\- *lemma* measure_mul_measure_eq

modified src/measure_theory/measure/haar.lean

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* _root_.measurable_equiv.sigma_finite_map
- \+ *lemma* ae_of_forall_measure_lt_top_ae_restrict'
- \+/\- *lemma* ae_of_forall_measure_lt_top_ae_restrict
- \+/\- *lemma* ae_of_forall_measure_lt_top_ae_restrict



## [2022-02-24 12:56:58](https://github.com/leanprover-community/mathlib/commit/8429ec9)
feat(topology/vector_bundle): `topological_vector_prebundle` ([#8154](https://github.com/leanprover-community/mathlib/pull/8154))
In this PR we implement a new standard construction for topological vector bundles: namely a structure that permits to define a vector bundle when trivializations are given as local equivalences but there is not yet a topology on the total space. The total space is hence given a topology in such a way that there is a vector bundle structure for which the local equivalences
are also local homeomorphism and hence local trivializations.
#### Estimated changes
modified src/data/bundle.lean
- \+/\- *def* proj
- \+/\- *def* proj

modified src/data/set/function.lean
- \+ *lemma* restrict_comp_cod_restrict

modified src/topology/constructions.lean
- \+ *lemma* inducing_coe
- \+ *lemma* inducing.of_cod_restrict
- \+ *lemma* continuous.cod_restrict

modified src/topology/fiber_bundle.lean

modified src/topology/local_homeomorph.lean
- \+ *lemma* continuous_iff_continuous_comp_left

modified src/topology/vector_bundle.lean
- \+ *lemma* mem_trivialization_at_source
- \+ *lemma* total_space_mk_preimage_source
- \+ *lemma* continuous_total_space_mk
- \+ *lemma* inducing_total_space_mk_of_inducing_comp
- \+ *lemma* to_topological_vector_bundle
- \+ *def* trivialization.to_pretrivialization
- \+ *def* to_topological_fiber_prebundle
- \+ *def* total_space_topology
- \+ *def* trivialization_at



## [2022-02-24 11:57:32](https://github.com/leanprover-community/mathlib/commit/76b1e01)
feat(data/equiv/option): option_congr ([#12263](https://github.com/leanprover-community/mathlib/pull/12263))
This is a universe-polymorphic version of the existing `equiv_functor.map_equiv option`.
#### Estimated changes
modified src/combinatorics/derangements/basic.lean

modified src/data/equiv/option.lean
- \+ *lemma* option_congr_refl
- \+ *lemma* option_congr_symm
- \+ *lemma* option_congr_trans
- \+ *lemma* option_congr_eq_equiv_function_map_equiv
- \+ *lemma* remove_none_option_congr
- \+ *lemma* option_congr_injective
- \- *lemma* remove_none_map_equiv
- \+ *def* option_congr

modified src/group_theory/perm/option.lean
- \+ *lemma* equiv.option_congr_one
- \+ *lemma* equiv.option_congr_swap
- \+ *lemma* equiv.option_congr_sign
- \- *lemma* equiv_functor.map_equiv_option_injective
- \- *lemma* equiv_functor.option.map_none
- \- *lemma* map_equiv_option_one
- \- *lemma* map_equiv_option_refl
- \- *lemma* map_equiv_option_swap
- \- *lemma* equiv_functor.option.sign



## [2022-02-24 11:57:31](https://github.com/leanprover-community/mathlib/commit/b8b1b57)
chore(geometry/euclidean): split repetitive proof ([#12209](https://github.com/leanprover-community/mathlib/pull/12209))
This PR is part of the subobject refactor [#11545](https://github.com/leanprover-community/mathlib/pull/11545), fixing a timeout caused by some expensive defeq checks.
I introduce a new definition `simplex.orthogonal_projection_span s := orthogonal_projection (affine_span ℝ (set.range s.points))`, and extract a couple of its properties from (repetitive) parts of proofs in `circumcenter.lean`, especially `eq_or_eq_reflection_of_dist_eq`. This makes the latter proof noticeably faster, especially after commit [#11750](https://github.com/leanprover-community/mathlib/pull/11750).
#### Estimated changes
modified src/geometry/euclidean/circumcenter.lean
- \+ *lemma* orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \+ *lemma* coe_orthogonal_projection_vadd_smul_vsub_orthogonal_projection
- \+ *lemma* dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq
- \+ *lemma* dist_circumcenter_sq_eq_sq_sub_circumradius
- \+ *def* orthogonal_projection_span



## [2022-02-24 10:42:14](https://github.com/leanprover-community/mathlib/commit/3d97cfb)
feat(ring_theory/ideal,dedekind_domain): lemmas on `I ≤ I^e` and `I < I^e` ([#12185](https://github.com/leanprover-community/mathlib/pull/12185))
#### Estimated changes
modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* ideal.strict_anti_pow
- \+ *lemma* ideal.pow_lt_self
- \+ *lemma* ideal.exists_mem_pow_not_mem_pow_succ

modified src/ring_theory/ideal/operations.lean
- \+ *lemma* pow_le_self



## [2022-02-24 08:26:23](https://github.com/leanprover-community/mathlib/commit/9eb78a3)
feat(measure_theory/function/ae_eq_fun): generalize scalar actions ([#12248](https://github.com/leanprover-community/mathlib/pull/12248))
This provides a more general `has_scalar` instance, along with `mul_action`, `distrib_mul_action`, `module`, `is_scalar_tower`, `smul_comm_class`, and `is_central_scalar` instances.
#### Estimated changes
modified src/measure_theory/function/ae_eq_fun.lean
- \+/\- *lemma* smul_mk
- \+/\- *lemma* coe_fn_smul
- \+/\- *lemma* smul_to_germ
- \+/\- *lemma* smul_mk
- \+/\- *lemma* coe_fn_smul
- \+/\- *lemma* smul_to_germ
- \+ *def* to_germ_monoid_hom



## [2022-02-24 04:27:02](https://github.com/leanprover-community/mathlib/commit/f6a7ad9)
feat(measure_theory/integral/average): define `measure_theory.average` ([#12128](https://github.com/leanprover-community/mathlib/pull/12128))
And use it to formulate Jensen's inequality. Also add Jensen's inequality for concave functions.
#### Estimated changes
modified src/analysis/convex/integral.lean
- \+/\- *lemma* convex.integral_mem
- \+ *lemma* convex.average_mem
- \+ *lemma* convex.set_average_mem
- \+ *lemma* convex_on.average_mem_epigraph
- \+ *lemma* concave_on.average_mem_hypograph
- \+ *lemma* convex_on.map_average_le
- \+ *lemma* concave_on.le_map_average
- \+ *lemma* convex_on.set_average_mem_epigraph
- \+ *lemma* concave_on.set_average_mem_hypograph
- \+ *lemma* convex_on.map_set_average_le
- \+ *lemma* concave_on.le_map_set_average
- \+ *lemma* concave_on.le_map_integral
- \- *lemma* convex.smul_integral_mem
- \+/\- *lemma* convex.integral_mem
- \- *lemma* convex_on.map_smul_integral_le

modified src/measure_theory/function/l1_space.lean
- \+ *lemma* integrable.to_average

created src/measure_theory/integral/average.lean
- \+ *lemma* average_zero
- \+ *lemma* average_zero_measure
- \+ *lemma* average_neg
- \+ *lemma* average_def
- \+ *lemma* average_def'
- \+ *lemma* average_eq_integral
- \+ *lemma* measure_smul_average
- \+ *lemma* set_average_eq
- \+ *lemma* average_congr
- \+ *lemma* average_add_measure
- \+ *lemma* average_pair
- \+ *lemma* measure_smul_set_average
- \+ *lemma* average_union
- \+ *lemma* average_union_mem_open_segment
- \+ *lemma* average_union_mem_segment
- \+ *lemma* average_mem_open_segment_compl_self

modified src/measure_theory/integral/bochner.lean
- \+ *lemma* tendsto_integral_approx_on_of_measurable

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* is_probability_measure_smul



## [2022-02-24 03:44:56](https://github.com/leanprover-community/mathlib/commit/f3ee462)
chore(category_theory/adjunction/opposites): Forgotten `category_theory` namespace ([#12256](https://github.com/leanprover-community/mathlib/pull/12256))
The forgotten `category_theory` namespace means that dot notation doesn't work on `category_theory.adjunction`.
#### Estimated changes
modified src/category_theory/adjunction/opposites.lean



## [2022-02-24 02:51:27](https://github.com/leanprover-community/mathlib/commit/ed55593)
feat(topology/metric_space/basic): add a few lemmas ([#12259](https://github.com/leanprover-community/mathlib/pull/12259))
Add `ne_of_mem_sphere`, `subsingleton_closed_ball`, and `metric.subsingleton_sphere`.
#### Estimated changes
modified src/topology/metric_space/basic.lean
- \+ *lemma* subsingleton_closed_ball
- \+ *lemma* subsingleton_sphere
- \+ *theorem* ne_of_mem_sphere



## [2022-02-24 01:18:43](https://github.com/leanprover-community/mathlib/commit/158550d)
feat(algebra/module/basic): add `smul_right_inj` ([#12252](https://github.com/leanprover-community/mathlib/pull/12252))
Also golf the proof of `smul_right_injective` by reusing
`add_monoid_hom.injective_iff`.
#### Estimated changes
modified src/algebra/module/basic.lean
- \+ *lemma* smul_right_inj



## [2022-02-24 01:18:42](https://github.com/leanprover-community/mathlib/commit/2939c77)
feat(topology/metric_space): multiplicative opposites inherit the same `(pseudo_?)(e?)metric` and `uniform_space` ([#12120](https://github.com/leanprover-community/mathlib/pull/12120))
This puts the "obvious" metric on the opposite type such that `dist (op x) (op y) = dist x y`.
This also merges `subtype.pseudo_dist_eq` and `subtype.dist_eq` as the latter was a special case of the former.
#### Estimated changes
modified src/measure_theory/function/simple_func_dense.lean

modified src/topology/metric_space/algebra.lean

modified src/topology/metric_space/basic.lean
- \+/\- *theorem* subtype.dist_eq
- \+ *theorem* subtype.nndist_eq
- \+ *theorem* dist_unop
- \+ *theorem* dist_op
- \+ *theorem* nndist_unop
- \+ *theorem* nndist_op
- \- *theorem* subtype.pseudo_dist_eq
- \+/\- *theorem* subtype.dist_eq

modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* edist_unop
- \+ *theorem* edist_op

modified src/topology/uniform_space/basic.lean
- \+ *lemma* uniformity_mul_opposite
- \+ *lemma* uniform_continuous_unop
- \+ *lemma* uniform_continuous_op



## [2022-02-24 00:25:00](https://github.com/leanprover-community/mathlib/commit/890338d)
feat(analysis/normed_space/basic): use weaker assumptions ([#12260](https://github.com/leanprover-community/mathlib/pull/12260))
Assume `r ≠ 0` instead of `0 < r` in `interior_closed_ball` and `frontier_closed_ball`.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+/\- *theorem* interior_closed_ball
- \+/\- *theorem* frontier_closed_ball
- \+/\- *theorem* interior_closed_ball
- \+/\- *theorem* frontier_closed_ball



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
modified src/analysis/normed_space/basic.lean

created src/topology/instances/int.lean
- \+ *lemma* pairwise_one_le_dist
- \+ *lemma* uniform_embedding_coe_real
- \+ *lemma* closed_embedding_coe_real
- \+ *lemma* cocompact_eq
- \+ *lemma* cofinite_eq
- \+ *theorem* dist_eq
- \+ *theorem* dist_cast_real
- \+ *theorem* preimage_ball
- \+ *theorem* preimage_closed_ball
- \+ *theorem* ball_eq_Ioo
- \+ *theorem* closed_ball_eq_Icc

created src/topology/instances/nat.lean
- \+ *lemma* dist_coe_int
- \+ *lemma* pairwise_one_le_dist
- \+ *lemma* uniform_embedding_coe_real
- \+ *lemma* closed_embedding_coe_real
- \+ *theorem* dist_eq
- \+ *theorem* dist_cast_real
- \+ *theorem* preimage_ball
- \+ *theorem* preimage_closed_ball
- \+ *theorem* closed_ball_eq_Icc

created src/topology/instances/rat.lean
- \+ *lemma* dist_cast
- \+ *lemma* nat.uniform_embedding_coe_rat
- \+ *lemma* nat.closed_embedding_coe_rat
- \+ *lemma* int.uniform_embedding_coe_rat
- \+ *lemma* int.closed_embedding_coe_rat
- \+ *lemma* rat.uniform_continuous_abs
- \+ *lemma* rat.continuous_mul
- \+ *lemma* rat.totally_bounded_Icc
- \+ *theorem* dist_eq
- \+ *theorem* uniform_continuous_coe_real
- \+ *theorem* uniform_embedding_coe_real
- \+ *theorem* dense_embedding_coe_real
- \+ *theorem* embedding_coe_real
- \+ *theorem* continuous_coe_real
- \+ *theorem* nat.dist_cast_rat
- \+ *theorem* int.dist_cast_rat
- \+ *theorem* rat.uniform_continuous_add
- \+ *theorem* rat.uniform_continuous_neg

modified src/topology/instances/real.lean
- \- *lemma* dist_cast
- \- *lemma* pairwise_one_le_dist
- \- *lemma* uniform_embedding_coe_rat
- \- *lemma* closed_embedding_coe_rat
- \- *lemma* uniform_embedding_coe_real
- \- *lemma* closed_embedding_coe_real
- \- *lemma* cocompact_eq
- \- *lemma* cofinite_eq
- \- *lemma* dist_coe_int
- \- *lemma* pairwise_one_le_dist
- \- *lemma* uniform_embedding_coe_rat
- \- *lemma* closed_embedding_coe_rat
- \- *lemma* uniform_embedding_coe_real
- \- *lemma* closed_embedding_coe_real
- \- *lemma* rat.uniform_continuous_abs
- \- *lemma* rat.continuous_mul
- \- *lemma* rat.totally_bounded_Icc
- \- *theorem* dist_eq
- \- *theorem* uniform_continuous_coe_real
- \- *theorem* uniform_embedding_coe_real
- \- *theorem* dense_embedding_coe_real
- \- *theorem* embedding_coe_real
- \- *theorem* continuous_coe_real
- \- *theorem* dist_eq
- \- *theorem* dist_cast_real
- \- *theorem* dist_cast_rat
- \- *theorem* preimage_ball
- \- *theorem* preimage_closed_ball
- \- *theorem* ball_eq_Ioo
- \- *theorem* closed_ball_eq_Icc
- \- *theorem* dist_eq
- \- *theorem* dist_cast_real
- \- *theorem* dist_cast_rat
- \- *theorem* preimage_ball
- \- *theorem* preimage_closed_ball
- \- *theorem* closed_ball_eq_Icc
- \- *theorem* rat.uniform_continuous_add
- \- *theorem* rat.uniform_continuous_neg

modified src/topology/instances/real_vector_space.lean

modified src/topology/uniform_space/compare_reals.lean



## [2022-02-23 22:56:45](https://github.com/leanprover-community/mathlib/commit/eae6ae3)
feat(algebra/associated): add decidable instances ([#12230](https://github.com/leanprover-community/mathlib/pull/12230))
Makes equality and divisibility decidable in `associates`, given that divisibility is decidable in the general case.
#### Estimated changes
modified src/algebra/associated.lean



## [2022-02-23 21:42:45](https://github.com/leanprover-community/mathlib/commit/2c74921)
feat(data/pfun): A new induction on pfun.fix ([#12109](https://github.com/leanprover-community/mathlib/pull/12109))
A new lemma that lets you prove predicates given `b ∈ f.fix a` if `f` preserves the predicate, and it holds for values which `f` maps to `b`.
#### Estimated changes
modified src/data/pfun.lean
- \+ *def* fix_induction'



## [2022-02-23 20:58:29](https://github.com/leanprover-community/mathlib/commit/9b333b2)
feat(topology/algebra/continuous_monoid_hom): `to_continuous_map` is a `closed_embedding` ([#12217](https://github.com/leanprover-community/mathlib/pull/12217))
This PR proves that `to_continuous_map : continuous_monoid_hom A B → C(A, B)` is a `closed_embedding`. This will be useful for showing that the Pontryagin dual is locally compact.
#### Estimated changes
modified src/topology/algebra/continuous_monoid_hom.lean
- \+ *lemma* is_closed_embedding



## [2022-02-23 17:43:01](https://github.com/leanprover-community/mathlib/commit/f04ad9a)
feat(analysis/normed_space/star/spectrum): prove the spectral radius of a selfadjoint element in a C*-algebra is its norm. ([#12211](https://github.com/leanprover-community/mathlib/pull/12211))
This establishes that the spectral radius of a selfadjoint element in a C*-algebra is its (nn)norm using the Gelfand formula for the spectral radius. The same theorem for normal elements can be proven using this once normal elements are defined in mathlib.
#### Estimated changes
modified src/analysis/normed_space/star/basic.lean
- \+ *lemma* nnnorm_star_mul_self
- \+ *lemma* nnnorm_pow_two_pow_of_self_adjoint
- \+ *lemma* self_adjoint.nnnorm_pow_two_pow

created src/analysis/normed_space/star/spectrum.lean
- \+ *lemma* spectral_radius_eq_nnnorm_of_self_adjoint
- \+ *lemma* self_adjoint.coe_spectral_radius_eq_nnnorm



## [2022-02-23 16:03:57](https://github.com/leanprover-community/mathlib/commit/b72cca4)
chore(geometry/manifold/algebra/smooth_functions): golf module instance ([#12247](https://github.com/leanprover-community/mathlib/pull/12247))
#### Estimated changes
modified src/geometry/manifold/algebra/smooth_functions.lean



## [2022-02-23 16:03:56](https://github.com/leanprover-community/mathlib/commit/3e2df83)
docs(order/order_iso_nat): Added note on `exists_increasing_or_nonincreasing_subseq` ([#12239](https://github.com/leanprover-community/mathlib/pull/12239))
#### Estimated changes
modified src/order/order_iso_nat.lean



## [2022-02-23 16:03:55](https://github.com/leanprover-community/mathlib/commit/162d060)
feat(measure_theory/function/strongly_measurable): more basic properties of `strongly_measurable` ([#12164](https://github.com/leanprover-community/mathlib/pull/12164))
#### Estimated changes
modified src/algebra/support.lean
- \+ *lemma* support_const_smul_of_ne_zero

modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* measurable_of_tendsto_ennreal'
- \+ *lemma* measurable_of_tendsto_ennreal
- \+/\- *lemma* measurable_of_tendsto_nnreal'
- \+/\- *lemma* measurable_of_tendsto_nnreal'

modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* simple_func.strongly_measurable
- \+ *lemma* strongly_measurable_const
- \+ *lemma* strongly_measurable_id
- \+ *lemma* fin_strongly_measurable_zero
- \+/\- *lemma* ae_fin_strongly_measurable
- \+/\- *lemma* exists_set_sigma_finite
- \+ *lemma* ae_fin_strongly_measurable_zero
- \+ *lemma* fin_strongly_measurable_mk
- \+ *lemma* ae_eq_mk
- \+/\- *lemma* ae_fin_strongly_measurable
- \+/\- *lemma* exists_set_sigma_finite
- \+/\- *def* approx
- \+/\- *def* approx

modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf



## [2022-02-23 16:03:54](https://github.com/leanprover-community/mathlib/commit/3fe20d4)
feat(ring_theory/localization): add mk' lemmas ([#12081](https://github.com/leanprover-community/mathlib/pull/12081))
#### Estimated changes
modified src/field_theory/ratfunc.lean

modified src/ring_theory/localization/basic.lean
- \+ *lemma* mk'_zero
- \+ *lemma* ne_zero_of_mk'_ne_zero

modified src/ring_theory/localization/fraction_ring.lean
- \+ *lemma* mk'_eq_zero_iff_eq_zero
- \+ *lemma* mk'_eq_one_iff_eq



## [2022-02-23 14:40:03](https://github.com/leanprover-community/mathlib/commit/0d5bed0)
feat(ring_theory/graded_algebra): definitions and basic operations of homogeneous ideal ([#10784](https://github.com/leanprover-community/mathlib/pull/10784))
This defines homogeneous ideals (`homogeneous_ideal`) of a graded algebra.
#### Estimated changes
modified src/algebra/graded_monoid.lean
- \+ *lemma* set_like.is_homogeneous_coe

created src/ring_theory/graded_algebra/homogeneous_ideal.lean
- \+ *lemma* ideal.homogeneous_core'_mono
- \+ *lemma* ideal.homogeneous_core'_le
- \+ *lemma* ideal.is_homogeneous_iff_forall_subset
- \+ *lemma* ideal.is_homogeneous_iff_subset_Inter
- \+ *lemma* ideal.mul_homogeneous_element_mem_of_mem
- \+ *lemma* ideal.is_homogeneous_span
- \+ *lemma* ideal.homogeneous_core_mono
- \+ *lemma* ideal.coe_homogeneous_core_le
- \+ *lemma* ideal.is_homogeneous.coe_homogeneous_core_eq_self
- \+ *lemma* homogeneous_ideal.homogeneous_core_coe_eq_self
- \+ *lemma* ideal.is_homogeneous.iff_eq
- \+ *lemma* ideal.is_homogeneous.iff_exists
- \+ *lemma* bot
- \+ *lemma* top
- \+ *lemma* inf
- \+ *lemma* Inf
- \+ *lemma* sup
- \+ *lemma* Sup
- \+ *lemma* coe_bot
- \+ *lemma* eq_bot_iff
- \+ *lemma* coe_top
- \+ *lemma* eq_top_iff
- \+ *lemma* coe_inf
- \+ *lemma* coe_Inf
- \+ *lemma* coe_infi
- \+ *lemma* coe_sup
- \+ *lemma* coe_Sup
- \+ *lemma* coe_supr
- \+ *lemma* coe_add
- \+ *lemma* ideal.is_homogeneous.mul
- \+ *lemma* homogeneous_ideal.coe_mul
- \+ *lemma* ideal.homogeneous_core.gc
- \+ *lemma* ideal.homogeneous_core_eq_Sup
- \+ *lemma* ideal.homogeneous_core'_eq_Sup
- \+ *lemma* ideal.le_coe_homogeneous_hull
- \+ *lemma* ideal.homogeneous_hull_mono
- \+ *lemma* ideal.is_homogeneous.homogeneous_hull_eq_self
- \+ *lemma* homogeneous_ideal.homogeneous_hull_coe_eq_self
- \+ *lemma* ideal.coe_homogeneous_hull_eq_supr
- \+ *lemma* ideal.homogeneous_hull_eq_supr
- \+ *lemma* ideal.homogeneous_hull.gc
- \+ *lemma* ideal.homogeneous_hull_eq_Inf
- \+ *def* ideal.is_homogeneous
- \+ *def* ideal.homogeneous_core'
- \+ *def* ideal.homogeneous_core
- \+ *def* ideal.homogeneous_core.gi
- \+ *def* ideal.homogeneous_hull
- \+ *def* ideal.homogeneous_hull.gi

modified src/ring_theory/ideal/basic.lean
- \+ *lemma* sum_mem
- \+ *lemma* span_empty
- \+ *lemma* span_univ
- \+ *lemma* span_union
- \+ *lemma* span_Union
- \+ *lemma* mem_span



## [2022-02-23 13:18:22](https://github.com/leanprover-community/mathlib/commit/e167efa)
chore(topology/instances/rat): rename to rat_lemmas ([#12246](https://github.com/leanprover-community/mathlib/pull/12246))
This is to make room for the changes in [#12207](https://github.com/leanprover-community/mathlib/pull/12207), which claim `topology.instances.rat` for more basic results. This has to be in a separate commit to keep the history reasonable.
#### Estimated changes
renamed src/topology/instances/rat.lean to src/topology/instances/rat_lemmas.lean



## [2022-02-23 13:18:20](https://github.com/leanprover-community/mathlib/commit/c526789)
feat(set_theory/ordinal_arithmetic): `is_normal.eq_iff_zero_and_succ` ([#12222](https://github.com/leanprover-community/mathlib/pull/12222))
Two normal functions are equal iff they're equal at `0` and successor ordinals. This is used for a few lemmas in [#12202](https://github.com/leanprover-community/mathlib/pull/12202).
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* is_normal.eq_iff_zero_and_succ



## [2022-02-23 13:18:19](https://github.com/leanprover-community/mathlib/commit/7de8137)
feat(topology/order/hom): Continuous order homomorphisms ([#12012](https://github.com/leanprover-community/mathlib/pull/12012))
Define continuous monotone functions, aka continuous order homomorphisms, aka Priestley homomorphisms, with notation `α →Co β`.
#### Estimated changes
modified src/topology/continuous_function/basic.lean

created src/topology/order/hom/basic.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *def* to_continuous_map
- \+ *def* comp



## [2022-02-23 12:32:53](https://github.com/leanprover-community/mathlib/commit/b0fbd91)
feat(measure_theory/measure): generalize scalar actions ([#12187](https://github.com/leanprover-community/mathlib/pull/12187))
As a result of this change, many smul lemmas now also apply to `nat` and `nnreal`, which allows some lemmas to be removed.
#### Estimated changes
modified src/measure_theory/covering/differentiation.lean

modified src/measure_theory/decomposition/lebesgue.lean

modified src/measure_theory/integral/set_to_l1.lean

modified src/measure_theory/measure/haar.lean

modified src/measure_theory/measure/hausdorff.lean

modified src/measure_theory/measure/lebesgue.lean

modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* ae_smul_measure
- \+/\- *lemma* smul_measure
- \+/\- *lemma* ae_smul_measure
- \+/\- *lemma* smul_measure
- \+/\- *theorem* smul_to_outer_measure
- \+/\- *theorem* coe_smul
- \+/\- *theorem* smul_apply
- \+/\- *theorem* smul_to_outer_measure
- \+/\- *theorem* coe_smul
- \+/\- *theorem* smul_apply
- \- *theorem* coe_nnreal_smul

modified src/measure_theory/measure/outer_measure.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *theorem* smul_supr
- \+/\- *theorem* trim_smul
- \+/\- *theorem* smul_supr
- \+/\- *theorem* trim_smul
- \+ *def* coe_fn_add_monoid_hom

modified src/measure_theory/measure/regular.lean

modified src/measure_theory/measure/vector_measure.lean

modified src/probability/independence.lean



## [2022-02-23 12:32:52](https://github.com/leanprover-community/mathlib/commit/d01b55f)
split(analysis/functional/gauge): Split off `analysis.seminorm` ([#12054](https://github.com/leanprover-community/mathlib/pull/12054))
Move the Minkowski functional to a new file `analysis.convex.gauge`.
#### Estimated changes
created src/analysis/convex/gauge.lean
- \+ *lemma* gauge_def
- \+ *lemma* gauge_def'
- \+ *lemma* absorbent.gauge_set_nonempty
- \+ *lemma* gauge_mono
- \+ *lemma* exists_lt_of_gauge_lt
- \+ *lemma* gauge_zero
- \+ *lemma* gauge_zero'
- \+ *lemma* gauge_empty
- \+ *lemma* gauge_of_subset_zero
- \+ *lemma* gauge_nonneg
- \+ *lemma* gauge_neg
- \+ *lemma* gauge_le_of_mem
- \+ *lemma* gauge_le_eq
- \+ *lemma* gauge_lt_eq'
- \+ *lemma* gauge_lt_eq
- \+ *lemma* gauge_lt_one_subset_self
- \+ *lemma* gauge_le_one_of_mem
- \+ *lemma* self_subset_gauge_le_one
- \+ *lemma* convex.gauge_le
- \+ *lemma* balanced.star_convex
- \+ *lemma* le_gauge_of_not_mem
- \+ *lemma* one_le_gauge_of_not_mem
- \+ *lemma* gauge_smul_of_nonneg
- \+ *lemma* gauge_smul
- \+ *lemma* gauge_smul_left_of_nonneg
- \+ *lemma* gauge_smul_left
- \+ *lemma* interior_subset_gauge_lt_one
- \+ *lemma* gauge_lt_one_eq_self_of_open
- \+ *lemma* gauge_lt_one_of_mem_of_open
- \+ *lemma* gauge_lt_of_mem_smul
- \+ *lemma* gauge_add_le
- \+ *lemma* gauge_seminorm_lt_one_of_open
- \+ *lemma* seminorm.gauge_seminorm_ball
- \+ *lemma* gauge_unit_ball
- \+ *lemma* smul_unit_ball
- \+ *lemma* gauge_ball
- \+ *lemma* mul_gauge_le_norm
- \+ *def* gauge
- \+ *def* gauge_seminorm

modified src/analysis/seminorm.lean
- \- *lemma* gauge_def
- \- *lemma* gauge_def'
- \- *lemma* absorbent.gauge_set_nonempty
- \- *lemma* gauge_mono
- \- *lemma* exists_lt_of_gauge_lt
- \- *lemma* gauge_zero
- \- *lemma* gauge_zero'
- \- *lemma* gauge_empty
- \- *lemma* gauge_of_subset_zero
- \- *lemma* gauge_nonneg
- \- *lemma* gauge_neg
- \- *lemma* gauge_le_of_mem
- \- *lemma* gauge_le_eq
- \- *lemma* gauge_lt_eq'
- \- *lemma* gauge_lt_eq
- \- *lemma* gauge_lt_one_subset_self
- \- *lemma* gauge_le_one_of_mem
- \- *lemma* self_subset_gauge_le_one
- \- *lemma* convex.gauge_le
- \- *lemma* balanced.star_convex
- \- *lemma* le_gauge_of_not_mem
- \- *lemma* one_le_gauge_of_not_mem
- \- *lemma* gauge_smul_of_nonneg
- \- *lemma* gauge_smul
- \- *lemma* gauge_smul_left_of_nonneg
- \- *lemma* gauge_smul_left
- \- *lemma* interior_subset_gauge_lt_one
- \- *lemma* gauge_lt_one_eq_self_of_open
- \- *lemma* gauge_lt_one_of_mem_of_open
- \- *lemma* gauge_lt_of_mem_smul
- \- *lemma* gauge_add_le
- \- *lemma* gauge_seminorm_lt_one_of_open
- \- *lemma* seminorm.gauge_seminorm_ball
- \- *lemma* gauge_unit_ball
- \- *lemma* smul_unit_ball
- \- *lemma* gauge_ball
- \- *lemma* mul_gauge_le_norm
- \- *def* gauge
- \- *def* gauge_seminorm



## [2022-02-23 10:50:57](https://github.com/leanprover-community/mathlib/commit/6179707)
feat(ring_theory/unique_factorization_domain): add count_self ([#12074](https://github.com/leanprover-community/mathlib/pull/12074))
#### Estimated changes
modified src/data/multiset/basic.lean
- \+/\- *theorem* count_singleton_self
- \+/\- *theorem* count_singleton_self

modified src/ring_theory/unique_factorization_domain.lean
- \+ *theorem* factors_self
- \+ *theorem* count_self



## [2022-02-23 10:50:56](https://github.com/leanprover-community/mathlib/commit/6f1d90d)
feat(algebra/order/monoid_lemmas_gt_zero): introduce the type of positive elements and prove some lemmas ([#11833](https://github.com/leanprover-community/mathlib/pull/11833))
This PR continues the `order` refactor.  Here I start working with the type of positive elements of a type with zero and lt.  Combining `covariant_` and `contravariant_classes` where the "acting" type is the type of positive elements, we can formulate the condition that "multiplication by positive elements is monotone" and variants.
I also prove some initial lemmas, just to give a flavour of the API.
More such lemmas will come in subsequent PRs (see for instance [#11782](https://github.com/leanprover-community/mathlib/pull/11782) for a few more lemmas).  After that, I will start simplifying existing lemmas, by weakening their assumptions.
#### Estimated changes
created src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* mul_lt_mul_left'
- \+ *lemma* mul_lt_mul_right'
- \+ *lemma* lt_of_mul_lt_mul_left'
- \+ *lemma* lt_of_mul_lt_mul_right'
- \+ *lemma* mul_lt_mul_iff_left
- \+ *lemma* mul_lt_mul_iff_right



## [2022-02-23 09:39:52](https://github.com/leanprover-community/mathlib/commit/3e77124)
refactor(topology/{separation,subset_properties}): use `set.subsingleton` ([#12232](https://github.com/leanprover-community/mathlib/pull/12232))
Use `set.subsingleton s` instead of `_root_.subsingleton s` in `is_preirreducible_iff_subsingleton` and `is_preirreducible_of_subsingleton`, rename the latter to `set.subsingleton.is_preirreducible`.
#### Estimated changes
modified src/topology/separation.lean

modified src/topology/sober.lean

modified src/topology/subset_properties.lean
- \+ *lemma* set.subsingleton.is_preirreducible
- \- *lemma* is_preirreducible_of_subsingleton



## [2022-02-23 09:39:50](https://github.com/leanprover-community/mathlib/commit/dc9b8be)
feat(analysis/normed_space/linear_isometry): add lemmas to `linear_isometry_equiv` ([#12218](https://github.com/leanprover-community/mathlib/pull/12218))
Added two API lemmas to `linear_isometry_equiv` that I need elsewhere.
#### Estimated changes
modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* trans_apply



## [2022-02-23 09:39:49](https://github.com/leanprover-community/mathlib/commit/f44ed74)
feat(ring_theory/ideal/over): `S/p` is noetherian over `R/p` if `S` is over `R` ([#12183](https://github.com/leanprover-community/mathlib/pull/12183))
#### Estimated changes
modified src/ring_theory/ideal/over.lean

modified src/ring_theory/ideal/quotient.lean
- \+ *lemma* subsingleton_iff



## [2022-02-23 08:16:08](https://github.com/leanprover-community/mathlib/commit/515eefa)
fix(algebra/star/basic): more type classes that should be props ([#12235](https://github.com/leanprover-community/mathlib/pull/12235))
#### Estimated changes
modified src/algebra/star/basic.lean



## [2022-02-23 08:16:07](https://github.com/leanprover-community/mathlib/commit/98bcabb)
feat(group_theory/perm): add lemmas for cycles of permutations ([#11955](https://github.com/leanprover-community/mathlib/pull/11955))
`nodup_powers_of_cycle_of` : shows that the the iterates of an element in the support give rise to a nodup list
`cycle_is_cycle_of` : asserts that a given cycle c in `f. cycle_factors_finset` is `f.cycle_of a` if c a \neq a
`equiv.perm.sign_of_cycle_type` : new formula for the sign of a permutations in terms of its cycle_type — It is simpler to use (just uses number of cycles and size of support) than the earlier lemma which is renamed as equiv.perm.sign_of_cycle_type'  (it could be deleted). I made one modification to make the file compile, but I need to check compatibility with the other ones.
#### Estimated changes
modified src/group_theory/perm/cycle_type.lean
- \+ *lemma* sign_of_cycle_type'
- \+/\- *lemma* sign_of_cycle_type
- \+/\- *lemma* sign_of_cycle_type

modified src/group_theory/perm/cycles.lean
- \+ *lemma* is_cycle_cycle_of_iff
- \+ *lemma* cycle_is_cycle_of

modified src/group_theory/specific_groups/alternating.lean



## [2022-02-23 07:46:35](https://github.com/leanprover-community/mathlib/commit/0eed60e)
feat(number_theory/cyclotomic/discriminant): discriminant of a p-th cyclotomic field ([#11804](https://github.com/leanprover-community/mathlib/pull/11804))
We compute the discriminant of a p-th cyclotomic field.
From flt-regular.
- [x] depends on: [#11786](https://github.com/leanprover-community/mathlib/pull/11786)
#### Estimated changes
created src/number_theory/cyclotomic/discriminant.lean
- \+ *lemma* discr_odd_prime

modified src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* sub_one_norm_is_prime_pow
- \+ *lemma* prime_ne_two_pow_sub_one_norm
- \+ *lemma* sub_one_norm_prime
- \+ *lemma* sub_one_norm_pow_two
- \+ *lemma* is_prime_pow_norm_zeta_sub_one
- \+ *lemma* prime_ne_two_pow_norm_zeta_sub_one
- \+ *lemma* prime_ne_two_norm_zeta_sub_one
- \+ *lemma* two_pow_norm_zeta_sub_one
- \- *lemma* sub_one_norm.is_prime_pow
- \- *lemma* prime_ne_two_pow.sub_one_norm
- \- *lemma* sub_one_norm.prime
- \- *lemma* sub_one_norm.pow_two
- \- *lemma* is_prime_pow.norm_zeta_sub_one
- \- *lemma* prime_ne_two_pow.norm_zeta_sub_one
- \- *lemma* prime_ne_two.norm_zeta_sub_one
- \- *lemma* two_pow.norm_zeta_sub_one

modified src/ring_theory/discriminant.lean
- \+ *lemma* discr_power_basis_eq_prod'
- \+ *lemma* discr_power_basis_eq_prod''
- \+ *lemma* discr_power_basis_eq_norm
- \- *lemma* of_power_basis_eq_prod'
- \- *lemma* of_power_basis_eq_prod''
- \- *lemma* of_power_basis_eq_norm

modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* cyclotomic_prime_pow_mul_X_pow_sub_one



## [2022-02-23 05:24:19](https://github.com/leanprover-community/mathlib/commit/257bddf)
feat(algebra/algebra/spectrum): add spectral mapping for inverses ([#12219](https://github.com/leanprover-community/mathlib/pull/12219))
Given a unit `a` in an algebra `A` over a field `𝕜`, the equality `(spectrum 𝕜 a)⁻¹ = spectrum 𝕜 a⁻¹` holds.
#### Estimated changes
modified src/algebra/algebra/spectrum.lean
- \+ *lemma* inv_mem_resolvent_set
- \+ *lemma* inv_mem_iff
- \+ *lemma* zero_mem_resolvent_set_of_unit
- \+ *lemma* ne_zero_of_mem_of_unit



## [2022-02-23 04:31:26](https://github.com/leanprover-community/mathlib/commit/e77675d)
fix(analysis/normed_space/star/basic): make prop type classes props ([#12233](https://github.com/leanprover-community/mathlib/pull/12233))
The type classes `normed_star_monoid` and `cstar_ring` are now properly declared as prop.
#### Estimated changes
modified src/analysis/normed_space/star/basic.lean



## [2022-02-23 04:01:36](https://github.com/leanprover-community/mathlib/commit/264dd7f)
feat(model_theory/basic): Language operations ([#12129](https://github.com/leanprover-community/mathlib/pull/12129))
Defines language homomorphisms with `first_order.language.Lhom`
Defines the sum of two languages with `first_order.language.sum`
Defines `first_order.language.with_constants`, a language with added constants, abbreviated `L[[A]]`.
Defines a `L[[A]].Structure` on `M` when `A : set M`.
(Some of this code comes from the Flypitch project)
#### Estimated changes
modified src/model_theory/basic.lean
- \+ *lemma* fun_map_eq_coe_constants
- \+/\- *lemma* nonempty_of_nonempty_constants
- \+ *lemma* map_constants
- \+ *lemma* map_constants
- \+ *lemma* map_constants
- \+ *lemma* fun_map_sum_inl
- \+ *lemma* fun_map_sum_inr
- \+ *lemma* rel_map_sum_inl
- \+ *lemma* rel_map_sum_inr
- \+ *lemma* id_comp
- \+ *lemma* comp_id
- \+ *lemma* constants_on_constants
- \+ *lemma* constants_on_map_is_expansion_on
- \+ *lemma* Lhom.map_constants_comp_with_constants
- \- *lemma* fun_map_eq_coe_const
- \+/\- *lemma* nonempty_of_nonempty_constants
- \- *lemma* map_const
- \- *lemma* map_const
- \- *lemma* map_const
- \+ *def* symbols
- \+ *def* comp
- \+ *def* sum_elim
- \+ *def* sum_map
- \+ *def* constants_on_functions
- \+ *def* constants_on
- \+ *def* constants_on.Structure
- \+ *def* Lhom.constants_on_map
- \+ *def* with_constants
- \+ *def* Lhom_with_constants
- \+ *def* Lhom.add_constants
- \+ *def* Lhom_trim_empty_constants
- \+ *def* Lhom_with_constants_map
- \- *def* const

modified src/model_theory/elementary_maps.lean
- \+ *lemma* map_constants
- \- *lemma* map_const

modified src/model_theory/substructures.lean
- \+ *lemma* constants_mem
- \- *lemma* const_mem

modified src/model_theory/terms_and_formulas.lean



## [2022-02-23 00:45:57](https://github.com/leanprover-community/mathlib/commit/7cc4eb9)
doc(number_theory/padics/*): typo in references ([#12229](https://github.com/leanprover-community/mathlib/pull/12229))
Fix typos in a reference.
#### Estimated changes
modified src/number_theory/padics/padic_integers.lean

modified src/number_theory/padics/padic_norm.lean

modified src/number_theory/padics/padic_numbers.lean



## [2022-02-23 00:45:56](https://github.com/leanprover-community/mathlib/commit/4238868)
chore(analysis): rename times_cont_diff ([#12227](https://github.com/leanprover-community/mathlib/pull/12227))
This replaces `times_cont_diff` by `cont_diff` everywhere, and the same for `times_cont_mdiff`. There is no change at all in content.
See https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/times_cont_diff.20name
#### Estimated changes
modified docs/overview.yaml

modified docs/undergrad.yaml

modified src/algebra/group/to_additive.lean

modified src/analysis/calculus/affine_map.lean
- \+ *lemma* cont_diff
- \- *lemma* times_cont_diff

renamed src/analysis/calculus/times_cont_diff.lean to src/analysis/calculus/cont_diff.lean
- \+ *lemma* cont_diff_within_at_nat
- \+ *lemma* cont_diff_within_at.of_le
- \+ *lemma* cont_diff_within_at_iff_forall_nat_le
- \+ *lemma* cont_diff_within_at_top
- \+ *lemma* cont_diff_within_at.continuous_within_at
- \+ *lemma* cont_diff_within_at.congr_of_eventually_eq
- \+ *lemma* cont_diff_within_at.congr_of_eventually_eq'
- \+ *lemma* filter.eventually_eq.cont_diff_within_at_iff
- \+ *lemma* cont_diff_within_at.congr
- \+ *lemma* cont_diff_within_at.congr'
- \+ *lemma* cont_diff_within_at.mono_of_mem
- \+ *lemma* cont_diff_within_at.mono
- \+ *lemma* cont_diff_within_at.congr_nhds
- \+ *lemma* cont_diff_within_at_congr_nhds
- \+ *lemma* cont_diff_within_at_inter'
- \+ *lemma* cont_diff_within_at_inter
- \+ *lemma* cont_diff_within_at.differentiable_within_at'
- \+ *lemma* cont_diff_within_at.differentiable_within_at
- \+ *lemma* cont_diff_on.cont_diff_within_at
- \+ *lemma* cont_diff_within_at.cont_diff_on
- \+ *lemma* cont_diff_on.of_le
- \+ *lemma* cont_diff_on_iff_forall_nat_le
- \+ *lemma* cont_diff_on_top
- \+ *lemma* cont_diff_on_all_iff_nat
- \+ *lemma* cont_diff_on.continuous_on
- \+ *lemma* cont_diff_on.congr
- \+ *lemma* cont_diff_on_congr
- \+ *lemma* cont_diff_on.mono
- \+ *lemma* cont_diff_on.congr_mono
- \+ *lemma* cont_diff_on.differentiable_on
- \+ *lemma* cont_diff_on_of_locally_cont_diff_on
- \+ *lemma* cont_diff_on_zero
- \+ *lemma* cont_diff_within_at_zero
- \+ *lemma* cont_diff_on_of_continuous_on_differentiable_on
- \+ *lemma* cont_diff_on_of_differentiable_on
- \+ *lemma* cont_diff_on.continuous_on_iterated_fderiv_within
- \+ *lemma* cont_diff_on.differentiable_on_iterated_fderiv_within
- \+ *lemma* cont_diff_on_iff_continuous_on_differentiable_on
- \+ *lemma* cont_diff_on.fderiv_within
- \+ *lemma* cont_diff_on.fderiv_of_open
- \+ *lemma* cont_diff_on.continuous_on_fderiv_within
- \+ *lemma* cont_diff_on.continuous_on_fderiv_of_open
- \+ *lemma* cont_diff_on.continuous_on_fderiv_within_apply
- \+ *lemma* cont_diff_at_top
- \+ *lemma* cont_diff_at.cont_diff_within_at
- \+ *lemma* cont_diff_within_at.cont_diff_at
- \+ *lemma* cont_diff_at.congr_of_eventually_eq
- \+ *lemma* cont_diff_at.of_le
- \+ *lemma* cont_diff_at.continuous_at
- \+ *lemma* cont_diff_at.differentiable_at
- \+ *lemma* cont_diff_iff_cont_diff_at
- \+ *lemma* cont_diff.cont_diff_at
- \+ *lemma* cont_diff.cont_diff_within_at
- \+ *lemma* cont_diff_top
- \+ *lemma* cont_diff_all_iff_nat
- \+ *lemma* cont_diff.cont_diff_on
- \+ *lemma* cont_diff_zero
- \+ *lemma* cont_diff_at_zero
- \+ *lemma* cont_diff.of_le
- \+ *lemma* cont_diff.continuous
- \+ *lemma* cont_diff.differentiable
- \+ *lemma* cont_diff_iff_continuous_differentiable
- \+ *lemma* cont_diff_of_differentiable_iterated_fderiv
- \+ *lemma* cont_diff.continuous_fderiv
- \+ *lemma* cont_diff.continuous_fderiv_apply
- \+ *lemma* cont_diff_zero_fun
- \+ *lemma* cont_diff_const
- \+ *lemma* cont_diff_on_const
- \+ *lemma* cont_diff_at_const
- \+ *lemma* cont_diff_within_at_const
- \+ *lemma* cont_diff_of_subsingleton
- \+ *lemma* cont_diff_at_of_subsingleton
- \+ *lemma* cont_diff_within_at_of_subsingleton
- \+ *lemma* cont_diff_on_of_subsingleton
- \+ *lemma* is_bounded_linear_map.cont_diff
- \+ *lemma* continuous_linear_map.cont_diff
- \+ *lemma* continuous_linear_equiv.cont_diff
- \+ *lemma* linear_isometry.cont_diff
- \+ *lemma* linear_isometry_equiv.cont_diff
- \+ *lemma* cont_diff_fst
- \+ *lemma* cont_diff_on_fst
- \+ *lemma* cont_diff_at_fst
- \+ *lemma* cont_diff_within_at_fst
- \+ *lemma* cont_diff_snd
- \+ *lemma* cont_diff_on_snd
- \+ *lemma* cont_diff_at_snd
- \+ *lemma* cont_diff_within_at_snd
- \+ *lemma* cont_diff_prod_assoc
- \+ *lemma* cont_diff_prod_assoc_symm
- \+ *lemma* cont_diff_id
- \+ *lemma* cont_diff_within_at_id
- \+ *lemma* cont_diff_at_id
- \+ *lemma* cont_diff_on_id
- \+ *lemma* is_bounded_bilinear_map.cont_diff
- \+ *lemma* cont_diff_within_at.continuous_linear_map_comp
- \+ *lemma* cont_diff_at.continuous_linear_map_comp
- \+ *lemma* cont_diff_on.continuous_linear_map_comp
- \+ *lemma* cont_diff.continuous_linear_map_comp
- \+ *lemma* continuous_linear_equiv.comp_cont_diff_within_at_iff
- \+ *lemma* continuous_linear_equiv.comp_cont_diff_on_iff
- \+ *lemma* cont_diff_within_at.comp_continuous_linear_map
- \+ *lemma* cont_diff_on.comp_continuous_linear_map
- \+ *lemma* cont_diff.comp_continuous_linear_map
- \+ *lemma* continuous_linear_equiv.cont_diff_within_at_comp_iff
- \+ *lemma* continuous_linear_equiv.cont_diff_on_comp_iff
- \+ *lemma* cont_diff_within_at.prod
- \+ *lemma* cont_diff_on.prod
- \+ *lemma* cont_diff_at.prod
- \+ *lemma* cont_diff.prod
- \+ *lemma* cont_diff_within_at_pi
- \+ *lemma* cont_diff_on_pi
- \+ *lemma* cont_diff_at_pi
- \+ *lemma* cont_diff_pi
- \+ *lemma* cont_diff_on.comp
- \+ *lemma* cont_diff_on.comp'
- \+ *lemma* cont_diff.comp_cont_diff_on
- \+ *lemma* cont_diff.comp
- \+ *lemma* cont_diff_within_at.comp
- \+ *lemma* cont_diff_within_at.comp'
- \+ *lemma* cont_diff_at.comp_cont_diff_within_at
- \+ *lemma* cont_diff_at.comp
- \+ *lemma* cont_diff.comp_cont_diff_within_at
- \+ *lemma* cont_diff.comp_cont_diff_at
- \+ *lemma* cont_diff_on_fderiv_within_apply
- \+ *lemma* cont_diff.cont_diff_fderiv_apply
- \+ *lemma* cont_diff_add
- \+ *lemma* cont_diff_within_at.add
- \+ *lemma* cont_diff_at.add
- \+ *lemma* cont_diff.add
- \+ *lemma* cont_diff_on.add
- \+ *lemma* cont_diff_neg
- \+ *lemma* cont_diff_within_at.neg
- \+ *lemma* cont_diff_at.neg
- \+ *lemma* cont_diff.neg
- \+ *lemma* cont_diff_on.neg
- \+ *lemma* cont_diff_within_at.sub
- \+ *lemma* cont_diff_at.sub
- \+ *lemma* cont_diff_on.sub
- \+ *lemma* cont_diff.sub
- \+ *lemma* cont_diff_within_at.sum
- \+ *lemma* cont_diff_at.sum
- \+ *lemma* cont_diff_on.sum
- \+ *lemma* cont_diff.sum
- \+ *lemma* cont_diff_mul
- \+ *lemma* cont_diff_within_at.mul
- \+ *lemma* cont_diff_at.mul
- \+ *lemma* cont_diff_on.mul
- \+ *lemma* cont_diff.mul
- \+ *lemma* cont_diff_within_at.div_const
- \+ *lemma* cont_diff_at.div_const
- \+ *lemma* cont_diff_on.div_const
- \+ *lemma* cont_diff.div_const
- \+ *lemma* cont_diff.pow
- \+ *lemma* cont_diff_at.pow
- \+ *lemma* cont_diff_within_at.pow
- \+ *lemma* cont_diff_on.pow
- \+ *lemma* cont_diff_smul
- \+ *lemma* cont_diff_within_at.smul
- \+ *lemma* cont_diff_at.smul
- \+ *lemma* cont_diff.smul
- \+ *lemma* cont_diff_on.smul
- \+ *lemma* cont_diff_within_at.prod_map'
- \+ *lemma* cont_diff_within_at.prod_map
- \+ *lemma* cont_diff_on.prod_map
- \+ *lemma* cont_diff_at.prod_map
- \+ *lemma* cont_diff_at.prod_map'
- \+ *lemma* cont_diff.prod_map
- \+ *lemma* cont_diff_at_ring_inverse
- \+ *lemma* cont_diff_at_inv
- \+ *lemma* cont_diff_on_inv
- \+ *lemma* cont_diff_within_at.inv
- \+ *lemma* cont_diff_on.inv
- \+ *lemma* cont_diff_at.inv
- \+ *lemma* cont_diff.inv
- \+ *lemma* cont_diff_within_at.div
- \+ *lemma* cont_diff_on.div
- \+ *lemma* cont_diff_at.div
- \+ *lemma* cont_diff.div
- \+ *lemma* cont_diff_at_map_inverse
- \+ *lemma* cont_diff_at.has_strict_fderiv_at'
- \+ *lemma* cont_diff_at.has_strict_deriv_at'
- \+ *lemma* cont_diff_at.has_strict_fderiv_at
- \+ *lemma* cont_diff_at.has_strict_deriv_at
- \+ *lemma* cont_diff.has_strict_fderiv_at
- \+ *lemma* cont_diff.has_strict_deriv_at
- \+ *lemma* cont_diff_within_at.exists_lipschitz_on_with
- \+ *lemma* cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt
- \+ *lemma* cont_diff_at.exists_lipschitz_on_with
- \+ *lemma* cont_diff_on.deriv_within
- \+ *lemma* cont_diff_on.deriv_of_open
- \+ *lemma* cont_diff_on.continuous_on_deriv_within
- \+ *lemma* cont_diff_on.continuous_on_deriv_of_open
- \+ *lemma* cont_diff_within_at.restrict_scalars
- \+ *lemma* cont_diff_on.restrict_scalars
- \+ *lemma* cont_diff_at.restrict_scalars
- \+ *lemma* cont_diff.restrict_scalars
- \- *lemma* times_cont_diff_within_at_nat
- \- *lemma* times_cont_diff_within_at.of_le
- \- *lemma* times_cont_diff_within_at_iff_forall_nat_le
- \- *lemma* times_cont_diff_within_at_top
- \- *lemma* times_cont_diff_within_at.continuous_within_at
- \- *lemma* times_cont_diff_within_at.congr_of_eventually_eq
- \- *lemma* times_cont_diff_within_at.congr_of_eventually_eq'
- \- *lemma* filter.eventually_eq.times_cont_diff_within_at_iff
- \- *lemma* times_cont_diff_within_at.congr
- \- *lemma* times_cont_diff_within_at.congr'
- \- *lemma* times_cont_diff_within_at.mono_of_mem
- \- *lemma* times_cont_diff_within_at.mono
- \- *lemma* times_cont_diff_within_at.congr_nhds
- \- *lemma* times_cont_diff_within_at_congr_nhds
- \- *lemma* times_cont_diff_within_at_inter'
- \- *lemma* times_cont_diff_within_at_inter
- \- *lemma* times_cont_diff_within_at.differentiable_within_at'
- \- *lemma* times_cont_diff_within_at.differentiable_within_at
- \- *lemma* times_cont_diff_on.times_cont_diff_within_at
- \- *lemma* times_cont_diff_within_at.times_cont_diff_on
- \- *lemma* times_cont_diff_on.of_le
- \- *lemma* times_cont_diff_on_iff_forall_nat_le
- \- *lemma* times_cont_diff_on_top
- \- *lemma* times_cont_diff_on_all_iff_nat
- \- *lemma* times_cont_diff_on.continuous_on
- \- *lemma* times_cont_diff_on.congr
- \- *lemma* times_cont_diff_on_congr
- \- *lemma* times_cont_diff_on.mono
- \- *lemma* times_cont_diff_on.congr_mono
- \- *lemma* times_cont_diff_on.differentiable_on
- \- *lemma* times_cont_diff_on_of_locally_times_cont_diff_on
- \- *lemma* times_cont_diff_on_zero
- \- *lemma* times_cont_diff_within_at_zero
- \- *lemma* times_cont_diff_on_of_continuous_on_differentiable_on
- \- *lemma* times_cont_diff_on_of_differentiable_on
- \- *lemma* times_cont_diff_on.continuous_on_iterated_fderiv_within
- \- *lemma* times_cont_diff_on.differentiable_on_iterated_fderiv_within
- \- *lemma* times_cont_diff_on_iff_continuous_on_differentiable_on
- \- *lemma* times_cont_diff_on.fderiv_within
- \- *lemma* times_cont_diff_on.fderiv_of_open
- \- *lemma* times_cont_diff_on.continuous_on_fderiv_within
- \- *lemma* times_cont_diff_on.continuous_on_fderiv_of_open
- \- *lemma* times_cont_diff_on.continuous_on_fderiv_within_apply
- \- *lemma* times_cont_diff_at_top
- \- *lemma* times_cont_diff_at.times_cont_diff_within_at
- \- *lemma* times_cont_diff_within_at.times_cont_diff_at
- \- *lemma* times_cont_diff_at.congr_of_eventually_eq
- \- *lemma* times_cont_diff_at.of_le
- \- *lemma* times_cont_diff_at.continuous_at
- \- *lemma* times_cont_diff_at.differentiable_at
- \- *lemma* times_cont_diff_iff_times_cont_diff_at
- \- *lemma* times_cont_diff.times_cont_diff_at
- \- *lemma* times_cont_diff.times_cont_diff_within_at
- \- *lemma* times_cont_diff_top
- \- *lemma* times_cont_diff_all_iff_nat
- \- *lemma* times_cont_diff.times_cont_diff_on
- \- *lemma* times_cont_diff_zero
- \- *lemma* times_cont_diff_at_zero
- \- *lemma* times_cont_diff.of_le
- \- *lemma* times_cont_diff.continuous
- \- *lemma* times_cont_diff.differentiable
- \- *lemma* times_cont_diff_iff_continuous_differentiable
- \- *lemma* times_cont_diff_of_differentiable_iterated_fderiv
- \- *lemma* times_cont_diff.continuous_fderiv
- \- *lemma* times_cont_diff.continuous_fderiv_apply
- \- *lemma* times_cont_diff_zero_fun
- \- *lemma* times_cont_diff_const
- \- *lemma* times_cont_diff_on_const
- \- *lemma* times_cont_diff_at_const
- \- *lemma* times_cont_diff_within_at_const
- \- *lemma* times_cont_diff_of_subsingleton
- \- *lemma* times_cont_diff_at_of_subsingleton
- \- *lemma* times_cont_diff_within_at_of_subsingleton
- \- *lemma* times_cont_diff_on_of_subsingleton
- \- *lemma* is_bounded_linear_map.times_cont_diff
- \- *lemma* continuous_linear_map.times_cont_diff
- \- *lemma* continuous_linear_equiv.times_cont_diff
- \- *lemma* linear_isometry.times_cont_diff
- \- *lemma* linear_isometry_equiv.times_cont_diff
- \- *lemma* times_cont_diff_fst
- \- *lemma* times_cont_diff_on_fst
- \- *lemma* times_cont_diff_at_fst
- \- *lemma* times_cont_diff_within_at_fst
- \- *lemma* times_cont_diff_snd
- \- *lemma* times_cont_diff_on_snd
- \- *lemma* times_cont_diff_at_snd
- \- *lemma* times_cont_diff_within_at_snd
- \- *lemma* times_cont_diff_prod_assoc
- \- *lemma* times_cont_diff_prod_assoc_symm
- \- *lemma* times_cont_diff_id
- \- *lemma* times_cont_diff_within_at_id
- \- *lemma* times_cont_diff_at_id
- \- *lemma* times_cont_diff_on_id
- \- *lemma* is_bounded_bilinear_map.times_cont_diff
- \- *lemma* times_cont_diff_within_at.continuous_linear_map_comp
- \- *lemma* times_cont_diff_at.continuous_linear_map_comp
- \- *lemma* times_cont_diff_on.continuous_linear_map_comp
- \- *lemma* times_cont_diff.continuous_linear_map_comp
- \- *lemma* continuous_linear_equiv.comp_times_cont_diff_within_at_iff
- \- *lemma* continuous_linear_equiv.comp_times_cont_diff_on_iff
- \- *lemma* times_cont_diff_within_at.comp_continuous_linear_map
- \- *lemma* times_cont_diff_on.comp_continuous_linear_map
- \- *lemma* times_cont_diff.comp_continuous_linear_map
- \- *lemma* continuous_linear_equiv.times_cont_diff_within_at_comp_iff
- \- *lemma* continuous_linear_equiv.times_cont_diff_on_comp_iff
- \- *lemma* times_cont_diff_within_at.prod
- \- *lemma* times_cont_diff_on.prod
- \- *lemma* times_cont_diff_at.prod
- \- *lemma* times_cont_diff.prod
- \- *lemma* times_cont_diff_within_at_pi
- \- *lemma* times_cont_diff_on_pi
- \- *lemma* times_cont_diff_at_pi
- \- *lemma* times_cont_diff_pi
- \- *lemma* times_cont_diff_on.comp
- \- *lemma* times_cont_diff_on.comp'
- \- *lemma* times_cont_diff.comp_times_cont_diff_on
- \- *lemma* times_cont_diff.comp
- \- *lemma* times_cont_diff_within_at.comp
- \- *lemma* times_cont_diff_within_at.comp'
- \- *lemma* times_cont_diff_at.comp_times_cont_diff_within_at
- \- *lemma* times_cont_diff_at.comp
- \- *lemma* times_cont_diff.comp_times_cont_diff_within_at
- \- *lemma* times_cont_diff.comp_times_cont_diff_at
- \- *lemma* times_cont_diff_on_fderiv_within_apply
- \- *lemma* times_cont_diff.times_cont_diff_fderiv_apply
- \- *lemma* times_cont_diff_add
- \- *lemma* times_cont_diff_within_at.add
- \- *lemma* times_cont_diff_at.add
- \- *lemma* times_cont_diff.add
- \- *lemma* times_cont_diff_on.add
- \- *lemma* times_cont_diff_neg
- \- *lemma* times_cont_diff_within_at.neg
- \- *lemma* times_cont_diff_at.neg
- \- *lemma* times_cont_diff.neg
- \- *lemma* times_cont_diff_on.neg
- \- *lemma* times_cont_diff_within_at.sub
- \- *lemma* times_cont_diff_at.sub
- \- *lemma* times_cont_diff_on.sub
- \- *lemma* times_cont_diff.sub
- \- *lemma* times_cont_diff_within_at.sum
- \- *lemma* times_cont_diff_at.sum
- \- *lemma* times_cont_diff_on.sum
- \- *lemma* times_cont_diff.sum
- \- *lemma* times_cont_diff_mul
- \- *lemma* times_cont_diff_within_at.mul
- \- *lemma* times_cont_diff_at.mul
- \- *lemma* times_cont_diff_on.mul
- \- *lemma* times_cont_diff.mul
- \- *lemma* times_cont_diff_within_at.div_const
- \- *lemma* times_cont_diff_at.div_const
- \- *lemma* times_cont_diff_on.div_const
- \- *lemma* times_cont_diff.div_const
- \- *lemma* times_cont_diff.pow
- \- *lemma* times_cont_diff_at.pow
- \- *lemma* times_cont_diff_within_at.pow
- \- *lemma* times_cont_diff_on.pow
- \- *lemma* times_cont_diff_smul
- \- *lemma* times_cont_diff_within_at.smul
- \- *lemma* times_cont_diff_at.smul
- \- *lemma* times_cont_diff.smul
- \- *lemma* times_cont_diff_on.smul
- \- *lemma* times_cont_diff_within_at.prod_map'
- \- *lemma* times_cont_diff_within_at.prod_map
- \- *lemma* times_cont_diff_on.prod_map
- \- *lemma* times_cont_diff_at.prod_map
- \- *lemma* times_cont_diff_at.prod_map'
- \- *lemma* times_cont_diff.prod_map
- \- *lemma* times_cont_diff_at_ring_inverse
- \- *lemma* times_cont_diff_at_inv
- \- *lemma* times_cont_diff_on_inv
- \- *lemma* times_cont_diff_within_at.inv
- \- *lemma* times_cont_diff_on.inv
- \- *lemma* times_cont_diff_at.inv
- \- *lemma* times_cont_diff.inv
- \- *lemma* times_cont_diff_within_at.div
- \- *lemma* times_cont_diff_on.div
- \- *lemma* times_cont_diff_at.div
- \- *lemma* times_cont_diff.div
- \- *lemma* times_cont_diff_at_map_inverse
- \- *lemma* times_cont_diff_at.has_strict_fderiv_at'
- \- *lemma* times_cont_diff_at.has_strict_deriv_at'
- \- *lemma* times_cont_diff_at.has_strict_fderiv_at
- \- *lemma* times_cont_diff_at.has_strict_deriv_at
- \- *lemma* times_cont_diff.has_strict_fderiv_at
- \- *lemma* times_cont_diff.has_strict_deriv_at
- \- *lemma* times_cont_diff_within_at.exists_lipschitz_on_with
- \- *lemma* times_cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt
- \- *lemma* times_cont_diff_at.exists_lipschitz_on_with
- \- *lemma* times_cont_diff_on.deriv_within
- \- *lemma* times_cont_diff_on.deriv_of_open
- \- *lemma* times_cont_diff_on.continuous_on_deriv_within
- \- *lemma* times_cont_diff_on.continuous_on_deriv_of_open
- \- *lemma* times_cont_diff_within_at.restrict_scalars
- \- *lemma* times_cont_diff_on.restrict_scalars
- \- *lemma* times_cont_diff_at.restrict_scalars
- \- *lemma* times_cont_diff.restrict_scalars
- \+ *theorem* cont_diff_within_at_succ_iff_has_fderiv_within_at
- \+ *theorem* cont_diff_on_succ_iff_has_fderiv_within_at
- \+ *theorem* cont_diff_on.ftaylor_series_within
- \+ *theorem* cont_diff_on_succ_iff_fderiv_within
- \+ *theorem* cont_diff_on_succ_iff_fderiv_of_open
- \+ *theorem* cont_diff_on_top_iff_fderiv_within
- \+ *theorem* cont_diff_on_top_iff_fderiv_of_open
- \+ *theorem* cont_diff_within_at_univ
- \+ *theorem* cont_diff_at_succ_iff_has_fderiv_at
- \+ *theorem* cont_diff_on_univ
- \+ *theorem* cont_diff_on_iff_ftaylor_series
- \+ *theorem* cont_diff_succ_iff_fderiv
- \+ *theorem* cont_diff_top_iff_fderiv
- \+ *theorem* local_homeomorph.cont_diff_at_symm
- \+ *theorem* local_homeomorph.cont_diff_at_symm_deriv
- \+ *theorem* cont_diff_on_succ_iff_deriv_within
- \+ *theorem* cont_diff_on_succ_iff_deriv_of_open
- \+ *theorem* cont_diff_on_top_iff_deriv_within
- \+ *theorem* cont_diff_on_top_iff_deriv_of_open
- \+ *theorem* cont_diff_succ_iff_deriv
- \- *theorem* times_cont_diff_within_at_succ_iff_has_fderiv_within_at
- \- *theorem* times_cont_diff_on_succ_iff_has_fderiv_within_at
- \- *theorem* times_cont_diff_on.ftaylor_series_within
- \- *theorem* times_cont_diff_on_succ_iff_fderiv_within
- \- *theorem* times_cont_diff_on_succ_iff_fderiv_of_open
- \- *theorem* times_cont_diff_on_top_iff_fderiv_within
- \- *theorem* times_cont_diff_on_top_iff_fderiv_of_open
- \- *theorem* times_cont_diff_within_at_univ
- \- *theorem* times_cont_diff_at_succ_iff_has_fderiv_at
- \- *theorem* times_cont_diff_on_univ
- \- *theorem* times_cont_diff_on_iff_ftaylor_series
- \- *theorem* times_cont_diff_succ_iff_fderiv
- \- *theorem* times_cont_diff_top_iff_fderiv
- \- *theorem* local_homeomorph.times_cont_diff_at_symm
- \- *theorem* local_homeomorph.times_cont_diff_at_symm_deriv
- \- *theorem* times_cont_diff_on_succ_iff_deriv_within
- \- *theorem* times_cont_diff_on_succ_iff_deriv_of_open
- \- *theorem* times_cont_diff_on_top_iff_deriv_within
- \- *theorem* times_cont_diff_on_top_iff_deriv_of_open
- \- *theorem* times_cont_diff_succ_iff_deriv
- \+ *def* cont_diff_within_at
- \+ *def* cont_diff_at
- \- *def* times_cont_diff_within_at
- \- *def* times_cont_diff_at

modified src/analysis/calculus/formal_multilinear_series.lean

modified src/analysis/calculus/inverse.lean

modified src/analysis/calculus/iterated_deriv.lean
- \+ *lemma* cont_diff_on_of_continuous_on_differentiable_on_deriv
- \+ *lemma* cont_diff_on_of_differentiable_on_deriv
- \+ *lemma* cont_diff_on.continuous_on_iterated_deriv_within
- \+ *lemma* cont_diff_on.differentiable_on_iterated_deriv_within
- \+ *lemma* cont_diff_on_iff_continuous_on_differentiable_on_deriv
- \+ *lemma* cont_diff_iff_iterated_deriv
- \+ *lemma* cont_diff_of_differentiable_iterated_deriv
- \+ *lemma* cont_diff.continuous_iterated_deriv
- \+ *lemma* cont_diff.differentiable_iterated_deriv
- \- *lemma* times_cont_diff_on_of_continuous_on_differentiable_on_deriv
- \- *lemma* times_cont_diff_on_of_differentiable_on_deriv
- \- *lemma* times_cont_diff_on.continuous_on_iterated_deriv_within
- \- *lemma* times_cont_diff_on.differentiable_on_iterated_deriv_within
- \- *lemma* times_cont_diff_on_iff_continuous_on_differentiable_on_deriv
- \- *lemma* times_cont_diff_iff_iterated_deriv
- \- *lemma* times_cont_diff_of_differentiable_iterated_deriv
- \- *lemma* times_cont_diff.continuous_iterated_deriv
- \- *lemma* times_cont_diff.differentiable_iterated_deriv

modified src/analysis/calculus/specific_functions.lean
- \+/\- *lemma* R_pos
- \+/\- *lemma* R_pos
- \+/\- *lemma* coe_eq_comp
- \+/\- *lemma* nonneg
- \+/\- *lemma* le_one
- \+ *lemma* exists_cont_diff_bump_function_of_mem_nhds
- \+/\- *lemma* R_pos
- \+/\- *lemma* R_pos
- \+/\- *lemma* coe_eq_comp
- \+/\- *lemma* nonneg
- \+/\- *lemma* le_one
- \- *lemma* exists_times_cont_diff_bump_function_of_mem_nhds
- \+/\- *def* to_fun
- \+/\- *def* to_fun
- \+/\- *def* to_fun
- \+/\- *def* to_fun

modified src/analysis/complex/real_deriv.lean
- \+ *theorem* cont_diff_at.real_of_complex
- \+ *theorem* cont_diff.real_of_complex
- \- *theorem* times_cont_diff_at.real_of_complex
- \- *theorem* times_cont_diff.real_of_complex

modified src/analysis/inner_product_space/calculus.lean
- \+ *lemma* cont_diff_inner
- \+ *lemma* cont_diff_at_inner
- \+ *lemma* cont_diff_within_at.inner
- \+ *lemma* cont_diff_at.inner
- \+ *lemma* cont_diff_on.inner
- \+ *lemma* cont_diff.inner
- \+ *lemma* cont_diff_norm_sq
- \+ *lemma* cont_diff.norm_sq
- \+ *lemma* cont_diff_within_at.norm_sq
- \+ *lemma* cont_diff_at.norm_sq
- \+ *lemma* cont_diff_at_norm
- \+ *lemma* cont_diff_at.norm
- \+ *lemma* cont_diff_at.dist
- \+ *lemma* cont_diff_within_at.norm
- \+ *lemma* cont_diff_within_at.dist
- \+ *lemma* cont_diff_on.norm_sq
- \+ *lemma* cont_diff_on.norm
- \+ *lemma* cont_diff_on.dist
- \+ *lemma* cont_diff.norm
- \+ *lemma* cont_diff.dist
- \- *lemma* times_cont_diff_inner
- \- *lemma* times_cont_diff_at_inner
- \- *lemma* times_cont_diff_within_at.inner
- \- *lemma* times_cont_diff_at.inner
- \- *lemma* times_cont_diff_on.inner
- \- *lemma* times_cont_diff.inner
- \- *lemma* times_cont_diff_norm_sq
- \- *lemma* times_cont_diff.norm_sq
- \- *lemma* times_cont_diff_within_at.norm_sq
- \- *lemma* times_cont_diff_at.norm_sq
- \- *lemma* times_cont_diff_at_norm
- \- *lemma* times_cont_diff_at.norm
- \- *lemma* times_cont_diff_at.dist
- \- *lemma* times_cont_diff_within_at.norm
- \- *lemma* times_cont_diff_within_at.dist
- \- *lemma* times_cont_diff_on.norm_sq
- \- *lemma* times_cont_diff_on.norm
- \- *lemma* times_cont_diff_on.dist
- \- *lemma* times_cont_diff.norm
- \- *lemma* times_cont_diff.dist

modified src/analysis/inner_product_space/euclidean_dist.lean
- \+ *lemma* cont_diff.euclidean_dist
- \- *lemma* times_cont_diff.euclidean_dist

modified src/analysis/special_functions/complex/log_deriv.lean
- \+ *lemma* cont_diff_at_log
- \- *lemma* times_cont_diff_at_log

modified src/analysis/special_functions/exp_deriv.lean
- \+ *lemma* cont_diff_exp
- \+ *lemma* cont_diff.cexp
- \+ *lemma* cont_diff_at.cexp
- \+ *lemma* cont_diff_on.cexp
- \+ *lemma* cont_diff_within_at.cexp
- \+ *lemma* cont_diff_exp
- \+ *lemma* cont_diff.exp
- \+ *lemma* cont_diff_at.exp
- \+ *lemma* cont_diff_on.exp
- \+ *lemma* cont_diff_within_at.exp
- \- *lemma* times_cont_diff_exp
- \- *lemma* times_cont_diff.cexp
- \- *lemma* times_cont_diff_at.cexp
- \- *lemma* times_cont_diff_on.cexp
- \- *lemma* times_cont_diff_within_at.cexp
- \- *lemma* times_cont_diff_exp
- \- *lemma* times_cont_diff.exp
- \- *lemma* times_cont_diff_at.exp
- \- *lemma* times_cont_diff_on.exp
- \- *lemma* times_cont_diff_within_at.exp

modified src/analysis/special_functions/log_deriv.lean
- \+ *lemma* cont_diff_on_log
- \+ *lemma* cont_diff_at_log
- \+ *lemma* cont_diff_at.log
- \+ *lemma* cont_diff_within_at.log
- \+ *lemma* cont_diff_on.log
- \+ *lemma* cont_diff.log
- \- *lemma* times_cont_diff_on_log
- \- *lemma* times_cont_diff_at_log
- \- *lemma* times_cont_diff_at.log
- \- *lemma* times_cont_diff_within_at.log
- \- *lemma* times_cont_diff_on.log
- \- *lemma* times_cont_diff.log

modified src/analysis/special_functions/pow_deriv.lean
- \+ *lemma* cont_diff_at_rpow_of_ne
- \+ *lemma* cont_diff_at_rpow_const_of_ne
- \+ *lemma* cont_diff_rpow_const_of_le
- \+ *lemma* cont_diff_at_rpow_const_of_le
- \+ *lemma* cont_diff_at_rpow_const
- \+ *lemma* cont_diff_within_at.rpow
- \+ *lemma* cont_diff_at.rpow
- \+ *lemma* cont_diff_on.rpow
- \+ *lemma* cont_diff.rpow
- \+ *lemma* cont_diff_within_at.rpow_const_of_ne
- \+ *lemma* cont_diff_at.rpow_const_of_ne
- \+ *lemma* cont_diff_on.rpow_const_of_ne
- \+ *lemma* cont_diff.rpow_const_of_ne
- \+ *lemma* cont_diff_within_at.rpow_const_of_le
- \+ *lemma* cont_diff_at.rpow_const_of_le
- \+ *lemma* cont_diff_on.rpow_const_of_le
- \+ *lemma* cont_diff.rpow_const_of_le
- \- *lemma* times_cont_diff_at_rpow_of_ne
- \- *lemma* times_cont_diff_at_rpow_const_of_ne
- \- *lemma* times_cont_diff_rpow_const_of_le
- \- *lemma* times_cont_diff_at_rpow_const_of_le
- \- *lemma* times_cont_diff_at_rpow_const
- \- *lemma* times_cont_diff_within_at.rpow
- \- *lemma* times_cont_diff_at.rpow
- \- *lemma* times_cont_diff_on.rpow
- \- *lemma* times_cont_diff.rpow
- \- *lemma* times_cont_diff_within_at.rpow_const_of_ne
- \- *lemma* times_cont_diff_at.rpow_const_of_ne
- \- *lemma* times_cont_diff_on.rpow_const_of_ne
- \- *lemma* times_cont_diff.rpow_const_of_ne
- \- *lemma* times_cont_diff_within_at.rpow_const_of_le
- \- *lemma* times_cont_diff_at.rpow_const_of_le
- \- *lemma* times_cont_diff_on.rpow_const_of_le
- \- *lemma* times_cont_diff.rpow_const_of_le

modified src/analysis/special_functions/sqrt.lean
- \+ *lemma* cont_diff_at_sqrt
- \+ *lemma* cont_diff_at.sqrt
- \+ *lemma* cont_diff_within_at.sqrt
- \+ *lemma* cont_diff_on.sqrt
- \+ *lemma* cont_diff.sqrt
- \- *lemma* times_cont_diff_at_sqrt
- \- *lemma* times_cont_diff_at.sqrt
- \- *lemma* times_cont_diff_within_at.sqrt
- \- *lemma* times_cont_diff_on.sqrt
- \- *lemma* times_cont_diff.sqrt

modified src/analysis/special_functions/trigonometric/arctan_deriv.lean
- \+ *lemma* cont_diff_at_tan
- \+ *lemma* cont_diff_arctan
- \+ *lemma* cont_diff_at.arctan
- \+ *lemma* cont_diff.arctan
- \+ *lemma* cont_diff_within_at.arctan
- \+ *lemma* cont_diff_on.arctan
- \- *lemma* times_cont_diff_at_tan
- \- *lemma* times_cont_diff_arctan
- \- *lemma* times_cont_diff_at.arctan
- \- *lemma* times_cont_diff.arctan
- \- *lemma* times_cont_diff_within_at.arctan
- \- *lemma* times_cont_diff_on.arctan

modified src/analysis/special_functions/trigonometric/complex_deriv.lean
- \+ *lemma* cont_diff_at_tan
- \- *lemma* times_cont_diff_at_tan

modified src/analysis/special_functions/trigonometric/deriv.lean
- \+ *lemma* cont_diff_sin
- \+ *lemma* cont_diff_cos
- \+ *lemma* cont_diff_sinh
- \+ *lemma* cont_diff_cosh
- \+ *lemma* cont_diff.ccos
- \+ *lemma* cont_diff_at.ccos
- \+ *lemma* cont_diff_on.ccos
- \+ *lemma* cont_diff_within_at.ccos
- \+ *lemma* cont_diff.csin
- \+ *lemma* cont_diff_at.csin
- \+ *lemma* cont_diff_on.csin
- \+ *lemma* cont_diff_within_at.csin
- \+ *lemma* cont_diff.ccosh
- \+ *lemma* cont_diff_at.ccosh
- \+ *lemma* cont_diff_on.ccosh
- \+ *lemma* cont_diff_within_at.ccosh
- \+ *lemma* cont_diff.csinh
- \+ *lemma* cont_diff_at.csinh
- \+ *lemma* cont_diff_on.csinh
- \+ *lemma* cont_diff_within_at.csinh
- \+ *lemma* cont_diff_sin
- \+ *lemma* cont_diff_cos
- \+ *lemma* cont_diff_sinh
- \+ *lemma* cont_diff_cosh
- \+ *lemma* cont_diff.cos
- \+ *lemma* cont_diff_at.cos
- \+ *lemma* cont_diff_on.cos
- \+ *lemma* cont_diff_within_at.cos
- \+ *lemma* cont_diff.sin
- \+ *lemma* cont_diff_at.sin
- \+ *lemma* cont_diff_on.sin
- \+ *lemma* cont_diff_within_at.sin
- \+ *lemma* cont_diff.cosh
- \+ *lemma* cont_diff_at.cosh
- \+ *lemma* cont_diff_on.cosh
- \+ *lemma* cont_diff_within_at.cosh
- \+ *lemma* cont_diff.sinh
- \+ *lemma* cont_diff_at.sinh
- \+ *lemma* cont_diff_on.sinh
- \+ *lemma* cont_diff_within_at.sinh
- \- *lemma* times_cont_diff_sin
- \- *lemma* times_cont_diff_cos
- \- *lemma* times_cont_diff_sinh
- \- *lemma* times_cont_diff_cosh
- \- *lemma* times_cont_diff.ccos
- \- *lemma* times_cont_diff_at.ccos
- \- *lemma* times_cont_diff_on.ccos
- \- *lemma* times_cont_diff_within_at.ccos
- \- *lemma* times_cont_diff.csin
- \- *lemma* times_cont_diff_at.csin
- \- *lemma* times_cont_diff_on.csin
- \- *lemma* times_cont_diff_within_at.csin
- \- *lemma* times_cont_diff.ccosh
- \- *lemma* times_cont_diff_at.ccosh
- \- *lemma* times_cont_diff_on.ccosh
- \- *lemma* times_cont_diff_within_at.ccosh
- \- *lemma* times_cont_diff.csinh
- \- *lemma* times_cont_diff_at.csinh
- \- *lemma* times_cont_diff_on.csinh
- \- *lemma* times_cont_diff_within_at.csinh
- \- *lemma* times_cont_diff_sin
- \- *lemma* times_cont_diff_cos
- \- *lemma* times_cont_diff_sinh
- \- *lemma* times_cont_diff_cosh
- \- *lemma* times_cont_diff.cos
- \- *lemma* times_cont_diff_at.cos
- \- *lemma* times_cont_diff_on.cos
- \- *lemma* times_cont_diff_within_at.cos
- \- *lemma* times_cont_diff.sin
- \- *lemma* times_cont_diff_at.sin
- \- *lemma* times_cont_diff_on.sin
- \- *lemma* times_cont_diff_within_at.sin
- \- *lemma* times_cont_diff.cosh
- \- *lemma* times_cont_diff_at.cosh
- \- *lemma* times_cont_diff_on.cosh
- \- *lemma* times_cont_diff_within_at.cosh
- \- *lemma* times_cont_diff.sinh
- \- *lemma* times_cont_diff_at.sinh
- \- *lemma* times_cont_diff_on.sinh
- \- *lemma* times_cont_diff_within_at.sinh

modified src/analysis/special_functions/trigonometric/inverse_deriv.lean
- \+ *lemma* cont_diff_at_arcsin
- \+ *lemma* cont_diff_on_arcsin
- \+ *lemma* cont_diff_at_arcsin_iff
- \+ *lemma* cont_diff_at_arccos
- \+ *lemma* cont_diff_on_arccos
- \+ *lemma* cont_diff_at_arccos_iff
- \- *lemma* times_cont_diff_at_arcsin
- \- *lemma* times_cont_diff_on_arcsin
- \- *lemma* times_cont_diff_at_arcsin_iff
- \- *lemma* times_cont_diff_at_arccos
- \- *lemma* times_cont_diff_on_arccos
- \- *lemma* times_cont_diff_at_arccos_iff

modified src/geometry/manifold/algebra/left_invariant_derivation.lean

modified src/geometry/manifold/algebra/lie_group.lean

modified src/geometry/manifold/algebra/monoid.lean

modified src/geometry/manifold/algebra/smooth_functions.lean

modified src/geometry/manifold/algebra/structures.lean

modified src/geometry/manifold/basic_smooth_bundle.lean

modified src/geometry/manifold/bump_function.lean
- \+/\- *lemma* R_pos
- \+/\- *lemma* R_pos

renamed src/geometry/manifold/times_cont_mdiff.lean to src/geometry/manifold/cont_mdiff.lean
- \+ *lemma* cont_diff_within_at_local_invariant_prop
- \+ *lemma* cont_diff_within_at_local_invariant_prop_mono
- \+ *lemma* cont_diff_within_at_local_invariant_prop_id
- \+ *lemma* cont_mdiff.smooth
- \+ *lemma* smooth.cont_mdiff
- \+ *lemma* cont_mdiff_on.smooth_on
- \+ *lemma* smooth_on.cont_mdiff_on
- \+ *lemma* cont_mdiff_at.smooth_at
- \+ *lemma* smooth_at.cont_mdiff_at
- \+ *lemma* cont_mdiff_within_at.smooth_within_at
- \+ *lemma* smooth_within_at.cont_mdiff_within_at
- \+ *lemma* cont_mdiff.cont_mdiff_at
- \+ *lemma* cont_mdiff_within_at_univ
- \+ *lemma* cont_mdiff_on_univ
- \+ *lemma* cont_mdiff_within_at_iff
- \+ *lemma* cont_mdiff_within_at_iff''
- \+ *lemma* cont_mdiff_within_at_iff_target
- \+ *lemma* cont_mdiff_at_ext_chart_at
- \+ *lemma* cont_mdiff_within_at_iff'
- \+ *lemma* cont_mdiff_at_ext_chart_at'
- \+ *lemma* cont_mdiff_on_iff
- \+ *lemma* cont_mdiff_on_iff_target
- \+ *lemma* cont_mdiff_iff
- \+ *lemma* cont_mdiff_iff_target
- \+ *lemma* cont_mdiff_within_at.of_le
- \+ *lemma* cont_mdiff_at.of_le
- \+ *lemma* cont_mdiff_on.of_le
- \+ *lemma* cont_mdiff.of_le
- \+ *lemma* cont_mdiff_within_at.of_succ
- \+ *lemma* cont_mdiff_at.of_succ
- \+ *lemma* cont_mdiff_on.of_succ
- \+ *lemma* cont_mdiff.of_succ
- \+ *lemma* cont_mdiff_within_at.continuous_within_at
- \+ *lemma* cont_mdiff_at.continuous_at
- \+ *lemma* cont_mdiff_on.continuous_on
- \+ *lemma* cont_mdiff.continuous
- \+ *lemma* cont_mdiff_within_at.mdifferentiable_within_at
- \+ *lemma* cont_mdiff_at.mdifferentiable_at
- \+ *lemma* cont_mdiff_on.mdifferentiable_on
- \+ *lemma* cont_mdiff.mdifferentiable
- \+ *lemma* cont_mdiff_within_at_top
- \+ *lemma* cont_mdiff_at_top
- \+ *lemma* cont_mdiff_on_top
- \+ *lemma* cont_mdiff_top
- \+ *lemma* cont_mdiff_within_at_iff_nat
- \+ *lemma* cont_mdiff_within_at.mono
- \+ *lemma* cont_mdiff_at.cont_mdiff_within_at
- \+ *lemma* cont_mdiff_on.mono
- \+ *lemma* cont_mdiff.cont_mdiff_on
- \+ *lemma* cont_mdiff_within_at_inter'
- \+ *lemma* cont_mdiff_within_at_inter
- \+ *lemma* cont_mdiff_within_at.cont_mdiff_at
- \+ *lemma* cont_mdiff_on_ext_chart_at
- \+ *lemma* cont_mdiff_within_at_iff_cont_mdiff_on_nhds
- \+ *lemma* cont_mdiff_at_iff_cont_mdiff_on_nhds
- \+ *lemma* cont_mdiff_within_at.congr
- \+ *lemma* cont_mdiff_within_at_congr
- \+ *lemma* cont_mdiff_within_at.congr_of_eventually_eq
- \+ *lemma* filter.eventually_eq.cont_mdiff_within_at_iff
- \+ *lemma* cont_mdiff_at.congr_of_eventually_eq
- \+ *lemma* filter.eventually_eq.cont_mdiff_at_iff
- \+ *lemma* cont_mdiff_on.congr
- \+ *lemma* cont_mdiff_on_congr
- \+ *lemma* cont_mdiff_on_of_locally_cont_mdiff_on
- \+ *lemma* cont_mdiff_of_locally_cont_mdiff_on
- \+ *lemma* cont_mdiff_within_at.comp
- \+ *lemma* cont_mdiff_on.comp
- \+ *lemma* cont_mdiff_on.comp'
- \+ *lemma* cont_mdiff.comp
- \+ *lemma* cont_mdiff_within_at.comp'
- \+ *lemma* cont_mdiff_at.comp_cont_mdiff_within_at
- \+ *lemma* cont_mdiff_at.comp
- \+ *lemma* cont_mdiff.comp_cont_mdiff_on
- \+ *lemma* cont_mdiff_on_of_mem_maximal_atlas
- \+ *lemma* cont_mdiff_on_symm_of_mem_maximal_atlas
- \+ *lemma* cont_mdiff_on_chart
- \+ *lemma* cont_mdiff_on_chart_symm
- \+ *lemma* cont_mdiff_id
- \+/\- *lemma* smooth_id
- \+ *lemma* cont_mdiff_on_id
- \+/\- *lemma* smooth_on_id
- \+ *lemma* cont_mdiff_at_id
- \+/\- *lemma* smooth_at_id
- \+ *lemma* cont_mdiff_within_at_id
- \+/\- *lemma* smooth_within_at_id
- \+ *lemma* cont_mdiff_const
- \+ *lemma* cont_mdiff_one
- \+/\- *lemma* smooth_const
- \+ *lemma* cont_mdiff_on_const
- \+ *lemma* cont_mdiff_on_one
- \+ *lemma* cont_mdiff_at_const
- \+ *lemma* cont_mdiff_at_one
- \+ *lemma* cont_mdiff_within_at_const
- \+ *lemma* cont_mdiff_within_at_one
- \+ *lemma* cont_mdiff_of_support
- \+ *lemma* cont_mdiff_within_at_iff_cont_diff_within_at
- \+ *lemma* cont_mdiff_at_iff_cont_diff_at
- \+ *lemma* cont_mdiff_on_iff_cont_diff_on
- \+ *lemma* cont_mdiff_iff_cont_diff
- \+ *lemma* cont_mdiff_on.continuous_on_tangent_map_within_aux
- \+ *lemma* cont_mdiff_on.cont_mdiff_on_tangent_map_within_aux
- \+ *lemma* cont_mdiff_proj
- \+ *lemma* cont_mdiff_on_proj
- \+ *lemma* cont_mdiff_at_proj
- \+ *lemma* cont_mdiff_within_at_proj
- \+ *lemma* cont_mdiff_proj
- \+ *lemma* cont_mdiff_on_proj
- \+ *lemma* cont_mdiff_at_proj
- \+ *lemma* cont_mdiff_within_at_proj
- \+ *lemma* cont_mdiff_within_at.prod_mk
- \+ *lemma* cont_mdiff_within_at.prod_mk_space
- \+ *lemma* cont_mdiff_at.prod_mk
- \+ *lemma* cont_mdiff_at.prod_mk_space
- \+ *lemma* cont_mdiff_on.prod_mk
- \+ *lemma* cont_mdiff_on.prod_mk_space
- \+ *lemma* cont_mdiff.prod_mk
- \+ *lemma* cont_mdiff.prod_mk_space
- \+ *lemma* cont_mdiff_within_at_fst
- \+ *lemma* cont_mdiff_at_fst
- \+ *lemma* cont_mdiff_on_fst
- \+ *lemma* cont_mdiff_fst
- \+ *lemma* cont_mdiff_within_at_snd
- \+ *lemma* cont_mdiff_at_snd
- \+ *lemma* cont_mdiff_on_snd
- \+ *lemma* cont_mdiff_snd
- \+ *lemma* cont_mdiff_within_at.prod_map'
- \+ *lemma* cont_mdiff_within_at.prod_map
- \+ *lemma* cont_mdiff_at.prod_map
- \+ *lemma* cont_mdiff_at.prod_map'
- \+ *lemma* cont_mdiff_on.prod_map
- \+ *lemma* cont_mdiff.prod_map
- \+ *lemma* cont_mdiff_within_at_pi_space
- \+ *lemma* cont_mdiff_on_pi_space
- \+ *lemma* cont_mdiff_at_pi_space
- \+ *lemma* cont_mdiff_pi_space
- \+ *lemma* continuous_linear_map.cont_mdiff
- \- *lemma* times_cont_diff_within_at_local_invariant_prop
- \- *lemma* times_cont_diff_within_at_local_invariant_prop_mono
- \- *lemma* times_cont_diff_within_at_local_invariant_prop_id
- \- *lemma* times_cont_mdiff.smooth
- \- *lemma* smooth.times_cont_mdiff
- \- *lemma* times_cont_mdiff_on.smooth_on
- \- *lemma* smooth_on.times_cont_mdiff_on
- \- *lemma* times_cont_mdiff_at.smooth_at
- \- *lemma* smooth_at.times_cont_mdiff_at
- \- *lemma* times_cont_mdiff_within_at.smooth_within_at
- \- *lemma* smooth_within_at.times_cont_mdiff_within_at
- \- *lemma* times_cont_mdiff.times_cont_mdiff_at
- \- *lemma* times_cont_mdiff_within_at_univ
- \- *lemma* times_cont_mdiff_on_univ
- \- *lemma* times_cont_mdiff_within_at_iff
- \- *lemma* times_cont_mdiff_within_at_iff''
- \- *lemma* times_cont_mdiff_within_at_iff_target
- \- *lemma* times_cont_mdiff_at_ext_chart_at
- \- *lemma* times_cont_mdiff_within_at_iff'
- \- *lemma* times_cont_mdiff_at_ext_chart_at'
- \- *lemma* times_cont_mdiff_on_iff
- \- *lemma* times_cont_mdiff_on_iff_target
- \- *lemma* times_cont_mdiff_iff
- \- *lemma* times_cont_mdiff_iff_target
- \- *lemma* times_cont_mdiff_within_at.of_le
- \- *lemma* times_cont_mdiff_at.of_le
- \- *lemma* times_cont_mdiff_on.of_le
- \- *lemma* times_cont_mdiff.of_le
- \- *lemma* times_cont_mdiff_within_at.of_succ
- \- *lemma* times_cont_mdiff_at.of_succ
- \- *lemma* times_cont_mdiff_on.of_succ
- \- *lemma* times_cont_mdiff.of_succ
- \- *lemma* times_cont_mdiff_within_at.continuous_within_at
- \- *lemma* times_cont_mdiff_at.continuous_at
- \- *lemma* times_cont_mdiff_on.continuous_on
- \- *lemma* times_cont_mdiff.continuous
- \- *lemma* times_cont_mdiff_within_at.mdifferentiable_within_at
- \- *lemma* times_cont_mdiff_at.mdifferentiable_at
- \- *lemma* times_cont_mdiff_on.mdifferentiable_on
- \- *lemma* times_cont_mdiff.mdifferentiable
- \- *lemma* times_cont_mdiff_within_at_top
- \- *lemma* times_cont_mdiff_at_top
- \- *lemma* times_cont_mdiff_on_top
- \- *lemma* times_cont_mdiff_top
- \- *lemma* times_cont_mdiff_within_at_iff_nat
- \- *lemma* times_cont_mdiff_within_at.mono
- \- *lemma* times_cont_mdiff_at.times_cont_mdiff_within_at
- \- *lemma* times_cont_mdiff_on.mono
- \- *lemma* times_cont_mdiff.times_cont_mdiff_on
- \- *lemma* times_cont_mdiff_within_at_inter'
- \- *lemma* times_cont_mdiff_within_at_inter
- \- *lemma* times_cont_mdiff_within_at.times_cont_mdiff_at
- \- *lemma* times_cont_mdiff_on_ext_chart_at
- \- *lemma* times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds
- \- *lemma* times_cont_mdiff_at_iff_times_cont_mdiff_on_nhds
- \- *lemma* times_cont_mdiff_within_at.congr
- \- *lemma* times_cont_mdiff_within_at_congr
- \- *lemma* times_cont_mdiff_within_at.congr_of_eventually_eq
- \- *lemma* filter.eventually_eq.times_cont_mdiff_within_at_iff
- \- *lemma* times_cont_mdiff_at.congr_of_eventually_eq
- \- *lemma* filter.eventually_eq.times_cont_mdiff_at_iff
- \- *lemma* times_cont_mdiff_on.congr
- \- *lemma* times_cont_mdiff_on_congr
- \- *lemma* times_cont_mdiff_on_of_locally_times_cont_mdiff_on
- \- *lemma* times_cont_mdiff_of_locally_times_cont_mdiff_on
- \- *lemma* times_cont_mdiff_within_at.comp
- \- *lemma* times_cont_mdiff_on.comp
- \- *lemma* times_cont_mdiff_on.comp'
- \- *lemma* times_cont_mdiff.comp
- \- *lemma* times_cont_mdiff_within_at.comp'
- \- *lemma* times_cont_mdiff_at.comp_times_cont_mdiff_within_at
- \- *lemma* times_cont_mdiff_at.comp
- \- *lemma* times_cont_mdiff.comp_times_cont_mdiff_on
- \- *lemma* times_cont_mdiff_on_of_mem_maximal_atlas
- \- *lemma* times_cont_mdiff_on_symm_of_mem_maximal_atlas
- \- *lemma* times_cont_mdiff_on_chart
- \- *lemma* times_cont_mdiff_on_chart_symm
- \- *lemma* times_cont_mdiff_id
- \+/\- *lemma* smooth_id
- \- *lemma* times_cont_mdiff_on_id
- \+/\- *lemma* smooth_on_id
- \- *lemma* times_cont_mdiff_at_id
- \+/\- *lemma* smooth_at_id
- \- *lemma* times_cont_mdiff_within_at_id
- \+/\- *lemma* smooth_within_at_id
- \- *lemma* times_cont_mdiff_const
- \- *lemma* times_cont_mdiff_one
- \+/\- *lemma* smooth_const
- \- *lemma* times_cont_mdiff_on_const
- \- *lemma* times_cont_mdiff_on_one
- \- *lemma* times_cont_mdiff_at_const
- \- *lemma* times_cont_mdiff_at_one
- \- *lemma* times_cont_mdiff_within_at_const
- \- *lemma* times_cont_mdiff_within_at_one
- \- *lemma* times_cont_mdiff_of_support
- \- *lemma* times_cont_mdiff_within_at_iff_times_cont_diff_within_at
- \- *lemma* times_cont_mdiff_at_iff_times_cont_diff_at
- \- *lemma* times_cont_mdiff_on_iff_times_cont_diff_on
- \- *lemma* times_cont_mdiff_iff_times_cont_diff
- \- *lemma* times_cont_mdiff_on.continuous_on_tangent_map_within_aux
- \- *lemma* times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within_aux
- \- *lemma* times_cont_mdiff_proj
- \- *lemma* times_cont_mdiff_on_proj
- \- *lemma* times_cont_mdiff_at_proj
- \- *lemma* times_cont_mdiff_within_at_proj
- \- *lemma* times_cont_mdiff_proj
- \- *lemma* times_cont_mdiff_on_proj
- \- *lemma* times_cont_mdiff_at_proj
- \- *lemma* times_cont_mdiff_within_at_proj
- \- *lemma* times_cont_mdiff_within_at.prod_mk
- \- *lemma* times_cont_mdiff_within_at.prod_mk_space
- \- *lemma* times_cont_mdiff_at.prod_mk
- \- *lemma* times_cont_mdiff_at.prod_mk_space
- \- *lemma* times_cont_mdiff_on.prod_mk
- \- *lemma* times_cont_mdiff_on.prod_mk_space
- \- *lemma* times_cont_mdiff.prod_mk
- \- *lemma* times_cont_mdiff.prod_mk_space
- \- *lemma* times_cont_mdiff_within_at_fst
- \- *lemma* times_cont_mdiff_at_fst
- \- *lemma* times_cont_mdiff_on_fst
- \- *lemma* times_cont_mdiff_fst
- \- *lemma* times_cont_mdiff_within_at_snd
- \- *lemma* times_cont_mdiff_at_snd
- \- *lemma* times_cont_mdiff_on_snd
- \- *lemma* times_cont_mdiff_snd
- \- *lemma* times_cont_mdiff_within_at.prod_map'
- \- *lemma* times_cont_mdiff_within_at.prod_map
- \- *lemma* times_cont_mdiff_at.prod_map
- \- *lemma* times_cont_mdiff_at.prod_map'
- \- *lemma* times_cont_mdiff_on.prod_map
- \- *lemma* times_cont_mdiff.prod_map
- \- *lemma* times_cont_mdiff_within_at_pi_space
- \- *lemma* times_cont_mdiff_on_pi_space
- \- *lemma* times_cont_mdiff_at_pi_space
- \- *lemma* times_cont_mdiff_pi_space
- \- *lemma* continuous_linear_map.times_cont_mdiff
- \+ *theorem* cont_mdiff_on.cont_mdiff_on_tangent_map_within
- \+ *theorem* cont_mdiff_on.continuous_on_tangent_map_within
- \+ *theorem* cont_mdiff.cont_mdiff_tangent_map
- \+ *theorem* cont_mdiff.continuous_tangent_map
- \- *theorem* times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within
- \- *theorem* times_cont_mdiff_on.continuous_on_tangent_map_within
- \- *theorem* times_cont_mdiff.times_cont_mdiff_tangent_map
- \- *theorem* times_cont_mdiff.continuous_tangent_map
- \+ *def* cont_diff_within_at_prop
- \+ *def* cont_mdiff_within_at
- \+ *def* cont_mdiff_at
- \+/\- *def* smooth_at
- \+ *def* cont_mdiff_on
- \+/\- *def* smooth_on
- \+ *def* cont_mdiff
- \+/\- *def* smooth
- \- *def* times_cont_diff_within_at_prop
- \- *def* times_cont_mdiff_within_at
- \- *def* times_cont_mdiff_at
- \+/\- *def* smooth_at
- \- *def* times_cont_mdiff_on
- \+/\- *def* smooth_on
- \- *def* times_cont_mdiff
- \+/\- *def* smooth

renamed src/geometry/manifold/times_cont_mdiff_map.lean to src/geometry/manifold/cont_mdiff_map.lean
- \+/\- *lemma* coe_fn_mk
- \+/\- *lemma* coe_fn_mk
- \+/\- *def* smooth_map
- \+/\- *def* id
- \+/\- *def* const
- \+/\- *def* smooth_map
- \+/\- *def* id
- \+/\- *def* const

modified src/geometry/manifold/derivation_bundle.lean

modified src/geometry/manifold/diffeomorph.lean
- \+ *lemma* cont_mdiff_within_at_comp_diffeomorph_iff
- \+ *lemma* cont_mdiff_on_comp_diffeomorph_iff
- \+ *lemma* cont_mdiff_at_comp_diffeomorph_iff
- \+ *lemma* cont_mdiff_comp_diffeomorph_iff
- \+ *lemma* cont_mdiff_within_at_diffeomorph_comp_iff
- \+ *lemma* cont_mdiff_at_diffeomorph_comp_iff
- \+ *lemma* cont_mdiff_on_diffeomorph_comp_iff
- \+ *lemma* cont_mdiff_diffeomorph_comp_iff
- \+ *lemma* cont_mdiff_within_at_trans_diffeomorph_right
- \+ *lemma* cont_mdiff_at_trans_diffeomorph_right
- \+ *lemma* cont_mdiff_on_trans_diffeomorph_right
- \+ *lemma* cont_mdiff_trans_diffeomorph_right
- \+ *lemma* cont_mdiff_within_at_trans_diffeomorph_left
- \+ *lemma* cont_mdiff_at_trans_diffeomorph_left
- \+ *lemma* cont_mdiff_on_trans_diffeomorph_left
- \+ *lemma* cont_mdiff_trans_diffeomorph_left
- \- *lemma* times_cont_mdiff_within_at_comp_diffeomorph_iff
- \- *lemma* times_cont_mdiff_on_comp_diffeomorph_iff
- \- *lemma* times_cont_mdiff_at_comp_diffeomorph_iff
- \- *lemma* times_cont_mdiff_comp_diffeomorph_iff
- \- *lemma* times_cont_mdiff_within_at_diffeomorph_comp_iff
- \- *lemma* times_cont_mdiff_at_diffeomorph_comp_iff
- \- *lemma* times_cont_mdiff_on_diffeomorph_comp_iff
- \- *lemma* times_cont_mdiff_diffeomorph_comp_iff
- \- *lemma* times_cont_mdiff_within_at_trans_diffeomorph_right
- \- *lemma* times_cont_mdiff_at_trans_diffeomorph_right
- \- *lemma* times_cont_mdiff_on_trans_diffeomorph_right
- \- *lemma* times_cont_mdiff_trans_diffeomorph_right
- \- *lemma* times_cont_mdiff_within_at_trans_diffeomorph_left
- \- *lemma* times_cont_mdiff_at_trans_diffeomorph_left
- \- *lemma* times_cont_mdiff_on_trans_diffeomorph_left
- \- *lemma* times_cont_mdiff_trans_diffeomorph_left

modified src/geometry/manifold/instances/real.lean

modified src/geometry/manifold/instances/sphere.lean
- \+ *lemma* cont_diff_on_stereo_to_fun
- \+ *lemma* cont_diff_stereo_inv_fun_aux
- \+ *lemma* cont_mdiff_coe_sphere
- \+ *lemma* cont_mdiff.cod_restrict_sphere
- \+ *lemma* cont_mdiff_neg_sphere
- \+ *lemma* cont_mdiff_exp_map_circle
- \- *lemma* times_cont_diff_on_stereo_to_fun
- \- *lemma* times_cont_diff_stereo_inv_fun_aux
- \- *lemma* times_cont_mdiff_coe_sphere
- \- *lemma* times_cont_mdiff.cod_restrict_sphere
- \- *lemma* times_cont_mdiff_neg_sphere
- \- *lemma* times_cont_mdiff_exp_map_circle

modified src/geometry/manifold/instances/units_of_normed_algebra.lean

modified src/geometry/manifold/mfderiv.lean

modified src/geometry/manifold/partition_of_unity.lean

modified src/geometry/manifold/smooth_manifold_with_corners.lean
- \+ *lemma* cont_diff_groupoid_le
- \+ *lemma* cont_diff_groupoid_zero_eq
- \+ *lemma* of_set_mem_cont_diff_groupoid
- \+ *lemma* symm_trans_mem_cont_diff_groupoid
- \+ *lemma* cont_diff_groupoid_prod
- \+ *lemma* smooth_manifold_with_corners_of_cont_diff_on
- \- *lemma* times_cont_diff_groupoid_le
- \- *lemma* times_cont_diff_groupoid_zero_eq
- \- *lemma* of_set_mem_times_cont_diff_groupoid
- \- *lemma* symm_trans_mem_times_cont_diff_groupoid
- \- *lemma* times_cont_diff_groupoid_prod
- \- *lemma* smooth_manifold_with_corners_of_times_cont_diff_on
- \+ *def* cont_diff_groupoid
- \+/\- *def* maximal_atlas
- \- *def* times_cont_diff_groupoid
- \+/\- *def* maximal_atlas

modified src/geometry/manifold/whitney_embedding.lean

modified src/measure_theory/integral/circle_integral.lean

modified src/topology/metric_space/hausdorff_dimension.lean
- \+ *lemma* cont_diff_on.dimH_image_le
- \+ *lemma* cont_diff.dimH_range_le
- \+ *lemma* cont_diff_on.dense_compl_image_of_dimH_lt_finrank
- \+ *lemma* cont_diff.dense_compl_range_of_finrank_lt_finrank
- \- *lemma* times_cont_diff_on.dimH_image_le
- \- *lemma* times_cont_diff.dimH_range_le
- \- *lemma* times_cont_diff_on.dense_compl_image_of_dimH_lt_finrank
- \- *lemma* times_cont_diff.dense_compl_range_of_finrank_lt_finrank



## [2022-02-23 00:45:54](https://github.com/leanprover-community/mathlib/commit/541a1a0)
refactor(combinatorics/simple_graph/{basic,degree_sum}): move darts from degree_sum to basic ([#12195](https://github.com/leanprover-community/mathlib/pull/12195))
This also changes `simple_graph.dart` to extend `prod`, so that darts are even closer to being an ordered pair.
Since this touches the module docstrings, they are updated to use fully qualified names.
#### Estimated changes
modified src/combinatorics/simple_graph/basic.lean
- \+ *lemma* adj.symm
- \+ *lemma* dart.edge_mk
- \+ *lemma* dart.edge_mem
- \+ *lemma* dart.symm_mk
- \+ *lemma* dart.edge_symm
- \+ *lemma* dart.symm_symm
- \+ *lemma* dart.symm_involutive
- \+ *lemma* dart.symm_ne
- \+ *lemma* dart_edge_eq_iff
- \+ *lemma* dart_of_neighbor_set_injective
- \+ *def* dart.edge
- \+ *def* dart.symm
- \+ *def* dart_of_neighbor_set

modified src/combinatorics/simple_graph/degree_sum.lean
- \- *lemma* dart.edge_mem
- \- *lemma* dart.rev_edge
- \- *lemma* dart.rev_rev
- \- *lemma* dart.rev_involutive
- \- *lemma* dart.rev_ne
- \- *lemma* dart_edge_eq_iff
- \- *lemma* dart_of_neighbor_set_injective
- \- *def* dart.edge
- \- *def* dart.rev
- \- *def* dart_of_neighbor_set

modified src/data/sym/sym2.lean
- \+ *lemma* mk_prod_swap_eq
- \+ *lemma* mk_eq_mk_iff



## [2022-02-23 00:45:53](https://github.com/leanprover-community/mathlib/commit/f6ec999)
feat(ring_theory/localization): add a fintype instance ([#12150](https://github.com/leanprover-community/mathlib/pull/12150))
#### Estimated changes
modified src/ring_theory/localization/basic.lean



## [2022-02-22 22:49:03](https://github.com/leanprover-community/mathlib/commit/e89222a)
feat(algebra/module,linear_algebra): some `restrict_scalars` lemmas ([#12181](https://github.com/leanprover-community/mathlib/pull/12181))
 * add `linear_map.coe_restrict_scalars` (demoting `linear_map.restrict_scalars_apply` from `simp` lemma)
 * add `submodule.restrict_scalars_eq_top_iff`
#### Estimated changes
modified src/algebra/module/linear_map.lean
- \+ *lemma* coe_restrict_scalars
- \+ *lemma* restrict_scalars_apply

modified src/algebra/module/submodule_lattice.lean
- \+ *lemma* restrict_scalars_eq_bot_iff
- \+ *lemma* restrict_scalars_eq_top_iff



## [2022-02-22 22:49:02](https://github.com/leanprover-community/mathlib/commit/2ab3e2f)
feat(algebra/group/{hom,prod}): has_mul and mul_hom.prod ([#12110](https://github.com/leanprover-community/mathlib/pull/12110))
Ported over from `monoid_hom`.
#### Estimated changes
modified src/algebra/group/hom.lean
- \+ *lemma* mul_apply
- \+ *lemma* mul_comp
- \+ *lemma* comp_mul

modified src/algebra/group/pi.lean
- \+ *lemma* coe_mul

modified src/algebra/group/prod.lean
- \+ *lemma* coe_fst
- \+ *lemma* coe_snd
- \+ *lemma* coe_prod
- \+ *lemma* prod_apply
- \+ *lemma* fst_comp_prod
- \+ *lemma* snd_comp_prod
- \+ *lemma* prod_unique
- \+ *lemma* prod_map_def
- \+ *lemma* coe_prod_map
- \+ *lemma* prod_comp_prod_map
- \+ *lemma* coprod_apply
- \+ *lemma* comp_coprod
- \+ *def* fst
- \+ *def* snd
- \+ *def* prod_map
- \+ *def* coprod



## [2022-02-22 22:49:01](https://github.com/leanprover-community/mathlib/commit/18d1bdf)
feat(topology/algebra/group): add subgroup lemmas ([#12026](https://github.com/leanprover-community/mathlib/pull/12026))
#### Estimated changes
modified src/topology/algebra/group.lean
- \+ *lemma* topological_group.continuous_conj
- \+ *lemma* subgroup.is_normal_topological_closure
- \+ *lemma* mul_mem_connected_component_one
- \+ *lemma* inv_mem_connected_component_one
- \+ *def* subgroup.connected_component_of_one



## [2022-02-22 22:49:00](https://github.com/leanprover-community/mathlib/commit/b60b790)
feat(topology/algebra/group): add continuity lemmas ([#11975](https://github.com/leanprover-community/mathlib/pull/11975))
#### Estimated changes
modified src/topology/algebra/uniform_group.lean
- \+ *lemma* uniform_group.uniform_continuous_iff_open_ker



## [2022-02-22 21:10:39](https://github.com/leanprover-community/mathlib/commit/64c8d21)
feat(set_theory/ordinal): `Inf_empty` ([#12226](https://github.com/leanprover-community/mathlib/pull/12226))
The docs mention that `Inf Ø` is defined as `0`. We prove that this is indeed the case.
#### Estimated changes
modified src/set_theory/ordinal.lean
- \+ *theorem* Inf_empty



## [2022-02-22 21:10:38](https://github.com/leanprover-community/mathlib/commit/d990681)
docs(set_theory/ordinal): Remove mention of `omin` from docs ([#12224](https://github.com/leanprover-community/mathlib/pull/12224))
[#11867](https://github.com/leanprover-community/mathlib/pull/11867) replaced `omin` by `Inf`. We remove all mentions of it from the docs.
#### Estimated changes
modified src/set_theory/ordinal.lean



## [2022-02-22 21:10:37](https://github.com/leanprover-community/mathlib/commit/f7b6f42)
feat(set_theory/ordinal_arithmetic): `out_nonempty_iff_ne_zero` ([#12223](https://github.com/leanprover-community/mathlib/pull/12223))
#### Estimated changes
modified src/set_theory/ordinal.lean
- \+ *theorem* out_nonempty_iff_ne_zero



## [2022-02-22 21:10:36](https://github.com/leanprover-community/mathlib/commit/e50ebde)
chore(analysis/specific_limits): simplify proof of `cauchy_series_of_le_geometric` ([#12215](https://github.com/leanprover-community/mathlib/pull/12215))
This lemma is identical to the one above except over `range (n + 1)`
instead of `range n`. Perhaps it could be removed entirely? I'm not sure what the policy is on breaking changes.
#### Estimated changes
modified src/analysis/specific_limits.lean



## [2022-02-22 21:10:34](https://github.com/leanprover-community/mathlib/commit/48ddfd5)
chore(linear_algebra/basic): golf `linear_equiv.smul_of_unit` ([#12190](https://github.com/leanprover-community/mathlib/pull/12190))
This already exists more generally as `distrib_mul_action.to_linear_equiv`.
The name is probably more discoverable and it needs fewer arguments, so I've left it around for now.
#### Estimated changes
modified src/linear_algebra/basic.lean

modified src/linear_algebra/finite_dimensional.lean



## [2022-02-22 20:21:17](https://github.com/leanprover-community/mathlib/commit/6bb8f22)
refactor(model_theory/terms_and_formulas): Improvements to basics of first-order formulas ([#12091](https://github.com/leanprover-community/mathlib/pull/12091))
Improves the simp set of lemmas related to `realize_bounded_formula` and `realize_formula`, so that they simplify higher-level definitions directly, and keep bounded formulas and formulas separate.
Generalizes relabelling of bounded formulas.
Defines `close_with_exists` and `close_with_forall` to quantify bounded formulas into closed formulas.
Defines `bd_iff` and `iff`.
#### Estimated changes
modified src/model_theory/basic.lean

modified src/model_theory/definability.lean

modified src/model_theory/direct_limit.lean

modified src/model_theory/elementary_maps.lean
- \+/\- *lemma* map_formula
- \+/\- *lemma* realize_term_substructure
- \+/\- *lemma* realize_bounded_formula_top
- \+ *lemma* realize_formula_top
- \+/\- *lemma* map_formula
- \+/\- *lemma* realize_term_substructure
- \+/\- *lemma* realize_bounded_formula_top

modified src/model_theory/quotients.lean
- \+ *lemma* term.realize_quotient_mk
- \- *lemma* realize_term_quotient_mk

modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* realize_relabel
- \+/\- *lemma* hom.realize_term
- \+/\- *lemma* embedding.realize_term
- \+/\- *lemma* equiv.realize_term
- \+ *lemma* sum_elim_comp_relabel_aux
- \+ *lemma* realize_bot
- \+/\- *lemma* realize_not
- \+ *lemma* realize_bd_equal
- \+ *lemma* realize_top
- \+/\- *lemma* realize_inf
- \+/\- *lemma* realize_imp
- \+ *lemma* realize_rel
- \+ *lemma* realize_sup
- \+ *lemma* realize_all
- \+ *lemma* realize_ex
- \+ *lemma* realize_iff
- \+ *lemma* realize_relabel
- \+/\- *lemma* realize_not
- \+ *lemma* realize_bot
- \+ *lemma* realize_top
- \+/\- *lemma* realize_inf
- \+/\- *lemma* realize_imp
- \+ *lemma* realize_rel
- \+ *lemma* realize_sup
- \+ *lemma* realize_iff
- \+ *lemma* realize_relabel
- \+/\- *lemma* realize_equal
- \+/\- *lemma* realize_graph
- \+ *lemma* realize_alls
- \+ *lemma* realize_exs
- \+/\- *lemma* equiv.realize_bounded_formula
- \+ *lemma* equiv.realize_formula
- \+/\- *lemma* is_satisfiable.some_model_models
- \+/\- *lemma* model.is_satisfiable
- \+/\- *lemma* is_satisfiable.mono
- \+/\- *lemma* is_satisfiable.is_finitely_satisfiable
- \+/\- *lemma* models_formula_iff
- \+/\- *lemma* models_sentence_iff
- \+ *lemma* semantically_equivalent.realize_bd_iff
- \+ *lemma* semantically_equivalent.some_model_realize_bd_iff
- \+ *lemma* semantically_equivalent.realize_iff
- \+ *lemma* semantically_equivalent.some_model_realize_iff
- \+/\- *lemma* semantically_equivalent_not_not
- \+/\- *lemma* imp_semantically_equivalent_not_sup
- \+/\- *lemma* sup_semantically_equivalent_not_inf_not
- \+/\- *lemma* inf_semantically_equivalent_not_sup_not
- \+/\- *lemma* semantically_equivalent_not_not
- \+/\- *lemma* imp_semantically_equivalent_not_sup
- \+/\- *lemma* sup_semantically_equivalent_not_inf_not
- \+/\- *lemma* inf_semantically_equivalent_not_sup_not
- \- *lemma* realize_term_relabel
- \+/\- *lemma* hom.realize_term
- \+/\- *lemma* embedding.realize_term
- \+/\- *lemma* equiv.realize_term
- \+/\- *lemma* realize_not
- \+/\- *lemma* realize_inf
- \+/\- *lemma* realize_imp
- \- *lemma* realize_bounded_formula_relabel
- \+/\- *lemma* equiv.realize_bounded_formula
- \- *lemma* realize_formula_relabel
- \- *lemma* realize_formula_equiv
- \+/\- *lemma* realize_equal
- \+/\- *lemma* realize_graph
- \+/\- *lemma* is_satisfiable.some_model_models
- \+/\- *lemma* model.is_satisfiable
- \+/\- *lemma* is_satisfiable.mono
- \+/\- *lemma* is_satisfiable.is_finitely_satisfiable
- \+/\- *lemma* models_formula_iff
- \+/\- *lemma* models_sentence_iff
- \- *lemma* semantically_equivalent.realize_eq
- \- *lemma* semantically_equivalent.some_model_realize_eq
- \+/\- *lemma* semantically_equivalent_not_not
- \+/\- *lemma* imp_semantically_equivalent_not_sup
- \+/\- *lemma* sup_semantically_equivalent_not_inf_not
- \+/\- *lemma* inf_semantically_equivalent_not_sup_not
- \+ *def* relabel
- \+ *def* realize
- \+/\- *def* formula
- \+/\- *def* sentence
- \+ *def* relations.bounded_formula
- \+ *def* term.bd_equal
- \+ *def* relations.formula
- \+ *def* term.equal
- \+ *def* relabel_aux
- \+ *def* relabel
- \+ *def* alls
- \+ *def* exs
- \+ *def* realize
- \+ *def* relabel
- \+ *def* realize
- \+/\- *def* is_satisfiable
- \+/\- *def* is_finitely_satisfiable
- \+/\- *def* is_satisfiable.some_model
- \+/\- *def* models_bounded_formula
- \- *def* term.relabel
- \- *def* realize_term
- \+/\- *def* formula
- \+/\- *def* sentence
- \- *def* bd_not
- \- *def* bounded_formula.relabel
- \- *def* equal
- \- *def* realize_bounded_formula
- \- *def* realize_formula
- \+/\- *def* is_satisfiable
- \+/\- *def* is_finitely_satisfiable
- \+/\- *def* is_satisfiable.some_model
- \+/\- *def* models_bounded_formula



## [2022-02-22 18:15:35](https://github.com/leanprover-community/mathlib/commit/d054fca)
feat(/analysis/inner_product_space/pi_L2): `inner_matrix_row_row` ([#12177](https://github.com/leanprover-community/mathlib/pull/12177))
The inner product between rows/columns of matrices.
#### Estimated changes
modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* inner_matrix_row_row
- \+ *lemma* inner_matrix_col_col



## [2022-02-22 18:15:34](https://github.com/leanprover-community/mathlib/commit/d0c37a1)
feat(analysis/inner_product_space/adjoint): is_self_adjoint_iff_inner… ([#12113](https://github.com/leanprover-community/mathlib/pull/12113))
…_map_self_real
A linear operator on a complex inner product space is self-adjoint
precisely when ⟪T v, v⟫ is real for all v.  I am interested in learning
style improvements!
#### Estimated changes
modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* inner_map_polarization'
- \+ *lemma* is_self_adjoint_iff_inner_map_self_real



## [2022-02-22 18:15:32](https://github.com/leanprover-community/mathlib/commit/8f16001)
chore(*): rename `erase_dup` to `dedup` ([#12057](https://github.com/leanprover-community/mathlib/pull/12057))
#### Estimated changes
modified src/algebra/big_operators/basic.lean

modified src/algebra/gcd_monoid/multiset.lean
- \+ *lemma* lcm_dedup
- \+ *lemma* gcd_dedup
- \- *lemma* lcm_erase_dup
- \- *lemma* gcd_erase_dup

modified src/algebra/squarefree.lean

modified src/data/fin_enum.lean

modified src/data/finset/basic.lean
- \+/\- *lemma* mem_to_finset
- \+/\- *lemma* mem_to_finset
- \+ *lemma* to_finset_eq_iff_perm_dedup
- \+/\- *lemma* mem_to_finset
- \+/\- *lemma* mem_to_finset
- \- *lemma* to_finset_eq_iff_perm_erase_dup
- \+ *theorem* dedup_eq_self
- \+/\- *theorem* insert_val'
- \+/\- *theorem* to_finset_val
- \+/\- *theorem* to_finset_val
- \+/\- *theorem* image_val
- \- *theorem* erase_dup_eq_self
- \+/\- *theorem* insert_val'
- \+/\- *theorem* to_finset_val
- \+/\- *theorem* to_finset_val
- \+/\- *theorem* image_val
- \+/\- *def* to_finset
- \+/\- *def* to_finset

modified src/data/finset/card.lean
- \+/\- *lemma* multiset.card_to_finset
- \+/\- *lemma* multiset.to_finset_card_le
- \+/\- *lemma* list.card_to_finset
- \+/\- *lemma* multiset.card_to_finset
- \+/\- *lemma* multiset.to_finset_card_le
- \+/\- *lemma* list.card_to_finset

modified src/data/finset/noncomm_prod.lean

modified src/data/finset/pi.lean

modified src/data/list/alist.lean

created src/data/list/dedup.lean
- \+ *theorem* dedup_nil
- \+ *theorem* dedup_cons_of_mem'
- \+ *theorem* dedup_cons_of_not_mem'
- \+ *theorem* mem_dedup
- \+ *theorem* dedup_cons_of_mem
- \+ *theorem* dedup_cons_of_not_mem
- \+ *theorem* dedup_sublist
- \+ *theorem* dedup_subset
- \+ *theorem* subset_dedup
- \+ *theorem* nodup_dedup
- \+ *theorem* dedup_eq_self
- \+ *theorem* dedup_idempotent
- \+ *theorem* dedup_append

modified src/data/list/default.lean

modified src/data/list/defs.lean
- \+ *def* dedup
- \- *def* erase_dup

deleted src/data/list/erase_dup.lean
- \- *theorem* erase_dup_nil
- \- *theorem* erase_dup_cons_of_mem'
- \- *theorem* erase_dup_cons_of_not_mem'
- \- *theorem* mem_erase_dup
- \- *theorem* erase_dup_cons_of_mem
- \- *theorem* erase_dup_cons_of_not_mem
- \- *theorem* erase_dup_sublist
- \- *theorem* erase_dup_subset
- \- *theorem* subset_erase_dup
- \- *theorem* nodup_erase_dup
- \- *theorem* erase_dup_eq_self
- \- *theorem* erase_dup_idempotent
- \- *theorem* erase_dup_append

modified src/data/list/perm.lean
- \+ *theorem* perm.dedup
- \- *theorem* perm.erase_dup

modified src/data/list/sigma.lean
- \+ *lemma* dedupkeys_cons
- \+ *lemma* nodupkeys_dedupkeys
- \+ *lemma* lookup_dedupkeys
- \+ *lemma* sizeof_dedupkeys
- \- *lemma* erase_dupkeys_cons
- \- *lemma* nodupkeys_erase_dupkeys
- \- *lemma* lookup_erase_dupkeys
- \- *lemma* sizeof_erase_dupkeys
- \+ *def* dedupkeys
- \- *def* erase_dupkeys

created src/data/multiset/dedup.lean
- \+ *lemma* dedup_nsmul
- \+ *lemma* nodup.le_dedup_iff_le
- \+ *lemma* multiset.nodup.le_nsmul_iff_le
- \+ *theorem* coe_dedup
- \+ *theorem* dedup_zero
- \+ *theorem* mem_dedup
- \+ *theorem* dedup_cons_of_mem
- \+ *theorem* dedup_cons_of_not_mem
- \+ *theorem* dedup_le
- \+ *theorem* dedup_subset
- \+ *theorem* subset_dedup
- \+ *theorem* dedup_subset'
- \+ *theorem* subset_dedup'
- \+ *theorem* nodup_dedup
- \+ *theorem* dedup_eq_self
- \+ *theorem* dedup_eq_zero
- \+ *theorem* dedup_singleton
- \+ *theorem* le_dedup
- \+ *theorem* dedup_ext
- \+ *theorem* dedup_map_dedup_eq
- \+ *def* dedup

modified src/data/multiset/default.lean

deleted src/data/multiset/erase_dup.lean
- \- *lemma* erase_dup_nsmul
- \- *lemma* nodup.le_erase_dup_iff_le
- \- *lemma* multiset.nodup.le_nsmul_iff_le
- \- *theorem* coe_erase_dup
- \- *theorem* erase_dup_zero
- \- *theorem* mem_erase_dup
- \- *theorem* erase_dup_cons_of_mem
- \- *theorem* erase_dup_cons_of_not_mem
- \- *theorem* erase_dup_le
- \- *theorem* erase_dup_subset
- \- *theorem* subset_erase_dup
- \- *theorem* erase_dup_subset'
- \- *theorem* subset_erase_dup'
- \- *theorem* nodup_erase_dup
- \- *theorem* erase_dup_eq_self
- \- *theorem* erase_dup_eq_zero
- \- *theorem* erase_dup_singleton
- \- *theorem* le_erase_dup
- \- *theorem* erase_dup_ext
- \- *theorem* erase_dup_map_erase_dup_eq
- \- *def* erase_dup

modified src/data/multiset/finset_ops.lean
- \+ *theorem* dedup_cons
- \+ *theorem* dedup_add
- \- *theorem* erase_dup_cons
- \- *theorem* erase_dup_add

modified src/data/multiset/fold.lean
- \+ *theorem* fold_dedup_idem
- \+ *theorem* le_smul_dedup
- \- *theorem* fold_erase_dup_idem
- \- *theorem* le_smul_erase_dup

modified src/data/multiset/lattice.lean
- \+ *lemma* sup_dedup
- \+ *lemma* inf_dedup
- \- *lemma* sup_erase_dup
- \- *lemma* inf_erase_dup

modified src/data/multiset/locally_finite.lean

modified src/data/nat/interval.lean

modified src/field_theory/finite/basic.lean

modified src/group_theory/perm/concrete_cycle.lean

modified src/group_theory/perm/cycle_type.lean

modified src/group_theory/perm/list.lean

modified src/number_theory/arithmetic_function.lean

modified src/ring_theory/norm.lean

modified src/ring_theory/roots_of_unity.lean

modified src/ring_theory/trace.lean

modified src/tactic/core.lean

modified src/tactic/simps.lean

modified src/tactic/where.lean

modified src/testing/slim_check/functions.lean



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
modified src/analysis/fourier.lean
- \+/\- *def* haar_circle
- \+/\- *def* haar_circle

modified src/measure_theory/measure/content.lean
- \+/\- *lemma* mono
- \+/\- *lemma* sup_disjoint
- \+/\- *lemma* le_inner_content
- \+/\- *lemma* inner_content_le
- \+/\- *lemma* le_outer_measure_compacts
- \+/\- *lemma* outer_measure_interior_compacts
- \+/\- *lemma* mono
- \+/\- *lemma* sup_disjoint
- \+/\- *lemma* le_inner_content
- \+/\- *lemma* inner_content_le
- \+/\- *lemma* le_outer_measure_compacts
- \+/\- *lemma* outer_measure_interior_compacts
- \+/\- *def* inner_content
- \+/\- *def* inner_content

modified src/measure_theory/measure/haar.lean
- \+/\- *lemma* prehaar_empty
- \+/\- *lemma* prehaar_mem_haar_product
- \+/\- *lemma* chaar_mem_haar_product
- \+/\- *lemma* chaar_self
- \+/\- *lemma* chaar_mono
- \+/\- *lemma* haar_content_self
- \+/\- *lemma* haar_measure_self
- \+/\- *lemma* prehaar_empty
- \+/\- *lemma* prehaar_mem_haar_product
- \+/\- *lemma* chaar_mem_haar_product
- \+/\- *lemma* chaar_self
- \+/\- *lemma* chaar_mono
- \+/\- *lemma* haar_content_self
- \+/\- *lemma* haar_measure_self
- \+/\- *def* prehaar
- \+/\- *def* haar
- \+/\- *def* prehaar
- \+/\- *def* haar

modified src/measure_theory/measure/haar_lebesgue.lean
- \- *def* topological_space.positive_compacts.Icc01
- \- *def* topological_space.positive_compacts.pi_Icc01

modified src/measure_theory/measure/haar_quotient.lean

modified src/topology/algebra/group.lean

modified src/topology/compacts.lean
- \+ *lemma* closed
- \+ *lemma* coe_mk
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* compact
- \+ *lemma* coe_mk
- \+ *lemma* coe_sup
- \+ *lemma* coe_inf
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_finset_sup
- \+ *lemma* coe_map
- \+ *lemma* compact
- \+ *lemma* coe_mk
- \+ *lemma* coe_sup
- \+ *lemma* coe_top
- \+ *lemma* compact
- \+ *lemma* interior_nonempty
- \+ *lemma* coe_mk
- \+ *lemma* coe_sup
- \+ *lemma* coe_top
- \- *lemma* positive_compacts_univ_val
- \- *lemma* bot_val
- \- *lemma* sup_val
- \- *lemma* finset_sup_val
- \- *lemma* map_val
- \+ *def* to_closeds
- \+ *def* to_nonempty_compacts
- \- *def* closeds
- \- *def* compacts
- \- *def* nonempty_compacts
- \- *def* positive_compacts:
- \- *def* positive_compacts_univ
- \- *def* nonempty_compacts.to_closeds

modified src/topology/metric_space/closeds.lean
- \+/\- *lemma* closeds.edist_eq
- \+/\- *lemma* lipschitz_inf_dist_set
- \+/\- *lemma* lipschitz_inf_dist
- \+/\- *lemma* closeds.edist_eq
- \+/\- *lemma* lipschitz_inf_dist_set
- \+/\- *lemma* lipschitz_inf_dist

modified src/topology/metric_space/gromov_hausdorff.lean
- \+/\- *lemma* eq_to_GH_space
- \+/\- *lemma* GH_space.to_GH_space_rep
- \+/\- *lemma* dist_GH_dist
- \+/\- *lemma* eq_to_GH_space
- \+/\- *lemma* GH_space.to_GH_space_rep
- \+/\- *lemma* dist_GH_dist
- \+ *def* GH_space.rep

modified src/topology/metric_space/kuratowski.lean



## [2022-02-22 15:16:21](https://github.com/leanprover-community/mathlib/commit/71da192)
chore(ring_theory/graded_algebra/basic): remove commutativity requirement ([#12208](https://github.com/leanprover-community/mathlib/pull/12208))
This wasn't used
#### Estimated changes
modified src/ring_theory/graded_algebra/basic.lean



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
modified src/algebra/category/CommRing/instances.lean

modified src/algebra/char_p/algebra.lean

modified src/algebraic_geometry/Spec.lean

modified src/algebraic_geometry/prime_spectrum/basic.lean

modified src/algebraic_geometry/structure_sheaf.lean

modified src/field_theory/ratfunc.lean

modified src/linear_algebra/matrix/to_linear_equiv.lean

modified src/number_theory/class_number/finite.lean

modified src/number_theory/function_field.lean

modified src/number_theory/number_field.lean

modified src/ring_theory/class_group.lean

created src/ring_theory/dedekind_domain/basic.lean
- \+ *lemma* dimension_le_one.principal_ideal_ring
- \+ *lemma* dimension_le_one.is_integral_closure
- \+ *lemma* dimension_le_one.integral_closure
- \+ *lemma* is_dedekind_domain_iff
- \+ *def* ring.dimension_le_one

created src/ring_theory/dedekind_domain/dvr.lean

renamed src/ring_theory/dedekind_domain.lean to src/ring_theory/dedekind_domain/ideal.lean
- \- *lemma* dimension_le_one.principal_ideal_ring
- \- *lemma* dimension_le_one.is_integral_closure
- \- *lemma* dimension_le_one.integral_closure
- \- *lemma* is_dedekind_domain_iff
- \- *lemma* is_integral_closure.range_le_span_dual_basis
- \- *lemma* integral_closure_le_span_dual_basis
- \- *lemma* exists_integral_multiples
- \- *lemma* finite_dimensional.exists_is_basis_integral
- \- *lemma* is_integral_closure.is_noetherian_ring
- \- *lemma* integral_closure.is_noetherian_ring
- \- *lemma* is_integral_closure.is_dedekind_domain
- \- *lemma* integral_closure.is_dedekind_domain
- \- *def* ring.dimension_le_one

created src/ring_theory/dedekind_domain/integral_closure.lean
- \+ *lemma* is_integral_closure.range_le_span_dual_basis
- \+ *lemma* integral_closure_le_span_dual_basis
- \+ *lemma* exists_integral_multiples
- \+ *lemma* finite_dimensional.exists_is_basis_integral
- \+ *lemma* is_integral_closure.is_noetherian_ring
- \+ *lemma* integral_closure.is_noetherian_ring
- \+ *lemma* is_integral_closure.is_dedekind_domain
- \+ *lemma* integral_closure.is_dedekind_domain

modified src/ring_theory/fractional_ideal.lean

modified src/ring_theory/ideal/over.lean

modified src/ring_theory/integrally_closed.lean

modified src/ring_theory/jacobson.lean

modified src/ring_theory/laurent_series.lean

modified src/ring_theory/local_properties.lean

deleted src/ring_theory/localization.lean
- \- *lemma* of_le
- \- *lemma* to_localization_map_to_map
- \- *lemma* to_localization_map_to_map_apply
- \- *lemma* is_integer_zero
- \- *lemma* is_integer_one
- \- *lemma* is_integer_add
- \- *lemma* is_integer_mul
- \- *lemma* is_integer_smul
- \- *lemma* exists_integer_multiple'
- \- *lemma* exists_integer_multiple
- \- *lemma* to_localization_map_sec
- \- *lemma* sec_spec
- \- *lemma* sec_spec'
- \- *lemma* exist_integer_multiples
- \- *lemma* exist_integer_multiples_of_fintype
- \- *lemma* exist_integer_multiples_of_finset
- \- *lemma* map_integer_multiple
- \- *lemma* finset_integer_multiple_image
- \- *lemma* map_right_cancel
- \- *lemma* map_left_cancel
- \- *lemma* eq_zero_of_fst_eq_zero
- \- *lemma* map_eq_zero_iff
- \- *lemma* mk'_sec
- \- *lemma* mk'_mul
- \- *lemma* mk'_one
- \- *lemma* mk'_spec
- \- *lemma* mk'_spec'
- \- *lemma* mk'_spec_mk
- \- *lemma* mk'_spec'_mk
- \- *lemma* mk'_surjective
- \- *lemma* mk'_eq_iff_eq
- \- *lemma* mk'_mem_iff
- \- *lemma* mk'_eq_zero_iff
- \- *lemma* eq_iff_eq
- \- *lemma* mk'_eq_iff_mk'_eq
- \- *lemma* mk'_eq_of_eq
- \- *lemma* mk'_self
- \- *lemma* mk'_self'
- \- *lemma* mk'_self''
- \- *lemma* mul_mk'_eq_mk'_of_mul
- \- *lemma* mk'_eq_mul_mk'_one
- \- *lemma* mk'_mul_cancel_left
- \- *lemma* mk'_mul_cancel_right
- \- *lemma* mk'_mul_mk'_eq_one
- \- *lemma* mk'_mul_mk'_eq_one'
- \- *lemma* is_unit_comp
- \- *lemma* eq_of_eq
- \- *lemma* mk'_add
- \- *lemma* lift_mk'
- \- *lemma* lift_mk'_spec
- \- *lemma* lift_eq
- \- *lemma* lift_eq_iff
- \- *lemma* lift_comp
- \- *lemma* lift_of_comp
- \- *lemma* monoid_hom_ext
- \- *lemma* ring_hom_ext
- \- *lemma* lift_unique
- \- *lemma* lift_id
- \- *lemma* lift_surjective_iff
- \- *lemma* lift_injective_iff
- \- *lemma* map_eq
- \- *lemma* map_comp
- \- *lemma* map_mk'
- \- *lemma* map_id
- \- *lemma* map_unique
- \- *lemma* map_comp_map
- \- *lemma* map_map
- \- *lemma* ring_equiv_of_ring_equiv_eq_map
- \- *lemma* ring_equiv_of_ring_equiv_eq
- \- *lemma* ring_equiv_of_ring_equiv_mk'
- \- *lemma* alg_equiv_mk'
- \- *lemma* alg_equiv_symm_mk'
- \- *lemma* is_localization_of_alg_equiv
- \- *lemma* is_localization_iff_of_alg_equiv
- \- *lemma* is_localization_iff_of_ring_equiv
- \- *lemma* is_localization_of_base_ring_equiv
- \- *lemma* is_localization_iff_of_base_ring_equiv
- \- *lemma* away_map.lift_eq
- \- *lemma* away_map.lift_comp
- \- *lemma* submonoid_map_le_is_unit
- \- *lemma* to_inv_submonoid_surjective
- \- *lemma* to_inv_submonoid_mul
- \- *lemma* mul_to_inv_submonoid
- \- *lemma* smul_to_inv_submonoid
- \- *lemma* surj'
- \- *lemma* to_inv_submonoid_eq_mk'
- \- *lemma* mem_inv_submonoid_iff_exists_mk'
- \- *lemma* span_inv_submonoid
- \- *lemma* finite_type_of_monoid_fg
- \- *lemma* non_zero_divisors_le_comap
- \- *lemma* map_non_zero_divisors_le
- \- *lemma* add_mk
- \- *lemma* add_mk_self
- \- *lemma* neg_mk
- \- *lemma* mk_zero
- \- *lemma* lift_on_zero
- \- *lemma* to_localization_map_eq_monoid_of
- \- *lemma* monoid_of_eq_algebra_map
- \- *lemma* mk_one_eq_algebra_map
- \- *lemma* mk_eq_mk'_apply
- \- *lemma* mk_eq_mk'
- \- *lemma* alg_equiv_mk'
- \- *lemma* alg_equiv_symm_mk'
- \- *lemma* alg_equiv_mk
- \- *lemma* alg_equiv_symm_mk
- \- *lemma* is_prime_iff_is_prime_disjoint
- \- *lemma* is_prime_of_is_prime_disjoint
- \- *lemma* surjective_quotient_map_of_maximal_of_localization
- \- *lemma* mem_localization_localization_submodule
- \- *lemma* localization_localization_map_units
- \- *lemma* localization_localization_surj
- \- *lemma* localization_localization_eq_iff_exists
- \- *lemma* localization_localization_is_localization
- \- *lemma* localization_localization_is_localization_of_has_all_units
- \- *lemma* is_localization_is_localization_at_prime_is_localization
- \- *lemma* localization_is_scalar_tower_of_submonoid_le
- \- *lemma* is_localization_of_submonoid_le
- \- *lemma* is_localization_of_is_exists_mul_mem
- \- *lemma* mem_coe_submodule
- \- *lemma* coe_submodule_mono
- \- *lemma* coe_submodule_bot
- \- *lemma* coe_submodule_top
- \- *lemma* coe_submodule_sup
- \- *lemma* coe_submodule_mul
- \- *lemma* coe_submodule_fg
- \- *lemma* coe_submodule_span
- \- *lemma* coe_submodule_span_singleton
- \- *lemma* map_smul
- \- *lemma* is_noetherian_ring
- \- *lemma* coeff_integer_normalization_of_not_mem_support
- \- *lemma* coeff_integer_normalization_mem_support
- \- *lemma* integer_normalization_coeff
- \- *lemma* integer_normalization_spec
- \- *lemma* integer_normalization_map_to_map
- \- *lemma* integer_normalization_eval₂_eq_zero
- \- *lemma* integer_normalization_aeval_eq_zero
- \- *lemma* to_map_eq_zero_iff
- \- *lemma* map_injective_of_injective
- \- *lemma* coe_submodule_le_coe_submodule
- \- *lemma* coe_submodule_strict_mono
- \- *lemma* coe_submodule_injective
- \- *lemma* coe_submodule_is_principal
- \- *lemma* is_unit_to_map_iff
- \- *lemma* to_map_mem_maximal_iff
- \- *lemma* is_unit_mk'_iff
- \- *lemma* mk'_mem_maximal_iff
- \- *lemma* at_prime.comap_maximal_ideal
- \- *lemma* at_prime.map_eq_maximal_ideal
- \- *lemma* le_comap_prime_compl_iff
- \- *lemma* local_ring_hom_to_map
- \- *lemma* local_ring_hom_mk'
- \- *lemma* local_ring_hom_unique
- \- *lemma* local_ring_hom_id
- \- *lemma* local_ring_hom_comp
- \- *lemma* localization_map_bijective_of_field
- \- *lemma* to_map_eq_zero_iff
- \- *lemma* coe_submodule_le_coe_submodule
- \- *lemma* coe_submodule_strict_mono
- \- *lemma* coe_submodule_injective
- \- *lemma* coe_submodule_is_principal
- \- *lemma* mk'_mk_eq_div
- \- *lemma* mk'_eq_div
- \- *lemma* div_surjective
- \- *lemma* is_unit_map_of_injective
- \- *lemma* lift_algebra_map
- \- *lemma* lift_mk'
- \- *lemma* integer_normalization_eq_zero_iff
- \- *lemma* is_algebraic_iff
- \- *lemma* comap_is_algebraic_iff
- \- *lemma* exists_reduced_fraction
- \- *lemma* num_denom_reduced
- \- *lemma* mk'_num_denom
- \- *lemma* num_mul_denom_eq_num_iff_eq
- \- *lemma* num_mul_denom_eq_num_iff_eq'
- \- *lemma* num_mul_denom_eq_num_mul_denom_iff_eq
- \- *lemma* eq_zero_of_num_eq_zero
- \- *lemma* is_integer_of_is_unit_denom
- \- *lemma* is_unit_denom_of_num_eq_zero
- \- *lemma* is_fraction_ring_iff_of_base_ring_equiv
- \- *lemma* is_fraction_ring_of_is_localization
- \- *lemma* nontrivial
- \- *lemma* is_fraction_ring_of_is_domain_of_is_localization
- \- *lemma* algebra_map_mk'
- \- *lemma* localization_algebra_injective
- \- *lemma* ring_hom.is_integral_elem_localization_at_leading_coeff
- \- *lemma* is_integral_localization'
- \- *lemma* is_fraction_ring_of_algebraic
- \- *lemma* is_fraction_ring_of_finite_extension
- \- *lemma* is_fraction_ring_of_algebraic
- \- *lemma* is_fraction_ring_of_finite_extension
- \- *lemma* mk_eq_div
- \- *lemma* is_algebraic_iff'
- \- *theorem* eq_mk'_iff_mul_eq
- \- *theorem* mk'_eq_iff_eq_mul
- \- *theorem* at_prime.local_ring
- \- *theorem* mem_map_algebra_map_iff
- \- *theorem* map_comap
- \- *theorem* comap_map_of_is_prime_disjoint
- \- *theorem* is_domain_of_le_non_zero_divisors
- \- *theorem* is_domain_localization
- \- *theorem* is_integral_localization_at_leading_coeff
- \- *theorem* is_integral_localization
- \- *def* to_localization_map
- \- *def* is_integer
- \- *def* common_denom
- \- *def* integer_multiple
- \- *def* common_denom_of_finset
- \- *def* finset_integer_multiple
- \- *def* map
- \- *def* inv_submonoid
- \- *def* to_inv_submonoid
- \- *def* prime_compl
- \- *def* order_embedding
- \- *def* order_iso_of_prime
- \- *def* at_units
- \- *def* at_unit
- \- *def* at_one
- \- *def* localization_localization_submodule
- \- *def* localization_localization_at_prime_iso_localization
- \- *def* localization_algebra_of_submonoid_le
- \- *def* coe_submodule
- \- *def* fraction_ring

created src/ring_theory/localization/at_prime.lean
- \+ *lemma* is_unit_to_map_iff
- \+ *lemma* to_map_mem_maximal_iff
- \+ *lemma* is_unit_mk'_iff
- \+ *lemma* mk'_mem_maximal_iff
- \+ *lemma* at_prime.comap_maximal_ideal
- \+ *lemma* at_prime.map_eq_maximal_ideal
- \+ *lemma* le_comap_prime_compl_iff
- \+ *lemma* local_ring_hom_to_map
- \+ *lemma* local_ring_hom_mk'
- \+ *lemma* local_ring_hom_unique
- \+ *lemma* local_ring_hom_id
- \+ *lemma* local_ring_hom_comp
- \+ *theorem* at_prime.local_ring
- \+ *def* prime_compl

created src/ring_theory/localization/away.lean
- \+ *lemma* away_map.lift_eq
- \+ *lemma* away_map.lift_comp
- \+ *def* map
- \+ *def* at_units
- \+ *def* at_unit
- \+ *def* at_one

created src/ring_theory/localization/basic.lean
- \+ *lemma* of_le
- \+ *lemma* to_localization_map_to_map
- \+ *lemma* to_localization_map_to_map_apply
- \+ *lemma* to_localization_map_sec
- \+ *lemma* sec_spec
- \+ *lemma* sec_spec'
- \+ *lemma* map_right_cancel
- \+ *lemma* map_left_cancel
- \+ *lemma* eq_zero_of_fst_eq_zero
- \+ *lemma* map_eq_zero_iff
- \+ *lemma* mk'_sec
- \+ *lemma* mk'_mul
- \+ *lemma* mk'_one
- \+ *lemma* mk'_spec
- \+ *lemma* mk'_spec'
- \+ *lemma* mk'_spec_mk
- \+ *lemma* mk'_spec'_mk
- \+ *lemma* mk'_surjective
- \+ *lemma* mk'_eq_iff_eq
- \+ *lemma* mk'_mem_iff
- \+ *lemma* mk'_eq_zero_iff
- \+ *lemma* eq_iff_eq
- \+ *lemma* mk'_eq_iff_mk'_eq
- \+ *lemma* mk'_eq_of_eq
- \+ *lemma* mk'_self
- \+ *lemma* mk'_self'
- \+ *lemma* mk'_self''
- \+ *lemma* mul_mk'_eq_mk'_of_mul
- \+ *lemma* mk'_eq_mul_mk'_one
- \+ *lemma* mk'_mul_cancel_left
- \+ *lemma* mk'_mul_cancel_right
- \+ *lemma* mk'_mul_mk'_eq_one
- \+ *lemma* mk'_mul_mk'_eq_one'
- \+ *lemma* is_unit_comp
- \+ *lemma* eq_of_eq
- \+ *lemma* mk'_add
- \+ *lemma* lift_mk'
- \+ *lemma* lift_mk'_spec
- \+ *lemma* lift_eq
- \+ *lemma* lift_eq_iff
- \+ *lemma* lift_comp
- \+ *lemma* lift_of_comp
- \+ *lemma* monoid_hom_ext
- \+ *lemma* ring_hom_ext
- \+ *lemma* lift_unique
- \+ *lemma* lift_id
- \+ *lemma* lift_surjective_iff
- \+ *lemma* lift_injective_iff
- \+ *lemma* map_eq
- \+ *lemma* map_comp
- \+ *lemma* map_mk'
- \+ *lemma* map_id
- \+ *lemma* map_unique
- \+ *lemma* map_comp_map
- \+ *lemma* map_map
- \+ *lemma* map_smul
- \+ *lemma* ring_equiv_of_ring_equiv_eq_map
- \+ *lemma* ring_equiv_of_ring_equiv_eq
- \+ *lemma* ring_equiv_of_ring_equiv_mk'
- \+ *lemma* alg_equiv_mk'
- \+ *lemma* alg_equiv_symm_mk'
- \+ *lemma* is_localization_of_alg_equiv
- \+ *lemma* is_localization_iff_of_alg_equiv
- \+ *lemma* is_localization_iff_of_ring_equiv
- \+ *lemma* is_localization_of_base_ring_equiv
- \+ *lemma* is_localization_iff_of_base_ring_equiv
- \+ *lemma* non_zero_divisors_le_comap
- \+ *lemma* map_non_zero_divisors_le
- \+ *lemma* add_mk
- \+ *lemma* add_mk_self
- \+ *lemma* neg_mk
- \+ *lemma* mk_zero
- \+ *lemma* lift_on_zero
- \+ *lemma* to_localization_map_eq_monoid_of
- \+ *lemma* monoid_of_eq_algebra_map
- \+ *lemma* mk_one_eq_algebra_map
- \+ *lemma* mk_eq_mk'_apply
- \+ *lemma* mk_eq_mk'
- \+ *lemma* alg_equiv_mk'
- \+ *lemma* alg_equiv_symm_mk'
- \+ *lemma* alg_equiv_mk
- \+ *lemma* alg_equiv_symm_mk
- \+ *lemma* to_map_eq_zero_iff
- \+ *lemma* map_injective_of_injective
- \+ *lemma* localization_map_bijective_of_field
- \+ *lemma* algebra_map_mk'
- \+ *lemma* localization_algebra_injective
- \+ *theorem* eq_mk'_iff_mul_eq
- \+ *theorem* mk'_eq_iff_eq_mul
- \+ *theorem* is_domain_of_le_non_zero_divisors
- \+ *theorem* is_domain_localization
- \+ *def* to_localization_map

created src/ring_theory/localization/fraction_ring.lean
- \+ *lemma* to_map_eq_zero_iff
- \+ *lemma* mk'_mk_eq_div
- \+ *lemma* mk'_eq_div
- \+ *lemma* div_surjective
- \+ *lemma* is_unit_map_of_injective
- \+ *lemma* lift_algebra_map
- \+ *lemma* lift_mk'
- \+ *lemma* is_fraction_ring_iff_of_base_ring_equiv
- \+ *lemma* nontrivial
- \+ *lemma* mk_eq_div
- \+ *def* fraction_ring

created src/ring_theory/localization/ideal.lean
- \+ *lemma* is_prime_iff_is_prime_disjoint
- \+ *lemma* is_prime_of_is_prime_disjoint
- \+ *lemma* surjective_quotient_map_of_maximal_of_localization
- \+ *theorem* mem_map_algebra_map_iff
- \+ *theorem* map_comap
- \+ *theorem* comap_map_of_is_prime_disjoint
- \+ *def* order_embedding
- \+ *def* order_iso_of_prime

created src/ring_theory/localization/integer.lean
- \+ *lemma* is_integer_zero
- \+ *lemma* is_integer_one
- \+ *lemma* is_integer_add
- \+ *lemma* is_integer_mul
- \+ *lemma* is_integer_smul
- \+ *lemma* exists_integer_multiple'
- \+ *lemma* exists_integer_multiple
- \+ *lemma* exist_integer_multiples
- \+ *lemma* exist_integer_multiples_of_fintype
- \+ *lemma* exist_integer_multiples_of_finset
- \+ *lemma* map_integer_multiple
- \+ *lemma* finset_integer_multiple_image
- \+ *def* is_integer
- \+ *def* common_denom
- \+ *def* integer_multiple
- \+ *def* common_denom_of_finset
- \+ *def* finset_integer_multiple

created src/ring_theory/localization/integral.lean
- \+ *lemma* coeff_integer_normalization_of_not_mem_support
- \+ *lemma* coeff_integer_normalization_mem_support
- \+ *lemma* integer_normalization_coeff
- \+ *lemma* integer_normalization_spec
- \+ *lemma* integer_normalization_map_to_map
- \+ *lemma* integer_normalization_eval₂_eq_zero
- \+ *lemma* integer_normalization_aeval_eq_zero
- \+ *lemma* integer_normalization_eq_zero_iff
- \+ *lemma* is_algebraic_iff
- \+ *lemma* comap_is_algebraic_iff
- \+ *lemma* ring_hom.is_integral_elem_localization_at_leading_coeff
- \+ *lemma* is_integral_localization'
- \+ *lemma* is_fraction_ring_of_algebraic
- \+ *lemma* is_fraction_ring_of_finite_extension
- \+ *lemma* is_fraction_ring_of_algebraic
- \+ *lemma* is_fraction_ring_of_finite_extension
- \+ *lemma* is_algebraic_iff'
- \+ *theorem* is_integral_localization_at_leading_coeff
- \+ *theorem* is_integral_localization

created src/ring_theory/localization/inv_submonoid.lean
- \+ *lemma* submonoid_map_le_is_unit
- \+ *lemma* to_inv_submonoid_surjective
- \+ *lemma* to_inv_submonoid_mul
- \+ *lemma* mul_to_inv_submonoid
- \+ *lemma* smul_to_inv_submonoid
- \+ *lemma* surj'
- \+ *lemma* to_inv_submonoid_eq_mk'
- \+ *lemma* mem_inv_submonoid_iff_exists_mk'
- \+ *lemma* span_inv_submonoid
- \+ *lemma* finite_type_of_monoid_fg
- \+ *def* inv_submonoid
- \+ *def* to_inv_submonoid

created src/ring_theory/localization/localization_localization.lean
- \+ *lemma* mem_localization_localization_submodule
- \+ *lemma* localization_localization_map_units
- \+ *lemma* localization_localization_surj
- \+ *lemma* localization_localization_eq_iff_exists
- \+ *lemma* localization_localization_is_localization
- \+ *lemma* localization_localization_is_localization_of_has_all_units
- \+ *lemma* is_localization_is_localization_at_prime_is_localization
- \+ *lemma* localization_is_scalar_tower_of_submonoid_le
- \+ *lemma* is_localization_of_submonoid_le
- \+ *lemma* is_localization_of_is_exists_mul_mem
- \+ *lemma* is_fraction_ring_of_is_localization
- \+ *lemma* is_fraction_ring_of_is_domain_of_is_localization
- \+ *def* localization_localization_submodule
- \+ *def* localization_localization_at_prime_iso_localization
- \+ *def* localization_algebra_of_submonoid_le

created src/ring_theory/localization/num_denom.lean
- \+ *lemma* exists_reduced_fraction
- \+ *lemma* num_denom_reduced
- \+ *lemma* mk'_num_denom
- \+ *lemma* num_mul_denom_eq_num_iff_eq
- \+ *lemma* num_mul_denom_eq_num_iff_eq'
- \+ *lemma* num_mul_denom_eq_num_mul_denom_iff_eq
- \+ *lemma* eq_zero_of_num_eq_zero
- \+ *lemma* is_integer_of_is_unit_denom
- \+ *lemma* is_unit_denom_of_num_eq_zero

created src/ring_theory/localization/submodule.lean
- \+ *lemma* mem_coe_submodule
- \+ *lemma* coe_submodule_mono
- \+ *lemma* coe_submodule_bot
- \+ *lemma* coe_submodule_top
- \+ *lemma* coe_submodule_sup
- \+ *lemma* coe_submodule_mul
- \+ *lemma* coe_submodule_fg
- \+ *lemma* coe_submodule_span
- \+ *lemma* coe_submodule_span_singleton
- \+ *lemma* is_noetherian_ring
- \+ *lemma* coe_submodule_le_coe_submodule
- \+ *lemma* coe_submodule_strict_mono
- \+ *lemma* coe_submodule_injective
- \+ *lemma* coe_submodule_is_principal
- \+ *lemma* coe_submodule_le_coe_submodule
- \+ *lemma* coe_submodule_strict_mono
- \+ *lemma* coe_submodule_injective
- \+ *lemma* coe_submodule_is_principal
- \+ *def* coe_submodule

modified src/ring_theory/perfection.lean

modified src/ring_theory/polynomial/dickson.lean

modified src/ring_theory/polynomial/gauss_lemma.lean

modified src/ring_theory/polynomial/rational_root.lean

modified src/set_theory/surreal/dyadic.lean

modified src/topology/algebra/localization.lean



## [2022-02-22 15:16:19](https://github.com/leanprover-community/mathlib/commit/deb5046)
feat(mv_polynomial/basic): monomial_eq_monomial_iff ([#12198](https://github.com/leanprover-community/mathlib/pull/12198))
#### Estimated changes
modified src/data/mv_polynomial/basic.lean
- \+ *lemma* monomial_eq_monomial_iff



## [2022-02-22 15:16:18](https://github.com/leanprover-community/mathlib/commit/8b09b0e)
feat(measure_theory/group/arithmetic): add `has_measurable_smul.op` and `has_measurable_smul₂.op` ([#12196](https://github.com/leanprover-community/mathlib/pull/12196))
This matches the naming of `has_continuous_smul.op`.
#### Estimated changes
modified src/measure_theory/group/arithmetic.lean



## [2022-02-22 15:16:17](https://github.com/leanprover-community/mathlib/commit/79c5de9)
feat(ring_theory/ideal/operations): remove unneeded assumptions from `smul_induction_on` ([#12193](https://github.com/leanprover-community/mathlib/pull/12193))
#### Estimated changes
modified src/linear_algebra/adic_completion.lean

modified src/ring_theory/ideal/operations.lean



## [2022-02-22 15:16:15](https://github.com/leanprover-community/mathlib/commit/f6d397f)
feat(order/hom/basic): `order_iso_class` ([#12157](https://github.com/leanprover-community/mathlib/pull/12157))
Define `order_iso_class`, following the hom refactor. Also add a few missing lemmas.
#### Estimated changes
modified src/data/equiv/basic.lean

modified src/linear_algebra/basic.lean
- \- *theorem* map_le_map_iff

modified src/linear_algebra/quotient.lean

modified src/order/hom/basic.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext



## [2022-02-22 15:16:14](https://github.com/leanprover-community/mathlib/commit/4c6b0de)
feat(topology/bases): disjoint unions of second-countable spaces are second-countable ([#12061](https://github.com/leanprover-community/mathlib/pull/12061))
#### Estimated changes
modified src/topology/bases.lean
- \+ *lemma* is_topological_basis.is_open_iff
- \+ *lemma* is_topological_basis_singletons
- \+ *lemma* is_topological_basis.sigma
- \+ *lemma* is_topological_basis.sum

modified src/topology/constructions.lean
- \+ *lemma* is_closed_range_inl
- \+ *lemma* is_closed_range_inr
- \+ *lemma* closed_embedding_inl
- \+ *lemma* closed_embedding_inr

modified src/topology/continuous_on.lean
- \+ *lemma* continuous_on.mono_dom
- \+ *lemma* continuous_on.mono_rng

modified src/topology/homeomorph.lean
- \+ *def* equiv.to_homeomorph_of_inducing

modified src/topology/order.lean
- \+ *lemma* continuous_id_of_le



## [2022-02-22 13:18:00](https://github.com/leanprover-community/mathlib/commit/8413f07)
feat(topology/support): define topological support and compactly supported functions ([#11923](https://github.com/leanprover-community/mathlib/pull/11923))
* Also add some variants of the extreme value theorem.
#### Estimated changes
modified src/algebra/group/to_additive.lean

modified src/analysis/calculus/specific_functions.lean
- \+ *lemma* tsupport_eq
- \+ *lemma* exists_tsupport_subset
- \- *lemma* closure_support_eq
- \- *lemma* compact_closure_support
- \- *lemma* exists_closure_support_subset

modified src/analysis/normed/group/basic.lean
- \+ *lemma* has_compact_support_norm_iff
- \+ *lemma* continuous.bounded_above_of_compact_support

modified src/geometry/manifold/bump_function.lean
- \+ *lemma* tsupport_mem_nhds
- \+ *lemma* tsupport_subset_symm_image_closed_ball
- \+ *lemma* tsupport_subset_ext_chart_at_source
- \+ *lemma* tsupport_subset_chart_at_source
- \+ *lemma* nhds_basis_tsupport
- \- *lemma* closure_support_mem_nhds
- \- *lemma* closure_support_subset_symm_image_closed_ball
- \- *lemma* closure_support_subset_ext_chart_at_source
- \- *lemma* closure_support_subset_chart_at_source
- \- *lemma* compact_closure_support
- \- *lemma* nhds_basis_closure_support

modified src/geometry/manifold/partition_of_unity.lean

modified src/geometry/manifold/times_cont_mdiff.lean

modified src/measure_theory/integral/integrable_on.lean
- \+ *lemma* continuous.integrable_of_has_compact_support
- \- *lemma* continuous.integrable_of_compact_closure_support

modified src/topology/algebra/order/compact.lean
- \+ *lemma* _root_.continuous.exists_forall_le'
- \+ *lemma* _root_.continuous.exists_forall_ge'
- \+ *lemma* _root_.continuous.exists_forall_le
- \+ *lemma* _root_.continuous.exists_forall_le_of_has_compact_mul_support
- \+ *lemma* continuous.exists_forall_ge_of_has_compact_mul_support
- \+ *lemma* continuous.bdd_below_range_of_has_compact_mul_support
- \+ *lemma* continuous.bdd_above_range_of_has_compact_mul_support
- \+ *lemma* is_compact.bdd_below_image
- \+ *lemma* is_compact.bdd_above_image
- \- *lemma* continuous.exists_forall_le

modified src/topology/homeomorph.lean
- \+ *lemma* _root_.has_compact_mul_support.comp_homeomorph

modified src/topology/partition_of_unity.lean

created src/topology/support.lean
- \+ *lemma* subset_mul_tsupport
- \+ *lemma* is_closed_mul_tsupport
- \+ *lemma* mul_tsupport_eq_empty_iff
- \+ *lemma* image_eq_zero_of_nmem_mul_tsupport
- \+ *lemma* not_mem_closure_mul_support_iff_eventually_eq
- \+ *lemma* has_compact_mul_support_def
- \+ *lemma* exists_compact_iff_has_compact_mul_support
- \+ *lemma* has_compact_mul_support.intro
- \+ *lemma* has_compact_mul_support.is_compact
- \+ *lemma* has_compact_mul_support_iff_eventually_eq
- \+ *lemma* has_compact_mul_support.mono'
- \+ *lemma* has_compact_mul_support.mono
- \+ *lemma* has_compact_mul_support.comp_left
- \+ *lemma* has_compact_mul_support_comp_left
- \+ *lemma* has_compact_mul_support.comp_closed_embedding
- \+ *lemma* has_compact_mul_support.comp₂_left
- \+ *lemma* has_compact_mul_support.mul
- \+ *lemma* has_compact_support.smul_left
- \+ *lemma* has_compact_support.smul_right
- \+ *lemma* has_compact_support.smul_left'
- \+ *lemma* has_compact_support.mul_right
- \+ *lemma* has_compact_support.mul_left
- \+ *def* mul_tsupport
- \+ *def* has_compact_mul_support



## [2022-02-22 10:50:40](https://github.com/leanprover-community/mathlib/commit/80591d6)
feat(order/hom/lattice): Finitary join-/meet-preserving maps ([#12149](https://github.com/leanprover-community/mathlib/pull/12149))
Define `sup_bot_hom`, `inf_top_hom` and their associated class.
#### Estimated changes
modified src/order/bounded_order.lean
- \+ *def* order_top.lift
- \+ *def* order_bot.lift
- \+ *def* bounded_order.lift

modified src/order/complete_lattice.lean
- \- *def* order_top.lift
- \- *def* order_bot.lift
- \- *def* bounded_order.lift

modified src/order/hom/lattice.lean
- \+ *lemma* map_finset_sup
- \+ *lemma* map_finset_inf
- \+/\- *lemma* coe_const
- \+/\- *lemma* const_apply
- \+/\- *lemma* coe_sup
- \+ *lemma* coe_bot
- \+ *lemma* coe_top
- \+/\- *lemma* sup_apply
- \+ *lemma* bot_apply
- \+ *lemma* top_apply
- \+/\- *lemma* coe_const
- \+/\- *lemma* const_apply
- \+ *lemma* coe_bot
- \+ *lemma* coe_top
- \+ *lemma* bot_apply
- \+ *lemma* top_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+/\- *lemma* coe_sup
- \+ *lemma* coe_bot
- \+/\- *lemma* sup_apply
- \+ *lemma* bot_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_inf
- \+ *lemma* coe_top
- \+ *lemma* inf_apply
- \+ *lemma* top_apply
- \+/\- *lemma* coe_sup
- \+/\- *lemma* sup_apply
- \+/\- *lemma* coe_const
- \+/\- *lemma* const_apply
- \+/\- *lemma* coe_const
- \+/\- *lemma* const_apply
- \+/\- *def* const
- \+/\- *def* const
- \+ *def* to_bot_hom
- \+ *def* comp
- \+ *def* to_top_hom
- \+ *def* comp
- \+ *def* to_sup_bot_hom
- \+ *def* to_inf_top_hom
- \+/\- *def* const
- \+/\- *def* const



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
modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_id

modified src/topology/algebra/continuous_monoid_hom.lean
- \+ *lemma* to_continuous_map_injective
- \+ *def* to_continuous_map
- \+/\- *def* mk'
- \+/\- *def* mk'

modified src/topology/category/CompHaus/default.lean

modified src/topology/compact_open.lean
- \+/\- *lemma* coe_const'
- \+/\- *lemma* continuous_const'
- \+/\- *lemma* coe_const'
- \+/\- *lemma* continuous_const'

modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* one_comp
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_one
- \+/\- *lemma* one_comp

modified src/topology/continuous_function/basic.lean
- \+ *lemma* map_continuous_at
- \+ *lemma* map_continuous_within_at
- \+ *lemma* ext
- \+/\- *lemma* continuous_set_coe
- \+ *lemma* coe_id
- \+ *lemma* coe_const
- \+/\- *lemma* id_apply
- \+/\- *lemma* const_apply
- \+ *lemma* coe_comp
- \+/\- *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_id
- \+ *lemma* const_comp
- \+ *lemma* comp_const
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+/\- *lemma* continuous_set_coe
- \- *lemma* ext_iff
- \- *lemma* id_coe
- \+/\- *lemma* id_apply
- \- *lemma* comp_coe
- \+/\- *lemma* comp_apply
- \+/\- *lemma* id_comp
- \+/\- *lemma* comp_id
- \- *lemma* const_coe
- \+/\- *lemma* const_apply
- \- *theorem* ext
- \+/\- *def* const
- \+/\- *def* comp
- \- *def* id
- \+/\- *def* comp
- \+/\- *def* const

modified src/topology/continuous_function/bounded.lean
- \+/\- *lemma* ext
- \+/\- *lemma* forall_coe_one_iff_one
- \+/\- *lemma* ext
- \- *lemma* ext_iff
- \- *lemma* coe_injective
- \+/\- *lemma* forall_coe_one_iff_one
- \+/\- *def* restrict
- \+/\- *def* restrict

modified src/topology/continuous_function/polynomial.lean

modified src/topology/continuous_function/stone_weierstrass.lean

modified src/topology/homotopy/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* apply_zero
- \+/\- *lemma* apply_one
- \+/\- *lemma* apply_zero
- \+/\- *lemma* apply_one
- \- *lemma* coe_fn_injective
- \+/\- *lemma* ext
- \+/\- *lemma* apply_zero
- \+/\- *lemma* apply_one
- \+/\- *lemma* apply_zero
- \+/\- *lemma* apply_one

modified src/topology/homotopy/equiv.lean

modified src/topology/homotopy/fundamental_groupoid.lean

modified src/topology/homotopy/path.lean

modified src/topology/homotopy/product.lean
- \+/\- *def* homotopy.pi
- \+/\- *def* homotopy.pi

modified src/topology/opens.lean
- \+/\- *lemma* comap_id
- \+/\- *lemma* comap_id

modified src/topology/tietze_extension.lean



## [2022-02-22 10:50:38](https://github.com/leanprover-community/mathlib/commit/247943a)
feat(analysis/seminorm): add inf ([#11791](https://github.com/leanprover-community/mathlib/pull/11791))
Define the infimum of seminorms.
#### Estimated changes
modified src/analysis/seminorm.lean
- \+ *lemma* le_insert
- \+ *lemma* le_insert'
- \+ *lemma* inf_apply
- \+ *lemma* smul_inf

modified src/order/conditionally_complete_lattice.lean
- \+ *lemma* le_mul_cinfi
- \+ *lemma* mul_csupr_le
- \+ *lemma* le_cinfi_mul
- \+ *lemma* csupr_mul_le
- \+ *lemma* le_cinfi_mul_cinfi
- \+ *lemma* csupr_mul_csupr_le



## [2022-02-22 10:10:32](https://github.com/leanprover-community/mathlib/commit/9a7ed8c)
chore(algebra/lie/engel): speed up proof of Engel's theorem slightly ([#12205](https://github.com/leanprover-community/mathlib/pull/12205))
Local measurements using `set_option profiler true` are noisy but indicate
that this speeds up elaboration of `lie_algebra.is_engelian_of_is_noetherian`
by about 20% from about 10s to about 8s.
#### Estimated changes
modified src/algebra/lie/engel.lean



## [2022-02-22 03:09:07](https://github.com/leanprover-community/mathlib/commit/cb45da2)
feat(category_theory/limits): is_bilimit ([#12108](https://github.com/leanprover-community/mathlib/pull/12108))
#### Estimated changes
modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *lemma* bicone_ι_π_ne
- \+ *lemma* ι_of_is_limit
- \+ *lemma* π_of_is_colimit
- \+/\- *lemma* bicone_ι_π_ne
- \+ *def* of_limit_cone
- \+ *def* of_colimit_cocone
- \+ *def* biproduct.is_bilimit
- \+ *def* to_bicone
- \+ *def* to_bicone_is_limit
- \+ *def* to_bicone_is_colimit
- \+/\- *def* to_binary_bicone_is_limit
- \+/\- *def* to_binary_bicone_is_colimit
- \+ *def* binary_bicone.to_bicone_is_bilimit
- \+ *def* bicone.to_binary_bicone_is_bilimit
- \+ *def* binary_biproduct.is_bilimit
- \+/\- *def* to_binary_bicone_is_limit
- \+/\- *def* to_binary_bicone_is_colimit



## [2022-02-22 00:37:45](https://github.com/leanprover-community/mathlib/commit/e16e093)
feat(analysis/specific_limits): dirichlet and alternating series tests  ([#11908](https://github.com/leanprover-community/mathlib/pull/11908))
Adds [Dirichlet's test](https://en.wikipedia.org/wiki/Dirichlet%27s_test) along with the [alternating series test](https://en.wikipedia.org/wiki/Alternating_series_test) as a special case of the former. For the curious, [Nick Bingham's course notes](https://www.ma.imperial.ac.uk/~bin06/M2PM3-Complex-Analysis/m2pm3abeldir.pdf) give some more context on Dirichlet's test. It's somewhat obscure.
#### Estimated changes
modified docs/undergrad.yaml

modified src/algebra/big_operators/intervals.lean

modified src/analysis/normed/group/infinite_sum.lean
- \+ *lemma* cauchy_seq_range_of_norm_bounded

modified src/analysis/specific_limits.lean
- \+ *lemma* norm_sum_neg_one_pow_le
- \+ *theorem* monotone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded
- \+ *theorem* antitone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded
- \+ *theorem* monotone.cauchy_seq_alternating_series_of_tendsto_zero
- \+ *theorem* monotone.tendsto_alternating_series_of_tendsto_zero
- \+ *theorem* antitone.cauchy_seq_alternating_series_of_tendsto_zero
- \+ *theorem* antitone.tendsto_alternating_series_of_tendsto_zero

modified src/topology/uniform_space/cauchy.lean
- \+/\- *def* set_seq
- \+/\- *def* set_seq



## [2022-02-21 23:46:54](https://github.com/leanprover-community/mathlib/commit/d77e91f)
perf(geometry/euclidean): speed up proof on the edge of timing out ([#12191](https://github.com/leanprover-community/mathlib/pull/12191))
#### Estimated changes
modified src/geometry/euclidean/oriented_angle.lean



## [2022-02-21 23:46:53](https://github.com/leanprover-community/mathlib/commit/22464cf)
feat(analysis/normed_space/basic): `norm_matrix_lt_iff` ([#12151](https://github.com/leanprover-community/mathlib/pull/12151))
A strict variant of `norm_matrix_le_iff`, using `pi_norm_lt_iff`
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* norm_matrix_lt_iff



## [2022-02-21 22:53:11](https://github.com/leanprover-community/mathlib/commit/eb5c5ed)
feat(measure_theory/integral/set_integral): Bochner integral with respect to a measure with density ([#12123](https://github.com/leanprover-community/mathlib/pull/12123))
This PR shows that `∫ a, g a ∂(μ.with_density (λ x, f x)) = ∫ a, f a • g a ∂μ`. (This fact is already available for the Lebesgue integral, not for the Bochner integral.)
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* continuous_on.measurable_piecewise

modified src/measure_theory/function/l1_space.lean
- \+ *lemma* integrable_with_density_iff_integrable_coe_smul
- \+/\- *lemma* integrable_with_density_iff_integrable_smul
- \+ *lemma* integrable_with_density_iff_integrable_coe_smul₀
- \+ *lemma* integrable_with_density_iff_integrable_smul₀
- \+ *lemma* mem_ℒ1_smul_of_L1_with_density
- \+ *lemma* with_density_smul_li_apply
- \+/\- *lemma* integrable_with_density_iff_integrable_smul

modified src/measure_theory/group/measure.lean

modified src/measure_theory/integral/set_integral.lean
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
modified src/tactic/linear_combination.lean

modified test/linear_combination.lean



## [2022-02-21 21:06:38](https://github.com/leanprover-community/mathlib/commit/2971f3d)
feat(algebra/star/self_adjoint): remove commutativity hypothesis from `has_pow (self_adjoint R)` ([#12188](https://github.com/leanprover-community/mathlib/pull/12188))
This was put in the wrong section. Powers of selfadjoint elements are still selfadjoint.
#### Estimated changes
modified src/algebra/star/self_adjoint.lean
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_pow



## [2022-02-21 21:06:37](https://github.com/leanprover-community/mathlib/commit/a607820)
feat(category_theory/equivalence): if two functors F and G are isomorphic, F is an equivalence iff G is ([#12162](https://github.com/leanprover-community/mathlib/pull/12162))
#### Estimated changes
modified src/category_theory/equivalence.lean
- \+ *lemma* of_iso_trans
- \+ *lemma* of_iso_refl
- \+ *def* of_iso
- \+ *def* equiv_of_iso
- \+ *def* cancel_comp_right
- \+ *def* cancel_comp_left



## [2022-02-21 21:06:35](https://github.com/leanprover-community/mathlib/commit/9a17b55)
feat(analysis/normed_space/basic): `norm_entry_le_entrywise_sup_norm` ([#12159](https://github.com/leanprover-community/mathlib/pull/12159))
The entries of a matrix are at most the entrywise sup norm.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* matrix.norm_entry_le_entrywise_sup_norm



## [2022-02-21 19:14:30](https://github.com/leanprover-community/mathlib/commit/1cfbcc6)
feat(algebra/ring/ulift): add a `field` instance ([#12141](https://github.com/leanprover-community/mathlib/pull/12141))
#### Estimated changes
modified src/algebra/group/ulift.lean

modified src/algebra/ring/ulift.lean



## [2022-02-21 16:41:40](https://github.com/leanprover-community/mathlib/commit/e3d3681)
feat(analysis/inner_product_space/spectrum): `pos_nonneg_eigenvalues` ([#12161](https://github.com/leanprover-community/mathlib/pull/12161))
If T is a positive self-adjoint operator, then its eigenvalues are
nonnegative.  Maybe there should be a definition of "positive operator",
and maybe this should be generalized.  Guidance appreciated!
#### Estimated changes
modified src/analysis/inner_product_space/spectrum.lean
- \+ *lemma* inner_product_apply_eigenvector
- \+ *lemma* eigenvalue_nonneg_of_nonneg
- \+ *lemma* eigenvalue_pos_of_pos



## [2022-02-21 15:30:08](https://github.com/leanprover-community/mathlib/commit/02dc6f2)
feat(probability/stopping): filtrations are a complete lattice ([#12169](https://github.com/leanprover-community/mathlib/pull/12169))
#### Estimated changes
modified src/probability/stopping.lean
- \+ *lemma* coe_fn_sup
- \+ *lemma* coe_fn_inf
- \+ *lemma* Sup_def
- \+ *lemma* Inf_def
- \+ *def* const
- \- *def* const_filtration



## [2022-02-21 15:30:07](https://github.com/leanprover-community/mathlib/commit/9ed7179)
refactor(*): move normed field lemmas into root namespace ([#12163](https://github.com/leanprover-community/mathlib/pull/12163))
This takes the normed field lemmas given in `analysis.normed_space.basic` and moves them from the `normed_field` namespace into the root namespace.
This PR moves these lemmas and definitions: `norm_mul`, `nnnorm_mul`, `norm_hom`, `nnnorm_hom`, `norm_pow`, `nnnorm_pow`, `norm_prod`, `nnnorm_prod`, `norm_div`, `nnnorm_div`, `norm_inv`, `nnnorm_inv`, `norm_zpow`, `nnnorm_zpow`.
#### Estimated changes
modified src/analysis/analytic/basic.lean

modified src/analysis/asymptotics/asymptotics.lean

modified src/analysis/asymptotics/specific_asymptotics.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/complex/cauchy_integral.lean

modified src/analysis/complex/conformal.lean

modified src/analysis/normed_space/add_torsor.lean

modified src/analysis/normed_space/banach.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/dual.lean

modified src/analysis/normed_space/enorm.lean

modified src/analysis/normed_space/extend.lean

modified src/analysis/normed_space/is_R_or_C.lean

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/normed_space/ordered.lean

modified src/analysis/normed_space/pointwise.lean

modified src/analysis/normed_space/spectrum.lean

modified src/analysis/normed_space/star/basic.lean

modified src/analysis/special_functions/exp.lean

modified src/analysis/special_functions/exp_deriv.lean

modified src/analysis/special_functions/trigonometric/complex_deriv.lean

modified src/analysis/specific_limits.lean

modified src/data/complex/is_R_or_C.lean

modified src/number_theory/padics/hensel.lean

modified src/number_theory/padics/padic_numbers.lean

modified src/topology/metric_space/cau_seq_filter.lean



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
created src/geometry/euclidean/oriented_angle.lean
- \+ *lemma* oangle_zero_left
- \+ *lemma* oangle_zero_right
- \+ *lemma* oangle_self
- \+ *lemma* oangle_rev
- \+ *lemma* oangle_add_oangle_rev
- \+ *lemma* oangle_neg_left
- \+ *lemma* oangle_neg_right
- \+ *lemma* two_zsmul_oangle_neg_left
- \+ *lemma* two_zsmul_oangle_neg_right
- \+ *lemma* oangle_neg_neg
- \+ *lemma* oangle_neg_left_eq_neg_right
- \+ *lemma* oangle_neg_self_left
- \+ *lemma* oangle_neg_self_right
- \+ *lemma* two_zsmul_oangle_neg_self_left
- \+ *lemma* two_zsmul_oangle_neg_self_right
- \+ *lemma* oangle_add_oangle_rev_neg_left
- \+ *lemma* oangle_add_oangle_rev_neg_right
- \+ *lemma* oangle_smul_left_of_pos
- \+ *lemma* oangle_smul_right_of_pos
- \+ *lemma* oangle_smul_left_of_neg
- \+ *lemma* oangle_smul_right_of_neg
- \+ *lemma* oangle_smul_left_self_of_nonneg
- \+ *lemma* oangle_smul_right_self_of_nonneg
- \+ *lemma* oangle_smul_smul_self_of_nonneg
- \+ *lemma* two_zsmul_oangle_smul_left_of_ne_zero
- \+ *lemma* two_zsmul_oangle_smul_right_of_ne_zero
- \+ *lemma* two_zsmul_oangle_smul_left_self
- \+ *lemma* two_zsmul_oangle_smul_right_self
- \+ *lemma* two_zsmul_oangle_smul_smul_self
- \+ *lemma* eq_iff_norm_eq_and_oangle_eq_zero
- \+ *lemma* eq_iff_oangle_eq_zero_of_norm_eq
- \+ *lemma* eq_iff_norm_eq_of_oangle_eq_zero
- \+ *lemma* oangle_add
- \+ *lemma* oangle_add_swap
- \+ *lemma* oangle_sub_left
- \+ *lemma* oangle_sub_right
- \+ *lemma* oangle_add_cyc3
- \+ *lemma* oangle_add_cyc3_neg_left
- \+ *lemma* oangle_add_cyc3_neg_right
- \+ *lemma* oangle_sub_eq_oangle_sub_rev_of_norm_eq
- \+ *lemma* oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq
- \+ *lemma* oangle_eq_two_zsmul_oangle_sub_of_norm_eq
- \+ *lemma* oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real
- \+ *lemma* two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq
- \+ *lemma* det_rotation
- \+ *lemma* linear_equiv_det_rotation
- \+ *lemma* rotation_symm
- \+ *lemma* rotation_zero
- \+ *lemma* rotation_pi
- \+ *lemma* rotation_trans
- \+ *lemma* oangle_rotation_left
- \+ *lemma* oangle_rotation_right
- \+ *lemma* oangle_rotation_self_left
- \+ *lemma* oangle_rotation_self_right
- \+ *lemma* oangle_rotation_oangle_left
- \+ *lemma* oangle_rotation_oangle_right
- \+ *lemma* oangle_rotation
- \+ *lemma* rotation_eq_self_iff_angle_eq_zero
- \+ *lemma* eq_rotation_self_iff_angle_eq_zero
- \+ *lemma* rotation_eq_self_iff
- \+ *lemma* eq_rotation_self_iff
- \+ *lemma* rotation_oangle_eq_iff_norm_eq
- \+ *lemma* oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero
- \+ *lemma* oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
- \+ *lemma* oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero
- \+ *lemma* oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero
- \+ *lemma* det_conj_lie
- \+ *lemma* linear_equiv_det_conj_lie
- \+ *lemma* conj_lie_symm
- \+ *lemma* oangle_conj_lie
- \+ *lemma* exists_linear_isometry_equiv_eq
- \+ *lemma* exists_linear_isometry_equiv_eq_of_det_pos
- \+ *lemma* exists_linear_isometry_equiv_eq_of_det_neg
- \+ *lemma* exists_linear_isometry_equiv_map_eq_of_orientation_eq
- \+ *lemma* exists_linear_isometry_equiv_map_eq_of_orientation_eq_neg
- \+ *lemma* oangle_map
- \+ *lemma* oangle_eq_of_orientation_eq
- \+ *lemma* oangle_eq_neg_of_orientation_eq_neg
- \+ *lemma* rotation_eq_of_orientation_eq
- \+ *lemma* rotation_eq_rotation_neg_of_orientation_eq_neg
- \+ *def* oangle
- \+ *def* rotation
- \+ *def* conj_lie



## [2022-02-21 15:30:04](https://github.com/leanprover-community/mathlib/commit/6db1577)
feat(category_theory/preadditive): separators in preadditive categories ([#11884](https://github.com/leanprover-community/mathlib/pull/11884))
#### Estimated changes
modified src/category_theory/generator.lean
- \+/\- *lemma* is_separating_op_iff
- \+/\- *lemma* is_detecting_op_iff
- \+/\- *lemma* is_codetecting_op_iff
- \+/\- *lemma* is_detecting_unop_iff
- \+/\- *lemma* is_detecting_iff_is_separating
- \+/\- *lemma* is_separator_def
- \+/\- *lemma* is_coseparator_def
- \+/\- *lemma* is_detector_def
- \+/\- *lemma* is_codetector_def
- \+/\- *lemma* is_separator_iff_faithful_coyoneda_obj
- \+/\- *lemma* is_coseparator_iff_faithful_yoneda_obj
- \+/\- *lemma* is_detector_iff_reflects_isomorphisms_coyoneda_obj
- \+/\- *lemma* is_codetector_iff_reflects_isomorphisms_yoneda_obj
- \+/\- *lemma* is_separating_op_iff
- \+/\- *lemma* is_detecting_op_iff
- \+/\- *lemma* is_codetecting_op_iff
- \+/\- *lemma* is_detecting_unop_iff
- \+/\- *lemma* is_detecting_iff_is_separating
- \+/\- *lemma* is_separator_def
- \+/\- *lemma* is_coseparator_def
- \+/\- *lemma* is_detector_def
- \+/\- *lemma* is_codetector_def
- \+/\- *lemma* is_separator_iff_faithful_coyoneda_obj
- \+/\- *lemma* is_coseparator_iff_faithful_yoneda_obj
- \+/\- *lemma* is_detector_iff_reflects_isomorphisms_coyoneda_obj
- \+/\- *lemma* is_codetector_iff_reflects_isomorphisms_yoneda_obj

created src/category_theory/preadditive/generator.lean
- \+ *lemma* preadditive.is_separating_iff
- \+ *lemma* preadditive.is_coseparating_iff
- \+ *lemma* preadditive.is_separator_iff
- \+ *lemma* preadditive.is_coseparator_iff
- \+ *lemma* is_separator_iff_faithful_preadditive_coyoneda
- \+ *lemma* is_separator_iff_faithful_preadditive_coyoneda_obj
- \+ *lemma* is_coseparator_iff_faithful_preadditive_yoneda
- \+ *lemma* is_coseparator_iff_faithful_preadditive_yoneda_obj



## [2022-02-21 13:33:45](https://github.com/leanprover-community/mathlib/commit/3ad7395)
chore(topology/algebra/infinite_sum): reference Cauchy criterion in docs ([#12172](https://github.com/leanprover-community/mathlib/pull/12172))
#### Estimated changes
modified src/topology/algebra/infinite_sum.lean



## [2022-02-21 13:33:44](https://github.com/leanprover-community/mathlib/commit/634dfc8)
feat(order/*): Missing order lifting instances ([#12154](https://github.com/leanprover-community/mathlib/pull/12154))
Add a few missing pullbacks of order instances.
#### Estimated changes
modified src/order/boolean_algebra.lean

modified src/order/complete_boolean_algebra.lean
- \+ *lemma* binfi_sup_eq
- \+ *lemma* sup_binfi_eq
- \- *theorem* binfi_sup_eq
- \- *theorem* sup_binfi_eq

modified src/order/complete_lattice.lean
- \+ *def* order_top.lift
- \+ *def* order_bot.lift
- \+ *def* bounded_order.lift



## [2022-02-21 13:33:43](https://github.com/leanprover-community/mathlib/commit/2f33463)
feat(group_theory/free_product): is_free_group_free_product_of_is_free_group ([#12125](https://github.com/leanprover-community/mathlib/pull/12125))
#### Estimated changes
modified src/group_theory/free_product.lean



## [2022-02-21 11:38:07](https://github.com/leanprover-community/mathlib/commit/7c6678a)
doc(topology/dense_embedding): fix markdown ([#12180](https://github.com/leanprover-community/mathlib/pull/12180))
Right now it just renders as "γ -f→ α g↓ ↓e δ -h→ β"
#### Estimated changes
modified src/topology/dense_embedding.lean



## [2022-02-21 11:38:06](https://github.com/leanprover-community/mathlib/commit/f66a5dd)
chore(data/set/basic): add a few lemmas and a `@[simp]` attribute ([#12176](https://github.com/leanprover-community/mathlib/pull/12176))
* rename `set.exists_eq_singleton_iff_nonempty_unique_mem` to `set.exists_eq_singleton_iff_nonempty_subsingleton`, use `set.subsingleton` in the statement;
* add `@[simp]` to `set.subset_compl_singleton_iff`;
* add `set.diff_diff_right_self`.
#### Estimated changes
modified src/data/set/basic.lean
- \+/\- *lemma* subset_compl_singleton_iff
- \+ *lemma* diff_diff_right_self
- \+ *lemma* exists_eq_singleton_iff_nonempty_subsingleton
- \- *lemma* exists_eq_singleton_iff_nonempty_unique_mem
- \+/\- *lemma* subset_compl_singleton_iff

modified src/group_theory/complement.lean

modified src/topology/separation.lean

modified src/topology/subset_properties.lean



## [2022-02-21 11:38:05](https://github.com/leanprover-community/mathlib/commit/0eb5e2d)
feat(topology/algebra): if a subobject is commutative, then so is its topological closure ([#12170](https://github.com/leanprover-community/mathlib/pull/12170))
We prove that if a submonoid (or subgroup, subsemiring, subring, subalgebra, and the additive versions where applicable) is commutative, then so is its topological closure.
#### Estimated changes
modified src/topology/algebra/algebra.lean
- \+ *def* subalgebra.comm_semiring_topological_closure
- \+ *def* subalgebra.comm_ring_topological_closure

modified src/topology/algebra/group.lean
- \+ *def* subgroup.comm_group_topological_closure

modified src/topology/algebra/monoid.lean
- \+ *def* submonoid.comm_monoid_topological_closure

modified src/topology/algebra/ring.lean
- \+ *def* subsemiring.comm_semiring_topological_closure
- \+ *def* subring.comm_ring_topological_closure



## [2022-02-21 11:38:04](https://github.com/leanprover-community/mathlib/commit/56dbb60)
feat(category_theory/opposites): nat_trans.remove_unop ([#12147](https://github.com/leanprover-community/mathlib/pull/12147))
#### Estimated changes
modified src/category_theory/opposites.lean
- \+ *lemma* remove_unop_id
- \+ *lemma* remove_left_op_id
- \+ *lemma* remove_right_op_id



## [2022-02-21 11:38:02](https://github.com/leanprover-community/mathlib/commit/b3b5e35)
chore(data/nat/prime): slightly golf proof of mem_factors ([#12143](https://github.com/leanprover-community/mathlib/pull/12143))
#### Estimated changes
modified src/data/nat/prime.lean



## [2022-02-21 11:38:01](https://github.com/leanprover-community/mathlib/commit/afcc7e7)
feat(data/nat/prime): move nat.prime_iff_prime_int; add int.prime_two/three ([#12133](https://github.com/leanprover-community/mathlib/pull/12133))
I found it useful to have these results with somewhat lighter imports.
#### Estimated changes
modified src/data/nat/prime.lean
- \+ *lemma* prime_iff_prime_int
- \+ *lemma* prime_two
- \+ *lemma* prime_three

modified src/ring_theory/int/basic.lean
- \- *lemma* nat.prime_iff_prime_int



## [2022-02-21 11:38:00](https://github.com/leanprover-community/mathlib/commit/37019db)
feat(topology/algebra/{group,monoid}): nat and int scalar multiplication is continuous ([#12124](https://github.com/leanprover-community/mathlib/pull/12124))
These instances allow a diamond to appear in the scalar action on `continuous_affine_map`s, which we fix at the same time.
#### Estimated changes
modified src/topology/algebra/continuous_affine_map.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/monoid.lean

modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* pow_comp
- \+/\- *lemma* pow_comp



## [2022-02-21 11:37:58](https://github.com/leanprover-community/mathlib/commit/72252b3)
feat(analysis/inner_product_space/projection): norm_sq_eq_sum_norm_sq… ([#12096](https://github.com/leanprover-community/mathlib/pull/12096))
…_projection
The Pythagorean theorem for an orthogonal projection onto a submodule S.
I am sure that there are some style changes that could/should be made!
#### Estimated changes
modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* norm_sq_eq_add_norm_sq_projection



## [2022-02-21 11:37:57](https://github.com/leanprover-community/mathlib/commit/271c323)
feat(order/filter): prod_assoc ([#12002](https://github.com/leanprover-community/mathlib/pull/12002))
map (prod_assoc α β γ) ((f ×ᶠ g) ×ᶠ h) = f ×ᶠ (g ×ᶠ h)
with two tiny supporting lemmas
#### Estimated changes
modified src/order/filter/bases.lean
- \+ *lemma* has_basis.comp_of_surjective
- \+ *lemma* has_basis.comp_equiv
- \+ *lemma* prod_assoc

modified src/order/filter/basic.lean
- \+ *lemma* map_equiv_symm
- \+ *lemma* comap_equiv_symm



## [2022-02-21 11:37:56](https://github.com/leanprover-community/mathlib/commit/d8d2f54)
feat(group_theory/nilpotent): n-ary products of nilpotent group ([#11829](https://github.com/leanprover-community/mathlib/pull/11829))
#### Estimated changes
modified src/group_theory/nilpotent.lean
- \+ *lemma* lower_central_series_pi_le
- \+ *lemma* is_nilpotent_pi_of_bounded_class
- \+ *lemma* lower_central_series_pi_of_fintype
- \+ *lemma* nilpotency_class_pi



## [2022-02-21 10:14:55](https://github.com/leanprover-community/mathlib/commit/e966efc)
chore(topology/constructions): golf a proof ([#12174](https://github.com/leanprover-community/mathlib/pull/12174))
#### Estimated changes
modified src/topology/constructions.lean
- \+/\- *lemma* is_open_sigma_fst_preimage
- \+/\- *lemma* is_open_sigma_fst_preimage



## [2022-02-21 10:14:54](https://github.com/leanprover-community/mathlib/commit/d0fa7a8)
chore(category_theory/limits): make fin_category_opposite an instance ([#12153](https://github.com/leanprover-community/mathlib/pull/12153))
#### Estimated changes
modified src/category_theory/fin_category.lean
- \- *def* fin_category_opposite

modified src/category_theory/limits/opposites.lean



## [2022-02-21 09:47:15](https://github.com/leanprover-community/mathlib/commit/b04851f)
chore(tactic): fix tactic doc tags ([#12131](https://github.com/leanprover-community/mathlib/pull/12131))
#### Estimated changes
modified src/tactic/linear_combination.lean

modified src/tactic/rewrite_search/frontend.lean



## [2022-02-21 08:48:32](https://github.com/leanprover-community/mathlib/commit/8b93d3a)
feat(measure_theory/function/lp_space): generalize some `integrable` lemmas to `mem_ℒp` ([#11231](https://github.com/leanprover-community/mathlib/pull/11231))
I would like to define integrable as `mem_ℒp` for `p = 1` and remove the `has_finite_integral` prop. But first we need to generalize everything we have about `integrable` to `mem_ℒp`. This is one step towards that goal.
#### Estimated changes
modified src/measure_theory/function/ess_sup.lean
- \+ *lemma* ess_sup_comp_le_ess_sup_map_measure
- \+ *lemma* _root_.measurable_embedding.ess_sup_map_measure
- \+ *lemma* ess_sup_map_measure_of_measurable
- \+ *lemma* ess_sup_map_measure

modified src/measure_theory/function/l1_space.lean

modified src/measure_theory/function/lp_space.lean
- \+ *lemma* mem_ℒp.smul_measure
- \+ *lemma* snorm_one_add_measure
- \+ *lemma* snorm_le_add_measure_right
- \+ *lemma* snorm_le_add_measure_left
- \+ *lemma* mem_ℒp.left_of_add_measure
- \+ *lemma* mem_ℒp.right_of_add_measure
- \+ *lemma* snorm_ess_sup_map_measure
- \+ *lemma* snorm_map_measure
- \+ *lemma* mem_ℒp_map_measure_iff
- \+ *lemma* _root_.measurable_embedding.snorm_ess_sup_map_measure
- \+ *lemma* _root_.measurable_embedding.snorm_map_measure
- \+ *lemma* _root_.measurable_embedding.mem_ℒp_map_measure_iff
- \+ *lemma* _root_.measurable_equiv.mem_ℒp_map_measure_iff



## [2022-02-21 08:00:52](https://github.com/leanprover-community/mathlib/commit/e60e1f2)
feat(data/real/pointwise): mul distributes over `infi` and `supr` ([#12105](https://github.com/leanprover-community/mathlib/pull/12105))
#### Estimated changes
modified src/data/real/pointwise.lean
- \+ *lemma* real.smul_infi_of_nonneg
- \+ *lemma* real.smul_supr_of_nonneg
- \+ *lemma* real.smul_supr_of_nonpos
- \+ *lemma* real.smul_infi_of_nonpos
- \+ *lemma* real.mul_infi_of_nonneg
- \+ *lemma* real.mul_supr_of_nonneg
- \+ *lemma* real.mul_infi_of_nonpos
- \+ *lemma* real.mul_supr_of_nonpos
- \+ *lemma* real.infi_mul_of_nonneg
- \+ *lemma* real.supr_mul_of_nonneg
- \+ *lemma* real.infi_mul_of_nonpos
- \+ *lemma* real.supr_mul_of_nonpos



## [2022-02-21 00:51:52](https://github.com/leanprover-community/mathlib/commit/6298a43)
feat(analysis/seminorm): smul_sup ([#12103](https://github.com/leanprover-community/mathlib/pull/12103))
The `have : real.smul_max` local proof doesn't feel very general, so I've left it as a `have` rather than promoting it to a lemma.
#### Estimated changes
modified src/analysis/seminorm.lean
- \+ *lemma* sup_apply
- \+ *lemma* smul_sup



## [2022-02-21 00:51:51](https://github.com/leanprover-community/mathlib/commit/6ecd7ab)
feat(topology/continuous_function/bounded): generalize scalar action ([#12098](https://github.com/leanprover-community/mathlib/pull/12098))
This also makes the scalar action computable
#### Estimated changes
modified src/topology/continuous_function/bounded.lean



## [2022-02-20 23:53:46](https://github.com/leanprover-community/mathlib/commit/6ae1b70)
feat(topology/uniform_space/cauchy): add `cauchy_seq.comp_injective` ([#11986](https://github.com/leanprover-community/mathlib/pull/11986))
API changes:
- add `filter.at_top_le_cofinite`;
- add `function.injective.nat_tendsto_at_top`;
- add `cauchy_seq.comp_injective`, `function.bijective.cauchy_seq_comp_iff`.
#### Estimated changes
modified src/order/filter/cofinite.lean
- \+ *lemma* at_top_le_cofinite
- \+/\- *lemma* function.injective.tendsto_cofinite
- \+ *lemma* function.injective.nat_tendsto_at_top
- \+/\- *lemma* function.injective.tendsto_cofinite

modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy_seq.comp_injective
- \+ *lemma* function.bijective.cauchy_seq_comp_iff



## [2022-02-20 22:01:51](https://github.com/leanprover-community/mathlib/commit/7e1ef9f)
feat(ring_theory/witt_vector): assorted facts about Witt vectors over char p rings ([#12093](https://github.com/leanprover-community/mathlib/pull/12093))
#### Estimated changes
modified src/ring_theory/witt_vector/frobenius.lean
- \+ *lemma* frobenius_bijective

modified src/ring_theory/witt_vector/identities.lean
- \+ *lemma* p_nonzero
- \+ *lemma* fraction_ring.p_nonzero



## [2022-02-20 14:25:15](https://github.com/leanprover-community/mathlib/commit/334fb89)
feat(algebra/order/ring): add three_ne_zero and four_ne_zero ([#12142](https://github.com/leanprover-community/mathlib/pull/12142))
#### Estimated changes
modified src/algebra/order/ring.lean
- \+ *lemma* three_ne_zero
- \+ *lemma* four_ne_zero



## [2022-02-20 09:43:13](https://github.com/leanprover-community/mathlib/commit/6c6e142)
chore(data/nat/factorization): Reorder lemmas and some minor golfing ([#12144](https://github.com/leanprover-community/mathlib/pull/12144))
Some minor housework on this file, reordering and regrouping lemmas, adding and editing a few docstrings and section headers, and golfing a few proofs.
#### Estimated changes
modified src/data/nat/factorization.lean
- \+/\- *lemma* prime_of_mem_factorization
- \+/\- *lemma* pos_of_mem_factorization
- \+/\- *lemma* prime.factorization_pos_of_dvd
- \+/\- *lemma* factorization_mul_support
- \+/\- *lemma* factorization_pow
- \+/\- *lemma* dvd_of_mem_factorization
- \+/\- *lemma* pow_factorization_dvd
- \+/\- *lemma* pow_succ_factorization_not_dvd
- \+/\- *lemma* factorization_mul_apply_of_coprime
- \+/\- *lemma* factorization_mul_of_coprime
- \+/\- *lemma* factorization_eq_of_coprime_left
- \+/\- *lemma* factorization_eq_of_coprime_right
- \+/\- *lemma* factorization_disjoint_of_coprime
- \+/\- *lemma* factorization_mul_support_of_coprime
- \+/\- *lemma* multiplicative_factorization
- \+/\- *lemma* multiplicative_factorization'
- \+/\- *lemma* prime_of_mem_factorization
- \+/\- *lemma* pos_of_mem_factorization
- \+/\- *lemma* factorization_pow
- \+/\- *lemma* factorization_mul_apply_of_coprime
- \+/\- *lemma* factorization_eq_of_coprime_left
- \+/\- *lemma* factorization_eq_of_coprime_right
- \+/\- *lemma* pow_factorization_dvd
- \+/\- *lemma* pow_succ_factorization_not_dvd
- \+/\- *lemma* prime.factorization_pos_of_dvd
- \+/\- *lemma* factorization_disjoint_of_coprime
- \+/\- *lemma* factorization_mul_of_coprime
- \+/\- *lemma* factorization_mul_support_of_coprime
- \+/\- *lemma* factorization_mul_support
- \+/\- *lemma* multiplicative_factorization
- \+/\- *lemma* multiplicative_factorization'
- \+/\- *lemma* dvd_of_mem_factorization
- \+/\- *def* rec_on_prime_pow
- \+ *def* rec_on_pos_prime_pos_coprime
- \+/\- *def* rec_on_prime_coprime
- \+/\- *def* rec_on_mul
- \+/\- *def* rec_on_prime_pow
- \- *def* rec_on_pos_prime_coprime
- \+/\- *def* rec_on_prime_coprime
- \+/\- *def* rec_on_mul



## [2022-02-20 01:22:26](https://github.com/leanprover-community/mathlib/commit/55c9cff)
chore(data/nat/prime): slightly weaken assumption in nat.exists_prime_and_dvd ([#12156](https://github.com/leanprover-community/mathlib/pull/12156))
It is vacuously true for zero, as everything divides zero.
#### Estimated changes
modified src/algebra/squarefree.lean

modified src/data/nat/prime.lean
- \+/\- *theorem* exists_prime_and_dvd
- \+/\- *theorem* exists_prime_and_dvd

modified src/data/pnat/prime.lean
- \+/\- *lemma* exists_prime_and_dvd
- \+/\- *lemma* exists_prime_and_dvd

modified src/ring_theory/int/basic.lean
- \+/\- *lemma* int.exists_prime_and_dvd
- \+/\- *lemma* int.exists_prime_and_dvd



## [2022-02-20 00:00:55](https://github.com/leanprover-community/mathlib/commit/fa603fe)
feat(order/category/FinPartialOrder): The category of finite partial orders ([#11997](https://github.com/leanprover-community/mathlib/pull/11997))
Define `FinPartialOrder`, the category of finite partial orders with monotone functions.
#### Estimated changes
created src/order/category/FinPartialOrder.lean
- \+ *lemma* FinPartialOrder_dual_comp_forget_to_PartialOrder
- \+ *def* of
- \+ *def* iso.mk
- \+ *def* dual
- \+ *def* dual_equiv



## [2022-02-19 22:26:11](https://github.com/leanprover-community/mathlib/commit/5611533)
feat(analysis/normed_space/star/complex): real and imaginary part of an element of a star module ([#11811](https://github.com/leanprover-community/mathlib/pull/11811))
We introduce the real and imaginary parts of an element of a star module, and show that elements of the type can be decomposed into these two parts in the obvious way.
#### Estimated changes
modified src/algebra/invertible.lean
- \+ *lemma* inv_of_two_add_inv_of_two

modified src/algebra/module/basic.lean
- \+ *lemma* inv_of_two_smul_add_inv_of_two_smul

modified src/algebra/star/module.lean
- \+ *lemma* star_module.self_adjoint_part_add_skew_adjoint_part
- \+ *def* self_adjoint.submodule
- \+ *def* skew_adjoint.submodule
- \+ *def* self_adjoint_part
- \+ *def* skew_adjoint_part
- \+ *def* star_module.decompose_prod_adjoint

modified src/analysis/normed_space/exponential.lean

created src/analysis/normed_space/star/complex.lean
- \+ *lemma* re_add_im
- \+ *def* mul_neg_I_lin

modified src/analysis/special_functions/exponential.lean

modified src/data/complex/basic.lean
- \+/\- *lemma* star_def
- \+ *lemma* conj_inv
- \+/\- *lemma* star_def

modified src/data/complex/is_R_or_C.lean
- \+ *lemma* star_def
- \+ *lemma* conj_inv
- \- *lemma* char_zero_R_or_C

modified src/data/complex/module.lean



## [2022-02-19 21:14:08](https://github.com/leanprover-community/mathlib/commit/3777543)
feat(category_theory/isomorphism): two lemmas is_iso.of_iso_comp_left/right on isomorphisms ([#12056](https://github.com/leanprover-community/mathlib/pull/12056))
#### Estimated changes
modified src/category_theory/isomorphism.lean
- \+ *lemma* of_is_iso_comp_left
- \+ *lemma* of_is_iso_comp_right
- \+ *lemma* of_is_iso_fac_left
- \+ *lemma* of_is_iso_fac_right



## [2022-02-19 19:27:37](https://github.com/leanprover-community/mathlib/commit/bc63071)
feat(algebra/is_prime_pow): dot notation for nat.prime ([#12145](https://github.com/leanprover-community/mathlib/pull/12145))
#### Estimated changes
modified src/algebra/is_prime_pow.lean
- \+ *lemma* nat.prime.is_prime_pow



## [2022-02-19 19:27:36](https://github.com/leanprover-community/mathlib/commit/628e8fb)
doc(group_theory/coset): Mention "Lagrange's theorem" ([#12137](https://github.com/leanprover-community/mathlib/pull/12137))
Suggested here: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.E2.9C.94.20Lagrange's.20Theorem.20.28Group.20theory.29/near/272469211
#### Estimated changes
modified src/group_theory/coset.lean



## [2022-02-19 18:23:35](https://github.com/leanprover-community/mathlib/commit/e88badb)
feat(analysis/inner_product_space/pi_L2): Orthonormal basis ([#12060](https://github.com/leanprover-community/mathlib/pull/12060))
Added the structure orthonormal_basis and basic associated API
Renamed the previous definition orthonormal_basis in analysis/inner_product_space/projection to std_orthonormal_basis
#### Estimated changes
modified src/analysis/inner_product_space/orientation.lean

modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* euclidean_space.inner_single_left
- \+ *lemma* euclidean_space.inner_single_right
- \+ *lemma* _root_.basis.coe_to_orthonormal_basis_repr
- \+ *lemma* _root_.basis.coe_to_orthonormal_basis_repr_symm
- \+ *lemma* _root_.basis.to_basis_to_orthonormal_basis
- \+ *lemma* _root_.basis.coe_to_orthonormal_basis
- \- *lemma* basis.coe_isometry_euclidean_of_orthonormal
- \- *lemma* basis.coe_isometry_euclidean_of_orthonormal_symm
- \+ *theorem* euclidean_space.single_apply
- \+ *def* euclidean_space.single
- \+ *def* _root_.basis.to_orthonormal_basis
- \- *def* basis.isometry_euclidean_of_orthonormal

modified src/analysis/inner_product_space/projection.lean
- \+ *lemma* std_orthonormal_basis_orthonormal
- \+ *lemma* coe_std_orthonormal_basis
- \+ *lemma* fin_std_orthonormal_basis_orthonormal
- \- *lemma* orthonormal_basis_orthonormal
- \- *lemma* coe_orthonormal_basis
- \- *lemma* fin_orthonormal_basis_orthonormal
- \+ *def* std_orthonormal_basis
- \+ *def* fin_std_orthonormal_basis
- \- *def* orthonormal_basis
- \- *def* fin_orthonormal_basis

modified src/analysis/inner_product_space/spectrum.lean

modified src/linear_algebra/basis.lean
- \+ *lemma* basis.of_equiv_fun_equiv_fun



## [2022-02-19 07:54:42](https://github.com/leanprover-community/mathlib/commit/518b5d2)
chore(topology/bases): golf a proof ([#12127](https://github.com/leanprover-community/mathlib/pull/12127))
Also add `function.injective_iff_pairwise_ne`.
#### Estimated changes
modified src/data/set/pairwise.lean
- \+ *lemma* function.injective_iff_pairwise_ne

modified src/topology/bases.lean

modified src/topology/dense_embedding.lean
- \- *lemma* preconnected_space



## [2022-02-18 21:46:45](https://github.com/leanprover-community/mathlib/commit/213e2ed)
feat(algebra/group/pi): add pi.nsmul_apply ([#12122](https://github.com/leanprover-community/mathlib/pull/12122))
via to_additive
#### Estimated changes
modified src/algebra/group/pi.lean
- \+/\- *lemma* pow_apply
- \+/\- *lemma* pow_apply



## [2022-02-18 21:46:43](https://github.com/leanprover-community/mathlib/commit/b3d0944)
feat(tactic/swap_var): name juggling, a weaker wlog ([#12006](https://github.com/leanprover-community/mathlib/pull/12006))
#### Estimated changes
created src/tactic/swap_var.lean

created test/swap_var.lean



## [2022-02-18 19:52:47](https://github.com/leanprover-community/mathlib/commit/5f46dd0)
fix(category_theory/limits): improve inaccurate docstrings ([#12130](https://github.com/leanprover-community/mathlib/pull/12130))
#### Estimated changes
modified src/category_theory/limits/shapes/images.lean



## [2022-02-18 19:52:46](https://github.com/leanprover-community/mathlib/commit/7b6c407)
feat(number_theory/divisors): add `prod_div_divisors` and `sum_div_divisors` ([#12087](https://github.com/leanprover-community/mathlib/pull/12087))
Adds lemma `prod_div_divisors : ∏ d in n.divisors, f (n/d) = n.divisors.prod f` and `sum_div_divisors`.
Also proves `image_div_divisors_eq_divisors : image (λ (x : ℕ), n / x) n.divisors = n.divisors`
and `div_eq_iff_eq_of_dvd_dvd : n / x = n / y ↔ x = y` (where `n ≠ 0` and `x ∣ n` and `y ∣ n`)
#### Estimated changes
modified src/data/nat/basic.lean
- \+ *lemma* div_eq_iff_eq_of_dvd_dvd

modified src/number_theory/divisors.lean
- \+ *lemma* image_div_divisors_eq_divisors
- \+ *lemma* prod_div_divisors



## [2022-02-18 19:52:44](https://github.com/leanprover-community/mathlib/commit/33179f7)
refactor(topology/metric_space/completion): change namespace ([#12077](https://github.com/leanprover-community/mathlib/pull/12077))
Move lemmas about metric on `uniform_space.completion` from `metric.completion` namespace to `uniform_space.completion`.
#### Estimated changes
modified src/analysis/normed/group/completion.lean

modified src/topology/metric_space/completion.lean
- \+ *lemma* coe_isometry
- \- *lemma* completion.coe_isometry

modified src/topology/metric_space/gromov_hausdorff.lean



## [2022-02-18 19:52:43](https://github.com/leanprover-community/mathlib/commit/18c3e3f)
feat(data/nat/fib): add that `fib` is sum of `nat.choose` along antidiagonal ([#12063](https://github.com/leanprover-community/mathlib/pull/12063))
#### Estimated changes
modified src/data/nat/fib.lean
- \+ *lemma* fib_succ_eq_sum_choose



## [2022-02-18 19:21:11](https://github.com/leanprover-community/mathlib/commit/ffc2bdf)
refactor(group_theory/abelianization): Define `commutator` in terms of `general_commutator` ([#11949](https://github.com/leanprover-community/mathlib/pull/11949))
It seems reasonable to define `commutator` in terms of `general_commutator`.
#### Estimated changes
modified src/group_theory/abelianization.lean
- \+ *lemma* commutator_def
- \+ *lemma* commutator_eq_closure
- \+ *lemma* commutator_eq_normal_closure

modified src/group_theory/nilpotent.lean
- \+/\- *lemma* lower_central_series_one
- \+/\- *lemma* lower_central_series_one

modified src/group_theory/solvable.lean
- \- *lemma* general_commutator_eq_commutator
- \- *lemma* commutator_def'



## [2022-02-18 18:09:38](https://github.com/leanprover-community/mathlib/commit/018c728)
refactor(ring_theory/fractional_ideal): rename lemmas for dot notation, add coe_pow ([#12080](https://github.com/leanprover-community/mathlib/pull/12080))
This replaces `fractional_ideal.fractional_mul` with `is_fractional.mul` and likewise for the other operations. The bundling was a distraction for the content of the lemmas anyway.
#### Estimated changes
modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* _root_.is_fractional.sup
- \+ *lemma* _root_.is_fractional.inf_right
- \+ *lemma* _root_.is_fractional.mul
- \+ *lemma* _root_.is_fractional.pow
- \+ *lemma* coe_pow
- \+ *lemma* _root_.is_fractional.map
- \+ *lemma* _root_.is_fractional.div_of_nonzero
- \+/\- *lemma* fractional_div_of_nonzero
- \- *lemma* fractional_sup
- \- *lemma* fractional_inf
- \- *lemma* fractional_mul
- \- *lemma* fractional_map
- \+/\- *lemma* fractional_div_of_nonzero



## [2022-02-18 18:09:37](https://github.com/leanprover-community/mathlib/commit/bcf8a6e)
feat(ring_theory/fractional_ideal): add coe_ideal lemmas ([#12073](https://github.com/leanprover-community/mathlib/pull/12073))
#### Estimated changes
modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* coe_ideal_pow
- \+ *lemma* coe_ideal_finprod



## [2022-02-18 16:58:17](https://github.com/leanprover-community/mathlib/commit/98643bc)
feat(algebra/big_operators/intervals): summation by parts ([#11814](https://github.com/leanprover-community/mathlib/pull/11814))
Add the "summation by parts" identity over intervals of natural numbers, as well as some helper lemmas.
#### Estimated changes
modified src/algebra/big_operators/intervals.lean
- \+ *lemma* prod_Ico_add'
- \+ *lemma* prod_range_succ_div_prod
- \+ *lemma* prod_range_succ_div_top
- \+ *lemma* prod_Ico_div_bot
- \+ *lemma* prod_Ico_succ_div_top
- \+ *lemma* sum_range_by_parts
- \- *lemma* sum_Ico_add
- \+ *theorem* sum_Ico_by_parts



## [2022-02-18 15:07:45](https://github.com/leanprover-community/mathlib/commit/3ca16d0)
feat(data/equiv): define `ring_equiv_class` ([#11977](https://github.com/leanprover-community/mathlib/pull/11977))
This PR applies the morphism class pattern to `ring_equiv`, producing a new `ring_equiv_class` extending `mul_equiv_class` and `add_equiv_class`. It also provides a `ring_equiv_class` instance for `alg_equiv`s.
#### Estimated changes
modified src/algebra/algebra/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext
- \- *lemma* ext_iff
- \- *lemma* map_add
- \- *lemma* map_zero
- \- *lemma* map_mul
- \- *lemma* map_one
- \- *lemma* map_pow
- \- *lemma* injective
- \- *lemma* surjective
- \- *lemma* bijective
- \- *lemma* map_neg
- \- *lemma* map_sub

modified src/algebra/ring/basic.lean
- \+ *lemma* coe_coe

modified src/data/equiv/ring.lean
- \+/\- *lemma* ext
- \+/\- *lemma* map_ne_zero_iff
- \+/\- *lemma* map_ne_one_iff
- \- *lemma* map_mul
- \- *lemma* map_add
- \+/\- *lemma* ext
- \- *lemma* ext_iff
- \- *lemma* map_zero
- \- *lemma* map_eq_zero_iff
- \+/\- *lemma* map_ne_zero_iff
- \- *lemma* map_one
- \- *lemma* map_eq_one_iff
- \+/\- *lemma* map_ne_one_iff
- \- *lemma* map_neg
- \- *lemma* map_sub
- \- *lemma* map_pow

modified src/data/mv_polynomial/equiv.lean

modified src/ring_theory/algebraic_independent.lean

modified src/ring_theory/finiteness.lean



## [2022-02-18 14:37:42](https://github.com/leanprover-community/mathlib/commit/223f149)
chore(algebra/star/self_adjoint): extract a lemma from `has_scalar` ([#12121](https://github.com/leanprover-community/mathlib/pull/12121))
#### Estimated changes
modified src/algebra/star/self_adjoint.lean
- \+ *lemma* smul_mem
- \+ *lemma* smul_mem



## [2022-02-18 13:41:21](https://github.com/leanprover-community/mathlib/commit/aed97e0)
doc(analysis/normed/group/basic): add docstring explaining the "insert" name ([#12100](https://github.com/leanprover-community/mathlib/pull/12100))
#### Estimated changes
modified src/analysis/normed/group/basic.lean



## [2022-02-18 12:57:33](https://github.com/leanprover-community/mathlib/commit/3e6439c)
fix(category_theory/limits/shapes/images): make class a Prop ([#12119](https://github.com/leanprover-community/mathlib/pull/12119))
#### Estimated changes
modified src/category_theory/limits/shapes/images.lean



## [2022-02-18 11:05:58](https://github.com/leanprover-community/mathlib/commit/33b4e73)
refactor(topology/algebra): reorder imports ([#12089](https://github.com/leanprover-community/mathlib/pull/12089))
* move `mul_opposite.topological_space` and `units.topological_space` to a new file;
* import `mul_action` in `monoid`, not vice versa.
With this order of imports, we can reuse results about `has_continuous_smul` in lemmas about topological monoids.
#### Estimated changes
modified src/analysis/convex/strict.lean

created src/topology/algebra/constructions.lean
- \+ *lemma* continuous_unop
- \+ *lemma* continuous_op
- \+ *lemma* continuous_embed_product
- \+ *lemma* continuous_coe
- \+ *def* op_homeomorph

modified src/topology/algebra/group.lean

modified src/topology/algebra/monoid.lean
- \- *lemma* continuous_unop
- \- *lemma* continuous_op
- \- *lemma* continuous_embed_product
- \- *lemma* continuous_coe

modified src/topology/algebra/mul_action.lean



## [2022-02-18 07:37:58](https://github.com/leanprover-community/mathlib/commit/77f264f)
feat(data/finset/basic): add lemma `filter_eq_empty_iff` ([#12104](https://github.com/leanprover-community/mathlib/pull/12104))
Add `filter_eq_empty_iff : (s.filter p = ∅) ↔ ∀ x ∈ s, ¬ p x`
We already have the right-to-left direction of this in `filter_false_of_mem`.
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* filter_eq_empty_iff



## [2022-02-18 05:49:20](https://github.com/leanprover-community/mathlib/commit/bb1b56c)
feat(algebra/indicator_function): smul lemmas for functions ([#12059](https://github.com/leanprover-community/mathlib/pull/12059))
And a few basic lemmas in `set/basic`.
#### Estimated changes
modified src/algebra/indicator_function.lean
- \+/\- *lemma* indicator_smul_apply
- \+/\- *lemma* indicator_smul
- \+ *lemma* indicator_const_smul_apply
- \+ *lemma* indicator_const_smul
- \+/\- *lemma* indicator_smul_apply
- \+/\- *lemma* indicator_smul

modified src/analysis/box_integral/integrability.lean

modified src/data/finsupp/basic.lean

modified src/data/set/basic.lean
- \+ *lemma* compl_range_inl
- \+ *lemma* compl_range_inr

modified src/logic/nonempty.lean
- \+ *lemma* function.surjective.nonempty



## [2022-02-18 04:52:16](https://github.com/leanprover-community/mathlib/commit/17b3357)
feat(topology/algebra): generalize `has_continuous_smul` arguments to `has_continuous_const_smul` ([#11999](https://github.com/leanprover-community/mathlib/pull/11999))
This changes the majority of the downstream call-sites of the `const_smul` lemmas to only need the weaker typeclass.
#### Estimated changes
modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/complex/cauchy_integral.lean

modified src/analysis/convex/strict.lean
- \+/\- *lemma* strict_convex.smul
- \+/\- *lemma* strict_convex.affinity
- \+/\- *lemma* strict_convex.smul
- \+/\- *lemma* strict_convex.affinity

modified src/analysis/convex/topology.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/operator_norm.lean
- \+/\- *def* prodₗᵢ
- \+/\- *def* prodₗᵢ

modified src/dynamics/minimal.lean
- \+/\- *lemma* is_compact.exists_finite_cover_smul
- \+/\- *lemma* is_minimal_iff_closed_smul_invariant
- \+/\- *lemma* is_compact.exists_finite_cover_smul
- \+/\- *lemma* is_minimal_iff_closed_smul_invariant

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/function/ae_eq_fun.lean

modified src/measure_theory/group/action.lean

modified src/measure_theory/measure/complex.lean

modified src/measure_theory/measure/vector_measure.lean
- \+/\- *lemma* smul
- \+/\- *lemma* smul_right
- \+/\- *lemma* smul_left
- \+/\- *lemma* smul
- \+/\- *lemma* smul_right
- \+/\- *lemma* smul_left

modified src/topology/algebra/affine.lean

modified src/topology/algebra/const_mul_action.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/module/basic.lean

modified src/topology/algebra/module/multilinear.lean

modified src/topology/algebra/module/weak_dual.lean

modified src/topology/continuous_function/locally_constant.lean
- \+/\- *def* to_continuous_map_linear_map
- \+/\- *def* to_continuous_map_alg_hom
- \+/\- *def* to_continuous_map_linear_map
- \+/\- *def* to_continuous_map_alg_hom



## [2022-02-18 02:05:51](https://github.com/leanprover-community/mathlib/commit/b757206)
feat(linear_algebra/finite_dimensional): finrank_range_of_inj ([#12067](https://github.com/leanprover-community/mathlib/pull/12067))
The dimensions of the domain and range of an injective linear map are
equal.
#### Estimated changes
modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* finrank_map_eq
- \+/\- *lemma* finrank_map_subtype_eq
- \+ *lemma* finrank_range_of_inj
- \+/\- *lemma* finrank_map_eq
- \+/\- *lemma* finrank_map_subtype_eq
- \+/\- *theorem* finrank_eq
- \+/\- *theorem* finrank_eq



## [2022-02-18 00:52:54](https://github.com/leanprover-community/mathlib/commit/59a183a)
feat(data/finset/locally_finite): add Ico_subset_Ico_union_Ico ([#11710](https://github.com/leanprover-community/mathlib/pull/11710))
This lemma extends the result for `set`s to `finset`s.
#### Estimated changes
modified src/data/finset/locally_finite.lean
- \+ *lemma* Ico_subset_Ico_union_Ico



## [2022-02-17 22:59:24](https://github.com/leanprover-community/mathlib/commit/e93996c)
feat(topology/instances/discrete): instances for the discrete topology ([#11349](https://github.com/leanprover-community/mathlib/pull/11349))
Prove `first_countable_topology`, `second_countable_topology` and `order_topology` for the discrete topology under appropriate conditions like `encodable`, or being a linear order with `pred` and `succ`. These instances give in particular `second_countable_topology ℕ` and `order_topology ℕ`
#### Estimated changes
modified src/order/filter/bases.lean
- \+ *lemma* is_countably_generated_pure

modified src/order/succ_pred/basic.lean
- \+ *lemma* lt_succ_of_not_is_max
- \+ *lemma* lt_succ_iff_of_not_is_max
- \+ *lemma* succ_le_iff_of_not_is_max
- \+ *lemma* Iic_eq_Iio_succ'
- \+ *lemma* Iic_eq_Iio_succ
- \+ *lemma* Ioi_eq_Ici_succ'
- \+ *lemma* Ioi_eq_Ici_succ
- \+ *lemma* pred_lt_of_not_is_min
- \+ *lemma* pred_lt_iff_of_not_is_min
- \+ *lemma* le_pred_iff_of_not_is_min
- \+ *lemma* Ici_eq_Ioi_pred'
- \+ *lemma* Ici_eq_Ioi_pred
- \+ *lemma* Iio_eq_Iic_pred'
- \+ *lemma* Iio_eq_Iic_pred

modified src/topology/bases.lean

created src/topology/instances/discrete.lean

modified src/topology/order.lean
- \+ *lemma* is_open_generate_from_of_mem



## [2022-02-17 21:50:25](https://github.com/leanprover-community/mathlib/commit/6089f08)
feat(data/nat/totient): add Euler's product formula for totient function ([#11332](https://github.com/leanprover-community/mathlib/pull/11332))
Proving four versions of Euler's product formula for the totient function `φ`:
* `totient_eq_prod_factorization :  φ n = n.factorization.prod (λ p k, p ^ (k - 1) * (p - 1))`
* `totient_mul_prod_factors : φ n * ∏ p in n.factors.to_finset, p = n * ∏ p in n.factors.to_finset, (p - 1)`
* `totient_eq_div_factors_mul : φ n = n / (∏ p in n.factors.to_finset, p) * (∏ p in n.factors.to_finset, (p - 1))`
* `totient_eq_mul_prod_factors : (φ n : ℚ) = n * ∏ p in n.factors.to_finset, (1 - p⁻¹)`
#### Estimated changes
modified src/data/nat/factorization.lean
- \+ *lemma* prod_factorization_eq_prod_factors

modified src/data/nat/prime.lean
- \+ *lemma* pos_of_mem_factors

modified src/data/nat/totient.lean
- \+ *theorem* totient_eq_prod_factorization
- \+ *theorem* totient_mul_prod_factors
- \+ *theorem* totient_eq_div_factors_mul
- \+ *theorem* totient_eq_mul_prod_factors



## [2022-02-17 21:06:46](https://github.com/leanprover-community/mathlib/commit/19534b2)
feat(analysis/inner_product_space/basic) : `inner_map_self_eq_zero` ([#12065](https://github.com/leanprover-community/mathlib/pull/12065))
The main result here is:  If ⟪T x, x⟫_C = 0 for all x, then T = 0.
The proof uses a polarization identity.  Note that this is false
with R in place of C.  I am confident that my use of ring_nf is
not optimal, but I hope to learn from the cleanup process!
#### Estimated changes
modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* inner_map_polarization
- \+ *lemma* inner_map_self_eq_zero



## [2022-02-17 22:00:06+01:00](https://github.com/leanprover-community/mathlib/commit/8b6901b)
Revert "feat(category_theory/limits): is_bilimit"
This reverts commit 8edfa75d79ad70c88dbae01ab6166dd8b1fd2ba0.
#### Estimated changes
modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *lemma* bicone_ι_π_ne
- \+/\- *lemma* bicone_ι_π_ne
- \- *lemma* ι_of_is_limit
- \- *lemma* π_of_is_colimit
- \+/\- *def* to_binary_bicone_is_limit
- \+/\- *def* to_binary_bicone_is_colimit
- \- *def* of_limit_cone
- \- *def* of_colimit_cocone
- \- *def* biproduct.is_bilimit
- \- *def* to_bicone
- \- *def* to_bicone_is_limit
- \- *def* to_bicone_is_colimit
- \+/\- *def* to_binary_bicone_is_limit
- \+/\- *def* to_binary_bicone_is_colimit
- \- *def* binary_bicone.to_bicone_is_bilimit
- \- *def* bicone.to_binary_bicone_is_bilimit
- \- *def* binary_biproduct.is_bilimit



## [2022-02-17 21:56:42+01:00](https://github.com/leanprover-community/mathlib/commit/8edfa75)
feat(category_theory/limits): is_bilimit
#### Estimated changes
modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *lemma* bicone_ι_π_ne
- \+ *lemma* ι_of_is_limit
- \+ *lemma* π_of_is_colimit
- \+/\- *lemma* bicone_ι_π_ne
- \+ *def* of_limit_cone
- \+ *def* of_colimit_cocone
- \+ *def* biproduct.is_bilimit
- \+ *def* to_bicone
- \+ *def* to_bicone_is_limit
- \+ *def* to_bicone_is_colimit
- \+/\- *def* to_binary_bicone_is_limit
- \+/\- *def* to_binary_bicone_is_colimit
- \+ *def* binary_bicone.to_bicone_is_bilimit
- \+ *def* bicone.to_binary_bicone_is_bilimit
- \+ *def* binary_biproduct.is_bilimit
- \+/\- *def* to_binary_bicone_is_limit
- \+/\- *def* to_binary_bicone_is_colimit



## [2022-02-17 19:35:15](https://github.com/leanprover-community/mathlib/commit/aacc36c)
feat(group_theory/commensurable): Definition and lemmas about commensurability. ([#9545](https://github.com/leanprover-community/mathlib/pull/9545))
This defines commensurability for subgroups, proves this defines a transitive relation and then defines the commensurator subgroup. In doing so it also needs some lemmas about indices of subgroups and the definition of the conjugate of a subgroup by an element of the parent group.
#### Estimated changes
created src/group_theory/commensurable.lean
- \+ *lemma* comm
- \+ *lemma* symm
- \+ *lemma* trans
- \+ *lemma* equivalence
- \+ *lemma* commensurable_conj
- \+ *lemma* commensurable_inv
- \+ *lemma* commensurator'_mem_iff
- \+ *lemma* commensurator_mem_iff
- \+ *lemma* eq
- \+ *def* commensurable
- \+ *def* commensurator'
- \+ *def* commensurator



## [2022-02-17 18:46:15](https://github.com/leanprover-community/mathlib/commit/8575f59)
feat(category_theory/limits): preservation of zero morphisms ([#12068](https://github.com/leanprover-community/mathlib/pull/12068))
#### Estimated changes
modified src/category_theory/differential_object.lean

created src/category_theory/limits/preserves/shapes/zero.lean
- \+ *lemma* preserves_zero_morphisms_of_map_zero_object
- \+ *def* map_zero_object

modified src/category_theory/limits/shapes/kernels.lean

modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* initial_iso_is_initial
- \+ *def* terminal_iso_is_terminal

modified src/category_theory/limits/shapes/zero.lean
- \+ *lemma* zero_iso_is_initial_hom
- \+ *lemma* zero_iso_is_initial_inv
- \+ *lemma* zero_iso_is_terminal_hom
- \+ *lemma* zero_iso_is_terminal_inv
- \+ *lemma* zero_iso_initial_hom
- \+ *lemma* zero_iso_initial_inv
- \+ *lemma* zero_iso_terminal_hom
- \+ *lemma* zero_iso_terminal_inv
- \- *lemma* equivalence_preserves_zero_morphisms
- \- *lemma* is_equivalence_preserves_zero_morphisms
- \+ *def* zero_iso_is_initial
- \+ *def* zero_iso_is_terminal
- \+ *def* zero_iso_initial
- \+ *def* zero_iso_terminal

modified src/category_theory/preadditive/additive_functor.lean
- \- *lemma* map_zero
- \- *def* map_zero_object

modified src/category_theory/shift.lean



## [2022-02-17 17:02:32](https://github.com/leanprover-community/mathlib/commit/c9e8c64)
chore(*): update to lean 3.39.2c ([#12102](https://github.com/leanprover-community/mathlib/pull/12102))
#### Estimated changes
modified leanpkg.toml



## [2022-02-17 17:02:31](https://github.com/leanprover-community/mathlib/commit/dcb2826)
feat(order/filter/basic): add eventually_eq.(smul/const_smul/sup/inf) ([#12101](https://github.com/leanprover-community/mathlib/pull/12101))
#### Estimated changes
modified src/order/filter/basic.lean
- \+ *lemma* eventually_eq.const_smul
- \+ *lemma* eventually_eq.smul
- \+ *lemma* eventually_eq.sup
- \+ *lemma* eventually_eq.inf



## [2022-02-17 15:34:44](https://github.com/leanprover-community/mathlib/commit/307711e)
feat(group_theory/general_commutator): subgroup.pi commutes with the general_commutator ([#11825](https://github.com/leanprover-community/mathlib/pull/11825))
#### Estimated changes
modified src/group_theory/general_commutator.lean
- \+ *lemma* general_commutator_pi_pi_le
- \+ *lemma* general_commutator_pi_pi_of_fintype

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* le_pi_iff
- \+ *lemma* single_mem_pi
- \+ *lemma* pi_mem_of_single_mem_aux
- \+ *lemma* pi_mem_of_single_mem
- \+ *lemma* pi_le_iff
- \+ *lemma* pi_eq_bot_iff



## [2022-02-17 13:10:49](https://github.com/leanprover-community/mathlib/commit/b54f44f)
feat(data/matrix/notation): expansions of matrix multiplication for 2x2 and 3x3 ([#12088](https://github.com/leanprover-community/mathlib/pull/12088))
A clever way to generalize this would be to make a recursivedefinition of `mul` and `one` that's defeq to the desired `![...]` result and prove that's equal to the usual definition, but that doesn't help with actually writing the lemma statement, which is the tedious bit.
#### Estimated changes
modified src/data/matrix/notation.lean
- \+ *lemma* one_fin_two
- \+ *lemma* one_fin_three
- \+ *lemma* mul_fin_two
- \+ *lemma* mul_fin_three



## [2022-02-17 12:16:09](https://github.com/leanprover-community/mathlib/commit/eb8d58d)
fix(topology/algebra/basic): remove duplicate lemma ([#12097](https://github.com/leanprover-community/mathlib/pull/12097))
This lemma duplicates the lemma of the same name in the root namespace, and should not be in this namespace in the first place.
The other half of [#12072](https://github.com/leanprover-community/mathlib/pull/12072), now that the dependent PR is merged.
#### Estimated changes
modified src/topology/algebra/module/basic.lean
- \- *lemma* continuous_zsmul
- \- *lemma* continuous.zsmul



## [2022-02-17 12:16:07](https://github.com/leanprover-community/mathlib/commit/4afd667)
feat(measure_theory/integral): add `integral_sum_measure` ([#12090](https://github.com/leanprover-community/mathlib/pull/12090))
Also add supporting lemmas about finite and infinite sums of measures.
#### Estimated changes
modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* integrable_zero_measure
- \+/\- *lemma* integrable_zero_measure
- \+ *theorem* integrable_finset_sum_measure

modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* pairwise_ae_disjoint_of_ac

modified src/measure_theory/integral/bochner.lean
- \+ *lemma* nndist_integral_add_measure_le_lintegral
- \+ *theorem* integral_finset_sum_measure
- \+ *theorem* has_sum_integral_measure
- \+ *theorem* integral_sum_measure

modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* lintegral_finset_sum_measure
- \+ *theorem* has_sum_lintegral_measure

modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* has_sum_integral_Union_ae
- \+/\- *lemma* has_sum_integral_Union
- \+ *lemma* integral_Union_ae
- \+/\- *lemma* has_sum_integral_Union
- \- *lemma* has_sum_integral_Union_of_null_inter
- \- *lemma* integral_Union_of_null_inter

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* coe_finset_sum
- \+ *lemma* sum_fintype
- \+ *lemma* sum_coe_finset
- \+ *lemma* sum_add_sum_compl
- \+ *theorem* finset_sum_apply
- \+ *def* coe_add_hom



## [2022-02-17 11:20:26](https://github.com/leanprover-community/mathlib/commit/20cf3ca)
feat(ring_theory/discriminant): add discr_eq_discr_of_to_matrix_coeff_is_integral ([#11994](https://github.com/leanprover-community/mathlib/pull/11994))
We add `discr_eq_discr_of_to_matrix_coeff_is_integral`: if `b` and `b'` are `ℚ`-basis of a number field `K` such that
`∀ i j, is_integral ℤ (b.to_matrix b' i j)` and `∀ i j, is_integral ℤ (b'.to_matrix b i j` then
`discr ℚ b = discr ℚ b'`.
#### Estimated changes
modified src/linear_algebra/matrix/basis.lean
- \+ *lemma* to_matrix_map_vec_mul

modified src/ring_theory/discriminant.lean
- \+ *lemma* discr_reindex
- \+ *lemma* discr_eq_discr_of_to_matrix_coeff_is_integral

modified src/ring_theory/trace.lean
- \+ *lemma* trace_matrix_reindex



## [2022-02-17 10:43:57](https://github.com/leanprover-community/mathlib/commit/614758e)
feat(order/category/DistribLattice): The category of distributive lattices ([#12092](https://github.com/leanprover-community/mathlib/pull/12092))
Define `DistribLattice`, the category of distributive lattices.
#### Estimated changes
created src/order/category/DistribLattice.lean
- \+ *lemma* DistribLattice_dual_comp_forget_to_Lattice
- \+ *def* DistribLattice
- \+ *def* of
- \+ *def* iso.mk
- \+ *def* dual
- \+ *def* dual_equiv

modified src/order/category/Lattice.lean



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
modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* complex.map_isometry_of_orthonormal
- \+ *lemma* complex.isometry_of_orthonormal_symm_apply
- \+ *lemma* complex.isometry_of_orthonormal_apply
- \+ *def* complex.isometry_of_orthonormal



## [2022-02-17 07:43:58](https://github.com/leanprover-community/mathlib/commit/a355d88)
feat(topology/metric_space/gluing): metric space structure on sigma types ([#11965](https://github.com/leanprover-community/mathlib/pull/11965))
We define a (noncanonical) metric space structure on sigma types (aka arbitrary disjoint unions), as follows. Each piece is isometrically embedded in the union, while for `x` and `y` in different pieces their distance is `dist x x0 + 1 + dist y0 y`, where `x0` and `y0` are basepoints in the respective parts. This is *not* registered as an instance.
This definition was already there for sum types (aka disjoint union of two pieces). We also fix this existing definition to avoid `inhabited` assumptions.
#### Estimated changes
modified src/topology/metric_space/gluing.lean
- \+/\- *lemma* sum.dist_eq_glue_dist
- \+ *lemma* isometry_inl
- \+ *lemma* isometry_inr
- \+ *lemma* dist_same
- \+ *lemma* dist_ne
- \+ *lemma* one_le_dist_of_ne
- \+ *lemma* fst_eq_of_dist_lt_one
- \+ *lemma* isometry_mk
- \+/\- *lemma* sum.dist_eq_glue_dist
- \- *lemma* isometry_on_inl
- \- *lemma* isometry_on_inr
- \+ *def* has_dist

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* is_complete_Union_separated



## [2022-02-17 06:05:54](https://github.com/leanprover-community/mathlib/commit/09960ea)
feat(algebra/group_power/basic): `two_zsmul` ([#12094](https://github.com/leanprover-community/mathlib/pull/12094))
Mark `zpow_two` with `@[to_additive two_zsmul]`.  I see no apparent
reason for this result not to use `to_additive`, and I found I had a
use for the additive version.
#### Estimated changes
modified src/algebra/group_power/basic.lean



## [2022-02-17 05:32:27](https://github.com/leanprover-community/mathlib/commit/1831d85)
feat(category_theory/limits): Preserves epi of preserves pushout. ([#12084](https://github.com/leanprover-community/mathlib/pull/12084))
#### Estimated changes
modified src/category_theory/limits/constructions/epi_mono.lean
- \+ *lemma* reflects_epi



## [2022-02-17 00:34:41](https://github.com/leanprover-community/mathlib/commit/84f12be)
chore(algebra/star/self_adjoint): improve definitional unfolding of pow and div ([#12085](https://github.com/leanprover-community/mathlib/pull/12085))
#### Estimated changes
modified src/algebra/star/self_adjoint.lean
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_mul
- \+ *lemma* coe_pow
- \+/\- *lemma* coe_inv
- \+ *lemma* coe_div
- \+ *lemma* coe_zpow
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_inv



## [2022-02-17 00:34:40](https://github.com/leanprover-community/mathlib/commit/834fd30)
feat(topology/continuous_function/algebra): generalize algebra instances ([#12055](https://github.com/leanprover-community/mathlib/pull/12055))
This adds:
* some missing instances in the algebra hierarchy (`comm_semigroup`, `mul_one_class`, `mul_zero_class`, `monoid_with_zero`, `comm_monoid_with_zero`, `comm_semiring`).
* finer-grained scalar action instances, notably none of which require `topological_space R` any more, as they only need `has_continuous_const_smul R M` instead of `has_continuous_smul R M`.
* continuity lemmas about `zpow` on groups and `zsmul` on additive groups (copied directly from the lemmas about `pow` on monoids), which are used to avoid diamonds in the int-action. In order to make room for these, the lemmas about `zpow` on groups with zero have been renamed to `zpow₀`, which is consistent with how the similar clash with `inv` is solved.
* a few lemmas about `mk_of_compact` since an existing proof was broken by `refl` closing the goal earlier than before.
#### Estimated changes
modified src/analysis/fourier.lean

modified src/analysis/special_functions/integrals.lean

modified src/analysis/specific_limits.lean

modified src/measure_theory/integral/circle_integral.lean

modified src/topology/algebra/group.lean
- \+ *lemma* continuous_zpow
- \+ *lemma* continuous.zpow
- \+ *lemma* continuous_on_zpow
- \+ *lemma* continuous_at_zpow
- \+ *lemma* filter.tendsto.zpow
- \+ *lemma* continuous_within_at.zpow
- \+ *lemma* continuous_at.zpow
- \+ *lemma* continuous_on.zpow

modified src/topology/algebra/group_with_zero.lean
- \+ *lemma* continuous_at_zpow₀
- \+ *lemma* continuous_on_zpow₀
- \+ *lemma* filter.tendsto.zpow₀
- \+ *lemma* continuous_at.zpow₀
- \+ *lemma* continuous_within_at.zpow₀
- \+ *lemma* continuous_on.zpow₀
- \+ *lemma* continuous.zpow₀
- \- *lemma* continuous_at_zpow
- \- *lemma* continuous_on_zpow
- \- *lemma* filter.tendsto.zpow
- \- *lemma* continuous_at.zpow
- \- *lemma* continuous_within_at.zpow
- \- *lemma* continuous_on.zpow
- \- *lemma* continuous.zpow

modified src/topology/category/Top/basic.lean

modified src/topology/category/Top/limits.lean

modified src/topology/continuous_function/algebra.lean
- \+/\- *lemma* mul_comp
- \+/\- *lemma* coe_one
- \+/\- *lemma* one_comp
- \+/\- *lemma* coe_pow
- \+/\- *lemma* pow_comp
- \+/\- *lemma* coe_inv
- \+/\- *lemma* inv_comp
- \+/\- *lemma* coe_div
- \+/\- *lemma* div_comp
- \+ *lemma* coe_zpow
- \+ *lemma* zpow_comp
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_comp
- \+/\- *lemma* coe_one
- \+/\- *lemma* mul_comp
- \+/\- *lemma* one_comp
- \+/\- *lemma* coe_pow
- \+/\- *lemma* pow_comp
- \+/\- *lemma* coe_inv
- \+/\- *lemma* coe_div
- \+/\- *lemma* inv_comp
- \+/\- *lemma* div_comp
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* smul_comp

modified src/topology/continuous_function/basic.lean
- \+ *lemma* coe_injective
- \- *lemma* coe_inj

modified src/topology/continuous_function/bounded.lean
- \+ *lemma* mk_of_compact_one
- \+ *lemma* mk_of_compact_add
- \+ *lemma* mk_of_compact_neg
- \+ *lemma* mk_of_compact_sub

modified src/topology/continuous_function/compact.lean

modified src/topology/tietze_extension.lean



## [2022-02-17 00:34:39](https://github.com/leanprover-community/mathlib/commit/27df8a0)
feat(topology/instances/rat): some facts about topology on `rat` ([#11832](https://github.com/leanprover-community/mathlib/pull/11832))
* `ℚ` is a totally disconnected space;
* `cocompact  ℚ` is not a countably generated filter;
* hence, `alexandroff  ℚ` is not a first countable topological space.
#### Estimated changes
modified src/topology/dense_embedding.lean
- \+ *lemma* interior_compact_eq_empty

created src/topology/instances/rat.lean
- \+ *lemma* interior_compact_eq_empty
- \+ *lemma* dense_compl_compact
- \+ *lemma* not_countably_generated_cocompact
- \+ *lemma* not_countably_generated_nhds_infty_alexandroff
- \+ *lemma* not_first_countable_topology_alexandroff
- \+ *lemma* not_second_countable_topology_alexandroff



## [2022-02-16 22:44:23](https://github.com/leanprover-community/mathlib/commit/7dae87f)
feat(topology/metric_space/basic): ext lemmas for metric spaces ([#12070](https://github.com/leanprover-community/mathlib/pull/12070))
Also add a few results in `metric_space.basic`:
* A decreasing intersection of closed sets with diameter tending to `0` is nonempty in a complete space
* new constructions of metric spaces by pulling back structures (and adjusting definitional equalities)
* fixing `metric_space empty` and `metric_space punit` to make sure the uniform structure is definitionally the right one.
#### Estimated changes
modified src/order/filter/basic.lean
- \+ *lemma* eq_top_of_ne_bot

modified src/topology/metric_space/basic.lean
- \+ *lemma* pseudo_metric_space.ext
- \+ *lemma* _root_.dense.exists_dist_lt
- \+ *lemma* _root_.dense_range.exists_dist_lt
- \+ *lemma* pseudo_metric_space.replace_uniformity_eq
- \+ *lemma* cauchy_seq_of_le_tendsto_0'
- \+ *lemma* _root_.is_complete.nonempty_Inter_of_nonempty_bInter
- \+ *lemma* nonempty_Inter_of_nonempty_bInter
- \+ *lemma* metric_space.ext
- \+ *lemma* metric_space.replace_uniformity_eq
- \+ *lemma* metric_space.replace_topology_eq
- \+ *def* metric_space.replace_topology
- \+/\- *def* uniform_embedding.comap_metric_space
- \+ *def* embedding.comap_metric_space
- \+/\- *def* uniform_embedding.comap_metric_space

modified src/topology/uniform_space/basic.lean



## [2022-02-16 22:44:22](https://github.com/leanprover-community/mathlib/commit/5db1ae4)
feat(analysis/specific_limits): useful specializations of some lemmas ([#12069](https://github.com/leanprover-community/mathlib/pull/12069))
#### Estimated changes
modified src/algebra/group_power/order.lean
- \+ *lemma* pow_le_pow_iff

modified src/analysis/normed/group/basic.lean
- \+ *lemma* le_mul_norm_sub

modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_pow_const_mul_const_pow_of_lt_one
- \+ *lemma* tendsto_self_mul_const_pow_of_abs_lt_one
- \+ *lemma* tendsto_self_mul_const_pow_of_lt_one
- \+ *lemma* summable_geometric_two_encode



## [2022-02-16 22:44:21](https://github.com/leanprover-community/mathlib/commit/1bf4181)
feat(data/equiv/{basic,mul_equiv)}: add Pi_subsingleton ([#12040](https://github.com/leanprover-community/mathlib/pull/12040))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+ *def* Pi_subsingleton

modified src/data/equiv/mul_add.lean
- \+ *def* Pi_subsingleton



## [2022-02-16 22:44:20](https://github.com/leanprover-community/mathlib/commit/b2aaece)
feat(field_theory/is_alg_closed): alg closed and char p implies perfect ([#12037](https://github.com/leanprover-community/mathlib/pull/12037))
#### Estimated changes
modified src/field_theory/is_alg_closed/basic.lean

modified src/field_theory/perfect_closure.lean



## [2022-02-16 21:09:23](https://github.com/leanprover-community/mathlib/commit/bd67e85)
feat(algebra/char_p/basic): add ring_char_of_prime_eq_zero ([#12024](https://github.com/leanprover-community/mathlib/pull/12024))
The characteristic of a ring is `p` if `p` is a prime and `p = 0` in the ring.
#### Estimated changes
modified src/algebra/char_p/basic.lean
- \+ *lemma* ring_char_of_prime_eq_zero



## [2022-02-16 21:09:22](https://github.com/leanprover-community/mathlib/commit/0fe91d0)
feat(data/part): Instance lemmas ([#12001](https://github.com/leanprover-community/mathlib/pull/12001))
Lemmas about `part` instances, proved by `tidy`
#### Estimated changes
modified src/data/part.lean
- \+ *lemma* one_mem_one
- \+ *lemma* mul_mem_mul
- \+ *lemma* some_mul_some
- \+ *lemma* inv_mem_inv
- \+ *lemma* inv_some
- \+ *lemma* div_mem_div
- \+ *lemma* some_div_some
- \+ *lemma* mod_mem_mod
- \+ *lemma* some_mod_some
- \+ *lemma* append_mem_append
- \+ *lemma* some_append_some
- \+ *lemma* inter_mem_inter
- \+ *lemma* some_inter_some
- \+ *lemma* union_mem_union
- \+ *lemma* some_union_some
- \+ *lemma* sdiff_mem_sdiff
- \+ *lemma* some_sdiff_some



## [2022-02-16 19:16:09](https://github.com/leanprover-community/mathlib/commit/b395a67)
chore(data/finsupp/pointwise): golf using injective lemmas ([#12086](https://github.com/leanprover-community/mathlib/pull/12086))
#### Estimated changes
modified src/data/finsupp/pointwise.lean
- \+ *lemma* coe_mul
- \+ *lemma* coe_pointwise_smul
- \- *lemma* coe_pointwise_module



## [2022-02-16 19:16:08](https://github.com/leanprover-community/mathlib/commit/0ab9b5f)
chore(topology/continuous_function/bounded): golf algebra instances ([#12082](https://github.com/leanprover-community/mathlib/pull/12082))
Using the `function.injective.*` lemmas saves a lot of proofs.
This also adds a few missing lemmas about `one` that were already present for `zero`.
#### Estimated changes
modified src/topology/continuous_function/bounded.lean
- \+ *lemma* coe_one
- \+ *lemma* forall_coe_one_iff_one
- \+ *lemma* one_comp_continuous
- \- *lemma* coe_zero
- \- *lemma* forall_coe_zero_iff_zero
- \- *lemma* zero_comp_continuous



## [2022-02-16 19:16:06](https://github.com/leanprover-community/mathlib/commit/d86ce02)
chore(ring_theory/fractional_ideal): golf ([#12076](https://github.com/leanprover-community/mathlib/pull/12076))
#### Estimated changes
modified src/ring_theory/fractional_ideal.lean
- \+ *lemma* coe_inf
- \+ *lemma* coe_sup



## [2022-02-16 19:16:04](https://github.com/leanprover-community/mathlib/commit/15c6eee)
feat(logic/basic): Better congruence lemmas for `or`, `or_or_or_comm` ([#12004](https://github.com/leanprover-community/mathlib/pull/12004))
Prove `or_congr_left` and `or_congr_right` and rename the existing `or_congr_left`/`or_congr_right` to `or_congr_left'`/`or_congr_right'` to match the `and` lemmas. Also prove `or_rotate`, `or.rotate`, `or_or_or_comm` based on `and` again.
#### Estimated changes
modified src/data/fin/basic.lean

modified src/data/set/basic.lean

modified src/logic/basic.lean
- \+ *lemma* and_rotate
- \+/\- *lemma* and.rotate
- \+ *lemma* or_congr_left'
- \+ *lemma* or_congr_right'
- \+ *lemma* or_or_or_comm
- \+ *lemma* or_rotate
- \+ *lemma* or.rotate
- \+ *lemma* or_congr_left
- \+ *lemma* or_congr_right
- \+ *lemma* forall₂_imp
- \+ *lemma* Exists₂.imp
- \+/\- *lemma* and.rotate
- \- *theorem* or_congr_left
- \- *theorem* or_congr_right



## [2022-02-16 19:16:03](https://github.com/leanprover-community/mathlib/commit/5e3d465)
feat(category_theory/category/PartialFun): The category of types with partial functions ([#11866](https://github.com/leanprover-community/mathlib/pull/11866))
Define `PartialFun`, the category of types with partial functions, and show its equivalence with `Pointed`.
#### Estimated changes
created src/category_theory/category/PartialFun.lean
- \+ *def* PartialFun
- \+ *def* of
- \+ *def* iso.mk
- \+ *def* Type_to_PartialFun
- \+ *def* Pointed_to_PartialFun

modified src/category_theory/category/Pointed.lean
- \+ *def* iso.mk

modified src/data/subtype.lean
- \+ *lemma* coe_injective
- \+ *lemma* val_injective
- \+ *lemma* coe_inj
- \+ *lemma* val_inj
- \+/\- *lemma* _root_.exists_eq_subtype_mk_iff
- \+/\- *lemma* _root_.exists_subtype_mk_eq_iff
- \+/\- *lemma* _root_.exists_subtype_mk_eq_iff
- \+/\- *lemma* _root_.exists_eq_subtype_mk_iff
- \- *theorem* coe_injective
- \- *theorem* val_injective



## [2022-02-16 17:16:29](https://github.com/leanprover-community/mathlib/commit/3c78d00)
docs(group_theory/semidirect_product): fix typo in module docs ([#12083](https://github.com/leanprover-community/mathlib/pull/12083))
#### Estimated changes
modified src/group_theory/semidirect_product.lean



## [2022-02-16 17:16:27](https://github.com/leanprover-community/mathlib/commit/3107a83)
feat(algebra/char_p/basic): Generalize `frobenius_inj`. ([#12079](https://github.com/leanprover-community/mathlib/pull/12079))
#### Estimated changes
modified src/algebra/char_p/basic.lean
- \+/\- *theorem* frobenius_inj
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
modified src/combinatorics/derangements/finite.lean

modified src/combinatorics/set_family/shadow.lean

modified src/combinatorics/simple_graph/basic.lean

modified src/combinatorics/simple_graph/degree_sum.lean

modified src/data/finset/basic.lean
- \+ *lemma* subset_cons
- \+ *lemma* ssubset_cons
- \+ *lemma* cons_subset
- \+ *lemma* ssubset_iff_exists_cons_subset
- \+ *lemma* eq_of_not_mem_of_mem_insert
- \+ *lemma* insert_inj
- \+ *lemma* insert_inj_on
- \+ *lemma* sdiff_nonempty
- \+ *lemma* _root_.disjoint.forall_ne_finset
- \+ *lemma* _root_.disjoint.of_image_finset
- \+ *lemma* disjoint_image
- \+ *lemma* disjoint_map

modified src/data/finset/card.lean
- \+/\- *lemma* card_erase_of_mem
- \+/\- *lemma* card_erase_eq_ite
- \+ *lemma* exists_eq_insert_iff
- \+/\- *lemma* card_eq_succ
- \+/\- *lemma* card_erase_of_mem
- \+/\- *lemma* card_erase_eq_ite
- \+/\- *lemma* card_eq_succ

modified src/data/finset/powerset.lean

modified src/data/multiset/basic.lean
- \+ *lemma* subset_cons
- \+ *lemma* ssubset_cons
- \+ *lemma* cons_subset_cons

modified src/data/nat/totient.lean

modified src/data/polynomial/erase_lead.lean

modified src/data/set/basic.lean
- \+ *lemma* mem_of_mem_insert_of_ne
- \+ *lemma* eq_of_not_mem_of_mem_insert
- \+ *lemma* insert_inj
- \- *theorem* mem_of_mem_insert_of_ne

modified src/data/set/finite.lean

modified src/data/set/function.lean
- \+ *lemma* insert_inj_on

modified src/linear_algebra/affine_space/finite_dimensional.lean

modified src/linear_algebra/lagrange.lean

modified src/logic/basic.lean
- \+ *lemma* ne_of_mem_of_not_mem
- \+ *lemma* ne_of_mem_of_not_mem'
- \+ *lemma* has_mem.mem.ne_of_not_mem
- \+ *lemma* has_mem.mem.ne_of_not_mem'
- \- *theorem* ne_of_mem_of_not_mem



## [2022-02-16 17:16:25](https://github.com/leanprover-community/mathlib/commit/6bcb12c)
feat(order/antisymmetrization): Turning a preorder into a partial order ([#11728](https://github.com/leanprover-community/mathlib/pull/11728))
Define `antisymmetrization`, the quotient of a preorder by the "less than both ways" relation. This effectively turns a preorder into a partial order, and this operation is functorial as shown by the new `Preorder_to_PartialOrder`.
#### Estimated changes
modified src/data/quot.lean

created src/order/antisymmetrization.lean
- \+ *lemma* antisymm_rel_swap
- \+ *lemma* antisymm_rel_refl
- \+ *lemma* antisymm_rel.symm
- \+ *lemma* antisymm_rel.trans
- \+ *lemma* antisymm_rel_iff_eq
- \+ *lemma* to_antisymmetrization_of_antisymmetrization
- \+ *lemma* antisymm_rel.image
- \+ *lemma* to_antisymmetrization_le_to_antisymmetrization_iff
- \+ *lemma* to_antisymmetrization_lt_to_antisymmetrization_iff
- \+ *lemma* of_antisymmetrization_le_of_antisymmetrization_iff
- \+ *lemma* of_antisymmetrization_lt_of_antisymmetrization_iff
- \+ *lemma* to_antisymmetrization_mono
- \+ *lemma* order_hom.coe_antisymmetrization
- \+ *lemma* order_hom.antisymmetrization_apply
- \+ *lemma* order_hom.antisymmetrization_apply_mk
- \+ *lemma* order_iso.dual_antisymmetrization_apply
- \+ *lemma* order_iso.dual_antisymmetrization_symm_apply
- \+ *def* antisymm_rel
- \+ *def* antisymm_rel.setoid
- \+ *def* antisymmetrization
- \+ *def* to_antisymmetrization
- \+ *def* order_hom.to_antisymmetrization
- \+ *def* order_iso.dual_antisymmetrization

modified src/order/category/PartialOrder.lean
- \+ *def* Preorder_to_PartialOrder
- \+ *def* Preorder_to_PartialOrder_forget_adjunction
- \+ *def* Preorder_to_PartialOrder_comp_to_dual_iso_to_dual_comp_Preorder_to_PartialOrder

modified src/order/rel_classes.lean
- \+/\- *lemma* antisymm'
- \+ *lemma* antisymm_iff
- \+/\- *lemma* antisymm'



## [2022-02-16 16:11:48](https://github.com/leanprover-community/mathlib/commit/8a286af)
chore(topology/algebra/mul_action): rename type variables ([#12020](https://github.com/leanprover-community/mathlib/pull/12020))
#### Estimated changes
modified src/topology/algebra/mul_action.lean
- \+/\- *lemma* filter.tendsto.smul
- \+/\- *lemma* filter.tendsto.smul_const
- \+/\- *lemma* has_continuous_smul_Inf
- \+/\- *lemma* has_continuous_smul_infi
- \+/\- *lemma* has_continuous_smul_inf
- \+/\- *lemma* filter.tendsto.smul
- \+/\- *lemma* filter.tendsto.smul_const
- \+/\- *lemma* has_continuous_smul_Inf
- \+/\- *lemma* has_continuous_smul_infi
- \+/\- *lemma* has_continuous_smul_inf



## [2022-02-16 14:23:54](https://github.com/leanprover-community/mathlib/commit/e815675)
chore(topology/algebra/module/basic): remove two duplicate lemmas ([#12072](https://github.com/leanprover-community/mathlib/pull/12072))
`continuous_linear_map.continuous_nsmul` is nothing to do with `continuous_linear_map`s, and is the same as `continuous_nsmul`, but the latter doesn't require commutativity. There is no reason to keep the former.
This lemma was added in [#7084](https://github.com/leanprover-community/mathlib/pull/7084), but probably got missed due to how large that PR had to be.
We can't remove `continuous_linear_map.continuous_zsmul` until [#12055](https://github.com/leanprover-community/mathlib/pull/12055) is merged, as there is currently no `continuous_zsmul` in the root namespace.
#### Estimated changes
modified src/topology/algebra/module/basic.lean
- \- *lemma* continuous_nsmul
- \- *lemma* continuous.nsmul



## [2022-02-16 14:23:53](https://github.com/leanprover-community/mathlib/commit/a26d17f)
feat(mv_polynomial/supported): restrict_to_vars ([#12043](https://github.com/leanprover-community/mathlib/pull/12043))
#### Estimated changes
modified src/data/mv_polynomial/supported.lean
- \+ *lemma* exists_restrict_to_vars



## [2022-02-16 14:23:52](https://github.com/leanprover-community/mathlib/commit/62297cf)
feat(analysis/complex/cauchy_integral, analysis/analytic/basic): entire functions have power series with infinite radius of convergence ([#11948](https://github.com/leanprover-community/mathlib/pull/11948))
This proves that a formal multilinear series `p` which represents a function `f : 𝕜 → E` on a ball of every positive radius, then `p` represents `f` on a ball of infinite radius. Consequently, it is shown that if `f : ℂ → E` is differentiable everywhere, then `cauchy_power_series f z R` represents `f` as a power series centered at `z` in the entirety of `ℂ`, regardless of `R` (assuming `0 < R`).
- [x] depends on: [#11896](https://github.com/leanprover-community/mathlib/pull/11896)
#### Estimated changes
modified src/analysis/analytic/basic.lean
- \+ *theorem* has_fpower_series_on_ball.r_eq_top_of_exists

modified src/analysis/complex/cauchy_integral.lean



## [2022-02-16 13:36:23](https://github.com/leanprover-community/mathlib/commit/22fdf47)
chore(linear_algebra/affine_space/affine_map,topology/algebra/continuous_affine_map): generalized scalar instances ([#11978](https://github.com/leanprover-community/mathlib/pull/11978))
The main result here is that `distrib_mul_action`s are available on affine maps to a module, inherited from their codomain.
This fixes a diamond in the `int`-action that was already present for `int`-affine maps, and prevents the new `nat`-action introducing a diamond.
This also removes the requirement for `R` to be a `topological_space` in the scalar action for `continuous_affine_map` by using `has_continuous_const_smul` instead of `has_continuous_smul`.
#### Estimated changes
modified src/linear_algebra/affine_space/affine_map.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_linear
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_linear
- \+/\- *def* to_const_prod_linear_map
- \+/\- *def* to_const_prod_linear_map

modified src/topology/algebra/continuous_affine_map.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_smul
- \+/\- *lemma* smul_apply



## [2022-02-16 11:53:41](https://github.com/leanprover-community/mathlib/commit/32beebb)
feat(algebra/order/monoid): add simp lemmas ([#12030](https://github.com/leanprover-community/mathlib/pull/12030))
#### Estimated changes
modified src/algebra/order/monoid.lean
- \+ *lemma* of_mul_le
- \+ *lemma* of_mul_lt
- \+ *lemma* to_mul_le
- \+ *lemma* to_mul_lt
- \+ *lemma* of_add_le
- \+ *lemma* of_add_lt
- \+ *lemma* to_add_le
- \+ *lemma* to_add_lt



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
modified src/algebra/group/basic.lean
- \+/\- *lemma* inv_involutive
- \+/\- *lemma* inv_surjective
- \+/\- *lemma* inv_injective
- \+/\- *lemma* eq_inv_of_eq_inv
- \+/\- *lemma* inv_involutive
- \+/\- *lemma* inv_surjective
- \+/\- *lemma* inv_injective
- \+/\- *lemma* eq_inv_of_eq_inv
- \+/\- *theorem* inv_inj
- \+/\- *theorem* eq_inv_iff_eq_inv
- \+/\- *theorem* inv_eq_iff_inv_eq
- \+/\- *theorem* inv_inj
- \+/\- *theorem* eq_inv_iff_eq_inv
- \+/\- *theorem* inv_eq_iff_inv_eq

modified src/algebra/group/defs.lean
- \+/\- *lemma* inv_inv
- \+/\- *lemma* inv_inv

modified src/algebra/group_power/basic.lean
- \+/\- *lemma* neg_one_pow_mul_eq_zero_iff
- \+/\- *lemma* mul_neg_one_pow_eq_zero_iff
- \+/\- *lemma* neg_one_pow_mul_eq_zero_iff
- \+/\- *lemma* mul_neg_one_pow_eq_zero_iff
- \- *lemma* neg_sq
- \- *theorem* neg_one_pow_eq_or
- \- *theorem* neg_pow
- \- *theorem* neg_pow_bit0
- \- *theorem* neg_pow_bit1

modified src/algebra/group_with_zero/basic.lean
- \- *lemma* inv_inv₀
- \- *lemma* inv_involutive₀
- \- *lemma* inv_injective₀
- \- *lemma* inv_inj₀
- \- *lemma* inv_eq_iff
- \- *lemma* eq_inv_iff

modified src/algebra/group_with_zero/power.lean

modified src/algebra/order/field.lean

modified src/algebra/order/with_zero.lean

modified src/algebra/periodic.lean

modified src/algebra/pointwise.lean
- \+/\- *lemma* nonempty_inv
- \+/\- *lemma* nonempty.inv
- \+/\- *lemma* inv_mem_inv
- \+/\- *lemma* image_inv
- \+/\- *lemma* inv_subset_inv
- \+/\- *lemma* inv_subset
- \+/\- *lemma* finite.inv
- \+/\- *lemma* inv_singleton
- \+/\- *lemma* nonempty_inv
- \+/\- *lemma* nonempty.inv
- \+/\- *lemma* inv_mem_inv
- \+/\- *lemma* image_inv
- \+/\- *lemma* inv_subset_inv
- \+/\- *lemma* inv_subset
- \+/\- *lemma* finite.inv
- \+/\- *lemma* inv_singleton

modified src/algebra/quandle.lean

modified src/algebra/ring/basic.lean
- \+/\- *lemma* neg_mul
- \+/\- *lemma* mul_neg
- \+/\- *lemma* neg_mul_neg
- \+/\- *lemma* neg_mul_eq_neg_mul
- \+/\- *lemma* neg_mul_eq_mul_neg
- \+/\- *lemma* neg_mul_comm
- \+/\- *lemma* mul_neg_one
- \+/\- *lemma* neg_one_mul
- \+ *lemma* inv_neg'
- \+/\- *lemma* neg_mul_eq_neg_mul
- \+/\- *lemma* neg_mul_eq_mul_neg
- \+/\- *lemma* neg_mul
- \+/\- *lemma* mul_neg
- \+/\- *lemma* neg_mul_neg
- \+/\- *lemma* neg_mul_comm
- \+/\- *lemma* mul_neg_one
- \+/\- *lemma* neg_one_mul
- \+/\- *lemma* neg_mul_eq_neg_mul
- \+/\- *lemma* neg_mul_eq_mul_neg
- \+/\- *lemma* mul_neg_one
- \+/\- *lemma* neg_one_mul
- \- *lemma* units_neg_right
- \- *lemma* units_neg_right_iff
- \- *lemma* units_neg_left
- \- *lemma* units_neg_left_iff
- \- *lemma* units_neg_one_right
- \- *lemma* units_neg_one_left
- \+/\- *theorem* neg_eq_neg_one_mul
- \+/\- *theorem* sub_right
- \+/\- *theorem* sub_left
- \+/\- *theorem* neg_eq_neg_one_mul
- \+/\- *theorem* sub_right
- \+/\- *theorem* sub_left
- \- *theorem* units_neg_right
- \- *theorem* units_neg_right_iff
- \- *theorem* units_neg_left
- \- *theorem* units_neg_left_iff
- \- *theorem* units_neg_one_right
- \- *theorem* units_neg_one_left

modified src/algebra/star/unitary.lean
- \+ *lemma* coe_neg

modified src/analysis/asymptotics/asymptotics.lean

modified src/analysis/asymptotics/superpolynomial_decay.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/lhopital.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/operator_norm.lean

modified src/analysis/normed_space/units.lean

modified src/analysis/seminorm.lean

modified src/analysis/special_functions/log_deriv.lean

modified src/analysis/specific_limits.lean

modified src/data/equiv/mul_add.lean
- \+/\- *lemma* inv_symm
- \+/\- *lemma* inv_symm
- \- *lemma* inv_symm₀

modified src/data/real/conjugate_exponents.lean

modified src/data/real/ennreal.lean
- \- *lemma* inv_inv
- \- *lemma* inv_involutive
- \- *lemma* inv_bijective
- \- *lemma* inv_eq_inv

modified src/data/real/ereal.lean
- \- *theorem* neg_inj
- \- *theorem* neg_eq_neg_iff
- \- *theorem* neg_eq_iff_neg_eq

modified src/data/real/golden_ratio.lean

modified src/data/real/hyperreal.lean
- \+/\- *lemma* inv_epsilon_eq_omega
- \+/\- *lemma* inv_epsilon_eq_omega

modified src/data/real/irrational.lean

modified src/data/real/nnreal.lean

modified src/data/set/intervals/image_preimage.lean

modified src/data/set/intervals/unordered_interval.lean

modified src/field_theory/finite/basic.lean

modified src/field_theory/ratfunc.lean

modified src/group_theory/perm/cycles.lean

modified src/group_theory/perm/sign.lean

modified src/group_theory/subgroup/basic.lean

modified src/group_theory/submonoid/pointwise.lean

modified src/linear_algebra/affine_space/ordered.lean

modified src/linear_algebra/alternating.lean

modified src/linear_algebra/general_linear_group.lean

modified src/linear_algebra/orientation.lean
- \- *lemma* neg_involutive

modified src/linear_algebra/special_linear_group.lean

modified src/measure_theory/decomposition/jordan.lean

modified src/measure_theory/group/arithmetic.lean

modified src/measure_theory/group/measurable_equiv.lean
- \+/\- *lemma* symm_inv
- \+/\- *lemma* symm_inv
- \- *lemma* symm_inv₀
- \+/\- *def* inv
- \+/\- *def* inv
- \- *def* inv₀

modified src/measure_theory/group/prod.lean

modified src/measure_theory/integral/interval_integral.lean

modified src/measure_theory/integral/mean_inequalities.lean

modified src/measure_theory/measure/haar_lebesgue.lean

modified src/number_theory/l_series.lean

modified src/number_theory/padics/padic_integers.lean

modified src/number_theory/padics/padic_numbers.lean

modified src/ring_theory/algebraic.lean

modified src/ring_theory/roots_of_unity.lean

modified src/tactic/norm_num.lean

modified src/topology/instances/ennreal.lean



## [2022-02-16 11:53:38](https://github.com/leanprover-community/mathlib/commit/d24792c)
feat(model_theory/terms_and_formulas): Define satisfiability and semantic equivalence of formulas ([#11928](https://github.com/leanprover-community/mathlib/pull/11928))
Defines satisfiability of theories
Provides a default model of a satisfiable theory
Defines semantic (logical) equivalence of formulas
#### Estimated changes
modified src/model_theory/basic.lean
- \+ *lemma* nonempty_of_nonempty_constants
- \- *def* empty

modified src/model_theory/definability.lean

modified src/model_theory/terms_and_formulas.lean
- \+ *lemma* realize_inf
- \+ *lemma* realize_imp
- \+ *lemma* Theory.model.mono
- \+ *lemma* is_satisfiable.some_model_models
- \+ *lemma* model.is_satisfiable
- \+ *lemma* is_satisfiable.mono
- \+ *lemma* is_satisfiable.is_finitely_satisfiable
- \+ *lemma* models_formula_iff
- \+ *lemma* models_sentence_iff
- \+ *lemma* semantically_equivalent.realize_eq
- \+ *lemma* semantically_equivalent.some_model_realize_eq
- \+ *lemma* semantically_equivalent_not_not
- \+ *lemma* imp_semantically_equivalent_not_sup
- \+ *lemma* sup_semantically_equivalent_not_inf_not
- \+ *lemma* inf_semantically_equivalent_not_sup_not
- \+ *def* Theory
- \+/\- *def* bd_not
- \+ *def* Theory.model
- \+ *def* is_satisfiable
- \+ *def* is_finitely_satisfiable
- \+ *def* is_satisfiable.some_model
- \+ *def* models_bounded_formula
- \+ *def* semantically_equivalent
- \+ *def* semantically_equivalent_setoid
- \- *def* theory
- \+/\- *def* bd_not



## [2022-02-16 11:19:27](https://github.com/leanprover-community/mathlib/commit/6dfb24c)
feat(algebra/star/self_adjoint): define skew-adjoint elements of a star additive group ([#12013](https://github.com/leanprover-community/mathlib/pull/12013))
This defines the skew-adjoint elements of a star additive group, as the additive subgroup that satisfies `star x = -x`. The development is analogous to that of `self_adjoint`.
#### Estimated changes
modified src/algebra/star/self_adjoint.lean
- \+/\- *lemma* bit0_mem
- \+ *lemma* mem_iff
- \+ *lemma* star_coe_eq
- \+/\- *lemma* bit0_mem
- \+ *lemma* conjugate
- \+ *lemma* conjugate'
- \+ *lemma* coe_smul
- \+/\- *lemma* bit0_mem
- \+ *def* skew_adjoint



## [2022-02-16 09:30:11](https://github.com/leanprover-community/mathlib/commit/06e6b35)
feat(analysis/special_functions/trigonometric/angle): `coe_pi_add_coe_pi` ([#12064](https://github.com/leanprover-community/mathlib/pull/12064))
Add another `simp` lemma to those expressing in different ways that 2π
is zero as a `real.angle`.
#### Estimated changes
modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* coe_pi_add_coe_pi



## [2022-02-16 07:45:37](https://github.com/leanprover-community/mathlib/commit/daf2989)
feat(algebra/big_operators): formula for product of sums to n+1 ([#12042](https://github.com/leanprover-community/mathlib/pull/12042))
#### Estimated changes
modified src/algebra/big_operators/ring.lean
- \+ *lemma* sum_range_succ_mul_sum_range_succ



## [2022-02-16 07:16:02](https://github.com/leanprover-community/mathlib/commit/6a09cd0)
chore(topology/uniform_space): use weaker TC assumptions ([#12066](https://github.com/leanprover-community/mathlib/pull/12066))
We don't need `[uniform_space β]` to prove
`uniform_space.completion.ext`.
#### Estimated changes
modified src/topology/uniform_space/abstract_completion.lean

modified src/topology/uniform_space/completion.lean
- \+/\- *lemma* ext
- \+/\- *lemma* ext



## [2022-02-15 20:57:33](https://github.com/leanprover-community/mathlib/commit/eeb2956)
feat(topology/algebra): relax some `Type*` assumptions to `Sort*` ([#12058](https://github.com/leanprover-community/mathlib/pull/12058))
When working on [#11720](https://github.com/leanprover-community/mathlib/pull/11720) I forgot that we have to deal with Prop-indexed infimums quite often, so this PR fixes that.
#### Estimated changes
modified src/topology/algebra/group.lean

modified src/topology/algebra/monoid.lean

modified src/topology/algebra/mul_action.lean



## [2022-02-15 19:34:16](https://github.com/leanprover-community/mathlib/commit/b0fe972)
feat (analysis/normed_space/spectrum): prove Gelfand's formula for the spectral radius ([#11916](https://github.com/leanprover-community/mathlib/pull/11916))
This establishes Gelfand's formula for the spectral radius in a complex Banach algebra `A`, namely that the sequence of n-th roots of the norms of n-th powers of any element tends to its spectral radius. Some results which hold in more generality concerning the function `z ↦ ring.inverse (1 - z • a)` are also given. In particular, this function is differentiable on the disk with radius the reciprocal of the spectral radius, and it has a power series on the ball with radius equal to the reciprocal of the norm of `a : A`.
Currently, the version of Gelfand's formula which appears here includes an assumption that `A` is second countable, which won't hold in general unless `A` is separable. This is not a true (i.e., mathematical) limitation, but a consequence of the current implementation of Bochner integrals in mathlib (which are an essential feature in the proof of Gelfand's formula because of its use of the Cauchy integral formula). When Bochner integrals are refactored, this type class assumption can be dropped.
- [x] depends on: [#11869](https://github.com/leanprover-community/mathlib/pull/11869)
- [x] depends on: [#11896](https://github.com/leanprover-community/mathlib/pull/11896) 
- [x] depends on: [#11915](https://github.com/leanprover-community/mathlib/pull/11915)
#### Estimated changes
modified src/analysis/normed_space/spectrum.lean
- \+ *lemma* mem_resolvent_set_of_spectral_radius_lt
- \+ *lemma* has_fpower_series_on_ball_inverse_one_sub_smul
- \+ *lemma* is_unit_one_sub_smul_of_lt_inv_radius
- \+ *lemma* limsup_pow_nnnorm_pow_one_div_le_spectral_radius
- \+ *theorem* differentiable_on_inverse_one_sub_smul
- \+ *theorem* pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius
- \+ *theorem* pow_norm_pow_one_div_tendsto_nhds_spectral_radius



## [2022-02-15 19:34:15](https://github.com/leanprover-community/mathlib/commit/d76ac2e)
feat(category_theory): separators and detectors ([#11880](https://github.com/leanprover-community/mathlib/pull/11880))
#### Estimated changes
modified src/category_theory/balanced.lean
- \+ *lemma* balanced_opposite

created src/category_theory/generator.lean
- \+ *lemma* is_separating_op_iff
- \+ *lemma* is_coseparating_op_iff
- \+ *lemma* is_coseparating_unop_iff
- \+ *lemma* is_separating_unop_iff
- \+ *lemma* is_detecting_op_iff
- \+ *lemma* is_codetecting_op_iff
- \+ *lemma* is_detecting_unop_iff
- \+ *lemma* is_codetecting_unop_iff
- \+ *lemma* is_detecting.is_separating
- \+ *lemma* is_codetecting.is_coseparating
- \+ *lemma* is_separating.is_detecting
- \+ *lemma* is_coseparating.is_codetecting
- \+ *lemma* is_detecting_iff_is_separating
- \+ *lemma* is_codetecting_iff_is_coseparating
- \+ *lemma* is_separating.mono
- \+ *lemma* is_coseparating.mono
- \+ *lemma* is_detecting.mono
- \+ *lemma* is_codetecting.mono
- \+ *lemma* thin_of_is_separating_empty
- \+ *lemma* is_separating_empty_of_thin
- \+ *lemma* thin_of_is_coseparating_empty
- \+ *lemma* is_coseparating_empty_of_thin
- \+ *lemma* groupoid_of_is_detecting_empty
- \+ *lemma* is_detecting_empty_of_groupoid
- \+ *lemma* groupoid_of_is_codetecting_empty
- \+ *lemma* is_codetecting_empty_of_groupoid
- \+ *lemma* is_separator_op_iff
- \+ *lemma* is_coseparator_op_iff
- \+ *lemma* is_coseparator_unop_iff
- \+ *lemma* is_separator_unop_iff
- \+ *lemma* is_detector_op_iff
- \+ *lemma* is_codetector_op_iff
- \+ *lemma* is_codetector_unop_iff
- \+ *lemma* is_detector_unop_iff
- \+ *lemma* is_detector.is_separator
- \+ *lemma* is_codetector.is_coseparator
- \+ *lemma* is_separator.is_detector
- \+ *lemma* is_cospearator.is_codetector
- \+ *lemma* is_separator_def
- \+ *lemma* is_separator.def
- \+ *lemma* is_coseparator_def
- \+ *lemma* is_coseparator.def
- \+ *lemma* is_detector_def
- \+ *lemma* is_detector.def
- \+ *lemma* is_codetector_def
- \+ *lemma* is_codetector.def
- \+ *lemma* is_separator_iff_faithful_coyoneda_obj
- \+ *lemma* is_coseparator_iff_faithful_yoneda_obj
- \+ *lemma* is_detector_iff_reflects_isomorphisms_coyoneda_obj
- \+ *lemma* is_codetector_iff_reflects_isomorphisms_yoneda_obj
- \+ *def* is_separating
- \+ *def* is_coseparating
- \+ *def* is_detecting
- \+ *def* is_codetecting
- \+ *def* is_separator
- \+ *def* is_coseparator
- \+ *def* is_detector
- \+ *def* is_codetector

modified src/category_theory/limits/shapes/equalizers.lean

modified src/category_theory/opposites.lean
- \+ *lemma* is_iso_op_iff
- \+ *lemma* is_iso_unop_iff
- \+/\- *lemma* op_inv
- \+ *lemma* unop_inv
- \+/\- *lemma* op_inv



## [2022-02-15 19:04:10](https://github.com/leanprover-community/mathlib/commit/ff2c9dc)
feat(combinatorics/simple_graph/connectivity): add functions to split walks and to create paths ([#11095](https://github.com/leanprover-community/mathlib/pull/11095))
This is chunk 3 of [#8737](https://github.com/leanprover-community/mathlib/pull/8737). Introduces `take_until` and `drop_until` to split walks at a vertex, `rotate` to rotate cycles, and `to_path` to remove internal redundancy from a walk to create a path with the same endpoints.
This also defines a bundled `path` type for `is_path` since `G.path u v` is a useful type.
#### Estimated changes
modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* mem_support_nil_iff
- \+ *lemma* take_spec
- \+ *lemma* count_support_take_until_eq_one
- \+ *lemma* count_edges_take_until_le_one
- \+ *lemma* support_take_until_subset
- \+ *lemma* support_drop_until_subset
- \+ *lemma* edges_take_until_subset
- \+ *lemma* edges_drop_until_subset
- \+ *lemma* length_take_until_le
- \+ *lemma* length_drop_until_le
- \+ *lemma* is_trail.take_until
- \+ *lemma* is_trail.drop_until
- \+ *lemma* is_path.take_until
- \+ *lemma* is_path.drop_until
- \+ *lemma* support_rotate
- \+ *lemma* rotate_edges
- \+ *lemma* is_trail.rotate
- \+ *lemma* is_circuit.rotate
- \+ *lemma* is_cycle.rotate
- \+ *lemma* bypass_is_path
- \+ *lemma* length_bypass_le
- \+ *lemma* support_bypass_subset
- \+ *lemma* support_to_path_subset
- \+ *lemma* edges_bypass_subset
- \+ *lemma* edges_to_path_subset
- \+ *def* take_until
- \+ *def* drop_until
- \+ *def* rotate
- \+ *def* bypass
- \+ *def* to_path



## [2022-02-15 17:47:31](https://github.com/leanprover-community/mathlib/commit/5027b28)
move(data/nat/choose/bounds): Move from `combinatorics.choose.bounds` ([#12051](https://github.com/leanprover-community/mathlib/pull/12051))
This file fits better with all other files about `nat.choose`. My bad for originally proposing it goes alone under `combinatorics`.
#### Estimated changes
renamed src/combinatorics/choose/bounds.lean to src/data/nat/choose/bounds.lean



## [2022-02-15 17:47:30](https://github.com/leanprover-community/mathlib/commit/52aaf17)
feat(data/{list,multiset,finset}/nat_antidiagonal): add lemmas to remove elements from head and tail of antidiagonal ([#12028](https://github.com/leanprover-community/mathlib/pull/12028))
Also lowered `finset.nat.map_swap_antidiagonal` down to `list` through `multiset`.
#### Estimated changes
modified src/data/finset/nat_antidiagonal.lean
- \+ *lemma* antidiagonal_succ'
- \+ *lemma* antidiagonal_succ_succ'
- \+/\- *lemma* map_swap_antidiagonal
- \+/\- *lemma* map_swap_antidiagonal

modified src/data/list/nat_antidiagonal.lean
- \+ *lemma* antidiagonal_succ'
- \+ *lemma* antidiagonal_succ_succ'
- \+ *lemma* map_swap_antidiagonal

modified src/data/multiset/nat_antidiagonal.lean
- \+ *lemma* antidiagonal_succ'
- \+ *lemma* antidiagonal_succ_succ'
- \+ *lemma* map_swap_antidiagonal



## [2022-02-15 15:53:29](https://github.com/leanprover-community/mathlib/commit/c0c673a)
feat(data/equiv,logic/embedding): add `can_lift` instances ([#12049](https://github.com/leanprover-community/mathlib/pull/12049))
#### Estimated changes
modified src/data/equiv/basic.lean
- \+/\- *lemma* of_bijective_apply_symm_apply
- \+/\- *lemma* of_bijective_symm_apply_apply
- \+/\- *lemma* of_bijective_apply_symm_apply
- \+/\- *lemma* of_bijective_symm_apply_apply

modified src/logic/embedding.lean



## [2022-02-15 15:52:59](https://github.com/leanprover-community/mathlib/commit/c686fcc)
feat(analysis/specific_limits): add `tendsto_zero_smul_of_tendsto_zero_of_bounded` ([#12039](https://github.com/leanprover-community/mathlib/pull/12039))
#### Estimated changes
modified src/analysis/specific_limits.lean
- \+ *lemma* tendsto_zero_smul_of_tendsto_zero_of_bounded



## [2022-02-15 15:52:56](https://github.com/leanprover-community/mathlib/commit/6e64492)
feat(ring_theory/multiplicity): Equality of `factorization`, `multiplicity`, and `padic_val_nat` ([#12033](https://github.com/leanprover-community/mathlib/pull/12033))
Proves `multiplicity_eq_factorization : multiplicity p n = n.factorization p` for prime `p` and `n ≠ 0` and uses this to golf the proof of `padic_val_nat_eq_factorization : padic_val_nat p n = n.factorization p`.
#### Estimated changes
modified src/number_theory/padics/padic_norm.lean
- \+/\- *lemma* padic_val_nat_eq_factorization
- \+/\- *lemma* padic_val_nat_eq_factorization

modified src/ring_theory/multiplicity.lean
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
modified src/order/filter/basic.lean
- \+ *lemma* tendsto_prod_iff'

modified src/topology/constructions.lean
- \+ *lemma* _root_.prod.tendsto_iff

modified src/topology/order/lattice.lean
- \+ *lemma* filter.tendsto.sup_right_nhds'
- \+ *lemma* filter.tendsto.sup_right_nhds
- \+ *lemma* filter.tendsto.inf_right_nhds'
- \+ *lemma* filter.tendsto.inf_right_nhds



## [2022-02-15 15:52:52](https://github.com/leanprover-community/mathlib/commit/60b77a7)
feat(analysis/special_functions/complex/circle): `real.angle.exp_map_circle` lemmas ([#11969](https://github.com/leanprover-community/mathlib/pull/11969))
Add four more `simp` lemmas about `real.angle.exp_map_circle`:
`exp_map_circle_zero`, `exp_map_circle_neg`, `exp_map_circle_add` and
`arg_exp_map_circle`.
#### Estimated changes
modified src/analysis/special_functions/complex/circle.lean
- \+ *lemma* real.angle.exp_map_circle_zero
- \+ *lemma* real.angle.exp_map_circle_neg
- \+ *lemma* real.angle.exp_map_circle_add
- \+ *lemma* real.angle.arg_exp_map_circle



## [2022-02-15 15:52:49](https://github.com/leanprover-community/mathlib/commit/0c33309)
feat(number_theory/zsqrtd/basic): add some lemmas ([#11964](https://github.com/leanprover-community/mathlib/pull/11964))
#### Estimated changes
modified src/number_theory/zsqrtd/basic.lean
- \+/\- *lemma* coe_int_dvd_iff
- \+ *lemma* coe_int_dvd_coe_int
- \+ *lemma* gcd_eq_zero_iff
- \+ *lemma* gcd_pos_iff
- \+ *lemma* coprime_of_dvd_coprime
- \+ *lemma* exists_coprime_of_gcd_pos
- \+/\- *lemma* coe_int_dvd_iff
- \+ *theorem* smul_re
- \+ *theorem* smul_im



## [2022-02-15 15:52:48](https://github.com/leanprover-community/mathlib/commit/3d1354c)
feat(set_theory/ordinal_arithmetic): Suprema of functions with the same range are equal ([#11910](https://github.com/leanprover-community/mathlib/pull/11910))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* mem_brange
- \+ *theorem* mem_brange_self
- \+ *theorem* range_family_of_bfamily'
- \+ *theorem* range_family_of_bfamily
- \+ *theorem* brange_bfamily_of_family'
- \+ *theorem* brange_bfamily_of_family
- \+ *theorem* sup_le_of_range_subset
- \+ *theorem* sup_eq_of_range_eq
- \+/\- *theorem* sup_eq_sup
- \+ *theorem* bsup_le_of_brange_subset
- \+ *theorem* bsup_eq_of_brange_eq
- \+ *theorem* lsub_le_of_range_subset
- \+ *theorem* lsub_eq_of_range_eq
- \+ *theorem* blsub_le_of_brange_subset
- \+ *theorem* blsub_eq_of_brange_eq
- \+/\- *theorem* sup_eq_sup
- \+ *def* brange



## [2022-02-15 15:52:46](https://github.com/leanprover-community/mathlib/commit/721bace)
refactor(set_theory/ordinal_arithmetic): `omin` → `Inf` ([#11867](https://github.com/leanprover-community/mathlib/pull/11867))
We remove the redundant `omin` in favor of `Inf`. We also introduce a `conditionally_complete_linear_order_bot` instance on `cardinals`, and golf a particularly messy proof.
#### Estimated changes
modified src/set_theory/cardinal.lean
- \+ *def* out_mk_equiv
- \+ *def* min
- \+ *def* succ
- \+ *def* sup
- \+ *def* to_nat
- \+ *def* to_enat
- \+ *def* powerlt

modified src/set_theory/cardinal_ordinal.lean
- \+/\- *theorem* ord_aleph'_eq_enum_card
- \+/\- *theorem* ord_aleph_eq_enum_card
- \+/\- *theorem* ord_aleph'_eq_enum_card
- \+/\- *theorem* ord_aleph_eq_enum_card

modified src/set_theory/game/nim.lean

modified src/set_theory/ordinal.lean
- \- *lemma* Inf_eq_omin
- \- *lemma* Inf_mem
- \- *theorem* omin_mem
- \- *theorem* le_omin
- \- *theorem* omin_le
- \- *theorem* not_lt_omin
- \- *def* omin

modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *lemma* div_def
- \+ *lemma* enum_ord_def_nonempty
- \+/\- *lemma* div_def
- \- *lemma* enum_ord_def'_H
- \- *lemma* enum_ord_def_H
- \+ *theorem* sub_nonempty
- \+ *theorem* div_nonempty
- \+/\- *theorem* div_zero
- \+ *theorem* sup_nonempty
- \+ *theorem* enum_ord_def'_nonempty
- \+/\- *theorem* enum_ord_mem
- \+/\- *theorem* blsub_le_enum_ord
- \+/\- *theorem* enum_ord.strict_mono
- \+ *theorem* enum_ord_zero
- \+ *theorem* enum_ord_zero_le
- \+ *theorem* enum_ord_succ_le
- \+/\- *theorem* enum_ord.surjective
- \+/\- *theorem* enum_ord_range
- \+/\- *theorem* eq_enum_ord
- \+ *theorem* log_nonempty
- \+/\- *theorem* log_def
- \+/\- *theorem* succ_log_def
- \+/\- *theorem* deriv_eq_enum_fp
- \+/\- *theorem* div_zero
- \+/\- *theorem* enum_ord_mem
- \+/\- *theorem* blsub_le_enum_ord
- \+/\- *theorem* enum_ord.strict_mono
- \+/\- *theorem* enum_ord.surjective
- \+/\- *theorem* enum_ord_range
- \+/\- *theorem* eq_enum_ord
- \+/\- *theorem* log_def
- \+/\- *theorem* succ_log_def
- \+/\- *theorem* deriv_eq_enum_fp
- \+/\- *def* sup
- \+/\- *def* enum_ord
- \+/\- *def* enum_ord.order_iso
- \+/\- *def* sup
- \+/\- *def* enum_ord
- \+/\- *def* enum_ord.order_iso



## [2022-02-15 15:52:45](https://github.com/leanprover-community/mathlib/commit/9acc1d4)
feat(model_theory/finitely_generated): Finitely generated and countably generated (sub)structures ([#11857](https://github.com/leanprover-community/mathlib/pull/11857))
Defines `substructure.fg` and `Structure.fg` to indicate when (sub)structures are finitely generated
Defines `substructure.cg` and `Structure.cg` to indicate when (sub)structures are countably generated
#### Estimated changes
created src/model_theory/finitely_generated.lean
- \+ *lemma* fg_iff_exists_fin_generating_family
- \+ *lemma* cg_iff_empty_or_exists_nat_generating_family
- \+ *lemma* fg_def
- \+ *lemma* fg_iff
- \+ *lemma* fg.range
- \+ *lemma* fg.map_of_surjective
- \+ *lemma* cg_def
- \+ *lemma* cg_iff
- \+ *lemma* cg.range
- \+ *lemma* cg.map_of_surjective
- \+ *lemma* equiv.fg_iff
- \+ *lemma* substructure.fg_iff_Structure_fg
- \+ *lemma* equiv.cg_iff
- \+ *lemma* substructure.cg_iff_Structure_cg
- \+ *theorem* fg_def
- \+ *theorem* fg_bot
- \+ *theorem* fg_closure
- \+ *theorem* fg_closure_singleton
- \+ *theorem* fg_sup
- \+ *theorem* fg.map
- \+ *theorem* fg.of_map_embedding
- \+ *theorem* cg_def
- \+ *theorem* fg.cg
- \+ *theorem* cg_bot
- \+ *theorem* cg_closure
- \+ *theorem* cg_closure_singleton
- \+ *theorem* cg_sup
- \+ *theorem* cg.map
- \+ *theorem* cg.of_map_embedding
- \+ *def* fg
- \+ *def* cg



## [2022-02-15 15:52:44](https://github.com/leanprover-community/mathlib/commit/41dd6d8)
feat(data/nat/modeq): add modeq and dvd lemmas from Apostol Chapter 5 ([#11787](https://github.com/leanprover-community/mathlib/pull/11787))
Various lemmas about `modeq` from Chapter 5 of Apostol (1976) Introduction to Analytic Number Theory:
* `mul_left_iff` and `mul_right_iff`: Apostol, Theorem 5.3
* `dvd_iff_of_modeq_of_dvd`: Apostol, Theorem 5.5
* `gcd_eq_of_modeq`: Apostol, Theorem 5.6
* `eq_of_modeq_of_abs_lt`: Apostol, Theorem 5.7
* `modeq_cancel_left_div_gcd`: Apostol, Theorem 5.4; plus other cancellation lemmas following from this.
#### Estimated changes
modified src/data/int/basic.lean
- \+ *lemma* eq_zero_of_abs_lt_dvd

modified src/data/nat/modeq.lean
- \+ *lemma* dvd_iff_of_modeq_of_dvd
- \+ *lemma* gcd_eq_of_modeq
- \+ *lemma* eq_of_modeq_of_abs_lt
- \+ *lemma* modeq_cancel_left_div_gcd
- \+ *lemma* modeq_cancel_right_div_gcd
- \+ *lemma* modeq_cancel_left_div_gcd'
- \+ *lemma* modeq_cancel_right_div_gcd'
- \+ *lemma* modeq_cancel_left_of_coprime
- \+ *lemma* modeq_cancel_right_of_coprime



## [2022-02-15 14:39:56](https://github.com/leanprover-community/mathlib/commit/b0508f3)
feat(topology/uniform/uniform_embedding): a sum of two complete spaces is complete ([#11971](https://github.com/leanprover-community/mathlib/pull/11971))
#### Estimated changes
modified src/topology/uniform_space/basic.lean
- \+ *lemma* discrete_topology_of_discrete_uniformity
- \+/\- *def* uniform_space.replace_topology
- \+/\- *def* uniform_space.replace_topology

modified src/topology/uniform_space/uniform_embedding.lean
- \+ *lemma* embedding.to_uniform_embedding
- \+ *theorem* uniform_embedding_inl
- \+ *theorem* uniform_embedding_inr
- \+ *def* embedding.comap_uniform_space



## [2022-02-15 14:39:55](https://github.com/leanprover-community/mathlib/commit/77ca1ed)
feat(order/category/Lattice): The category of lattices ([#11968](https://github.com/leanprover-community/mathlib/pull/11968))
Define `Lattice`, the category of lattices with lattice homs.
#### Estimated changes
modified src/category_theory/concrete_category/bundled_hom.lean

created src/order/category/Lattice.lean
- \+ *lemma* Lattice_dual_comp_forget_to_PartialOrder
- \+ *def* Lattice
- \+ *def* of
- \+ *def* iso.mk
- \+ *def* dual
- \+ *def* dual_equiv

modified src/order/category/LinearOrder.lean
- \+ *lemma* LinearOrder_dual_comp_forget_to_Lattice
- \- *lemma* LinearOrder_dual_equiv_comp_forget_to_PartialOrder
- \+ *def* dual
- \- *def* to_dual

modified src/order/hom/lattice.lean



## [2022-02-15 12:59:13](https://github.com/leanprover-community/mathlib/commit/5bcffd9)
feat(number_theory/cyclotomic/zeta): add lemmas ([#11786](https://github.com/leanprover-community/mathlib/pull/11786))
Lemmas about the norm of `ζ - 1`.
From flt-regular.
- [x] depends on: [#11941](https://github.com/leanprover-community/mathlib/pull/11941)
#### Estimated changes
modified src/number_theory/cyclotomic/primitive_roots.lean
- \+/\- *lemma* sub_one_norm_eq_eval_cyclotomic
- \+ *lemma* sub_one_norm.is_prime_pow
- \+ *lemma* prime_ne_two_pow.sub_one_norm
- \+ *lemma* sub_one_norm.prime
- \+ *lemma* sub_one_norm.pow_two
- \+ *lemma* norm_zeta_eq_one
- \+ *lemma* is_prime_pow.norm_zeta_sub_one
- \+ *lemma* prime_ne_two_pow.norm_zeta_sub_one
- \+ *lemma* prime_ne_two.norm_zeta_sub_one
- \+ *lemma* two_pow.norm_zeta_sub_one
- \+/\- *lemma* sub_one_norm_eq_eval_cyclotomic



## [2022-02-15 12:59:12](https://github.com/leanprover-community/mathlib/commit/a2d7b55)
feat(order/complete_boolean_algebra): Frames ([#11709](https://github.com/leanprover-community/mathlib/pull/11709))
Define the order theoretic `order.frame` and `order.coframe` and insert them between `complete_lattice` and `complete_distrib_lattice`.
#### Estimated changes
modified docs/references.bib

modified src/data/set/prod.lean
- \+ *lemma* image_prod_mk_subset_prod_left
- \+ *lemma* image_prod_mk_subset_prod_right

modified src/order/complete_boolean_algebra.lean
- \+ *lemma* inf_Sup_eq
- \+ *lemma* Sup_inf_eq
- \+ *lemma* supr_inf_eq
- \+ *lemma* inf_supr_eq
- \+ *lemma* bsupr_inf_eq
- \+ *lemma* inf_bsupr_eq
- \+ *lemma* supr_inf_supr
- \+ *lemma* bsupr_inf_bsupr
- \+ *lemma* Sup_inf_Sup
- \+/\- *lemma* supr_disjoint_iff
- \+/\- *lemma* disjoint_supr_iff
- \+ *lemma* infi_sup_infi
- \+ *lemma* binfi_sup_binfi
- \+/\- *lemma* supr_disjoint_iff
- \+/\- *lemma* disjoint_supr_iff
- \+/\- *theorem* sup_Inf_eq
- \+/\- *theorem* Inf_sup_eq
- \+/\- *theorem* sup_Inf_eq
- \+/\- *theorem* Inf_sup_eq
- \- *theorem* inf_Sup_eq
- \- *theorem* Sup_inf_eq
- \- *theorem* supr_inf_eq
- \- *theorem* inf_supr_eq
- \- *theorem* bsupr_inf_eq
- \- *theorem* inf_bsupr_eq
- \- *theorem* Sup_inf_Sup

modified src/order/copy.lean
- \+ *def* frame.copy
- \+ *def* coframe.copy



## [2022-02-15 12:30:09](https://github.com/leanprover-community/mathlib/commit/440e6b3)
feat(topology/algebra/module/locally_convex): define locally convex spaces ([#11859](https://github.com/leanprover-community/mathlib/pull/11859))
#### Estimated changes
modified src/analysis/seminorm.lean
- \+ *lemma* with_seminorms.to_locally_convex_space
- \+ *lemma* normed_space.to_locally_convex_space'

created src/topology/algebra/module/locally_convex.lean
- \+ *lemma* locally_convex_space_iff
- \+ *lemma* locally_convex_space.of_bases
- \+ *lemma* locally_convex_space.convex_basis_zero
- \+ *lemma* locally_convex_space_iff_exists_convex_subset
- \+ *lemma* locally_convex_space.of_basis_zero
- \+ *lemma* locally_convex_space_iff_zero
- \+ *lemma* locally_convex_space_iff_exists_convex_subset_zero



## [2022-02-15 11:12:39](https://github.com/leanprover-community/mathlib/commit/c5578f9)
feat(group_theory/nilpotent): products of nilpotent groups ([#11827](https://github.com/leanprover-community/mathlib/pull/11827))
#### Estimated changes
modified src/group_theory/nilpotent.lean
- \+ *lemma* lower_central_series_prod
- \+ *lemma* nilpotency_class_prod



## [2022-02-15 08:27:11](https://github.com/leanprover-community/mathlib/commit/f12b3d9)
feat(topology/algebra): weaken typeclasses to only require `has_continuous_const_smul` ([#11995](https://github.com/leanprover-community/mathlib/pull/11995))
This changes all the continuity-based `const_smul` lemmas to only require `has_continuous_const_smul` rather than `has_continuous_smul`. It does not attempt to  propagate the changes out of this file.
Four new instances are added in `const_mul_action.lean` for `has_continuous_const_smul`: `mul_opposite`, `prod`, `pi`, and `units`; all copied from the corresponding `has_continuous_smul` instance in `mul_action.lean`.
Presumably these lemmas existed before this typeclass did.
At any rate, the connection was less obvious until the rename a few days ago in [#11940](https://github.com/leanprover-community/mathlib/pull/11940).
#### Estimated changes
modified src/topology/algebra/const_mul_action.lean
- \+ *lemma* filter.tendsto.const_smul
- \+ *lemma* continuous_within_at.const_smul
- \+ *lemma* continuous_at.const_smul
- \+ *lemma* continuous_on.const_smul
- \+ *lemma* continuous.const_smul
- \+ *lemma* smul_closure_subset
- \+ *lemma* smul_closure_orbit_subset
- \+ *lemma* tendsto_const_smul_iff
- \+ *lemma* continuous_within_at_const_smul_iff
- \+ *lemma* continuous_on_const_smul_iff
- \+ *lemma* continuous_at_const_smul_iff
- \+ *lemma* continuous_const_smul_iff
- \+ *lemma* is_open_map_smul
- \+ *lemma* is_open.smul
- \+ *lemma* is_closed_map_smul
- \+ *lemma* is_closed.smul
- \+ *lemma* tendsto_const_smul_iff₀
- \+ *lemma* continuous_within_at_const_smul_iff₀
- \+ *lemma* continuous_on_const_smul_iff₀
- \+ *lemma* continuous_at_const_smul_iff₀
- \+ *lemma* continuous_const_smul_iff₀
- \+ *lemma* is_open_map_smul₀
- \+ *lemma* is_open.smul₀
- \+ *lemma* interior_smul₀
- \+ *lemma* is_closed_map_smul_of_ne_zero
- \+ *lemma* is_closed_map_smul₀
- \+ *lemma* tendsto_const_smul_iff
- \+ *lemma* continuous_within_at_const_smul_iff
- \+ *lemma* continuous_on_const_smul_iff
- \+ *lemma* continuous_at_const_smul_iff
- \+ *lemma* continuous_const_smul_iff
- \+ *lemma* is_open_map_smul
- \+ *lemma* is_closed_map_smul
- \+/\- *def* homeomorph.smul
- \+/\- *def* homeomorph.smul
- \- *def* homeomorph.vadd

modified src/topology/algebra/mul_action.lean
- \- *lemma* filter.tendsto.const_smul
- \- *lemma* continuous_within_at.const_smul
- \- *lemma* continuous_at.const_smul
- \- *lemma* continuous_on.const_smul
- \- *lemma* continuous.const_smul
- \- *lemma* smul_closure_subset
- \- *lemma* smul_closure_orbit_subset
- \- *lemma* tendsto_const_smul_iff
- \- *lemma* continuous_within_at_const_smul_iff
- \- *lemma* continuous_on_const_smul_iff
- \- *lemma* continuous_at_const_smul_iff
- \- *lemma* continuous_const_smul_iff
- \- *lemma* is_open_map_smul
- \- *lemma* is_open.smul
- \- *lemma* is_closed_map_smul
- \- *lemma* is_closed.smul
- \- *lemma* tendsto_const_smul_iff₀
- \- *lemma* continuous_within_at_const_smul_iff₀
- \- *lemma* continuous_on_const_smul_iff₀
- \- *lemma* continuous_at_const_smul_iff₀
- \- *lemma* continuous_const_smul_iff₀
- \- *lemma* is_open_map_smul₀
- \- *lemma* is_open.smul₀
- \- *lemma* interior_smul₀
- \- *lemma* is_closed_map_smul_of_ne_zero
- \- *lemma* is_closed_map_smul₀
- \- *lemma* tendsto_const_smul_iff
- \- *lemma* continuous_within_at_const_smul_iff
- \- *lemma* continuous_on_const_smul_iff
- \- *lemma* continuous_at_const_smul_iff
- \- *lemma* continuous_const_smul_iff
- \- *lemma* is_open_map_smul
- \- *lemma* is_closed_map_smul



## [2022-02-15 06:34:35](https://github.com/leanprover-community/mathlib/commit/f1334b9)
chore(category_theory/triangulated/rotate): optimizing some proofs ([#12031](https://github.com/leanprover-community/mathlib/pull/12031))
Removes some non-terminal `simp`s; replaces some `simp`s by `simp only [...]` and `rw`.
Compilation time dropped from 1m40s to 1m05s on my machine.
#### Estimated changes
modified src/category_theory/triangulated/rotate.lean



## [2022-02-15 05:21:51](https://github.com/leanprover-community/mathlib/commit/4c76eac)
chore(probability_theory/*): Rename folder  ([#11989](https://github.com/leanprover-community/mathlib/pull/11989))
Rename `probability_theory` to `probability`.
#### Estimated changes
renamed src/probability_theory/density.lean to src/probability/density.lean

renamed src/probability_theory/independence.lean to src/probability/independence.lean

renamed src/probability_theory/integration.lean to src/probability/integration.lean

renamed src/probability_theory/martingale.lean to src/probability/martingale.lean

renamed src/probability_theory/notation.lean to src/probability/notation.lean

renamed src/probability_theory/stopping.lean to src/probability/stopping.lean



## [2022-02-15 02:51:23](https://github.com/leanprover-community/mathlib/commit/430faa9)
chore(scripts): update nolints.txt ([#12048](https://github.com/leanprover-community/mathlib/pull/12048))
I am happy to remove some nolints for you!
#### Estimated changes
modified scripts/nolints.txt

modified scripts/style-exceptions.txt



## [2022-02-15 02:21:36](https://github.com/leanprover-community/mathlib/commit/a1283d0)
feat(analysis/inner_product_space/adjoint): `is_self_adjoint_iff_eq_a… ([#12047](https://github.com/leanprover-community/mathlib/pull/12047))
…djoint`
A self-adjoint linear map is equal to its adjoint.
#### Estimated changes
modified src/analysis/inner_product_space/adjoint.lean
- \+ *lemma* is_self_adjoint_iff_eq_adjoint



## [2022-02-15 01:27:49](https://github.com/leanprover-community/mathlib/commit/92ac8ff)
feat(analysis/special_functions/complex/arg): `arg_coe_angle_eq_iff` ([#12017](https://github.com/leanprover-community/mathlib/pull/12017))
Add a lemma that `arg` of two numbers coerced to `real.angle` is equal
if and only if `arg` is equal.
#### Estimated changes
modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* arg_coe_angle_eq_iff



## [2022-02-14 23:41:27](https://github.com/leanprover-community/mathlib/commit/5dc720d)
chore(number_theory/padics/padic_norm): golf `prod_pow_prime_padic_val_nat` ([#12034](https://github.com/leanprover-community/mathlib/pull/12034))
A todo comment said "this proof can probably be golfed with `factorization` stuff"; it turns out that indeed it can be. :)
#### Estimated changes
modified src/number_theory/padics/padic_norm.lean



## [2022-02-14 21:58:15](https://github.com/leanprover-community/mathlib/commit/f9bac45)
chore(category_theory/linear/yoneda): Removing some slow uses of `obviously` ([#11979](https://github.com/leanprover-community/mathlib/pull/11979))
Providing explicit proofs for `map_id'` and `map_comp'` rather than leaving them for `obviously` (and hence `tidy`) to fill in.
Suggested by Kevin Buzzard in [this Zulip comment](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60tidy.60.20in.20mathlib.20proofs/near/271474418).
(These are temporary changes until `obviously` can be tweaked to do this more quickly)
#### Estimated changes
modified src/category_theory/linear/yoneda.lean



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
modified src/topology/alexandroff.lean
- \+ *lemma* not_continuous_cofinite_topology_of_symm
- \+ *lemma* continuous.homeo_of_equiv_compact_to_t2.t1_counterexample

modified src/topology/constructions.lean
- \+ *lemma* is_open_iff
- \+ *lemma* is_open_iff'
- \+ *lemma* is_closed_iff
- \+ *lemma* nhds_eq
- \+ *lemma* mem_nhds_iff
- \- *lemma* nhds_cofinite
- \- *lemma* mem_nhds_cofinite
- \+/\- *def* cofinite_topology
- \+ *def* of
- \+/\- *def* cofinite_topology

modified src/topology/homeomorph.lean
- \- *lemma* homeo_of_equiv_compact_to_t2.t1_counterexample

modified src/topology/separation.lean
- \+/\- *lemma* t1_space_tfae
- \+ *lemma* t1_space_iff_continuous_cofinite_of
- \+ *lemma* cofinite_topology.continuous_of
- \+/\- *lemma* t1_space_tfae
- \- *lemma* t1_space_iff_le_cofinite



## [2022-02-14 21:58:13](https://github.com/leanprover-community/mathlib/commit/ec11e5f)
feat(algebra/covariant_and_contravariant): covariance and monotonicity ([#11815](https://github.com/leanprover-community/mathlib/pull/11815))
Some simple lemmas about monotonicity and covariant operators. Proves things like `monotone f → monotone (λ n, f (3 + n))` by library search.
#### Estimated changes
modified src/algebra/covariant_and_contravariant.lean
- \+ *lemma* covariant.monotone_of_const
- \+ *lemma* monotone.covariant_of_const
- \+ *lemma* monotone.covariant_of_const'
- \+ *lemma* antitone.covariant_of_const
- \+ *lemma* antitone.covariant_of_const'



## [2022-02-14 20:17:46](https://github.com/leanprover-community/mathlib/commit/4ba8334)
doc(number_theory/cyclotomic/gal): fix typo ([#12038](https://github.com/leanprover-community/mathlib/pull/12038))
#### Estimated changes
modified src/number_theory/cyclotomic/gal.lean



## [2022-02-14 20:17:44](https://github.com/leanprover-community/mathlib/commit/263833c)
feat(data/nat/factorization): add `le_of_mem_factorization` ([#12032](https://github.com/leanprover-community/mathlib/pull/12032))
`le_of_mem_factors`: every factor of `n` is `≤ n`
`le_of_mem_factorization`: everything in `n.factorization.support` is `≤ n`
#### Estimated changes
modified src/data/nat/factorization.lean
- \+ *lemma* le_of_mem_factorization

modified src/data/nat/prime.lean
- \+ *lemma* le_of_mem_factors



## [2022-02-14 20:17:42](https://github.com/leanprover-community/mathlib/commit/1a3c069)
chore(data/equiv/set): more lemmas about prod ([#12022](https://github.com/leanprover-community/mathlib/pull/12022))
Note we don't need the `symm` lemmas for `prod.comm`, since `prod.comm` is involutive
#### Estimated changes
modified src/data/equiv/set.lean
- \+ *lemma* prod_comm_preimage
- \+ *lemma* prod_comm_image
- \+ *lemma* prod_assoc_symm_preimage
- \+ *lemma* prod_assoc_image
- \+ *lemma* prod_assoc_symm_image



## [2022-02-14 18:40:35](https://github.com/leanprover-community/mathlib/commit/583ea58)
feat(data/list/big_operators): add `list.prod_map_mul` ([#12029](https://github.com/leanprover-community/mathlib/pull/12029))
This is an analogue of the corresponding lemma `multiset.prod_map_mul`.
#### Estimated changes
modified src/data/list/big_operators.lean
- \+ *lemma* prod_map_mul



## [2022-02-14 14:46:55](https://github.com/leanprover-community/mathlib/commit/199e8ca)
feat(algebra/star/self_adjoint): generalize scalar action instances ([#12021](https://github.com/leanprover-community/mathlib/pull/12021))
The `distrib_mul_action` instance did not require the underlying space to be a module.
#### Estimated changes
modified src/algebra/star/self_adjoint.lean
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_smul



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
modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* trans_one
- \+ *lemma* one_trans
- \+ *lemma* refl_mul
- \+ *lemma* mul_refl



## [2022-02-14 12:13:11](https://github.com/leanprover-community/mathlib/commit/d33792e)
feat(data/nat/factorization): add lemma `factorization_gcd` ([#11605](https://github.com/leanprover-community/mathlib/pull/11605))
For positive `a` and `b`, `(gcd a b).factorization = a.factorization ⊓ b.factorization`; i.e. the power of prime `p` in `gcd a b` is the minimum of its powers in `a` and `b`.  This is Theorem 1.12 in Apostol (1976) Introduction to Analytic Number Theory.
#### Estimated changes
modified src/data/nat/factorization.lean
- \+ *lemma* factorization_gcd



## [2022-02-14 10:22:27](https://github.com/leanprover-community/mathlib/commit/132ea05)
docs(computability/partrec_code): add docs ([#11929](https://github.com/leanprover-community/mathlib/pull/11929))
#### Estimated changes
modified src/computability/partrec_code.lean



## [2022-02-14 10:22:26](https://github.com/leanprover-community/mathlib/commit/dce5dd4)
feat(order/well_founded, set_theory/ordinal_arithmetic): `eq_strict_mono_iff_eq_range` ([#11882](https://github.com/leanprover-community/mathlib/pull/11882))
Two strict monotonic functions with well-founded domains are equal iff their ranges are. We use this to golf `eq_enum_ord`.
#### Estimated changes
modified src/order/well_founded.lean
- \+ *theorem* eq_strict_mono_iff_eq_range

modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* eq_enum_ord
- \+/\- *theorem* eq_enum_ord



## [2022-02-14 08:41:45](https://github.com/leanprover-community/mathlib/commit/a87d431)
feat(topology/algebra): add `@[to_additive]` to some lemmas ([#12018](https://github.com/leanprover-community/mathlib/pull/12018))
* rename `embed_product` to `units.embed_product`, add `add_units.embed_product`;
* add additive versions to lemmas about topology on `units M`;
* add `add_opposite.topological_space` and `add_opposite.has_continuous_add`;
* move `continuous_op` and `continuous_unop` to the `mul_opposite` namespace, add additive versions.
#### Estimated changes
modified src/algebra/group/prod.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/monoid.lean
- \+/\- *lemma* continuous_unop
- \+/\- *lemma* continuous_op
- \+/\- *lemma* continuous_embed_product
- \+/\- *lemma* continuous_coe
- \+/\- *lemma* continuous_unop
- \+/\- *lemma* continuous_op
- \+/\- *lemma* continuous_embed_product
- \+/\- *lemma* continuous_coe

modified src/topology/algebra/mul_action.lean



## [2022-02-14 08:04:35](https://github.com/leanprover-community/mathlib/commit/2ceacc1)
feat(measure_theory/measure): more lemmas about `null_measurable_set`s ([#12019](https://github.com/leanprover-community/mathlib/pull/12019))
#### Estimated changes
modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* null_measurable_set_smul

modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* restrict_mono'
- \+/\- *lemma* restrict_mono
- \+/\- *lemma* restrict_mono_ae
- \+/\- *lemma* restrict_congr_set
- \+ *lemma* restrict_apply₀'
- \+ *lemma* restrict_restrict₀
- \+ *lemma* restrict_restrict₀'
- \+/\- *lemma* restrict_Union_ae
- \+/\- *lemma* restrict_mono'
- \+/\- *lemma* restrict_mono
- \+/\- *lemma* restrict_mono_ae
- \+/\- *lemma* restrict_congr_set
- \+/\- *lemma* restrict_Union_ae



## [2022-02-14 07:20:08](https://github.com/leanprover-community/mathlib/commit/25ebf41)
chore(analysis): move some code ([#12008](https://github.com/leanprover-community/mathlib/pull/12008))
Move the code that doesn't rely on `normed_space` from
`analysis.normed_space.add_torsor` to
`analysis.normed.group.add_torsor`.
#### Estimated changes
created src/analysis/normed/group/add_torsor.lean
- \+ *lemma* dist_eq_norm_vsub
- \+ *lemma* dist_vadd_cancel_left
- \+ *lemma* dist_vadd_cancel_right
- \+ *lemma* dist_vadd_left
- \+ *lemma* dist_vadd_right
- \+ *lemma* dist_vsub_cancel_left
- \+ *lemma* dist_vsub_cancel_right
- \+ *lemma* vadd_ball
- \+ *lemma* vadd_closed_ball
- \+ *lemma* vadd_sphere
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
- \+ *lemma* continuous_vsub
- \+ *lemma* filter.tendsto.vsub
- \+ *lemma* continuous.vsub
- \+ *lemma* continuous_at.vsub
- \+ *lemma* continuous_within_at.vsub
- \+ *lemma* filter.tendsto.line_map
- \+ *lemma* filter.tendsto.midpoint
- \+ *def* isometric.vadd_const
- \+ *def* isometric.const_vadd
- \+ *def* isometric.const_vsub
- \+ *def* pseudo_metric_space_of_normed_group_of_add_torsor
- \+ *def* metric_space_of_normed_group_of_add_torsor

modified src/analysis/normed_space/add_torsor.lean
- \- *lemma* dist_eq_norm_vsub
- \- *lemma* dist_vadd_cancel_left
- \- *lemma* dist_vadd_cancel_right
- \- *lemma* dist_vadd_left
- \- *lemma* dist_vadd_right
- \- *lemma* dist_vsub_cancel_left
- \- *lemma* dist_vsub_cancel_right
- \- *lemma* vadd_ball
- \- *lemma* vadd_closed_ball
- \- *lemma* vadd_sphere
- \- *lemma* dist_vadd_vadd_le
- \- *lemma* dist_vsub_vsub_le
- \- *lemma* nndist_vadd_vadd_le
- \- *lemma* nndist_vsub_vsub_le
- \- *lemma* edist_vadd_vadd_le
- \- *lemma* edist_vsub_vsub_le
- \- *lemma* lipschitz_with.vadd
- \- *lemma* lipschitz_with.vsub
- \- *lemma* uniform_continuous_vadd
- \- *lemma* uniform_continuous_vsub
- \- *lemma* continuous_vsub
- \- *lemma* filter.tendsto.vsub
- \- *lemma* continuous.vsub
- \- *lemma* continuous_at.vsub
- \- *lemma* continuous_within_at.vsub
- \- *lemma* filter.tendsto.line_map
- \- *lemma* filter.tendsto.midpoint
- \- *def* isometric.vadd_const
- \- *def* isometric.const_vadd
- \- *def* isometric.const_vsub
- \- *def* pseudo_metric_space_of_normed_group_of_add_torsor
- \- *def* metric_space_of_normed_group_of_add_torsor



## [2022-02-14 06:18:50](https://github.com/leanprover-community/mathlib/commit/26fd61c)
feat(analysis/complex/isometry): `rotation_trans` ([#12015](https://github.com/leanprover-community/mathlib/pull/12015))
Add a `simp` lemma about the composition of two rotations.
#### Estimated changes
modified src/analysis/complex/isometry.lean
- \+ *lemma* rotation_trans



## [2022-02-14 06:18:49](https://github.com/leanprover-community/mathlib/commit/77dfac2)
feat(order/filter/bases): basis of infimum of filters ([#11855](https://github.com/leanprover-community/mathlib/pull/11855))
#### Estimated changes
modified src/order/filter/bases.lean
- \+ *lemma* has_basis_infi

modified src/order/filter/pi.lean
- \+ *lemma* has_basis_pi



## [2022-02-14 04:42:39](https://github.com/leanprover-community/mathlib/commit/6550cba)
feat(order/partition/finpartition): Finite partitions ([#9795](https://github.com/leanprover-community/mathlib/pull/9795))
This defines finite partitions along with quite a few constructions,
#### Estimated changes
modified src/data/finset/lattice.lean
- \+/\- *lemma* sup_inf_distrib_left
- \+/\- *lemma* sup_inf_distrib_right
- \+/\- *lemma* disjoint_sup_right
- \+/\- *lemma* disjoint_sup_left
- \+/\- *lemma* inf_sup_distrib_left
- \+/\- *lemma* inf_sup_distrib_right
- \+/\- *lemma* disjoint_sup_right
- \+/\- *lemma* disjoint_sup_left
- \+/\- *lemma* sup_inf_distrib_left
- \+/\- *lemma* sup_inf_distrib_right
- \+/\- *lemma* inf_sup_distrib_left
- \+/\- *lemma* inf_sup_distrib_right

modified src/data/finset/prod.lean
- \+ *lemma* mk_mem_product

modified src/data/set/pairwise.lean
- \+ *lemma* pairwise_disjoint.eq_of_le

modified src/data/setoid/partition.lean

created src/order/partition/finpartition.lean
- \+ *lemma* default_eq_empty
- \+ *lemma* ne_bot
- \+ *lemma* parts_eq_empty_iff
- \+ *lemma* parts_nonempty_iff
- \+ *lemma* parts_nonempty
- \+ *lemma* parts_inf
- \+ *lemma* exists_le_of_le
- \+ *lemma* card_mono
- \+ *lemma* mem_bind
- \+ *lemma* card_bind
- \+ *lemma* card_extend
- \+ *lemma* nonempty_of_mem_parts
- \+ *lemma* exists_mem
- \+ *lemma* bUnion_parts
- \+ *lemma* sum_card_parts
- \+ *lemma* parts_bot
- \+ *lemma* card_bot
- \+ *lemma* mem_bot_iff
- \+ *lemma* card_parts_le_card
- \+ *lemma* mem_atomise
- \+ *lemma* atomise_empty
- \+ *lemma* card_atomise_le
- \+ *lemma* bUnion_filter_atomise
- \+ *def* of_erase
- \+ *def* of_subset
- \+ *def* copy
- \+ *def* indiscrete
- \+ *def* _root_.is_atom.unique_finpartition
- \+ *def* bind
- \+ *def* extend
- \+ *def* avoid
- \+ *def* atomise

modified src/order/sup_indep.lean



## [2022-02-13 20:36:13](https://github.com/leanprover-community/mathlib/commit/f91a32d)
feat(data/nat/factorization): add lemma `prod_prime_factors_dvd` ([#11572](https://github.com/leanprover-community/mathlib/pull/11572))
For all `n : ℕ`, the product of the set of prime factors of `n` divides `n`, 
i.e. `(∏ (p : ℕ) in n.factors.to_finset, p) ∣ n`
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* to_finset_prod_dvd_prod
- \+/\- *lemma* to_finset_prod_dvd_prod

modified src/data/nat/factorization.lean
- \+ *lemma* prod_prime_factors_dvd



## [2022-02-13 17:37:37](https://github.com/leanprover-community/mathlib/commit/b08dc17)
chore(number_theory/dioph): fix docs ([#12011](https://github.com/leanprover-community/mathlib/pull/12011))
#### Estimated changes
modified src/number_theory/dioph.lean



## [2022-02-12 22:55:33](https://github.com/leanprover-community/mathlib/commit/af1355c)
chore(measure_theory/integral/lebesgue): use to_additive when declaring instances and basic lemmas about simple functions ([#12000](https://github.com/leanprover-community/mathlib/pull/12000))
I also grouped similar lemmas together and added one or two missing ones.
#### Estimated changes
modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* const_one
- \+ *lemma* coe_one
- \+/\- *lemma* coe_mul
- \+ *lemma* coe_inv
- \+ *lemma* coe_div
- \+/\- *lemma* mul_apply
- \+ *lemma* div_apply
- \+ *lemma* inv_apply
- \+/\- *lemma* sup_apply
- \+ *lemma* inf_apply
- \+ *lemma* range_one
- \+/\- *lemma* mul_eq_map₂
- \+/\- *lemma* sup_eq_map₂
- \- *lemma* coe_zero
- \- *lemma* const_zero
- \- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \- *lemma* range_zero
- \+/\- *lemma* sup_apply
- \+/\- *lemma* mul_apply
- \- *lemma* add_apply
- \- *lemma* add_eq_map₂
- \+/\- *lemma* mul_eq_map₂
- \+/\- *lemma* sup_eq_map₂
- \- *lemma* coe_neg
- \- *lemma* coe_sub
- \- *lemma* sub_apply
- \+ *theorem* map_mul
- \- *theorem* map_add



## [2022-02-12 21:57:51](https://github.com/leanprover-community/mathlib/commit/4b217ea)
chore(topology/algebra): rename file to match renamed lemmas ([#11996](https://github.com/leanprover-community/mathlib/pull/11996))
[#11940](https://github.com/leanprover-community/mathlib/pull/11940) renamed the lemmas from `continuous_smul₂` to `continuous_const_smul`, so this renames the file from `mul_action2` to `const_mul_action` accordingly.
#### Estimated changes
renamed src/topology/algebra/mul_action2.lean to src/topology/algebra/const_mul_action.lean

modified src/topology/algebra/mul_action.lean



## [2022-02-12 19:33:32](https://github.com/leanprover-community/mathlib/commit/4a4a3a9)
chore(data/finset/basic): Golf and compress ([#11987](https://github.com/leanprover-community/mathlib/pull/11987))
* Move the `lattice` instance earlier so that it can be used to prove lemmas
* Golf proofs
* Compress statements within the style guidelines
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* eq_empty_of_forall_not_mem
- \+/\- *lemma* coe_eq_empty
- \+ *lemma* eq_of_mem_singleton
- \+/\- *lemma* singleton_subset_set_iff
- \+/\- *lemma* singleton_subset_iff
- \+ *lemma* subset_singleton_iff'
- \+ *lemma* mem_cons
- \+/\- *lemma* mem_cons_self
- \+ *lemma* cons_val
- \+ *lemma* mk_cons
- \+ *lemma* nonempty_cons
- \+/\- *lemma* cons_subset_cons
- \+ *lemma* mem_insert
- \+ *lemma* mem_insert_of_mem
- \+ *lemma* mem_of_mem_insert_of_ne
- \+ *lemma* insert_eq_of_mem
- \+/\- *lemma* ne_insert_of_not_mem
- \+ *lemma* insert_subset
- \+ *lemma* subset_insert
- \+/\- *lemma* ssubset_iff
- \+/\- *lemma* ssubset_insert
- \+ *lemma* sup_eq_union
- \+ *lemma* inf_eq_inter
- \+ *lemma* union_val_nd
- \+ *lemma* union_val
- \+ *lemma* mem_union
- \+ *lemma* disj_union_eq_union
- \+ *lemma* mem_union_left
- \+ *lemma* mem_union_right
- \+ *lemma* forall_mem_union
- \+ *lemma* not_mem_union
- \+ *lemma* union_subset
- \+/\- *lemma* union_subset_union
- \+ *lemma* union_comm
- \+ *lemma* union_assoc
- \+ *lemma* union_idempotent
- \+ *lemma* union_subset_left
- \+ *lemma* union_subset_right
- \+ *lemma* union_left_comm
- \+ *lemma* union_right_comm
- \+ *lemma* insert_union_distrib
- \+/\- *lemma* union_eq_left_iff_subset
- \+/\- *lemma* left_eq_union_iff_subset
- \+/\- *lemma* union_eq_right_iff_subset
- \+/\- *lemma* right_eq_union_iff_subset
- \+ *lemma* inter_val
- \+ *lemma* subset_inter
- \+ *lemma* inter_self
- \+ *lemma* inter_empty
- \+ *lemma* empty_inter
- \+/\- *lemma* inter_subset_inter_left
- \+/\- *lemma* inter_subset_inter_right
- \+/\- *lemma* union_subset_iff
- \+/\- *lemma* subset_inter_iff
- \+ *lemma* inter_eq_left_iff_subset
- \+ *lemma* inter_eq_right_iff_subset
- \+ *lemma* ne_of_mem_erase
- \+ *lemma* mem_of_mem_erase
- \+ *lemma* mem_erase_of_ne_of_mem
- \+/\- *lemma* eq_of_mem_of_not_mem_erase
- \+/\- *lemma* erase_inj
- \+/\- *lemma* erase_inj_on
- \+ *lemma* union_sdiff_of_subset
- \+ *lemma* inter_sdiff
- \+ *lemma* sdiff_inter_self
- \+ *lemma* sdiff_self
- \+ *lemma* sdiff_inter_distrib_right
- \+ *lemma* sdiff_inter_self_left
- \+ *lemma* sdiff_inter_self_right
- \+ *lemma* sdiff_empty
- \+ *lemma* sdiff_subset_sdiff
- \+/\- *lemma* sdiff_union_inter
- \+/\- *lemma* sdiff_idem
- \+/\- *lemma* empty_sdiff
- \+/\- *lemma* insert_sdiff_of_mem
- \+/\- *lemma* sdiff_insert_of_not_mem
- \+/\- *lemma* sdiff_subset
- \+/\- *lemma* sdiff_ssubset
- \+/\- *lemma* union_sdiff_distrib
- \+/\- *lemma* sdiff_union_distrib
- \+/\- *lemma* union_sdiff_self
- \+/\- *lemma* sdiff_erase
- \+/\- *lemma* sdiff_sdiff_self_left
- \+/\- *lemma* piecewise_insert_self
- \+/\- *lemma* piecewise_empty
- \+/\- *lemma* piecewise_coe
- \+/\- *lemma* piecewise_eq_of_mem
- \+/\- *lemma* piecewise_insert_of_ne
- \+/\- *lemma* piecewise_insert
- \+/\- *lemma* monotone_filter_left
- \+ *lemma* sdiff_eq_self
- \+/\- *lemma* filter_eq
- \+/\- *lemma* filter_ne
- \+/\- *lemma* filter_ne'
- \+ *lemma* range_add_one
- \+/\- *lemma* mem_range_le
- \+ *lemma* exists_mem_insert
- \+ *lemma* forall_mem_insert
- \+ *lemma* mem_to_finset
- \+/\- *lemma* to_finset_zero
- \+/\- *lemma* to_finset_singleton
- \+/\- *lemma* to_finset_add
- \+/\- *lemma* to_finset_inter
- \+/\- *lemma* to_finset_union
- \+/\- *lemma* to_finset_subset
- \+/\- *lemma* val_le_iff_val_subset
- \+ *lemma* to_finset_eq
- \+ *lemma* mem_to_finset
- \+ *lemma* to_finset_nil
- \+ *lemma* to_finset_cons
- \+/\- *lemma* to_finset_eq_iff_perm_erase_dup
- \+/\- *lemma* to_finset.ext
- \+/\- *lemma* to_finset_eq_of_perm
- \+/\- *lemma* perm_of_nodup_nodup_to_finset_eq
- \+/\- *lemma* to_finset_append
- \+/\- *lemma* to_finset_reverse
- \+/\- *lemma* to_finset_repeat_of_ne_zero
- \+/\- *lemma* to_finset_eq_empty_iff
- \+ *lemma* mem_map_equiv
- \+ *lemma* mem_map'
- \+ *lemma* mem_map_of_mem
- \+ *lemma* map_insert
- \+/\- *lemma* mem_image_const
- \+/\- *lemma* mem_image_const_self
- \+/\- *lemma* _root_.function.injective.mem_finset_image
- \+/\- *lemma* nonempty.image_iff
- \+ *lemma* image_id
- \+ *lemma* image_subset_iff
- \+ *lemma* image_inter
- \+/\- *lemma* map_subtype_subset
- \+/\- *lemma* subset_image_iff
- \+/\- *lemma* to_list_empty
- \+/\- *lemma* coe_to_list
- \+ *lemma* mem_bUnion
- \+ *lemma* bUnion_congr
- \+/\- *lemma* bUnion_mono
- \+/\- *lemma* bUnion_subset_bUnion_of_subset_left
- \+/\- *lemma* subset_bUnion_of_mem
- \+/\- *lemma* bUnion_singleton_eq_self
- \+/\- *lemma* nonempty.bUnion
- \+ *lemma* disjoint_left
- \+ *lemma* disjoint_val
- \+ *lemma* disjoint_iff_inter_eq_empty
- \+ *lemma* disjoint_right
- \+ *lemma* disjoint_iff_ne
- \+/\- *lemma* not_disjoint_iff
- \+ *lemma* disjoint_of_subset_left
- \+ *lemma* disjoint_of_subset_right
- \+ *lemma* disjoint_singleton_left
- \+ *lemma* disjoint_singleton_right
- \+/\- *lemma* disjoint_singleton
- \+ *lemma* disjoint_insert_left
- \+ *lemma* disjoint_insert_right
- \+ *lemma* disjoint_union_left
- \+ *lemma* disjoint_union_right
- \+/\- *lemma* sdiff_disjoint
- \+/\- *lemma* disjoint_sdiff
- \+/\- *lemma* sdiff_eq_self_iff_disjoint
- \+/\- *lemma* sdiff_eq_self_of_disjoint
- \+/\- *lemma* disjoint_self_iff_empty
- \+/\- *lemma* disjoint_bUnion_left
- \+/\- *lemma* disjoint_bUnion_right
- \+/\- *lemma* disjoint_filter
- \+/\- *lemma* disjoint_filter_filter
- \+/\- *lemma* disjoint_iff_disjoint_coe
- \+/\- *lemma* finset_congr_refl
- \+/\- *lemma* finset_congr_symm
- \+/\- *lemma* disjoint_to_finset_iff_disjoint
- \+/\- *lemma* coe_eq_empty
- \+/\- *lemma* singleton_subset_set_iff
- \+/\- *lemma* singleton_subset_iff
- \+/\- *lemma* mem_cons_self
- \+/\- *lemma* cons_subset_cons
- \+/\- *lemma* ne_insert_of_not_mem
- \+/\- *lemma* ssubset_iff
- \+/\- *lemma* ssubset_insert
- \+/\- *lemma* union_subset_union
- \+/\- *lemma* union_eq_left_iff_subset
- \+/\- *lemma* left_eq_union_iff_subset
- \+/\- *lemma* union_eq_right_iff_subset
- \+/\- *lemma* right_eq_union_iff_subset
- \+/\- *lemma* inter_subset_inter_right
- \+/\- *lemma* inter_subset_inter_left
- \+/\- *lemma* union_subset_iff
- \+/\- *lemma* subset_inter_iff
- \+/\- *lemma* eq_of_mem_of_not_mem_erase
- \+/\- *lemma* erase_inj
- \+/\- *lemma* erase_inj_on
- \+/\- *lemma* sdiff_union_inter
- \+/\- *lemma* sdiff_idem
- \+/\- *lemma* empty_sdiff
- \+/\- *lemma* insert_sdiff_of_mem
- \+/\- *lemma* sdiff_insert_of_not_mem
- \+/\- *lemma* sdiff_subset
- \+/\- *lemma* sdiff_ssubset
- \+/\- *lemma* union_sdiff_distrib
- \+/\- *lemma* sdiff_union_distrib
- \+/\- *lemma* union_sdiff_self
- \+/\- *lemma* sdiff_erase
- \+/\- *lemma* sdiff_sdiff_self_left
- \+/\- *lemma* piecewise_insert_self
- \+/\- *lemma* piecewise_empty
- \+/\- *lemma* piecewise_coe
- \+/\- *lemma* piecewise_eq_of_mem
- \+/\- *lemma* piecewise_insert_of_ne
- \+/\- *lemma* piecewise_insert
- \+/\- *lemma* monotone_filter_left
- \+/\- *lemma* filter_eq
- \+/\- *lemma* filter_ne
- \+/\- *lemma* filter_ne'
- \+/\- *lemma* mem_range_le
- \+/\- *lemma* to_finset_zero
- \+/\- *lemma* to_finset_singleton
- \+/\- *lemma* to_finset_add
- \+/\- *lemma* to_finset_inter
- \+/\- *lemma* to_finset_union
- \+/\- *lemma* to_finset_subset
- \+/\- *lemma* val_le_iff_val_subset
- \+/\- *lemma* to_finset_eq_iff_perm_erase_dup
- \+/\- *lemma* to_finset.ext
- \+/\- *lemma* to_finset_eq_of_perm
- \+/\- *lemma* perm_of_nodup_nodup_to_finset_eq
- \+/\- *lemma* to_finset_append
- \+/\- *lemma* to_finset_reverse
- \+/\- *lemma* to_finset_repeat_of_ne_zero
- \+/\- *lemma* to_finset_eq_empty_iff
- \+/\- *lemma* mem_image_const
- \+/\- *lemma* mem_image_const_self
- \+/\- *lemma* _root_.function.injective.mem_finset_image
- \- *lemma* nonempty.image
- \+/\- *lemma* nonempty.image_iff
- \+/\- *lemma* map_subtype_subset
- \+/\- *lemma* subset_image_iff
- \+/\- *lemma* to_list_empty
- \+/\- *lemma* coe_to_list
- \+/\- *lemma* bUnion_mono
- \+/\- *lemma* bUnion_subset_bUnion_of_subset_left
- \+/\- *lemma* subset_bUnion_of_mem
- \+/\- *lemma* bUnion_singleton_eq_self
- \+/\- *lemma* nonempty.bUnion
- \+/\- *lemma* not_disjoint_iff
- \+/\- *lemma* disjoint_singleton
- \+/\- *lemma* sdiff_disjoint
- \+/\- *lemma* disjoint_sdiff
- \+/\- *lemma* sdiff_eq_self_iff_disjoint
- \+/\- *lemma* sdiff_eq_self_of_disjoint
- \+/\- *lemma* disjoint_self_iff_empty
- \+/\- *lemma* disjoint_bUnion_left
- \+/\- *lemma* disjoint_bUnion_right
- \+/\- *lemma* disjoint_filter
- \+/\- *lemma* disjoint_filter_filter
- \+/\- *lemma* disjoint_iff_disjoint_coe
- \+/\- *lemma* finset_congr_refl
- \+/\- *lemma* finset_congr_symm
- \+/\- *lemma* disjoint_to_finset_iff_disjoint
- \- *theorem* eq_empty_of_forall_not_mem
- \- *theorem* eq_of_mem_singleton
- \- *theorem* mem_cons
- \- *theorem* cons_val
- \- *theorem* mk_cons
- \- *theorem* nonempty_cons
- \- *theorem* mem_insert
- \- *theorem* mem_insert_of_mem
- \- *theorem* mem_of_mem_insert_of_ne
- \- *theorem* insert_eq_of_mem
- \- *theorem* insert_subset
- \- *theorem* subset_insert
- \- *theorem* union_val_nd
- \- *theorem* union_val
- \- *theorem* mem_union
- \- *theorem* disj_union_eq_union
- \- *theorem* mem_union_left
- \- *theorem* mem_union_right
- \- *theorem* forall_mem_union
- \- *theorem* not_mem_union
- \- *theorem* union_subset
- \- *theorem* union_comm
- \- *theorem* union_assoc
- \- *theorem* union_idempotent
- \- *theorem* union_subset_left
- \- *theorem* union_subset_right
- \- *theorem* union_left_comm
- \- *theorem* union_right_comm
- \- *theorem* insert_union_distrib
- \- *theorem* inter_val
- \- *theorem* subset_inter
- \- *theorem* inter_self
- \- *theorem* inter_empty
- \- *theorem* empty_inter
- \- *theorem* sup_eq_union
- \- *theorem* inf_eq_inter
- \- *theorem* inter_eq_left_iff_subset
- \- *theorem* inter_eq_right_iff_subset
- \- *theorem* ne_of_mem_erase
- \- *theorem* mem_of_mem_erase
- \- *theorem* mem_erase_of_ne_of_mem
- \- *theorem* union_sdiff_of_subset
- \- *theorem* inter_sdiff
- \- *theorem* sdiff_inter_self
- \- *theorem* sdiff_self
- \- *theorem* sdiff_inter_distrib_right
- \- *theorem* sdiff_inter_self_left
- \- *theorem* sdiff_inter_self_right
- \- *theorem* sdiff_empty
- \- *theorem* sdiff_subset_sdiff
- \- *theorem* sdiff_eq_self
- \- *theorem* range_add_one
- \- *theorem* exists_mem_insert
- \- *theorem* forall_mem_insert
- \- *theorem* mem_to_finset
- \- *theorem* to_finset_eq
- \- *theorem* mem_to_finset
- \- *theorem* to_finset_nil
- \- *theorem* to_finset_cons
- \- *theorem* mem_map_equiv
- \- *theorem* mem_map'
- \- *theorem* mem_map_of_mem
- \- *theorem* map_insert
- \- *theorem* image_id
- \- *theorem* image_subset_iff
- \- *theorem* image_inter
- \- *theorem* mem_bUnion
- \- *theorem* bUnion_congr
- \- *theorem* disjoint_left
- \- *theorem* disjoint_val
- \- *theorem* disjoint_iff_inter_eq_empty
- \- *theorem* disjoint_right
- \- *theorem* disjoint_iff_ne
- \- *theorem* disjoint_of_subset_left
- \- *theorem* disjoint_of_subset_right
- \- *theorem* disjoint_singleton_left
- \- *theorem* disjoint_singleton_right
- \- *theorem* disjoint_insert_left
- \- *theorem* disjoint_insert_right
- \- *theorem* disjoint_union_left
- \- *theorem* disjoint_union_right
- \+/\- *def* cons
- \+/\- *def* piecewise
- \+/\- *def* cons
- \+/\- *def* piecewise



## [2022-02-12 18:45:31](https://github.com/leanprover-community/mathlib/commit/5f70cd9)
chore(measure_theory/function/ae_eq_fun): replace topological assumptions by measurability assumptions ([#11981](https://github.com/leanprover-community/mathlib/pull/11981))
Since the introduction of the `has_measurable_*` typeclasses, the topological assumptions in that file are only used to derive the measurability assumptions. This PR removes that step.
#### Estimated changes
modified src/measure_theory/function/ae_eq_fun.lean



## [2022-02-12 17:23:47](https://github.com/leanprover-community/mathlib/commit/b72300f)
feat(group_theory/sylow): all max groups normal imply sylow normal ([#11841](https://github.com/leanprover-community/mathlib/pull/11841))
#### Estimated changes
modified src/group_theory/sylow.lean
- \+ *lemma* normal_of_all_max_subgroups_normal



## [2022-02-12 16:17:52](https://github.com/leanprover-community/mathlib/commit/06e7f76)
feat(analysis/analytic/basic): add uniqueness results for power series ([#11896](https://github.com/leanprover-community/mathlib/pull/11896))
This establishes that if a function has two power series representations on balls of positive radius, then the corresponding formal multilinear series are equal; this is only for the one-dimensional case (i.e., for functions from the scalar field). Consequently, one may exchange the radius of convergence between these power series.
#### Estimated changes
modified src/analysis/analytic/basic.lean
- \+ *lemma* asymptotics.is_O.continuous_multilinear_map_apply_eq_zero
- \+ *lemma* has_fpower_series_at.apply_eq_zero
- \+ *lemma* has_fpower_series_at.eq_zero
- \+ *theorem* has_fpower_series_at.eq_formal_multilinear_series
- \+ *theorem* has_fpower_series_on_ball.exchange_radius



## [2022-02-12 09:20:49](https://github.com/leanprover-community/mathlib/commit/91cc4ae)
feat(order/category/BoundedOrder): The category of bounded orders ([#11961](https://github.com/leanprover-community/mathlib/pull/11961))
Define `BoundedOrder`, the category of bounded orders with bounded order homs along with its forgetful functors to `PartialOrder` and `Bipointed`.
#### Estimated changes
created src/order/category/BoundedOrder.lean
- \+ *lemma* BoundedOrder_dual_comp_forget_to_PartialOrder
- \+ *lemma* BoundedOrder_dual_comp_forget_to_Bipointed
- \+ *def* of
- \+ *def* dual
- \+ *def* iso.mk
- \+ *def* dual_equiv

modified src/order/category/PartialOrder.lean
- \+ *lemma* PartialOrder_to_dual_comp_forget_to_Preorder
- \- *lemma* PartialOrder_dual_equiv_comp_forget_to_Preorder

modified src/order/hom/bounded.lean



## [2022-02-12 08:07:28](https://github.com/leanprover-community/mathlib/commit/1b5f8c2)
chore(topology/algebra/ordered/*): Rename folder ([#11988](https://github.com/leanprover-community/mathlib/pull/11988))
Rename `topology.algebra.ordered` to `topology.algebra.order` to match `order`, `algebra.order`, `topology.order`.
#### Estimated changes
modified src/algebra/continued_fractions/computation/approximation_corollaries.lean

modified src/analysis/asymptotics/asymptotics.lean

modified src/analysis/asymptotics/superpolynomial_decay.lean

modified src/analysis/box_integral/box/basic.lean

modified src/analysis/calculus/local_extr.lean

modified src/analysis/convex/strict.lean

modified src/analysis/normed/group/basic.lean

modified src/analysis/normed_space/lp_space.lean

modified src/analysis/special_functions/trigonometric/inverse.lean

modified src/data/real/sqrt.lean

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/topology/algebra/floor_ring.lean

modified src/topology/algebra/infinite_sum.lean

renamed src/topology/algebra/ordered/basic.lean to src/topology/algebra/order/basic.lean

renamed src/topology/algebra/ordered/compact.lean to src/topology/algebra/order/compact.lean

renamed src/topology/algebra/ordered/extend_from.lean to src/topology/algebra/order/extend_from.lean

renamed src/topology/algebra/ordered/intermediate_value.lean to src/topology/algebra/order/intermediate_value.lean

renamed src/topology/algebra/ordered/left_right.lean to src/topology/algebra/order/left_right.lean

renamed src/topology/algebra/ordered/liminf_limsup.lean to src/topology/algebra/order/liminf_limsup.lean

renamed src/topology/algebra/ordered/monotone_continuity.lean to src/topology/algebra/order/monotone_continuity.lean

renamed src/topology/algebra/ordered/monotone_convergence.lean to src/topology/algebra/order/monotone_convergence.lean

renamed src/topology/algebra/ordered/proj_Icc.lean to src/topology/algebra/order/proj_Icc.lean

modified src/topology/algebra/with_zero_topology.lean

modified src/topology/continuous_function/ordered.lean

modified src/topology/fiber_bundle.lean

modified src/topology/homotopy/basic.lean

modified src/topology/instances/ereal.lean

modified src/topology/metric_space/basic.lean

modified src/topology/order/lattice.lean

modified src/topology/path_connected.lean

modified src/topology/tietze_extension.lean



## [2022-02-12 08:07:27](https://github.com/leanprover-community/mathlib/commit/7bebee6)
chore(category_theory/monad/equiv_mon): Removing some slow uses of `obviously` ([#11980](https://github.com/leanprover-community/mathlib/pull/11980))
Providing explicit proofs for various fields rather than leaving them for `obviously` (and hence `tidy`) to fill in.
Follow-up to this suggestion by Kevin Buzzard in [this Zulip comment](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60tidy.60.20in.20mathlib.20proofs/near/271474418).
(These are temporary changes until `obviously` can be tweaked to do this more quickly)
#### Estimated changes
modified src/category_theory/monad/equiv_mon.lean



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
modified src/analysis/calculus/times_cont_diff.lean

modified src/analysis/normed_space/multilinear.lean

modified src/topology/algebra/module/multilinear.lean
- \+ *lemma* to_multilinear_map_zero



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
modified src/analysis/box_integral/integrability.lean

modified src/analysis/fourier.lean

modified src/measure_theory/constructions/pi.lean

modified src/measure_theory/group/arithmetic.lean

created src/measure_theory/group/integration.lean
- \+ *lemma* lintegral_mul_left_eq_self
- \+ *lemma* lintegral_mul_right_eq_self
- \+ *lemma* integral_mul_left_eq_self
- \+ *lemma* integral_mul_right_eq_self
- \+ *lemma* integral_zero_of_mul_left_eq_neg
- \+ *lemma* integral_zero_of_mul_right_eq_neg
- \+ *lemma* lintegral_eq_zero_of_is_mul_left_invariant

renamed src/measure_theory/group/basic.lean to src/measure_theory/group/measure.lean
- \- *lemma* lintegral_eq_zero_of_is_mul_left_invariant
- \- *lemma* lintegral_mul_left_eq_self
- \- *lemma* lintegral_mul_right_eq_self

modified src/measure_theory/group/prod.lean

modified src/measure_theory/integral/bochner.lean
- \- *lemma* integral_mul_left_eq_self
- \- *lemma* integral_mul_right_eq_self
- \- *lemma* integral_zero_of_mul_left_eq_neg
- \- *lemma* integral_zero_of_mul_right_eq_neg

modified src/measure_theory/integral/interval_integral.lean

modified src/measure_theory/integral/periodic.lean

modified src/measure_theory/measure/haar_lebesgue.lean

modified src/measure_theory/measure/lebesgue.lean
- \- *lemma* map_volume_add_left
- \- *lemma* volume_preimage_add_left
- \- *lemma* map_volume_add_right
- \- *lemma* volume_preimage_add_right
- \- *lemma* map_volume_pi_add_left
- \- *lemma* volume_pi_preimage_add_left

modified src/number_theory/liouville/measure.lean



## [2022-02-12 07:11:55](https://github.com/leanprover-community/mathlib/commit/60d3233)
feat(topology/instances/real): metric space structure on nat ([#11963](https://github.com/leanprover-community/mathlib/pull/11963))
Mostly copied from the already existing int version.
#### Estimated changes
modified src/algebra/order/floor.lean
- \+ *lemma* preimage_Ioo
- \+ *lemma* preimage_Ico
- \+ *lemma* preimage_Ioc
- \+ *lemma* preimage_Icc
- \+ *lemma* preimage_Ioi
- \+ *lemma* preimage_Ici
- \+ *lemma* preimage_Iio
- \+ *lemma* preimage_Iic

modified src/topology/instances/real.lean
- \+ *lemma* dist_coe_int
- \+ *lemma* pairwise_one_le_dist
- \+ *lemma* uniform_embedding_coe_rat
- \+ *lemma* closed_embedding_coe_rat
- \+ *lemma* uniform_embedding_coe_real
- \+ *lemma* closed_embedding_coe_real
- \+ *theorem* dist_eq
- \+ *theorem* dist_cast_real
- \+ *theorem* dist_cast_rat
- \+ *theorem* preimage_ball
- \+ *theorem* preimage_closed_ball
- \+ *theorem* closed_ball_eq_Icc



## [2022-02-12 02:46:24](https://github.com/leanprover-community/mathlib/commit/dff8393)
feat(tactic/lint): add unprintable tactic linter ([#11725](https://github.com/leanprover-community/mathlib/pull/11725))
This linter will banish the recurring issue of tactics for which `param_desc` fails, leaving a nasty error message in hovers.
#### Estimated changes
modified src/ring_theory/witt_vector/init_tail.lean

modified src/tactic/interactive.lean

modified src/tactic/itauto.lean

modified src/tactic/linear_combination.lean

modified src/tactic/lint/default.lean

modified src/tactic/lint/misc.lean

modified src/tactic/monotonicity/interactive.lean

modified src/tactic/push_neg.lean

modified src/tactic/squeeze.lean



## [2022-02-12 00:03:02](https://github.com/leanprover-community/mathlib/commit/227293b)
feat(category_theory/category/Twop): The category of two-pointed types ([#11844](https://github.com/leanprover-community/mathlib/pull/11844))
Define `Twop`, the category of two-pointed types. Also add `Pointed_to_Bipointed` and remove the erroneous TODOs.
#### Estimated changes
modified src/category_theory/category/Bipointed.lean
- \+ *lemma* Pointed_to_Bipointed_fst_comp_swap
- \+ *lemma* Pointed_to_Bipointed_snd_comp_swap
- \- *lemma* Pointed_to_Bipointed_fst_comp
- \- *lemma* Pointed_to_Bipointed_snd_comp
- \+ *def* Pointed_to_Bipointed
- \+ *def* Pointed_to_Bipointed_comp_Bipointed_to_Pointed_fst
- \+ *def* Pointed_to_Bipointed_comp_Bipointed_to_Pointed_snd

modified src/category_theory/category/Pointed.lean

created src/category_theory/category/Twop.lean
- \+ *lemma* swap_equiv_symm
- \+ *lemma* Twop_swap_comp_forget_to_Bipointed
- \+ *lemma* Pointed_to_Twop_fst_comp_swap
- \+ *lemma* Pointed_to_Twop_snd_comp_swap
- \+ *lemma* Pointed_to_Twop_fst_comp_forget_to_Bipointed
- \+ *lemma* Pointed_to_Twop_snd_comp_forget_to_Bipointed
- \+ *def* of
- \+ *def* to_Bipointed
- \+ *def* swap
- \+ *def* swap_equiv
- \+ *def* Pointed_to_Twop_fst
- \+ *def* Pointed_to_Twop_snd
- \+ *def* Pointed_to_Twop_fst_forget_comp_Bipointed_to_Pointed_fst_adjunction
- \+ *def* Pointed_to_Twop_snd_forget_comp_Bipointed_to_Pointed_snd_adjunction



## [2022-02-11 21:25:20](https://github.com/leanprover-community/mathlib/commit/788240c)
chore(order/cover): Rename `covers` to `covby` ([#11984](https://github.com/leanprover-community/mathlib/pull/11984))
This matches the way it is written. `a ⋖ b` means that `b` covers `a`, that is `a` is covered by `b`.
#### Estimated changes
modified src/order/atoms.lean
- \+ *lemma* bot_covby_iff
- \+ *lemma* covby_top_iff
- \+ *lemma* bot_covby_top
- \- *lemma* bot_covers_iff
- \- *lemma* covers_top_iff
- \- *lemma* bot_covers_top

modified src/order/cover.lean
- \+ *lemma* covby.lt
- \+ *lemma* not_covby_iff
- \+ *lemma* not_covby
- \+ *lemma* densely_ordered_iff_forall_not_covby
- \+ *lemma* to_dual_covby_to_dual_iff
- \+ *lemma* of_dual_covby_of_dual_iff
- \+ *lemma* covby.le
- \+ *lemma* covby.ne'
- \+ *lemma* covby.Ioo_eq
- \+ *lemma* covby.of_image
- \+ *lemma* covby.image
- \+ *lemma* apply_covby_apply_iff
- \+ *lemma* covby.Ico_eq
- \+ *lemma* covby.Ioc_eq
- \+ *lemma* covby.Icc_eq
- \- *lemma* covers.lt
- \- *lemma* not_covers_iff
- \- *lemma* not_covers
- \- *lemma* densely_ordered_iff_forall_not_covers
- \- *lemma* to_dual_covers_to_dual_iff
- \- *lemma* of_dual_covers_of_dual_iff
- \- *lemma* covers.le
- \- *lemma* covers.ne'
- \- *lemma* covers.Ioo_eq
- \- *lemma* covers.of_image
- \- *lemma* covers.image
- \- *lemma* apply_covers_apply_iff
- \- *lemma* covers.Ico_eq
- \- *lemma* covers.Ioc_eq
- \- *lemma* covers.Icc_eq
- \+ *def* covby
- \- *def* covers

modified src/order/succ_pred/basic.lean
- \+ *lemma* covby_succ_of_nonempty_Ioi
- \+ *lemma* covby_succ
- \+ *lemma* _root_.covby.succ_eq
- \+ *lemma* _root_.covby_iff_succ_eq
- \+ *lemma* pred_covby_of_nonempty_Iio
- \+ *lemma* pred_covby
- \+ *lemma* _root_.covby.pred_eq
- \+ *lemma* _root_.covby_iff_pred_eq
- \+/\- *lemma* succ_pred
- \+/\- *lemma* pred_succ
- \- *lemma* covers_succ_of_nonempty_Ioi
- \- *lemma* covers_succ
- \- *lemma* _root_.covers.succ_eq
- \- *lemma* _root_.covers_iff_succ_eq
- \- *lemma* pred_covers_of_nonempty_Iio
- \- *lemma* pred_covers
- \- *lemma* _root_.covers.pred_eq
- \- *lemma* _root_.covers_iff_pred_eq
- \+/\- *lemma* succ_pred
- \+/\- *lemma* pred_succ



## [2022-02-11 19:49:06](https://github.com/leanprover-community/mathlib/commit/3fcb738)
doc(data/finset/basic): correct some function names ([#11983](https://github.com/leanprover-community/mathlib/pull/11983))
#### Estimated changes
modified src/data/finset/basic.lean



## [2022-02-11 19:49:04](https://github.com/leanprover-community/mathlib/commit/515ce79)
refactor(data/nat/factorization): Use factorization instead of factors.count ([#11384](https://github.com/leanprover-community/mathlib/pull/11384))
Refactor to use `factorization` over `factors.count`, and adjust lemmas to be stated in terms of the former instead.
#### Estimated changes
modified src/algebra/is_prime_pow.lean

modified src/data/nat/factorization.lean
- \+ *lemma* factors_count_eq
- \+ *lemma* eq_of_factorization_eq
- \+/\- *lemma* factorization_zero
- \+/\- *lemma* support_factorization
- \+/\- *lemma* factorization_pow
- \+ *lemma* factorization_mul_apply_of_coprime
- \+ *lemma* factorization_eq_of_coprime_left
- \+ *lemma* factorization_eq_of_coprime_right
- \+/\- *lemma* pow_factorization_dvd
- \+ *lemma* pow_succ_factorization_not_dvd
- \+ *lemma* prime.factorization_pos_of_dvd
- \+/\- *lemma* prime.factorization_pow
- \+ *lemma* dvd_of_mem_factorization
- \+ *lemma* factorization_le_factorization_mul_left
- \+ *lemma* factorization_le_factorization_mul_right
- \+ *lemma* factorization_div
- \- *lemma* factorization_eq_count
- \+/\- *lemma* factorization_zero
- \+/\- *lemma* support_factorization
- \+/\- *lemma* factorization_pow
- \+/\- *lemma* prime.factorization_pow
- \- *lemma* div_factorization_eq_tsub_of_dvd
- \+/\- *lemma* pow_factorization_dvd
- \+ *def* rec_on_prime_pow
- \+ *def* rec_on_pos_prime_coprime
- \+ *def* rec_on_prime_coprime
- \+ *def* rec_on_mul

deleted src/data/nat/mul_ind.lean
- \- *def* rec_on_prime_pow
- \- *def* rec_on_pos_prime_coprime
- \- *def* rec_on_prime_coprime
- \- *def* rec_on_mul

modified src/data/nat/prime.lean
- \+/\- *lemma* prod_factors
- \+/\- *lemma* eq_of_perm_factors
- \+/\- *lemma* mem_factors_iff_dvd
- \+ *lemma* perm_factors_mul
- \+/\- *lemma* mem_factors_mul_of_coprime
- \+/\- *lemma* mem_factors_mul_left
- \+/\- *lemma* mem_factors_mul_right
- \+/\- *lemma* prod_factors
- \+/\- *lemma* eq_of_perm_factors
- \- *lemma* eq_of_count_factors_eq
- \+/\- *lemma* mem_factors_iff_dvd
- \- *lemma* perm_factors_mul_of_pos
- \- *lemma* count_factors_mul_of_pos
- \- *lemma* count_factors_mul_of_coprime
- \- *lemma* factors_count_pow
- \- *lemma* pow_factors_count_dvd
- \+/\- *lemma* mem_factors_mul_of_coprime
- \- *lemma* le_factors_count_mul_left
- \- *lemma* le_factors_count_mul_right
- \+/\- *lemma* mem_factors_mul_left
- \+/\- *lemma* mem_factors_mul_right
- \- *lemma* factors_count_eq_of_coprime_left
- \- *lemma* factors_count_eq_of_coprime_right

modified src/data/pnat/factors.lean

modified src/group_theory/exponent.lean
- \+ *lemma* _root_.nat.prime.exists_order_of_eq_pow_factorization_exponent
- \- *lemma* _root_.nat.prime.exists_order_of_eq_pow_padic_val_nat_exponent

modified src/group_theory/p_group.lean

modified src/group_theory/sylow.lean

modified src/number_theory/arithmetic_function.lean

modified src/number_theory/padics/padic_norm.lean
- \+ *lemma* padic_val_nat_eq_factorization
- \- *lemma* padic_val_nat_eq_factors_count

modified src/ring_theory/int/basic.lean



## [2022-02-11 18:25:43](https://github.com/leanprover-community/mathlib/commit/da76d21)
feat(measure_theory/measure/haar_quotient): Pushforward of Haar measure is Haar ([#11593](https://github.com/leanprover-community/mathlib/pull/11593))
For `G` a topological group with discrete subgroup `Γ`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. When `Γ` is normal (and under other certain suitable conditions), we show that this measure is the Haar measure on the quotient group `G ⧸ Γ`.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* smul_opposite_mul
- \+ *lemma* smul_opposite_image_mul_preimage
- \+ *def* opposite
- \+ *def* opposite_equiv

modified src/measure_theory/group/arithmetic.lean
- \+ *lemma* measurable_mul_op
- \+ *lemma* measurable_mul_unop
- \- *lemma* measurable_op
- \- *lemma* measurable_unop

modified src/measure_theory/group/fundamental_domain.lean
- \+ *lemma* measure_set_eq

created src/measure_theory/measure/haar_quotient.lean
- \+ *lemma* subgroup.smul_invariant_measure
- \+ *lemma* measure_theory.is_fundamental_domain.smul
- \+ *lemma* measure_theory.is_fundamental_domain.smul_invariant_measure_map
- \+ *lemma* measure_theory.is_fundamental_domain.is_mul_left_invariant_map
- \+ *lemma* measure_theory.is_fundamental_domain.map_restrict_quotient



## [2022-02-11 15:45:40](https://github.com/leanprover-community/mathlib/commit/edefc11)
feat(number_theory/number_field/basic) : the ring of integers of a number field is not a field  ([#11956](https://github.com/leanprover-community/mathlib/pull/11956))
#### Estimated changes
modified src/data/int/char_zero.lean
- \+ *lemma* ring_hom.injective_int

modified src/number_theory/number_field.lean
- \+ *lemma* int.not_is_field
- \+ *lemma* not_is_field



## [2022-02-11 13:10:47](https://github.com/leanprover-community/mathlib/commit/1b78b4d)
feat(measure_theory/function/ae_eq_of_integral): remove a few unnecessary `@` ([#11974](https://github.com/leanprover-community/mathlib/pull/11974))
Those `@` were necessary at the time, but `measurable_set.inter` changed and they can now be removed.
#### Estimated changes
modified src/measure_theory/function/ae_eq_of_integral.lean



## [2022-02-11 13:10:46](https://github.com/leanprover-community/mathlib/commit/114752c)
fix(algebra/monoid_algebra/basic): remove an instance that forms a diamond ([#11918](https://github.com/leanprover-community/mathlib/pull/11918))
This turns `monoid_algebra.comap_distrib_mul_action_self` from an instance to a def.
This also adds some tests to prove that this diamond exists.
Note that this diamond is not just non-defeq, it's also just plain not equal.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Schur's.20lemma/near/270990004)
#### Estimated changes
modified src/algebra/monoid_algebra/basic.lean
- \+ *def* comap_distrib_mul_action_self

modified src/data/finsupp/basic.lean

modified test/instance_diamonds.lean



## [2022-02-11 11:23:57](https://github.com/leanprover-community/mathlib/commit/492393b)
feat(model_theory/direct_limit): Direct limits of first-order structures ([#11789](https://github.com/leanprover-community/mathlib/pull/11789))
Constructs the direct limit of a directed system of first-order embeddings
#### Estimated changes
modified src/data/fintype/order.lean
- \+ *lemma* fintype.exists_le
- \+ *lemma* fintype.bdd_above_range
- \+ *theorem* directed.fintype_le

modified src/data/quot.lean
- \+ *lemma* quotient.lift_comp_mk

created src/model_theory/direct_limit.lean
- \+ *lemma* map_self
- \+ *lemma* map_map
- \+ *lemma* unify_sigma_mk_self
- \+ *lemma* comp_unify
- \+ *lemma* equiv_iff
- \+ *lemma* fun_map_unify_equiv
- \+ *lemma* rel_map_unify_equiv
- \+ *lemma* exists_unify_eq
- \+ *lemma* fun_map_equiv_unify
- \+ *lemma* rel_map_equiv_unify
- \+ *lemma* fun_map_quotient_mk_sigma_mk
- \+ *lemma* rel_map_quotient_mk_sigma_mk
- \+ *lemma* exists_quotient_mk_sigma_mk_eq
- \+ *lemma* of_apply
- \+ *lemma* of_f
- \+ *lemma* lift_quotient_mk_sigma_mk
- \+ *lemma* lift_of
- \+ *theorem* exists_of
- \+ *theorem* lift_unique
- \+ *def* unify
- \+ *def* setoid
- \+ *def* direct_limit

modified src/model_theory/quotients.lean
- \+ *lemma* rel_map_quotient_mk



## [2022-02-11 07:37:33](https://github.com/leanprover-community/mathlib/commit/024aef0)
feat(data/pi): provide `pi.mul_single` ([#11849](https://github.com/leanprover-community/mathlib/pull/11849))
the additive version was previously called `pi.single`, to this requires refactoring existing code.
#### Estimated changes
modified src/algebra/group/pi.lean
- \+ *lemma* pi.mul_single_mul
- \+ *lemma* pi.mul_single_inv
- \+ *lemma* pi.single_div
- \+ *lemma* pi.update_eq_div_mul_single
- \- *lemma* pi.single_add
- \- *lemma* pi.single_neg
- \- *lemma* pi.single_sub
- \- *lemma* pi.update_eq_sub_add_single
- \+ *def* one_hom.single
- \+ *def* monoid_hom.single
- \- *def* zero_hom.single
- \- *def* add_monoid_hom.single

modified src/algebra/group/to_additive.lean

modified src/data/pi.lean
- \+ *lemma* mul_single_eq_same
- \+ *lemma* mul_single_eq_of_ne
- \+ *lemma* mul_single_eq_of_ne'
- \+ *lemma* mul_single_one
- \+ *lemma* mul_single_apply
- \+ *lemma* mul_single_comm
- \+ *lemma* apply_mul_single
- \+ *lemma* apply_mul_single₂
- \+ *lemma* mul_single_op
- \+ *lemma* mul_single_op₂
- \+ *lemma* mul_single_injective
- \+ *lemma* mul_single_inj
- \+ *lemma* subsingleton.pi_mul_single_eq
- \- *lemma* single_eq_same
- \- *lemma* single_eq_of_ne
- \- *lemma* single_eq_of_ne'
- \- *lemma* single_zero
- \- *lemma* single_apply
- \- *lemma* single_comm
- \- *lemma* apply_single
- \- *lemma* apply_single₂
- \- *lemma* single_op
- \- *lemma* single_op₂
- \- *lemma* single_injective
- \- *lemma* single_inj
- \- *lemma* subsingleton.pi_single_eq
- \+ *def* mul_single
- \- *def* single



## [2022-02-11 03:15:15](https://github.com/leanprover-community/mathlib/commit/8c60a92)
fix(ring_theory/algebraic): prove a diamond exists and remove the instances ([#11935](https://github.com/leanprover-community/mathlib/pull/11935))
It seems nothing used these instances anyway.
#### Estimated changes
modified src/ring_theory/algebraic.lean
- \+ *def* polynomial.has_scalar_pi

modified test/instance_diamonds.lean



## [2022-02-11 01:36:55](https://github.com/leanprover-community/mathlib/commit/fbfdff7)
chore(data/real/ennreal, topology/instances/ennreal): change name of the order isomorphism for `inv` ([#11959](https://github.com/leanprover-community/mathlib/pull/11959))
On [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/naming.20defs/near/271228611) it was decided that the name should be changed from `ennreal.inv_order_iso` to `order_iso.inv_ennreal` in order to better accord with the rest of the library.
#### Estimated changes
modified src/data/real/ennreal.lean
- \+ *lemma* _root_.order_iso.inv_ennreal_symm_apply
- \- *lemma* inv_order_iso_symm_apply
- \+ *def* _root_.order_iso.inv_ennreal
- \- *def* inv_order_iso

modified src/topology/instances/ennreal.lean



## [2022-02-11 01:36:54](https://github.com/leanprover-community/mathlib/commit/ae14f6a)
chore(algebra/star): generalize star_bit0, add star_inv_of ([#11951](https://github.com/leanprover-community/mathlib/pull/11951))
#### Estimated changes
modified src/algebra/star/basic.lean
- \+/\- *lemma* star_bit0
- \+/\- *lemma* star_bit1
- \+ *lemma* star_inv_of
- \+/\- *lemma* star_bit0
- \+/\- *lemma* star_bit1



## [2022-02-11 01:36:53](https://github.com/leanprover-community/mathlib/commit/0227820)
feat(topology/algebra/group): added (right/left)_coset_(open/closed) ([#11876](https://github.com/leanprover-community/mathlib/pull/11876))
Added lemmas saying that, in a topological group, cosets of an open (resp. closed) set are open (resp. closed).
#### Estimated changes
modified src/topology/algebra/group.lean
- \+ *lemma* is_open.left_coset
- \+ *lemma* is_closed.left_coset
- \+ *lemma* is_open.right_coset
- \+ *lemma* is_closed.right_coset



## [2022-02-11 01:36:52](https://github.com/leanprover-community/mathlib/commit/7351358)
refactor(order/well_founded, set_theory/ordinal_arithmetic): Fix namespace in `self_le_of_strict_mono` ([#11871](https://github.com/leanprover-community/mathlib/pull/11871))
This places `self_le_of_strict_mono` in the `well_founded` namespace. We also rename `is_normal.le_self` to `is_normal.self_le` .
#### Estimated changes
modified src/order/well_founded.lean
- \+ *theorem* self_le_of_strict_mono
- \- *theorem* well_founded.self_le_of_strict_mono

modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* is_normal.self_le
- \- *theorem* is_normal.le_self

modified src/set_theory/principal.lean



## [2022-02-10 23:42:58](https://github.com/leanprover-community/mathlib/commit/4a5728f)
chore(number_theory/cyclotomic/zeta): generalize to primitive roots ([#11941](https://github.com/leanprover-community/mathlib/pull/11941))
This was done as `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ)) = zeta p ℚ ℚ(ζₚ)` is independent of Lean's type theory. Allows far more flexibility with results.
#### Estimated changes
modified src/number_theory/cyclotomic/gal.lean
- \+/\- *lemma* aut_to_pow_injective
- \+/\- *lemma* from_zeta_aut_spec
- \+/\- *lemma* aut_to_pow_injective
- \+/\- *lemma* from_zeta_aut_spec

created src/number_theory/cyclotomic/primitive_roots.lean
- \+ *lemma* zeta_spec
- \+ *lemma* zeta_spec'
- \+ *lemma* zeta_pow
- \+ *lemma* zeta_primitive_root
- \+ *lemma* finrank
- \+ *lemma* norm_eq_one
- \+ *lemma* sub_one_norm_eq_eval_cyclotomic

deleted src/number_theory/cyclotomic/zeta.lean
- \- *lemma* zeta_spec
- \- *lemma* zeta_spec'
- \- *lemma* zeta_pow
- \- *lemma* zeta_primitive_root
- \- *lemma* zeta_minpoly
- \- *lemma* zeta.power_basis_gen_minpoly
- \- *lemma* finrank
- \- *lemma* norm_zeta_eq_one
- \- *lemma* norm_zeta_sub_one_eq_eval_cyclotomic
- \- *def* zeta
- \- *def* zeta.power_basis
- \- *def* zeta.embeddings_equiv_primitive_roots



## [2022-02-10 23:42:56](https://github.com/leanprover-community/mathlib/commit/d487230)
feat(algebra/big_operators): add prod_multiset_count_of_subset ([#11919](https://github.com/leanprover-community/mathlib/pull/11919))
Inspired by [#4259](https://github.com/leanprover-community/mathlib/pull/4259).
Co-Authored-By: Bhavik Mehta <bhavikmehta8@gmail.com>
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_multiset_count_of_subset



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
modified src/algebra/module/basic.lean
- \+ *lemma* two_nsmul_eq_zero
- \+ *lemma* self_eq_neg
- \+ *lemma* neg_eq_self
- \+ *lemma* self_ne_neg
- \+ *lemma* neg_ne_self
- \- *lemma* eq_zero_of_two_nsmul_eq_zero
- \- *lemma* eq_zero_of_eq_neg
- \- *lemma* ne_neg_of_ne_zero

modified src/analysis/normed_space/basic.lean

modified src/measure_theory/integral/bochner.lean



## [2022-02-10 20:43:58](https://github.com/leanprover-community/mathlib/commit/0929387)
feat(group_theory/group_action/defs): add ext attributes ([#11936](https://github.com/leanprover-community/mathlib/pull/11936))
This adds `ext` attributes to `has_scalar`, `mul_action`, `distrib_mul_action`, `mul_distrib_mul_action`, and `module`.
The `ext` and `ext_iff` lemmas were eventually generated by `category_theory/preadditive/schur.lean` anyway - we may as well generate them much earlier.
The generated lemmas are slightly uglier than the `module_ext` we already have, but it doesn't really seem worth the trouble of writing out the "nice" versions when the `ext` tactic cleans up the mess for us anyway.
#### Estimated changes
modified src/algebra/group/defs.lean

modified src/algebra/module/basic.lean
- \+ *lemma* module.ext'
- \- *lemma* module_ext

modified src/category_theory/preadditive/schur.lean

modified src/group_theory/group_action/defs.lean

modified src/number_theory/number_field.lean



## [2022-02-10 20:43:57](https://github.com/leanprover-community/mathlib/commit/007d660)
feat(analysis/inner_product_space/pi_L2): `map_isometry_euclidean_of_orthonormal` ([#11907](https://github.com/leanprover-community/mathlib/pull/11907))
Add a lemma giving the result of `isometry_euclidean_of_orthonormal`
when applied to an orthonormal basis obtained from another orthonormal
basis with `basis.map`.
#### Estimated changes
modified src/analysis/inner_product_space/pi_L2.lean
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
modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* arg_mul_cos_add_sin_mul_I_eq_mul_fract
- \+ *lemma* arg_cos_add_sin_mul_I_eq_mul_fract
- \+ *lemma* arg_mul_cos_add_sin_mul_I_sub
- \+ *lemma* arg_cos_add_sin_mul_I_sub
- \+ *lemma* arg_mul_cos_add_sin_mul_I_coe_angle
- \+ *lemma* arg_cos_add_sin_mul_I_coe_angle
- \+ *lemma* arg_mul_coe_angle
- \+ *lemma* arg_div_coe_angle



## [2022-02-10 20:43:55](https://github.com/leanprover-community/mathlib/commit/1141703)
feat(group_theory/group_action/sub_mul_action): orbit and stabilizer lemmas ([#11899](https://github.com/leanprover-community/mathlib/pull/11899))
Feat: add lemmas for stabilizer and orbit for sub_mul_action
#### Estimated changes
modified src/group_theory/group_action/sub_mul_action.lean
- \+ *lemma* coe_image_orbit
- \+ *lemma* orbit_of_sub_mul
- \+ *lemma* stabilizer_of_sub_mul.submonoid
- \+ *lemma* stabilizer_of_sub_mul



## [2022-02-10 18:46:21](https://github.com/leanprover-community/mathlib/commit/de70722)
chore(algebra/punit_instances): all actions on punit are central ([#11953](https://github.com/leanprover-community/mathlib/pull/11953))
#### Estimated changes
modified src/algebra/punit_instances.lean



## [2022-02-10 18:46:20](https://github.com/leanprover-community/mathlib/commit/779d836)
feat(category_theory): variants of Yoneda are fully faithful ([#11950](https://github.com/leanprover-community/mathlib/pull/11950))
#### Estimated changes
modified src/algebra/category/Module/basic.lean
- \+ *lemma* forget₂_obj
- \+ *lemma* forget₂_obj_Module_of
- \+ *lemma* forget₂_map

modified src/category_theory/linear/yoneda.lean

modified src/category_theory/preadditive/yoneda.lean

modified src/category_theory/whiskering.lean



## [2022-02-10 18:46:19](https://github.com/leanprover-community/mathlib/commit/8012445)
feat(group_theory/subgroup/basic): `subgroup.map_le_map_iff_of_injective` ([#11947](https://github.com/leanprover-community/mathlib/pull/11947))
If `f` is injective, then `H.map f ≤ K.map f ↔ H ≤ K`.
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* map_le_map_iff_of_injective



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
modified src/data/set/basic.lean
- \+ *lemma* insert_none_range_some

modified src/topology/alexandroff.lean

modified src/topology/instances/real.lean
- \+ *lemma* cofinite_eq

modified src/topology/locally_constant/basic.lean

modified src/topology/subset_properties.lean
- \+/\- *lemma* is_compact.image_of_continuous_on
- \+/\- *lemma* is_compact.image
- \+ *lemma* is_compact.finite_of_discrete
- \+ *lemma* is_compact_iff_finite
- \+ *lemma* cocompact_le_cofinite
- \+ *lemma* cocompact_eq_cofinite
- \+ *lemma* _root_.nat.cocompact_eq
- \+ *lemma* tendsto.is_compact_insert_range_of_cocompact
- \+ *lemma* tendsto.is_compact_insert_range_of_cofinite
- \+ *lemma* tendsto.is_compact_insert_range
- \- *lemma* finite_of_is_compact_of_discrete
- \+/\- *lemma* is_compact.image_of_continuous_on
- \+/\- *lemma* is_compact.image



## [2022-02-10 17:14:10](https://github.com/leanprover-community/mathlib/commit/45ab382)
chore(field_theory/galois): make `intermediate_field.fixing_subgroup_equiv` computable ([#11938](https://github.com/leanprover-community/mathlib/pull/11938))
This also golfs and generalizes some results to reuse infrastructure from elsewhere.
In particular, this generalizes:
* `intermediate_field.fixed_field` to `fixed_points.intermediate_field`, where the latter matches the API of `fixed_points.subfield`
* `intermediate_field.fixing_subgroup` to `fixing_subgroup` and `fixing_submonoid`
This removes `open_locale classical` in favor of ensuring the lemmas take in the necessary decidable / fintype arguments.
#### Estimated changes
modified src/field_theory/fixed.lean

modified src/field_theory/galois.lean
- \+/\- *lemma* finrank_fixed_field_eq_card
- \+/\- *lemma* card_fixing_subgroup_eq_finrank
- \+/\- *lemma* finrank_fixed_field_eq_card
- \+/\- *lemma* card_fixing_subgroup_eq_finrank
- \+ *def* fixed_points.intermediate_field
- \+ *def* fixing_submonoid
- \+ *def* fixing_subgroup

modified src/field_theory/krull_topology.lean



## [2022-02-10 13:11:46](https://github.com/leanprover-community/mathlib/commit/a86277a)
feat(category_theory/limits): epi equalizer implies equal ([#11873](https://github.com/leanprover-community/mathlib/pull/11873))
#### Estimated changes
modified src/category_theory/abelian/basic.lean

modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* eq_of_epi_fork_ι
- \+ *lemma* eq_of_epi_equalizer
- \+ *lemma* eq_of_mono_cofork_π
- \+ *lemma* eq_of_mono_coequalizer



## [2022-02-10 13:11:45](https://github.com/leanprover-community/mathlib/commit/20ef909)
feat(data/part): add instances ([#11868](https://github.com/leanprover-community/mathlib/pull/11868))
Add common instances for `part \alpha` to be inherited from `\alpha`. Spun off of [#11046](https://github.com/leanprover-community/mathlib/pull/11046)
#### Estimated changes
modified src/computability/halting.lean

modified src/data/part.lean



## [2022-02-10 13:11:42](https://github.com/leanprover-community/mathlib/commit/3b9dc08)
feat(analysis/complex): add the Cauchy-Goursat theorem for an annulus ([#11864](https://github.com/leanprover-community/mathlib/pull/11864))
#### Estimated changes
modified src/analysis/complex/cauchy_integral.lean
- \+ *lemma* circle_integral_eq_of_differentiable_on_annulus_off_countable

modified src/measure_theory/integral/circle_integral.lean
- \+ *lemma* set.countable.preimage_circle_map
- \+ *lemma* integral_sub_inv_smul_sub_smul

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* _root_.set.countable.ae_not_mem



## [2022-02-10 13:11:41](https://github.com/leanprover-community/mathlib/commit/efa3157)
feat(order/conditionally_complete_lattice): `cInf_le` variant without redundant assumption ([#11863](https://github.com/leanprover-community/mathlib/pull/11863))
We prove `cInf_le'` on a `conditionally_complete_linear_order_bot`. We no longer need the boundedness assumption.
#### Estimated changes
modified src/order/conditionally_complete_lattice.lean
- \+ *theorem* le_cInf_iff''
- \+ *theorem* cInf_le'



## [2022-02-10 13:11:40](https://github.com/leanprover-community/mathlib/commit/66d9cc1)
feat(number_theory/cyclotomic/gal): the Galois group of K(ζₙ) ([#11808](https://github.com/leanprover-community/mathlib/pull/11808))
from flt-regular!
#### Estimated changes
created src/number_theory/cyclotomic/gal.lean
- \+ *lemma* aut_to_pow_injective
- \+ *lemma* from_zeta_aut_spec

modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* aut_to_pow_spec



## [2022-02-10 13:11:39](https://github.com/leanprover-community/mathlib/commit/1373d54)
feat(group_theory/nilpotent): add nilpotent implies normalizer condition ([#11586](https://github.com/leanprover-community/mathlib/pull/11586))
#### Estimated changes
modified src/group_theory/nilpotent.lean
- \+ *lemma* normalizer_condition_of_is_nilpotent

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* map_top_of_surjective



## [2022-02-10 13:11:37](https://github.com/leanprover-community/mathlib/commit/c3f6fce)
feat(algebra/group_power/basic): add lemmas about pow and neg on units ([#11447](https://github.com/leanprover-community/mathlib/pull/11447))
In future we might want to add a typeclass for monoids with a well-behaved negation operator to avoid needing to repeat these lemmas. Such a typeclass would also apply to the `unitary` submonoid too.
#### Estimated changes
modified src/algebra/group/units_hom.lean
- \+ *lemma* coe_pow
- \+ *lemma* coe_zpow

modified src/algebra/group_power/basic.lean
- \+ *lemma* neg_sq
- \+ *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+ *theorem* neg_one_pow_eq_or
- \+ *theorem* neg_pow
- \+ *theorem* neg_pow_bit0
- \+ *theorem* neg_pow_bit1

modified src/algebra/group_power/lemmas.lean
- \- *lemma* units.coe_pow
- \- *lemma* units.coe_zpow

modified src/algebra/ring/basic.lean
- \+ *lemma* neg_mul_eq_neg_mul
- \+ *lemma* neg_mul_eq_mul_neg
- \+ *lemma* mul_neg_one
- \+ *lemma* neg_one_mul
- \+ *lemma* units_neg_right
- \+ *lemma* units_neg_right_iff
- \+ *lemma* units_neg_left
- \+ *lemma* units_neg_left_iff
- \+ *lemma* units_neg_one_right
- \+ *lemma* units_neg_one_left
- \+ *theorem* units_neg_right
- \+ *theorem* units_neg_right_iff
- \+ *theorem* units_neg_left
- \+ *theorem* units_neg_left_iff
- \+ *theorem* units_neg_one_right
- \+ *theorem* units_neg_one_left



## [2022-02-10 13:11:36](https://github.com/leanprover-community/mathlib/commit/c3d8782)
feat(category_theory/bicategory/functor_bicategory): bicategory structure on oplax functors ([#11405](https://github.com/leanprover-community/mathlib/pull/11405))
This PR defines a bicategory structure on the oplax functors between bicategories.
#### Estimated changes
created src/category_theory/bicategory/functor_bicategory.lean
- \+ *def* whisker_left
- \+ *def* whisker_right
- \+ *def* associator
- \+ *def* left_unitor
- \+ *def* right_unitor



## [2022-02-10 10:46:35](https://github.com/leanprover-community/mathlib/commit/da164c6)
feat (category_theory/karoubi_karoubi) : idempotence of karoubi ([#11931](https://github.com/leanprover-community/mathlib/pull/11931))
In this file, we construct the equivalence of categories
`karoubi_karoubi.equivalence C : karoubi C ≌ karoubi (karoubi C)` for any category `C`.
#### Estimated changes
created src/category_theory/idempotents/karoubi_karoubi.lean
- \+ *def* inverse
- \+ *def* unit_iso
- \+ *def* counit_iso
- \+ *def* equivalence



## [2022-02-10 10:46:34](https://github.com/leanprover-community/mathlib/commit/0490977)
feat(algebra/lie/engel): add proof of Engel's theorem ([#11922](https://github.com/leanprover-community/mathlib/pull/11922))
#### Estimated changes
modified docs/references.bib

modified src/algebra/lie/cartan_subalgebra.lean
- \+ *lemma* lie_mem_sup_of_mem_normalizer

created src/algebra/lie/engel.lean
- \+ *lemma* exists_smul_add_of_span_sup_eq_top
- \+ *lemma* lie_top_eq_of_span_sup_eq_top
- \+ *lemma* lcs_le_lcs_of_is_nilpotent_span_sup_eq_top
- \+ *lemma* is_nilpotent_of_is_nilpotent_span_sup_eq_top
- \+ *lemma* lie_algebra.is_engelian_of_subsingleton
- \+ *lemma* function.surjective.is_engelian
- \+ *lemma* lie_equiv.is_engelian_iff
- \+ *lemma* lie_algebra.exists_engelian_lie_subalgebra_of_lt_normalizer
- \+ *lemma* lie_algebra.is_engelian_of_is_noetherian
- \+ *lemma* lie_module.is_nilpotent_iff_forall
- \+ *lemma* lie_algebra.is_nilpotent_iff_forall
- \+ *def* lie_algebra.is_engelian

modified src/algebra/lie/of_associative.lean
- \+ *lemma* lie_subalgebra.to_endomorphism_eq
- \+ *lemma* lie_subalgebra.to_endomorphism_mk
- \+ *lemma* lie_submodule.coe_map_to_endomorphism_le

modified src/algebra/lie/subalgebra.lean
- \+ *lemma* subsingleton_bot

modified src/algebra/module/submodule.lean
- \+ *lemma* injective_subtype

modified src/linear_algebra/basic.lean
- \+ *lemma* sup_span
- \+ *lemma* span_sup



## [2022-02-10 10:46:32](https://github.com/leanprover-community/mathlib/commit/f32fda7)
feat(set_theory/ordinal_arithmetic): More `lsub` and `blsub` lemmas ([#11848](https://github.com/leanprover-community/mathlib/pull/11848))
We prove variants of `sup_typein`, which serve as analogs for `blsub_id`. We also prove `sup_eq_lsub_or_sup_succ_eq_lsub`, which combines `sup_le_lsub` and `lsub_le_sup_succ`.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* bsup_id_limit
- \+ *theorem* bsup_id_succ
- \+ *theorem* sup_eq_lsub_or_sup_succ_eq_lsub
- \+ *theorem* bsup_eq_blsub_or_succ_bsup_eq_blsub
- \+/\- *theorem* blsub_id
- \+ *theorem* lsub_typein
- \+ *theorem* sup_typein_limit
- \+ *theorem* sup_typein_succ
- \- *theorem* bsup_id
- \+/\- *theorem* blsub_id



## [2022-02-10 10:46:31](https://github.com/leanprover-community/mathlib/commit/b7360f9)
feat(group_theory/general_commutator): subgroup.prod commutes with the general_commutator ([#11818](https://github.com/leanprover-community/mathlib/pull/11818))
#### Estimated changes
modified src/group_theory/general_commutator.lean
- \+ *lemma* map_general_commutator
- \+ *lemma* general_commutator_prod_prod



## [2022-02-10 10:46:28](https://github.com/leanprover-community/mathlib/commit/6afaf36)
feat(algebra/order/hom/ring): Ordered semiring/ring homomorphisms ([#11634](https://github.com/leanprover-community/mathlib/pull/11634))
Define `order_ring_hom` with notation `→+*o` along with its hom class.
#### Estimated changes
modified src/algebra/order/hom/monoid.lean
- \+/\- *lemma* coe_monoid_with_zero_hom
- \+/\- *lemma* coe_order_monoid_hom
- \+/\- *lemma* coe_monoid_with_zero_hom
- \+/\- *lemma* coe_order_monoid_hom

created src/algebra/order/hom/ring.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* to_ring_hom_eq_coe
- \+ *lemma* to_order_add_monoid_hom_eq_coe
- \+ *lemma* to_order_monoid_with_zero_hom_eq_coe
- \+ *lemma* coe_coe_ring_hom
- \+ *lemma* coe_coe_order_add_monoid_hom
- \+ *lemma* coe_coe_order_monoid_with_zero_hom
- \+ *lemma* coe_ring_hom_apply
- \+ *lemma* coe_order_add_monoid_hom_apply
- \+ *lemma* coe_order_monoid_with_zero_hom_apply
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_ring_hom_id
- \+ *lemma* coe_order_add_monoid_hom_id
- \+ *lemma* coe_order_monoid_with_zero_hom_id
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *def* to_order_add_monoid_hom
- \+ *def* to_order_monoid_with_zero_hom

modified src/algebra/ring/basic.lean
- \+ *def* copy



## [2022-02-10 09:27:23](https://github.com/leanprover-community/mathlib/commit/8f5fd26)
feat(data/nat/factorization): bijection between positive nats and finsupps over primes ([#11440](https://github.com/leanprover-community/mathlib/pull/11440))
Proof that for any finsupp `f : ℕ →₀ ℕ` whose support is in the primes, `f = (f.prod pow).factorization`, and hence that the positive natural numbers are bijective with finsupps `ℕ →₀ ℕ` with support in the primes.
#### Estimated changes
modified src/algebra/big_operators/finsupp.lean
- \+ *lemma* prod_pow_pos_of_zero_not_mem_support

modified src/data/nat/factorization.lean
- \+ *lemma* prod_pow_factorization_eq_self
- \+ *lemma* eq_factorization_iff
- \+ *lemma* factorization_equiv_apply
- \+ *lemma* factorization_equiv_inv_apply
- \+ *def* factorization_equiv



## [2022-02-10 09:27:22](https://github.com/leanprover-community/mathlib/commit/0aa0bc8)
feat(set_theory/ordinal_arithmetic): The derivative of addition ([#11270](https://github.com/leanprover-community/mathlib/pull/11270))
We prove that the derivative of `(+) a` evaluated at `b` is given by `a * ω + b`.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* is_normal.le_iff_eq
- \+ *theorem* mul_one_add
- \+/\- *theorem* family_of_bfamily_enum
- \+/\- *theorem* sup_nat_cast
- \+/\- *theorem* sup_add_nat
- \+/\- *theorem* sup_mul_nat
- \+/\- *theorem* is_normal.nfp_le_fp
- \+/\- *theorem* is_normal.nfp_fp
- \+/\- *theorem* is_normal.le_nfp
- \+/\- *theorem* nfp_eq_self
- \+/\- *theorem* is_normal.deriv_fp
- \+ *theorem* is_normal.le_iff_deriv
- \+ *theorem* is_normal.apply_eq_self_iff_deriv
- \+ *theorem* nfp_add_zero
- \+ *theorem* nfp_add_eq_mul_omega
- \+ *theorem* add_eq_right_iff_mul_omega_le
- \+ *theorem* add_le_right_iff_mul_omega_le
- \+ *theorem* deriv_add_eq_mul_omega_add
- \+/\- *theorem* family_of_bfamily_enum
- \+/\- *theorem* sup_nat_cast
- \+/\- *theorem* sup_add_nat
- \+/\- *theorem* sup_mul_nat
- \- *theorem* is_normal.nfp_le
- \+/\- *theorem* is_normal.nfp_le_fp
- \+/\- *theorem* is_normal.nfp_fp
- \+/\- *theorem* is_normal.le_nfp
- \+/\- *theorem* nfp_eq_self
- \+/\- *theorem* is_normal.deriv_fp
- \- *theorem* is_normal.fp_iff_deriv'
- \- *theorem* is_normal.fp_iff_deriv
- \+/\- *def* family_of_bfamily
- \+/\- *def* family_of_bfamily



## [2022-02-10 08:34:06](https://github.com/leanprover-community/mathlib/commit/e60ca6b)
feat(data/real/ennreal): `inv` is an `order_iso` to the order dual and lemmas for `supr, infi` ([#11869](https://github.com/leanprover-community/mathlib/pull/11869))
Establishes that `inv` is an order isomorphism to the order dual. We then provide some convenience lemmas which guarantee that `inv` switches `supr` and `infi` and hence also switches `limsup` and `liminf`.
#### Estimated changes
modified src/data/real/ennreal.lean
- \+ *lemma* inv_order_iso_symm_apply
- \+ *def* inv_order_iso

modified src/topology/instances/ennreal.lean
- \+ *lemma* inv_map_infi
- \+ *lemma* inv_map_supr
- \+ *lemma* inv_limsup
- \+ *lemma* inv_liminf



## [2022-02-10 08:34:05](https://github.com/leanprover-community/mathlib/commit/b7e72ea)
feat(measure_theory/probability_mass_function): Measure calculations for additional pmf constructions ([#11858](https://github.com/leanprover-community/mathlib/pull/11858))
This PR adds calculations of the measures of sets under various `pmf` constructions.
#### Estimated changes
modified src/measure_theory/probability_mass_function/constructions.lean
- \+ *lemma* to_outer_measure_map_apply
- \+ *lemma* to_measure_map_apply
- \+ *lemma* to_outer_measure_of_finset_apply
- \+ *lemma* to_measure_of_finset_apply
- \+ *lemma* to_outer_measure_of_fintype_apply
- \+ *lemma* to_measure_of_fintype_apply
- \+ *lemma* to_outer_measure_of_multiset_apply
- \+ *lemma* to_measure_of_multiset_apply
- \+ *lemma* to_outer_measure_uniform_of_finset_apply
- \+ *lemma* to_measure_uniform_of_finset_apply
- \+/\- *lemma* support_uniform_of_fintype
- \+ *lemma* mem_support_uniform_of_fintype
- \+ *lemma* to_outer_measure_uniform_of_fintype_apply
- \+ *lemma* to_measure_uniform_of_fintype_apply
- \+/\- *lemma* support_uniform_of_fintype
- \- *lemma* mem_support_uniform_of_fintype_iff

modified src/measure_theory/probability_mass_function/monad.lean
- \+/\- *lemma* to_outer_measure_pure_apply
- \+/\- *lemma* to_measure_pure_apply
- \+/\- *lemma* to_outer_measure_bind_apply
- \+/\- *lemma* to_measure_bind_apply
- \+/\- *lemma* to_outer_measure_bind_on_support_apply
- \+/\- *lemma* to_measure_bind_on_support_apply
- \+/\- *lemma* to_outer_measure_pure_apply
- \+/\- *lemma* to_measure_pure_apply
- \+/\- *lemma* to_outer_measure_bind_apply
- \+/\- *lemma* to_measure_bind_apply
- \+/\- *lemma* to_outer_measure_bind_on_support_apply
- \+/\- *lemma* to_measure_bind_on_support_apply



## [2022-02-10 08:04:04](https://github.com/leanprover-community/mathlib/commit/e9a1893)
chore(tactic/default): import `linear_combination` ([#11942](https://github.com/leanprover-community/mathlib/pull/11942))
#### Estimated changes
modified src/tactic/default.lean



## [2022-02-10 03:40:32](https://github.com/leanprover-community/mathlib/commit/ea0e458)
refactor(topology/algebra/mul_action2): rename type classes ([#11940](https://github.com/leanprover-community/mathlib/pull/11940))
Rename `has_continuous_smul₂` and `has_continuous_vadd₂` to
`has_continuous_const_smul` and `has_continuous_const_vadd`,
respectively.
#### Estimated changes
modified src/topology/algebra/group.lean

modified src/topology/algebra/mul_action.lean

modified src/topology/algebra/mul_action2.lean
- \+/\- *lemma* is_open_map_quotient_mk_mul
- \+/\- *lemma* is_open_map_quotient_mk_mul



## [2022-02-09 23:10:35](https://github.com/leanprover-community/mathlib/commit/4e8d8fa)
feat(order/hom/bounded): Bounded order homomorphisms ([#11806](https://github.com/leanprover-community/mathlib/pull/11806))
Define `bounded_order_hom` in `order.hom.bounded` and move `top_hom`, `bot_hom` there.
#### Estimated changes
modified src/order/hom/basic.lean

created src/order/hom/bounded.lean
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_top
- \+ *lemma* top_apply
- \+ *lemma* coe_inf
- \+ *lemma* inf_apply
- \+ *lemma* coe_sup
- \+ *lemma* sup_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *lemma* coe_bot
- \+ *lemma* bot_apply
- \+ *lemma* coe_inf
- \+ *lemma* inf_apply
- \+ *lemma* coe_sup
- \+ *lemma* sup_apply
- \+ *lemma* to_fun_eq_coe
- \+ *lemma* ext
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* coe_comp
- \+ *lemma* comp_apply
- \+ *lemma* coe_comp_order_hom
- \+ *lemma* coe_comp_top_hom
- \+ *lemma* coe_comp_bot_hom
- \+ *lemma* comp_assoc
- \+ *lemma* comp_id
- \+ *lemma* id_comp
- \+ *lemma* cancel_right
- \+ *lemma* cancel_left
- \+ *def* comp
- \+ *def* comp
- \+ *def* to_top_hom
- \+ *def* to_bot_hom
- \+ *def* comp

modified src/order/hom/lattice.lean
- \+/\- *lemma* cancel_right
- \+/\- *lemma* cancel_left
- \+/\- *lemma* cancel_right
- \+/\- *lemma* cancel_left
- \+/\- *lemma* cancel_right
- \+/\- *lemma* cancel_left
- \- *lemma* to_fun_eq_coe
- \- *lemma* ext
- \- *lemma* coe_id
- \- *lemma* id_apply
- \- *lemma* coe_comp
- \- *lemma* comp_apply
- \- *lemma* comp_assoc
- \- *lemma* comp_id
- \- *lemma* id_comp
- \+/\- *lemma* cancel_right
- \+/\- *lemma* cancel_left
- \- *lemma* coe_top
- \- *lemma* top_apply
- \- *lemma* coe_inf
- \- *lemma* inf_apply
- \- *lemma* coe_sup
- \- *lemma* sup_apply
- \- *lemma* to_fun_eq_coe
- \- *lemma* ext
- \- *lemma* coe_id
- \- *lemma* id_apply
- \- *lemma* coe_comp
- \- *lemma* comp_apply
- \- *lemma* comp_assoc
- \- *lemma* comp_id
- \- *lemma* id_comp
- \+/\- *lemma* cancel_right
- \+/\- *lemma* cancel_left
- \- *lemma* coe_bot
- \- *lemma* bot_apply
- \- *lemma* coe_inf
- \- *lemma* inf_apply
- \- *lemma* coe_sup
- \- *lemma* sup_apply
- \+/\- *lemma* cancel_right
- \+/\- *lemma* cancel_left
- \+/\- *lemma* cancel_right
- \+/\- *lemma* cancel_left
- \+/\- *lemma* cancel_right
- \+/\- *lemma* cancel_left
- \+ *def* to_bounded_order_hom
- \- *def* comp
- \- *def* comp
- \- *def* to_top_hom
- \- *def* to_bot_hom



## [2022-02-09 21:35:24](https://github.com/leanprover-community/mathlib/commit/4691159)
doc(algebra/group/hom_instances): Fix spellings ([#11943](https://github.com/leanprover-community/mathlib/pull/11943))
Fixes spelling mistakes introduced by [#11843](https://github.com/leanprover-community/mathlib/pull/11843)
#### Estimated changes
modified src/algebra/group/hom_instances.lean



## [2022-02-09 20:38:41](https://github.com/leanprover-community/mathlib/commit/352e064)
feat(topology/uniform_space/cauchy): add a few lemmas ([#11912](https://github.com/leanprover-community/mathlib/pull/11912))
#### Estimated changes
modified src/topology/uniform_space/cauchy.lean
- \+ *lemma* cauchy.ultrafilter_of
- \+ *lemma* is_complete_iff_cluster_pt
- \+ *lemma* is_complete_iff_ultrafilter
- \+ *lemma* is_complete_iff_ultrafilter'
- \+ *lemma* complete_space_iff_ultrafilter
- \- *lemma* is_compact.is_complete



## [2022-02-09 18:57:12](https://github.com/leanprover-community/mathlib/commit/2b9aca7)
feat(topology): a few more results about compact sets ([#11905](https://github.com/leanprover-community/mathlib/pull/11905))
* Also a few lemmas about sets and `mul_support`.
#### Estimated changes
modified src/algebra/support.lean
- \+ *lemma* mul_support_disjoint_iff
- \+ *lemma* disjoint_mul_support_iff

modified src/data/set/basic.lean
- \+ *lemma* not_mem_compl_iff
- \+ *lemma* compl_ne_univ

modified src/topology/algebra/group.lean
- \+ *lemma* is_compact.inv

modified src/topology/algebra/monoid.lean
- \+ *lemma* is_compact.mul

modified src/topology/separation.lean
- \+ *lemma* exists_compact_superset_iff



## [2022-02-09 18:57:10](https://github.com/leanprover-community/mathlib/commit/b8fb8e5)
feat(set_theory/ordinal_arithmetic): `le_one_iff` ([#11847](https://github.com/leanprover-community/mathlib/pull/11847))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* le_one_iff



## [2022-02-09 18:57:09](https://github.com/leanprover-community/mathlib/commit/2726e23)
feat(algebra.group.hom_instances): Define left and right multiplication operators ([#11843](https://github.com/leanprover-community/mathlib/pull/11843))
Defines left and right multiplication operators on non unital, non associative semirings.
Suggested by @ocfnash for [#11073](https://github.com/leanprover-community/mathlib/pull/11073)
#### Estimated changes
modified src/algebra/group/hom_instances.lean
- \+ *def* add_monoid.End.mul_left
- \+ *def* add_monoid.End.mul_right



## [2022-02-09 17:14:15](https://github.com/leanprover-community/mathlib/commit/5008de8)
feat(order): some properties about monotone predicates ([#11904](https://github.com/leanprover-community/mathlib/pull/11904))
* We prove that some predicates are monotone/antitone w.r.t. some order. The proofs are all trivial.
* We prove 2 `iff` statements depending on the hypothesis that a certain predicate is (anti)mono: `exists_ge_and_iff_exists` and `filter.exists_mem_and_iff`)
* The former is used to prove `bdd_above_iff_exists_ge`, the latter will be used in a later PR.
#### Estimated changes
modified src/order/bounded_order.lean
- \+ *lemma* monotone_le
- \+ *lemma* monotone_lt
- \+ *lemma* antitone_le
- \+ *lemma* antitone_lt
- \+ *lemma* monotone.forall
- \+ *lemma* antitone.forall
- \+ *lemma* monotone.ball
- \+ *lemma* antitone.ball
- \+ *lemma* exists_ge_and_iff_exists
- \+ *lemma* exists_le_and_iff_exists

modified src/order/bounds.lean
- \+ *lemma* bdd_above_def
- \+ *lemma* bdd_below_def
- \+ *lemma* bdd_above_iff_exists_ge
- \+ *lemma* bdd_below_iff_exists_le
- \+ *lemma* bdd_above.exists_ge
- \+ *lemma* bdd_below.exists_le

modified src/order/filter/basic.lean
- \+ *lemma* exists_mem_and_iff

modified src/topology/continuous_on.lean
- \+ *lemma* antitone_continuous_on



## [2022-02-09 17:14:14](https://github.com/leanprover-community/mathlib/commit/d3cdcd8)
feat(order/filter/basic): add lemma `le_prod_map_fst_snd` ([#11901](https://github.com/leanprover-community/mathlib/pull/11901))
A lemma relating filters on products and the filter-product of the projections. This lemma is particularly useful when proving the continuity of a function on a product space using filters.
Discussion: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Some.20missing.20prod.20stuff
#### Estimated changes
modified src/order/filter/basic.lean
- \+ *lemma* le_prod_map_fst_snd



## [2022-02-09 17:14:12](https://github.com/leanprover-community/mathlib/commit/9648ce2)
chore(data/pi): add pi.prod and use elsewhere ([#11877](https://github.com/leanprover-community/mathlib/pull/11877))
`pi.prod` is the function that underlies `add_monoid_hom.prod`, `linear_map.prod`, etc.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Some.20missing.20prod.20stuff/near/270851797)
#### Estimated changes
modified archive/sensitivity.lean

modified src/algebra/big_operators/basic.lean
- \+ *lemma* monoid_hom.coe_finset_prod
- \- *lemma* monoid_hom.coe_prod

modified src/algebra/direct_sum/ring.lean

modified src/algebra/group/prod.lean
- \+ *lemma* coe_prod

modified src/algebra/triv_sq_zero_ext.lean

modified src/data/dfinsupp/basic.lean

modified src/data/finsupp/basic.lean

modified src/data/pi.lean
- \+ *lemma* prod_fst_snd
- \+ *lemma* prod_snd_fst

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/prod.lean
- \+ *lemma* coe_prod

modified src/topology/algebra/group.lean



## [2022-02-09 15:50:47](https://github.com/leanprover-community/mathlib/commit/ca2450f)
feat(order/atoms): finite orders are (co)atomic ([#11930](https://github.com/leanprover-community/mathlib/pull/11930))
#### Estimated changes
modified src/order/atoms.lean

modified src/order/minimal.lean



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
modified src/algebra/tropical/basic.lean



## [2022-02-09 11:36:35](https://github.com/leanprover-community/mathlib/commit/fea68aa)
chore(data/fintype/basic): documenting elaboration bug ([#11247](https://github.com/leanprover-community/mathlib/pull/11247))
Simplifying an expression and documenting an elaboration bug that it was avoiding.
#### Estimated changes
modified src/data/fintype/basic.lean
- \+/\- *lemma* set.to_finset_univ
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
modified src/algebra/field/basic.lean

modified src/algebra/geom_sum.lean

modified src/algebra/group_power/basic.lean

modified src/algebra/order/field.lean

modified src/algebra/order/ring.lean

modified src/algebra/quaternion.lean

modified src/algebra/quaternion_basis.lean

modified src/algebra/ring/basic.lean
- \+ *lemma* neg_mul
- \+ *lemma* mul_neg
- \- *lemma* neg_mul_eq_neg_mul_symm
- \- *lemma* mul_neg_eq_neg_mul_symm

modified src/algebra/star/chsh.lean

modified src/algebraic_geometry/structure_sheaf.lean

modified src/algebraic_topology/alternating_face_map_complex.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/lhopital.lean

modified src/analysis/complex/polynomial.lean

modified src/analysis/convex/cone.lean

modified src/analysis/inner_product_space/basic.lean

modified src/analysis/normed_space/extend.lean

modified src/analysis/normed_space/hahn_banach.lean

modified src/analysis/normed_space/units.lean

modified src/analysis/special_functions/complex/log.lean

modified src/analysis/special_functions/integrals.lean

modified src/data/complex/basic.lean

modified src/data/complex/exponential.lean

modified src/data/complex/is_R_or_C.lean

modified src/data/int/basic.lean

modified src/data/int/gcd.lean

modified src/data/int/modeq.lean

modified src/data/matrix/basic.lean
- \- *theorem* neg_mul
- \- *theorem* mul_neg

modified src/data/polynomial/field_division.lean

modified src/data/rat/basic.lean

modified src/field_theory/ratfunc.lean

modified src/geometry/euclidean/triangle.lean

modified src/group_theory/free_abelian_group.lean

modified src/group_theory/specific_groups/quaternion.lean

modified src/linear_algebra/adic_completion.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/matrix/determinant.lean

modified src/linear_algebra/orientation.lean

modified src/linear_algebra/quadratic_form/basic.lean

modified src/measure_theory/measure/lebesgue.lean

modified src/number_theory/bernoulli.lean

modified src/number_theory/modular.lean

modified src/number_theory/pell.lean

modified src/number_theory/pythagorean_triples.lean

modified src/number_theory/quadratic_reciprocity.lean

modified src/number_theory/zsqrtd/basic.lean

modified src/ring_theory/coprime/basic.lean

modified src/ring_theory/henselian.lean

modified src/ring_theory/int/basic.lean

modified src/ring_theory/integral_closure.lean

modified src/ring_theory/jacobson_ideal.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/polynomial/cyclotomic/basic.lean

modified src/ring_theory/power_series/basic.lean

modified src/tactic/noncomm_ring.lean

modified src/tactic/omega/int/preterm.lean

modified src/tactic/ring.lean

modified src/topology/continuous_function/polynomial.lean

modified test/matrix.lean



## [2022-02-09 08:51:48](https://github.com/leanprover-community/mathlib/commit/4e17e08)
feat(data/complex/basic): re-im set product ([#11770](https://github.com/leanprover-community/mathlib/pull/11770))
`set.re_im_prod s t` (notation: `s ×ℂ t`) is the product of a set on the real axis and a set on the
imaginary axis of the complex plane.
#### Estimated changes
modified src/analysis/complex/cauchy_integral.lean

modified src/analysis/complex/re_im_topology.lean
- \+ *lemma* closure_re_prod_im
- \+ *lemma* interior_re_prod_im
- \+ *lemma* frontier_re_prod_im
- \+/\- *lemma* is_open.re_prod_im
- \- *lemma* closure_preimage_re_inter_preimage_im
- \- *lemma* interior_preimage_re_inter_preimage_im
- \- *lemma* frontier_preimage_re_inter_preimage_im
- \+/\- *lemma* is_open.re_prod_im

modified src/data/complex/basic.lean
- \+ *def* _root_.set.re_prod_im



## [2022-02-09 07:16:44](https://github.com/leanprover-community/mathlib/commit/78c3975)
feat(category_theory/pseudoabelian/basic): basic facts and contructions about pseudoabelian categories ([#11817](https://github.com/leanprover-community/mathlib/pull/11817))
#### Estimated changes
created src/category_theory/idempotents/basic.lean
- \+ *lemma* is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent
- \+ *lemma* idempotence_of_id_sub_idempotent
- \+ *lemma* is_idempotent_complete_iff_idempotents_have_kernels
- \+ *lemma* split_imp_of_iso
- \+ *lemma* split_iff_of_iso
- \+ *lemma* equivalence.is_idempotent_complete
- \+ *lemma* is_idempotent_complete_iff_of_equivalence
- \+ *lemma* is_idempotent_complete_of_is_idempotent_complete_opposite
- \+ *lemma* is_idempotent_complete_iff_opposite

created src/category_theory/idempotents/karoubi.lean
- \+ *lemma* ext
- \+ *lemma* hom_ext
- \+ *lemma* p_comp
- \+ *lemma* comp_p
- \+ *lemma* p_comm
- \+ *lemma* comp_proof
- \+ *lemma* comp
- \+ *lemma* id_eq
- \+ *lemma* coe_X
- \+ *lemma* coe_p
- \+ *lemma* eq_to_hom_f
- \+ *lemma* hom_eq_zero_iff
- \+ *lemma* sum_hom
- \+ *lemma* decomp_id
- \+ *lemma* decomp_p
- \+ *lemma* decomp_id_i_to_karoubi
- \+ *lemma* decomp_id_p_to_karoubi
- \+ *lemma* decomp_id_i_naturality
- \+ *lemma* decomp_id_p_naturality
- \+ *def* to_karoubi
- \+ *def* inclusion_hom
- \+ *def* to_karoubi_is_equivalence
- \+ *def* decomp_id_i
- \+ *def* decomp_id_p

modified src/category_theory/preadditive/default.lean
- \+ *lemma* has_kernel_of_has_equalizer



## [2022-02-08 22:14:40](https://github.com/leanprover-community/mathlib/commit/56db7ed)
feat(analysis/normed_space/basic): add lemmas `nnnorm_mul_le` and `nnnorm_pow_succ_le` ([#11915](https://github.com/leanprover-community/mathlib/pull/11915))
Adds two convenience lemmas for `nnnorm`, submultiplicativity of `nnnorm` for semi-normed rings and the corresponding extension to powers. We only allow successors so as not to incur the `norm_one_class` type class constraint.
#### Estimated changes
modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnnorm_mul_le
- \+ *lemma* nnnorm_pow_le'
- \+ *lemma* nnnorm_pow_le
- \+/\- *lemma* norm_pow_le'
- \+/\- *lemma* norm_pow_le
- \+/\- *lemma* norm_pow_le'
- \+/\- *lemma* norm_pow_le



## [2022-02-08 21:07:37](https://github.com/leanprover-community/mathlib/commit/a3d6b43)
feat(topology/algebra/uniform_group): `cauchy_seq.const_mul` and friends ([#11917](https://github.com/leanprover-community/mathlib/pull/11917))
A Cauchy sequence multiplied by a constant (including `-1`) remains a Cauchy sequence.
#### Estimated changes
modified src/topology/algebra/uniform_group.lean
- \+ *lemma* cauchy_seq.mul_const
- \+ *lemma* cauchy_seq.const_mul
- \+ *lemma* cauchy_seq.inv

modified src/topology/uniform_space/cauchy.lean
- \+/\- *lemma* cauchy_seq_const
- \+/\- *lemma* cauchy_seq_const



## [2022-02-08 19:01:57](https://github.com/leanprover-community/mathlib/commit/4545e31)
feat(model_theory/substructures): More operations on substructures ([#11906](https://github.com/leanprover-community/mathlib/pull/11906))
Defines the substructure `first_order.language.hom.range`.
Defines the homomorphisms `first_order.language.hom.dom_restrict` and `first_order.language.hom.cod_restrict`, and the embeddings `first_order.language.embedding.dom_restrict`, `first_order.language.embedding.cod_restrict` which restrict the domain or codomain of a first-order hom or embedding to a substructure.
Defines the embedding `first_order.language.substructure.inclusion` between nested substructures.
#### Estimated changes
modified src/model_theory/basic.lean
- \+ *lemma* comp_to_hom

modified src/model_theory/substructures.lean
- \+ *lemma* map_closure
- \+ *lemma* closure_image
- \+ *lemma* comp_cod_restrict
- \+ *lemma* subtype_comp_cod_restrict
- \+ *lemma* range_eq_map
- \+ *lemma* range_le_iff_comap
- \+ *lemma* map_le_range
- \+ *lemma* dom_restrict_apply
- \+ *lemma* comp_cod_restrict
- \+ *lemma* subtype_comp_cod_restrict
- \+ *lemma* substructure_equiv_map_apply
- \+ *lemma* equiv_range_apply
- \+ *lemma* to_hom_range
- \+ *lemma* coe_inclusion
- \+ *lemma* range_subtype
- \+ *theorem* range_coe
- \+ *theorem* mem_range
- \+ *theorem* mem_range_self
- \+ *theorem* range_id
- \+ *theorem* range_comp
- \+ *theorem* range_comp_le_range
- \+ *theorem* range_eq_top
- \+ *theorem* cod_restrict_apply
- \+ *def* dom_restrict
- \+ *def* cod_restrict
- \+ *def* range
- \+ *def* dom_restrict
- \+ *def* cod_restrict
- \+ *def* inclusion



## [2022-02-08 17:19:13](https://github.com/leanprover-community/mathlib/commit/1ae8304)
chore(*): update to lean 3.39.1c ([#11926](https://github.com/leanprover-community/mathlib/pull/11926))
#### Estimated changes
modified leanpkg.toml



## [2022-02-08 13:50:04](https://github.com/leanprover-community/mathlib/commit/b1269b0)
chore(algebra/order/ring): add a few aliases ([#11911](https://github.com/leanprover-community/mathlib/pull/11911))
Add aliases `one_pos`, `two_pos`, `three_pos`, and `four_pos`.
We used to have (some of) these lemmas. They were removed during one of cleanups but it doesn't hurt to have aliases.
#### Estimated changes
modified src/algebra/order/ring.lean

modified src/data/list/basic.lean



## [2022-02-08 12:43:42](https://github.com/leanprover-community/mathlib/commit/85d9f21)
feat(*): localized `R[X]` notation for `polynomial R` ([#11895](https://github.com/leanprover-community/mathlib/pull/11895))
I did not change `polynomial (complex_term_here taking args)` in many places because I thought it would be more confusing. Also, in some files that prove things about polynomials incidentally, I also did not include the notation and change the files.
#### Estimated changes
modified archive/100-theorems-list/16_abel_ruffini.lean

modified src/algebra/algebra/spectrum.lean
- \+/\- *lemma* exists_mem_of_not_is_unit_aeval_prod
- \+/\- *lemma* exists_mem_of_not_is_unit_aeval_prod
- \+/\- *theorem* subset_polynomial_aeval
- \+/\- *theorem* map_polynomial_aeval_of_degree_pos
- \+/\- *theorem* map_polynomial_aeval_of_nonempty
- \+/\- *theorem* subset_polynomial_aeval
- \+/\- *theorem* map_polynomial_aeval_of_degree_pos
- \+/\- *theorem* map_polynomial_aeval_of_nonempty

modified src/algebra/cubic_discriminant.lean
- \+/\- *def* to_poly
- \+/\- *def* equiv
- \+/\- *def* to_poly
- \+/\- *def* equiv

modified src/algebra/linear_recurrence.lean
- \+/\- *def* char_poly
- \+/\- *def* char_poly

modified src/algebra/polynomial/big_operators.lean
- \+/\- *lemma* nat_degree_list_sum_le
- \+/\- *lemma* nat_degree_multiset_sum_le
- \+/\- *lemma* nat_degree_sum_le
- \+/\- *lemma* degree_list_sum_le
- \+/\- *lemma* nat_degree_list_prod_le
- \+/\- *lemma* degree_list_prod_le
- \+/\- *lemma* coeff_list_prod_of_nat_degree_le
- \+/\- *lemma* coeff_prod_of_nat_degree_le
- \+/\- *lemma* nat_degree_multiset_prod
- \+/\- *lemma* nat_degree_list_sum_le
- \+/\- *lemma* nat_degree_multiset_sum_le
- \+/\- *lemma* nat_degree_sum_le
- \+/\- *lemma* degree_list_sum_le
- \+/\- *lemma* nat_degree_list_prod_le
- \+/\- *lemma* degree_list_prod_le
- \+/\- *lemma* coeff_list_prod_of_nat_degree_le
- \+/\- *lemma* coeff_prod_of_nat_degree_le
- \+/\- *lemma* nat_degree_multiset_prod

modified src/algebra/polynomial/group_ring_action.lean
- \+/\- *lemma* smul_X
- \+/\- *lemma* smul_X
- \+/\- *theorem* smul_eval_smul
- \+/\- *theorem* eval_smul'
- \+/\- *theorem* smul_eval
- \+/\- *theorem* smul_eval_smul
- \+/\- *theorem* eval_smul'
- \+/\- *theorem* smul_eval

modified src/algebraic_geometry/prime_spectrum/is_open_comap_C.lean
- \+/\- *lemma* comap_C_mem_image_of_Df
- \+/\- *lemma* comap_C_mem_image_of_Df

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/local_extr.lean
- \+/\- *lemma* card_root_set_le_derivative
- \+/\- *lemma* card_root_set_le_derivative

modified src/analysis/special_functions/polynomials.lean

modified src/data/mv_polynomial/equiv.lean
- \+/\- *def* punit_alg_equiv
- \+/\- *def* option_equiv_right
- \+/\- *def* punit_alg_equiv
- \+/\- *def* option_equiv_right

modified src/data/polynomial/algebra_map.lean
- \+/\- *lemma* eval₂_int_cast_ring_hom_X
- \+/\- *lemma* adjoin_X
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* aeval_zero
- \+/\- *lemma* aeval_X
- \+/\- *lemma* aeval_X_pow
- \+/\- *lemma* aeval_one
- \+/\- *lemma* aeval_nat_cast
- \+/\- *lemma* aeval_algebra_map_apply
- \+/\- *lemma* aeval_fn_apply
- \+/\- *lemma* coeff_zero_eq_aeval_zero
- \+/\- *lemma* coeff_zero_eq_aeval_zero'
- \+/\- *lemma* aeval_eq_sum_range
- \+/\- *lemma* aeval_eq_sum_range'
- \+/\- *lemma* aeval_sum
- \+/\- *lemma* is_root_of_aeval_algebra_map_eq_zero
- \+/\- *lemma* aeval_tower_comp_C
- \+/\- *lemma* dvd_term_of_dvd_eval_of_dvd_terms
- \+/\- *lemma* dvd_term_of_is_root_of_dvd_terms
- \+/\- *lemma* eval_mul_X_sub_C
- \+/\- *lemma* eval₂_int_cast_ring_hom_X
- \+/\- *lemma* adjoin_X
- \+/\- *lemma* alg_hom_ext
- \+/\- *lemma* aeval_zero
- \+/\- *lemma* aeval_X
- \+/\- *lemma* aeval_X_pow
- \+/\- *lemma* aeval_one
- \+/\- *lemma* aeval_nat_cast
- \+/\- *lemma* aeval_algebra_map_apply
- \+/\- *lemma* aeval_fn_apply
- \+/\- *lemma* coeff_zero_eq_aeval_zero
- \+/\- *lemma* coeff_zero_eq_aeval_zero'
- \+/\- *lemma* aeval_eq_sum_range
- \+/\- *lemma* aeval_eq_sum_range'
- \+/\- *lemma* aeval_sum
- \+/\- *lemma* is_root_of_aeval_algebra_map_eq_zero
- \+/\- *lemma* aeval_tower_comp_C
- \+/\- *lemma* dvd_term_of_dvd_eval_of_dvd_terms
- \+/\- *lemma* dvd_term_of_is_root_of_dvd_terms
- \+/\- *lemma* eval_mul_X_sub_C
- \+/\- *theorem* aeval_def
- \+/\- *theorem* aeval_X_left
- \+/\- *theorem* eval_unique
- \+/\- *theorem* aeval_alg_hom_apply
- \+/\- *theorem* aeval_alg_equiv_apply
- \+/\- *theorem* aeval_def
- \+/\- *theorem* aeval_X_left
- \+/\- *theorem* eval_unique
- \+/\- *theorem* aeval_alg_hom_apply
- \+/\- *theorem* aeval_alg_equiv_apply
- \+/\- *def* to_finsupp_iso_alg
- \+/\- *def* aeval
- \+/\- *def* aeval_tower
- \+/\- *def* to_finsupp_iso_alg
- \+/\- *def* aeval
- \+/\- *def* aeval_tower

modified src/data/polynomial/basic.lean
- \+/\- *lemma* forall_iff_forall_finsupp
- \+/\- *lemma* exists_iff_exists_finsupp
- \+/\- *lemma* zero_to_finsupp
- \+/\- *lemma* one_to_finsupp
- \+/\- *lemma* add_to_finsupp
- \+/\- *lemma* neg_to_finsupp
- \+/\- *lemma* mul_to_finsupp
- \+/\- *lemma* support_zero
- \+/\- *lemma* C_eq_nat_cast
- \+/\- *lemma* commute_X
- \+/\- *lemma* commute_X_pow
- \+/\- *lemma* coeff_zero
- \+/\- *lemma* coeff_one_zero
- \+/\- *lemma* coeff_X_one
- \+/\- *lemma* coeff_X_zero
- \+/\- *lemma* coeff_X
- \+/\- *lemma* coeff_X_of_ne_one
- \+/\- *lemma* ext
- \+/\- *lemma* add_hom_ext
- \+/\- *lemma* add_hom_ext'
- \+/\- *lemma* lhom_ext'
- \+/\- *lemma* eq_zero_of_eq_zero
- \+/\- *lemma* support_X_pow
- \+/\- *lemma* support_X_empty
- \+/\- *lemma* support_X
- \+/\- *lemma* nat_cast_mul
- \+/\- *lemma* sum_def
- \+/\- *lemma* sum_eq_of_subset
- \+/\- *lemma* sum_add_index
- \+/\- *lemma* sum_add'
- \+/\- *lemma* sum_add
- \+/\- *lemma* sum_smul_index
- \+/\- *lemma* support_erase
- \+/\- *lemma* monomial_add_erase
- \+/\- *lemma* coeff_erase
- \+/\- *lemma* erase_zero
- \+/\- *lemma* erase_same
- \+/\- *lemma* erase_ne
- \+/\- *lemma* coeff_update
- \+/\- *lemma* coeff_update_apply
- \+/\- *lemma* coeff_update_same
- \+/\- *lemma* coeff_update_ne
- \+/\- *lemma* update_zero_eq_erase
- \+/\- *lemma* support_update
- \+/\- *lemma* support_update_zero
- \+/\- *lemma* support_update_ne_zero
- \+/\- *lemma* coeff_neg
- \+/\- *lemma* coeff_sub
- \+/\- *lemma* support_neg
- \+/\- *lemma* X_ne_zero
- \+/\- *lemma* forall_iff_forall_finsupp
- \+/\- *lemma* exists_iff_exists_finsupp
- \+/\- *lemma* zero_to_finsupp
- \+/\- *lemma* one_to_finsupp
- \+/\- *lemma* add_to_finsupp
- \+/\- *lemma* neg_to_finsupp
- \+/\- *lemma* mul_to_finsupp
- \+/\- *lemma* support_zero
- \+/\- *lemma* C_eq_nat_cast
- \+/\- *lemma* commute_X
- \+/\- *lemma* commute_X_pow
- \+/\- *lemma* coeff_zero
- \+/\- *lemma* coeff_one_zero
- \+/\- *lemma* coeff_X_one
- \+/\- *lemma* coeff_X_zero
- \+/\- *lemma* coeff_X
- \+/\- *lemma* coeff_X_of_ne_one
- \+/\- *lemma* ext
- \+/\- *lemma* add_hom_ext
- \+/\- *lemma* add_hom_ext'
- \+/\- *lemma* lhom_ext'
- \+/\- *lemma* eq_zero_of_eq_zero
- \+/\- *lemma* support_X_pow
- \+/\- *lemma* support_X_empty
- \+/\- *lemma* support_X
- \+/\- *lemma* nat_cast_mul
- \+/\- *lemma* sum_def
- \+/\- *lemma* sum_eq_of_subset
- \+/\- *lemma* sum_add_index
- \+/\- *lemma* sum_add'
- \+/\- *lemma* sum_add
- \+/\- *lemma* sum_smul_index
- \+/\- *lemma* support_erase
- \+/\- *lemma* monomial_add_erase
- \+/\- *lemma* coeff_erase
- \+/\- *lemma* erase_zero
- \+/\- *lemma* erase_same
- \+/\- *lemma* erase_ne
- \+/\- *lemma* coeff_update
- \+/\- *lemma* coeff_update_apply
- \+/\- *lemma* coeff_update_same
- \+/\- *lemma* coeff_update_ne
- \+/\- *lemma* update_zero_eq_erase
- \+/\- *lemma* support_update
- \+/\- *lemma* support_update_zero
- \+/\- *lemma* support_update_ne_zero
- \+/\- *lemma* coeff_neg
- \+/\- *lemma* coeff_sub
- \+/\- *lemma* support_neg
- \+/\- *lemma* X_ne_zero
- \+/\- *theorem* ext_iff
- \+/\- *theorem* ext_iff
- \+/\- *def* monomial_fun
- \+/\- *def* to_finsupp_iso
- \+/\- *def* op_ring_equiv
- \+/\- *def* support
- \+/\- *def* monomial
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* coeff
- \+/\- *def* sum
- \+/\- *def* update
- \+/\- *def* monomial_fun
- \+/\- *def* to_finsupp_iso
- \+/\- *def* op_ring_equiv
- \+/\- *def* support
- \+/\- *def* monomial
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* coeff
- \+/\- *def* sum
- \+/\- *def* update

modified src/data/polynomial/cancel_leads.lean
- \+/\- *lemma* dvd_cancel_leads_of_dvd_of_dvd
- \+/\- *lemma* dvd_cancel_leads_of_dvd_of_dvd
- \+/\- *def* cancel_leads
- \+/\- *def* cancel_leads

modified src/data/polynomial/cardinal.lean
- \+/\- *lemma* cardinal_mk_le_max
- \+/\- *lemma* cardinal_mk_le_max

modified src/data/polynomial/coeff.lean
- \+/\- *lemma* coeff_one
- \+/\- *lemma* coeff_add
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* support_smul
- \+/\- *lemma* lcoeff_apply
- \+/\- *lemma* finset_sum_coeff
- \+/\- *lemma* coeff_sum
- \+/\- *lemma* coeff_mul
- \+/\- *lemma* mul_coeff_zero
- \+/\- *lemma* coeff_mul_X_zero
- \+/\- *lemma* coeff_X_mul_zero
- \+/\- *lemma* coeff_C_mul_X
- \+/\- *lemma* coeff_C_mul
- \+/\- *lemma* C_mul'
- \+/\- *lemma* coeff_mul_C
- \+/\- *lemma* coeff_mul_X_pow'
- \+/\- *lemma* coeff_X_pow_mul'
- \+/\- *lemma* C_dvd_iff_dvd_coeff
- \+/\- *lemma* coeff_bit0_mul
- \+/\- *lemma* coeff_bit1_mul
- \+/\- *lemma* update_eq_add_sub_coeff
- \+/\- *lemma* coeff_one
- \+/\- *lemma* coeff_add
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* support_smul
- \+/\- *lemma* lcoeff_apply
- \+/\- *lemma* finset_sum_coeff
- \+/\- *lemma* coeff_sum
- \+/\- *lemma* coeff_mul
- \+/\- *lemma* mul_coeff_zero
- \+/\- *lemma* coeff_mul_X_zero
- \+/\- *lemma* coeff_X_mul_zero
- \+/\- *lemma* coeff_C_mul_X
- \+/\- *lemma* coeff_C_mul
- \+/\- *lemma* C_mul'
- \+/\- *lemma* coeff_mul_C
- \+/\- *lemma* coeff_mul_X_pow'
- \+/\- *lemma* coeff_X_pow_mul'
- \+/\- *lemma* C_dvd_iff_dvd_coeff
- \+/\- *lemma* coeff_bit0_mul
- \+/\- *lemma* coeff_bit1_mul
- \+/\- *lemma* update_eq_add_sub_coeff
- \+/\- *theorem* coeff_mul_X_pow
- \+/\- *theorem* coeff_X_pow_mul
- \+/\- *theorem* coeff_mul_X
- \+/\- *theorem* coeff_X_mul
- \+/\- *theorem* mul_X_pow_eq_zero
- \+/\- *theorem* coeff_mul_X_pow
- \+/\- *theorem* coeff_X_pow_mul
- \+/\- *theorem* coeff_mul_X
- \+/\- *theorem* coeff_X_mul
- \+/\- *theorem* mul_X_pow_eq_zero
- \+/\- *def* lcoeff
- \+/\- *def* lcoeff

modified src/data/polynomial/degree/card_pow_degree.lean
- \+/\- *lemma* card_pow_degree_apply
- \+/\- *lemma* card_pow_degree_zero
- \+/\- *lemma* card_pow_degree_nonzero
- \+/\- *lemma* card_pow_degree_apply
- \+/\- *lemma* card_pow_degree_zero
- \+/\- *lemma* card_pow_degree_nonzero

modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* degree_lt_wf
- \+/\- *lemma* monic_of_subsingleton
- \+/\- *lemma* monic.leading_coeff
- \+/\- *lemma* monic.coeff_nat_degree
- \+/\- *lemma* degree_zero
- \+/\- *lemma* nat_degree_zero
- \+/\- *lemma* degree_eq_iff_nat_degree_eq
- \+/\- *lemma* degree_eq_iff_nat_degree_eq_of_pos
- \+/\- *lemma* nat_degree_eq_of_degree_eq_some
- \+/\- *lemma* nat_degree_eq_of_degree_eq
- \+/\- *lemma* degree_mono
- \+/\- *lemma* nat_degree_le_nat_degree
- \+/\- *lemma* degree_one_le
- \+/\- *lemma* nat_degree_one
- \+/\- *lemma* nat_degree_nat_cast
- \+/\- *lemma* coeff_eq_zero_of_nat_degree_lt
- \+/\- *lemma* coeff_nat_degree_succ_eq_zero
- \+/\- *lemma* ite_le_nat_degree_coeff
- \+/\- *lemma* as_sum_support
- \+/\- *lemma* as_sum_support_C_mul_X_pow
- \+/\- *lemma* sum_over_range'
- \+/\- *lemma* sum_over_range
- \+/\- *lemma* as_sum_range'
- \+/\- *lemma* as_sum_range
- \+/\- *lemma* as_sum_range_C_mul_X_pow
- \+/\- *lemma* nat_degree_X_le
- \+/\- *lemma* card_supp_le_succ_nat_degree
- \+/\- *lemma* degree_one
- \+/\- *lemma* degree_X
- \+/\- *lemma* nat_degree_X
- \+/\- *lemma* coeff_mul_X_sub_C
- \+/\- *lemma* degree_neg
- \+/\- *lemma* nat_degree_neg
- \+/\- *lemma* nat_degree_int_cast
- \+/\- *lemma* next_coeff_of_pos_nat_degree
- \+/\- *lemma* degree_add_le
- \+/\- *lemma* degree_add_le_of_degree_le
- \+/\- *lemma* nat_degree_add_le
- \+/\- *lemma* nat_degree_add_le_of_degree_le
- \+/\- *lemma* leading_coeff_zero
- \+/\- *lemma* degree_erase_le
- \+/\- *lemma* degree_update_le
- \+/\- *lemma* degree_sum_le
- \+/\- *lemma* degree_mul_le
- \+/\- *lemma* degree_pow_le
- \+/\- *lemma* leading_coeff_X_pow
- \+/\- *lemma* leading_coeff_X
- \+/\- *lemma* monic_X_pow
- \+/\- *lemma* monic_X
- \+/\- *lemma* leading_coeff_one
- \+/\- *lemma* monic_one
- \+/\- *lemma* monic.ne_zero
- \+/\- *lemma* monic.ne_zero_of_ne
- \+/\- *lemma* coeff_mul_degree_add_degree
- \+/\- *lemma* nat_degree_mul_le
- \+/\- *lemma* nat_degree_pow_le
- \+/\- *lemma* coeff_pow_mul_nat_degree
- \+/\- *lemma* subsingleton_of_monic_zero
- \+/\- *lemma* zero_le_degree_iff
- \+/\- *lemma* degree_smul_le
- \+/\- *lemma* nat_degree_smul_le
- \+/\- *lemma* degree_X_pow
- \+/\- *lemma* nat_degree_X_pow
- \+/\- *lemma* degree_sub_le
- \+/\- *lemma* degree_pow
- \+/\- *lemma* leading_coeff_mul
- \+/\- *lemma* leading_coeff_hom_apply
- \+/\- *lemma* leading_coeff_pow
- \+/\- *lemma* degree_lt_wf
- \+/\- *lemma* monic_of_subsingleton
- \+/\- *lemma* monic.leading_coeff
- \+/\- *lemma* monic.coeff_nat_degree
- \+/\- *lemma* degree_zero
- \+/\- *lemma* nat_degree_zero
- \+/\- *lemma* degree_eq_iff_nat_degree_eq
- \+/\- *lemma* degree_eq_iff_nat_degree_eq_of_pos
- \+/\- *lemma* nat_degree_eq_of_degree_eq_some
- \+/\- *lemma* nat_degree_eq_of_degree_eq
- \+/\- *lemma* degree_mono
- \+/\- *lemma* nat_degree_le_nat_degree
- \+/\- *lemma* degree_one_le
- \+/\- *lemma* nat_degree_one
- \+/\- *lemma* nat_degree_nat_cast
- \+/\- *lemma* coeff_eq_zero_of_nat_degree_lt
- \+/\- *lemma* coeff_nat_degree_succ_eq_zero
- \+/\- *lemma* ite_le_nat_degree_coeff
- \+/\- *lemma* as_sum_support
- \+/\- *lemma* as_sum_support_C_mul_X_pow
- \+/\- *lemma* sum_over_range'
- \+/\- *lemma* sum_over_range
- \+/\- *lemma* as_sum_range'
- \+/\- *lemma* as_sum_range
- \+/\- *lemma* as_sum_range_C_mul_X_pow
- \+/\- *lemma* nat_degree_X_le
- \+/\- *lemma* card_supp_le_succ_nat_degree
- \+/\- *lemma* degree_one
- \+/\- *lemma* degree_X
- \+/\- *lemma* nat_degree_X
- \+/\- *lemma* coeff_mul_X_sub_C
- \+/\- *lemma* degree_neg
- \+/\- *lemma* nat_degree_neg
- \+/\- *lemma* nat_degree_int_cast
- \+/\- *lemma* next_coeff_of_pos_nat_degree
- \+/\- *lemma* degree_add_le
- \+/\- *lemma* degree_add_le_of_degree_le
- \+/\- *lemma* nat_degree_add_le
- \+/\- *lemma* nat_degree_add_le_of_degree_le
- \+/\- *lemma* leading_coeff_zero
- \+/\- *lemma* degree_erase_le
- \+/\- *lemma* degree_update_le
- \+/\- *lemma* degree_sum_le
- \+/\- *lemma* degree_mul_le
- \+/\- *lemma* degree_pow_le
- \+/\- *lemma* leading_coeff_X_pow
- \+/\- *lemma* leading_coeff_X
- \+/\- *lemma* monic_X_pow
- \+/\- *lemma* monic_X
- \+/\- *lemma* leading_coeff_one
- \+/\- *lemma* monic_one
- \+/\- *lemma* monic.ne_zero
- \+/\- *lemma* monic.ne_zero_of_ne
- \+/\- *lemma* coeff_mul_degree_add_degree
- \+/\- *lemma* nat_degree_mul_le
- \+/\- *lemma* nat_degree_pow_le
- \+/\- *lemma* coeff_pow_mul_nat_degree
- \+/\- *lemma* subsingleton_of_monic_zero
- \+/\- *lemma* zero_le_degree_iff
- \+/\- *lemma* degree_smul_le
- \+/\- *lemma* nat_degree_smul_le
- \+/\- *lemma* degree_X_pow
- \+/\- *lemma* nat_degree_X_pow
- \+/\- *lemma* degree_sub_le
- \+/\- *lemma* degree_pow
- \+/\- *lemma* leading_coeff_mul
- \+/\- *lemma* leading_coeff_hom_apply
- \+/\- *lemma* leading_coeff_pow
- \+/\- *theorem* degree_X_pow_le
- \+/\- *theorem* degree_X_le
- \+/\- *theorem* leading_coeff_monic_mul
- \+/\- *theorem* leading_coeff_mul_monic
- \+/\- *theorem* leading_coeff_mul_X_pow
- \+/\- *theorem* leading_coeff_mul_X
- \+/\- *theorem* degree_le_iff_coeff_zero
- \+/\- *theorem* degree_lt_iff_coeff_zero
- \+/\- *theorem* not_is_unit_X
- \+/\- *theorem* degree_X_pow_le
- \+/\- *theorem* degree_X_le
- \+/\- *theorem* leading_coeff_monic_mul
- \+/\- *theorem* leading_coeff_mul_monic
- \+/\- *theorem* leading_coeff_mul_X_pow
- \+/\- *theorem* leading_coeff_mul_X
- \+/\- *theorem* degree_le_iff_coeff_zero
- \+/\- *theorem* degree_lt_iff_coeff_zero
- \+/\- *theorem* not_is_unit_X
- \+/\- *def* degree
- \+/\- *def* nat_degree
- \+/\- *def* leading_coeff
- \+/\- *def* monic
- \+/\- *def* next_coeff
- \+/\- *def* leading_coeff_hom
- \+/\- *def* degree
- \+/\- *def* nat_degree
- \+/\- *def* leading_coeff
- \+/\- *def* monic
- \+/\- *def* next_coeff
- \+/\- *def* leading_coeff_hom

modified src/data/polynomial/degree/lemmas.lean
- \+/\- *lemma* degree_pos_of_root
- \+/\- *lemma* nat_degree_C_mul_le
- \+/\- *lemma* nat_degree_mul_C_le
- \+/\- *lemma* nat_degree_add_coeff_mul
- \+/\- *lemma* degree_sum_eq_of_disjoint
- \+/\- *lemma* nat_degree_sum_eq_of_disjoint
- \+/\- *lemma* nat_degree_pos_of_eval₂_root
- \+/\- *lemma* degree_pos_of_eval₂_root
- \+/\- *lemma* coe_lt_degree
- \+/\- *lemma* degree_pos_of_root
- \+/\- *lemma* nat_degree_C_mul_le
- \+/\- *lemma* nat_degree_mul_C_le
- \+/\- *lemma* nat_degree_add_coeff_mul
- \+/\- *lemma* degree_sum_eq_of_disjoint
- \+/\- *lemma* nat_degree_sum_eq_of_disjoint
- \+/\- *lemma* nat_degree_pos_of_eval₂_root
- \+/\- *lemma* degree_pos_of_eval₂_root
- \+/\- *lemma* coe_lt_degree

modified src/data/polynomial/degree/trailing_degree.lean
- \+/\- *lemma* trailing_monic.trailing_coeff
- \+/\- *lemma* trailing_degree_zero
- \+/\- *lemma* trailing_coeff_zero
- \+/\- *lemma* nat_trailing_degree_zero
- \+/\- *lemma* trailing_degree_eq_iff_nat_trailing_degree_eq
- \+/\- *lemma* trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos
- \+/\- *lemma* nat_trailing_degree_eq_of_trailing_degree_eq_some
- \+/\- *lemma* nat_trailing_degree_eq_of_trailing_degree_eq
- \+/\- *lemma* trailing_degree_one_le
- \+/\- *lemma* nat_trailing_degree_one
- \+/\- *lemma* nat_trailing_degree_nat_cast
- \+/\- *lemma* coeff_eq_zero_of_lt_nat_trailing_degree
- \+/\- *lemma* coeff_nat_trailing_degree_pred_eq_zero
- \+/\- *lemma* nat_trailing_degree_X_le
- \+/\- *lemma* nat_trailing_degree_le_nat_degree
- \+/\- *lemma* nat_trailing_degree_mul_X_pow
- \+/\- *lemma* trailing_degree_one
- \+/\- *lemma* trailing_degree_X
- \+/\- *lemma* nat_trailing_degree_X
- \+/\- *lemma* trailing_degree_neg
- \+/\- *lemma* nat_trailing_degree_neg
- \+/\- *lemma* nat_trailing_degree_int_cast
- \+/\- *lemma* next_coeff_up_of_pos_nat_trailing_degree
- \+/\- *lemma* trailing_monic.trailing_coeff
- \+/\- *lemma* trailing_degree_zero
- \+/\- *lemma* trailing_coeff_zero
- \+/\- *lemma* nat_trailing_degree_zero
- \+/\- *lemma* trailing_degree_eq_iff_nat_trailing_degree_eq
- \+/\- *lemma* trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos
- \+/\- *lemma* nat_trailing_degree_eq_of_trailing_degree_eq_some
- \+/\- *lemma* nat_trailing_degree_eq_of_trailing_degree_eq
- \+/\- *lemma* trailing_degree_one_le
- \+/\- *lemma* nat_trailing_degree_one
- \+/\- *lemma* nat_trailing_degree_nat_cast
- \+/\- *lemma* coeff_eq_zero_of_lt_nat_trailing_degree
- \+/\- *lemma* coeff_nat_trailing_degree_pred_eq_zero
- \+/\- *lemma* nat_trailing_degree_X_le
- \+/\- *lemma* nat_trailing_degree_le_nat_degree
- \+/\- *lemma* nat_trailing_degree_mul_X_pow
- \+/\- *lemma* trailing_degree_one
- \+/\- *lemma* trailing_degree_X
- \+/\- *lemma* nat_trailing_degree_X
- \+/\- *lemma* trailing_degree_neg
- \+/\- *lemma* nat_trailing_degree_neg
- \+/\- *lemma* nat_trailing_degree_int_cast
- \+/\- *lemma* next_coeff_up_of_pos_nat_trailing_degree
- \+/\- *theorem* le_trailing_degree_X
- \+/\- *theorem* le_trailing_degree_X
- \+/\- *def* trailing_degree
- \+/\- *def* nat_trailing_degree
- \+/\- *def* trailing_coeff
- \+/\- *def* trailing_monic
- \+/\- *def* next_coeff_up
- \+/\- *def* trailing_degree
- \+/\- *def* nat_trailing_degree
- \+/\- *def* trailing_coeff
- \+/\- *def* trailing_monic
- \+/\- *def* next_coeff_up

modified src/data/polynomial/denoms_clearable.lean
- \+/\- *lemma* denoms_clearable.add
- \+/\- *lemma* one_le_pow_mul_abs_eval_div
- \+/\- *lemma* denoms_clearable.add
- \+/\- *lemma* one_le_pow_mul_abs_eval_div
- \+/\- *def* denoms_clearable
- \+/\- *def* denoms_clearable

modified src/data/polynomial/derivative.lean
- \+/\- *lemma* derivative_apply
- \+/\- *lemma* coeff_derivative
- \+/\- *lemma* derivative_zero
- \+/\- *lemma* iterate_derivative_zero
- \+/\- *lemma* derivative_X
- \+/\- *lemma* derivative_one
- \+/\- *lemma* derivative_bit0
- \+/\- *lemma* derivative_bit1
- \+/\- *lemma* derivative_add
- \+/\- *lemma* iterate_derivative_add
- \+/\- *lemma* derivative_neg
- \+/\- *lemma* iterate_derivative_neg
- \+/\- *lemma* derivative_sub
- \+/\- *lemma* iterate_derivative_sub
- \+/\- *lemma* derivative_sum
- \+/\- *lemma* derivative_smul
- \+/\- *lemma* iterate_derivative_smul
- \+/\- *lemma* derivative_C_mul
- \+/\- *lemma* iterate_derivative_C_mul
- \+/\- *lemma* derivative_eval
- \+/\- *lemma* derivative_mul
- \+/\- *lemma* derivative_comp
- \+/\- *lemma* derivative_cast_nat
- \+/\- *lemma* iterate_derivative_cast_nat_mul
- \+/\- *lemma* derivative_comp_one_sub_X
- \+/\- *lemma* iterate_derivative_comp_one_sub_X
- \+/\- *lemma* mem_support_derivative
- \+/\- *lemma* degree_derivative_eq
- \+/\- *lemma* derivative_apply
- \+/\- *lemma* coeff_derivative
- \+/\- *lemma* derivative_zero
- \+/\- *lemma* iterate_derivative_zero
- \+/\- *lemma* derivative_X
- \+/\- *lemma* derivative_one
- \+/\- *lemma* derivative_bit0
- \+/\- *lemma* derivative_bit1
- \+/\- *lemma* derivative_add
- \+/\- *lemma* iterate_derivative_add
- \+/\- *lemma* derivative_neg
- \+/\- *lemma* iterate_derivative_neg
- \+/\- *lemma* derivative_sub
- \+/\- *lemma* iterate_derivative_sub
- \+/\- *lemma* derivative_sum
- \+/\- *lemma* derivative_smul
- \+/\- *lemma* iterate_derivative_smul
- \+/\- *lemma* derivative_C_mul
- \+/\- *lemma* iterate_derivative_C_mul
- \+/\- *lemma* derivative_eval
- \+/\- *lemma* derivative_mul
- \+/\- *lemma* derivative_comp
- \+/\- *lemma* derivative_cast_nat
- \+/\- *lemma* iterate_derivative_cast_nat_mul
- \+/\- *lemma* derivative_comp_one_sub_X
- \+/\- *lemma* iterate_derivative_comp_one_sub_X
- \+/\- *lemma* mem_support_derivative
- \+/\- *lemma* degree_derivative_eq
- \+/\- *theorem* derivative_pow_succ
- \+/\- *theorem* derivative_pow
- \+/\- *theorem* derivative_map
- \+/\- *theorem* iterate_derivative_map
- \+/\- *theorem* derivative_eval₂_C
- \+/\- *theorem* derivative_prod
- \+/\- *theorem* of_mem_support_derivative
- \+/\- *theorem* degree_derivative_lt
- \+/\- *theorem* nat_degree_derivative_lt
- \+/\- *theorem* degree_derivative_le
- \+/\- *theorem* derivative_pow_succ
- \+/\- *theorem* derivative_pow
- \+/\- *theorem* derivative_map
- \+/\- *theorem* iterate_derivative_map
- \+/\- *theorem* derivative_eval₂_C
- \+/\- *theorem* derivative_prod
- \+/\- *theorem* of_mem_support_derivative
- \+/\- *theorem* degree_derivative_lt
- \+/\- *theorem* nat_degree_derivative_lt
- \+/\- *theorem* degree_derivative_le
- \+/\- *def* derivative
- \+/\- *def* derivative_lhom
- \+/\- *def* derivative
- \+/\- *def* derivative_lhom

modified src/data/polynomial/div.lean
- \+/\- *lemma* degree_mod_by_monic_lt
- \+/\- *lemma* zero_mod_by_monic
- \+/\- *lemma* zero_div_by_monic
- \+/\- *lemma* mod_by_monic_zero
- \+/\- *lemma* div_by_monic_zero
- \+/\- *lemma* div_by_monic_eq_of_not_monic
- \+/\- *lemma* mod_by_monic_eq_of_not_monic
- \+/\- *lemma* mod_by_monic_eq_sub_mul_div
- \+/\- *lemma* mod_by_monic_add_div
- \+/\- *lemma* degree_div_by_monic_le
- \+/\- *lemma* degree_div_by_monic_lt
- \+/\- *lemma* div_mod_by_monic_unique
- \+/\- *lemma* mod_by_monic_one
- \+/\- *lemma* div_by_monic_one
- \+/\- *lemma* mod_by_monic_X_sub_C_eq_C_eval
- \+/\- *lemma* mod_by_monic_X
- \+/\- *lemma* root_multiplicity_eq_multiplicity
- \+/\- *lemma* root_multiplicity_eq_zero
- \+/\- *lemma* root_multiplicity_pos
- \+/\- *lemma* pow_root_multiplicity_dvd
- \+/\- *lemma* degree_mod_by_monic_lt
- \+/\- *lemma* zero_mod_by_monic
- \+/\- *lemma* zero_div_by_monic
- \+/\- *lemma* mod_by_monic_zero
- \+/\- *lemma* div_by_monic_zero
- \+/\- *lemma* div_by_monic_eq_of_not_monic
- \+/\- *lemma* mod_by_monic_eq_of_not_monic
- \+/\- *lemma* mod_by_monic_eq_sub_mul_div
- \+/\- *lemma* mod_by_monic_add_div
- \+/\- *lemma* degree_div_by_monic_le
- \+/\- *lemma* degree_div_by_monic_lt
- \+/\- *lemma* div_mod_by_monic_unique
- \+/\- *lemma* mod_by_monic_one
- \+/\- *lemma* div_by_monic_one
- \+/\- *lemma* mod_by_monic_X_sub_C_eq_C_eval
- \+/\- *lemma* mod_by_monic_X
- \+/\- *lemma* root_multiplicity_eq_multiplicity
- \+/\- *lemma* root_multiplicity_eq_zero
- \+/\- *lemma* root_multiplicity_pos
- \+/\- *lemma* pow_root_multiplicity_dvd
- \+/\- *theorem* X_dvd_iff
- \+/\- *theorem* degree_mod_by_monic_le
- \+/\- *theorem* nat_degree_div_by_monic
- \+/\- *theorem* map_dvd_map
- \+/\- *theorem* X_dvd_iff
- \+/\- *theorem* degree_mod_by_monic_le
- \+/\- *theorem* nat_degree_div_by_monic
- \+/\- *theorem* map_dvd_map
- \+/\- *def* div_by_monic
- \+/\- *def* mod_by_monic
- \+/\- *def* decidable_dvd_monic
- \+/\- *def* root_multiplicity
- \+/\- *def* div_by_monic
- \+/\- *def* mod_by_monic
- \+/\- *def* decidable_dvd_monic
- \+/\- *def* root_multiplicity

modified src/data/polynomial/erase_lead.lean
- \+/\- *lemma* erase_lead_support
- \+/\- *lemma* erase_lead_zero
- \+/\- *lemma* erase_lead_add_monomial_nat_degree_leading_coeff
- \+/\- *lemma* erase_lead_add_C_mul_X_pow
- \+/\- *lemma* self_sub_monomial_nat_degree_leading_coeff
- \+/\- *lemma* self_sub_C_mul_X_pow
- \+/\- *lemma* erase_lead_X
- \+/\- *lemma* erase_lead_X_pow
- \+/\- *lemma* erase_lead_nat_degree_lt_or_erase_lead_eq_zero
- \+/\- *lemma* induction_with_nat_degree_le
- \+/\- *lemma* erase_lead_support
- \+/\- *lemma* erase_lead_zero
- \+/\- *lemma* erase_lead_add_monomial_nat_degree_leading_coeff
- \+/\- *lemma* erase_lead_add_C_mul_X_pow
- \+/\- *lemma* self_sub_monomial_nat_degree_leading_coeff
- \+/\- *lemma* self_sub_C_mul_X_pow
- \+/\- *lemma* erase_lead_X
- \+/\- *lemma* erase_lead_X_pow
- \+/\- *lemma* erase_lead_nat_degree_lt_or_erase_lead_eq_zero
- \+/\- *lemma* induction_with_nat_degree_le
- \+/\- *def* erase_lead
- \+/\- *def* erase_lead

modified src/data/polynomial/eval.lean
- \+/\- *lemma* eval₂_zero
- \+/\- *lemma* eval₂_one
- \+/\- *lemma* eval₂_smul
- \+/\- *lemma* eval₂_nat_cast
- \+/\- *lemma* eval₂_sum
- \+/\- *lemma* eval₂_finset_sum
- \+/\- *lemma* eval₂_list_prod_noncomm
- \+/\- *lemma* eval₂_mul_eq_zero_of_left
- \+/\- *lemma* eval₂_mul_eq_zero_of_right
- \+/\- *lemma* eval₂_eq_sum_range'
- \+/\- *lemma* eval_eq_finset_sum
- \+/\- *lemma* eval_eq_finset_sum'
- \+/\- *lemma* eval_nat_cast
- \+/\- *lemma* eval_zero
- \+/\- *lemma* eval_one
- \+/\- *lemma* eval_smul
- \+/\- *lemma* eval_nat_cast_mul
- \+/\- *lemma* eval_sum
- \+/\- *lemma* eval_finset_sum
- \+/\- *lemma* coeff_zero_eq_eval_zero
- \+/\- *lemma* zero_is_root_of_coeff_zero_eq_zero
- \+/\- *lemma* is_root.dvd
- \+/\- *lemma* nat_cast_comp
- \+/\- *lemma* comp_zero
- \+/\- *lemma* zero_comp
- \+/\- *lemma* one_comp
- \+/\- *lemma* nat_cast_mul_comp
- \+/\- *lemma* mul_comp
- \+/\- *lemma* prod_comp
- \+/\- *lemma* pow_comp
- \+/\- *lemma* bit0_comp
- \+/\- *lemma* bit1_comp
- \+/\- *lemma* comp_assoc
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_one
- \+/\- *lemma* degree_map_le
- \+/\- *lemma* nat_degree_map_le
- \+/\- *lemma* map_ring_hom_id
- \+/\- *lemma* map_list_prod
- \+/\- *lemma* mem_map_srange
- \+/\- *lemma* map_sum
- \+/\- *lemma* map_comp
- \+/\- *lemma* eval_zero_map
- \+/\- *lemma* eval_one_map
- \+/\- *lemma* eval_nat_cast_map
- \+/\- *lemma* coe_eval_ring_hom
- \+/\- *lemma* root_mul_left_of_is_root
- \+/\- *lemma* root_mul_right_of_is_root
- \+/\- *lemma* eval_list_prod
- \+/\- *lemma* eval_multiset_prod
- \+/\- *lemma* eval_prod
- \+/\- *lemma* map_multiset_prod
- \+/\- *lemma* map_prod
- \+/\- *lemma* support_map_subset
- \+/\- *lemma* is_root.map
- \+/\- *lemma* is_root.of_map
- \+/\- *lemma* is_root_map_iff
- \+/\- *lemma* eval_int_cast
- \+/\- *lemma* eval_neg
- \+/\- *lemma* eval_sub
- \+/\- *lemma* cast_int_comp
- \+/\- *lemma* eval₂_zero
- \+/\- *lemma* eval₂_one
- \+/\- *lemma* eval₂_smul
- \+/\- *lemma* eval₂_nat_cast
- \+/\- *lemma* eval₂_sum
- \+/\- *lemma* eval₂_finset_sum
- \+/\- *lemma* eval₂_list_prod_noncomm
- \+/\- *lemma* eval₂_mul_eq_zero_of_left
- \+/\- *lemma* eval₂_mul_eq_zero_of_right
- \+/\- *lemma* eval₂_eq_sum_range'
- \+/\- *lemma* eval_eq_finset_sum
- \+/\- *lemma* eval_eq_finset_sum'
- \+/\- *lemma* eval_nat_cast
- \+/\- *lemma* eval_zero
- \+/\- *lemma* eval_one
- \+/\- *lemma* eval_smul
- \+/\- *lemma* eval_nat_cast_mul
- \+/\- *lemma* eval_sum
- \+/\- *lemma* eval_finset_sum
- \+/\- *lemma* coeff_zero_eq_eval_zero
- \+/\- *lemma* zero_is_root_of_coeff_zero_eq_zero
- \+/\- *lemma* is_root.dvd
- \+/\- *lemma* nat_cast_comp
- \+/\- *lemma* comp_zero
- \+/\- *lemma* zero_comp
- \+/\- *lemma* one_comp
- \+/\- *lemma* nat_cast_mul_comp
- \+/\- *lemma* mul_comp
- \+/\- *lemma* prod_comp
- \+/\- *lemma* pow_comp
- \+/\- *lemma* bit0_comp
- \+/\- *lemma* bit1_comp
- \+/\- *lemma* comp_assoc
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_one
- \+/\- *lemma* degree_map_le
- \+/\- *lemma* nat_degree_map_le
- \+/\- *lemma* map_ring_hom_id
- \+/\- *lemma* map_list_prod
- \+/\- *lemma* mem_map_srange
- \+/\- *lemma* map_sum
- \+/\- *lemma* map_comp
- \+/\- *lemma* eval_zero_map
- \+/\- *lemma* eval_one_map
- \+/\- *lemma* eval_nat_cast_map
- \+/\- *lemma* coe_eval_ring_hom
- \+/\- *lemma* root_mul_left_of_is_root
- \+/\- *lemma* root_mul_right_of_is_root
- \+/\- *lemma* eval_list_prod
- \+/\- *lemma* eval_multiset_prod
- \+/\- *lemma* eval_prod
- \+/\- *lemma* map_multiset_prod
- \+/\- *lemma* map_prod
- \+/\- *lemma* support_map_subset
- \+/\- *lemma* is_root.map
- \+/\- *lemma* is_root.of_map
- \+/\- *lemma* is_root_map_iff
- \+/\- *lemma* eval_int_cast
- \+/\- *lemma* eval_neg
- \+/\- *lemma* eval_sub
- \+/\- *lemma* cast_int_comp
- \+/\- *def* eval₂
- \+/\- *def* eval₂_add_monoid_hom
- \+/\- *def* eval₂_ring_hom'
- \+/\- *def* eval₂_ring_hom
- \+/\- *def* eval
- \+/\- *def* leval
- \+/\- *def* is_root
- \+/\- *def* comp
- \+/\- *def* map
- \+/\- *def* map_ring_hom
- \+/\- *def* map_equiv
- \+/\- *def* eval_ring_hom
- \+/\- *def* comp_ring_hom
- \+/\- *def* eval₂
- \+/\- *def* eval₂_add_monoid_hom
- \+/\- *def* eval₂_ring_hom'
- \+/\- *def* eval₂_ring_hom
- \+/\- *def* eval
- \+/\- *def* leval
- \+/\- *def* is_root
- \+/\- *def* comp
- \+/\- *def* map
- \+/\- *def* map_ring_hom
- \+/\- *def* map_equiv
- \+/\- *def* eval_ring_hom
- \+/\- *def* comp_ring_hom

modified src/data/polynomial/field_division.lean
- \+/\- *lemma* coe_norm_unit
- \+/\- *lemma* leading_coeff_normalize
- \+/\- *lemma* monic.normalize_eq_self
- \+/\- *lemma* prod_multiset_root_eq_finset_root
- \+/\- *lemma* roots_C_mul
- \+/\- *lemma* roots_normalize
- \+/\- *lemma* degree_mul_leading_coeff_inv
- \+/\- *lemma* mod_by_monic_eq_mod
- \+/\- *lemma* div_by_monic_eq_div
- \+/\- *lemma* mod_X_sub_C_eq_C_eval
- \+/\- *lemma* degree_div_le
- \+/\- *lemma* degree_map
- \+/\- *lemma* eval₂_gcd_eq_zero
- \+/\- *lemma* eval_gcd_eq_zero
- \+/\- *lemma* root_left_of_root_gcd
- \+/\- *lemma* root_right_of_root_gcd
- \+/\- *lemma* root_gcd_iff_root_left_right
- \+/\- *lemma* is_root_gcd_iff_is_root_left_right
- \+/\- *lemma* coeff_inv_units
- \+/\- *lemma* coe_norm_unit_of_ne_zero
- \+/\- *lemma* prod_multiset_X_sub_C_dvd
- \+/\- *lemma* coe_norm_unit
- \+/\- *lemma* leading_coeff_normalize
- \+/\- *lemma* monic.normalize_eq_self
- \+/\- *lemma* prod_multiset_root_eq_finset_root
- \+/\- *lemma* roots_C_mul
- \+/\- *lemma* roots_normalize
- \+/\- *lemma* degree_mul_leading_coeff_inv
- \+/\- *lemma* mod_by_monic_eq_mod
- \+/\- *lemma* div_by_monic_eq_div
- \+/\- *lemma* mod_X_sub_C_eq_C_eval
- \+/\- *lemma* degree_div_le
- \+/\- *lemma* degree_map
- \+/\- *lemma* eval₂_gcd_eq_zero
- \+/\- *lemma* eval_gcd_eq_zero
- \+/\- *lemma* root_left_of_root_gcd
- \+/\- *lemma* root_right_of_root_gcd
- \+/\- *lemma* root_gcd_iff_root_left_right
- \+/\- *lemma* is_root_gcd_iff_is_root_left_right
- \+/\- *lemma* coeff_inv_units
- \+/\- *lemma* coe_norm_unit_of_ne_zero
- \+/\- *lemma* prod_multiset_X_sub_C_dvd
- \+/\- *theorem* irreducible_of_monic
- \+/\- *theorem* monic_map_iff
- \+/\- *theorem* map_dvd_map'
- \+/\- *theorem* irreducible_of_monic
- \+/\- *theorem* monic_map_iff
- \+/\- *theorem* map_dvd_map'
- \+/\- *def* div
- \+/\- *def* mod
- \+/\- *def* div
- \+/\- *def* mod

modified src/data/polynomial/hasse_deriv.lean
- \+/\- *lemma* hasse_deriv_eq_zero_of_lt_nat_degree
- \+/\- *lemma* hasse_deriv_apply_one
- \+/\- *lemma* hasse_deriv_X
- \+/\- *lemma* nat_degree_hasse_deriv_le
- \+/\- *lemma* nat_degree_hasse_deriv
- \+/\- *lemma* hasse_deriv_mul
- \+/\- *lemma* hasse_deriv_eq_zero_of_lt_nat_degree
- \+/\- *lemma* hasse_deriv_apply_one
- \+/\- *lemma* hasse_deriv_X
- \+/\- *lemma* nat_degree_hasse_deriv_le
- \+/\- *lemma* nat_degree_hasse_deriv
- \+/\- *lemma* hasse_deriv_mul
- \+/\- *def* hasse_deriv
- \+/\- *def* hasse_deriv

modified src/data/polynomial/identities.lean
- \+/\- *def* binom_expansion
- \+/\- *def* eval_sub_factor
- \+/\- *def* binom_expansion
- \+/\- *def* eval_sub_factor

modified src/data/polynomial/induction.lean
- \+/\- *lemma* sum_C_mul_X_eq
- \+/\- *lemma* sum_monomial_eq
- \+/\- *lemma* sum_C_mul_X_eq
- \+/\- *lemma* sum_monomial_eq
- \+/\- *theorem* coeff_mul_monomial
- \+/\- *theorem* coeff_monomial_mul
- \+/\- *theorem* coeff_mul_monomial_zero
- \+/\- *theorem* coeff_monomial_zero_mul
- \+/\- *theorem* coeff_mul_monomial
- \+/\- *theorem* coeff_monomial_mul
- \+/\- *theorem* coeff_mul_monomial_zero
- \+/\- *theorem* coeff_monomial_zero_mul

modified src/data/polynomial/inductions.lean
- \+/\- *lemma* div_X_mul_X_add
- \+/\- *lemma* nat_degree_ne_zero_induction_on
- \+/\- *lemma* div_X_mul_X_add
- \+/\- *lemma* nat_degree_ne_zero_induction_on
- \+/\- *def* div_X
- \+/\- *def* div_X

modified src/data/polynomial/integral_normalization.lean
- \+/\- *lemma* integral_normalization_coeff
- \+/\- *lemma* integral_normalization_support
- \+/\- *lemma* integral_normalization_coeff_degree
- \+/\- *lemma* integral_normalization_coeff_nat_degree
- \+/\- *lemma* integral_normalization_coeff_ne_degree
- \+/\- *lemma* monic_integral_normalization
- \+/\- *lemma* support_integral_normalization
- \+/\- *lemma* integral_normalization_eval₂_eq_zero
- \+/\- *lemma* integral_normalization_aeval_eq_zero
- \+/\- *lemma* integral_normalization_coeff
- \+/\- *lemma* integral_normalization_support
- \+/\- *lemma* integral_normalization_coeff_degree
- \+/\- *lemma* integral_normalization_coeff_nat_degree
- \+/\- *lemma* integral_normalization_coeff_ne_degree
- \+/\- *lemma* monic_integral_normalization
- \+/\- *lemma* support_integral_normalization
- \+/\- *lemma* integral_normalization_eval₂_eq_zero
- \+/\- *lemma* integral_normalization_aeval_eq_zero

modified src/data/polynomial/iterated_deriv.lean
- \+/\- *lemma* iterated_deriv_zero_left
- \+/\- *lemma* iterated_deriv_X_zero
- \+/\- *lemma* iterated_deriv_X_one
- \+/\- *lemma* iterated_deriv_X
- \+/\- *lemma* iterated_deriv_one_zero
- \+/\- *lemma* iterated_deriv_one
- \+/\- *lemma* iterated_deriv_zero_left
- \+/\- *lemma* iterated_deriv_X_zero
- \+/\- *lemma* iterated_deriv_X_one
- \+/\- *lemma* iterated_deriv_X
- \+/\- *lemma* iterated_deriv_one_zero
- \+/\- *lemma* iterated_deriv_one
- \+/\- *def* iterated_deriv
- \+/\- *def* iterated_deriv

modified src/data/polynomial/lifts.lean
- \+/\- *lemma* mem_lifts
- \+/\- *lemma* lifts_iff_set_range
- \+/\- *lemma* lifts_iff_ring_hom_srange
- \+/\- *lemma* lifts_iff_coeff_lifts
- \+/\- *lemma* X_mem_lifts
- \+/\- *lemma* X_pow_mem_lifts
- \+/\- *lemma* base_mul_mem_lifts
- \+/\- *lemma* erase_mem_lifts
- \+/\- *lemma* mem_lifts_and_degree_eq
- \+/\- *lemma* lifts_and_degree_eq_and_monic
- \+/\- *lemma* lifts_iff_lifts_ring
- \+/\- *lemma* map_alg_eq_map
- \+/\- *lemma* smul_mem_lifts
- \+/\- *lemma* mem_lifts
- \+/\- *lemma* lifts_iff_set_range
- \+/\- *lemma* lifts_iff_ring_hom_srange
- \+/\- *lemma* lifts_iff_coeff_lifts
- \+/\- *lemma* X_mem_lifts
- \+/\- *lemma* X_pow_mem_lifts
- \+/\- *lemma* base_mul_mem_lifts
- \+/\- *lemma* erase_mem_lifts
- \+/\- *lemma* mem_lifts_and_degree_eq
- \+/\- *lemma* lifts_and_degree_eq_and_monic
- \+/\- *lemma* lifts_iff_lifts_ring
- \+/\- *lemma* map_alg_eq_map
- \+/\- *lemma* smul_mem_lifts
- \+/\- *def* lifts
- \+/\- *def* lifts_ring
- \+/\- *def* lifts
- \+/\- *def* lifts_ring

modified src/data/polynomial/mirror.lean
- \+/\- *lemma* mirror_zero
- \+/\- *lemma* mirror_X
- \+/\- *lemma* mirror_mul_of_domain
- \+/\- *lemma* mirror_smul
- \+/\- *lemma* mirror_neg
- \+/\- *lemma* irreducible_of_mirror
- \+/\- *lemma* mirror_zero
- \+/\- *lemma* mirror_X
- \+/\- *lemma* mirror_mul_of_domain
- \+/\- *lemma* mirror_smul
- \+/\- *lemma* mirror_neg
- \+/\- *lemma* irreducible_of_mirror

modified src/data/polynomial/monic.lean
- \+/\- *lemma* monic.as_sum
- \+/\- *lemma* monic_add_of_left
- \+/\- *lemma* monic_add_of_right
- \+/\- *lemma* nat_degree_eq_zero_iff_eq_one
- \+/\- *lemma* degree_le_zero_iff_eq_one
- \+/\- *lemma* nat_degree_mul
- \+/\- *lemma* degree_mul_comm
- \+/\- *lemma* nat_degree_mul'
- \+/\- *lemma* nat_degree_mul_comm
- \+/\- *lemma* next_coeff_mul
- \+/\- *lemma* monic_multiset_prod_of_monic
- \+/\- *lemma* monic_prod_of_monic
- \+/\- *lemma* monic.next_coeff_multiset_prod
- \+/\- *lemma* monic.next_coeff_prod
- \+/\- *lemma* monic_sub_of_left
- \+/\- *lemma* monic_sub_of_right
- \+/\- *lemma* degree_map_eq_of_injective
- \+/\- *lemma* nat_degree_map_eq_of_injective
- \+/\- *lemma* leading_coeff_map'
- \+/\- *lemma* next_coeff_map
- \+/\- *lemma* leading_coeff_of_injective
- \+/\- *lemma* monic_of_injective
- \+/\- *lemma* not_monic_zero
- \+/\- *lemma* monic.mul_left_ne_zero
- \+/\- *lemma* monic.mul_right_ne_zero
- \+/\- *lemma* monic.mul_nat_degree_lt_iff
- \+/\- *lemma* monic.mul_right_eq_zero_iff
- \+/\- *lemma* monic.mul_left_eq_zero_iff
- \+/\- *lemma* monic.is_regular
- \+/\- *lemma* is_unit_leading_coeff_mul_right_eq_zero_iff
- \+/\- *lemma* is_unit_leading_coeff_mul_left_eq_zero_iff
- \+/\- *lemma* monic.as_sum
- \+/\- *lemma* monic_add_of_left
- \+/\- *lemma* monic_add_of_right
- \+/\- *lemma* nat_degree_eq_zero_iff_eq_one
- \+/\- *lemma* degree_le_zero_iff_eq_one
- \+/\- *lemma* nat_degree_mul
- \+/\- *lemma* degree_mul_comm
- \+/\- *lemma* nat_degree_mul'
- \+/\- *lemma* nat_degree_mul_comm
- \+/\- *lemma* next_coeff_mul
- \+/\- *lemma* monic_multiset_prod_of_monic
- \+/\- *lemma* monic_prod_of_monic
- \+/\- *lemma* monic.next_coeff_multiset_prod
- \+/\- *lemma* monic.next_coeff_prod
- \+/\- *lemma* monic_sub_of_left
- \+/\- *lemma* monic_sub_of_right
- \+/\- *lemma* degree_map_eq_of_injective
- \+/\- *lemma* nat_degree_map_eq_of_injective
- \+/\- *lemma* leading_coeff_map'
- \+/\- *lemma* next_coeff_map
- \+/\- *lemma* leading_coeff_of_injective
- \+/\- *lemma* monic_of_injective
- \+/\- *lemma* not_monic_zero
- \+/\- *lemma* monic.mul_left_ne_zero
- \+/\- *lemma* monic.mul_right_ne_zero
- \+/\- *lemma* monic.mul_nat_degree_lt_iff
- \+/\- *lemma* monic.mul_right_eq_zero_iff
- \+/\- *lemma* monic.mul_left_eq_zero_iff
- \+/\- *lemma* monic.is_regular
- \+/\- *lemma* is_unit_leading_coeff_mul_right_eq_zero_iff
- \+/\- *lemma* is_unit_leading_coeff_mul_left_eq_zero_iff

modified src/data/polynomial/monomial.lean
- \+/\- *lemma* card_support_le_one_iff_monomial
- \+/\- *lemma* ring_hom_ext
- \+/\- *lemma* ring_hom_ext'
- \+/\- *lemma* card_support_le_one_iff_monomial
- \+/\- *lemma* ring_hom_ext
- \+/\- *lemma* ring_hom_ext'

modified src/data/polynomial/reverse.lean
- \+/\- *lemma* reflect_support
- \+/\- *lemma* coeff_reflect
- \+/\- *lemma* reflect_zero
- \+/\- *lemma* reflect_eq_zero_iff
- \+/\- *lemma* reflect_add
- \+/\- *lemma* reflect_C_mul
- \+/\- *lemma* reflect_monomial
- \+/\- *lemma* eval₂_reflect_mul_pow
- \+/\- *lemma* eval₂_reflect_eq_zero_iff
- \+/\- *lemma* coeff_reverse
- \+/\- *lemma* coeff_zero_reverse
- \+/\- *lemma* reverse_zero
- \+/\- *lemma* reverse_nat_degree_le
- \+/\- *lemma* nat_degree_eq_reverse_nat_degree_add_nat_trailing_degree
- \+/\- *lemma* reverse_nat_degree
- \+/\- *lemma* reverse_leading_coeff
- \+/\- *lemma* reverse_nat_trailing_degree
- \+/\- *lemma* reverse_trailing_coeff
- \+/\- *lemma* reverse_mul_of_domain
- \+/\- *lemma* trailing_coeff_mul
- \+/\- *lemma* coeff_one_reverse
- \+/\- *lemma* eval₂_reverse_mul_pow
- \+/\- *lemma* eval₂_reverse_eq_zero_iff
- \+/\- *lemma* reflect_neg
- \+/\- *lemma* reflect_sub
- \+/\- *lemma* reverse_neg
- \+/\- *lemma* reflect_support
- \+/\- *lemma* coeff_reflect
- \+/\- *lemma* reflect_zero
- \+/\- *lemma* reflect_eq_zero_iff
- \+/\- *lemma* reflect_add
- \+/\- *lemma* reflect_C_mul
- \+/\- *lemma* reflect_monomial
- \+/\- *lemma* eval₂_reflect_mul_pow
- \+/\- *lemma* eval₂_reflect_eq_zero_iff
- \+/\- *lemma* coeff_reverse
- \+/\- *lemma* coeff_zero_reverse
- \+/\- *lemma* reverse_zero
- \+/\- *lemma* reverse_nat_degree_le
- \+/\- *lemma* nat_degree_eq_reverse_nat_degree_add_nat_trailing_degree
- \+/\- *lemma* reverse_nat_degree
- \+/\- *lemma* reverse_leading_coeff
- \+/\- *lemma* reverse_nat_trailing_degree
- \+/\- *lemma* reverse_trailing_coeff
- \+/\- *lemma* reverse_mul_of_domain
- \+/\- *lemma* trailing_coeff_mul
- \+/\- *lemma* coeff_one_reverse
- \+/\- *lemma* eval₂_reverse_mul_pow
- \+/\- *lemma* eval₂_reverse_eq_zero_iff
- \+/\- *lemma* reflect_neg
- \+/\- *lemma* reflect_sub
- \+/\- *lemma* reverse_neg
- \+/\- *theorem* reverse_mul
- \+/\- *theorem* reverse_mul

modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* nat_degree_pos_of_aeval_root
- \+/\- *lemma* degree_pos_of_aeval_root
- \+/\- *lemma* mod_by_monic_eq_of_dvd_sub
- \+/\- *lemma* nat_degree_pow
- \+/\- *lemma* degree_le_mul_left
- \+/\- *lemma* degree_coe_units
- \+/\- *lemma* root_multiplicity_mul
- \+/\- *lemma* root_multiplicity_of_dvd
- \+/\- *lemma* root_multiplicity_add
- \+/\- *lemma* exists_multiset_roots
- \+/\- *lemma* roots_zero
- \+/\- *lemma* card_roots'
- \+/\- *lemma* card_roots_sub_C
- \+/\- *lemma* card_roots_sub_C'
- \+/\- *lemma* count_roots
- \+/\- *lemma* exists_max_root
- \+/\- *lemma* exists_min_root
- \+/\- *lemma* roots_mul
- \+/\- *lemma* mem_roots_sub_C
- \+/\- *lemma* roots_one
- \+/\- *lemma* roots_smul_nonzero
- \+/\- *lemma* roots_list_prod
- \+/\- *lemma* roots_multiset_prod
- \+/\- *lemma* roots_prod
- \+/\- *lemma* units_coeff_zero_smul
- \+/\- *lemma* nat_degree_coe_units
- \+/\- *lemma* zero_of_eval_zero
- \+/\- *lemma* funext
- \+/\- *lemma* root_set_def
- \+/\- *lemma* root_set_finite
- \+/\- *lemma* coeff_coe_units_zero_ne_zero
- \+/\- *lemma* leading_coeff_div_by_monic_X_sub_C
- \+/\- *lemma* monic.irreducible_of_irreducible_map
- \+/\- *lemma* nat_degree_pos_of_aeval_root
- \+/\- *lemma* degree_pos_of_aeval_root
- \+/\- *lemma* mod_by_monic_eq_of_dvd_sub
- \+/\- *lemma* nat_degree_pow
- \+/\- *lemma* degree_le_mul_left
- \+/\- *lemma* degree_coe_units
- \+/\- *lemma* root_multiplicity_mul
- \+/\- *lemma* root_multiplicity_of_dvd
- \+/\- *lemma* root_multiplicity_add
- \+/\- *lemma* exists_multiset_roots
- \+/\- *lemma* roots_zero
- \+/\- *lemma* card_roots'
- \+/\- *lemma* card_roots_sub_C
- \+/\- *lemma* card_roots_sub_C'
- \+/\- *lemma* count_roots
- \+/\- *lemma* exists_max_root
- \+/\- *lemma* exists_min_root
- \+/\- *lemma* roots_mul
- \+/\- *lemma* mem_roots_sub_C
- \+/\- *lemma* roots_one
- \+/\- *lemma* roots_smul_nonzero
- \+/\- *lemma* roots_list_prod
- \+/\- *lemma* roots_multiset_prod
- \+/\- *lemma* roots_prod
- \+/\- *lemma* units_coeff_zero_smul
- \+/\- *lemma* nat_degree_coe_units
- \+/\- *lemma* zero_of_eval_zero
- \+/\- *lemma* funext
- \+/\- *lemma* root_set_def
- \+/\- *lemma* root_set_finite
- \+/\- *lemma* coeff_coe_units_zero_ne_zero
- \+/\- *lemma* leading_coeff_div_by_monic_X_sub_C
- \+/\- *lemma* monic.irreducible_of_irreducible_map
- \+/\- *theorem* nat_degree_le_of_dvd
- \+/\- *theorem* prime_X
- \+/\- *theorem* irreducible_X
- \+/\- *theorem* card_le_degree_of_subset_roots
- \+/\- *theorem* is_unit_iff
- \+/\- *theorem* nat_degree_le_of_dvd
- \+/\- *theorem* prime_X
- \+/\- *theorem* irreducible_X
- \+/\- *theorem* card_le_degree_of_subset_roots
- \+/\- *theorem* is_unit_iff
- \+/\- *def* root_set
- \+/\- *def* root_set

modified src/data/polynomial/taylor.lean
- \+/\- *lemma* taylor_zero
- \+/\- *lemma* taylor_one
- \+/\- *lemma* nat_degree_taylor
- \+/\- *lemma* taylor_mul
- \+/\- *lemma* taylor_taylor
- \+/\- *lemma* taylor_eval
- \+/\- *lemma* taylor_eval_sub
- \+/\- *lemma* eq_zero_of_hasse_deriv_eq_zero
- \+/\- *lemma* sum_taylor_eq
- \+/\- *lemma* taylor_zero
- \+/\- *lemma* taylor_one
- \+/\- *lemma* nat_degree_taylor
- \+/\- *lemma* taylor_mul
- \+/\- *lemma* taylor_taylor
- \+/\- *lemma* taylor_eval
- \+/\- *lemma* taylor_eval_sub
- \+/\- *lemma* eq_zero_of_hasse_deriv_eq_zero
- \+/\- *lemma* sum_taylor_eq
- \+/\- *def* taylor
- \+/\- *def* taylor

modified src/field_theory/abel_ruffini.lean
- \+/\- *lemma* gal_zero_is_solvable
- \+/\- *lemma* gal_one_is_solvable
- \+/\- *lemma* gal_X_is_solvable
- \+/\- *lemma* gal_X_pow_is_solvable
- \+/\- *lemma* gal_mul_is_solvable
- \+/\- *lemma* gal_prod_is_solvable
- \+/\- *lemma* gal_is_solvable_of_splits
- \+/\- *lemma* gal_is_solvable_tower
- \+/\- *lemma* gal_X_pow_sub_one_is_solvable
- \+/\- *lemma* is_solvable'
- \+/\- *lemma* gal_zero_is_solvable
- \+/\- *lemma* gal_one_is_solvable
- \+/\- *lemma* gal_X_is_solvable
- \+/\- *lemma* gal_X_pow_is_solvable
- \+/\- *lemma* gal_mul_is_solvable
- \+/\- *lemma* gal_prod_is_solvable
- \+/\- *lemma* gal_is_solvable_of_splits
- \+/\- *lemma* gal_is_solvable_tower
- \+/\- *lemma* gal_X_pow_sub_one_is_solvable
- \+/\- *lemma* is_solvable'

modified src/field_theory/adjoin.lean
- \+/\- *lemma* equiv_adjoin_simple_aeval
- \+/\- *lemma* equiv_adjoin_simple_symm_aeval
- \+/\- *lemma* equiv_adjoin_simple_aeval
- \+/\- *lemma* equiv_adjoin_simple_symm_aeval

modified src/field_theory/finite/basic.lean
- \+/\- *lemma* card_image_polynomial_eval
- \+/\- *lemma* exists_root_sum_quadratic
- \+/\- *lemma* X_pow_card_sub_X_ne_zero
- \+/\- *lemma* roots_X_pow_card_sub_X
- \+/\- *lemma* expand_card
- \+/\- *lemma* card_image_polynomial_eval
- \+/\- *lemma* exists_root_sum_quadratic
- \+/\- *lemma* X_pow_card_sub_X_ne_zero
- \+/\- *lemma* roots_X_pow_card_sub_X
- \+/\- *lemma* expand_card

modified src/field_theory/finite/galois_field.lean

modified src/field_theory/galois.lean

modified src/field_theory/intermediate_field.lean

modified src/field_theory/is_alg_closed/algebraic_closure.lean
- \+/\- *theorem* adjoin_monic.exists_root
- \+/\- *theorem* adjoin_monic.exists_root

modified src/field_theory/is_alg_closed/basic.lean
- \+/\- *lemma* roots_eq_zero_iff
- \+/\- *lemma* degree_eq_one_of_irreducible
- \+/\- *lemma* roots_eq_zero_iff
- \+/\- *lemma* degree_eq_one_of_irreducible
- \+/\- *theorem* exists_root
- \+/\- *theorem* of_exists_root
- \+/\- *theorem* exists_root
- \+/\- *theorem* of_exists_root

modified src/field_theory/is_alg_closed/classification.lean

modified src/field_theory/laurent.lean
- \+/\- *lemma* taylor_mem_non_zero_divisors
- \+/\- *lemma* laurent_aux_of_fraction_ring_mk
- \+/\- *lemma* taylor_mem_non_zero_divisors
- \+/\- *lemma* laurent_aux_of_fraction_ring_mk

modified src/field_theory/minpoly.lean
- \+/\- *lemma* min
- \+/\- *lemma* aeval_ne_zero_of_dvd_not_unit_minpoly
- \+/\- *lemma* unique
- \+/\- *lemma* dvd
- \+/\- *lemma* eq_of_irreducible
- \+/\- *lemma* min
- \+/\- *lemma* aeval_ne_zero_of_dvd_not_unit_minpoly
- \+/\- *lemma* unique
- \+/\- *lemma* dvd
- \+/\- *lemma* eq_of_irreducible

modified src/field_theory/normal.lean
- \+/\- *lemma* normal.of_is_splitting_field
- \+/\- *lemma* normal.of_is_splitting_field

modified src/field_theory/polynomial_galois_group.lean
- \+/\- *lemma* mul_splits_in_splitting_field_of_mul
- \+/\- *lemma* splits_ℚ_ℂ
- \+/\- *lemma* card_complex_roots_eq_card_real_add_card_not_gal_inv
- \+/\- *lemma* mul_splits_in_splitting_field_of_mul
- \+/\- *lemma* splits_ℚ_ℂ
- \+/\- *lemma* card_complex_roots_eq_card_real_add_card_not_gal_inv

modified src/field_theory/primitive_element.lean
- \+/\- *lemma* primitive_element_inf_aux_exists_c
- \+/\- *lemma* primitive_element_inf_aux_exists_c

modified src/field_theory/ratfunc.lean
- \+/\- *lemma* lift_on_of_fraction_ring_mk
- \+/\- *lemma* mk_eq_div'
- \+/\- *lemma* mk_zero
- \+/\- *lemma* mk_coe_def
- \+/\- *lemma* mk_def_of_mem
- \+/\- *lemma* mk_def_of_ne
- \+/\- *lemma* mk_eq_localization_mk
- \+/\- *lemma* mk_one'
- \+/\- *lemma* mk_eq_mk
- \+/\- *lemma* lift_on_mk
- \+/\- *lemma* lift_on_condition_of_lift_on'_condition
- \+/\- *lemma* lift_on'_mk
- \+/\- *lemma* of_fraction_ring_add
- \+/\- *lemma* of_fraction_ring_sub
- \+/\- *lemma* of_fraction_ring_neg
- \+/\- *lemma* of_fraction_ring_mul
- \+/\- *lemma* of_fraction_ring_div
- \+/\- *lemma* of_fraction_ring_inv
- \+/\- *lemma* of_fraction_ring_smul
- \+/\- *lemma* to_fraction_ring_smul
- \+/\- *lemma* mk_smul
- \+/\- *lemma* map_apply_of_fraction_ring_mk
- \+/\- *lemma* map_injective
- \+/\- *lemma* coe_map_ring_hom_eq_coe_map
- \+/\- *lemma* lift_monoid_with_zero_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* lift_monoid_with_zero_hom_injective
- \+/\- *lemma* lift_ring_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* lift_ring_hom_injective
- \+/\- *lemma* mk_one
- \+/\- *lemma* of_fraction_ring_algebra_map
- \+/\- *lemma* mk_eq_div
- \+/\- *lemma* div_smul
- \+/\- *lemma* algebra_map_apply
- \+/\- *lemma* algebra_map_injective
- \+/\- *lemma* algebra_map_eq_zero_iff
- \+/\- *lemma* algebra_map_ne_zero
- \+/\- *lemma* coe_map_alg_hom_eq_coe_map
- \+/\- *lemma* lift_alg_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* lift_alg_hom_injective
- \+/\- *lemma* lift_alg_hom_apply_div
- \+/\- *lemma* lift_on_div
- \+/\- *lemma* lift_on'_div
- \+/\- *lemma* of_fraction_ring_mk'
- \+/\- *lemma* num_denom_div
- \+/\- *lemma* num_div
- \+/\- *lemma* num_algebra_map
- \+/\- *lemma* num_div_dvd
- \+/\- *lemma* denom_div
- \+/\- *lemma* denom_algebra_map
- \+/\- *lemma* denom_div_dvd
- \+/\- *lemma* num_mul_eq_mul_denom_iff
- \+/\- *lemma* num_dvd
- \+/\- *lemma* denom_dvd
- \+/\- *lemma* map_denom_ne_zero
- \+/\- *lemma* lift_alg_hom_apply
- \+/\- *lemma* eval_algebra_map
- \+/\- *lemma* lift_on_of_fraction_ring_mk
- \+/\- *lemma* mk_eq_div'
- \+/\- *lemma* mk_zero
- \+/\- *lemma* mk_coe_def
- \+/\- *lemma* mk_def_of_mem
- \+/\- *lemma* mk_def_of_ne
- \+/\- *lemma* mk_eq_localization_mk
- \+/\- *lemma* mk_one'
- \+/\- *lemma* mk_eq_mk
- \+/\- *lemma* lift_on_mk
- \+/\- *lemma* lift_on_condition_of_lift_on'_condition
- \+/\- *lemma* lift_on'_mk
- \+/\- *lemma* of_fraction_ring_add
- \+/\- *lemma* of_fraction_ring_sub
- \+/\- *lemma* of_fraction_ring_neg
- \+/\- *lemma* of_fraction_ring_mul
- \+/\- *lemma* of_fraction_ring_div
- \+/\- *lemma* of_fraction_ring_inv
- \+/\- *lemma* of_fraction_ring_smul
- \+/\- *lemma* to_fraction_ring_smul
- \+/\- *lemma* mk_smul
- \+/\- *lemma* map_apply_of_fraction_ring_mk
- \+/\- *lemma* map_injective
- \+/\- *lemma* coe_map_ring_hom_eq_coe_map
- \+/\- *lemma* lift_monoid_with_zero_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* lift_monoid_with_zero_hom_injective
- \+/\- *lemma* lift_ring_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* lift_ring_hom_injective
- \+/\- *lemma* mk_one
- \+/\- *lemma* of_fraction_ring_algebra_map
- \+/\- *lemma* mk_eq_div
- \+/\- *lemma* div_smul
- \+/\- *lemma* algebra_map_apply
- \+/\- *lemma* algebra_map_injective
- \+/\- *lemma* algebra_map_eq_zero_iff
- \+/\- *lemma* algebra_map_ne_zero
- \+/\- *lemma* coe_map_alg_hom_eq_coe_map
- \+/\- *lemma* lift_alg_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* lift_alg_hom_injective
- \+/\- *lemma* lift_alg_hom_apply_div
- \+/\- *lemma* lift_on_div
- \+/\- *lemma* lift_on'_div
- \+/\- *lemma* of_fraction_ring_mk'
- \+/\- *lemma* num_denom_div
- \+/\- *lemma* num_div
- \+/\- *lemma* num_algebra_map
- \+/\- *lemma* num_div_dvd
- \+/\- *lemma* denom_div
- \+/\- *lemma* denom_algebra_map
- \+/\- *lemma* denom_div_dvd
- \+/\- *lemma* num_mul_eq_mul_denom_iff
- \+/\- *lemma* num_dvd
- \+/\- *lemma* denom_dvd
- \+/\- *lemma* map_denom_ne_zero
- \+/\- *lemma* lift_alg_hom_apply
- \+/\- *lemma* eval_algebra_map
- \+/\- *def* to_fraction_ring_ring_equiv
- \+/\- *def* map
- \+/\- *def* map_ring_hom
- \+/\- *def* lift_monoid_with_zero_hom
- \+/\- *def* lift_ring_hom
- \+/\- *def* map_alg_hom
- \+/\- *def* num_denom
- \+/\- *def* num
- \+/\- *def* denom
- \+/\- *def* X
- \+/\- *def* to_fraction_ring_ring_equiv
- \+/\- *def* map
- \+/\- *def* map_ring_hom
- \+/\- *def* lift_monoid_with_zero_hom
- \+/\- *def* lift_ring_hom
- \+/\- *def* map_alg_hom
- \+/\- *def* num_denom
- \+/\- *def* num
- \+/\- *def* denom
- \+/\- *def* X

modified src/field_theory/separable.lean
- \+/\- *lemma* separable_def
- \+/\- *lemma* separable_def'
- \+/\- *lemma* not_separable_zero
- \+/\- *lemma* separable_one
- \+/\- *lemma* separable_of_subsingleton
- \+/\- *lemma* separable_X
- \+/\- *lemma* separable.of_mul_left
- \+/\- *lemma* separable.of_mul_right
- \+/\- *lemma* separable.of_dvd
- \+/\- *lemma* separable_gcd_left
- \+/\- *lemma* separable_gcd_right
- \+/\- *lemma* separable.is_coprime
- \+/\- *lemma* coe_expand
- \+/\- *lemma* expand_eq_sum
- \+/\- *lemma* monic.expand
- \+/\- *lemma* expand_eval
- \+/\- *lemma* is_unit_of_self_mul_dvd_separable
- \+/\- *lemma* multiplicity_le_one_of_separable
- \+/\- *lemma* separable.squarefree
- \+/\- *lemma* separable.mul
- \+/\- *lemma* separable_prod'
- \+/\- *lemma* separable_prod
- \+/\- *lemma* root_multiplicity_le_one_of_separable
- \+/\- *lemma* count_roots_le_one
- \+/\- *lemma* nodup_roots
- \+/\- *lemma* card_root_set_eq_nat_degree
- \+/\- *lemma* eq_X_sub_C_of_separable_of_root_eq
- \+/\- *lemma* separable_def
- \+/\- *lemma* separable_def'
- \+/\- *lemma* not_separable_zero
- \+/\- *lemma* separable_one
- \+/\- *lemma* separable_of_subsingleton
- \+/\- *lemma* separable_X
- \+/\- *lemma* separable.of_mul_left
- \+/\- *lemma* separable.of_mul_right
- \+/\- *lemma* separable.of_dvd
- \+/\- *lemma* separable_gcd_left
- \+/\- *lemma* separable_gcd_right
- \+/\- *lemma* separable.is_coprime
- \+/\- *lemma* coe_expand
- \+/\- *lemma* expand_eq_sum
- \+/\- *lemma* monic.expand
- \+/\- *lemma* expand_eval
- \+/\- *lemma* is_unit_of_self_mul_dvd_separable
- \+/\- *lemma* multiplicity_le_one_of_separable
- \+/\- *lemma* separable.squarefree
- \+/\- *lemma* separable.mul
- \+/\- *lemma* separable_prod'
- \+/\- *lemma* separable_prod
- \+/\- *lemma* root_multiplicity_le_one_of_separable
- \+/\- *lemma* count_roots_le_one
- \+/\- *lemma* nodup_roots
- \+/\- *lemma* card_root_set_eq_nat_degree
- \+/\- *lemma* eq_X_sub_C_of_separable_of_root_eq
- \+/\- *theorem* separable.of_pow'
- \+/\- *theorem* separable.of_pow
- \+/\- *theorem* separable.map
- \+/\- *theorem* expand_expand
- \+/\- *theorem* expand_mul
- \+/\- *theorem* expand_zero
- \+/\- *theorem* expand_one
- \+/\- *theorem* expand_pow
- \+/\- *theorem* derivative_expand
- \+/\- *theorem* coeff_expand
- \+/\- *theorem* coeff_expand_mul
- \+/\- *theorem* coeff_expand_mul'
- \+/\- *theorem* expand_inj
- \+/\- *theorem* expand_eq_zero
- \+/\- *theorem* expand_eq_C
- \+/\- *theorem* nat_degree_expand
- \+/\- *theorem* map_expand
- \+/\- *theorem* coeff_contract
- \+/\- *theorem* contract_expand
- \+/\- *theorem* expand_contract
- \+/\- *theorem* expand_char
- \+/\- *theorem* map_expand_pow_char
- \+/\- *theorem* of_irreducible_expand
- \+/\- *theorem* of_irreducible_expand_pow
- \+/\- *theorem* separable_iff_derivative_ne_zero
- \+/\- *theorem* separable_map
- \+/\- *theorem* separable_or
- \+/\- *theorem* exists_separable_of_irreducible
- \+/\- *theorem* is_unit_or_eq_zero_of_separable_expand
- \+/\- *theorem* unique_separable_of_irreducible
- \+/\- *theorem* _root_.irreducible.separable
- \+/\- *theorem* separable.of_pow'
- \+/\- *theorem* separable.of_pow
- \+/\- *theorem* separable.map
- \+/\- *theorem* expand_expand
- \+/\- *theorem* expand_mul
- \+/\- *theorem* expand_zero
- \+/\- *theorem* expand_one
- \+/\- *theorem* expand_pow
- \+/\- *theorem* derivative_expand
- \+/\- *theorem* coeff_expand
- \+/\- *theorem* coeff_expand_mul
- \+/\- *theorem* coeff_expand_mul'
- \+/\- *theorem* expand_inj
- \+/\- *theorem* expand_eq_zero
- \+/\- *theorem* expand_eq_C
- \+/\- *theorem* nat_degree_expand
- \+/\- *theorem* map_expand
- \+/\- *theorem* coeff_contract
- \+/\- *theorem* contract_expand
- \+/\- *theorem* expand_contract
- \+/\- *theorem* expand_char
- \+/\- *theorem* map_expand_pow_char
- \+/\- *theorem* of_irreducible_expand
- \+/\- *theorem* of_irreducible_expand_pow
- \+/\- *theorem* separable_iff_derivative_ne_zero
- \+/\- *theorem* separable_map
- \+/\- *theorem* separable_or
- \+/\- *theorem* exists_separable_of_irreducible
- \+/\- *theorem* is_unit_or_eq_zero_of_separable_expand
- \+/\- *theorem* unique_separable_of_irreducible
- \+/\- *theorem* _root_.irreducible.separable
- \+/\- *def* separable
- \+/\- *def* separable

modified src/field_theory/separable_degree.lean
- \+/\- *lemma* has_separable_contraction.eq_degree
- \+/\- *lemma* has_separable_contraction.eq_degree
- \+/\- *def* is_separable_contraction
- \+/\- *def* has_separable_contraction
- \+/\- *def* has_separable_contraction.contraction
- \+/\- *def* is_separable_contraction
- \+/\- *def* has_separable_contraction
- \+/\- *def* has_separable_contraction.contraction

modified src/field_theory/splitting_field.lean
- \+/\- *lemma* splits_zero
- \+/\- *lemma* splits_of_degree_eq_one
- \+/\- *lemma* splits_of_degree_le_one
- \+/\- *lemma* splits_of_nat_degree_le_one
- \+/\- *lemma* splits_of_nat_degree_eq_one
- \+/\- *lemma* splits_mul
- \+/\- *lemma* splits_of_splits_mul
- \+/\- *lemma* splits_of_splits_of_dvd
- \+/\- *lemma* splits_of_splits_gcd_left
- \+/\- *lemma* splits_of_splits_gcd_right
- \+/\- *lemma* splits_map_iff
- \+/\- *lemma* splits_pow
- \+/\- *lemma* degree_eq_one_of_irreducible_of_splits
- \+/\- *lemma* exists_root_of_splits
- \+/\- *lemma* exists_multiset_of_splits
- \+/\- *lemma* eq_prod_roots_of_splits
- \+/\- *lemma* eq_prod_roots_of_splits_id
- \+/\- *lemma* eq_prod_roots_of_monic_of_splits_id
- \+/\- *lemma* eq_X_sub_C_of_splits_of_single_root
- \+/\- *lemma* nat_degree_eq_card_roots
- \+/\- *lemma* degree_eq_card_roots
- \+/\- *lemma* splits_of_exists_multiset
- \+/\- *lemma* splits_of_splits_id
- \+/\- *lemma* splits_iff_exists_multiset
- \+/\- *lemma* splits_comp_of_splits
- \+/\- *lemma* splits_iff_card_roots
- \+/\- *lemma* aeval_root_derivative_of_splits
- \+/\- *lemma* prod_roots_eq_coeff_zero_of_monic_of_split
- \+/\- *lemma* sum_roots_eq_next_coeff_of_monic_of_split
- \+/\- *lemma* splits_zero
- \+/\- *lemma* splits_of_degree_eq_one
- \+/\- *lemma* splits_of_degree_le_one
- \+/\- *lemma* splits_of_nat_degree_le_one
- \+/\- *lemma* splits_of_nat_degree_eq_one
- \+/\- *lemma* splits_mul
- \+/\- *lemma* splits_of_splits_mul
- \+/\- *lemma* splits_of_splits_of_dvd
- \+/\- *lemma* splits_of_splits_gcd_left
- \+/\- *lemma* splits_of_splits_gcd_right
- \+/\- *lemma* splits_map_iff
- \+/\- *lemma* splits_pow
- \+/\- *lemma* degree_eq_one_of_irreducible_of_splits
- \+/\- *lemma* exists_root_of_splits
- \+/\- *lemma* exists_multiset_of_splits
- \+/\- *lemma* eq_prod_roots_of_splits
- \+/\- *lemma* eq_prod_roots_of_splits_id
- \+/\- *lemma* eq_prod_roots_of_monic_of_splits_id
- \+/\- *lemma* eq_X_sub_C_of_splits_of_single_root
- \+/\- *lemma* nat_degree_eq_card_roots
- \+/\- *lemma* degree_eq_card_roots
- \+/\- *lemma* splits_of_exists_multiset
- \+/\- *lemma* splits_of_splits_id
- \+/\- *lemma* splits_iff_exists_multiset
- \+/\- *lemma* splits_comp_of_splits
- \+/\- *lemma* splits_iff_card_roots
- \+/\- *lemma* aeval_root_derivative_of_splits
- \+/\- *lemma* prod_roots_eq_coeff_zero_of_monic_of_split
- \+/\- *lemma* sum_roots_eq_next_coeff_of_monic_of_split
- \+/\- *theorem* splits_of_is_unit
- \+/\- *theorem* splits_id_iff_splits
- \+/\- *theorem* splits_mul_iff
- \+/\- *theorem* splits_prod
- \+/\- *theorem* splits_prod_iff
- \+/\- *theorem* map_root_of_splits
- \+/\- *theorem* roots_map
- \+/\- *theorem* factor_dvd_of_not_is_unit
- \+/\- *theorem* factor_dvd_of_degree_ne_zero
- \+/\- *theorem* factor_dvd_of_nat_degree_ne_zero
- \+/\- *theorem* X_sub_C_mul_remove_factor
- \+/\- *theorem* nat_degree_remove_factor
- \+/\- *theorem* nat_degree_remove_factor'
- \+/\- *theorem* succ
- \+/\- *theorem* algebra_map_succ
- \+/\- *theorem* splits_iff
- \+/\- *theorem* mul
- \+/\- *theorem* finite_dimensional
- \+/\- *theorem* splits_of_is_unit
- \+/\- *theorem* splits_id_iff_splits
- \+/\- *theorem* splits_mul_iff
- \+/\- *theorem* splits_prod
- \+/\- *theorem* splits_prod_iff
- \+/\- *theorem* map_root_of_splits
- \+/\- *theorem* roots_map
- \+/\- *theorem* factor_dvd_of_not_is_unit
- \+/\- *theorem* factor_dvd_of_degree_ne_zero
- \+/\- *theorem* factor_dvd_of_nat_degree_ne_zero
- \+/\- *theorem* X_sub_C_mul_remove_factor
- \+/\- *theorem* nat_degree_remove_factor
- \+/\- *theorem* nat_degree_remove_factor'
- \+/\- *theorem* succ
- \+/\- *theorem* algebra_map_succ
- \+/\- *theorem* splits_iff
- \+/\- *theorem* mul
- \+/\- *theorem* finite_dimensional
- \+/\- *def* splits
- \+/\- *def* root_of_splits
- \+/\- *def* factor
- \+/\- *def* remove_factor
- \+/\- *def* splitting_field_aux
- \+/\- *def* splitting_field
- \+/\- *def* lift
- \+/\- *def* alg_equiv
- \+/\- *def* splits
- \+/\- *def* root_of_splits
- \+/\- *def* factor
- \+/\- *def* remove_factor
- \+/\- *def* splitting_field_aux
- \+/\- *def* splitting_field
- \+/\- *def* lift
- \+/\- *def* alg_equiv

modified src/linear_algebra/charpoly/basic.lean
- \+/\- *def* charpoly
- \+/\- *def* charpoly

modified src/linear_algebra/eigenspace.lean

modified src/linear_algebra/lagrange.lean
- \+/\- *theorem* eq_zero_of_eval_eq_zero
- \+/\- *theorem* eq_of_eval_eq
- \+/\- *theorem* eq_interpolate_of_eval_eq
- \+/\- *theorem* eq_interpolate
- \+/\- *theorem* eq_zero_of_eval_eq_zero
- \+/\- *theorem* eq_of_eval_eq
- \+/\- *theorem* eq_interpolate_of_eval_eq
- \+/\- *theorem* eq_interpolate
- \+/\- *def* basis
- \+/\- *def* interpolate
- \+/\- *def* basis
- \+/\- *def* interpolate

modified src/linear_algebra/matrix/adjugate.lean

modified src/linear_algebra/matrix/charpoly/basic.lean
- \+/\- *def* charmatrix
- \+/\- *def* matrix.charpoly
- \+/\- *def* charmatrix
- \+/\- *def* matrix.charpoly

modified src/linear_algebra/matrix/charpoly/coeff.lean
- \+/\- *lemma* mat_poly_equiv_eval
- \+/\- *lemma* eval_det
- \+/\- *lemma* mat_poly_equiv_eval
- \+/\- *lemma* eval_det

modified src/linear_algebra/matrix/polynomial.lean

modified src/linear_algebra/smodeq.lean

modified src/number_theory/bernoulli_polynomials.lean
- \+/\- *def* bernoulli
- \+/\- *def* bernoulli

modified src/number_theory/class_number/admissible_card_pow_degree.lean
- \+/\- *lemma* exists_eq_polynomial
- \+/\- *lemma* exists_approx_polynomial
- \+/\- *lemma* card_pow_degree_anti_archimedean
- \+/\- *lemma* exists_eq_polynomial
- \+/\- *lemma* exists_approx_polynomial
- \+/\- *lemma* card_pow_degree_anti_archimedean

modified src/number_theory/class_number/function_field.lean

modified src/number_theory/function_field.lean
- \+/\- *def* ring_of_integers
- \+/\- *def* ring_of_integers

modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* mk_eq_mk
- \+/\- *lemma* aeval_eq
- \+/\- *lemma* eval₂_root
- \+/\- *lemma* is_root_root
- \+/\- *lemma* lift_mk
- \+/\- *lemma* lift_hom_eq_alg_hom
- \+/\- *lemma* lift_hom_mk
- \+/\- *lemma* mod_by_monic_hom_mk
- \+/\- *lemma* mk_eq_mk
- \+/\- *lemma* aeval_eq
- \+/\- *lemma* eval₂_root
- \+/\- *lemma* is_root_root
- \+/\- *lemma* lift_mk
- \+/\- *lemma* lift_hom_eq_alg_hom
- \+/\- *lemma* lift_hom_mk
- \+/\- *lemma* mod_by_monic_hom_mk
- \+/\- *def* adjoin_root
- \+/\- *def* mk
- \+/\- *def* equiv
- \+/\- *def* adjoin_root
- \+/\- *def* mk
- \+/\- *def* equiv

modified src/ring_theory/algebraic.lean
- \+/\- *lemma* inv_eq_of_aeval_div_X_ne_zero
- \+/\- *lemma* inv_eq_of_root_of_coeff_zero_ne_zero
- \+/\- *lemma* subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero
- \+/\- *lemma* inv_eq_of_aeval_div_X_ne_zero
- \+/\- *lemma* inv_eq_of_root_of_coeff_zero_ne_zero
- \+/\- *lemma* subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero

modified src/ring_theory/dedekind_domain.lean

modified src/ring_theory/eisenstein_criterion.lean
- \+/\- *lemma* map_eq_C_mul_X_pow_of_forall_coeff_mem
- \+/\- *lemma* is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit
- \+/\- *lemma* map_eq_C_mul_X_pow_of_forall_coeff_mem
- \+/\- *lemma* is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit
- \+/\- *theorem* irreducible_of_eisenstein_criterion
- \+/\- *theorem* irreducible_of_eisenstein_criterion

modified src/ring_theory/finiteness.lean
- \+/\- *lemma* module_polynomial_of_endo.is_scalar_tower
- \+/\- *lemma* module_polynomial_of_endo.is_scalar_tower
- \+/\- *def* module_polynomial_of_endo
- \+/\- *def* module_polynomial_of_endo

modified src/ring_theory/free_comm_ring.lean

modified src/ring_theory/hahn_series.lean
- \+/\- *lemma* _root_.polynomial.algebra_map_hahn_series_apply
- \+/\- *lemma* _root_.polynomial.algebra_map_hahn_series_apply

modified src/ring_theory/henselian.lean

modified src/ring_theory/ideal/over.lean
- \+/\- *lemma* coeff_zero_mem_comap_of_root_mem_of_eval_mem
- \+/\- *lemma* coeff_zero_mem_comap_of_root_mem
- \+/\- *lemma* injective_quotient_le_comap_map
- \+/\- *lemma* quotient_mk_maps_eq
- \+/\- *lemma* exists_nonzero_mem_of_ne_bot
- \+/\- *lemma* coeff_zero_mem_comap_of_root_mem_of_eval_mem
- \+/\- *lemma* coeff_zero_mem_comap_of_root_mem
- \+/\- *lemma* injective_quotient_le_comap_map
- \+/\- *lemma* quotient_mk_maps_eq
- \+/\- *lemma* exists_nonzero_mem_of_ne_bot

modified src/ring_theory/integral_closure.lean
- \+/\- *lemma* leading_coeff_smul_normalize_scale_roots
- \+/\- *lemma* is_integral_trans_aux
- \+/\- *lemma* leading_coeff_smul_normalize_scale_roots
- \+/\- *lemma* is_integral_trans_aux
- \+/\- *def* normalize_scale_roots
- \+/\- *def* normalize_scale_roots

modified src/ring_theory/jacobson.lean

modified src/ring_theory/jacobson_ideal.lean

modified src/ring_theory/laurent_series.lean
- \+ *lemma* coe_sub
- \+ *lemma* coe_neg

modified src/ring_theory/localization.lean
- \+/\- *lemma* coeff_integer_normalization_of_not_mem_support
- \+/\- *lemma* coeff_integer_normalization_mem_support
- \+/\- *lemma* integer_normalization_coeff
- \+/\- *lemma* integer_normalization_spec
- \+/\- *lemma* integer_normalization_map_to_map
- \+/\- *lemma* integer_normalization_eval₂_eq_zero
- \+/\- *lemma* integer_normalization_eq_zero_iff
- \+/\- *lemma* coeff_integer_normalization_of_not_mem_support
- \+/\- *lemma* coeff_integer_normalization_mem_support
- \+/\- *lemma* integer_normalization_coeff
- \+/\- *lemma* integer_normalization_spec
- \+/\- *lemma* integer_normalization_map_to_map
- \+/\- *lemma* integer_normalization_eval₂_eq_zero
- \+/\- *lemma* integer_normalization_eq_zero_iff
- \+/\- *theorem* is_integral_localization_at_leading_coeff
- \+/\- *theorem* is_integral_localization_at_leading_coeff

modified src/ring_theory/mv_polynomial/basic.lean

modified src/ring_theory/polynomial/basic.lean
- \+/\- *lemma* frange_zero
- \+/\- *lemma* mem_frange_iff
- \+/\- *lemma* frange_one
- \+/\- *lemma* coeff_mem_frange
- \+/\- *lemma* support_restriction
- \+/\- *lemma* coeff_of_subring
- \+/\- *lemma* mem_ker_mod_by_monic
- \+/\- *lemma* polynomial_mem_ideal_of_coeff_mem_ideal
- \+/\- *lemma* polynomial_quotient_equiv_quotient_polynomial_symm_mk
- \+/\- *lemma* polynomial_quotient_equiv_quotient_polynomial_map_mk
- \+/\- *lemma* eq_zero_of_polynomial_mem_map_range
- \+/\- *lemma* polynomial_not_is_field
- \+/\- *lemma* sup_ker_aeval_le_ker_aeval_mul
- \+/\- *lemma* frange_zero
- \+/\- *lemma* mem_frange_iff
- \+/\- *lemma* frange_one
- \+/\- *lemma* coeff_mem_frange
- \+/\- *lemma* support_restriction
- \+/\- *lemma* coeff_of_subring
- \+/\- *lemma* mem_ker_mod_by_monic
- \+/\- *lemma* polynomial_mem_ideal_of_coeff_mem_ideal
- \+/\- *lemma* polynomial_quotient_equiv_quotient_polynomial_symm_mk
- \+/\- *lemma* polynomial_quotient_equiv_quotient_polynomial_map_mk
- \+/\- *lemma* eq_zero_of_polynomial_mem_map_range
- \+/\- *lemma* polynomial_not_is_field
- \+/\- *lemma* sup_ker_aeval_le_ker_aeval_mul
- \+/\- *theorem* mem_degree_le
- \+/\- *theorem* mem_degree_lt
- \+/\- *theorem* coeff_restriction
- \+/\- *theorem* coeff_restriction'
- \+/\- *theorem* map_restriction
- \+/\- *theorem* degree_restriction
- \+/\- *theorem* nat_degree_restriction
- \+/\- *theorem* monic_restriction
- \+/\- *theorem* restriction_zero
- \+/\- *theorem* restriction_one
- \+/\- *theorem* eval₂_restriction
- \+/\- *theorem* to_subring_zero
- \+/\- *theorem* to_subring_one
- \+/\- *theorem* frange_of_subring
- \+/\- *theorem* mem_map_C_iff
- \+/\- *theorem* mem_degree_le
- \+/\- *theorem* mem_degree_lt
- \+/\- *theorem* coeff_restriction
- \+/\- *theorem* coeff_restriction'
- \+/\- *theorem* map_restriction
- \+/\- *theorem* degree_restriction
- \+/\- *theorem* nat_degree_restriction
- \+/\- *theorem* monic_restriction
- \+/\- *theorem* restriction_zero
- \+/\- *theorem* restriction_one
- \+/\- *theorem* eval₂_restriction
- \+/\- *theorem* to_subring_zero
- \+/\- *theorem* to_subring_one
- \+/\- *theorem* frange_of_subring
- \+/\- *theorem* mem_map_C_iff
- \+/\- *def* degree_le
- \+/\- *def* degree_lt
- \+/\- *def* frange
- \+/\- *def* restriction
- \+/\- *def* to_subring
- \+/\- *def* of_subring
- \+/\- *def* of_polynomial
- \+/\- *def* degree_le
- \+/\- *def* degree_le
- \+/\- *def* degree_lt
- \+/\- *def* frange
- \+/\- *def* restriction
- \+/\- *def* to_subring
- \+/\- *def* of_subring
- \+/\- *def* of_polynomial
- \+/\- *def* degree_le

modified src/ring_theory/polynomial/bernstein.lean
- \+/\- *def* bernstein_polynomial
- \+/\- *def* bernstein_polynomial

modified src/ring_theory/polynomial/chebyshev.lean

modified src/ring_theory/polynomial/content.lean
- \+/\- *lemma* is_primitive_iff_is_unit_of_C_dvd
- \+/\- *lemma* is_primitive_one
- \+/\- *lemma* monic.is_primitive
- \+/\- *lemma* is_primitive.ne_zero
- \+/\- *lemma* content_dvd_coeff
- \+/\- *lemma* content_zero
- \+/\- *lemma* content_one
- \+/\- *lemma* content_X_mul
- \+/\- *lemma* content_X_pow
- \+/\- *lemma* content_X
- \+/\- *lemma* content_C_mul
- \+/\- *lemma* content_eq_zero_iff
- \+/\- *lemma* normalize_content
- \+/\- *lemma* content_eq_gcd_range_of_lt
- \+/\- *lemma* content_eq_gcd_range_succ
- \+/\- *lemma* content_eq_gcd_leading_coeff_content_erase_lead
- \+/\- *lemma* dvd_content_iff_C_dvd
- \+/\- *lemma* C_content_dvd
- \+/\- *lemma* is_primitive_iff_content_eq_one
- \+/\- *lemma* is_primitive.content_eq_one
- \+/\- *lemma* eq_C_content_mul_prim_part
- \+/\- *lemma* prim_part_zero
- \+/\- *lemma* is_primitive_prim_part
- \+/\- *lemma* content_prim_part
- \+/\- *lemma* prim_part_ne_zero
- \+/\- *lemma* nat_degree_prim_part
- \+/\- *lemma* is_primitive.prim_part_eq
- \+/\- *lemma* prim_part_dvd
- \+/\- *lemma* gcd_content_eq_of_dvd_sub
- \+/\- *lemma* content_mul_aux
- \+/\- *lemma* is_primitive.is_primitive_of_dvd
- \+/\- *lemma* is_primitive.dvd_prim_part_iff_dvd
- \+/\- *lemma* degree_gcd_le_left
- \+/\- *lemma* degree_gcd_le_right
- \+/\- *lemma* is_primitive_iff_is_unit_of_C_dvd
- \+/\- *lemma* is_primitive_one
- \+/\- *lemma* monic.is_primitive
- \+/\- *lemma* is_primitive.ne_zero
- \+/\- *lemma* content_dvd_coeff
- \+/\- *lemma* content_zero
- \+/\- *lemma* content_one
- \+/\- *lemma* content_X_mul
- \+/\- *lemma* content_X_pow
- \+/\- *lemma* content_X
- \+/\- *lemma* content_C_mul
- \+/\- *lemma* content_eq_zero_iff
- \+/\- *lemma* normalize_content
- \+/\- *lemma* content_eq_gcd_range_of_lt
- \+/\- *lemma* content_eq_gcd_range_succ
- \+/\- *lemma* content_eq_gcd_leading_coeff_content_erase_lead
- \+/\- *lemma* dvd_content_iff_C_dvd
- \+/\- *lemma* C_content_dvd
- \+/\- *lemma* is_primitive_iff_content_eq_one
- \+/\- *lemma* is_primitive.content_eq_one
- \+/\- *lemma* eq_C_content_mul_prim_part
- \+/\- *lemma* prim_part_zero
- \+/\- *lemma* is_primitive_prim_part
- \+/\- *lemma* content_prim_part
- \+/\- *lemma* prim_part_ne_zero
- \+/\- *lemma* nat_degree_prim_part
- \+/\- *lemma* is_primitive.prim_part_eq
- \+/\- *lemma* prim_part_dvd
- \+/\- *lemma* gcd_content_eq_of_dvd_sub
- \+/\- *lemma* content_mul_aux
- \+/\- *lemma* is_primitive.is_primitive_of_dvd
- \+/\- *lemma* is_primitive.dvd_prim_part_iff_dvd
- \+/\- *lemma* degree_gcd_le_left
- \+/\- *lemma* degree_gcd_le_right
- \+/\- *theorem* content_mul
- \+/\- *theorem* is_primitive.mul
- \+/\- *theorem* prim_part_mul
- \+/\- *theorem* exists_primitive_lcm_of_is_primitive
- \+/\- *theorem* content_mul
- \+/\- *theorem* is_primitive.mul
- \+/\- *theorem* prim_part_mul
- \+/\- *theorem* exists_primitive_lcm_of_is_primitive
- \+/\- *def* is_primitive
- \+/\- *def* content
- \+/\- *def* prim_part
- \+/\- *def* is_primitive
- \+/\- *def* content
- \+/\- *def* prim_part

modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+/\- *lemma* int_cyclotomic_unique
- \+/\- *lemma* int_cyclotomic_unique
- \+/\- *def* cyclotomic'
- \+/\- *def* cyclotomic
- \+/\- *def* cyclotomic'
- \+/\- *def* cyclotomic

modified src/ring_theory/polynomial/dickson.lean

modified src/ring_theory/polynomial/eisenstein.lean

modified src/ring_theory/polynomial/gauss_lemma.lean
- \+/\- *lemma* is_primitive.is_unit_iff_is_unit_map
- \+/\- *lemma* is_primitive.dvd_of_fraction_map_dvd_fraction_map
- \+/\- *lemma* is_primitive.dvd_iff_fraction_map_dvd_fraction_map
- \+/\- *lemma* is_primitive.int.dvd_iff_map_cast_dvd_map_cast
- \+/\- *lemma* is_primitive.is_unit_iff_is_unit_map
- \+/\- *lemma* is_primitive.dvd_of_fraction_map_dvd_fraction_map
- \+/\- *lemma* is_primitive.dvd_iff_fraction_map_dvd_fraction_map
- \+/\- *lemma* is_primitive.int.dvd_iff_map_cast_dvd_map_cast

modified src/ring_theory/polynomial/pochhammer.lean
- \+/\- *lemma* polynomial.mul_X_add_nat_cast_comp
- \+/\- *lemma* polynomial.mul_X_add_nat_cast_comp

modified src/ring_theory/polynomial/rational_root.lean
- \+/\- *lemma* scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero
- \+/\- *lemma* scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero
- \+/\- *theorem* num_dvd_of_is_root
- \+/\- *theorem* denom_dvd_of_is_root
- \+/\- *theorem* is_integer_of_is_root_of_monic
- \+/\- *theorem* num_dvd_of_is_root
- \+/\- *theorem* denom_dvd_of_is_root
- \+/\- *theorem* is_integer_of_is_root_of_monic

modified src/ring_theory/polynomial/scale_roots.lean
- \+/\- *lemma* coeff_scale_roots
- \+/\- *lemma* coeff_scale_roots_nat_degree
- \+/\- *lemma* scale_roots_ne_zero
- \+/\- *lemma* support_scale_roots_le
- \+/\- *lemma* support_scale_roots_eq
- \+/\- *lemma* degree_scale_roots
- \+/\- *lemma* nat_degree_scale_roots
- \+/\- *lemma* monic_scale_roots_iff
- \+/\- *lemma* scale_roots_eval₂_eq_zero
- \+/\- *lemma* scale_roots_aeval_eq_zero
- \+/\- *lemma* coeff_scale_roots
- \+/\- *lemma* coeff_scale_roots_nat_degree
- \+/\- *lemma* scale_roots_ne_zero
- \+/\- *lemma* support_scale_roots_le
- \+/\- *lemma* support_scale_roots_eq
- \+/\- *lemma* degree_scale_roots
- \+/\- *lemma* nat_degree_scale_roots
- \+/\- *lemma* monic_scale_roots_iff
- \+/\- *lemma* scale_roots_eval₂_eq_zero
- \+/\- *lemma* scale_roots_aeval_eq_zero

modified src/ring_theory/polynomial/tower.lean
- \+/\- *lemma* algebra_map_aeval
- \+/\- *lemma* aeval_eq_zero_of_aeval_algebra_map_eq_zero
- \+/\- *lemma* aeval_coe
- \+/\- *lemma* algebra_map_aeval
- \+/\- *lemma* aeval_eq_zero_of_aeval_algebra_map_eq_zero
- \+/\- *lemma* aeval_coe
- \+/\- *theorem* aeval_apply
- \+/\- *theorem* aeval_apply

modified src/ring_theory/polynomial/vieta.lean

modified src/ring_theory/polynomial_algebra.lean
- \+/\- *lemma* to_fun_bilinear_apply_eq_sum
- \+/\- *lemma* to_fun_linear_tmul_apply
- \+/\- *lemma* to_fun_linear_mul_tmul_mul_aux_2
- \+/\- *lemma* to_fun_linear_mul_tmul_mul
- \+/\- *lemma* to_fun_alg_hom_apply_tmul
- \+/\- *lemma* left_inv
- \+/\- *lemma* right_inv
- \+/\- *lemma* poly_equiv_tensor_apply
- \+/\- *lemma* poly_equiv_tensor_symm_apply_tmul
- \+/\- *lemma* mat_poly_equiv_smul_one
- \+/\- *lemma* to_fun_bilinear_apply_eq_sum
- \+/\- *lemma* to_fun_linear_tmul_apply
- \+/\- *lemma* to_fun_linear_mul_tmul_mul_aux_2
- \+/\- *lemma* to_fun_linear_mul_tmul_mul
- \+/\- *lemma* to_fun_alg_hom_apply_tmul
- \+/\- *lemma* left_inv
- \+/\- *lemma* right_inv
- \+/\- *lemma* poly_equiv_tensor_apply
- \+/\- *lemma* poly_equiv_tensor_symm_apply_tmul
- \+/\- *lemma* mat_poly_equiv_smul_one
- \+/\- *def* to_fun_bilinear
- \+/\- *def* to_fun_linear
- \+/\- *def* to_fun_alg_hom
- \+/\- *def* inv_fun
- \+/\- *def* equiv
- \+/\- *def* poly_equiv_tensor
- \+/\- *def* to_fun_bilinear
- \+/\- *def* to_fun_linear
- \+/\- *def* to_fun_alg_hom
- \+/\- *def* inv_fun
- \+/\- *def* equiv
- \+/\- *def* poly_equiv_tensor

modified src/ring_theory/power_basis.lean
- \+/\- *lemma* dim_le_nat_degree_of_root
- \+/\- *lemma* dim_le_degree_of_root
- \+/\- *lemma* nat_degree_lt_nat_degree
- \+/\- *lemma* dim_le_nat_degree_of_root
- \+/\- *lemma* dim_le_degree_of_root
- \+/\- *lemma* nat_degree_lt_nat_degree

modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* map_X
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_injective
- \+/\- *lemma* algebra_map_apply'
- \+/\- *lemma* map_X
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_injective
- \+/\- *lemma* algebra_map_apply'
- \+/\- *def* trunc
- \+/\- *def* coe_to_power_series.ring_hom
- \+/\- *def* coe_to_power_series.alg_hom
- \+/\- *def* trunc
- \+/\- *def* coe_to_power_series.ring_hom
- \+/\- *def* coe_to_power_series.alg_hom

modified src/ring_theory/roots_of_unity.lean

modified src/topology/algebra/polynomial.lean
- \+/\- *lemma* tendsto_norm_at_top
- \+/\- *lemma* exists_forall_norm_le
- \+/\- *lemma* tendsto_norm_at_top
- \+/\- *lemma* exists_forall_norm_le

modified src/topology/continuous_function/polynomial.lean
- \+/\- *lemma* aeval_continuous_map_apply
- \+/\- *lemma* aeval_continuous_map_apply
- \+/\- *def* to_continuous_map
- \+/\- *def* to_continuous_map_on
- \+/\- *def* to_continuous_map_alg_hom
- \+/\- *def* to_continuous_map_on_alg_hom
- \+/\- *def* to_continuous_map
- \+/\- *def* to_continuous_map_on
- \+/\- *def* to_continuous_map_alg_hom
- \+/\- *def* to_continuous_map_on_alg_hom

modified test/differentiable.lean

modified test/instance_diamonds.lean

modified test/library_search/ring_theory.lean



## [2022-02-08 09:20:10](https://github.com/leanprover-community/mathlib/commit/5932581)
feat(group_theory/submonoid/operations): prod_le_iff and le_prod_iff, also for groups and modules ([#11898](https://github.com/leanprover-community/mathlib/pull/11898))
#### Estimated changes
modified src/algebra/module/submodule.lean
- \+ *lemma* to_add_submonoid_le
- \+ *lemma* to_add_subgroup_le

modified src/group_theory/subgroup/basic.lean
- \+ *lemma* map_one_eq_bot
- \+ *lemma* le_prod_iff
- \+ *lemma* prod_le_iff
- \+ *lemma* prod_eq_bot_iff

modified src/group_theory/submonoid/operations.lean
- \+ *lemma* le_prod_iff
- \+ *lemma* prod_le_iff
- \+ *lemma* mker_inl
- \+ *lemma* mker_inr
- \+ *lemma* prod_eq_bot_iff
- \+ *lemma* prod_eq_top_iff

modified src/linear_algebra/prod.lean
- \+ *lemma* le_prod_iff
- \+ *lemma* prod_le_iff
- \+ *lemma* prod_eq_bot_iff
- \+ *lemma* prod_eq_top_iff

modified src/order/galois_connection.lean
- \+ *lemma* le_iff_le



## [2022-02-08 08:51:03](https://github.com/leanprover-community/mathlib/commit/2b68801)
refactor(number_theory/bernoulli_polynomials): improve names ([#11805](https://github.com/leanprover-community/mathlib/pull/11805))
Cleanup the bernoulli_polynomials file
#### Estimated changes
modified src/number_theory/bernoulli_polynomials.lean
- \+ *lemma* bernoulli_def
- \+ *lemma* bernoulli_zero
- \+ *lemma* bernoulli_eval_zero
- \+ *lemma* bernoulli_eval_one
- \- *lemma* bernoulli_poly_def
- \- *lemma* bernoulli_poly_zero
- \- *lemma* bernoulli_poly_eval_zero
- \- *lemma* bernoulli_poly_eval_one
- \+ *theorem* sum_bernoulli
- \+ *theorem* bernoulli_generating_function
- \- *theorem* sum_bernoulli_poly
- \- *theorem* exp_bernoulli_poly'
- \+ *def* bernoulli
- \- *def* bernoulli_poly



## [2022-02-08 04:53:51](https://github.com/leanprover-community/mathlib/commit/1077eb3)
feat(analysis/complex): a few lemmas about `dist` and `conj` ([#11913](https://github.com/leanprover-community/mathlib/pull/11913))
#### Estimated changes
modified src/analysis/complex/basic.lean
- \+ *lemma* dist_self_conj
- \+ *lemma* dist_conj_self
- \+ *lemma* dist_conj_conj
- \+ *lemma* dist_conj_comm



## [2022-02-07 20:25:46](https://github.com/leanprover-community/mathlib/commit/36d3b68)
feat(linear_algebra/basis): `basis.map_equiv_fun` ([#11888](https://github.com/leanprover-community/mathlib/pull/11888))
Add a `simp` lemma about the effect of `equiv_fun` for a basis
obtained with `basis.map`.
#### Estimated changes
modified src/linear_algebra/basis.lean
- \+ *lemma* basis.map_equiv_fun



## [2022-02-07 19:33:57](https://github.com/leanprover-community/mathlib/commit/f94b0b3)
style(analysis/special_functions/trigonometric/angle): make types of `sin` and `cos` explicit ([#11902](https://github.com/leanprover-community/mathlib/pull/11902))
Give the types of the results of `real.angle.sin` and `real.angle.cos`
explicitly, as requested by @eric-wieser in [#11887](https://github.com/leanprover-community/mathlib/pull/11887).
#### Estimated changes
modified src/analysis/special_functions/trigonometric/angle.lean
- \+/\- *def* sin
- \+/\- *def* cos
- \+/\- *def* sin
- \+/\- *def* cos



## [2022-02-07 19:33:56](https://github.com/leanprover-community/mathlib/commit/9ceb3c2)
feat(topology/sheaf_condition): connect sheaves on sites and on spaces without has_products ([#11706](https://github.com/leanprover-community/mathlib/pull/11706))
As an application of [#11692](https://github.com/leanprover-community/mathlib/pull/11692), show that the is_sheaf_opens_le_cover sheaf condition on spaces is equivalent to is_sheaf on sites, thereby connecting sheaves on sites and on spaces without the value category has_products for the first time. (@justus-springer: you might want to take a look so as to determine whether and which of your work in [#9609](https://github.com/leanprover-community/mathlib/pull/9609) should be deprecated.) This could be seen as a step towards refactoring sheaves on spaces through sheaves on sites.
- [x] depends on: [#11692](https://github.com/leanprover-community/mathlib/pull/11692)
#### Estimated changes
modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean
- \+ *lemma* is_sheaf_sites_iff_is_sheaf_opens_le_cover
- \+ *def* generate_equivalence_opens_le
- \+ *def* whisker_iso_map_generate_cocone
- \+ *def* is_limit_opens_le_equiv_generate₁
- \+ *def* is_limit_opens_le_equiv_generate₂

modified src/topology/sheaves/sheaf_condition/sites.lean
- \+ *lemma* covering_presieve_eq_self
- \+ *def* presieve_of_covering_aux
- \+/\- *def* presieve_of_covering
- \+/\- *def* presieve_of_covering



## [2022-02-07 17:28:22](https://github.com/leanprover-community/mathlib/commit/436966c)
chore(data/finsupp/basic): generalize comap_mul_action ([#11900](https://github.com/leanprover-community/mathlib/pull/11900))
This new definition is propoitionally equal to the old one in the presence of `[group G]` (all the previous `lemma`s continue to apply), but generalizes to `[monoid G]`.
This also removes `finsupp.comap_distrib_mul_action_self` as there is no need to have this as a separate definition.
#### Estimated changes
modified src/algebra/monoid_algebra/basic.lean

modified src/data/finsupp/basic.lean
- \+ *lemma* comap_smul_def
- \+/\- *lemma* comap_smul_single
- \+/\- *lemma* comap_smul_apply
- \+/\- *lemma* comap_smul_single
- \+/\- *lemma* comap_smul_apply
- \- *def* comap_distrib_mul_action_self

modified src/group_theory/group_action/defs.lean
- \+ *lemma* one_smul_eq_id
- \+ *lemma* comp_smul_left



## [2022-02-07 17:28:21](https://github.com/leanprover-community/mathlib/commit/7b91f00)
feat(algebra/big_operators/basic): add multiset.prod_sum ([#11885](https://github.com/leanprover-community/mathlib/pull/11885))
#### Estimated changes
modified src/algebra/big_operators/basic.lean
- \+ *lemma* prod_sum



## [2022-02-07 15:42:07](https://github.com/leanprover-community/mathlib/commit/02c9d69)
feat(analysis/inner_product_space/basic): `orthonormal.map_linear_isometry_equiv` ([#11893](https://github.com/leanprover-community/mathlib/pull/11893))
Add a variant of `orthonormal.comp_linear_isometry_equiv` for the case
of an orthonormal basis mapped with `basis.map`.
If in future we get a bundled type of orthonormal bases with its own
`map` operation, this would no longer be a separate lemma, but until
then it's useful.
#### Estimated changes
modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* orthonormal.map_linear_isometry_equiv



## [2022-02-07 15:42:06](https://github.com/leanprover-community/mathlib/commit/c61ea33)
feat(analysis/complex/isometry): `rotation_symm` ([#11891](https://github.com/leanprover-community/mathlib/pull/11891))
Add a `simp` lemma that the inverse of `rotation` is rotation by the
inverse angle.
#### Estimated changes
modified src/analysis/complex/isometry.lean
- \+ *lemma* rotation_symm



## [2022-02-07 15:42:04](https://github.com/leanprover-community/mathlib/commit/2364a09)
feat(analysis/complex/circle): `exp_map_circle_neg` ([#11889](https://github.com/leanprover-community/mathlib/pull/11889))
Add the lemma `exp_map_circle_neg`, similar to other lemmas for
`exp_map_circle` that are already present.
#### Estimated changes
modified src/analysis/complex/circle.lean
- \+ *lemma* exp_map_circle_neg



## [2022-02-07 15:42:03](https://github.com/leanprover-community/mathlib/commit/99215e3)
feat(analysis/special_functions/trigonometric/angle): `sin`, `cos` ([#11887](https://github.com/leanprover-community/mathlib/pull/11887))
Add definitions of `sin` and `cos` that act on a `real.angle`.
#### Estimated changes
modified src/analysis/special_functions/trigonometric/angle.lean
- \+ *lemma* sin_coe
- \+ *lemma* cos_coe
- \+ *def* sin
- \+ *def* cos



## [2022-02-07 15:42:01](https://github.com/leanprover-community/mathlib/commit/98ef84e)
feat(analysis/special_functions/trigonometric/angle): `induction_on` ([#11886](https://github.com/leanprover-community/mathlib/pull/11886))
Add `real.angle.induction_on`, for use in deducing results for
`real.angle` from those for `ℝ`.
#### Estimated changes
modified src/analysis/special_functions/trigonometric/angle.lean



## [2022-02-07 15:42:00](https://github.com/leanprover-community/mathlib/commit/26179cc)
feat(data/list): add some lemmas. ([#11879](https://github.com/leanprover-community/mathlib/pull/11879))
#### Estimated changes
modified src/data/list/basic.lean
- \+ *theorem* filter_length_eq_length

modified src/data/list/count.lean
- \+ *lemma* countp_eq_length
- \+ *lemma* count_eq_length



## [2022-02-07 15:41:58](https://github.com/leanprover-community/mathlib/commit/dcbb59c)
feat(category_theory/limits): is_limit.exists_unique ([#11875](https://github.com/leanprover-community/mathlib/pull/11875))
Yet another restatement of the limit property which is occasionally useful.
#### Estimated changes
modified src/category_theory/limits/has_limits.lean
- \+ *lemma* limit.exists_unique
- \+ *lemma* colimit.exists_unique

modified src/category_theory/limits/is_limit.lean
- \+ *lemma* exists_unique
- \+ *lemma* exists_unique
- \+ *def* of_exists_unique
- \+ *def* of_exists_unique

modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* fork.is_limit.exists_unique
- \+ *lemma* cofork.is_colimit.exists_unique
- \+ *lemma* equalizer.exists_unique
- \+ *lemma* coequalizer.exists_unique
- \+ *def* fork.is_limit.of_exists_unique
- \+ *def* cofork.is_colimit.of_exists_unique



## [2022-02-07 15:41:57](https://github.com/leanprover-community/mathlib/commit/556483f)
feat(category_theory/limits): (co)equalizers in the opposite category ([#11874](https://github.com/leanprover-community/mathlib/pull/11874))
#### Estimated changes
modified src/category_theory/limits/opposites.lean
- \+ *lemma* has_equalizers_opposite
- \+ *lemma* has_coequalizers_opposite



## [2022-02-07 15:41:55](https://github.com/leanprover-community/mathlib/commit/7a2a546)
feat(data/set/opposite): the opposite of a set ([#11860](https://github.com/leanprover-community/mathlib/pull/11860))
#### Estimated changes
created src/data/set/opposite.lean
- \+ *lemma* mem_op
- \+ *lemma* op_mem_op
- \+ *lemma* mem_unop
- \+ *lemma* unop_mem_unop
- \+ *lemma* op_unop
- \+ *lemma* unop_op
- \+ *lemma* singleton_op
- \+ *lemma* singleton_unop
- \+ *lemma* singleton_op_unop
- \+ *lemma* singleton_unop_op
- \+ *def* op_equiv



## [2022-02-07 15:41:54](https://github.com/leanprover-community/mathlib/commit/0354e56)
feat(order/complete_lattice): infi_le_iff ([#11810](https://github.com/leanprover-community/mathlib/pull/11810))
Add missing lemma `infi_le_iff {s : ι → α} : infi s ≤ a ↔ (∀ b, (∀ i, b ≤ s i) → b ≤ a)`
Also take the opportunity to restate `Inf_le_iff` to restore consistency with `le_Sup_iff` that was broken in [#10607](https://github.com/leanprover-community/mathlib/pull/10607) and move `le_supr_iff` close to `le_Sup_iff` and remove a couple of unneeded parentheses.
#### Estimated changes
modified src/order/complete_lattice.lean
- \+/\- *lemma* le_Sup_iff
- \+/\- *lemma* le_supr_iff
- \+ *lemma* infi_le_iff
- \+/\- *lemma* le_Sup_iff
- \+/\- *lemma* le_supr_iff
- \+/\- *theorem* Sup_le_iff
- \+/\- *theorem* supr_le_iff
- \+/\- *theorem* Sup_le_iff
- \+/\- *theorem* supr_le_iff



## [2022-02-07 14:32:55](https://github.com/leanprover-community/mathlib/commit/a2f3f55)
chore(algebra/monoid_algebra): generalize lift_nc ([#11881](https://github.com/leanprover-community/mathlib/pull/11881))
The g argument does not need to be a bundled morphism here in the definition.
Instead, we require it be a bundled morphism only in the downstream lemmas, using the new typeclass machinery
#### Estimated changes
modified src/algebra/monoid_algebra/basic.lean
- \+/\- *lemma* lift_nc_single
- \+/\- *lemma* lift_nc_mul
- \+/\- *lemma* lift_nc_one
- \+/\- *lemma* lift_nc_single
- \+/\- *lemma* lift_nc_mul
- \+/\- *lemma* lift_nc_one
- \+/\- *lemma* lift_nc_single
- \+/\- *lemma* lift_nc_one
- \+/\- *lemma* lift_nc_mul
- \+/\- *lemma* lift_nc_single
- \+/\- *lemma* lift_nc_one
- \+/\- *lemma* lift_nc_mul
- \+/\- *def* lift_nc
- \+/\- *def* lift_nc
- \+/\- *def* lift_nc
- \+/\- *def* lift_nc



## [2022-02-07 12:33:08](https://github.com/leanprover-community/mathlib/commit/04b9d28)
feat(data/pfun): Composition of partial functions ([#11865](https://github.com/leanprover-community/mathlib/pull/11865))
Define
* `pfun.id`: The identity as a partial function
* `pfun.comp`: Composition of partial functions
* `pfun.to_subtype`: Restrict the codomain of a function to a subtype and make it partial
#### Estimated changes
modified src/data/part.lean
- \+ *lemma* mem_mk_iff
- \+ *lemma* some_injective
- \+/\- *lemma* some_inj
- \+ *lemma* to_option_eq_none_iff
- \+ *lemma* elim_to_option
- \+ *lemma* dom.of_bind
- \+ *lemma* bind_to_option
- \+/\- *lemma* some_inj

modified src/data/pfun.lean
- \+ *lemma* mem_dom
- \+ *lemma* fn_apply
- \+ *lemma* dom_coe
- \+ *lemma* coe_injective
- \+ *lemma* bind_apply
- \+/\- *lemma* mem_preimage
- \+/\- *lemma* mem_core
- \+ *lemma* dom_to_subtype
- \+ *lemma* to_subtype_apply
- \+ *lemma* dom_to_subtype_apply_iff
- \+ *lemma* mem_to_subtype_iff
- \+ *lemma* coe_id
- \+ *lemma* id_apply
- \+ *lemma* comp_apply
- \+ *lemma* id_comp
- \+ *lemma* comp_id
- \+ *lemma* dom_comp
- \+ *lemma* preimage_comp
- \+ *lemma* _root_.part.bind_comp
- \+ *lemma* comp_assoc
- \+ *lemma* coe_comp
- \+/\- *lemma* mem_preimage
- \+/\- *lemma* mem_core
- \- *theorem* mem_dom
- \+/\- *def* fn
- \+ *def* to_subtype
- \+ *def* comp
- \+/\- *def* fn

modified src/data/subtype.lean
- \+ *lemma* _root_.exists_subtype_mk_eq_iff
- \+ *lemma* _root_.exists_eq_subtype_mk_iff



## [2022-02-07 11:17:01](https://github.com/leanprover-community/mathlib/commit/0090891)
chore(model_theory/*): Split up model_theory/basic ([#11846](https://github.com/leanprover-community/mathlib/pull/11846))
Splits model_theory/basic into separate files: basic, substructures, terms_and_formulas, definability, quotients
Improves documentation throughout
#### Estimated changes
modified src/model_theory/basic.lean
- \- *lemma* closed_under_univ
- \- *lemma* inter
- \- *lemma* inf
- \- *lemma* Inf
- \- *lemma* mem_carrier
- \- *lemma* coe_copy
- \- *lemma* copy_eq
- \- *lemma* const_mem
- \- *lemma* mem_top
- \- *lemma* coe_top
- \- *lemma* coe_inf
- \- *lemma* mem_inf
- \- *lemma* coe_Inf
- \- *lemma* mem_Inf
- \- *lemma* mem_infi
- \- *lemma* coe_infi
- \- *lemma* mem_closure
- \- *lemma* subset_closure
- \- *lemma* not_mem_of_not_mem_closure
- \- *lemma* closed
- \- *lemma* closure_le
- \- *lemma* closure_mono
- \- *lemma* closure_eq_of_le
- \- *lemma* closure_induction
- \- *lemma* dense_induction
- \- *lemma* closure_eq
- \- *lemma* closure_empty
- \- *lemma* closure_univ
- \- *lemma* closure_union
- \- *lemma* closure_Union
- \- *lemma* mem_comap
- \- *lemma* comap_comap
- \- *lemma* comap_id
- \- *lemma* mem_map
- \- *lemma* mem_map_of_mem
- \- *lemma* apply_coe_mem_map
- \- *lemma* map_map
- \- *lemma* map_le_iff_le_comap
- \- *lemma* gc_map_comap
- \- *lemma* map_le_of_le_comap
- \- *lemma* le_comap_of_map_le
- \- *lemma* le_comap_map
- \- *lemma* map_comap_le
- \- *lemma* monotone_map
- \- *lemma* monotone_comap
- \- *lemma* map_comap_map
- \- *lemma* comap_map_comap
- \- *lemma* map_sup
- \- *lemma* map_supr
- \- *lemma* comap_inf
- \- *lemma* comap_infi
- \- *lemma* map_bot
- \- *lemma* comap_top
- \- *lemma* map_id
- \- *lemma* comap_map_eq_of_injective
- \- *lemma* comap_surjective_of_injective
- \- *lemma* map_injective_of_injective
- \- *lemma* comap_inf_map_of_injective
- \- *lemma* comap_infi_map_of_injective
- \- *lemma* comap_sup_map_of_injective
- \- *lemma* comap_supr_map_of_injective
- \- *lemma* map_le_map_iff_of_injective
- \- *lemma* map_strict_mono_of_injective
- \- *lemma* map_comap_eq_of_surjective
- \- *lemma* map_surjective_of_surjective
- \- *lemma* comap_injective_of_surjective
- \- *lemma* map_inf_comap_of_surjective
- \- *lemma* map_infi_comap_of_surjective
- \- *lemma* map_sup_comap_of_surjective
- \- *lemma* map_supr_comap_of_surjective
- \- *lemma* comap_le_comap_iff_of_surjective
- \- *lemma* comap_strict_mono_of_surjective
- \- *lemma* coe_top_equiv
- \- *lemma* closure_induction'
- \- *lemma* eq_on_closure
- \- *lemma* eq_of_eq_on_top
- \- *lemma* eq_of_eq_on_dense
- \- *lemma* realize_term_relabel
- \- *lemma* hom.realize_term
- \- *lemma* embedding.realize_term
- \- *lemma* equiv.realize_term
- \- *lemma* realize_term_substructure
- \- *lemma* realize_not
- \- *lemma* realize_bounded_formula_relabel
- \- *lemma* equiv.realize_bounded_formula
- \- *lemma* realize_bounded_formula_top
- \- *lemma* realize_formula_relabel
- \- *lemma* realize_formula_equiv
- \- *lemma* realize_equal
- \- *lemma* realize_graph
- \- *lemma* is_definable_empty
- \- *lemma* is_definable_univ
- \- *lemma* is_definable.inter
- \- *lemma* is_definable.union
- \- *lemma* is_definable.compl
- \- *lemma* is_definable.sdiff
- \- *lemma* mem_top
- \- *lemma* coe_top
- \- *lemma* not_mem_bot
- \- *lemma* coe_bot
- \- *lemma* le_iff
- \- *lemma* coe_sup
- \- *lemma* mem_sup
- \- *lemma* coe_inf
- \- *lemma* mem_inf
- \- *lemma* mem_compl
- \- *lemma* coe_compl
- \- *lemma* fun_map_quotient_mk
- \- *lemma* realize_term_quotient_mk
- \- *theorem* ext
- \- *theorem* coe_subtype
- \- *def* closed_under
- \- *def* simps.coe
- \- *def* closure
- \- *def* comap
- \- *def* map
- \- *def* gci_map_comap
- \- *def* gi_map_comap
- \- *def* subtype
- \- *def* top_equiv
- \- *def* eq_locus
- \- *def* term.relabel
- \- *def* realize_term
- \- *def* formula
- \- *def* sentence
- \- *def* theory
- \- *def* bd_not
- \- *def* bounded_formula.relabel
- \- *def* equal
- \- *def* graph
- \- *def* realize_bounded_formula
- \- *def* realize_formula
- \- *def* realize_sentence
- \- *def* definable_set

created src/model_theory/definability.lean
- \+ *lemma* is_definable_empty
- \+ *lemma* is_definable_univ
- \+ *lemma* is_definable.inter
- \+ *lemma* is_definable.union
- \+ *lemma* is_definable.compl
- \+ *lemma* is_definable.sdiff
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* not_mem_bot
- \+ *lemma* coe_bot
- \+ *lemma* le_iff
- \+ *lemma* coe_sup
- \+ *lemma* mem_sup
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* mem_compl
- \+ *lemma* coe_compl
- \+ *def* definable_set

modified src/model_theory/elementary_maps.lean
- \+ *lemma* realize_term_substructure
- \+ *lemma* realize_bounded_formula_top

created src/model_theory/quotients.lean
- \+ *lemma* fun_map_quotient_mk
- \+ *lemma* realize_term_quotient_mk

created src/model_theory/substructures.lean
- \+ *lemma* closed_under_univ
- \+ *lemma* inter
- \+ *lemma* inf
- \+ *lemma* Inf
- \+ *lemma* mem_carrier
- \+ *lemma* coe_copy
- \+ *lemma* copy_eq
- \+ *lemma* const_mem
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* coe_Inf
- \+ *lemma* mem_Inf
- \+ *lemma* mem_infi
- \+ *lemma* coe_infi
- \+ *lemma* mem_closure
- \+ *lemma* subset_closure
- \+ *lemma* not_mem_of_not_mem_closure
- \+ *lemma* closed
- \+ *lemma* closure_le
- \+ *lemma* closure_mono
- \+ *lemma* closure_eq_of_le
- \+ *lemma* closure_induction
- \+ *lemma* dense_induction
- \+ *lemma* closure_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_union
- \+ *lemma* closure_Union
- \+ *lemma* mem_comap
- \+ *lemma* comap_comap
- \+ *lemma* comap_id
- \+ *lemma* mem_map
- \+ *lemma* mem_map_of_mem
- \+ *lemma* apply_coe_mem_map
- \+ *lemma* map_map
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *lemma* map_le_of_le_comap
- \+ *lemma* le_comap_of_map_le
- \+ *lemma* le_comap_map
- \+ *lemma* map_comap_le
- \+ *lemma* monotone_map
- \+ *lemma* monotone_comap
- \+ *lemma* map_comap_map
- \+ *lemma* comap_map_comap
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* comap_inf
- \+ *lemma* comap_infi
- \+ *lemma* map_bot
- \+ *lemma* comap_top
- \+ *lemma* map_id
- \+ *lemma* comap_map_eq_of_injective
- \+ *lemma* comap_surjective_of_injective
- \+ *lemma* map_injective_of_injective
- \+ *lemma* comap_inf_map_of_injective
- \+ *lemma* comap_infi_map_of_injective
- \+ *lemma* comap_sup_map_of_injective
- \+ *lemma* comap_supr_map_of_injective
- \+ *lemma* map_le_map_iff_of_injective
- \+ *lemma* map_strict_mono_of_injective
- \+ *lemma* map_comap_eq_of_surjective
- \+ *lemma* map_surjective_of_surjective
- \+ *lemma* comap_injective_of_surjective
- \+ *lemma* map_inf_comap_of_surjective
- \+ *lemma* map_infi_comap_of_surjective
- \+ *lemma* map_sup_comap_of_surjective
- \+ *lemma* map_supr_comap_of_surjective
- \+ *lemma* comap_le_comap_iff_of_surjective
- \+ *lemma* comap_strict_mono_of_surjective
- \+ *lemma* coe_top_equiv
- \+ *lemma* closure_induction'
- \+ *lemma* eq_on_closure
- \+ *lemma* eq_of_eq_on_top
- \+ *lemma* eq_of_eq_on_dense
- \+ *theorem* ext
- \+ *theorem* coe_subtype
- \+ *def* closed_under
- \+ *def* simps.coe
- \+ *def* closure
- \+ *def* comap
- \+ *def* map
- \+ *def* gci_map_comap
- \+ *def* gi_map_comap
- \+ *def* subtype
- \+ *def* top_equiv
- \+ *def* eq_locus

created src/model_theory/terms_and_formulas.lean
- \+ *lemma* realize_term_relabel
- \+ *lemma* hom.realize_term
- \+ *lemma* embedding.realize_term
- \+ *lemma* equiv.realize_term
- \+ *lemma* realize_not
- \+ *lemma* realize_bounded_formula_relabel
- \+ *lemma* equiv.realize_bounded_formula
- \+ *lemma* realize_formula_relabel
- \+ *lemma* realize_formula_equiv
- \+ *lemma* realize_equal
- \+ *lemma* realize_graph
- \+ *def* term.relabel
- \+ *def* realize_term
- \+ *def* formula
- \+ *def* sentence
- \+ *def* theory
- \+ *def* bd_not
- \+ *def* bounded_formula.relabel
- \+ *def* equal
- \+ *def* graph
- \+ *def* realize_bounded_formula
- \+ *def* realize_formula
- \+ *def* realize_sentence



## [2022-02-07 10:17:41](https://github.com/leanprover-community/mathlib/commit/3c70566)
feat(analysis/normed_space/linear_isometry): `symm_trans` ([#11892](https://github.com/leanprover-community/mathlib/pull/11892))
Add a `simp` lemma `linear_isometry_equiv.symm_trans`, like
`coe_symm_trans` but without a coercion involved.  `coe_symm_trans`
can then be proved by `simp`, so stops being a `simp` lemma itself.
#### Estimated changes
modified src/analysis/normed_space/linear_isometry.lean
- \+ *lemma* symm_trans
- \+/\- *lemma* coe_symm_trans
- \+/\- *lemma* coe_symm_trans



## [2022-02-07 08:33:33](https://github.com/leanprover-community/mathlib/commit/b1b09eb)
refactor(data/quot): Make more `setoid` arguments implicit ([#11824](https://github.com/leanprover-community/mathlib/pull/11824))
Currently, not all of the `quotient` API can be used with non-instance setoids. This fixes it by making a few `setoid` arguments explicit rather than instances.
#### Estimated changes
modified src/data/quot.lean
- \+/\- *lemma* quotient.out_equiv_out
- \+/\- *lemma* quotient.out_inj
- \+/\- *lemma* quotient.out_equiv_out
- \+/\- *lemma* quotient.out_inj

modified src/group_theory/schur_zassenhaus.lean



## [2022-02-07 03:57:45](https://github.com/leanprover-community/mathlib/commit/25297ec)
feat(analysis/complex/basic): `conj_lie_symm` ([#11890](https://github.com/leanprover-community/mathlib/pull/11890))
Add a `simp` lemma that the inverse of `conj_lie` is `conj_lie`.
#### Estimated changes
modified src/analysis/complex/basic.lean
- \+ *lemma* conj_lie_symm



## [2022-02-06 19:03:43](https://github.com/leanprover-community/mathlib/commit/e18972b)
feat(set_theory/ordinal_arithmetic): Suprema of empty families ([#11872](https://github.com/leanprover-community/mathlib/pull/11872))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *lemma* lsub_empty
- \+ *lemma* blsub_zero
- \- *lemma* lsub_eq_zero
- \- *lemma* blsub_eq_zero
- \+ *theorem* sup_empty
- \+ *theorem* bsup_zero



## [2022-02-06 07:25:14](https://github.com/leanprover-community/mathlib/commit/24ebc5c)
feat(group_theory/sylow): the cardinality of a sylow group ([#11776](https://github.com/leanprover-community/mathlib/pull/11776))
#### Estimated changes
modified src/algebra/is_prime_pow.lean

modified src/data/nat/factorization.lean
- \+ *lemma* prime.pow_dvd_iff_le_factorization
- \+ *lemma* prime.pow_dvd_iff_dvd_pow_factorization
- \- *lemma* prime_pow_dvd_iff_le_factorization

modified src/group_theory/sylow.lean
- \+ *lemma* card_eq_multiplicity



## [2022-02-06 01:53:58](https://github.com/leanprover-community/mathlib/commit/4148990)
feat(set_theory/ordinal_arithmetic): Suprema and least strict upper bounds of constant families ([#11862](https://github.com/leanprover-community/mathlib/pull/11862))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* sup_const
- \+ *theorem* bsup_const
- \+ *theorem* lsub_const
- \+ *theorem* blsub_const



## [2022-02-05 21:22:39](https://github.com/leanprover-community/mathlib/commit/6787a8d)
feat(category_theory): a hierarchy of balanced categories ([#11856](https://github.com/leanprover-community/mathlib/pull/11856))
#### Estimated changes
modified src/algebra/category/Group/abelian.lean

modified src/algebra/category/Module/abelian.lean

modified src/category_theory/abelian/basic.lean
- \- *lemma* strong_epi_of_epi
- \- *lemma* strong_mono_of_mono
- \- *lemma* is_iso_of_mono_of_epi

modified src/category_theory/abelian/non_preadditive.lean
- \- *lemma* strong_epi_of_epi
- \- *lemma* is_iso_of_mono_of_epi

modified src/category_theory/abelian/opposite.lean

created src/category_theory/balanced.lean
- \+ *lemma* is_iso_of_mono_of_epi
- \+ *lemma* is_iso_iff_mono_and_epi

modified src/category_theory/epi_mono.lean
- \+ *def* split_mono_of_mono
- \+ *def* split_epi_of_epi

modified src/category_theory/limits/shapes/normal_mono.lean
- \+ *def* normal_mono_of_mono
- \+ *def* normal_epi_of_epi

modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *def* regular_mono_of_mono
- \+ *def* regular_epi_of_epi

modified src/category_theory/limits/shapes/strong_epi.lean
- \+ *lemma* strong_epi_of_epi
- \+ *lemma* strong_mono_of_mono

modified src/category_theory/simple.lean

modified src/category_theory/types.lean
- \+ *lemma* injective_of_mono
- \+ *lemma* surjective_of_epi



## [2022-02-05 19:40:29](https://github.com/leanprover-community/mathlib/commit/0f9c153)
feat(algebra/cubic_discriminant): basics of cubic polynomials and their discriminants ([#11483](https://github.com/leanprover-community/mathlib/pull/11483))
#### Estimated changes
created src/algebra/cubic_discriminant.lean
- \+ *lemma* coeff_gt_three
- \+ *lemma* coeff_three
- \+ *lemma* coeff_two
- \+ *lemma* coeff_one
- \+ *lemma* coeff_zero
- \+ *lemma* a_of_eq
- \+ *lemma* b_of_eq
- \+ *lemma* c_of_eq
- \+ *lemma* d_of_eq
- \+ *lemma* to_poly_injective
- \+ *lemma* of_a_eq_zero
- \+ *lemma* of_a_b_eq_zero
- \+ *lemma* of_a_b_c_eq_zero
- \+ *lemma* of_zero
- \+ *lemma* zero
- \+ *lemma* eq_zero_iff
- \+ *lemma* ne_zero
- \+ *lemma* ne_zero_of_a_ne_zero
- \+ *lemma* ne_zero_of_b_ne_zero
- \+ *lemma* ne_zero_of_c_ne_zero
- \+ *lemma* ne_zero_of_d_ne_zero
- \+ *lemma* degree
- \+ *lemma* degree_of_a_eq_zero
- \+ *lemma* degree_of_a_b_eq_zero
- \+ *lemma* degree_of_a_b_c_eq_zero
- \+ *lemma* degree_of_zero
- \+ *lemma* leading_coeff
- \+ *lemma* leading_coeff_of_a_eq_zero
- \+ *lemma* leading_coeff_of_a_b_eq_zero
- \+ *lemma* leading_coeff_of_a_b_c_eq_zero
- \+ *lemma* map_to_poly
- \+ *lemma* map_roots
- \+ *theorem* mem_roots_iff
- \+ *theorem* card_roots_le
- \+ *theorem* splits_iff_card_roots
- \+ *theorem* splits_iff_roots_eq_three
- \+ *theorem* eq_prod_three_roots
- \+ *theorem* eq_sum_three_roots
- \+ *theorem* b_eq_three_roots
- \+ *theorem* c_eq_three_roots
- \+ *theorem* d_eq_three_roots
- \+ *theorem* disc_eq_prod_three_roots
- \+ *theorem* disc_ne_zero_iff_roots_ne
- \+ *theorem* disc_ne_zero_iff_roots_nodup
- \+ *theorem* card_roots_of_disc_ne_zero
- \+ *def* to_poly
- \+ *def* equiv
- \+ *def* map
- \+ *def* roots
- \+ *def* disc

modified src/data/polynomial/coeff.lean
- \+ *lemma* coeff_C_mul_X_pow
- \+/\- *lemma* coeff_C_mul_X
- \+/\- *lemma* coeff_C_mul_X

modified src/data/polynomial/degree/definitions.lean
- \+/\- *lemma* degree_C_lt
- \+ *lemma* degree_C_mul_X
- \+ *lemma* degree_add_le_of_degree_le
- \+ *lemma* nat_degree_add_le_of_degree_le
- \+ *lemma* leading_coeff_C_mul_X
- \+ *lemma* degree_linear_le
- \+ *lemma* degree_linear_lt
- \+ *lemma* degree_C_lt_degree_C_mul_X
- \+ *lemma* degree_linear
- \+ *lemma* nat_degree_linear_le
- \+ *lemma* nat_degree_linear
- \+ *lemma* leading_coeff_linear
- \+ *lemma* degree_quadratic_le
- \+ *lemma* degree_quadratic_lt
- \+ *lemma* degree_linear_lt_degree_C_mul_X_sq
- \+ *lemma* degree_quadratic
- \+ *lemma* nat_degree_quadratic_le
- \+ *lemma* nat_degree_quadratic
- \+ *lemma* leading_coeff_quadratic
- \+ *lemma* degree_cubic_le
- \+ *lemma* degree_cubic_lt
- \+ *lemma* degree_quadratic_lt_degree_C_mul_X_cb
- \+ *lemma* degree_cubic
- \+ *lemma* nat_degree_cubic_le
- \+ *lemma* nat_degree_cubic
- \+ *lemma* leading_coeff_cubic
- \+/\- *lemma* degree_C_lt
- \- *lemma* leading_coeff_C_mul_X_add_C

modified src/data/polynomial/eval.lean

modified src/ring_theory/polynomial/vieta.lean

modified src/ring_theory/power_series/basic.lean
- \+ *lemma* coeff_C_mul_X_pow
- \- *lemma* coeff_C_mul_X



## [2022-02-05 17:59:51](https://github.com/leanprover-community/mathlib/commit/39b1262)
feat(algebra/lie/nilpotent): nilpotency of Lie modules depends only on the Lie subalgebra of linear endomorphisms ([#11853](https://github.com/leanprover-community/mathlib/pull/11853))
#### Estimated changes
modified src/algebra/lie/nilpotent.lean
- \+ *lemma* coe_lcs_range_to_endomorphism_eq
- \+ *lemma* is_nilpotent_range_to_endomorphism_iff
- \+ *lemma* lie_hom.is_nilpotent_range
- \+ *lemma* lie_algebra.is_nilpotent_range_ad_iff



## [2022-02-05 17:59:49](https://github.com/leanprover-community/mathlib/commit/b9d19ed)
feat(algebra/lie/nilpotent): nilpotency of Lie modules is preserved under surjective morphisms ([#11852](https://github.com/leanprover-community/mathlib/pull/11852))
#### Estimated changes
modified src/algebra/lie/nilpotent.lean
- \+ *lemma* function.surjective.lie_module_lcs_map_eq
- \+ *lemma* function.surjective.lie_module_is_nilpotent
- \+ *lemma* equiv.lie_module_is_nilpotent_iff
- \+ *lemma* lie_module.is_nilpotent_of_top_iff



## [2022-02-05 17:59:47](https://github.com/leanprover-community/mathlib/commit/9fcd1f2)
feat(algebra/lie/nilpotent): add lemma `lie_module.coe_lower_central_series_ideal_le` ([#11851](https://github.com/leanprover-community/mathlib/pull/11851))
#### Estimated changes
modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lie_module.coe_lower_central_series_ideal_le



## [2022-02-05 17:31:04](https://github.com/leanprover-community/mathlib/commit/df7c217)
feat(algebra/lie/nilpotent): add definition `lie_ideal.lcs` ([#11854](https://github.com/leanprover-community/mathlib/pull/11854))
This is extremely useful when proving a generalised version of Engel's lemma.
#### Estimated changes
modified src/algebra/lie/nilpotent.lean
- \+ *lemma* lcs_zero
- \+ *lemma* lcs_succ
- \+ *lemma* lcs_top
- \+ *lemma* coe_lcs_eq
- \+ *def* lcs



## [2022-02-05 09:52:03](https://github.com/leanprover-community/mathlib/commit/9969321)
feat(measure_theory/probability_mass_function): Lemmas connecting `pmf.support` and `pmf.to_measure` ([#11842](https://github.com/leanprover-community/mathlib/pull/11842))
Add lemmas relating the support of a `pmf` to the measures of sets under the induced measure.
#### Estimated changes
modified src/measure_theory/probability_mass_function/basic.lean
- \+/\- *lemma* to_outer_measure_apply
- \+/\- *lemma* to_outer_measure_apply'
- \+/\- *lemma* to_outer_measure_apply_finset
- \+/\- *lemma* to_outer_measure_apply_eq_zero_iff
- \+ *lemma* to_outer_measure_apply_eq_one_iff
- \+ *lemma* to_outer_measure_apply_inter_support
- \+ *lemma* to_outer_measure_mono
- \+ *lemma* to_outer_measure_apply_eq_of_inter_support_eq
- \+/\- *lemma* to_outer_measure_apply_fintype
- \+/\- *lemma* to_outer_measure_apply_le_to_measure_apply
- \+/\- *lemma* to_measure_apply_eq_to_outer_measure_apply
- \+/\- *lemma* to_measure_apply
- \+/\- *lemma* to_measure_apply'
- \+ *lemma* to_measure_apply_eq_one_iff
- \+ *lemma* to_measure_apply_inter_support
- \+ *lemma* to_measure_mono
- \+ *lemma* to_measure_apply_eq_of_inter_support_eq
- \+/\- *lemma* to_measure_apply_finset
- \+/\- *lemma* to_measure_apply_of_finite
- \+/\- *lemma* to_measure_apply_fintype
- \+/\- *lemma* to_outer_measure_apply
- \+/\- *lemma* to_outer_measure_apply'
- \+/\- *lemma* to_outer_measure_apply_finset
- \+/\- *lemma* to_outer_measure_apply_fintype
- \+/\- *lemma* to_outer_measure_apply_eq_zero_iff
- \+/\- *lemma* to_measure_apply_eq_to_outer_measure_apply
- \+/\- *lemma* to_outer_measure_apply_le_to_measure_apply
- \+/\- *lemma* to_measure_apply
- \+/\- *lemma* to_measure_apply'
- \+/\- *lemma* to_measure_apply_finset
- \+/\- *lemma* to_measure_apply_of_finite
- \+/\- *lemma* to_measure_apply_fintype



## [2022-02-05 09:52:01](https://github.com/leanprover-community/mathlib/commit/612ca40)
feat(data/finset): erase is empty iff ([#11838](https://github.com/leanprover-community/mathlib/pull/11838))
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* erase_eq_empty_iff



## [2022-02-05 09:52:00](https://github.com/leanprover-community/mathlib/commit/31f5688)
refactor(ring_theory/valuation/basic): `fun_like` design for `valuation` ([#11830](https://github.com/leanprover-community/mathlib/pull/11830))
Introduce `valuation_class`, the companion typeclass to `valuation`. Deprecate lemmas. Rename the field from `map_add'` to `map_add_le_max'` to avoid confusion with the eponymous field from `add_hom`.
#### Estimated changes
modified src/ring_theory/perfection.lean

modified src/ring_theory/valuation/basic.lean
- \+ *lemma* to_fun_eq_coe
- \+/\- *lemma* ext
- \+/\- *lemma* coe_coe
- \+/\- *lemma* map_add
- \+/\- *lemma* ext_iff
- \+/\- *lemma* coe_coe
- \+/\- *lemma* map_add
- \+/\- *lemma* ext
- \+/\- *lemma* ext_iff

modified src/topology/algebra/valued_field.lean



## [2022-02-05 09:51:59](https://github.com/leanprover-community/mathlib/commit/e78563c)
feat(ring_theory/power_series): reindex trunc of a power series to truncate below index n ([#10891](https://github.com/leanprover-community/mathlib/pull/10891))
Currently the definition of truncation of a univariate and multivariate power series truncates above the index, that is if we truncate a power series $\sum a_i x^i$ at index `n` the term $a_n x^n$ is included.
This makes it impossible to truncate the first monomial $x^0$ away as it is included with the smallest possible value of n, which causes some issues in applications (imagine if you could only pop elements of lists if the result was non-empty!).
#### Estimated changes
modified src/ring_theory/power_series/basic.lean
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C
- \+/\- *lemma* trunc_one
- \+/\- *lemma* trunc_C



## [2022-02-05 08:16:33](https://github.com/leanprover-community/mathlib/commit/6b4e269)
chore(data/fintype/basic): rename some instances ([#11845](https://github.com/leanprover-community/mathlib/pull/11845))
Rename instances from `infinite.multiset.infinite` etc to
`multiset.infinite` etc; rename `infinite.set.infinite` to
`infinite.set` to avoid name clash.
Also add `option.infinite`.
#### Estimated changes
modified src/data/fintype/basic.lean
- \+/\- *lemma* infinite_sum
- \+/\- *lemma* infinite_prod
- \+/\- *lemma* infinite_sum
- \+/\- *lemma* infinite_prod



## [2022-02-05 05:19:33](https://github.com/leanprover-community/mathlib/commit/b0d9761)
feat(ring_theory/hahn_series): add a map to power series and dickson's lemma ([#11836](https://github.com/leanprover-community/mathlib/pull/11836))
Add a ring equivalence between `hahn_series` and `mv_power_series` as discussed in https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/induction.20on.20an.20index.20type/near/269463528.
This required adding some partially well ordered lemmas that it seems go under the name Dickson's lemma.
This may be independently useful, a constructive version of this has been used in other provers, especially in connection to Grobner basis and commutative algebra type material.
#### Estimated changes
created src/data/finsupp/pwo.lean
- \+ *lemma* finsupp.is_pwo

modified src/order/well_founded_set.lean
- \+ *lemma* pi.is_pwo
- \+ *theorem* is_pwo.mono

modified src/ring_theory/hahn_series.lean
- \+ *lemma* coeff_to_mv_power_series
- \+ *lemma* coeff_to_mv_power_series_symm
- \+ *def* to_mv_power_series



## [2022-02-04 23:34:38](https://github.com/leanprover-community/mathlib/commit/bd7d034)
feat(ring_theory/nilpotent): add lemma `module.End.is_nilpotent_mapq` ([#11831](https://github.com/leanprover-community/mathlib/pull/11831))
Together with the other lemmas necessary for its proof.
#### Estimated changes
modified src/linear_algebra/basic.lean
- \+ *lemma* le_comap_pow_of_le_comap

modified src/linear_algebra/quotient.lean
- \+ *lemma* mapq_zero
- \+ *lemma* mapq_comp
- \+ *lemma* mapq_id
- \+ *lemma* mapq_pow

modified src/ring_theory/nilpotent.lean
- \+ *lemma* is_nilpotent.mapq



## [2022-02-04 22:50:46](https://github.com/leanprover-community/mathlib/commit/b905eb6)
fix(group_theory/nilpotent): don’t unnecessarily `open_locale classical` ([#11779](https://github.com/leanprover-community/mathlib/pull/11779))
h/t @pechersky for noticing
#### Estimated changes
modified src/group_theory/nilpotent.lean



## [2022-02-04 21:12:18](https://github.com/leanprover-community/mathlib/commit/b3b32c8)
feat(algebra/lie/quotient): first isomorphism theorem for morphisms of Lie algebras ([#11826](https://github.com/leanprover-community/mathlib/pull/11826))
#### Estimated changes
modified src/algebra/lie/quotient.lean



## [2022-02-04 21:12:17](https://github.com/leanprover-community/mathlib/commit/292bf34)
feat(algebra/lie/ideal_operations): add lemma `lie_ideal_oper_eq_linear_span'` ([#11823](https://github.com/leanprover-community/mathlib/pull/11823))
It is useful to have this alternate form in situations where we have a hypothesis like `h : I = J` since we can then rewrite using `h` after applying this lemma.
An (admittedly brief) scan of the existing applications of `lie_ideal_oper_eq_linear_span` indicates that it's worth keeping both forms for convenience but I'm happy to dig deeper into this if requested.
#### Estimated changes
modified src/algebra/lie/ideal_operations.lean
- \+ *lemma* lie_ideal_oper_eq_linear_span'



## [2022-02-04 21:12:16](https://github.com/leanprover-community/mathlib/commit/fa20482)
feat(linear_algebra/basic): add minor lemmas, tweak `simp` attributes ([#11822](https://github.com/leanprover-community/mathlib/pull/11822))
#### Estimated changes
modified src/algebra/module/submodule.lean
- \+/\- *lemma* coe_subtype
- \+/\- *lemma* coe_subtype
- \+/\- *theorem* subtype_apply
- \+/\- *theorem* subtype_apply

modified src/linear_algebra/basic.lean
- \+/\- *lemma* comap_id
- \+ *lemma* map_subtype_span_singleton
- \+/\- *lemma* span_singleton_le_iff_mem
- \+ *lemma* map_subtype_range_of_le
- \+/\- *lemma* comap_id
- \+/\- *lemma* span_singleton_le_iff_mem



## [2022-02-04 21:12:15](https://github.com/leanprover-community/mathlib/commit/247504c)
feat(algebra/lie/cartan_subalgebra): add lemma `lie_subalgebra.exists_nested_lie_ideal_of_le_normalizer` ([#11820](https://github.com/leanprover-community/mathlib/pull/11820))
#### Estimated changes
modified src/algebra/lie/cartan_subalgebra.lean
- \+/\- *lemma* ideal_in_normalizer
- \+ *lemma* exists_nested_lie_ideal_of_le_normalizer
- \+/\- *lemma* ideal_in_normalizer



## [2022-02-04 21:12:13](https://github.com/leanprover-community/mathlib/commit/a2fd0bd)
feat(algebra/lie/basic): define pull back of a Lie module along a morphism of Lie algebras. ([#11819](https://github.com/leanprover-community/mathlib/pull/11819))
#### Estimated changes
modified src/algebra/lie/basic.lean
- \+ *lemma* lie_ring_module.comp_lie_hom_apply
- \+ *def* lie_ring_module.comp_lie_hom
- \+ *def* lie_module.comp_lie_hom



## [2022-02-04 21:12:12](https://github.com/leanprover-community/mathlib/commit/2e7efe9)
refactor(set_theory/ordinal_arithmetic): Change `α → Prop` to `set α` ([#11816](https://github.com/leanprover-community/mathlib/pull/11816))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+/\- *theorem* is_normal.le_set
- \+/\- *theorem* is_normal.le_set'
- \+/\- *theorem* is_normal.sup
- \+/\- *theorem* is_normal.le_set
- \+/\- *theorem* is_normal.le_set'
- \+/\- *theorem* is_normal.sup



## [2022-02-04 21:12:11](https://github.com/leanprover-community/mathlib/commit/a741585)
chore(algebra/group): make `coe_norm_subgroup` and `submodule.norm_coe` consistent ([#11427](https://github.com/leanprover-community/mathlib/pull/11427))
The `simp` lemmas for norms in a subgroup and in a submodule disagreed: the first inserted a coercion to the larger group, the second deleted the coercion. Currently this is not a big deal, but it will become a real issue when defining `add_subgroup_class`. I want to make them consistent by pointing them in the same direction. The consensus in the [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Simp.20normal.20form.3A.20coe_norm_subgroup.2C.20submodule.2Enorm_coe) suggests `simp` should insert a coercion here, so I went with that.
After making the changes, a few places need extra `simp [submodule.coe_norm]` on the local hypotheses, but nothing major.
#### Estimated changes
modified src/analysis/normed/group/basic.lean
- \+ *lemma* add_subgroup.coe_norm
- \+ *lemma* add_subgroup.norm_coe
- \+ *lemma* submodule.coe_norm
- \+/\- *lemma* submodule.norm_coe
- \- *lemma* coe_norm_subgroup
- \+/\- *lemma* submodule.norm_coe
- \- *lemma* submodule.norm_mk

modified src/geometry/manifold/instances/sphere.lean

modified src/measure_theory/function/simple_func_dense.lean



## [2022-02-04 20:39:46](https://github.com/leanprover-community/mathlib/commit/c3273aa)
feat(algebra/lie/subalgebra): add `lie_subalgebra.equiv_of_le` and `lie_subalgebra.equiv_range_of_injective` ([#11828](https://github.com/leanprover-community/mathlib/pull/11828))
#### Estimated changes
modified src/algebra/lie/basic.lean

modified src/algebra/lie/subalgebra.lean
- \+ *lemma* equiv_range_of_injective_apply
- \+ *lemma* coe_of_le
- \+ *lemma* equiv_of_le_apply



## [2022-02-04 18:53:26](https://github.com/leanprover-community/mathlib/commit/3c00e5d)
fix(algebra/Module/colimits): Change `comm_ring` to `ring`. ([#11837](https://github.com/leanprover-community/mathlib/pull/11837))
... despite the well-known fact that all rings are commutative.
#### Estimated changes
modified src/algebra/category/Module/colimits.lean



## [2022-02-04 18:53:25](https://github.com/leanprover-community/mathlib/commit/5b3cd4a)
refactor(analysis/normed_space/add_torsor): Kill `seminormed_add_torsor` ([#11795](https://github.com/leanprover-community/mathlib/pull/11795))
Delete `normed_add_torsor` in favor of the equivalent `seminormed_add_torsor` and rename `seminormed_add_torsor` to `normed_add_torsor`.
#### Estimated changes
modified src/analysis/normed_space/add_torsor.lean
- \+/\- *lemma* dist_eq_norm_vsub
- \+/\- *lemma* dist_eq_norm_vsub

modified src/analysis/normed_space/affine_isometry.lean

modified src/analysis/normed_space/finite_dimension.lean

modified src/geometry/euclidean/basic.lean



## [2022-02-04 18:53:24](https://github.com/leanprover-community/mathlib/commit/aaaeeae)
feat(category_theory/category/{Pointed,Bipointed}): The categories of pointed/bipointed types ([#11777](https://github.com/leanprover-community/mathlib/pull/11777))
Define
* `Pointed`, the category of pointed types
* `Bipointed`, the category of bipointed types
* the forgetful functors from `Bipointed` to `Pointed` and from `Pointed` to `Type*`
* `Type_to_Pointed`, the functor from `Type*` to `Pointed` induced by `option`
* `Bipointed.swap_equiv` the equivalence between `Bipointed` and itself induced by `prod.swap` both ways.
#### Estimated changes
created src/category_theory/category/Bipointed.lean
- \+ *lemma* swap_equiv_symm
- \+ *lemma* Bipointed_to_Pointed_fst_comp_forget
- \+ *lemma* Bipointed_to_Pointed_snd_comp_forget
- \+ *lemma* swap_comp_Bipointed_to_Pointed_fst
- \+ *lemma* swap_comp_Bipointed_to_Pointed_snd
- \+ *lemma* Pointed_to_Bipointed_fst_comp
- \+ *lemma* Pointed_to_Bipointed_snd_comp
- \+ *def* of
- \+ *def* id
- \+ *def* comp
- \+ *def* swap
- \+ *def* swap_equiv
- \+ *def* Bipointed_to_Pointed_fst
- \+ *def* Bipointed_to_Pointed_snd
- \+ *def* Pointed_to_Bipointed_fst
- \+ *def* Pointed_to_Bipointed_snd
- \+ *def* Pointed_to_Bipointed_fst_Bipointed_to_Pointed_fst_adjunction
- \+ *def* Pointed_to_Bipointed_snd_Bipointed_to_Pointed_snd_adjunction

created src/category_theory/category/Pointed.lean
- \+ *def* of
- \+ *def* id
- \+ *def* comp
- \+ *def* Type_to_Pointed
- \+ *def* Type_to_Pointed_forget_adjunction



## [2022-02-04 17:10:26](https://github.com/leanprover-community/mathlib/commit/cedcf07)
chore(*): update to lean 3.39.0c ([#11821](https://github.com/leanprover-community/mathlib/pull/11821))
#### Estimated changes
modified leanpkg.toml

modified src/tactic/rewrite.lean
- \+ *def* id_tag.assoc_proof



## [2022-02-04 08:58:31](https://github.com/leanprover-community/mathlib/commit/049a1b2)
feat(group_theory/subgroup/basic): add pi subgroups ([#11801](https://github.com/leanprover-community/mathlib/pull/11801))
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* coe_pi
- \+ *lemma* mem_pi
- \+ *lemma* pi_top
- \+ *lemma* pi_empty
- \+ *lemma* pi_bot
- \+ *def* _root_.submonoid.pi
- \+ *def* pi



## [2022-02-04 06:54:32](https://github.com/leanprover-community/mathlib/commit/46c48d7)
feat(logic/basic): add projection notation for iff ([#11803](https://github.com/leanprover-community/mathlib/pull/11803))
#### Estimated changes
modified src/data/set/basic.lean

modified src/logic/basic.lean
- \+ *lemma* iff.imp
- \+ *lemma* iff.not
- \+ *lemma* iff.and
- \+ *lemma* iff.or
- \+ *lemma* iff.iff
- \+/\- *theorem* and_congr_left'
- \+/\- *theorem* and_congr_right'
- \+/\- *theorem* or_congr_left
- \+/\- *theorem* or_congr_right
- \+/\- *theorem* and_congr_left'
- \+/\- *theorem* and_congr_right'
- \+/\- *theorem* or_congr_left
- \+/\- *theorem* or_congr_right

modified src/tactic/lint/misc.lean



## [2022-02-04 02:33:18](https://github.com/leanprover-community/mathlib/commit/553cb9c)
fix(algebra/category/Module/colimits): Add some additional instances with permuted universe parameters ([#11812](https://github.com/leanprover-community/mathlib/pull/11812))
#### Estimated changes
modified src/algebra/category/Module/colimits.lean



## [2022-02-04 02:33:17](https://github.com/leanprover-community/mathlib/commit/4cfc30e)
chore(*): use le_rfl instead of le_refl _ ([#11797](https://github.com/leanprover-community/mathlib/pull/11797))
#### Estimated changes
modified src/algebra/algebra/operations.lean

modified src/algebra/algebra/subalgebra.lean

modified src/algebra/big_operators/order.lean

modified src/algebra/direct_limit.lean

modified src/algebra/indicator_function.lean

modified src/algebra/lie/nilpotent.lean

modified src/algebra/lie/submodule.lean

modified src/algebra/order/archimedean.lean

modified src/algebra/order/monoid.lean

modified src/algebra/order/pi.lean

modified src/algebra/order/ring.lean

modified src/algebra/order/with_zero.lean

modified src/algebra/tropical/basic.lean

modified src/algebraic_topology/simplex_category.lean

modified src/analysis/analytic/basic.lean

modified src/analysis/asymptotics/asymptotics.lean

modified src/analysis/calculus/deriv.lean

modified src/analysis/calculus/fderiv.lean

modified src/analysis/calculus/fderiv_measurable.lean

modified src/analysis/calculus/fderiv_symmetric.lean

modified src/analysis/calculus/inverse.lean

modified src/analysis/calculus/times_cont_diff.lean

modified src/analysis/inner_product_space/projection.lean

modified src/analysis/normed/group/SemiNormedGroup/kernels.lean

modified src/analysis/normed/group/basic.lean

modified src/analysis/normed/group/infinite_sum.lean

modified src/analysis/normed/group/quotient.lean

modified src/analysis/normed_space/basic.lean

modified src/analysis/normed_space/enorm.lean

modified src/analysis/normed_space/multilinear.lean

modified src/analysis/special_functions/bernstein.lean

modified src/analysis/specific_limits.lean

modified src/category_theory/sites/closed.lean

modified src/category_theory/sites/grothendieck.lean

modified src/category_theory/sites/pretopology.lean

modified src/category_theory/subobject/basic.lean

modified src/combinatorics/composition.lean

modified src/computability/language.lean

modified src/computability/partrec_code.lean

modified src/computability/turing_machine.lean

modified src/control/lawful_fix.lean

modified src/data/W/basic.lean

modified src/data/W/cardinal.lean

modified src/data/analysis/filter.lean

modified src/data/buffer/parser/basic.lean

modified src/data/complex/exponential.lean

modified src/data/finset/lattice.lean

modified src/data/fintype/basic.lean

modified src/data/int/basic.lean

modified src/data/list/min_max.lean

modified src/data/list/rotate.lean

modified src/data/multiset/finset_ops.lean

modified src/data/multiset/lattice.lean

modified src/data/mv_polynomial/cardinal.lean

modified src/data/mv_polynomial/variables.lean

modified src/data/nat/basic.lean

modified src/data/nat/cast.lean

modified src/data/nat/choose/basic.lean

modified src/data/nat/enat.lean

modified src/data/nat/factorial/basic.lean

modified src/data/nat/lattice.lean

modified src/data/nat/pow.lean

modified src/data/nat/prime.lean

modified src/data/ordmap/ordnode.lean

modified src/data/ordmap/ordset.lean

modified src/data/polynomial/degree/definitions.lean

modified src/data/polynomial/degree/trailing_degree.lean

modified src/data/polynomial/eval.lean

modified src/data/polynomial/field_division.lean

modified src/data/polynomial/inductions.lean

modified src/data/polynomial/reverse.lean

modified src/data/rbtree/basic.lean

modified src/data/real/basic.lean

modified src/data/real/cau_seq.lean

modified src/data/real/ennreal.lean

modified src/data/real/ereal.lean

modified src/data/real/pi/bounds.lean

modified src/data/real/pi/wallis.lean

modified src/data/real/sqrt.lean

modified src/data/set/intervals/disjoint.lean

modified src/field_theory/adjoin.lean

modified src/field_theory/galois.lean

modified src/field_theory/is_alg_closed/basic.lean

modified src/field_theory/splitting_field.lean

modified src/geometry/manifold/instances/real.lean

modified src/geometry/manifold/times_cont_mdiff.lean

modified src/group_theory/perm/support.lean

modified src/group_theory/specific_groups/alternating.lean

modified src/group_theory/subgroup/basic.lean

modified src/linear_algebra/adic_completion.lean

modified src/linear_algebra/basic.lean

modified src/linear_algebra/bilinear_form.lean

modified src/linear_algebra/dimension.lean

modified src/linear_algebra/finite_dimensional.lean

modified src/linear_algebra/isomorphisms.lean

modified src/linear_algebra/linear_independent.lean

modified src/linear_algebra/quotient.lean

modified src/linear_algebra/std_basis.lean

modified src/measure_theory/decomposition/lebesgue.lean

modified src/measure_theory/decomposition/unsigned_hahn.lean

modified src/measure_theory/function/l1_space.lean

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/integral/integrable_on.lean

modified src/measure_theory/integral/integral_eq_improper.lean

modified src/measure_theory/integral/interval_integral.lean

modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/integral/vitali_caratheodory.lean

modified src/measure_theory/measurable_space_def.lean

modified src/measure_theory/measure/giry_monad.lean

modified src/measure_theory/measure/measure_space.lean

modified src/measure_theory/measure/outer_measure.lean

modified src/measure_theory/measure/stieltjes.lean

modified src/measure_theory/measure/vector_measure.lean

modified src/measure_theory/pi_system.lean

modified src/number_theory/class_number/finite.lean

modified src/number_theory/padics/hensel.lean

modified src/number_theory/padics/padic_numbers.lean

modified src/number_theory/primorial.lean

modified src/number_theory/quadratic_reciprocity.lean

modified src/number_theory/sum_four_squares.lean

modified src/number_theory/zsqrtd/basic.lean

modified src/order/atoms.lean

modified src/order/bounded_order.lean

modified src/order/closure.lean

modified src/order/complete_lattice.lean

modified src/order/conditionally_complete_lattice.lean

modified src/order/filter/at_top_bot.lean

modified src/order/filter/bases.lean

modified src/order/filter/extr.lean

modified src/order/filter/indicator_function.lean

modified src/order/filter/lift.lean

modified src/order/filter/ultrafilter.lean

modified src/order/galois_connection.lean

modified src/order/lattice.lean

modified src/order/liminf_limsup.lean

modified src/order/modular_lattice.lean

modified src/order/monotone.lean

modified src/order/omega_complete_partial_order.lean

modified src/order/partial_sups.lean

modified src/order/pilex.lean

modified src/order/well_founded_set.lean

modified src/order/zorn.lean

modified src/probability_theory/stopping.lean

modified src/ring_theory/artinian.lean

modified src/ring_theory/dedekind_domain.lean

modified src/ring_theory/ideal/operations.lean

modified src/ring_theory/int/basic.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/nakayama.lean

modified src/ring_theory/polynomial/basic.lean

modified src/ring_theory/polynomial/bernstein.lean

modified src/ring_theory/power_series/basic.lean

modified src/ring_theory/unique_factorization_domain.lean

modified src/ring_theory/valuation/basic.lean
- \+/\- *lemma* supp_quot_supp
- \+/\- *lemma* supp_quot_supp
- \+/\- *lemma* supp_quot_supp
- \+/\- *lemma* supp_quot_supp

modified src/set_theory/cardinal.lean

modified src/set_theory/cardinal_ordinal.lean

modified src/set_theory/cofinality.lean

modified src/set_theory/ordinal.lean

modified src/set_theory/ordinal_arithmetic.lean

modified src/testing/slim_check/sampleable.lean

modified src/topology/algebra/floor_ring.lean

modified src/topology/algebra/group.lean

modified src/topology/algebra/infinite_sum.lean

modified src/topology/algebra/ordered/intermediate_value.lean

modified src/topology/algebra/ordered/monotone_convergence.lean

modified src/topology/category/Top/open_nhds.lean

modified src/topology/continuous_function/bounded.lean

modified src/topology/instances/ennreal.lean

modified src/topology/list.lean

modified src/topology/local_extr.lean

modified src/topology/metric_space/baire.lean

modified src/topology/metric_space/basic.lean

modified src/topology/metric_space/contracting.lean

modified src/topology/metric_space/emetric_space.lean

modified src/topology/metric_space/gluing.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/gromov_hausdorff_realized.lean

modified src/topology/metric_space/lipschitz.lean

modified src/topology/order.lean

modified src/topology/path_connected.lean

modified src/topology/semicontinuous.lean

modified src/topology/separation.lean

modified src/topology/sheaves/sheaf_condition/equalizer_products.lean

modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean

modified src/topology/stone_cech.lean

modified src/topology/uniform_space/basic.lean

modified src/topology/uniform_space/completion.lean

modified src/topology/uniform_space/separation.lean

modified src/topology/vector_bundle.lean

modified test/apply.lean

modified test/monotonicity.lean



## [2022-02-04 02:03:42](https://github.com/leanprover-community/mathlib/commit/6dcad02)
feat(linear_algebra/lagrange): Add recurrence formula for Lagrange polynomials ([#11762](https://github.com/leanprover-community/mathlib/pull/11762))
I have also changed `interpolate` to take in a function `f : F → F` instead of `f : s → F`, since this makes the statement of the theorem nicer.
#### Estimated changes
modified docs/undergrad.yaml

modified src/linear_algebra/lagrange.lean
- \+ *theorem* basis_singleton_self
- \+ *theorem* interpolate_singleton
- \+/\- *theorem* eval_interpolate
- \+ *theorem* degree_interpolate_erase
- \+ *theorem* interpolate_eq_of_eval_eq
- \+ *theorem* eq_interpolate_of_eval_eq
- \+ *theorem* interpolate_eq_interpolate_erase_add
- \+/\- *theorem* eval_interpolate
- \+/\- *def* linterpolate
- \+/\- *def* linterpolate



## [2022-02-03 23:36:11](https://github.com/leanprover-community/mathlib/commit/853192c)
feat(topology/algebra): Inf and inducing preserve compatibility with algebraic structure ([#11720](https://github.com/leanprover-community/mathlib/pull/11720))
This partly duplicates @mariainesdff 's work on group topologies, but I'm using an unbundled approach which avoids defining a new `X_topology` structure for each interesting X.
#### Estimated changes
modified src/topology/algebra/group.lean
- \+ *lemma* topological_group_Inf
- \+ *lemma* topological_group_infi
- \+ *lemma* topological_group_inf
- \+ *lemma* topological_group_induced

modified src/topology/algebra/module/basic.lean
- \+ *lemma* has_continuous_smul_induced

modified src/topology/algebra/monoid.lean
- \+ *lemma* has_continuous_mul_Inf
- \+ *lemma* has_continuous_mul_infi
- \+ *lemma* has_continuous_mul_inf
- \+ *lemma* has_continuous_mul_induced

modified src/topology/algebra/mul_action.lean
- \+ *lemma* has_continuous_smul_Inf
- \+ *lemma* has_continuous_smul_infi
- \+ *lemma* has_continuous_smul_inf



## [2022-02-03 18:39:52](https://github.com/leanprover-community/mathlib/commit/30a731c)
fix(algebra/category/Module/colimits): generalize universes ([#11802](https://github.com/leanprover-community/mathlib/pull/11802))
#### Estimated changes
modified src/algebra/category/Module/colimits.lean
- \+/\- *lemma* cocone_naturality_components
- \+/\- *lemma* cocone_naturality_components
- \+/\- *def* colimit_type
- \+/\- *def* colimit_type



## [2022-02-03 18:39:51](https://github.com/leanprover-community/mathlib/commit/f2be0d2)
feat(polynomial/cyclotomic): irreducible cyclotomic polynomials are minimal polynomials ([#11796](https://github.com/leanprover-community/mathlib/pull/11796))
from flt-regular
#### Estimated changes
modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* _root_.is_primitive_root.minpoly_dvd_cyclotomic
- \+ *lemma* _root_.is_primitive_root.minpoly_eq_cyclotomic_of_irreducible
- \- *lemma* _root_.minpoly_dvd_cyclotomic



## [2022-02-03 16:59:03](https://github.com/leanprover-community/mathlib/commit/2c5f36c)
feat(data/finset/sort): an order embedding from fin ([#11800](https://github.com/leanprover-community/mathlib/pull/11800))
Given a set `s` of at least `k` element in a linear order, there is an order embedding from `fin k` whose image is contained in `s`.
#### Estimated changes
modified src/data/finset/sort.lean
- \+ *lemma* order_emb_of_card_le_mem
- \+ *def* order_emb_of_card_le



## [2022-02-03 16:59:01](https://github.com/leanprover-community/mathlib/commit/25f0406)
fix(topology/connected): typos in docstrings ([#11798](https://github.com/leanprover-community/mathlib/pull/11798))
As pointed out by @YaelDillies
#### Estimated changes
modified src/topology/connected.lean



## [2022-02-03 15:03:19](https://github.com/leanprover-community/mathlib/commit/a4d9581)
feat(algebra/group_power/order): add pow_bit0_pos_iff ([#11785](https://github.com/leanprover-community/mathlib/pull/11785))
#### Estimated changes
modified src/algebra/group_power/order.lean
- \+ *theorem* pow_bit0_pos_iff
- \+ *theorem* sq_pos_iff



## [2022-02-03 14:17:31](https://github.com/leanprover-community/mathlib/commit/324d845)
feat(field_theory/krull_topology): defined Krull topology on Galois groups ([#11780](https://github.com/leanprover-community/mathlib/pull/11780))
#### Estimated changes
created src/field_theory/krull_topology.lean
- \+ *lemma* intermediate_field.map_mono
- \+ *lemma* intermediate_field.map_id
- \+ *lemma* intermediate_field.finite_dimensional_bot
- \+ *lemma* intermediate_field.fixing_subgroup.bot
- \+ *lemma* top_fixed_by_finite
- \+ *lemma* finite_dimensional_sup
- \+ *lemma* mem_fixing_subgroup_iff
- \+ *lemma* intermediate_field.fixing_subgroup.antimono
- \+ *lemma* mem_gal_basis_iff
- \+ *def* finite_exts
- \+ *def* fixed_by_finite
- \+ *def* gal_basis
- \+ *def* gal_group_basis



## [2022-02-03 12:53:15](https://github.com/leanprover-community/mathlib/commit/d6e1c55)
chore(data/polynomial/monic): dedup `degree_map` ([#11792](https://github.com/leanprover-community/mathlib/pull/11792))
#### Estimated changes
modified src/data/polynomial/monic.lean
- \+ *lemma* nat_degree_map_eq_of_injective
- \- *lemma* degree_map'
- \- *lemma* nat_degree_map'

modified src/field_theory/splitting_field.lean

modified src/ring_theory/algebraic.lean

modified src/ring_theory/polynomial/gauss_lemma.lean



## [2022-02-03 12:53:14](https://github.com/leanprover-community/mathlib/commit/2f4f8ad)
feat(set_theory/principal): Principal ordinals are unbounded ([#11755](https://github.com/leanprover-community/mathlib/pull/11755))
Amazingly, this theorem requires no conditions on the operation.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* lt_nfp
- \- *theorem* is_normal.lt_nfp

modified src/set_theory/principal.lean
- \+ *theorem* lt_blsub₂
- \+ *theorem* principal_nfp_blsub₂
- \+ *theorem* unbounded_principal
- \+ *def* blsub₂



## [2022-02-03 12:12:38](https://github.com/leanprover-community/mathlib/commit/50ee3d5)
feat(ring_theory/roots_of_unity): coe_injective ([#11793](https://github.com/leanprover-community/mathlib/pull/11793))
from flt-regular
#### Estimated changes
modified src/ring_theory/roots_of_unity.lean
- \+ *lemma* roots_of_unity.coe_injective



## [2022-02-03 11:20:19](https://github.com/leanprover-community/mathlib/commit/934f182)
feat(field_theory/is_alg_closed/classification): Classify algebraically closed fields ([#9370](https://github.com/leanprover-community/mathlib/pull/9370))
The main results here are that two algebraically closed fields with the same characteristic and the same cardinality of transcendence basis are isomorphic. The consequence of this is that two uncountable algebraically closed fields of the same cardinality and characteristic are isomorphic. This has applications in model theory, in particular the Lefschetz principle https://proofwiki.org/wiki/Lefschetz_Principle_(First-Order)
#### Estimated changes
created src/field_theory/is_alg_closed/classification.lean
- \+ *lemma* cardinal_mk_le_sigma_polynomial
- \+ *lemma* cardinal_mk_le_max
- \+ *lemma* is_alg_closure_of_transcendence_basis
- \+ *lemma* cardinal_le_max_transcendence_basis
- \+ *lemma* cardinal_eq_cardinal_transcendence_basis_of_omega_lt
- \+ *lemma* ring_equiv_of_cardinal_eq_of_char_zero
- \+ *lemma* ring_equiv_of_cardinal_eq_of_char_eq
- \+ *def* equiv_of_transcendence_basis



## [2022-02-03 10:20:39](https://github.com/leanprover-community/mathlib/commit/e39f617)
feat(category_theory/linear): compatibility of linear Yoneda ([#11784](https://github.com/leanprover-community/mathlib/pull/11784))
#### Estimated changes
modified src/category_theory/linear/yoneda.lean
- \+ *lemma* whiskering_linear_yoneda
- \+ *lemma* whiskering_linear_yoneda₂
- \+ *lemma* whiskering_linear_coyoneda
- \+ *lemma* whiskering_linear_coyoneda₂
- \+ *def* linear_coyoneda



## [2022-02-03 10:20:38](https://github.com/leanprover-community/mathlib/commit/e61ce5d)
chore(category_theory/limits): dualize strong_epi ([#11783](https://github.com/leanprover-community/mathlib/pull/11783))
#### Estimated changes
modified src/category_theory/abelian/basic.lean
- \+ *lemma* strong_mono_of_mono

modified src/category_theory/limits/shapes/regular_mono.lean
- \+/\- *lemma* is_iso_of_regular_epi_of_mono
- \+/\- *lemma* is_iso_of_regular_epi_of_mono

modified src/category_theory/limits/shapes/strong_epi.lean
- \+ *lemma* strong_mono_comp
- \+ *lemma* strong_mono_of_strong_mono
- \+ *lemma* is_iso_of_epi_of_strong_mono



## [2022-02-03 10:20:37](https://github.com/leanprover-community/mathlib/commit/93f2bdc)
feat(topology/algebra/ordered/monotone_convergence): add `antitone.{ge,le}_of_tendsto` ([#11754](https://github.com/leanprover-community/mathlib/pull/11754))
#### Estimated changes
modified src/topology/algebra/ordered/monotone_convergence.lean
- \+ *lemma* antitone.le_of_tendsto
- \+ *lemma* antitone.ge_of_tendsto



## [2022-02-03 09:25:26](https://github.com/leanprover-community/mathlib/commit/a483158)
feat(topology/algebra/group): continuity of action of a group on its own coset space ([#11772](https://github.com/leanprover-community/mathlib/pull/11772))
Given a subgroup `Γ` of a topological group `G`, there is an induced scalar action of `G` on the coset space `G ⧸ Γ`, and there is also an induced topology on `G ⧸ Γ`.  We prove that this action is continuous in each variable, and, if the group `G` is locally compact, also jointly continuous.
#### Estimated changes
modified src/topology/algebra/group.lean
- \+ *lemma* quotient_group.continuous_smul₁

modified src/topology/algebra/group_completion.lean

modified src/topology/compact_open.lean
- \+ *lemma* quotient_map.continuous_lift_prod_left
- \+ *lemma* quotient_map.continuous_lift_prod_right



## [2022-02-03 04:55:55](https://github.com/leanprover-community/mathlib/commit/1816378)
chore(*): golf `by_contra, push_neg` to `by_contra'` ([#11768](https://github.com/leanprover-community/mathlib/pull/11768))
#### Estimated changes
modified archive/imo/imo1972_b2.lean

modified archive/imo/imo2008_q4.lean

modified archive/imo/imo2013_q5.lean

modified counterexamples/phillips.lean

modified src/algebra/big_operators/finprod.lean

modified src/algebraic_topology/simplex_category.lean

modified src/analysis/convex/extrema.lean

modified src/analysis/specific_limits.lean

modified src/combinatorics/composition.lean

modified src/data/fintype/basic.lean

modified src/data/nat/nth.lean

modified src/dynamics/circle/rotation_number/translation_number.lean

modified src/measure_theory/constructions/borel_space.lean

modified src/measure_theory/covering/besicovitch_vector_space.lean

modified src/measure_theory/decomposition/signed_hahn.lean

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/measure/hausdorff.lean

modified src/measure_theory/measure/measure_space_def.lean

modified src/number_theory/class_number/finite.lean

modified src/order/extension.lean

modified src/order/well_founded.lean

modified src/ring_theory/polynomial/content.lean

modified src/ring_theory/witt_vector/domain.lean

modified src/topology/algebra/ordered/liminf_limsup.lean

modified src/topology/metric_space/emetric_paracompact.lean



## [2022-02-03 04:21:08](https://github.com/leanprover-community/mathlib/commit/89a3c07)
feat(field_theory/laurent): Laurent expansions of rational functions ([#11199](https://github.com/leanprover-community/mathlib/pull/11199))
Also provide more API for `ratfunc`, lifting homomorphisms of (polynomial to polynomial) to (ratfunc to ratfunc).
#### Estimated changes
created src/field_theory/laurent.lean
- \+ *lemma* taylor_mem_non_zero_divisors
- \+ *lemma* laurent_aux_of_fraction_ring_mk
- \+ *lemma* laurent_aux_div
- \+ *lemma* laurent_aux_algebra_map
- \+ *lemma* laurent_div
- \+ *lemma* laurent_algebra_map
- \+ *lemma* laurent_X
- \+ *lemma* laurent_C
- \+ *lemma* laurent_at_zero
- \+ *lemma* laurent_laurent
- \+ *lemma* laurent_injective
- \+ *def* laurent_aux
- \+ *def* laurent

modified src/field_theory/ratfunc.lean
- \+ *lemma* map_apply_of_fraction_ring_mk
- \+ *lemma* map_injective
- \+ *lemma* coe_map_ring_hom_eq_coe_map
- \+/\- *lemma* lift_monoid_with_zero_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* lift_monoid_with_zero_hom_injective
- \+/\- *lemma* lift_ring_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* lift_ring_hom_injective
- \+/\- *lemma* div_smul
- \+ *lemma* map_apply_div_ne_zero
- \+ *lemma* map_apply_div
- \+ *lemma* coe_map_alg_hom_eq_coe_map
- \+/\- *lemma* lift_alg_hom_injective
- \+ *lemma* map_apply
- \+/\- *lemma* lift_monoid_with_zero_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* lift_monoid_with_zero_hom_injective
- \+/\- *lemma* lift_ring_hom_apply_of_fraction_ring_mk
- \+/\- *lemma* lift_ring_hom_injective
- \+/\- *lemma* div_smul
- \+/\- *lemma* lift_alg_hom_injective
- \+ *def* map
- \+ *def* map_ring_hom
- \+/\- *def* lift_monoid_with_zero_hom
- \+/\- *def* lift_ring_hom
- \+ *def* map_alg_hom
- \+/\- *def* lift_monoid_with_zero_hom
- \+/\- *def* lift_ring_hom

modified src/ring_theory/hahn_series.lean
- \+ *lemma* single_eq_zero_iff



## [2022-02-02 21:05:56](https://github.com/leanprover-community/mathlib/commit/7f3590b)
feat(field_theory/minpoly): add a nontriviality lemma ([#11781](https://github.com/leanprover-community/mathlib/pull/11781))
#### Estimated changes
modified src/field_theory/minpoly.lean
- \+ *lemma* subsingleton



## [2022-02-02 20:04:39](https://github.com/leanprover-community/mathlib/commit/cdad110)
feat(tactic/equiv_rw): enhancing 'equiv_rw' ([#11730](https://github.com/leanprover-community/mathlib/pull/11730))
Expands the `equiv_rw` API by:
* Making it accept a list of equivalences instead of a single one, if intended
* Allowing multiple targets (closes [#2891](https://github.com/leanprover-community/mathlib/pull/2891))
Extra: some optimizations.
#### Estimated changes
modified src/ring_theory/witt_vector/truncated.lean

modified src/tactic/equiv_rw.lean

modified src/topology/continuous_function/compact.lean

modified test/equiv_rw.lean



## [2022-02-02 16:48:16](https://github.com/leanprover-community/mathlib/commit/41811cd)
feat(number_theory): von Mangoldt function ([#11727](https://github.com/leanprover-community/mathlib/pull/11727))
Defines the von Mangoldt function
#### Estimated changes
modified src/algebra/is_prime_pow.lean
- \+ *lemma* is_prime_pow_pow_iff
- \+ *lemma* nat.coprime.is_prime_pow_dvd_mul
- \+ *lemma* nat.disjoint_divisors_filter_prime_pow
- \+ *lemma* nat.mul_divisors_filter_prime_pow

modified src/number_theory/divisors.lean
- \+ *lemma* prod_divisors_antidiagonal
- \+ *lemma* prod_divisors_antidiagonal'

created src/number_theory/von_mangoldt.lean
- \+ *lemma* log_apply
- \+ *lemma* von_mangoldt_apply
- \+ *lemma* von_mangoldt_apply_one
- \+ *lemma* von_mangoldt_nonneg
- \+ *lemma* von_mangoldt_apply_pow
- \+ *lemma* von_mangoldt_apply_prime
- \+ *lemma* von_mangoldt_sum
- \+ *lemma* von_mangoldt_mul_zeta
- \+ *lemma* zeta_mul_von_mangoldt
- \+ *lemma* log_mul_moebius_eq_von_mangoldt
- \+ *lemma* moebius_mul_log_eq_von_mangoldt
- \+ *lemma* sum_moebius_mul_log_eq



## [2022-02-02 16:48:15](https://github.com/leanprover-community/mathlib/commit/c235c61)
refactor(set_theory/ordinal_arithmetic): Simpler `bsup` definition ([#11386](https://github.com/leanprover-community/mathlib/pull/11386))
We also simplify some existing proofs.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* comp_bfamily_of_family'
- \+ *theorem* comp_bfamily_of_family
- \+ *theorem* comp_family_of_bfamily'
- \+ *theorem* comp_family_of_bfamily
- \+/\- *theorem* sup_eq_sup
- \+/\- *theorem* bsup_eq_sup
- \+/\- *theorem* bsup_le
- \+/\- *theorem* le_bsup
- \+/\- *theorem* lt_bsup
- \+/\- *theorem* lsub_eq_lsub
- \+/\- *theorem* bsup_le
- \+/\- *theorem* le_bsup
- \+/\- *theorem* lt_bsup
- \+/\- *theorem* sup_eq_sup
- \+/\- *theorem* bsup_eq_sup
- \+/\- *theorem* lsub_eq_lsub
- \+/\- *def* bsup
- \+/\- *def* bsup



## [2022-02-02 16:48:14](https://github.com/leanprover-community/mathlib/commit/4d0b398)
feat(topology/connected): Connectedness of unions of sets ([#10005](https://github.com/leanprover-community/mathlib/pull/10005))
* Add multiple results about when unions of sets are (pre)connected. In particular, the union of connected sets indexed by `ℕ` such that each set intersects the next is connected.
* Remove some `set.` prefixes in the file
* There are two minor fixes in other files, presumably caused by the fact that they now import `order.succ_pred`
* Co-authored by Floris van Doorn fpvdoorn@gmail.com
#### Estimated changes
modified src/analysis/calculus/specific_functions.lean

modified src/data/real/cardinality.lean

modified src/data/set/lattice.lean
- \+ *lemma* nonempty_bUnion

modified src/topology/connected.lean
- \+ *theorem* is_preconnected.union'
- \+ *theorem* is_preconnected.sUnion_directed
- \+ *theorem* is_preconnected.bUnion_of_refl_trans_gen
- \+ *theorem* is_connected.bUnion_of_refl_trans_gen
- \+ *theorem* is_preconnected.Union_of_refl_trans_gen
- \+ *theorem* is_connected.Union_of_refl_trans_gen
- \+ *theorem* is_preconnected.Union_of_chain
- \+ *theorem* is_connected.Union_of_chain
- \+ *theorem* is_preconnected.bUnion_of_chain
- \+ *theorem* is_connected.bUnion_of_chain
- \+/\- *theorem* is_connected.subset_closure
- \+/\- *theorem* is_connected.subset_closure



## [2022-02-02 14:51:44](https://github.com/leanprover-community/mathlib/commit/d6c002c)
feat(group_theory/p_group): finite p-groups with different p have coprime orders ([#11775](https://github.com/leanprover-community/mathlib/pull/11775))
#### Estimated changes
modified src/group_theory/p_group.lean
- \+ *lemma* coprime_card_of_ne



## [2022-02-02 14:51:43](https://github.com/leanprover-community/mathlib/commit/307a456)
refactor(set_theory/ordinal): Add `covariant_class` instances for ordinal addition and multiplication ([#11678](https://github.com/leanprover-community/mathlib/pull/11678))
This replaces the old `add_le_add_left`, `add_le_add_right`, `mul_le_mul_left`, `mul_le_mul_right` theorems.
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean

modified src/set_theory/ordinal.lean
- \- *theorem* add_le_add_left
- \- *theorem* add_le_add_right

modified src/set_theory/ordinal_arithmetic.lean
- \- *theorem* add_le_add_iff_left
- \- *theorem* add_lt_add_iff_left
- \- *theorem* mul_le_mul_left
- \- *theorem* mul_le_mul_right
- \- *theorem* mul_le_mul

modified src/set_theory/ordinal_notation.lean



## [2022-02-02 14:51:42](https://github.com/leanprover-community/mathlib/commit/cd1d839)
feat(order/rel_classes): Unbundled typeclass to state that two relations are the non strict and strict versions ([#11381](https://github.com/leanprover-community/mathlib/pull/11381))
This defines a Prop-valued mixin `is_nonstrict_strict_order α r s` to state `s a b ↔ r a b ∧ ¬ r b a`.
The idea is to allow dot notation for lemmas about the interaction of `⊆` and `⊂` (which currently do not have a `preorder`-like typeclass). Dot notation on each of them is already possible thanks to unbundled relation classes (which allow to state lemmas for both `set` and `finset`).
#### Estimated changes
modified src/data/finset/basic.lean
- \+ *lemma* subset_def
- \+ *lemma* ssubset_def
- \+/\- *lemma* coe_coe_emb
- \+/\- *lemma* coe_coe_emb
- \- *theorem* subset_def
- \- *theorem* subset_of_eq
- \+/\- *def* coe_emb
- \+/\- *def* coe_emb

modified src/data/set/basic.lean
- \+ *lemma* subset_def
- \+ *lemma* ssubset_def
- \- *lemma* has_subset.subset.trans
- \- *lemma* has_subset.subset.antisymm
- \- *lemma* has_ssubset.ssubset.trans
- \- *lemma* has_ssubset.ssubset.asymm
- \- *lemma* ssubset_iff_subset_ne
- \- *lemma* ssubset_of_ssubset_of_subset
- \- *lemma* ssubset_of_subset_of_ssubset
- \- *theorem* subset_def
- \- *theorem* ssubset_def
- \- *theorem* eq_or_ssubset_of_subset

modified src/order/rel_classes.lean
- \+/\- *lemma* comm
- \+ *lemma* antisymm'
- \+ *lemma* antisymm_of'
- \+/\- *lemma* ne_of_irrefl
- \+ *lemma* ne_of_irrefl'
- \+ *lemma* right_iff_left_not_left
- \+ *lemma* right_iff_left_not_left_of
- \+ *lemma* subset_refl
- \+ *lemma* subset_rfl
- \+ *lemma* subset_of_eq
- \+ *lemma* superset_of_eq
- \+ *lemma* ne_of_not_subset
- \+ *lemma* ne_of_not_superset
- \+ *lemma* subset_trans
- \+ *lemma* subset_antisymm
- \+ *lemma* superset_antisymm
- \+ *lemma* subset_antisymm_iff
- \+ *lemma* superset_antisymm_iff
- \+ *lemma* ssubset_irrefl
- \+ *lemma* ssubset_irrfl
- \+ *lemma* ne_of_ssubset
- \+ *lemma* ne_of_ssuperset
- \+ *lemma* ssubset_trans
- \+ *lemma* ssubset_asymm
- \+ *lemma* ssubset_iff_subset_not_subset
- \+ *lemma* subset_of_ssubset
- \+ *lemma* not_subset_of_ssubset
- \+ *lemma* not_ssubset_of_subset
- \+ *lemma* ssubset_of_subset_not_subset
- \+ *lemma* ssubset_of_subset_of_ssubset
- \+ *lemma* ssubset_of_ssubset_of_subset
- \+ *lemma* ssubset_of_subset_of_ne
- \+ *lemma* ssubset_of_ne_of_subset
- \+ *lemma* eq_or_ssubset_of_subset
- \+ *lemma* ssubset_or_eq_of_subset
- \+ *lemma* ssubset_iff_subset_ne
- \+ *lemma* subset_iff_ssubset_or_eq
- \+/\- *lemma* comm
- \+/\- *lemma* ne_of_irrefl



## [2022-02-02 13:59:38](https://github.com/leanprover-community/mathlib/commit/d002769)
refactor(ring_theory): clean up `algebraic_iff_integral` ([#11773](https://github.com/leanprover-community/mathlib/pull/11773))
The definitions `is_algebraic_iff_integral`, `is_algebraic_iff_integral'` and `algebra.is_algebraic_of_finite` have always been annoying me, so I decided to fix that:
 * The name `is_algebraic_iff_integral'` doesn't explain how it differs from `is_algebraic_iff_integral` (namely that the whole algebra is algebraic, rather than one element), so I renamed it to `algebra.is_algebraic_iff_integral`.
 * The two `is_algebraic_iff_integral` lemmas have an unnecessarily explicit parameter `K`, so I made that implicit
 * `is_algebraic_of_finite` has no explicit parameters (so we always have to use type ascriptions), so I made them explicit
 * Half of the usages of `is_algebraic_of_finite` are of the form `is_algebraic_iff_integral.mp is_algebraic_of_finite`, even though `is_algebraic_of_finite` is proved as `is_algebraic_iff_integral.mpr (some_proof_that_it_is_integral)`, so I split it up into a part showing it is integral, that we can use directly.
As a result, I was able to golf a few proofs.
#### Estimated changes
modified src/field_theory/abel_ruffini.lean

modified src/field_theory/adjoin.lean

modified src/field_theory/is_alg_closed/algebraic_closure.lean

modified src/field_theory/is_alg_closed/basic.lean

modified src/field_theory/polynomial_galois_group.lean

modified src/field_theory/separable.lean

modified src/field_theory/splitting_field.lean

modified src/number_theory/class_number/finite.lean

modified src/number_theory/number_field.lean

modified src/ring_theory/adjoin_root.lean

modified src/ring_theory/algebraic.lean
- \+ *lemma* is_integral_of_finite
- \- *lemma* is_algebraic_iff_is_integral'

modified src/ring_theory/dedekind_domain.lean

modified src/ring_theory/localization.lean



## [2022-02-02 13:59:37](https://github.com/leanprover-community/mathlib/commit/07d6d17)
refactor(field_theory/is_alg_closed/basic): Generalize alg closures to commutative rings ([#11703](https://github.com/leanprover-community/mathlib/pull/11703))
#### Estimated changes
modified src/field_theory/is_alg_closed/basic.lean
- \+/\- *lemma* equiv_of_equiv_comp_algebra_map
- \+/\- *lemma* equiv_of_equiv_algebra_map
- \+/\- *lemma* equiv_of_equiv_symm_algebra_map
- \+/\- *lemma* equiv_of_equiv_symm_comp_algebra_map
- \+/\- *lemma* equiv_of_equiv_comp_algebra_map
- \+/\- *lemma* equiv_of_equiv_algebra_map
- \+/\- *lemma* equiv_of_equiv_symm_algebra_map
- \+/\- *lemma* equiv_of_equiv_symm_comp_algebra_map

modified src/ring_theory/localization.lean



## [2022-02-02 12:30:43](https://github.com/leanprover-community/mathlib/commit/4db1f96)
chore(algebra/ne_zero): revert transitivity changes ([#11760](https://github.com/leanprover-community/mathlib/pull/11760))
The `trans` methods were a disaster for `flt-regular` - this reverts them unless a better solution can be found.
#### Estimated changes
modified src/number_theory/cyclotomic/basic.lean

modified src/number_theory/cyclotomic/zeta.lean
- \+/\- *lemma* zeta_primitive_root
- \+/\- *lemma* zeta_primitive_root



## [2022-02-02 12:30:42](https://github.com/leanprover-community/mathlib/commit/6c6fbe6)
feat(group_theory/subgroup/basic): normalizer condition implies max subgroups normal ([#11597](https://github.com/leanprover-community/mathlib/pull/11597))
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* normalizer_condition.normal_of_coatom



## [2022-02-02 10:56:10](https://github.com/leanprover-community/mathlib/commit/1ed19a9)
feat(group_theory/nilpotent): p-groups are nilpotent ([#11726](https://github.com/leanprover-community/mathlib/pull/11726))
#### Estimated changes
modified src/data/fintype/basic.lean
- \+ *lemma* fintype.induction_subsingleton_or_nontrivial

modified src/group_theory/nilpotent.lean
- \+ *lemma* of_quotient_center_nilpotent
- \+ *lemma* is_p_group.is_nilpotent



## [2022-02-02 10:56:09](https://github.com/leanprover-community/mathlib/commit/c1d2860)
feat(measure_theory/probability_mass_function): Measures of sets under `pmf` monad operations ([#11613](https://github.com/leanprover-community/mathlib/pull/11613))
This PR adds explicit formulas for the measures of sets under `pmf.pure`, `pmf.bind`, and `pmf.bind_on_support`.
#### Estimated changes
modified src/measure_theory/probability_mass_function/monad.lean
- \+ *lemma* to_outer_measure_pure_apply
- \+ *lemma* to_measure_pure_apply
- \+/\- *lemma* coe_bind_apply
- \+/\- *lemma* pure_bind
- \+/\- *lemma* bind_pure
- \+/\- *lemma* bind_bind
- \+ *lemma* to_outer_measure_bind_apply
- \+ *lemma* to_measure_bind_apply
- \+ *lemma* to_outer_measure_bind_on_support_apply
- \+ *lemma* to_measure_bind_on_support_apply
- \+/\- *lemma* coe_bind_apply
- \+/\- *lemma* pure_bind
- \+/\- *lemma* bind_pure
- \+/\- *lemma* bind_bind



## [2022-02-02 10:56:08](https://github.com/leanprover-community/mathlib/commit/a687cbf)
feat(field_theory/intermediate_field, ring_theory/.., algebra/algebra… ([#11168](https://github.com/leanprover-community/mathlib/pull/11168))
If `E` is an subsemiring/subring/subalgebra/intermediate_field and e is an equivalence of the larger semiring/ring/algebra/field, then e induces an equivalence from E to E.map e. We define this equivalence.
#### Estimated changes
modified src/algebra/algebra/subalgebra.lean
- \+ *def* subalgebra_map

modified src/field_theory/intermediate_field.lean
- \+ *def* intermediate_field_map

modified src/ring_theory/subring/basic.lean
- \+ *def* subring_map

modified src/ring_theory/subsemiring/basic.lean
- \+ *def* subsemiring_map



## [2022-02-02 08:53:09](https://github.com/leanprover-community/mathlib/commit/d5d5784)
chore(ring_theory/power_basis): add `simps` ([#11766](https://github.com/leanprover-community/mathlib/pull/11766))
for flt-regular
#### Estimated changes
modified src/ring_theory/power_basis.lean



## [2022-02-02 08:53:07](https://github.com/leanprover-community/mathlib/commit/2fdc151)
refactor(power_series/basic): generalize order to semirings ([#11765](https://github.com/leanprover-community/mathlib/pull/11765))
There are still some TODOs about generalizing statements downstream of this file.
#### Estimated changes
modified src/data/finset/nat_antidiagonal.lean
- \+ *lemma* filter_fst_eq_antidiagonal
- \+ *lemma* filter_snd_eq_antidiagonal

modified src/ring_theory/power_series/basic.lean
- \+ *lemma* exists_coeff_ne_zero_iff_ne_zero
- \+/\- *lemma* order_zero
- \+ *lemma* order_finite_iff_ne_zero
- \+/\- *lemma* coeff_order
- \+/\- *lemma* order_le
- \+/\- *lemma* coeff_of_lt_order
- \+ *lemma* X_pow_order_dvd
- \+ *lemma* order_eq_multiplicity_X
- \- *lemma* order_finite_of_coeff_ne_zero
- \+/\- *lemma* coeff_order
- \+/\- *lemma* order_le
- \+/\- *lemma* coeff_of_lt_order
- \+/\- *lemma* order_zero
- \+/\- *def* order
- \+/\- *def* order



## [2022-02-02 08:53:06](https://github.com/leanprover-community/mathlib/commit/a32b0d3)
feat(group_theory/p_group): p-groups with different p are disjoint ([#11752](https://github.com/leanprover-community/mathlib/pull/11752))
#### Estimated changes
modified src/group_theory/p_group.lean
- \+ *lemma* disjoint_of_ne



## [2022-02-02 08:53:04](https://github.com/leanprover-community/mathlib/commit/664b5be)
feat(group_theory/subgroup/basic): add commute_of_normal_of_disjoint ([#11751](https://github.com/leanprover-community/mathlib/pull/11751))
#### Estimated changes
modified src/group_theory/subgroup/basic.lean
- \+ *lemma* commute_of_normal_of_disjoint



## [2022-02-02 08:53:03](https://github.com/leanprover-community/mathlib/commit/a6d70aa)
feat(order/category/*): `order_dual` as an equivalence of categories ([#11743](https://github.com/leanprover-community/mathlib/pull/11743))
For `whatever` a category of orders, define
* `whatever.iso_of_order_iso`: Turns an order isomorphism into an equivalence of objects inside `whatever`
* `whatever.to_dual`: `order_dual` as a functor from `whatever` to itself
* `whatever.dual_equiv`: The equivalence of categories between `whatever` and itself induced by `order_dual` both ways
* `order_iso.dual_dual`: The order isomorphism between `α` and `order_dual (order_dual α)`
#### Estimated changes
modified src/data/fin/basic.lean

modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_order_dual
- \+ *lemma* fintype.card_lex

modified src/order/category/LinearOrder.lean
- \+ *lemma* LinearOrder_dual_equiv_comp_forget_to_PartialOrder
- \+ *def* iso.mk
- \+ *def* to_dual
- \+ *def* dual_equiv

modified src/order/category/NonemptyFinLinOrd.lean
- \+ *lemma* NonemptyFinLinOrd_dual_equiv_comp_forget_to_LinearOrder
- \+ *def* iso.mk
- \+ *def* to_dual
- \+ *def* dual_equiv

modified src/order/category/PartialOrder.lean
- \+ *lemma* PartialOrder_dual_equiv_comp_forget_to_Preorder
- \+ *def* iso.mk
- \+ *def* to_dual
- \+ *def* dual_equiv

modified src/order/category/Preorder.lean
- \+ *def* iso.mk
- \+ *def* to_dual
- \+ *def* dual_equiv

modified src/order/hom/basic.lean
- \+ *lemma* coe_dual_dual
- \+ *lemma* coe_dual_dual_symm
- \+ *lemma* dual_dual_apply
- \+ *lemma* dual_dual_symm_apply
- \+ *def* dual_dual



## [2022-02-02 07:21:06](https://github.com/leanprover-community/mathlib/commit/400dbb3)
refactor(ring_theory/non_zero_divisors): use fun_like ([#11764](https://github.com/leanprover-community/mathlib/pull/11764))
#### Estimated changes
modified src/field_theory/ratfunc.lean

modified src/number_theory/cyclotomic/basic.lean

modified src/ring_theory/jacobson.lean

modified src/ring_theory/laurent_series.lean

modified src/ring_theory/localization.lean

modified src/ring_theory/non_zero_divisors.lean
- \+ *lemma* mem_non_zero_divisors_of_ne_zero
- \+ *lemma* map_ne_zero_of_mem_non_zero_divisors
- \+ *lemma* map_mem_non_zero_divisors
- \+ *lemma* map_le_non_zero_divisors_of_injective
- \+ *lemma* non_zero_divisors_le_comap_non_zero_divisors_of_injective
- \- *lemma* monoid_with_zero_hom.map_ne_zero_of_mem_non_zero_divisors
- \- *lemma* ring_hom.map_ne_zero_of_mem_non_zero_divisors
- \- *lemma* monoid_with_zero_hom.map_mem_non_zero_divisors
- \- *lemma* ring_hom.map_mem_non_zero_divisors
- \- *lemma* monoid_with_zero_hom.map_le_non_zero_divisors_of_injective
- \- *lemma* ring_hom.map_le_non_zero_divisors_of_injective

modified src/ring_theory/polynomial/scale_roots.lean



## [2022-02-02 07:21:05](https://github.com/leanprover-community/mathlib/commit/c8fd7e3)
chore(measure_theory/covering/besicovitch): Weaker import ([#11763](https://github.com/leanprover-community/mathlib/pull/11763))
We relax the `set_theory.cardinal_ordinal` import to the weaker `set_theory.ordinal_arithmetic` import. We also fix some trivial spacing issues in the docs.
#### Estimated changes
modified src/measure_theory/covering/besicovitch.lean



## [2022-02-02 07:21:04](https://github.com/leanprover-community/mathlib/commit/a18680a)
chore(topology/continuous_function/ordered): split from `continuous_function/basic` ([#11761](https://github.com/leanprover-community/mathlib/pull/11761))
Split material about orders out from `continuous_function/basic`, to move that file lower down the import hierarchy.
#### Estimated changes
modified src/combinatorics/configuration.lean

modified src/topology/continuous_function/algebra.lean

modified src/topology/continuous_function/basic.lean
- \- *lemma* abs_apply
- \- *lemma* le_def
- \- *lemma* lt_def
- \- *lemma* sup_coe
- \- *lemma* sup_apply
- \- *lemma* inf_coe
- \- *lemma* inf_apply
- \- *lemma* sup'_apply
- \- *lemma* sup'_coe
- \- *lemma* inf'_apply
- \- *lemma* inf'_coe
- \- *lemma* coe_Icc_extend
- \- *def* abs
- \- *def* Icc_extend

created src/topology/continuous_function/ordered.lean
- \+ *lemma* abs_apply
- \+ *lemma* le_def
- \+ *lemma* lt_def
- \+ *lemma* sup_coe
- \+ *lemma* sup_apply
- \+ *lemma* inf_coe
- \+ *lemma* inf_apply
- \+ *lemma* sup'_apply
- \+ *lemma* sup'_coe
- \+ *lemma* inf'_apply
- \+ *lemma* inf'_coe
- \+ *lemma* coe_Icc_extend
- \+ *def* abs
- \+ *def* Icc_extend

modified src/topology/homotopy/basic.lean



## [2022-02-02 07:21:03](https://github.com/leanprover-community/mathlib/commit/366fd9b)
feat(analysis/special_functions): show (2 / π) * x ≤ sin x ([#11724](https://github.com/leanprover-community/mathlib/pull/11724))
I wasn't entirely sure where to put this - trigonometric/basic is too high on the import graph but here seems to work. 
This is a fairly weak inequality but it can sometimes turn out to be useful, and is important enough to be named!
#### Estimated changes
modified src/analysis/special_functions/trigonometric/complex.lean
- \+ *lemma* lt_sin_mul
- \+ *lemma* le_sin_mul
- \+ *lemma* mul_lt_sin
- \+ *lemma* mul_le_sin



## [2022-02-02 07:21:01](https://github.com/leanprover-community/mathlib/commit/5c4c1c0)
feat(topology/homotopy): Fundamental groupoid preserves products ([#11459](https://github.com/leanprover-community/mathlib/pull/11459))
#### Estimated changes
modified src/category_theory/category/Groupoid.lean
- \+ *lemma* hom_to_functor
- \+ *lemma* pi_iso_pi_hom_π
- \+ *def* pi_limit_cone

modified src/category_theory/discrete_category.lean
- \+ *def* comp_nat_iso_discrete

modified src/category_theory/groupoid.lean

modified src/category_theory/pi/basic.lean
- \+ *lemma* eq_to_hom_proj
- \+ *lemma* pi'_eval
- \+ *lemma* pi_ext
- \+ *def* pi'

modified src/category_theory/products/basic.lean
- \+ *def* prod'

modified src/topology/homotopy/fundamental_groupoid.lean
- \+/\- *lemma* comp_eq
- \+ *lemma* id_eq_path_refl
- \+/\- *lemma* comp_eq
- \+ *def* to_top
- \+ *def* from_top
- \+ *def* to_path
- \+ *def* from_path

modified src/topology/homotopy/product.lean
- \+ *lemma* proj_map
- \+ *lemma* cone_discrete_comp_obj_map_cone
- \+ *lemma* proj_left_map
- \+ *lemma* proj_right_map
- \+ *def* proj
- \+ *def* pi_to_pi_Top
- \+ *def* pi_iso
- \+ *def* cone_discrete_comp
- \+ *def* pi_Top_to_pi_cone
- \+ *def* preserves_product
- \+ *def* proj_left
- \+ *def* proj_right
- \+ *def* prod_to_prod_Top
- \+ *def* prod_iso



## [2022-02-02 06:20:40](https://github.com/leanprover-community/mathlib/commit/fa86370)
chore(*): Golfed some random theorems ([#11769](https://github.com/leanprover-community/mathlib/pull/11769))
#### Estimated changes
modified src/algebraic_geometry/properties.lean

modified src/category_theory/simple.lean

modified src/data/nat/log.lean

modified src/ring_theory/discrete_valuation_ring.lean

modified src/topology/subset_properties.lean



## [2022-02-02 05:25:14](https://github.com/leanprover-community/mathlib/commit/8ef783b)
feat(measure_theory/measure): drop more `measurable_set` args ([#11547](https://github.com/leanprover-community/mathlib/pull/11547))
Most notably, in `measure_Union_eq_supr`.
#### Estimated changes
modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* bsupr_measure_Iic

modified src/measure_theory/decomposition/unsigned_hahn.lean

modified src/measure_theory/integral/lebesgue.lean

modified src/measure_theory/integral/set_integral.lean

modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_add_diff
- \+ *lemma* measure_diff'
- \+ *lemma* ae_eq_of_subset_of_measure_ge
- \+ *lemma* measure_Union_congr_of_subset
- \+ *lemma* measure_union_congr_of_subset
- \+ *lemma* measure_Union_to_measurable
- \+ *lemma* measure_bUnion_to_measurable
- \+ *lemma* measure_to_measurable_union
- \+ *lemma* measure_union_to_measurable
- \+/\- *lemma* measure_Union_eq_supr
- \+/\- *lemma* tendsto_measure_Union
- \+/\- *lemma* restrict_union_congr
- \+/\- *lemma* restrict_finset_bUnion_congr
- \+/\- *lemma* restrict_Union_congr
- \+/\- *lemma* restrict_bUnion_congr
- \+/\- *lemma* restrict_sUnion_congr
- \+/\- *lemma* ext_iff_of_Union_eq_univ
- \+/\- *lemma* ext_iff_of_sUnion_eq_univ
- \+ *lemma* bsupr_measure_Iic
- \+/\- *lemma* measure_Union_eq_supr
- \+/\- *lemma* tendsto_measure_Union
- \+/\- *lemma* restrict_union_congr
- \+/\- *lemma* restrict_finset_bUnion_congr
- \+/\- *lemma* restrict_Union_congr
- \+/\- *lemma* restrict_bUnion_congr
- \+/\- *lemma* restrict_sUnion_congr
- \+/\- *lemma* ext_iff_of_Union_eq_univ
- \+/\- *lemma* ext_iff_of_sUnion_eq_univ

modified src/measure_theory/measure/measure_space_def.lean
- \+ *lemma* exists_measurable_superset₂

modified src/measure_theory/measure/regular.lean
- \+/\- *lemma* of_pseudo_emetric_space
- \+/\- *lemma* is_compact_is_closed
- \+/\- *lemma* of_pseudo_emetric_space
- \+/\- *lemma* is_compact_is_closed

modified src/topology/metric_space/hausdorff_distance.lean



## [2022-02-02 02:57:46](https://github.com/leanprover-community/mathlib/commit/d68b480)
chore(linear_algebra): remove `bilinear_map` from imports in `pi` ([#11767](https://github.com/leanprover-community/mathlib/pull/11767))
Remove `bilinear_map` from imports in `pi`
#### Estimated changes
modified src/linear_algebra/pi.lean



## [2022-02-01 20:41:27](https://github.com/leanprover-community/mathlib/commit/343cbd9)
feat(sites/sheaf): simple sheaf condition in terms of limit ([#11692](https://github.com/leanprover-community/mathlib/pull/11692))
+ Given a presheaf on a site, construct a simple cone for each sieve. The sheaf condition is equivalent to all these cones being limit cones for all covering sieves of the Grothendieck topology. This is made possible by a series of work that mostly removed universe restrictions on limits.
+ Given a sieve over X : C, the diagram of its associated cone is a functor from the full subcategory of the over category C/X consisting of the arrows in the sieve, constructed from the canonical cocone over `forget : over X ⥤ C` with cone point X, which is only now added to mathlib. This cone is simpler than the multifork cone in [`is_sheaf_iff_multifork`](https://leanprover-community.github.io/mathlib_docs/category_theory/sites/sheaf.html#category_theory.presheaf.is_sheaf_iff_multifork). The underlying type of this full subcategory is equivalent to [`grothendieck_topology.cover.arrow`](https://leanprover-community.github.io/mathlib_docs/category_theory/sites/grothendieck.html#category_theory.grothendieck_topology.cover.arrow).
+ This limit sheaf condition might be more convenient to use to do sheafification, which has been done by @adamtopaz using the multifork cone before universes are sufficiently generalized for limits, though I haven't thought about it in detail. It may not be worth refactoring sheafification in terms of this sheaf condition, but we might consider using this if we ever want to do sheafification for more general (e.g. non-concrete) value categories. [#11706](https://github.com/leanprover-community/mathlib/pull/11706) is another application.
This is based on a [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/universe.20restriction.20on.20limit/near/260732627) with @adamtopaz.
#### Estimated changes
modified src/category_theory/limits/shapes/terminal.lean
- \+ *def* is_terminal_equiv_unique
- \+ *def* is_initial_equiv_unique
- \+/\- *def* terminal_is_terminal
- \+/\- *def* initial_is_initial
- \+/\- *def* terminal_is_terminal
- \+/\- *def* initial_is_initial

modified src/category_theory/over.lean
- \+ *def* forget_cocone
- \+ *def* forget_cone

modified src/category_theory/sites/sheaf.lean
- \+ *lemma* is_limit_iff_is_sheaf_for
- \+ *lemma* subsingleton_iff_is_separated_for
- \+ *lemma* is_sheaf_iff_is_limit
- \+ *lemma* is_separated_iff_subsingleton
- \+ *lemma* is_limit_iff_is_sheaf_for_presieve
- \+ *lemma* is_sheaf_iff_is_limit_pretopology
- \+ *def* cones_equiv_sieve_compatible_family
- \+ *def* _root_.category_theory.presieve.family_of_elements.sieve_compatible.cone
- \+ *def* hom_equiv_amalgamation

modified src/category_theory/sites/sheaf_of_types.lean
- \+/\- *lemma* family_of_elements.compatible.sieve_extend
- \+/\- *lemma* restrict_inj
- \+/\- *lemma* family_of_elements.compatible.sieve_extend
- \+/\- *lemma* restrict_inj

modified src/category_theory/sites/sieves.lean

modified src/category_theory/sites/spaces.lean
- \+ *lemma* pretopology_of_grothendieck

modified src/logic/unique.lean
- \+ *lemma* unique_iff_exists_unique
- \+ *lemma* unique_subtype_iff_exists_unique



## [2022-02-01 18:24:10](https://github.com/leanprover-community/mathlib/commit/ec61182)
feat(algebra/group_power): relate square equality and absolute value equality ([#11683](https://github.com/leanprover-community/mathlib/pull/11683))
#### Estimated changes
modified src/algebra/group_power/order.lean
- \+ *lemma* sq_eq_sq_iff_abs_eq_abs
- \+ *lemma* sq_eq_one_iff
- \+ *lemma* sq_ne_one_iff
- \+ *lemma* sq_le_one_iff_abs_le_one
- \+ *lemma* sq_lt_one_iff_abs_lt_one
- \+ *lemma* one_le_sq_iff_one_le_abs
- \+ *lemma* one_lt_sq_iff_one_lt_abs
- \+/\- *theorem* sq_lt_sq
- \+/\- *theorem* sq_lt_sq

modified src/analysis/inner_product_space/basic.lean



## [2022-02-01 12:46:25](https://github.com/leanprover-community/mathlib/commit/23e0e29)
chore(*): register global fact instances ([#11749](https://github.com/leanprover-community/mathlib/pull/11749))
We register globally some fact instances which are necessary for integration or euclidean spaces. And also the fact that 2 and 3 are prime. See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/euclidean_space.20error/near/269992165
#### Estimated changes
modified src/algebra/char_p/two.lean

modified src/analysis/fourier.lean

modified src/analysis/inner_product_space/l2_space.lean

modified src/analysis/inner_product_space/pi_L2.lean

modified src/analysis/inner_product_space/spectrum.lean

modified src/analysis/normed_space/pi_Lp.lean
- \- *lemma* fact_one_le_one_real
- \- *lemma* fact_one_le_two_real

modified src/data/nat/prime.lean
- \- *lemma* fact_prime_two
- \- *lemma* fact_prime_three

modified src/data/real/ennreal.lean
- \- *lemma* _root_.fact_one_le_one_ennreal
- \- *lemma* _root_.fact_one_le_two_ennreal
- \- *lemma* _root_.fact_one_le_top_ennreal

modified src/geometry/manifold/instances/real.lean

modified src/group_theory/order_of_element.lean

modified src/measure_theory/function/conditional_expectation.lean

modified src/measure_theory/function/l2_space.lean

modified src/measure_theory/function/lp_space.lean

modified src/measure_theory/function/simple_func_dense.lean

modified src/measure_theory/integral/bochner.lean

modified src/measure_theory/integral/set_integral.lean

modified src/measure_theory/integral/set_to_l1.lean

modified src/number_theory/quadratic_reciprocity.lean

modified src/topology/metric_space/gromov_hausdorff.lean

modified src/topology/metric_space/kuratowski.lean



## [2022-02-01 11:04:30](https://github.com/leanprover-community/mathlib/commit/2508cbd)
feat(model_theory/basic.lean): Elementary embeddings and elementary substructures ([#11089](https://github.com/leanprover-community/mathlib/pull/11089))
Defines elementary embeddings between structures
Defines when substructures are elementary
Provides lemmas about preservation of realizations of terms and formulas under various maps
#### Estimated changes
modified src/model_theory/basic.lean
- \+ *lemma* apply_symm_apply
- \+ *lemma* symm_apply_apply
- \+ *lemma* coe_top_equiv
- \+ *lemma* realize_term_relabel
- \+ *lemma* hom.realize_term
- \+ *lemma* embedding.realize_term
- \+ *lemma* equiv.realize_term
- \+ *lemma* realize_term_substructure
- \+ *lemma* realize_bounded_formula_relabel
- \+ *lemma* equiv.realize_bounded_formula
- \+ *lemma* realize_bounded_formula_top
- \+ *lemma* realize_formula_relabel
- \+ *lemma* realize_formula_equiv
- \+ *lemma* realize_equal
- \+ *lemma* realize_graph
- \+ *def* top_equiv
- \+ *def* term.relabel
- \+ *def* bounded_formula.relabel
- \+ *def* equal
- \+ *def* graph

created src/model_theory/elementary_maps.lean
- \+ *lemma* map_formula
- \+ *lemma* map_fun
- \+ *lemma* map_const
- \+ *lemma* map_rel
- \+ *lemma* injective
- \+ *lemma* to_embedding_to_hom
- \+ *lemma* coe_to_hom
- \+ *lemma* coe_to_embedding
- \+ *lemma* coe_injective
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* refl_apply
- \+ *lemma* comp_apply
- \+ *lemma* comp_assoc
- \+ *lemma* to_elementary_embedding_to_embedding
- \+ *lemma* coe_to_elementary_embedding
- \+ *lemma* is_elementary
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *theorem* coe_subtype
- \+ *def* to_embedding
- \+ *def* to_hom
- \+ *def* refl
- \+ *def* comp
- \+ *def* to_elementary_embedding
- \+ *def* is_elementary
- \+ *def* subtype



## [2022-02-01 10:02:45](https://github.com/leanprover-community/mathlib/commit/94a700f)
chore(set_theory/ordinal_arithmetic): Remove redundant explicit argument ([#11757](https://github.com/leanprover-community/mathlib/pull/11757))
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean



## [2022-02-01 10:02:44](https://github.com/leanprover-community/mathlib/commit/ca2a99d)
feat(set_theory/ordinal_arithmetic): Normal functions evaluated at `ω` ([#11687](https://github.com/leanprover-community/mathlib/pull/11687))
#### Estimated changes
modified src/set_theory/ordinal.lean
- \+ *theorem* eq_zero_or_pos

modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* sup_nat_cast
- \+ *theorem* is_normal.apply_omega
- \+ *theorem* sup_add_nat
- \+ *theorem* sup_mul_nat
- \+ *theorem* sup_opow_nat



## [2022-02-01 09:01:20](https://github.com/leanprover-community/mathlib/commit/cbad62c)
feat(set_theory/{ordinal_arithmetic, cardinal_ordinal}): Ordinals aren't a small type ([#11756](https://github.com/leanprover-community/mathlib/pull/11756))
We substantially golf and extend some results previously in `cardinal_ordinal.lean`.
#### Estimated changes
modified src/set_theory/cardinal_ordinal.lean
- \- *lemma* not_injective_of_ordinal
- \- *lemma* not_injective_of_ordinal_of_small

modified src/set_theory/ordinal_arithmetic.lean
- \+ *lemma* not_surjective_of_ordinal
- \+ *lemma* not_injective_of_ordinal
- \+ *lemma* not_surjective_of_ordinal_of_small
- \+ *lemma* not_injective_of_ordinal_of_small
- \+ *theorem* lsub_nmem_range
- \+ *theorem* not_small_ordinal



## [2022-02-01 08:32:51](https://github.com/leanprover-community/mathlib/commit/30dcd70)
feat(number_theory/cyclotomic/zeta): add lemmas ([#11753](https://github.com/leanprover-community/mathlib/pull/11753))
Various lemmas about `zeta`.
From flt-regular.
#### Estimated changes
modified src/number_theory/cyclotomic/basic.lean
- \+/\- *lemma* finite_dimensional
- \+ *lemma* is_galois
- \+/\- *lemma* finite_dimensional

modified src/number_theory/cyclotomic/zeta.lean
- \+ *lemma* zeta_pow
- \+/\- *lemma* zeta_primitive_root
- \+/\- *lemma* zeta_minpoly
- \+ *lemma* finrank
- \+ *lemma* norm_zeta_eq_one
- \+ *lemma* norm_zeta_sub_one_eq_eval_cyclotomic
- \+/\- *lemma* zeta_primitive_root
- \+/\- *lemma* zeta_minpoly
- \+/\- *def* zeta.embeddings_equiv_primitive_roots
- \+/\- *def* zeta.embeddings_equiv_primitive_roots



## [2022-02-01 07:42:44](https://github.com/leanprover-community/mathlib/commit/350ba8d)
feat(data/two_pointing): Two pointings of a type ([#11648](https://github.com/leanprover-community/mathlib/pull/11648))
Define `two_pointing α` as the type of two pointings of `α`. This is a Type-valued structure version of `nontrivial`.
#### Estimated changes
created src/data/two_pointing.lean
- \+ *lemma* snd_ne_fst
- \+ *lemma* swap_fst
- \+ *lemma* swap_snd
- \+ *lemma* swap_swap
- \+ *lemma* to_nontrivial
- \+ *lemma* nonempty_two_pointing_iff
- \+ *lemma* pi_fst
- \+ *lemma* pi_snd
- \+ *lemma* prod_fst
- \+ *lemma* prod_snd
- \+ *lemma* sum_fst
- \+ *lemma* sum_snd
- \+ *lemma* bool_fst
- \+ *lemma* bool_snd
- \+ *lemma* Prop_fst
- \+ *lemma* Prop_snd
- \+ *def* swap
- \+ *def* pi
- \+ *def* prod



## [2022-02-01 06:40:21](https://github.com/leanprover-community/mathlib/commit/5582d84)
feat(ring_theory/localization): fraction rings of algebraic extensions are algebraic ([#11717](https://github.com/leanprover-community/mathlib/pull/11717))
#### Estimated changes
modified src/ring_theory/algebraic.lean
- \+/\- *lemma* is_integral.is_algebraic
- \+/\- *lemma* is_algebraic_algebra_map
- \+ *lemma* is_algebraic_algebra_map_of_is_algebraic
- \+ *lemma* _root_.is_algebraic_of_larger_base_of_injective
- \+/\- *lemma* is_algebraic_of_larger_base_of_injective
- \+ *lemma* _root_.is_algebraic_of_larger_base
- \+/\- *lemma* is_integral.is_algebraic
- \+/\- *lemma* is_algebraic_algebra_map
- \+/\- *lemma* is_algebraic_of_larger_base_of_injective

modified src/ring_theory/localization.lean
- \+ *lemma* is_algebraic_iff'



## [2022-02-01 02:13:10](https://github.com/leanprover-community/mathlib/commit/4b9f048)
feat(set_theory/principal): Define `principal` ordinals ([#11679](https://github.com/leanprover-community/mathlib/pull/11679))
An ordinal `o` is said to be principal or indecomposable under an operation when the set of ordinals less than it is closed under that operation. In standard mathematical usage, this term is almost exclusively used for additive and multiplicative principal ordinals.
For simplicity, we break usual convention and regard 0 as principal.
#### Estimated changes
modified src/set_theory/ordinal_arithmetic.lean
- \+ *theorem* nfp_le

created src/set_theory/principal.lean
- \+ *theorem* principal_iff_principal_swap
- \+ *theorem* principal_zero
- \+ *theorem* principal_one_iff
- \+ *theorem* principal.iterate_lt
- \+ *theorem* op_eq_self_of_principal
- \+ *theorem* nfp_le_of_principal
- \+ *def* principal



## [2022-02-01 00:59:42](https://github.com/leanprover-community/mathlib/commit/e37daad)
feat(linear_algebra/sesquilinear_form): Add orthogonality properties ([#10992](https://github.com/leanprover-community/mathlib/pull/10992))
Generalize lemmas about orthogonality from bilinear forms to sesquilinear forms.
#### Estimated changes
modified src/linear_algebra/bilinear_map.lean
- \+/\- *theorem* map_smul₂
- \+/\- *theorem* map_smul₂

modified src/linear_algebra/sesquilinear_form.lean
- \+/\- *lemma* is_ortho_def
- \+/\- *lemma* is_ortho_zero_left
- \+/\- *lemma* is_ortho_zero_right
- \+ *lemma* is_Ortho_def
- \+/\- *lemma* ortho_smul_left
- \+/\- *lemma* ortho_smul_right
- \+ *lemma* linear_independent_of_is_Ortho
- \+/\- *lemma* is_refl
- \+/\- *lemma* ortho_comm
- \+ *lemma* mem_orthogonal_bilin_iff
- \+ *lemma* orthogonal_bilin_le
- \+ *lemma* le_orthogonal_bilin_orthogonal_bilin
- \+ *lemma* span_singleton_inf_orthogonal_eq_bot
- \+ *lemma* orthogonal_span_singleton_eq_to_lin_ker
- \+ *lemma* span_singleton_sup_orthogonal_eq_top
- \+ *lemma* is_compl_span_singleton_orthogonal
- \+/\- *lemma* is_ortho_def
- \+/\- *lemma* is_ortho_zero_left
- \+/\- *lemma* is_ortho_zero_right
- \+/\- *lemma* ortho_smul_left
- \+/\- *lemma* ortho_smul_right
- \+/\- *lemma* is_refl
- \+/\- *lemma* ortho_comm
- \+/\- *def* is_ortho
- \+ *def* is_Ortho
- \+/\- *def* is_refl
- \+/\- *def* is_alt
- \+ *def* orthogonal_bilin
- \+/\- *def* is_ortho
- \+/\- *def* is_refl
- \+/\- *def* is_alt



## [2022-02-01 00:08:19](https://github.com/leanprover-community/mathlib/commit/b52cb02)
feat(analysis/special_functions/{log, pow}): add log_base ([#11246](https://github.com/leanprover-community/mathlib/pull/11246))
Adds `real.logb`, the log base `b` of `x`, defined as `log x / log b`. Proves that this is related to `real.rpow`.
#### Estimated changes
modified src/analysis/special_functions/log.lean
- \+/\- *lemma* log_le_log
- \+/\- *lemma* log_le_log

created src/analysis/special_functions/logb.lean
- \+ *lemma* log_div_log
- \+ *lemma* logb_zero
- \+ *lemma* logb_one
- \+ *lemma* logb_abs
- \+ *lemma* logb_neg_eq_logb
- \+ *lemma* logb_mul
- \+ *lemma* logb_div
- \+ *lemma* logb_inv
- \+ *lemma* logb_rpow
- \+ *lemma* rpow_logb_eq_abs
- \+ *lemma* rpow_logb
- \+ *lemma* rpow_logb_of_neg
- \+ *lemma* surj_on_logb
- \+ *lemma* logb_surjective
- \+ *lemma* range_logb
- \+ *lemma* surj_on_logb'
- \+ *lemma* logb_le_logb
- \+ *lemma* logb_lt_logb
- \+ *lemma* logb_lt_logb_iff
- \+ *lemma* logb_le_iff_le_rpow
- \+ *lemma* logb_lt_iff_lt_rpow
- \+ *lemma* le_logb_iff_rpow_le
- \+ *lemma* lt_logb_iff_rpow_lt
- \+ *lemma* logb_pos_iff
- \+ *lemma* logb_pos
- \+ *lemma* logb_neg_iff
- \+ *lemma* logb_neg
- \+ *lemma* logb_nonneg_iff
- \+ *lemma* logb_nonneg
- \+ *lemma* logb_nonpos_iff
- \+ *lemma* logb_nonpos_iff'
- \+ *lemma* logb_nonpos
- \+ *lemma* strict_mono_on_logb
- \+ *lemma* strict_anti_on_logb
- \+ *lemma* logb_inj_on_pos
- \+ *lemma* eq_one_of_pos_of_logb_eq_zero
- \+ *lemma* logb_ne_zero_of_pos_of_ne_one
- \+ *lemma* tendsto_logb_at_top
- \+ *lemma* logb_le_logb_of_base_lt_one
- \+ *lemma* logb_lt_logb_of_base_lt_one
- \+ *lemma* logb_lt_logb_iff_of_base_lt_one
- \+ *lemma* logb_le_iff_le_rpow_of_base_lt_one
- \+ *lemma* logb_lt_iff_lt_rpow_of_base_lt_one
- \+ *lemma* le_logb_iff_rpow_le_of_base_lt_one
- \+ *lemma* lt_logb_iff_rpow_lt_of_base_lt_one
- \+ *lemma* logb_pos_iff_of_base_lt_one
- \+ *lemma* logb_pos_of_base_lt_one
- \+ *lemma* logb_neg_iff_of_base_lt_one
- \+ *lemma* logb_neg_of_base_lt_one
- \+ *lemma* logb_nonneg_iff_of_base_lt_one
- \+ *lemma* logb_nonneg_of_base_lt_one
- \+ *lemma* logb_nonpos_iff_of_base_lt_one
- \+ *lemma* strict_anti_on_logb_of_base_lt_one
- \+ *lemma* strict_mono_on_logb_of_base_lt_one
- \+ *lemma* logb_inj_on_pos_of_base_lt_one
- \+ *lemma* eq_one_of_pos_of_logb_eq_zero_of_base_lt_one
- \+ *lemma* logb_ne_zero_of_pos_of_ne_one_of_base_lt_one
- \+ *lemma* tendsto_logb_at_top_of_base_lt_one
- \+ *lemma* logb_eq_zero
- \+ *lemma* logb_prod

modified src/analysis/special_functions/pow.lean
- \+ *lemma* rpow_le_rpow_left_iff
- \+ *lemma* rpow_lt_rpow_left_iff
- \+ *lemma* rpow_le_rpow_left_iff_of_base_lt_one
- \+ *lemma* rpow_lt_rpow_left_iff_of_base_lt_one

