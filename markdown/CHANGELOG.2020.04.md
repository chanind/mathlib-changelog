## [2020-04-30 21:10:46](https://github.com/leanprover-community/mathlib/commit/c568bb4)
fix(scripts): stop updating mathlib-nightly repository ([#2576](https://github.com/leanprover-community/mathlib/pull/2576))
The `gothub` tool that we've used to push the nightlies doesn't build at the moment.  Now that we have `leanproject`, we no longer need the separate nightlies repository.
#### Estimated changes
Modified .github/workflows/build.yml


Deleted scripts/deploy_nightly.sh


Created scripts/update_branch.sh




## [2020-04-30 21:10:44](https://github.com/leanprover-community/mathlib/commit/06adf7d)
chore(scripts): update nolints.txt ([#2572](https://github.com/leanprover-community/mathlib/pull/2572))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-30 18:20:23](https://github.com/leanprover-community/mathlib/commit/caf93b7)
feat(*): small additions that prepare for Chevalley-Warning ([#2560](https://github.com/leanprover-community/mathlib/pull/2560))
A number a small changes that prepare for [#1564](https://github.com/leanprover-community/mathlib/pull/1564).
#### Estimated changes
Modified src/algebra/associated.lean
- \- *theorem* is_unit.mk0
- \- *theorem* is_unit_iff_ne_zero

Modified src/algebra/big_operators.lean
- \+ *lemma* sum_mul_sum

Modified src/algebra/group_with_zero.lean
- \+ *lemma* exists_iff_ne_zero
- \+ *lemma* is_unit.mk0
- \+ *lemma* is_unit_iff_ne_zero

Modified src/data/fintype/basic.lean
- \+ *lemma* univ_inter
- \+ *lemma* inter_univ
- \+ *lemma* set.to_finset_univ

Modified src/data/fintype/card.lean
- \+ *lemma* prod_extend_by_one

Modified src/group_theory/order_of_element.lean
- \+ *lemma* image_range_order_of
- \+ *lemma* is_cyclic.image_range_order_of
- \+ *lemma* is_cyclic.image_range_card



## [2020-04-30 14:07:21](https://github.com/leanprover-community/mathlib/commit/8fa8f17)
refactor(tsum): use ∑' instead of ∑ as notation ([#2571](https://github.com/leanprover-community/mathlib/pull/2571))
As discussed in: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/big.20ops/near/195821357
This is the result of
```
git grep -l '∑' | grep -v "mean_ineq" | xargs sed -i "s/∑/∑'/g"
```
after manually cleaning some occurences of `∑` in TeX strings. Probably `∑` has now also been changed in a lot of comments and docstrings, but my reasoning is that if the string "tsum" occurs in the file, then it doesn't do harm to write `∑'` instead of `∑` in the comments as well.
#### Estimated changes
Modified src/algebra/geom_sum.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* norm_tsum_le_tsum_norm

Modified src/analysis/specific_limits.lean
- \+/\- *lemma* tsum_geometric
- \+/\- *lemma* tsum_geometric_two
- \+/\- *lemma* tsum_geometric_two'
- \+/\- *lemma* tsum_geometric_nnreal
- \+/\- *lemma* ennreal.tsum_geometric

Modified src/data/real/cardinality.lean
- \+/\- *def* cantor_function

Modified src/measure_theory/integration.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean
- \+/\- *theorem* measure_Union_le

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/probability_mass_function.lean
- \+/\- *lemma* tsum_coe
- \+/\- *lemma* bind_apply

Modified src/measure_theory/set_integral.lean


Modified src/number_theory/bernoulli.lean


Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* summable.has_sum
- \+/\- *lemma* tsum_eq_zero_of_not_summable
- \+/\- *lemma* tsum_eq_has_sum
- \+/\- *lemma* summable.has_sum_iff
- \+/\- *lemma* tsum_zero
- \+/\- *lemma* tsum_fintype
- \+/\- *lemma* tsum_ite_eq
- \+/\- *lemma* tsum_equiv
- \+/\- *lemma* tsum_add
- \+/\- *lemma* tsum_neg
- \+/\- *lemma* tsum_sub
- \+/\- *lemma* tsum_eq_zero_add
- \+/\- *lemma* tsum_mul_left
- \+/\- *lemma* tsum_mul_right
- \+/\- *lemma* tsum_le_tsum
- \+/\- *lemma* tsum_nonneg
- \+/\- *lemma* tsum_nonpos

Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* coe_tsum



## [2020-04-30 14:07:19](https://github.com/leanprover-community/mathlib/commit/ee70afb)
doc(.github): remove pull-request template ([#2568](https://github.com/leanprover-community/mathlib/pull/2568))
Move the pull-request template to `CONTRIBUTING.md`.  This reduces the boilerplate in the PR description that almost nobody reads anyhow.
#### Estimated changes
Renamed .github/PULL_REQUEST_TEMPLATE.md to .github/CONTRIBUTING.md




## [2020-04-30 11:23:34](https://github.com/leanprover-community/mathlib/commit/9c8bc7a)
fix(tactic/interactive): make `inhabit` work on quantified goals ([#2570](https://github.com/leanprover-community/mathlib/pull/2570))
This didn't work before because of the `∀` in the goal:
```lean
lemma c {α} [nonempty α] : ∀ n : ℕ, ∃ b : α, n = n :=
by inhabit α; intro; use default _; refl
```
#### Estimated changes
Modified src/tactic/interactive.lean


Created test/inhabit.lean
- \+ *lemma* a
- \+ *lemma* c



## [2020-04-30 07:10:15](https://github.com/leanprover-community/mathlib/commit/b14a26e)
refactor(analysis/complex/exponential): split into three files in special_functions/ ([#2565](https://github.com/leanprover-community/mathlib/pull/2565))
The file `analysis/complex/exponential.lean` was growing out of control (2500 lines) and was dealing with complex and real exponentials, trigonometric functions, and power functions. I split it into three files corresponding to these three topics, and put them instead in `analysis/special_functions/`, as it was not specifically complex.
This is purely a refactor, so absolutely no new material nor changed proof.
Related Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.232565.20exponential.20split
#### Estimated changes
Modified src/analysis/ODE/gronwall.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/real_inner_product.lean


Created src/analysis/special_functions/exp_log.lean
- \+ *lemma* has_deriv_at_exp
- \+ *lemma* differentiable_exp
- \+ *lemma* differentiable_at_exp
- \+ *lemma* deriv_exp
- \+ *lemma* iter_deriv_exp
- \+ *lemma* continuous_exp
- \+ *lemma* has_deriv_at.cexp
- \+ *lemma* has_deriv_within_at.cexp
- \+ *lemma* differentiable_within_at.cexp
- \+ *lemma* differentiable_at.cexp
- \+ *lemma* differentiable_on.cexp
- \+ *lemma* differentiable.cexp
- \+ *lemma* deriv_within_cexp
- \+ *lemma* deriv_cexp
- \+ *lemma* has_deriv_at.exp
- \+ *lemma* has_deriv_within_at.exp
- \+ *lemma* differentiable_within_at.exp
- \+ *lemma* differentiable_at.exp
- \+ *lemma* differentiable_on.exp
- \+ *lemma* differentiable.exp
- \+ *lemma* deriv_within_exp
- \+ *lemma* exists_exp_eq_of_pos
- \+ *lemma* exp_log_eq_abs
- \+ *lemma* exp_log
- \+ *lemma* log_exp
- \+ *lemma* log_zero
- \+ *lemma* log_one
- \+ *lemma* log_abs
- \+ *lemma* log_neg_eq_log
- \+ *lemma* log_mul
- \+ *lemma* log_le_log
- \+ *lemma* log_lt_log
- \+ *lemma* log_lt_log_iff
- \+ *lemma* log_pos_iff
- \+ *lemma* log_pos
- \+ *lemma* log_neg_iff
- \+ *lemma* log_neg
- \+ *lemma* log_nonneg
- \+ *lemma* log_nonpos
- \+ *lemma* tendsto_log_one_zero
- \+ *lemma* continuous_log'
- \+ *lemma* continuous_at_log
- \+ *lemma* continuous_log
- \+ *lemma* has_deriv_at_log_of_pos
- \+ *lemma* has_deriv_at_log
- \+ *lemma* has_deriv_within_at.log
- \+ *lemma* has_deriv_at.log
- \+ *lemma* differentiable_within_at.log
- \+ *lemma* differentiable_at.log
- \+ *lemma* differentiable_on.log
- \+ *lemma* differentiable.log
- \+ *lemma* deriv_within_log'
- \+ *lemma* deriv_log'
- \+ *lemma* tendsto_exp_at_top
- \+ *lemma* tendsto_exp_neg_at_top_nhds_0
- \+ *lemma* tendsto_exp_div_pow_at_top
- \+ *lemma* tendsto_pow_mul_exp_neg_at_top_nhds_0

Created src/analysis/special_functions/pow.lean
- \+ *lemma* cpow_eq_pow
- \+ *lemma* cpow_def
- \+ *lemma* cpow_zero
- \+ *lemma* cpow_eq_zero_iff
- \+ *lemma* zero_cpow
- \+ *lemma* cpow_one
- \+ *lemma* one_cpow
- \+ *lemma* cpow_add
- \+ *lemma* cpow_mul
- \+ *lemma* cpow_neg
- \+ *lemma* cpow_nat_cast
- \+ *lemma* cpow_int_cast
- \+ *lemma* cpow_nat_inv_pow
- \+ *lemma* rpow_eq_pow
- \+ *lemma* rpow_def
- \+ *lemma* rpow_def_of_nonneg
- \+ *lemma* rpow_def_of_pos
- \+ *lemma* rpow_eq_zero_iff_of_nonneg
- \+ *lemma* rpow_def_of_neg
- \+ *lemma* rpow_def_of_nonpos
- \+ *lemma* rpow_pos_of_pos
- \+ *lemma* abs_rpow_le_abs_rpow
- \+ *lemma* of_real_cpow
- \+ *lemma* abs_cpow_real
- \+ *lemma* abs_cpow_inv_nat
- \+ *lemma* rpow_zero
- \+ *lemma* zero_rpow
- \+ *lemma* rpow_one
- \+ *lemma* one_rpow
- \+ *lemma* rpow_nonneg_of_nonneg
- \+ *lemma* rpow_add
- \+ *lemma* rpow_mul
- \+ *lemma* rpow_neg
- \+ *lemma* rpow_nat_cast
- \+ *lemma* rpow_int_cast
- \+ *lemma* mul_rpow
- \+ *lemma* one_le_rpow
- \+ *lemma* rpow_le_rpow
- \+ *lemma* rpow_lt_rpow
- \+ *lemma* rpow_lt_rpow_of_exponent_lt
- \+ *lemma* rpow_le_rpow_of_exponent_le
- \+ *lemma* rpow_lt_rpow_of_exponent_gt
- \+ *lemma* rpow_le_rpow_of_exponent_ge
- \+ *lemma* rpow_le_one
- \+ *lemma* one_lt_rpow
- \+ *lemma* rpow_lt_one
- \+ *lemma* pow_nat_rpow_nat_inv
- \+ *lemma* rpow_nat_inv_pow_nat
- \+ *lemma* continuous_rpow_aux1
- \+ *lemma* continuous_rpow_aux2
- \+ *lemma* continuous_at_rpow_of_ne_zero
- \+ *lemma* continuous_rpow_aux3
- \+ *lemma* continuous_at_rpow_of_pos
- \+ *lemma* continuous_at_rpow
- \+ *lemma* continuous_rpow
- \+ *lemma* continuous_rpow_of_ne_zero
- \+ *lemma* continuous_rpow_of_pos
- \+ *lemma* sqrt_eq_rpow
- \+ *lemma* continuous_sqrt
- \+ *lemma* coe_rpow
- \+ *lemma* rpow_eq_zero_iff
- \+ *lemma* filter.tendsto.nnrpow

Renamed src/analysis/complex/exponential.lean to src/analysis/special_functions/trigonometric.lean
- \- *lemma* has_deriv_at_exp
- \- *lemma* differentiable_exp
- \- *lemma* differentiable_at_exp
- \- *lemma* deriv_exp
- \- *lemma* iter_deriv_exp
- \- *lemma* continuous_exp
- \- *lemma* has_deriv_at.cexp
- \- *lemma* has_deriv_within_at.cexp
- \- *lemma* differentiable_within_at.cexp
- \- *lemma* differentiable_at.cexp
- \- *lemma* differentiable_on.cexp
- \- *lemma* differentiable.cexp
- \- *lemma* deriv_within_cexp
- \- *lemma* deriv_cexp
- \- *lemma* has_deriv_at.exp
- \- *lemma* has_deriv_within_at.exp
- \- *lemma* differentiable_within_at.exp
- \- *lemma* differentiable_at.exp
- \- *lemma* differentiable_on.exp
- \- *lemma* differentiable.exp
- \- *lemma* deriv_within_exp
- \- *lemma* exists_exp_eq_of_pos
- \- *lemma* exp_log_eq_abs
- \- *lemma* exp_log
- \- *lemma* log_exp
- \- *lemma* log_zero
- \- *lemma* log_one
- \- *lemma* log_abs
- \- *lemma* log_neg_eq_log
- \- *lemma* log_mul
- \- *lemma* log_le_log
- \- *lemma* log_lt_log
- \- *lemma* log_lt_log_iff
- \- *lemma* log_pos_iff
- \- *lemma* log_pos
- \- *lemma* log_neg_iff
- \- *lemma* log_neg
- \- *lemma* log_nonneg
- \- *lemma* log_nonpos
- \- *lemma* tendsto_log_one_zero
- \- *lemma* continuous_log'
- \- *lemma* continuous_at_log
- \- *lemma* continuous_log
- \- *lemma* has_deriv_at_log_of_pos
- \- *lemma* has_deriv_at_log
- \- *lemma* has_deriv_within_at.log
- \- *lemma* has_deriv_at.log
- \- *lemma* differentiable_within_at.log
- \- *lemma* differentiable_at.log
- \- *lemma* differentiable_on.log
- \- *lemma* differentiable.log
- \- *lemma* deriv_within_log'
- \- *lemma* deriv_log'
- \- *lemma* cpow_eq_pow
- \- *lemma* cpow_def
- \- *lemma* cpow_zero
- \- *lemma* cpow_eq_zero_iff
- \- *lemma* zero_cpow
- \- *lemma* cpow_one
- \- *lemma* one_cpow
- \- *lemma* cpow_add
- \- *lemma* cpow_mul
- \- *lemma* cpow_neg
- \- *lemma* cpow_nat_cast
- \- *lemma* cpow_int_cast
- \- *lemma* cpow_nat_inv_pow
- \- *lemma* rpow_eq_pow
- \- *lemma* rpow_def
- \- *lemma* rpow_def_of_nonneg
- \- *lemma* rpow_def_of_pos
- \- *lemma* rpow_eq_zero_iff_of_nonneg
- \- *lemma* rpow_def_of_neg
- \- *lemma* rpow_def_of_nonpos
- \- *lemma* rpow_pos_of_pos
- \- *lemma* abs_rpow_le_abs_rpow
- \- *lemma* of_real_cpow
- \- *lemma* abs_cpow_real
- \- *lemma* abs_cpow_inv_nat
- \- *lemma* rpow_zero
- \- *lemma* zero_rpow
- \- *lemma* rpow_one
- \- *lemma* one_rpow
- \- *lemma* rpow_nonneg_of_nonneg
- \- *lemma* rpow_add
- \- *lemma* rpow_mul
- \- *lemma* rpow_neg
- \- *lemma* rpow_nat_cast
- \- *lemma* rpow_int_cast
- \- *lemma* mul_rpow
- \- *lemma* one_le_rpow
- \- *lemma* rpow_le_rpow
- \- *lemma* rpow_lt_rpow
- \- *lemma* rpow_lt_rpow_of_exponent_lt
- \- *lemma* rpow_le_rpow_of_exponent_le
- \- *lemma* rpow_lt_rpow_of_exponent_gt
- \- *lemma* rpow_le_rpow_of_exponent_ge
- \- *lemma* rpow_le_one
- \- *lemma* one_lt_rpow
- \- *lemma* rpow_lt_one
- \- *lemma* pow_nat_rpow_nat_inv
- \- *lemma* rpow_nat_inv_pow_nat
- \- *lemma* continuous_rpow_aux1
- \- *lemma* continuous_rpow_aux2
- \- *lemma* continuous_at_rpow_of_ne_zero
- \- *lemma* continuous_rpow_aux3
- \- *lemma* continuous_at_rpow_of_pos
- \- *lemma* continuous_at_rpow
- \- *lemma* continuous_rpow
- \- *lemma* continuous_rpow_of_ne_zero
- \- *lemma* continuous_rpow_of_pos
- \- *lemma* sqrt_eq_rpow
- \- *lemma* continuous_sqrt
- \- *lemma* tendsto_exp_at_top
- \- *lemma* tendsto_exp_neg_at_top_nhds_0
- \- *lemma* tendsto_exp_div_pow_at_top
- \- *lemma* tendsto_pow_mul_exp_neg_at_top_nhds_0
- \- *lemma* has_deriv_at.rexp
- \- *lemma* has_deriv_within_at.rexp
- \- *lemma* coe_rpow
- \- *lemma* rpow_eq_zero_iff
- \- *lemma* filter.tendsto.nnrpow

Modified src/data/real/pi.lean


Modified test/differentiable.lean


Modified test/simp_command.lean




## [2020-04-29 17:26:19](https://github.com/leanprover-community/mathlib/commit/e6491de)
chore(data/equiv/ring): make ring_aut reducible ([#2563](https://github.com/leanprover-community/mathlib/pull/2563))
This makes the coercion to fun work. This is the same approach as we used for `perm` and it worked okay for `perm`.
Related Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/ring_aut.20coerce.20to.20function
#### Estimated changes
Modified src/data/equiv/ring.lean
- \+/\- *def* ring_aut



## [2020-04-29 16:12:56](https://github.com/leanprover-community/mathlib/commit/8490c54)
refactor(analysis/complex/exponential): define log x = log |x|  for x < 0 ([#2564](https://github.com/leanprover-community/mathlib/pull/2564))
Previously we had `log  x = 0` for `x < 0`. This PR changes it to `log x = log (-x)`, to make sure that the formulas `log (xy) = log x + log y` and `log' = 1/x` are true for all nonzero variables.
Also, add a few simp lemmas on the differentiability properties of `log` to make sure that the following works:
```lean
example (x : ℝ) (h : x ≠ 0) : deriv (λ x, x * (log x - 1)) x = log x :=
by simp [h]
```
Related Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/definition.20of.20real.20log
#### Estimated changes
Modified src/analysis/complex/exponential.lean
- \+ *lemma* exp_log_eq_abs
- \+/\- *lemma* exp_log
- \+ *lemma* log_abs
- \+ *lemma* log_neg_eq_log
- \+/\- *lemma* log_mul
- \+/\- *lemma* log_le_log
- \+/\- *lemma* log_pos_iff
- \+/\- *lemma* log_pos
- \+/\- *lemma* log_nonpos
- \+ *lemma* has_deriv_at_log_of_pos
- \+/\- *lemma* has_deriv_at_log
- \+ *lemma* has_deriv_within_at.log
- \+ *lemma* has_deriv_at.log
- \+ *lemma* differentiable_within_at.log
- \+ *lemma* differentiable_at.log
- \+ *lemma* differentiable_on.log
- \+ *lemma* differentiable.log
- \+ *lemma* deriv_within_log'
- \+ *lemma* deriv_log'
- \+ *lemma* log_of_real_re
- \+/\- *lemma* rpow_def_of_neg

Modified test/differentiable.lean




## [2020-04-29 13:32:57](https://github.com/leanprover-community/mathlib/commit/4580069)
feat(field_theory/subfield): is_subfield.inter and is_subfield.Inter ([#2562](https://github.com/leanprover-community/mathlib/pull/2562))
Prove that intersection of subfields is subfield.
#### Estimated changes
Modified src/field_theory/subfield.lean




## [2020-04-29 10:32:44](https://github.com/leanprover-community/mathlib/commit/84f8b39)
chore(data/nat/basic): move `iterate_inj` to `injective.iterate` ([#2561](https://github.com/leanprover-community/mathlib/pull/2561))
Also add versions for `surjective` and `bijective`
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *theorem* iterate_ind
- \+ *theorem* injective.iterate
- \+ *theorem* surjective.iterate
- \+ *theorem* bijective.iterate
- \- *theorem* iterate_inj

Modified src/field_theory/perfect_closure.lean




## [2020-04-29 07:43:15](https://github.com/leanprover-community/mathlib/commit/f8fe596)
chore(algebra/*): missing `simp`/`inj` lemmas ([#2557](https://github.com/leanprover-community/mathlib/pull/2557))
Sometimes I have a specialized `ext` lemma for `A →+ B` that uses structure of `A` (e.g., `A = monoid_algebra α R`) and want to apply it to `A →+* B` or `A →ₐ[R] B`. These `coe_*_inj` lemmas make it easier.
Also add missing `simp` lemmas for bundled multiplication and rename `pow_of_add` and `gpow_of_add` to `of_add_smul` and `of_add_gsmul`, respectively.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* coe_mul_left
- \+ *lemma* mul_right_apply

Modified src/algebra/group_power.lean
- \+ *lemma* of_add_smul
- \+ *lemma* of_add_gsmul
- \+ *lemma* powers_hom_apply
- \+ *lemma* powers_hom_symm_apply
- \+ *lemma* mnat_monoid_hom_eq
- \+ *lemma* mnat_monoid_hom_ext
- \- *lemma* pow_of_add
- \- *lemma* gpow_of_add

Modified src/algebra/ring.lean
- \+/\- *lemma* coe_monoid_hom
- \+/\- *lemma* coe_add_monoid_hom
- \- *lemma* coe_monoid_hom'
- \- *lemma* coe_add_monoid_hom'
- \+ *theorem* coe_add_monoid_hom_inj
- \+ *theorem* coe_monoid_hom_inj

Modified src/ring_theory/algebra.lean
- \+ *lemma* coe_to_add_monoid_hom
- \+ *theorem* coe_fn_inj
- \+ *theorem* coe_ring_hom_inj
- \+ *theorem* coe_monoid_hom_inj
- \+ *theorem* coe_add_monoid_hom_inj



## [2020-04-29 05:44:26](https://github.com/leanprover-community/mathlib/commit/cb3a017)
chore(category_theory): remove `[𝒞 : category.{v₁} C] / include 𝒞` ([#2556](https://github.com/leanprover-community/mathlib/pull/2556))
It is no longer necessary in Lean 3.9.0, thanks to
https://github.com/leanprover-community/lean/commit/01063857bb6814374156433e8cbc0c94a9483f52
#### Estimated changes
Modified docs/theories/category_theory.md


Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/comma.lean


Modified src/category_theory/connected.lean


Modified src/category_theory/const.lean


Modified src/category_theory/core.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/differential_object.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/endomorphism.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/functor_category.lean


Modified src/category_theory/functorial.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/hom_functor.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/isomorphism_classes.lean


Modified src/category_theory/limits/concrete_category.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/constructions/equalizers.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/strong_epi.lean


Modified src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/limits/shapes/wide_pullbacks.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/monad/basic.lean


Modified src/category_theory/monad/limits.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/monoidal/of_has_finite_products.lean


Modified src/category_theory/natural_isomorphism.lean


Modified src/category_theory/natural_transformation.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/pempty.lean


Modified src/category_theory/products/associator.lean


Modified src/category_theory/products/basic.lean


Modified src/category_theory/products/bifunctor.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/reflect_isomorphisms.lean


Modified src/category_theory/shift.lean


Modified src/category_theory/sums/associator.lean


Modified src/category_theory/sums/basic.lean


Modified src/category_theory/types.lean


Modified src/category_theory/whiskering.lean


Modified src/category_theory/yoneda.lean




## [2020-04-29 04:34:22](https://github.com/leanprover-community/mathlib/commit/ba9fc4d)
doc(install/*): remove outdated youtube links ([#2559](https://github.com/leanprover-community/mathlib/pull/2559))
Fixes [#2558](https://github.com/leanprover-community/mathlib/pull/2558).
#### Estimated changes
Modified docs/install/macos.md


Modified docs/install/windows.md




## [2020-04-28 23:03:24](https://github.com/leanprover-community/mathlib/commit/94ff59a)
chore(scripts): update nolints.txt ([#2555](https://github.com/leanprover-community/mathlib/pull/2555))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-28 19:57:52](https://github.com/leanprover-community/mathlib/commit/d12db89)
chore(category): rename to control ([#2516](https://github.com/leanprover-community/mathlib/pull/2516))
This is parallel to https://github.com/leanprover-community/lean/pull/202 for community Lean (now merged).
It seems the changes are actually completely independent; this compiles against current community Lean, and that PR. (I'm surprised, but I guess it's just that everything is in the root namespace, and in `init/`.)
This PR anticipates then renaming `category_theory/` to `category/`.
#### Estimated changes
Deleted src/category/traversable/default.lean


Modified src/category_theory/core.lean


Renamed src/category/applicative.lean to src/control/applicative.lean


Renamed src/category/basic.lean to src/control/basic.lean


Renamed src/category/bifunctor.lean to src/control/bifunctor.lean


Renamed src/category/bitraversable/basic.lean to src/control/bitraversable/basic.lean


Renamed src/category/bitraversable/instances.lean to src/control/bitraversable/instances.lean


Renamed src/category/bitraversable/lemmas.lean to src/control/bitraversable/lemmas.lean


Renamed src/category/equiv_functor.lean to src/control/equiv_functor.lean


Renamed src/category/equiv_functor/instances.lean to src/control/equiv_functor/instances.lean


Renamed src/category/fold.lean to src/control/fold.lean


Renamed src/category/functor.lean to src/control/functor.lean


Renamed src/category/monad/basic.lean to src/control/monad/basic.lean


Renamed src/category/monad/cont.lean to src/control/monad/cont.lean


Renamed src/category/monad/writer.lean to src/control/monad/writer.lean


Renamed src/category/traversable/basic.lean to src/control/traversable/basic.lean


Created src/control/traversable/default.lean


Renamed src/category/traversable/derive.lean to src/control/traversable/derive.lean


Renamed src/category/traversable/equiv.lean to src/control/traversable/equiv.lean


Renamed src/category/traversable/instances.lean to src/control/traversable/instances.lean


Renamed src/category/traversable/lemmas.lean to src/control/traversable/lemmas.lean


Modified src/data/array/lemmas.lean


Modified src/data/buffer/basic.lean


Modified src/data/dlist/instances.lean


Modified src/data/equiv/functor.lean


Modified src/data/fin_enum.lean


Modified src/data/lazy_list2.lean


Modified src/data/multiset.lean


Modified src/tactic/converter/old_conv.lean


Modified src/tactic/core.lean


Modified src/tactic/equiv_rw.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/squeeze.lean


Modified test/equiv_rw.lean


Modified test/traversable.lean




## [2020-04-28 19:57:50](https://github.com/leanprover-community/mathlib/commit/c435b1c)
feat(analysis/calculus/inverse): Inverse function theorem ([#2228](https://github.com/leanprover-community/mathlib/pull/2228))
Ref [#1849](https://github.com/leanprover-community/mathlib/pull/1849)
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *lemma* is_o.def'
- \+ *theorem* is_o.right_is_O_sub
- \+ *theorem* is_o.right_is_O_add

Modified src/analysis/calculus/deriv.lean
- \+ *theorem* has_strict_deriv_at.has_strict_fderiv_at_equiv
- \+ *theorem* has_deriv_at.has_fderiv_at_equiv
- \+ *theorem* has_strict_deriv_at.of_local_left_inverse
- \+ *theorem* has_deriv_at.of_local_left_inverse

Modified src/analysis/calculus/fderiv.lean
- \+ *lemma* has_strict_fderiv_at.is_O_sub_rev
- \+ *lemma* has_fderiv_at_filter.is_O_sub_rev
- \- *lemma* has_strict_fderiv_at.has_fderiv_at
- \- *lemma* has_strict_fderiv_at.differentiable_at
- \- *lemma* has_strict_fderiv_at.continuous_at
- \- *lemma* has_strict_fderiv_at.comp
- \- *lemma* has_strict_fderiv_at.prod
- \+ *theorem* has_strict_fderiv_at.of_local_left_inverse
- \+ *theorem* has_fderiv_at.of_local_left_inverse

Created src/analysis/calculus/inverse.lean
- \+ *lemma* lipschitz_sub
- \+ *lemma* inverse_continuous_on
- \+ *lemma* inverse_approx_map_sub
- \+ *lemma* inverse_approx_map_dist_self
- \+ *lemma* inverse_approx_map_dist_self_le
- \+ *lemma* inverse_approx_map_fixed_iff
- \+ *lemma* inverse_approx_map_contracts_on
- \+ *lemma* inverse_approx_map_maps_to
- \+ *lemma* to_local_homeomorph_to_fun
- \+ *lemma* to_local_homeomorph_source
- \+ *lemma* to_local_homeomorph_target
- \+ *lemma* closed_ball_subset_target
- \+ *lemma* approximates_deriv_on_nhds
- \+ *lemma* approximates_deriv_on_open_nhds
- \+ *lemma* mem_to_local_homeomorph_source
- \+ *lemma* image_mem_to_local_homeomorph_target
- \+ *lemma* eventually_left_inverse
- \+ *lemma* local_inverse_apply_image
- \+ *lemma* eventually_right_inverse
- \+ *lemma* local_inverse_continuous_at
- \+ *theorem* mono_num
- \+ *theorem* mono_set
- \+ *theorem* surj_on_closed_ball
- \+ *theorem* to_local_inverse
- \+ *theorem* to_local_left_inverse
- \+ *def* approximates_linear_on
- \+ *def* to_local_equiv
- \+ *def* inverse_approx_map
- \+ *def* to_local_homeomorph
- \+ *def* local_inverse

Modified src/analysis/complex/exponential.lean
- \+ *lemma* has_deriv_at_log

Modified src/analysis/normed_space/operator_norm.lean
- \+ *theorem* is_O_comp
- \+ *theorem* is_O_sub
- \+ *theorem* is_O_comp_rev
- \+ *theorem* is_O_sub_rev

Modified src/topology/local_homeomorph.lean
- \+ *lemma* inv_fun_tendsto

Modified src/topology/metric_space/antilipschitz.lean




## [2020-04-28 17:54:30](https://github.com/leanprover-community/mathlib/commit/3c02800)
chore(data/dfinsupp): use more precise `decidable` requirement ([#2535](https://github.com/leanprover-community/mathlib/pull/2535))
Removed `decidable_zero_symm` and replaced all `[Π i, decidable_pred (eq (0 : β i))]` with `[Π i (x : β i), decidable (x ≠ 0)]`. This should work better with `open_locale classical` because now the lemmas and definitions don't assume that `[Π i (x : β i), decidable (x ≠ 0)]` comes from `decidable_zero_symm`.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \+/\- *lemma* sub_apply
- \+/\- *lemma* smul_apply
- \+/\- *lemma* subtype_domain_add
- \+/\- *lemma* subtype_domain_neg
- \+/\- *lemma* subtype_domain_sub
- \+/\- *lemma* single_apply
- \+/\- *lemma* map_range_def
- \+/\- *lemma* support_add
- \+/\- *lemma* support_neg
- \+/\- *lemma* prod_zero_index
- \+/\- *lemma* prod_single_index
- \+/\- *lemma* prod_neg_index
- \+/\- *lemma* sum_zero
- \+/\- *lemma* sum_add
- \+/\- *lemma* sum_neg
- \+/\- *lemma* prod_add_index
- \+/\- *lemma* sum_sub_index
- \+/\- *lemma* prod_subtype_domain_index
- \+/\- *theorem* support_mk_subset
- \+/\- *theorem* eq_mk_support
- \+/\- *def* dfinsupp
- \+/\- *def* zip_with
- \+/\- *def* to_has_scalar
- \+/\- *def* to_module
- \+/\- *def* sum
- \+/\- *def* prod
- \- *def* decidable_zero_symm



## [2020-04-28 15:02:18](https://github.com/leanprover-community/mathlib/commit/f6c9372)
feat(data/fin): add some lemmas about coercions ([#2522](https://github.com/leanprover-community/mathlib/pull/2522))
Two of these lemmas allow norm_cast to work with inequalities
involving fin values converted to ℕ.  The rest are for simplifying
expressions where coercions are used to convert from ℕ to fin, in
cases where an inequality means those coercions do not in fact change
the value.
There are very few lemmas relating to coercions from ℕ to fin in
mathlib at present; the lemma of_nat_eq_coe (and val_add on which it
depends, and a few similarly trivial lemmas alongside val_add) is
moved from data.zmod.basic to fin.basic for use in proving the other
lemmas, while the nat lemma add_mod is moved to data.nat.basic for use
in the proof of of_nat_eq_coe, and mul_mod is moved alongside it as
suggested in review.  These lemmas were found useful in formalising
solutions to an olympiad problem, see
<https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Some.20olympiad.20formalisations>,
and seem more generally relevant than to just that particular problem.
#### Estimated changes
Modified src/data/fin.lean
- \+ *lemma* coe_fin_lt
- \+ *lemma* coe_fin_le
- \+ *lemma* val_add
- \+ *lemma* val_mul
- \+ *lemma* one_val
- \+ *lemma* zero_val
- \+ *lemma* of_nat_eq_coe
- \+ *lemma* coe_val_of_lt
- \+ *lemma* coe_val_eq_self
- \+ *lemma* coe_coe_of_lt
- \+ *lemma* coe_coe_eq_self

Modified src/data/nat/basic.lean
- \+ *lemma* add_mod
- \+ *lemma* mul_mod

Modified src/data/nat/modeq.lean
- \- *lemma* add_mod
- \- *lemma* mul_mod

Modified src/data/zmod/basic.lean
- \- *lemma* val_add
- \- *lemma* val_mul
- \- *lemma* one_val
- \- *lemma* zero_val
- \- *lemma* of_nat_eq_coe



## [2020-04-28 12:08:15](https://github.com/leanprover-community/mathlib/commit/f567962)
feat(data/complex/basic): inv_I and div_I ([#2550](https://github.com/leanprover-community/mathlib/pull/2550))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *lemma* div_I
- \+ *lemma* inv_I



## [2020-04-28 12:08:13](https://github.com/leanprover-community/mathlib/commit/9c81886)
fix(tactic/doc_commands): clean up copy_doc_string command ([#2543](https://github.com/leanprover-community/mathlib/pull/2543))
[#2471](https://github.com/leanprover-community/mathlib/pull/2471) added a command for copying a doc string from one decl to another. This PR:
* documents this command
* extends it to copy to a list of decls
* moves `add_doc_string` from root to the `tactic` namespace
#### Estimated changes
Modified src/tactic/doc_commands.lean


Modified src/tactic/nth_rewrite/default.lean




## [2020-04-28 06:54:15](https://github.com/leanprover-community/mathlib/commit/ae06db3)
feat(category_theory/concrete): make constructing morphisms easier ([#2502](https://github.com/leanprover-community/mathlib/pull/2502))
Previously, if you wrote:
```lean
example (R : CommMon.{u}) : R ⟶ R :=
{ to_fun := λ x, _,
  map_one' := sorry,
  map_mul' := sorry, }
```
you were told the expected type was `↥(bundled.map comm_monoid.to_monoid R)`, which is not particularly reassuring unless you understand the details of how we've set up concrete categories.
If you called `dsimp`, this got better, just giving `R.α`. This still isn't ideal, as we prefer to talk about the underlying type of a bundled object via the coercion, not the structure projection.
After this PR, which provides a slightly different mechanism for constructing "induced" categories from bundled categories, the expected type is exactly what you might have hoped for: `↥R`.
There seems to be one place where we used to get away with writing `𝟙 _` and now have to write `𝟙 A`, but otherwise there appear to be no ill-effects of this change.
(For follow-up, I think I can entirely get rid of our `local attribute [reducible]` work-arounds when setting up concrete categories, and in fact construct most of the instances in `@[derive]` handlers, but these will be separate PRs.)
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean
- \+/\- *def* Ring
- \+/\- *def* CommSemiRing
- \+/\- *def* CommRing

Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebra/category/Group/basic.lean
- \+/\- *def* Group
- \+/\- *def* CommGroup

Modified src/algebra/category/Mon/basic.lean
- \+/\- *def* CommMon

Modified src/category_theory/concrete_category/bundled_hom.lean
- \+ *def* map_hom
- \+ *def* map

Modified src/tactic/interactive.lean




## [2020-04-27 16:34:48](https://github.com/leanprover-community/mathlib/commit/fd3afb4)
chore(ring_theory/algebra): move instances about complex to get rid of dependency ([#2549](https://github.com/leanprover-community/mathlib/pull/2549))
Previously `ring_theory.algebra` imported the complex numbers. This PR moves some instances in order to get rid of that dependency.
#### Estimated changes
Modified src/analysis/convex/basic.lean


Created src/data/complex/module.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/power_series.lean


Modified src/topology/algebra/polynomial.lean




## [2020-04-27 14:30:55](https://github.com/leanprover-community/mathlib/commit/948d0ff)
chore(topology/algebra/module): don't use unbundled homs for `algebra` instance ([#2545](https://github.com/leanprover-community/mathlib/pull/2545))
Define special `algebra.of_semimodule` and `algebra.of_semimodule'`
constructors instead.
ref. [#2534](https://github.com/leanprover-community/mathlib/pull/2534)
#### Estimated changes
Modified src/ring_theory/algebra.lean
- \+ *def* of_semimodule'
- \+ *def* of_semimodule

Modified src/topology/algebra/module.lean
- \+ *lemma* mul_apply



## [2020-04-27 05:41:19](https://github.com/leanprover-community/mathlib/commit/2fc9b15)
chore(data/real/*): use bundled homs to prove `coe_sum` etc ([#2533](https://github.com/leanprover-community/mathlib/pull/2533))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* ring_hom.map_list_prod
- \+ *lemma* ring_hom.map_list_sum
- \+ *lemma* ring_hom.map_multiset_prod
- \+ *lemma* ring_hom.map_multiset_sum

Modified src/data/real/ennreal.lean
- \+ *lemma* coe_of_nnreal_hom
- \+ *def* of_nnreal_hom

Modified src/data/real/nnreal.lean
- \+ *lemma* coe_to_real_hom
- \+ *def* to_real_hom



## [2020-04-26 21:58:07](https://github.com/leanprover-community/mathlib/commit/134c5a5)
chore(scripts): update nolints.txt ([#2548](https://github.com/leanprover-community/mathlib/pull/2548))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-26 20:47:49](https://github.com/leanprover-community/mathlib/commit/039c5a6)
chore(ring_theory/adjoin_root): drop `is_ring_hom` instance ([#2546](https://github.com/leanprover-community/mathlib/pull/2546))
ref [#2534](https://github.com/leanprover-community/mathlib/pull/2534)
#### Estimated changes
Modified src/ring_theory/adjoin_root.lean




## [2020-04-26 19:06:10](https://github.com/leanprover-community/mathlib/commit/942b795)
doc(field_theory/subfield): don't mention unbundled homs in the comment ([#2544](https://github.com/leanprover-community/mathlib/pull/2544))
ref [#2534](https://github.com/leanprover-community/mathlib/pull/2534)
#### Estimated changes
Modified src/field_theory/subfield.lean




## [2020-04-26 13:59:51](https://github.com/leanprover-community/mathlib/commit/fa13d16)
chore(scripts): update nolints.txt ([#2542](https://github.com/leanprover-community/mathlib/pull/2542))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-26 12:04:36](https://github.com/leanprover-community/mathlib/commit/30ae5ba)
chore(scripts): update nolints.txt ([#2541](https://github.com/leanprover-community/mathlib/pull/2541))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-26 12:04:34](https://github.com/leanprover-community/mathlib/commit/74b9647)
feat(measure_theory/measure_space): pigeonhole principle in a measure space ([#2538](https://github.com/leanprover-community/mathlib/pull/2538))
ref [#2272](https://github.com/leanprover-community/mathlib/pull/2272)
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* sum_volume_le_volume_univ
- \+ *lemma* tsum_volume_le_volume_univ
- \+ *lemma* exists_nonempty_inter_of_volume_univ_lt_tsum_volume
- \+ *lemma* exists_nonempty_inter_of_volume_univ_lt_sum_volume



## [2020-04-26 09:29:30](https://github.com/leanprover-community/mathlib/commit/c170ce3)
chore(data/finset): add `coe_map`, `coe_image_subset_range`, and `coe_map_subset_range` ([#2530](https://github.com/leanprover-community/mathlib/pull/2530))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* coe_map
- \+ *theorem* coe_map_subset_range
- \+ *theorem* coe_image_subset_range



## [2020-04-26 09:29:28](https://github.com/leanprover-community/mathlib/commit/40e97d3)
feat(topology/algebra/module): ker, range, cod_restrict, subtype_val, coprod ([#2525](https://github.com/leanprover-community/mathlib/pull/2525))
Also move `smul_right` to `general_ring` and define some
maps/equivalences useful for the inverse/implicit function theorem.
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* coe_mk

Modified src/topology/algebra/module.lean
- \+ *lemma* ker_coe
- \+ *lemma* mem_ker
- \+ *lemma* is_closed_ker
- \+ *lemma* apply_ker
- \+ *lemma* range_coe
- \+ *lemma* mem_range
- \+ *lemma* coe_cod_restrict
- \+ *lemma* coe_cod_restrict_apply
- \+ *lemma* coe_subtype_val
- \+ *lemma* subtype_val_apply
- \+ *lemma* coe_prod_map'
- \+ *lemma* coe_coprod
- \+ *lemma* coprod_apply
- \+ *lemma* coe_proj_ker_of_right_inverse_apply
- \+ *lemma* proj_ker_of_right_inverse_apply_idem
- \+ *lemma* proj_ker_of_right_inverse_comp_inv
- \+ *lemma* smul_right_comp
- \+/\- *lemma* smul_comp
- \+/\- *lemma* smul_apply
- \+/\- *lemma* coe_apply
- \+/\- *lemma* coe_apply'
- \+/\- *lemma* comp_smul
- \+ *lemma* ext₁
- \+ *lemma* equiv_of_inverse_apply
- \+ *lemma* symm_equiv_of_inverse
- \+ *lemma* units_equiv_aut_apply
- \+ *lemma* units_equiv_aut_apply_symm
- \+ *lemma* units_equiv_aut_symm_apply
- \+ *lemma* fst_equiv_of_right_inverse
- \+ *lemma* snd_equiv_of_right_inverse
- \+ *lemma* equiv_of_right_inverse_symm_apply
- \- *lemma* prod_map_apply
- \+ *def* ker
- \+ *def* range
- \+ *def* cod_restrict
- \+ *def* subtype_val
- \+ *def* coprod
- \+ *def* proj_ker_of_right_inverse
- \+ *def* equiv_of_inverse
- \+ *def* units_equiv_aut
- \+ *def* equiv_of_right_inverse



## [2020-04-26 09:29:26](https://github.com/leanprover-community/mathlib/commit/11ccc1b)
feat(analysis/calculus/deriv): define `has_strict_deriv_at` ([#2524](https://github.com/leanprover-community/mathlib/pull/2524))
Also make more proofs explicitly use their `has_fderiv*` counterparts
and mark some lemmas in `fderiv` as `protected`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* has_fderiv_at_filter.has_deriv_at_filter
- \+ *lemma* has_fderiv_within_at.has_deriv_within_at
- \+ *lemma* has_fderiv_at.has_deriv_at
- \+ *lemma* has_strict_fderiv_at_iff_has_strict_deriv_at
- \+ *lemma* has_strict_fderiv_at.has_strict_deriv_at
- \+ *lemma* continuous_linear_map.has_deriv_at_filter
- \+ *lemma* continuous_linear_map.has_strict_deriv_at
- \+ *lemma* continuous_linear_map.has_deriv_at
- \+ *lemma* continuous_linear_map.has_deriv_within_at
- \+ *lemma* continuous_linear_map.deriv
- \+ *lemma* continuous_linear_map.deriv_within
- \+ *lemma* linear_map.has_deriv_at_filter
- \+ *lemma* linear_map.has_strict_deriv_at
- \+ *lemma* linear_map.has_deriv_at
- \+ *lemma* linear_map.has_deriv_within_at
- \+ *lemma* linear_map.deriv
- \+ *lemma* linear_map.deriv_within
- \+ *lemma* has_strict_deriv_at_pow
- \+/\- *lemma* has_deriv_at_pow
- \+ *lemma* has_strict_deriv_at_fpow
- \+/\- *lemma* has_deriv_at_fpow
- \- *lemma* is_linear_map.has_deriv_at_filter
- \- *lemma* is_linear_map.has_deriv_within_at
- \- *lemma* is_linear_map.has_deriv_at
- \- *lemma* is_linear_map.differentiable_at
- \- *lemma* is_linear_map.differentiable_within_at
- \- *lemma* is_linear_map.deriv
- \- *lemma* is_linear_map.deriv_within
- \- *lemma* is_linear_map.differentiable
- \- *lemma* is_linear_map.differentiable_on
- \- *lemma* has_deriv_at_inv_one
- \+ *theorem* has_strict_deriv_at.has_deriv_at
- \+ *theorem* has_strict_deriv_at_id
- \+ *theorem* has_strict_deriv_at_const
- \+ *theorem* has_strict_deriv_at.add
- \+ *theorem* has_strict_deriv_at.smul
- \+ *theorem* has_strict_deriv_at.neg
- \+ *theorem* has_strict_deriv_at.sub
- \+ *theorem* has_strict_deriv_at.scomp
- \+ *theorem* has_strict_deriv_at.comp
- \+ *theorem* has_strict_deriv_at.mul
- \+ *theorem* has_strict_deriv_at_inv
- \+ *def* has_strict_deriv_at

Modified src/analysis/calculus/fderiv.lean
- \- *lemma* has_strict_fderiv_at.fst
- \- *lemma* has_fderiv_at_filter.fst
- \- *lemma* has_fderiv_at.fst
- \- *lemma* has_fderiv_within_at.fst
- \- *lemma* differentiable_at.fst
- \- *lemma* differentiable.fst
- \- *lemma* differentiable_within_at.fst
- \- *lemma* differentiable_on.fst
- \- *lemma* has_fderiv_at_filter.snd
- \- *lemma* has_fderiv_at.snd
- \- *lemma* has_fderiv_within_at.snd
- \- *lemma* differentiable_at.snd
- \- *lemma* differentiable.snd
- \- *lemma* differentiable_within_at.snd
- \- *lemma* differentiable_on.snd
- \+ *theorem* has_strict_fderiv_at.congr_of_mem_sets
- \- *theorem* has_strict_fderiv_at.prod_map
- \- *theorem* has_fderiv_at.prod_map
- \- *theorem* differentiable_at.prod_map

Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* linear_map.to_continuous_linear_map₁_coe
- \+ *lemma* linear_map.to_continuous_linear_map₁_apply
- \+ *def* linear_map.to_continuous_linear_map₁

Modified src/linear_algebra/basic.lean




## [2020-04-26 06:46:28](https://github.com/leanprover-community/mathlib/commit/21b7292)
feat(data/nat/basic): add `iterate_one` and `iterate_mul` ([#2540](https://github.com/leanprover-community/mathlib/pull/2540))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* iterate_mul
- \+ *theorem* iterate_one
- \+/\- *theorem* iterate₂
- \+/\- *theorem* iterate_cancel



## [2020-04-26 06:46:26](https://github.com/leanprover-community/mathlib/commit/21d8e0a)
chore(data/real/ennreal): +2 simple lemmas ([#2539](https://github.com/leanprover-community/mathlib/pull/2539))
Extracted from [#2311](https://github.com/leanprover-community/mathlib/pull/2311)
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* exists_nat_mul_gt



## [2020-04-26 06:46:24](https://github.com/leanprover-community/mathlib/commit/401d321)
feat(analysis/normed_space/basic): add continuous_at.div ([#2532](https://github.com/leanprover-community/mathlib/pull/2532))
When proving a particular function continuous at a particular point,
lemmas such as continuous_at.mul, continuous_at.add and
continuous_at.comp can be used to build this up from continuity
properties of simpler functions.  It's convenient to have something
similar for division as well.
This adds continuous_at.div for normed fields, as suggested by Yury.
If mathlib gets topological (semi)fields in future, this should become
a result for those.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean
- \+ *lemma* continuous_at.div



## [2020-04-26 06:46:22](https://github.com/leanprover-community/mathlib/commit/1182e91)
refactor(tactic/nth_rewrite): enable rewriting hypotheses, add docstrings ([#2471](https://github.com/leanprover-community/mathlib/pull/2471))
This PR
* renames the interactive tactic `perform_nth_rewrite` to `nth_rewrite`
* enables rewriting at hypotheses, instead of only the target
* renames the directory and namespace `rewrite_all` to `nth_rewrite`
* adds a bunch of docstrings
#### Estimated changes
Created src/meta/expr_lens.lean
- \+ *def* dir.to_string

Modified src/tactic/doc_commands.lean


Created src/tactic/nth_rewrite/basic.lean


Created src/tactic/nth_rewrite/congr.lean


Created src/tactic/nth_rewrite/default.lean


Deleted src/tactic/rewrite_all/congr.lean


Deleted src/tactic/rewrite_all/default.lean


Created test/expr_lens.lean


Renamed test/rewrite_all.lean to test/nth_rewrite.lean




## [2020-04-26 03:56:10](https://github.com/leanprover-community/mathlib/commit/c34add7)
chore(scripts): update nolints.txt ([#2537](https://github.com/leanprover-community/mathlib/pull/2537))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-26 03:56:08](https://github.com/leanprover-community/mathlib/commit/bda206a)
chore(data/option,order/bounded_lattice): 2 simple lemmas about `get_or_else` ([#2531](https://github.com/leanprover-community/mathlib/pull/2531))
I'm going to use these lemmas for `polynomial.nat_degree`. I don't want to PR
this change to `data/polynomial` because this would create merge conflicts later.
#### Estimated changes
Modified src/data/option/basic.lean
- \+ *lemma* get_or_else_of_ne_none

Modified src/order/bounded_lattice.lean
- \+/\- *lemma* bot_lt_some
- \+/\- *lemma* bot_lt_coe
- \+ *lemma* le_coe_get_or_else



## [2020-04-26 03:56:06](https://github.com/leanprover-community/mathlib/commit/ee6f20a)
chore(algebra/module): use bundled homs for `smul_sum` and `sum_smul` ([#2529](https://github.com/leanprover-community/mathlib/pull/2529))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* one_apply
- \+ *lemma* mul_apply
- \+ *lemma* flip_apply
- \+ *lemma* inv_apply
- \+ *def* flip

Modified src/algebra/module.lean
- \+ *lemma* smul_add_hom_apply
- \+ *def* smul_add_hom

Modified src/group_theory/group_action.lean
- \+ *lemma* const_smul_hom_apply
- \+ *def* const_smul_hom

Modified src/ring_theory/noetherian.lean




## [2020-04-25 23:03:27](https://github.com/leanprover-community/mathlib/commit/5219ca1)
doc(data/nat/modeq): add module docstring and lemma ([#2528](https://github.com/leanprover-community/mathlib/pull/2528))
I add a simple docstrong and also a lemma which I found useful for a codewars kata.
#### Estimated changes
Modified src/data/nat/modeq.lean
- \+ *theorem* modeq_iff_dvd'



## [2020-04-25 23:03:25](https://github.com/leanprover-community/mathlib/commit/ba4dc1a)
doc(algebra/order_functions): add docstring and lemma ([#2526](https://github.com/leanprover-community/mathlib/pull/2526))
I added a missing lemma, and then figured that while I was here I should add a docstring
#### Estimated changes
Modified src/algebra/order_functions.lean
- \+ *lemma* lt_abs



## [2020-04-25 19:55:53](https://github.com/leanprover-community/mathlib/commit/a8ae8e8)
feat(data/bool): add de Morgan's laws ([#2523](https://github.com/leanprover-community/mathlib/pull/2523))
I will go away with my tail between my legs if someone can show me that our esteemed mathematics library already contains de Morgan's laws for booleans. I also added a docstring. I can't lint the file because it's so high up in the import heirarchy, but I also added a docstring for the two instances.
#### Estimated changes
Modified src/data/bool.lean
- \+ *lemma* bnot_band
- \+ *lemma* bnot_bor
- \+ *lemma* bnot_inj



## [2020-04-25 19:55:51](https://github.com/leanprover-community/mathlib/commit/94fd41a)
refactor(data/padics/*): use [fact p.prime] to assume that p is prime ([#2519](https://github.com/leanprover-community/mathlib/pull/2519))
#### Estimated changes
Modified docs/theories/padics.md


Modified src/data/padics/hensel.lean
- \+/\- *lemma* padic_polynomial_dist

Modified src/data/padics/padic_integers.lean
- \+/\- *def* padic_int

Modified src/data/padics/padic_norm.lean
- \+/\- *lemma* padic_val_rat_def
- \+/\- *lemma* finite_int_prime_iff

Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* eq_of_norm_add_lt_right
- \+/\- *lemma* eq_of_norm_add_lt_left
- \+/\- *theorem* rat_dense'
- \+/\- *theorem* rat_dense
- \+/\- *def* padic_seq
- \+/\- *def* padic
- \+/\- *def* padic_norm_e

Modified src/data/real/irrational.lean




## [2020-04-25 18:43:05](https://github.com/leanprover-community/mathlib/commit/632c4ba)
feat(continued_fractions) add equivalence of convergents computations ([#2459](https://github.com/leanprover-community/mathlib/pull/2459))
### What
Add lemmas showing that the two methods for computing the convergents of a continued fraction (recurrence relation vs direct evaluation) coincide. A high-level overview on how the proof works is given in the header of the file. 
### Why
One wants to be able to relate both computations. The recurrence relation can be faster to compute, the direct evaluation is more intuitive and might be easier for some proofs.
### How
The proof of the equivalence is by induction. To make the induction work, one needs to "squash" a sequence into a shorter one while maintaining the value of the convergents computations. Most lemmas in this commit deal with this squashing operation.
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/continued_fractions/basic.lean
- \+/\- *def* next_numerator
- \+/\- *def* next_denominator
- \+/\- *def* next_continuants
- \+/\- *def* continuants_aux
- \+/\- *def* continuants
- \+/\- *def* numerators
- \+/\- *def* denominators
- \+/\- *def* convergents
- \+/\- *def* convergents'_aux
- \+/\- *def* convergents'

Modified src/algebra/continued_fractions/continuants_recurrence.lean
- \+/\- *lemma* continuants_aux_recurrence
- \+/\- *lemma* continuants_recurrence_aux
- \+/\- *lemma* numerators_recurrence
- \+/\- *lemma* denominators_recurrence
- \+/\- *theorem* continuants_recurrence

Created src/algebra/continued_fractions/convergents_equiv.lean
- \+ *lemma* squash_seq_eq_self_of_terminated
- \+ *lemma* squash_seq_nth_of_not_terminated
- \+ *lemma* squash_seq_nth_of_lt
- \+ *lemma* squash_seq_succ_n_tail_eq_squash_seq_tail_n
- \+ *lemma* succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq
- \+ *lemma* squash_gcf_eq_self_of_terminated
- \+ *lemma* squash_gcf_nth_of_lt
- \+ *lemma* succ_nth_convergent'_eq_squash_gcf_nth_convergent'
- \+ *lemma* continuants_aux_eq_continuants_aux_squash_gcf_of_le
- \+ *lemma* succ_nth_convergent_eq_squash_gcf_nth_convergent
- \+ *theorem* convergents_eq_convergents'
- \+ *def* squash_seq
- \+ *def* squash_gcf

Modified src/algebra/continued_fractions/default.lean


Modified src/algebra/continued_fractions/terminated_stable.lean
- \+/\- *lemma* convergents'_aux_stable_step_of_terminated
- \+/\- *lemma* convergents'_aux_stable_of_terminated

Modified src/algebra/continued_fractions/translations.lean
- \+/\- *lemma* obtain_conts_a_of_num
- \+/\- *lemma* obtain_conts_b_of_denom
- \+/\- *lemma* zeroth_convergent'_aux_eq_zero



## [2020-04-25 09:58:14](https://github.com/leanprover-community/mathlib/commit/d9327e4)
refactor(geometry/manifold/real_instances): use fact instead of lt_class ([#2521](https://github.com/leanprover-community/mathlib/pull/2521))
To define a manifold with boundary structure on the interval `[x, y]`, typeclass inference needs to know that `x < y`. This used to be provided by the introduction of a dummy class `lt_class`. The new mechanism based on `fact` makes it possible to remove this dummy class.
#### Estimated changes
Modified src/geometry/manifold/real_instances.lean
- \+/\- *def* Icc_left_chart
- \+/\- *def* Icc_right_chart
- \- *def* lt_class



## [2020-04-25 09:58:12](https://github.com/leanprover-community/mathlib/commit/2b95532)
refactor(*): use [fact p.prime] for frobenius and perfect_closure ([#2518](https://github.com/leanprover-community/mathlib/pull/2518))
This also removes the dependency of `algebra.char_p` on `data.padics.padic_norm`, which was only there to make `nat.prime` a class.
I also used this opportunity to rename all alphas and betas to `K` and `L` in the perfect closure file.
#### Estimated changes
Modified src/algebra/char_p.lean
- \+/\- *theorem* monoid_hom.iterate_map_frobenius
- \+/\- *theorem* ring_hom.iterate_map_frobenius
- \+/\- *theorem* frobenius_inj

Modified src/field_theory/perfect_closure.lean
- \+/\- *lemma* coe_frobenius_equiv
- \+/\- *lemma* quot_mk_eq_mk
- \+/\- *lemma* lift_on_mk
- \+/\- *lemma* induction_on
- \+/\- *lemma* mk_mul_mk
- \+/\- *lemma* one_def
- \+/\- *lemma* mk_add_mk
- \+/\- *lemma* neg_mk
- \+/\- *lemma* zero_def
- \+/\- *lemma* of_apply
- \+/\- *theorem* frobenius_pth_root
- \+/\- *theorem* pth_root_frobenius
- \+/\- *theorem* eq_pth_root_iff
- \+/\- *theorem* pth_root_eq_iff
- \+/\- *theorem* monoid_hom.map_pth_root
- \+/\- *theorem* monoid_hom.map_iterate_pth_root
- \+/\- *theorem* ring_hom.map_pth_root
- \+/\- *theorem* ring_hom.map_iterate_pth_root
- \+/\- *theorem* mk_zero
- \+/\- *theorem* r.sound
- \+/\- *theorem* eq_iff'
- \+/\- *theorem* nat_cast
- \+/\- *theorem* int_cast
- \+/\- *theorem* nat_cast_eq_iff
- \+/\- *theorem* frobenius_mk
- \+/\- *theorem* eq_iff
- \+/\- *theorem* eq_pth_root
- \+/\- *def* frobenius_equiv
- \+/\- *def* pth_root
- \+/\- *def* perfect_closure
- \+/\- *def* mk
- \+/\- *def* lift_on
- \+/\- *def* of
- \+/\- *def* lift



## [2020-04-25 08:51:08](https://github.com/leanprover-community/mathlib/commit/f192f2f)
chore(*): move quadratic_reciprocity to number_theory/ ([#2520](https://github.com/leanprover-community/mathlib/pull/2520))
I've never really understood why we put all these cool theorems under the data/ directory, so I suggest moving them out of there, and into the place where thy "belong".
#### Estimated changes
Modified src/data/zsqrtd/gaussian_int.lean


Renamed src/data/zmod/quadratic_reciprocity.lean to src/number_theory/quadratic_reciprocity.lean




## [2020-04-25 05:42:30](https://github.com/leanprover-community/mathlib/commit/3c8584d)
feat(order/filter/bases): add `exists_iff` and `forall_iff` ([#2507](https://github.com/leanprover-community/mathlib/pull/2507))
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* has_basis.exists_iff
- \+ *lemma* has_basis.forall_iff



## [2020-04-25 05:42:28](https://github.com/leanprover-community/mathlib/commit/199f6fe)
refactor(tactic/suggest): call library_search and suggest with additional lemmas, better lemma caching ([#2429](https://github.com/leanprover-community/mathlib/pull/2429))
This PR is mainly a refactoring of suggest. The changes include:
* Removed `(discharger : tactic unit := done)` from `library_search`, `suggest`, `suggest_scripts` `suggest_core`, `suggest_core'`, `apply_declaration` and `apply_and_solve` and replaced by `(opt : by_elim_opt := { })` from `solve_by_elim`.
* Replaced all occurences of `discharger` by `opt`, `opt.discharger`, or `..opt`.
* inserted a do block into the interactive `library_search` function.
* Added `asms ← mk_assumption_set no_dflt hs attr_names`, to the interactive `suggest` and `library_search` functions. This is so `library_search` and `suggest` don't rebuild the assumption set each time a lemma is applied.
* Added several inputs for the interactive `library_search` and `suggest` function. These parameters were lifted from the interactive `solve_by_elim` function and allow the user to control how `solve_by_elim` is utilized by `library_search` and `suggest`.
* Removed the `message` function (redundant code.)
* Removed several unnecessary `g ← instantiate_mvars g`, lines.
#### Estimated changes
Modified src/tactic/solve_by_elim.lean


Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean
- \+ *def* map_from_sum



## [2020-04-25 04:11:06](https://github.com/leanprover-community/mathlib/commit/06f8c55)
chore(scripts): update nolints.txt ([#2517](https://github.com/leanprover-community/mathlib/pull/2517))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-25 02:22:56](https://github.com/leanprover-community/mathlib/commit/22d89c4)
chore(scripts): update nolints.txt ([#2515](https://github.com/leanprover-community/mathlib/pull/2515))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-24 23:37:04](https://github.com/leanprover-community/mathlib/commit/e918f72)
refactor(zmod): merge `zmodp` into `zmod`, use `[fact p.prime]` for tc search ([#2511](https://github.com/leanprover-community/mathlib/pull/2511))
This PR introduces the class `fact P := P` for `P : Prop`, which is a way to inject elementary propositions into the type class system. This desing is inspired by @cipher1024 's https://gist.github.com/cipher1024/9bd785a75384a4870b331714ec86ad6f#file-zmod_redesign-lean.
We use this to endow `zmod p` with a `field` instance under the assumption `[fact p.prime]`.
As a consequence, the type `zmodp` is no longer needed, which removes a lot of duplicate code.
Besides that, we redefine `zmod n`, so that `n` is a natural number instead of a *positive* natural number, and `zmod 0` is now definitionally the integers.
To preserve computational properties, `zmod n` is not defined as quotient type, but rather as `int` and `fin n`, depending on whether `n` is `0` or `(k+1)`.
The rest of this PR is adapting the library to the new definitions (most notably quadratic reciprocity and Lagrange's four squares theorem).
Future work: Refactor the padics to use `[fact p.prime]` instead of making `nat.prime` a class in those files. This will address [#1601](https://github.com/leanprover-community/mathlib/pull/1601) and [#1648](https://github.com/leanprover-community/mathlib/pull/1648). Once that is done, we can clean up the mess in `char_p` (where the imports are really tangled) and finally get some movement in [#1564](https://github.com/leanprover-community/mathlib/pull/1564).
#### Estimated changes
Modified src/algebra/char_p.lean
- \+ *lemma* char_p.int_cast_eq_zero_iff
- \+ *lemma* char_is_prime_of_pos
- \+ *lemma* false_of_nonzero_of_char_one
- \+/\- *theorem* char_is_prime
- \- *def* cast_hom

Modified src/data/nat/basic.lean
- \+ *lemma* dvd_sub_mod

Modified src/data/nat/modeq.lean
- \+ *lemma* add_mod
- \+ *lemma* mul_mod

Modified src/data/nat/prime.lean


Modified src/data/nat/totient.lean
- \- *lemma* card_units_eq_totient

Modified src/data/zmod/basic.lean
- \+ *lemma* val_add
- \+ *lemma* val_mul
- \+/\- *lemma* one_val
- \+/\- *lemma* zero_val
- \+ *lemma* of_nat_eq_coe
- \+ *lemma* card
- \+ *lemma* val_lt
- \+ *lemma* val_zero
- \+/\- *lemma* val_cast_nat
- \+ *lemma* cast_self
- \+ *lemma* cast_self'
- \+ *lemma* cast_zero
- \+ *lemma* nat_cast_surjective
- \+ *lemma* int_cast_surjective
- \+/\- *lemma* cast_val
- \+ *lemma* cast_id
- \+ *lemma* nat_cast_val
- \+ *lemma* cast_one
- \+ *lemma* cast_add
- \+ *lemma* cast_mul
- \+ *lemma* cast_hom_apply
- \+ *lemma* cast_nat_cast
- \+ *lemma* cast_int_cast
- \+ *lemma* val_injective
- \+ *lemma* val_one_eq_one_mod
- \+ *lemma* val_one
- \+ *lemma* inv_zero
- \+/\- *lemma* mul_inv_eq_gcd
- \+/\- *lemma* cast_mod_nat
- \+/\- *lemma* eq_iff_modeq_nat
- \+ *lemma* coe_mul_inv_eq_one
- \+/\- *lemma* cast_unit_of_coprime
- \+ *lemma* val_coe_unit_coprime
- \+ *lemma* inv_coe_unit
- \+ *lemma* mul_inv_of_unit
- \+ *lemma* inv_mul_of_unit
- \+ *lemma* card_units_eq_totient
- \+/\- *lemma* le_div_two_iff_lt_neg
- \+/\- *lemma* ne_neg_self
- \+ *lemma* neg_one_ne_one
- \+/\- *lemma* neg_eq_self_mod_two
- \+/\- *lemma* nat_abs_mod_two
- \+ *lemma* val_eq_zero
- \+/\- *lemma* val_cast_of_lt
- \+/\- *lemma* neg_val'
- \+/\- *lemma* neg_val
- \+ *lemma* val_min_abs_def_zero
- \+ *lemma* val_min_abs_def_pos
- \+/\- *lemma* coe_val_min_abs
- \+/\- *lemma* nat_abs_val_min_abs_le
- \+/\- *lemma* val_min_abs_zero
- \+/\- *lemma* val_min_abs_eq_zero
- \+/\- *lemma* cast_nat_abs_val_min_abs
- \+/\- *lemma* nat_abs_val_min_abs_neg
- \+/\- *lemma* val_eq_ite_val_min_abs
- \+/\- *lemma* prime_ne_zero
- \- *lemma* add_val
- \- *lemma* mul_val
- \- *lemma* mk_eq_cast
- \- *lemma* cast_self_eq_zero
- \- *lemma* cast_mod_nat'
- \- *lemma* cast_mod_int
- \- *lemma* cast_mod_int'
- \- *lemma* val_cast_int
- \- *lemma* coe_val_cast_int
- \- *lemma* eq_iff_modeq_nat'
- \- *lemma* eq_iff_modeq_int
- \- *lemma* eq_iff_modeq_int'
- \- *lemma* eq_zero_iff_dvd_nat
- \- *lemma* eq_zero_iff_dvd_int
- \- *lemma* card_zmod
- \- *lemma* cast_mul_right_val_cast
- \- *lemma* cast_mul_left_val_cast
- \- *lemma* cast_val_cast_of_dvd
- \- *lemma* cast_self_eq_zero:
- \- *lemma* card_zmodp
- \+ *def* has_neg
- \+ *def* add_comm_semigroup
- \+ *def* comm_semigroup
- \+ *def* comm_ring
- \+/\- *def* zmod
- \+ *def* val
- \+/\- *def* cast
- \+ *def* cast_hom
- \+ *def* inv
- \+/\- *def* unit_of_coprime
- \+/\- *def* units_equiv_coprime
- \+/\- *def* val_min_abs
- \- *def* zmodp

Modified src/data/zmod/quadratic_reciprocity.lean
- \+ *lemma* card_units
- \+/\- *lemma* euler_criterion_units
- \+/\- *lemma* euler_criterion
- \+/\- *lemma* pow_div_two_eq_neg_one_or_one
- \+/\- *lemma* wilsons_lemma
- \+/\- *lemma* prod_Ico_one_prime
- \+/\- *lemma* legendre_sym_eq_pow
- \+/\- *lemma* legendre_sym_eq_one_or_neg_one
- \+ *lemma* legendre_sym_eq_zero_iff
- \+/\- *lemma* gauss_lemma
- \+/\- *lemma* legendre_sym_eq_one_iff
- \+/\- *lemma* eisenstein_lemma
- \+/\- *lemma* legendre_sym_two
- \+/\- *lemma* exists_pow_two_eq_two_iff
- \+/\- *lemma* exists_pow_two_eq_prime_iff_of_mod_four_eq_one
- \- *lemma* card_units_zmodp
- \+ *theorem* fermat_little_units
- \+/\- *theorem* fermat_little
- \+/\- *theorem* quadratic_reciprocity
- \+/\- *def* legendre_sym

Modified src/data/zsqrtd/gaussian_int.lean
- \+/\- *lemma* mod_four_eq_three_of_nat_prime_of_prime
- \+/\- *lemma* sum_two_squares_of_nat_prime_of_not_irreducible
- \+/\- *lemma* prime_of_nat_prime_of_mod_four_eq_three
- \+/\- *lemma* prime_iff_mod_four_eq_three_of_nat_prime

Modified src/field_theory/finite.lean
- \+/\- *lemma* sum_two_squares
- \+/\- *lemma* zmod.pow_totient

Modified src/field_theory/finite_card.lean
- \+/\- *theorem* card
- \+/\- *theorem* card'

Modified src/group_theory/order_of_element.lean


Modified src/group_theory/sylow.lean
- \+/\- *lemma* one_mem_fixed_points_rotate
- \+/\- *lemma* exists_prime_order_of_dvd_card
- \+/\- *lemma* exists_subgroup_card_pow_prime
- \+/\- *def* rotate_vectors_prod_eq_one

Modified src/logic/basic.lean
- \+ *def* fact

Modified src/number_theory/sum_four_squares.lean
- \+/\- *lemma* exists_sum_two_squares_add_one_eq_k

Modified src/number_theory/sum_two_squares.lean
- \+/\- *lemma* sum_two_squares



## [2020-04-24 23:37:01](https://github.com/leanprover-community/mathlib/commit/3e54e97)
chore(topology/separation): prove that `{y | y ≠ x}` is open ([#2506](https://github.com/leanprover-community/mathlib/pull/2506))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/data/set/basic.lean
- \+ *lemma* compl_singleton_eq

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* is_open_ne_top

Modified src/topology/separation.lean
- \+ *lemma* is_open_ne



## [2020-04-24 21:12:05](https://github.com/leanprover-community/mathlib/commit/ee8451b)
feat(data/list): more lemmas on joins and sums ([#2501](https://github.com/leanprover-community/mathlib/pull/2501))
A few more lemmas on lists (especially joins) and sums. I also linted the file `lists/basic.lean` and converted some comments to section headers.
Some lemmas got renamed:
`of_fn_prod_take` -> `prod_take_of_fn`
`of_fn_sum_take` -> `sum_take_of_fn`
`of_fn_prod` ->`prod_of_fn`
`of_fn_sum` -> `sum_of_fn`
The arguments of `nth_le_repeat` were changed for better `simp` efficiency
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* sum_range_sub_of_monotone

Modified src/analysis/analytic/composition.lean


Modified src/combinatorics/composition.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_sigma_univ

Modified src/data/fintype/card.lean
- \+ *lemma* fin.prod_univ_eq_prod_range
- \+ *lemma* prod_equiv
- \+ *lemma* prod_take_of_fn
- \+ *lemma* sum_take_of_fn
- \+ *lemma* prod_of_fn
- \- *lemma* of_fn_prod_take
- \- *lemma* of_fn_sum_take
- \- *lemma* of_fn_prod

Modified src/data/list/basic.lean
- \+ *lemma* forall_mem_map_iff
- \+ *lemma* nth_le_of_eq
- \+/\- *lemma* nth_le_repeat
- \+ *lemma* eq_cons_of_length_one
- \+/\- *lemma* take_append_of_le_length
- \+ *lemma* take_append
- \+ *lemma* nth_le_take
- \+ *lemma* nth_le_take'
- \+ *lemma* drop_append
- \+ *lemma* nth_le_drop
- \+ *lemma* nth_le_drop'
- \+/\- *lemma* join_join
- \+ *lemma* take_sum_join
- \+ *lemma* drop_sum_join
- \+ *lemma* drop_take_succ_eq_cons_nth_le
- \+ *lemma* drop_take_succ_join_eq_nth_le
- \+ *lemma* sum_take_map_length_lt1
- \+ *lemma* sum_take_map_length_lt2
- \+ *lemma* nth_le_join
- \+ *theorem* take_repeat
- \+/\- *theorem* join_eq_nil
- \+/\- *theorem* join_append
- \+ *theorem* eq_iff_join_eq

Modified src/data/list/of_fn.lean
- \+ *lemma* mem_of_fn
- \+ *lemma* forall_mem_of_fn_iff

Modified src/data/nat/modeq.lean




## [2020-04-24 20:10:09](https://github.com/leanprover-community/mathlib/commit/6795c9d)
chore(scripts): update nolints.txt ([#2514](https://github.com/leanprover-community/mathlib/pull/2514))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-24 17:09:09](https://github.com/leanprover-community/mathlib/commit/3162c1c)
feat(tactic/delta_instance): protect names and deal with functions ([#2477](https://github.com/leanprover-community/mathlib/pull/2477))
There were (at least) two issues with the `delta_instance` derive handler:
* It couldn't protect the names of the instances it generated, so they had to be ugly to avoid clashes.
* It didn't deal well with deriving instances on function types, so `@[derive monad]` usually failed.
This should fix both. The first is possible with recent(ish) additions to core.
closes [#1951](https://github.com/leanprover-community/mathlib/pull/1951)
#### Estimated changes
Modified src/category_theory/limits/shapes/wide_pullbacks.lean


Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified src/tactic/linarith.lean


Modified src/tactic/ring.lean


Modified src/tactic/ring_exp.lean


Modified test/delta_instance.lean




## [2020-04-24 14:15:51](https://github.com/leanprover-community/mathlib/commit/2f6b8d7)
chore(scripts): update nolints.txt ([#2510](https://github.com/leanprover-community/mathlib/pull/2510))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-24 14:15:48](https://github.com/leanprover-community/mathlib/commit/7a71866)
chore(topology/algebra/module): make `id` use explicit args ([#2509](https://github.com/leanprover-community/mathlib/pull/2509))
#### Estimated changes
Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* fderiv_id
- \- *lemma* has_strict_fderiv_at.snd
- \+/\- *theorem* has_fderiv_at_id

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* norm_id_le
- \+/\- *lemma* norm_id

Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/mfderiv.lean
- \+/\- *lemma* mfderiv_id

Modified src/topology/algebra/module.lean
- \+/\- *lemma* id_apply
- \+/\- *lemma* coe_id
- \+/\- *lemma* coe_id'
- \+/\- *theorem* comp_id
- \+/\- *theorem* id_comp



## [2020-04-24 14:15:46](https://github.com/leanprover-community/mathlib/commit/62feebc)
chore(*): add missing copyright headers ([#2505](https://github.com/leanprover-community/mathlib/pull/2505))
I think these are close to the last remaining files without copyright headers.
(We decided at some point to allow that `import`-only files don't need one.)
#### Estimated changes
Modified src/data/string/defs.lean


Modified src/deprecated/group.lean


Modified src/tactic/transform_decl.lean


Modified src/topology/algebra/open_subgroup.lean




## [2020-04-24 14:15:44](https://github.com/leanprover-community/mathlib/commit/c8946c9)
chore(tactic/*): remove some unused args in commands ([#2498](https://github.com/leanprover-community/mathlib/pull/2498))
#### Estimated changes
Modified src/tactic/localized.lean


Modified src/tactic/replacer.lean


Modified src/tactic/restate_axiom.lean




## [2020-04-24 11:14:03](https://github.com/leanprover-community/mathlib/commit/00d7da2)
docs(*): merge rewrite tactic tag into rewriting ([#2512](https://github.com/leanprover-community/mathlib/pull/2512))
We had two overlapping tags in the docs.
#### Estimated changes
Modified src/tactic/converter/apply_congr.lean


Modified src/tactic/elide.lean


Modified src/tactic/ext.lean


Modified src/tactic/interactive.lean


Modified src/tactic/lean_core_docs.lean


Modified src/tactic/rewrite.lean




## [2020-04-24 11:14:01](https://github.com/leanprover-community/mathlib/commit/13393e3)
chore(data/list/*): various renamings to use dot notation ([#2481](https://github.com/leanprover-community/mathlib/pull/2481))
* use dot notation
* add a version of `list.perm.prod_eq` that only assumes that elements of the list pairwise commute instead of commutativity of the monoid.
## List of renamed symbols
### `data/list/basic`
* `append_sublist_append_of_sublist_right` : `sublist.append_right`;
* `reverse_sublist` : `sublist.reverse`;
* `append_sublist_append` : `sublist.append`;
* `subset_of_sublist`: `sublist.subset`;
* `sublist_antisymm` : `sublist.antisymm`;
* `filter_map_sublist_filter_map` : `sublist.filter_map`
* `map_sublist_map` : `sublist.map`
* `erasep_sublist_erasep`: `sublist.erasep`
* `erase_sublist_erase` : `sublist.erase`;
* `diff_sublist_of_sublist` : `sublist.diff_right`;
### `data/list/perm`
* `perm.skip` : `perm.cons`;
* `perm_comm` (new);
* `perm_subset` : `perm.subset`;
* `mem_of_perm` : `perm.mem_iff`;
* `perm_app_left` : `perm.append_right` (note `right` vs `left`)
* `perm_app_right` : `perm.append_left` (note `right` vs `left`)
* `perm_app` : `perm.append`;
* `perm_app_cons` : `perm.append_cons`;
* `perm_cons_app` : `perm_append_singleton`;
* `perm_app_comm` : `perm_append_comm`;
* `perm_length` : `perm.length_eq`;
* `eq_nil_of_perm_nil` : `perm.eq_nil` and `perm.nil_eq`
  with different choices of lhs/rhs;
* `eq_singleton_of_perm_inv` : `perm.eq_singleton` and `perm.singleton_eq`
  with different choices of lhs/rhs;
* `perm_singleton` and `singleton_perm`: `iff` versions
  of `perm.eq_singleton` and `perm.singleton_eq`;
* `eq_singleton_of_perm` : `singleton_perm_singleton`;
* `perm_cons_app_cons` : `perm_cons_append_cons`;
* `perm_repeat` : `repeat_perm`; new `perm_repeat` differs from it
  in the choice of lhs/rhs;
* `perm_erase` : `perm_cons_erase`;
* `perm_filter_map` : `perm.filter_map`;
* `perm_map` : `perm.map`;
* `perm_pmap` : `perm.pmap`;
* `perm_filter` : `perm.filter`;
* `subperm_of_sublist` : `sublist.subperm`;
* `subperm_of_perm` : `perm.subperm`;
* `subperm.refl` : now has `@[refl]` attribute;
* `subperm.trans` : now has `@[trans]` attribute;
* `length_le_of_subperm` : `subperm.length_le`;
* `subset_of_subperm` : `subperm.subset`;
* `exists_perm_append_of_sublist` : `sublist.exists_perm_append`;
* `perm_countp` : `perm.countp_eq`;
* `countp_le_of_subperm` : `subperm.countp_le`;
* `perm_count` : `perm.count_eq`;
* `count_le_of_subperm` : `subperm.count_le`;
* `foldl_eq_of_perm` : `perm.foldl_eq`, added a primed version
  with slightly weaker assumptions;
* `foldr_eq_of_perm` : `perm.foldr_eq`;
* `rec_heq_of_perm` : `perm.eec_heq`;
* `fold_op_eq_of_perm` : `perm.fold_op_eq`;
* `prod_eq_of_perm`: `perm.prod_eq` and `perm.prod_eq'`;
* `perm_cons_inv` : `perm.cons_inv`;
* `perm_cons` : now is a `@[simp]` lemma;
* `perm_app_right_iff` : `perm_append_right_iff`;
* `subperm_app_left` : `subperm_append_left`;
* `subperm_app_right` : `subperm_append_right`;
* `perm_ext_sublist_nodup` : `nodup.sublist_ext`;
* `erase_perm_erase` : `perm.erase`;
* `subperm_cons_erase` (new);
* `erase_subperm_erase` : `subperm.erase`;
* `perm_diff_left` : `perm.diff_right` (note `left` vs `right`);
* `perm_diff_right` : `perm.diff_left` (note `left` vs `right`);
* `perm.diff`, `subperm.diff_right`, `erase_cons_subperm_cons_erase` (new);
* `perm_bag_inter_left` : `perm.bag_inter_right` (note `left` vs `right`);
* `perm_bag_inter_right` : `perm.bag_inter_left` (note `left` vs `right`);
* `perm.bag_inter` (new);
* `perm_erase_dup_of_perm` : `perm.erase_dup`;
* `perm_union_left` : `perm.union_right` (note `left` vs `right`);
* `perm_union_right` : `perm.union_left` (note `left` vs `right`);
* `perm_union` : `perm.union`;
* `perm_inter_left` : `perm.inter_right` (note `left` vs `right`);
* `perm_inter_right` : `perm.inter_left` (note `left` vs `right`);
* `perm_inter` : `perm.inter`;
* `perm_nodup` : `perm.nodup_iff`;
* `perm_bind_left` : `perm.bind_right` (note `left` vs `right`);
* `perm_bind_right` : `perm.bind_left` (note `left` vs `right`);
* `perm_product_left` : `perm.product_right` (note `left` vs `right`);
* `perm_product_right` : `peerm.product_left` (note `left` vs `right`);
* `perm_product` : `perm.product`;
* `perm_erasep` : `perm.erasep`;
### `data/list/sigma`
* `nodupkeys.pairwise_ne` (new);
* `perm_kreplace` : `perm.kreplace`;
* `perm_kerase` : `perm.kerase`;
* `perm_kinsert` : `perm.kinsert`;
* `erase_dupkeys_cons` : now take `x : sigma β` instead
  of `{x : α}` and `{y : β x}`;
* `perm_kunion_left` : `perm.kunion_right` (note `left` vs `right`);
* `perm_kunion_right` : `perm.kunion_left` (note `left` vs `right`);
* `perm_kunion` : `perm.kunion`;
*
#### Estimated changes
Modified src/data/fintype/basic.lean


Modified src/data/list/alist.lean
- \+/\- *lemma* insert_singleton_eq
- \+/\- *theorem* insert_insert
- \+/\- *theorem* entries_to_alist
- \+/\- *theorem* to_alist_cons
- \+/\- *theorem* union_comm_of_disjoint

Modified src/data/list/basic.lean
- \+ *theorem* sublist.append_right
- \+ *theorem* sublist.reverse
- \+ *theorem* sublist.append
- \+ *theorem* sublist.subset
- \+ *theorem* sublist.antisymm
- \+ *theorem* sublist.filter_map
- \+ *theorem* sublist.map
- \+/\- *theorem* span_eq_take_drop
- \+/\- *theorem* take_while_append_drop
- \+ *theorem* sublist.erasep
- \+ *theorem* sublist.erase
- \+ *theorem* sublist.diff_right
- \- *theorem* append_sublist_append_of_sublist_right
- \- *theorem* reverse_sublist
- \- *theorem* append_sublist_append
- \- *theorem* subset_of_sublist
- \- *theorem* sublist_antisymm
- \- *theorem* filter_map_sublist_filter_map
- \- *theorem* map_sublist_map
- \- *theorem* erasep_sublist_erasep
- \- *theorem* erase_sublist_erase
- \- *theorem* diff_sublist_of_sublist

Modified src/data/list/pairwise.lean


Modified src/data/list/perm.lean
- \+ *lemma* perm.rec_heq
- \+ *lemma* perm.fold_op_eq
- \+ *lemma* perm.prod_eq'
- \+ *lemma* perm.prod_eq
- \- *lemma* rec_heq_of_perm
- \- *lemma* fold_op_eq_of_perm
- \- *lemma* prod_eq_of_perm
- \+ *theorem* perm_comm
- \+ *theorem* perm.subset
- \+ *theorem* perm.mem_iff
- \+ *theorem* perm.append_right
- \+ *theorem* perm.append_left
- \+ *theorem* perm.append
- \+ *theorem* perm.append_cons
- \+ *theorem* perm_append_singleton
- \+ *theorem* perm_append_comm
- \+ *theorem* perm.length_eq
- \+ *theorem* perm.eq_nil
- \+ *theorem* perm.nil_eq
- \+ *theorem* perm_cons_append_cons
- \+/\- *theorem* perm_repeat
- \+ *theorem* repeat_perm
- \+ *theorem* perm_singleton
- \+ *theorem* singleton_perm
- \+ *theorem* perm.eq_singleton
- \+ *theorem* perm.singleton_eq
- \+ *theorem* singleton_perm_singleton
- \+ *theorem* perm_cons_erase
- \+ *theorem* perm.filter_map
- \+ *theorem* perm.map
- \+ *theorem* perm.pmap
- \+ *theorem* perm.filter
- \+ *theorem* sublist.subperm
- \+ *theorem* perm.subperm
- \+/\- *theorem* subperm.refl
- \+/\- *theorem* subperm.trans
- \+ *theorem* subperm.length_le
- \+ *theorem* subperm.subset
- \+ *theorem* sublist.exists_perm_append
- \+ *theorem* perm.countp_eq
- \+ *theorem* subperm.countp_le
- \+ *theorem* perm.count_eq
- \+ *theorem* subperm.count_le
- \+ *theorem* perm.foldl_eq'
- \+ *theorem* perm.foldl_eq
- \+ *theorem* perm.foldr_eq
- \+ *theorem* perm.cons_inv
- \+/\- *theorem* perm_cons
- \+ *theorem* perm_append_left_iff
- \+ *theorem* perm_append_right_iff
- \+ *theorem* subperm_append_left
- \+ *theorem* subperm_append_right
- \+/\- *theorem* perm_ext
- \+ *theorem* nodup.sublist_ext
- \+ *theorem* perm.erase
- \+ *theorem* subperm_cons_erase
- \+ *theorem* subperm.erase
- \+ *theorem* perm.diff_right
- \+ *theorem* perm.diff_left
- \+ *theorem* perm.diff
- \+ *theorem* subperm.diff_right
- \+ *theorem* erase_cons_subperm_cons_erase
- \+ *theorem* perm.bag_inter_right
- \+ *theorem* perm.bag_inter_left
- \+ *theorem* perm.bag_inter
- \+ *theorem* perm.erase_dup
- \+ *theorem* perm.insert
- \+ *theorem* perm.union_right
- \+ *theorem* perm.union_left
- \+ *theorem* perm.union
- \+ *theorem* perm.inter_right
- \+ *theorem* perm.inter_left
- \+ *theorem* perm.inter
- \+ *theorem* perm.pairwise_iff
- \+ *theorem* perm.nodup_iff
- \+ *theorem* perm.bind_right
- \+ *theorem* perm.bind_left
- \+ *theorem* perm.product_right
- \+ *theorem* perm.product_left
- \+ *theorem* perm.product
- \+ *theorem* perm.erasep
- \- *theorem* perm_subset
- \- *theorem* mem_of_perm
- \- *theorem* perm_app_left
- \- *theorem* perm_app_right
- \- *theorem* perm_app
- \- *theorem* perm_app_cons
- \- *theorem* perm_cons_app
- \- *theorem* perm_app_comm
- \- *theorem* perm_length
- \- *theorem* eq_nil_of_perm_nil
- \- *theorem* eq_singleton_of_perm
- \- *theorem* eq_singleton_of_perm_inv
- \- *theorem* perm_cons_app_cons
- \- *theorem* perm_erase
- \- *theorem* perm_filter_map
- \- *theorem* perm_map
- \- *theorem* perm_pmap
- \- *theorem* perm_filter
- \- *theorem* subperm_of_sublist
- \- *theorem* subperm_of_perm
- \- *theorem* length_le_of_subperm
- \- *theorem* subset_of_subperm
- \- *theorem* exists_perm_append_of_sublist
- \- *theorem* perm_countp
- \- *theorem* countp_le_of_subperm
- \- *theorem* perm_count
- \- *theorem* count_le_of_subperm
- \- *theorem* foldl_eq_of_perm
- \- *theorem* foldr_eq_of_perm
- \- *theorem* perm_cons_inv
- \- *theorem* perm_app_left_iff
- \- *theorem* perm_app_right_iff
- \- *theorem* subperm_app_left
- \- *theorem* subperm_app_right
- \- *theorem* perm_ext_sublist_nodup
- \- *theorem* erase_perm_erase
- \- *theorem* erase_subperm_erase
- \- *theorem* perm_diff_left
- \- *theorem* perm_diff_right
- \- *theorem* perm_bag_inter_left
- \- *theorem* perm_bag_inter_right
- \- *theorem* perm_erase_dup_of_perm
- \- *theorem* perm_insert
- \- *theorem* perm_union_left
- \- *theorem* perm_union_right
- \- *theorem* perm_union
- \- *theorem* perm_inter_left
- \- *theorem* perm_inter_right
- \- *theorem* perm_inter
- \- *theorem* perm_pairwise
- \- *theorem* perm_nodup
- \- *theorem* perm_bind_left
- \- *theorem* perm_bind_right
- \- *theorem* perm_product_left
- \- *theorem* perm_product_right
- \- *theorem* perm_product
- \- *theorem* perm_erasep

Modified src/data/list/range.lean


Modified src/data/list/sigma.lean
- \+/\- *lemma* erase_dupkeys_cons
- \+ *theorem* nodupkeys.pairwise_ne
- \+/\- *theorem* nodupkeys_of_sublist
- \+ *theorem* perm.kreplace
- \+/\- *theorem* kerase_kerase
- \+ *theorem* perm.kerase
- \+ *theorem* perm.kinsert
- \+ *theorem* perm.kunion_right
- \+ *theorem* perm.kunion_left
- \+ *theorem* perm.kunion
- \- *theorem* perm_kreplace
- \- *theorem* perm_kerase
- \- *theorem* perm_kinsert
- \- *theorem* perm_kunion_left
- \- *theorem* perm_kunion_right
- \- *theorem* perm_kunion

Modified src/data/list/sort.lean


Modified src/data/multiset.lean
- \+/\- *theorem* erase_add_right_pos
- \+/\- *theorem* erase_add_right_neg
- \+/\- *theorem* erase_add_left_neg
- \+/\- *theorem* card_erase_of_mem
- \+/\- *theorem* coe_filter_map
- \+/\- *theorem* cons_ndunion

Modified src/data/nat/prime.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean




## [2020-04-24 11:13:59](https://github.com/leanprover-community/mathlib/commit/3ae22de)
feat(linear_algebra): quadratic forms ([#2480](https://github.com/leanprover-community/mathlib/pull/2480))
Define quadratic forms over a module, maps from quadratic forms to bilinear forms and matrices, positive definite quadratic forms and the discriminant of quadratic forms.
Along the way, I added some definitions to `data/matrix/basic.lean` and `linear_algebra/bilinear_form.lean` and did some cleaning up.
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* coe_fn_congr

Modified src/data/matrix/basic.lean
- \+ *lemma* vec_mul_diagonal
- \+ *lemma* vec_mul_one
- \+ *lemma* mul_vec_zero
- \+ *lemma* vec_mul_zero
- \+ *lemma* vec_mul_vec_mul
- \+ *lemma* mul_vec_mul_vec
- \+ *lemma* col_add
- \+ *lemma* col_smul
- \+ *lemma* row_add
- \+ *lemma* row_smul
- \+ *lemma* col_val
- \+ *lemma* row_val
- \+ *lemma* transpose_col
- \+ *lemma* transpose_row
- \+ *lemma* row_vec_mul
- \+ *lemma* col_vec_mul
- \+ *lemma* col_mul_vec
- \+ *lemma* row_mul_vec

Modified src/linear_algebra/basic.lean
- \+ *lemma* coe_fn_sum

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* coe_fn_mk
- \+ *lemma* coe_fn_congr
- \+ *lemma* add_apply
- \+ *lemma* smul_apply
- \+ *lemma* coe_fn_to_linear_map
- \+ *lemma* map_sum_left
- \+ *lemma* map_sum_right
- \+ *lemma* comp_left_comp_right
- \+ *lemma* comp_right_comp_left
- \+ *lemma* comp_apply
- \+ *lemma* comp_left_apply
- \+ *lemma* comp_right_apply
- \+ *lemma* matrix.to_bilin_form_apply
- \+ *lemma* bilin_form.to_matrix_apply
- \+ *lemma* bilin_form.to_matrix_smul
- \+ *lemma* bilin_form.to_matrix_comp
- \+ *lemma* bilin_form.to_matrix_comp_left
- \+ *lemma* bilin_form.to_matrix_comp_right
- \+ *lemma* bilin_form.mul_to_matrix_mul
- \+ *lemma* bilin_form.mul_to_matrix
- \+ *lemma* bilin_form.to_matrix_mul
- \+ *def* comp
- \+ *def* comp_left
- \+ *def* comp_right
- \+ *def* matrix.to_bilin_formₗ
- \+ *def* matrix.to_bilin_form
- \+ *def* bilin_form.to_matrixₗ
- \+ *def* bilin_form.to_matrix
- \+ *def* bilin_form_equiv_matrix

Modified src/linear_algebra/matrix.lean
- \+ *lemma* to_matrix_id

Created src/linear_algebra/quadratic_form.lean
- \+ *lemma* to_fun_eq_apply
- \+ *lemma* map_smul
- \+ *lemma* map_add_self
- \+ *lemma* map_zero
- \+ *lemma* map_neg
- \+ *lemma* map_sub
- \+ *lemma* ext
- \+ *lemma* smul_apply
- \+ *lemma* comp_apply
- \+ *lemma* polar_to_quadratic_form
- \+ *lemma* to_quadratic_form_apply
- \+ *lemma* associated_apply
- \+ *lemma* associated_is_sym
- \+ *lemma* associated_smul
- \+ *lemma* associated_comp
- \+ *lemma* associated_to_quadratic_form
- \+ *lemma* associated_left_inverse
- \+ *lemma* associated_right_inverse
- \+ *lemma* smul_pos_def_of_smul_nonzero
- \+ *lemma* smul_pos_def_of_nonzero
- \+ *lemma* quadratic_form.to_matrix_smul
- \+ *lemma* to_matrix_comp
- \+ *lemma* discr_smul
- \+ *lemma* discr_comp
- \+ *def* quadratic_form.polar
- \+ *def* comp
- \+ *def* to_quadratic_form
- \+ *def* associated
- \+ *def* pos_def
- \+ *def* matrix.to_quadratic_form
- \+ *def* quadratic_form.to_matrix
- \+ *def* discr



## [2020-04-24 06:43:01](https://github.com/leanprover-community/mathlib/commit/e7bd312)
chore(tactic/pi_instance): add a docstring, remove a little bit of redundancy ([#2500](https://github.com/leanprover-community/mathlib/pull/2500))
#### Estimated changes
Modified src/tactic/pi_instances.lean




## [2020-04-24 04:03:04](https://github.com/leanprover-community/mathlib/commit/b7af283)
feat(algebra): define `invertible` typeclass ([#2504](https://github.com/leanprover-community/mathlib/pull/2504))
In the discussion for [#2480](https://github.com/leanprover-community/mathlib/pull/2480), we decided that the definitions would be cleaner if the elaborator could supply us with a suitable value of `1/2`. With these changes, we can now add an `[invertible 2]` argument to write `⅟ 2`.
Related to Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.232480.20bilinear.20forms
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* left_inv_eq_right_inv

Created src/algebra/invertible.lean
- \+ *lemma* inv_of_mul_self
- \+ *lemma* mul_inv_of_self
- \+ *lemma* mul_inv_of_mul_self_cancel
- \+ *lemma* mul_mul_inv_of_self_cancel
- \+ *lemma* inv_of_eq_right_inv
- \+ *lemma* is_unit_of_invertible
- \+ *lemma* inv_of_eq_group_inv
- \+ *lemma* inv_of_one
- \+ *lemma* inv_of_neg
- \+ *lemma* inv_of_inv_of
- \+ *lemma* inv_of_mul
- \+ *lemma* nonzero_of_invertible
- \+ *lemma* inv_of_eq_inv
- \+ *lemma* inv_mul_cancel_of_invertible
- \+ *lemma* mul_inv_cancel_of_invertible
- \+ *lemma* div_mul_cancel_of_invertible
- \+ *lemma* mul_div_cancel_of_invertible
- \+ *lemma* div_self_of_invertible
- \+ *lemma* inv_of_div
- \+ *def* invertible_of_group
- \+ *def* invertible_one
- \+ *def* invertible_neg
- \+ *def* invertible_inv_of
- \+ *def* invertible_mul
- \+ *def* invertible_of_nonzero
- \+ *def* invertible_div
- \+ *def* invertible_inv



## [2020-04-24 01:03:57](https://github.com/leanprover-community/mathlib/commit/02d7308)
feat(cmd/simp): let `#simp` use declared `variables` ([#2478](https://github.com/leanprover-community/mathlib/pull/2478))
Let `#simp` see declared `variables`.
~~Sits atop the minor `tactic.core` rearrangement in [#2465](https://github.com/leanprover-community/mathlib/pull/2465).~~
@semorrison It turns out that `push_local_scope` and `pop_local_scope` weren't required; the parser is smarter than we thought, and if you declared some `variables` and then tried to `#simp` them, lean would half-know what you are talking about.
Indeed, the parsed `pexpr` from the command would include this information, but `to_expr` would report `no such 'blah'` when called afterward. To fix this you have to add the local variables you want `simp` to be able to see as local hypotheses in the same `tactic_state` in which you invoke `expr.simp`---so no wrapping your call to `expr.simp` directly in `lean.parser.of_tactic` (since this cooks up a fresh `tactic_state` for you).
Closes [#2475](https://github.com/leanprover-community/mathlib/pull/2475).
<br>
<br>
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified src/tactic/simp_command.lean


Modified test/simp_command.lean
- \+ *theorem* spell'
- \+/\- *def* f



## [2020-04-23 23:53:50](https://github.com/leanprover-community/mathlib/commit/0196748)
chore(scripts): update nolints.txt ([#2503](https://github.com/leanprover-community/mathlib/pull/2503))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-23 21:05:16](https://github.com/leanprover-community/mathlib/commit/fdbf22d)
doc(tactic/*): doc entries for some missing tactics ([#2489](https://github.com/leanprover-community/mathlib/pull/2489))
This covers most of the remaining list in the old issue [#450](https://github.com/leanprover-community/mathlib/pull/450). I've already checked off my additions.
#### Estimated changes
Modified src/tactic/default.lean


Modified src/tactic/ring2.lean


Modified src/tactic/scc.lean


Modified src/tactic/slice.lean


Modified src/tactic/split_ifs.lean


Modified src/tactic/subtype_instance.lean


Modified src/tactic/wlog.lean




## [2020-04-23 18:01:07](https://github.com/leanprover-community/mathlib/commit/fc7ac67)
feat(data/string): add docstrings and improve semantics ([#2497](https://github.com/leanprover-community/mathlib/pull/2497))
Could have gone in [#2493](https://github.com/leanprover-community/mathlib/pull/2493), but I didn't want to hold up [#2478](https://github.com/leanprover-community/mathlib/pull/2478). Besides, what's a tiny pull request between friends.
This "writing docstrings" thing really lets helps you discover tiny little tweaks here and here.
<br>
<br>
<br>
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/data/string/defs.lean
- \+/\- *def* split_on
- \+/\- *def* map_tokens
- \- *def* over_list

Modified src/tactic/replacer.lean




## [2020-04-23 15:14:10](https://github.com/leanprover-community/mathlib/commit/9ccfa92)
feat(data/string): add phrasings common to conventional languages ([#2493](https://github.com/leanprover-community/mathlib/pull/2493))
Just add a pair of string comparison functions with semantics which are common to conventional programming languages.
<br>
<br>
<br>
#### Estimated changes
Modified src/data/string/defs.lean




## [2020-04-23 12:15:02](https://github.com/leanprover-community/mathlib/commit/64e464f)
chore(*): remove unnecessary transitive imports ([#2496](https://github.com/leanprover-community/mathlib/pull/2496))
This removes all imports which have already been imported by other imports.
Overall, this is slightly over a third of the total import lines. This should have no effect whatsoever on compilation, but should make `leanproject import-graph` somewhat... leaner!
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/associated.lean


Modified src/algebra/big_operators.lean


Modified src/algebra/category/CommRing/adjunctions.lean


Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/CommRing/default.lean


Modified src/algebra/category/CommRing/limits.lean


Modified src/algebra/category/Group/adjunctions.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Group/default.lean


Modified src/algebra/category/Group/images.lean


Modified src/algebra/category/Group/limits.lean


Modified src/algebra/category/Module/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/category/Mon/default.lean


Modified src/algebra/char_p.lean


Modified src/algebra/char_zero.lean


Modified src/algebra/commute.lean


Modified src/algebra/continued_fractions/default.lean


Modified src/algebra/default.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/field.lean


Modified src/algebra/field_power.lean


Modified src/algebra/floor.lean


Modified src/algebra/free.lean


Modified src/algebra/free_monoid.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group/conj.lean


Modified src/algebra/group/default.lean


Modified src/algebra/group/hom.lean


Modified src/algebra/group/units.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_with_zero_power.lean


Modified src/algebra/lie_algebra.lean


Modified src/algebra/module.lean


Modified src/algebra/order_functions.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/pointwise.lean


Modified src/algebra/quadratic_discriminant.lean


Modified src/algebra/semiconj.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/asymptotics.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/normed_space/riesz_lemma.lean


Modified src/category/bifunctor.lean


Modified src/category/bitraversable/basic.lean


Modified src/category/bitraversable/instances.lean


Modified src/category/equiv_functor/instances.lean


Modified src/category/fold.lean


Modified src/category/functor.lean


Modified src/category/monad/cont.lean


Modified src/category/monad/writer.lean


Modified src/category/traversable/basic.lean


Modified src/category/traversable/default.lean


Modified src/category/traversable/derive.lean


Modified src/category/traversable/instances.lean


Modified src/category/traversable/lemmas.lean


Modified src/category_theory/action.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/category/Groupoid.lean


Modified src/category_theory/comma.lean


Modified src/category_theory/concrete_category/default.lean


Modified src/category_theory/conj.lean


Modified src/category_theory/const.lean


Modified src/category_theory/core.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/differential_object.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/elements.lean


Modified src/category_theory/endomorphism.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/eq_to_hom.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/hom_functor.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/isomorphism_classes.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/functor_category.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/over.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/default.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/limits/types.lean


Modified src/category_theory/monad/limits.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/of_has_finite_products.lean


Modified src/category_theory/monoidal/types.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/pempty.lean


Modified src/category_theory/products/basic.lean


Modified src/category_theory/quotient.lean


Modified src/category_theory/reflect_isomorphisms.lean


Modified src/category_theory/single_obj.lean


Modified src/category_theory/sums/basic.lean


Modified src/category_theory/types.lean


Modified src/category_theory/yoneda.lean


Modified src/computability/turing_machine.lean


Modified src/data/W.lean


Modified src/data/buffer/basic.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/dfinsupp.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/list.lean


Modified src/data/equiv/mul_add.lean


Modified src/data/equiv/nat.lean


Modified src/data/fin_enum.lean


Modified src/data/finset.lean


Modified src/data/finsupp.lean


Modified src/data/fintype/basic.lean


Modified src/data/fintype/card.lean


Modified src/data/fintype/intervals.lean


Modified src/data/hash_map.lean


Modified src/data/indicator_function.lean


Modified src/data/int/basic.lean


Modified src/data/int/gcd.lean


Modified src/data/int/modeq.lean


Modified src/data/int/parity.lean


Modified src/data/list/basic.lean


Modified src/data/list/forall2.lean


Modified src/data/list/func.lean


Modified src/data/matrix/basic.lean


Modified src/data/multiset.lean


Modified src/data/mv_polynomial.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/cast.lean


Modified src/data/nat/choose.lean


Modified src/data/nat/enat.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/parity.lean


Modified src/data/nat/prime.lean


Modified src/data/nat/sqrt.lean


Modified src/data/nat/totient.lean


Modified src/data/num/lemmas.lean


Modified src/data/option/basic.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/pequiv.lean


Modified src/data/pfun.lean


Modified src/data/pnat/basic.lean


Modified src/data/pnat/factors.lean


Modified src/data/pnat/xgcd.lean


Modified src/data/polynomial.lean


Modified src/data/rat/basic.lean


Modified src/data/rat/default.lean


Modified src/data/rat/floor.lean


Modified src/data/real/basic.lean


Modified src/data/real/cardinality.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/hyperreal.lean


Modified src/data/real/irrational.lean


Modified src/data/real/nnreal.lean


Modified src/data/rel.lean


Modified src/data/semiquot.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/seq.lean


Modified src/data/seq/wseq.lean


Modified src/data/set/countable.lean


Modified src/data/set/default.lean


Modified src/data/set/disjointed.lean


Modified src/data/set/finite.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/set/intervals/default.lean


Modified src/data/set/intervals/disjoint.lean


Modified src/data/set/intervals/unordered_interval.lean


Modified src/data/set/lattice.lean


Modified src/data/setoid.lean


Modified src/data/support.lean


Modified src/data/vector2.lean


Modified src/data/zmod/basic.lean


Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/data/zsqrtd/basic.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/field_theory/finite.lean


Modified src/field_theory/finite_card.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/field_theory/splitting_field.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/coset.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/submonoid.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/contraction.lean


Modified src/linear_algebra/determinant.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/nonsingular_inverse.lean


Modified src/linear_algebra/special_linear_group.lean


Modified src/logic/embedding.lean


Modified src/logic/relation.lean


Modified src/measure_theory/indicator_function.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/order/basic.lean


Modified src/order/bounds.lean


Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/default.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/default.lean


Modified src/order/filter/extr.lean


Modified src/order/filter/partial.lean


Modified src/order/galois_connection.lean


Modified src/order/lexicographic.lean


Modified src/order/liminf_limsup.lean


Modified src/order/order_iso.lean


Modified src/order/pilex.lean


Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/fractional_ideal.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/free_ring.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/power_series.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/subring.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/lists.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/set_theory/schroeder_bernstein.lean


Modified src/tactic/abel.lean


Modified src/tactic/alias.lean


Modified src/tactic/apply_fun.lean


Modified src/tactic/auto_cases.lean


Modified src/tactic/basic.lean


Modified src/tactic/chain.lean


Modified src/tactic/converter/binders.lean


Modified src/tactic/core.lean


Modified src/tactic/default.lean


Modified src/tactic/elide.lean


Modified src/tactic/equiv_rw.lean


Modified src/tactic/ext.lean


Modified src/tactic/finish.lean


Modified src/tactic/interval_cases.lean


Modified src/tactic/linarith.lean


Modified src/tactic/local_cache.lean


Modified src/tactic/localized.lean


Modified src/tactic/monotonicity/basic.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/norm_num.lean


Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/int/preterm.lean


Modified src/tactic/omega/main.lean


Modified src/tactic/pi_instances.lean


Modified src/tactic/replacer.lean


Modified src/tactic/rewrite_all/basic.lean


Modified src/tactic/rewrite_all/congr.lean


Modified src/tactic/ring.lean


Modified src/tactic/ring2.lean


Modified src/tactic/scc.lean


Modified src/tactic/show_term.lean


Modified src/tactic/subtype_instance.lean


Modified src/tactic/tauto.lean


Modified src/tactic/tfae.lean


Modified src/tactic/tidy.lean


Modified src/tactic/trunc_cases.lean


Modified src/tactic/where.lean


Modified src/tactic/wlog.lean


Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/bases.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/category/Top/default.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/category/Top/open_nhds.lean


Modified src/topology/category/Top/opens.lean


Modified src/topology/category/UniformSpace.lean


Modified src/topology/homeomorph.lean


Modified src/topology/instances/complex.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/cau_seq_filter.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/contracting.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/metric_space/premetric_space.lean


Modified src/topology/opens.lean


Modified src/topology/sequences.lean


Modified src/topology/sheaves/presheaf.lean


Modified src/topology/sheaves/presheaf_of_functions.lean


Modified src/topology/uniform_space/abstract_completion.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/completion.lean




## [2020-04-23 09:12:20](https://github.com/leanprover-community/mathlib/commit/8a7b94f)
chore(tactic/suggest): add a docstring ([#2499](https://github.com/leanprover-community/mathlib/pull/2499))
#### Estimated changes
Modified src/tactic/suggest.lean




## [2020-04-23 02:52:58](https://github.com/leanprover-community/mathlib/commit/7c10fd2)
feat(category_theory/epi_mono): opposite epi mono properties ([#2479](https://github.com/leanprover-community/mathlib/pull/2479))
Relating epis and monos to the opposite category.
#### Estimated changes
Modified src/category_theory/epi_mono.lean




## [2020-04-23 01:10:17](https://github.com/leanprover-community/mathlib/commit/4d94de4)
feat(category_theory): wide pullbacks and limits in the over category ([#2461](https://github.com/leanprover-community/mathlib/pull/2461))
This PR introduces [wide pullbacks](https://ncatlab.org/nlab/show/wide+pullback). 
Ordinary pullbacks are then defined as a special case of wide pullbacks, which simplifies some of the definitions and proofs there. 
Finally we show that the existence of wide pullbacks in `C` gives products in the slice `C/B`, and in fact gives all limits.
#### Estimated changes
Modified src/category_theory/adjunction/basic.lean
- \+ *lemma* hom_equiv_apply_eq
- \+ *lemma* eq_hom_equiv_apply

Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/limits.lean
- \+ *def* of_cone_equiv

Modified src/category_theory/limits/over.lean
- \- *lemma* over_prod_pair_left
- \- *lemma* over_prod_pair_hom
- \- *lemma* over_prod_fst_left
- \- *lemma* over_prod_snd_left
- \- *lemma* over_prod_map_left
- \+ *def* wide_pullback_diagram_of_diagram_over
- \+ *def* cones_equiv_inverse
- \+ *def* cones_equiv_functor
- \+ *def* cones_equiv
- \+ *def* has_over_limit_discrete_of_wide_pullback_limit
- \+ *def* over_product_of_wide_pullback
- \+ *def* over_binary_product_of_pullback
- \+ *def* over_products_of_wide_pullbacks
- \+ *def* over_finite_products_of_finite_wide_pullbacks
- \- *def* over_product_of_pullbacks

Modified src/category_theory/limits/shapes/pullbacks.lean
- \- *lemma* hom_id
- \- *lemma* cone.of_pullback_cone_π
- \- *lemma* cocone.of_pushout_cocone_ι
- \- *lemma* pullback_cone.of_cone_π
- \- *lemma* pushout_cocone.of_cocone_ι
- \- *def* hom.comp

Created src/category_theory/limits/shapes/wide_pullbacks.lean
- \+ *lemma* hom_id
- \+ *def* wide_pullback_shape
- \+ *def* wide_pushout_shape
- \+ *def* wide_cospan
- \+ *def* diagram_iso_wide_cospan
- \+ *def* wide_span
- \+ *def* diagram_iso_wide_span
- \+ *def* has_finite_wide_pullbacks_of_has_finite_limits
- \+ *def* has_finite_wide_pushouts_of_has_finite_limits



## [2020-04-22 23:11:50](https://github.com/leanprover-community/mathlib/commit/4dadd26)
chore(scripts): update nolints.txt ([#2495](https://github.com/leanprover-community/mathlib/pull/2495))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-22 21:20:58](https://github.com/leanprover-community/mathlib/commit/bcbdeba)
chore(tactic/apply_fun): add doc string and remove duplication ([#2485](https://github.com/leanprover-community/mathlib/pull/2485))
I was just adding a docstring to `tactic.apply_fun`, and then saw some duplication and removed it. An example of a use of [#2484](https://github.com/leanprover-community/mathlib/pull/2484).
<br>
<br>
<br>
#### Estimated changes
Modified src/tactic/apply_fun.lean




## [2020-04-22 18:31:17](https://github.com/leanprover-community/mathlib/commit/691a230)
chore(scripts): update nolints.txt ([#2494](https://github.com/leanprover-community/mathlib/pull/2494))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-22 18:31:15](https://github.com/leanprover-community/mathlib/commit/2fb6022)
feat(mk_iff_of_inductive_prop): add, use, and document command ([#2490](https://github.com/leanprover-community/mathlib/pull/2490))
This existed as an (undocumented) tactic that was being called with `run_cmd`. It deserves to be a documented user command.
#### Estimated changes
Modified src/data/list/chain.lean


Modified src/data/list/forall2.lean


Modified src/data/list/pairwise.lean


Modified src/data/multiset.lean


Modified src/field_theory/perfect_closure.lean


Modified src/logic/relation.lean


Modified src/tactic/mk_iff_of_inductive_prop.lean


Modified test/mk_iff_of_inductive.lean




## [2020-04-22 16:17:53](https://github.com/leanprover-community/mathlib/commit/591a0a0)
chore(*): only import one file per line ([#2470](https://github.com/leanprover-community/mathlib/pull/2470))
This perhaps-unnecessarily-obsessive PR puts every import statement on its own line.
Why?
1. it's nice to be able to grep for `import X`
2. ~~if we enforced this, it would be easier deal with commands after imports, etc.~~ (irrelevant in 3.9)
3. it means I can remove all unnecessary transitive imports with a script
4. it's just tidier. :-)
#### Estimated changes
Modified archive/cubing_a_cube.lean


Modified docs/contribute/doc.md


Modified docs/contribute/style.md


Modified scripts/lint_mathlib.lean


Modified src/algebra/archimedean.lean


Modified src/algebra/associated.lean


Modified src/algebra/big_operators.lean


Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/char_p.lean


Modified src/algebra/char_zero.lean


Modified src/algebra/commute.lean


Modified src/algebra/default.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/direct_sum.lean


Modified src/algebra/field.lean


Modified src/algebra/field_power.lean


Modified src/algebra/floor.lean


Modified src/algebra/free.lean


Modified src/algebra/free_monoid.lean


Modified src/algebra/gcd_domain.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group/basic.lean


Modified src/algebra/group/conj.lean


Modified src/algebra/group/default.lean


Modified src/algebra/group/hom.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group/to_additive.lean


Modified src/algebra/group/units.lean


Modified src/algebra/group/units_hom.lean


Modified src/algebra/group/with_one.lean


Modified src/algebra/group_power.lean


Modified src/algebra/group_with_zero.lean


Modified src/algebra/group_with_zero_power.lean


Modified src/algebra/lie_algebra.lean


Modified src/algebra/module.lean


Modified src/algebra/order_functions.lean


Modified src/algebra/ordered_field.lean


Modified src/algebra/ordered_group.lean


Modified src/algebra/ordered_ring.lean


Modified src/algebra/pointwise.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/quadratic_discriminant.lean


Modified src/algebra/ring.lean


Modified src/algebra/semiconj.lean


Modified src/algebraic_geometry/prime_spectrum.lean


Modified src/analysis/ODE/gronwall.lean


Modified src/analysis/analytic/basic.lean


Modified src/analysis/analytic/composition.lean


Modified src/analysis/asymptotics.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/iterated_deriv.lean


Modified src/analysis/calculus/local_extr.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/calculus/specific_functions.lean


Modified src/analysis/calculus/tangent_cone.lean


Modified src/analysis/calculus/times_cont_diff.lean


Modified src/analysis/complex/basic.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/convex/cone.lean


Modified src/analysis/convex/specific_functions.lean


Modified src/analysis/convex/topology.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/hahn_banach.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/normed_space/operator_norm.lean


Modified src/analysis/normed_space/real_inner_product.lean


Modified src/analysis/normed_space/riesz_lemma.lean


Modified src/analysis/specific_limits.lean


Modified src/category/applicative.lean


Modified src/category/bifunctor.lean


Modified src/category/bitraversable/basic.lean


Modified src/category/bitraversable/instances.lean


Modified src/category/bitraversable/lemmas.lean


Modified src/category/equiv_functor.lean


Modified src/category/fold.lean


Modified src/category/functor.lean


Modified src/category/monad/basic.lean


Modified src/category/monad/cont.lean


Modified src/category/monad/writer.lean


Modified src/category/traversable/basic.lean


Modified src/category/traversable/default.lean


Modified src/category/traversable/derive.lean


Modified src/category/traversable/equiv.lean


Modified src/category/traversable/instances.lean


Modified src/category/traversable/lemmas.lean


Modified src/category_theory/action.lean


Modified src/category_theory/category/Cat.lean


Modified src/category_theory/category/default.lean


Modified src/category_theory/concrete_category/basic.lean


Modified src/category_theory/conj.lean


Modified src/category_theory/connected.lean


Modified src/category_theory/const.lean


Modified src/category_theory/core.lean


Modified src/category_theory/currying.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/endomorphism.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/functorial.lean


Modified src/category_theory/groupoid.lean


Modified src/category_theory/isomorphism_classes.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/shapes/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/constructions/equalizers.lean


Modified src/category_theory/limits/shapes/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/shapes/constructions/pullbacks.lean


Modified src/category_theory/monad/default.lean


Modified src/category_theory/monad/types.lean


Modified src/category_theory/natural_transformation.lean


Modified src/category_theory/quotient.lean


Modified src/category_theory/single_obj.lean


Modified src/combinatorics/composition.lean


Modified src/computability/halting.lean


Modified src/computability/partrec.lean


Modified src/computability/reduce.lean


Modified src/computability/turing_machine.lean


Modified src/data/W.lean


Modified src/data/analysis/topology.lean


Modified src/data/array/lemmas.lean


Modified src/data/buffer/basic.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/dfinsupp.lean


Modified src/data/dlist/basic.lean


Modified src/data/dlist/instances.lean


Modified src/data/equiv/basic.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/encodable.lean


Modified src/data/equiv/fin.lean


Modified src/data/equiv/functor.lean


Modified src/data/equiv/list.lean


Modified src/data/equiv/local_equiv.lean


Modified src/data/equiv/mul_add.lean


Modified src/data/equiv/nat.lean


Modified src/data/equiv/ring.lean


Modified src/data/equiv/transfer_instance.lean


Modified src/data/erased.lean


Modified src/data/finmap.lean


Modified src/data/finset.lean


Modified src/data/finsupp.lean


Modified src/data/fintype/basic.lean


Modified src/data/fintype/card.lean


Modified src/data/fp/basic.lean


Modified src/data/hash_map.lean


Modified src/data/indicator_function.lean


Modified src/data/int/basic.lean


Modified src/data/int/gcd.lean


Modified src/data/int/modeq.lean


Modified src/data/int/parity.lean


Modified src/data/int/sqrt.lean


Modified src/data/lazy_list2.lean


Modified src/data/list/basic.lean


Modified src/data/list/defs.lean


Modified src/data/list/sigma.lean


Modified src/data/matrix/basic.lean


Modified src/data/matrix/pequiv.lean


Modified src/data/multiset.lean


Modified src/data/mv_polynomial.lean


Modified src/data/nat/basic.lean


Modified src/data/nat/cast.lean


Modified src/data/nat/choose.lean


Modified src/data/nat/enat.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/multiplicity.lean


Modified src/data/nat/parity.lean


Modified src/data/nat/prime.lean
- \+/\- *lemma* factors_prime

Modified src/data/nat/sqrt.lean


Modified src/data/nat/totient.lean


Modified src/data/num/bitwise.lean


Modified src/data/num/lemmas.lean


Modified src/data/option/basic.lean


Modified src/data/padics/hensel.lean


Modified src/data/padics/padic_integers.lean


Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean


Modified src/data/pequiv.lean


Modified src/data/pfun.lean


Modified src/data/pnat/basic.lean


Modified src/data/pnat/factors.lean


Modified src/data/pnat/xgcd.lean


Modified src/data/polynomial.lean


Modified src/data/prod.lean


Modified src/data/rat/basic.lean


Modified src/data/rat/denumerable.lean


Modified src/data/rat/meta_defs.lean


Modified src/data/real/basic.lean


Modified src/data/real/cardinality.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/ereal.lean


Modified src/data/real/hyperreal.lean


Modified src/data/real/irrational.lean


Modified src/data/real/nnreal.lean


Modified src/data/real/pi.lean


Modified src/data/rel.lean


Modified src/data/semiquot.lean


Modified src/data/seq/computation.lean


Modified src/data/seq/seq.lean


Modified src/data/seq/wseq.lean


Modified src/data/set/basic.lean


Modified src/data/set/countable.lean


Modified src/data/set/default.lean


Modified src/data/set/disjointed.lean


Modified src/data/set/enumerate.lean


Modified src/data/set/finite.lean


Modified src/data/set/function.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/set/intervals/default.lean


Modified src/data/set/intervals/disjoint.lean


Modified src/data/set/intervals/unordered_interval.lean


Modified src/data/set/lattice.lean


Modified src/data/setoid.lean


Modified src/data/sigma/basic.lean


Modified src/data/stream/basic.lean


Modified src/data/string/basic.lean


Modified src/data/support.lean


Modified src/data/tree.lean


Modified src/data/vector2.lean


Modified src/data/zmod/basic.lean


Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/data/zsqrtd/basic.lean


Modified src/data/zsqrtd/gaussian_int.lean


Modified src/deprecated/group.lean


Modified src/field_theory/finite.lean


Modified src/field_theory/finite_card.lean


Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/mv_polynomial.lean


Modified src/field_theory/perfect_closure.lean


Modified src/field_theory/splitting_field.lean


Modified src/field_theory/subfield.lean


Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/manifold.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/geometry/manifold/real_instances.lean


Modified src/geometry/manifold/smooth_manifold_with_corners.lean


Modified src/group_theory/abelianization.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/coset.lean


Modified src/group_theory/eckmann_hilton.lean


Modified src/group_theory/group_action.lean


Modified src/group_theory/monoid_localization.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/presented_group.lean


Modified src/group_theory/submonoid.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/bilinear_form.lean


Modified src/linear_algebra/direct_sum_module.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/finsupp.lean


Modified src/linear_algebra/finsupp_vector_space.lean


Modified src/linear_algebra/matrix.lean


Modified src/linear_algebra/multilinear.lean


Modified src/linear_algebra/sesquilinear_form.lean


Modified src/linear_algebra/tensor_product.lean


Modified src/logic/basic.lean


Modified src/logic/embedding.lean


Modified src/logic/function.lean


Modified src/logic/relation.lean


Modified src/measure_theory/ae_eq_fun.lean


Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/indicator_function.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/measure_theory/set_integral.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/meta/expr.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/dioph.lean


Modified src/number_theory/pell.lean


Modified src/number_theory/sum_four_squares.lean


Modified src/order/basic.lean


Modified src/order/boolean_algebra.lean


Modified src/order/bounded_lattice.lean


Modified src/order/bounds.lean


Modified src/order/complete_boolean_algebra.lean


Modified src/order/complete_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/copy.lean


Modified src/order/default.lean


Modified src/order/filter/bases.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/default.lean


Modified src/order/filter/extr.lean


Modified src/order/filter/filter_product.lean


Modified src/order/filter/pointwise.lean


Modified src/order/galois_connection.lean


Modified src/order/lattice.lean


Modified src/order/liminf_limsup.lean


Modified src/order/order_iso.lean


Modified src/order/pilex.lean


Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/adjoin_root.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/euclidean_domain.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/free_ring.lean


Modified src/ring_theory/ideal_operations.lean


Modified src/ring_theory/ideals.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/maps.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/noetherian.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/power_series.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/subring.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/lists.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/ordinal_notation.lean


Modified src/set_theory/schroeder_bernstein.lean


Modified src/tactic/abel.lean


Modified src/tactic/algebra.lean


Modified src/tactic/alias.lean


Modified src/tactic/apply_fun.lean


Modified src/tactic/basic.lean


Modified src/tactic/clear.lean


Modified src/tactic/converter/apply_congr.lean


Modified src/tactic/converter/binders.lean


Modified src/tactic/converter/interactive.lean


Modified src/tactic/core.lean


Modified src/tactic/default.lean


Modified src/tactic/derive_inhabited.lean


Modified src/tactic/doc_commands.lean


Modified src/tactic/elide.lean


Modified src/tactic/explode.lean


Modified src/tactic/ext.lean


Modified src/tactic/finish.lean


Modified src/tactic/linarith.lean


Modified src/tactic/lint/default.lean


Modified src/tactic/local_cache.lean


Modified src/tactic/localized.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/norm_cast.lean


Modified src/tactic/norm_num.lean


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


Modified src/tactic/pi_instances.lean


Modified src/tactic/rcases.lean


Modified src/tactic/rename_var.lean


Modified src/tactic/replacer.lean


Modified src/tactic/restate_axiom.lean


Modified src/tactic/rewrite.lean


Modified src/tactic/rewrite_all/basic.lean


Modified src/tactic/ring.lean


Modified src/tactic/ring2.lean


Modified src/tactic/scc.lean


Modified src/tactic/simpa.lean


Modified src/tactic/subtype_instance.lean


Modified src/tactic/suggest.lean


Modified src/tactic/tauto.lean


Modified src/tactic/tfae.lean


Modified src/tactic/transfer.lean


Modified src/tactic/transform_decl.lean


Modified src/tactic/wlog.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/group_completion.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/multilinear.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/polynomial.lean


Modified src/topology/algebra/ring.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/uniform_ring.lean


Modified src/topology/bases.lean


Modified src/topology/basic.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/category/UniformSpace.lean


Modified src/topology/compact_open.lean


Modified src/topology/homeomorph.lean


Modified src/topology/instances/complex.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/instances/real.lean


Modified src/topology/local_extr.lean


Modified src/topology/local_homeomorph.lean


Modified src/topology/metric_space/baire.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/cau_seq_filter.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/completion.lean


Modified src/topology/metric_space/contracting.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/gluing.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/metric_space/lipschitz.lean


Modified src/topology/metric_space/premetric_space.lean


Modified src/topology/opens.lean


Modified src/topology/separation.lean


Modified src/topology/sequences.lean


Modified src/topology/stone_cech.lean


Modified src/topology/subset_properties.lean


Modified src/topology/topological_fiber_bundle.lean


Modified src/topology/uniform_space/absolute_value.lean


Modified src/topology/uniform_space/abstract_completion.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/compare_reals.lean


Modified src/topology/uniform_space/complete_separated.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/pi.lean


Modified src/topology/uniform_space/uniform_convergence.lean


Modified src/topology/uniform_space/uniform_embedding.lean


Modified test/tactics.lean




## [2020-04-22 15:09:08](https://github.com/leanprover-community/mathlib/commit/8865b00)
chore(scripts): update nolints.txt ([#2491](https://github.com/leanprover-community/mathlib/pull/2491))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-22 12:17:00](https://github.com/leanprover-community/mathlib/commit/d40662f)
chore(tactic/auto_cases): add docstring and remove duplication ([#2488](https://github.com/leanprover-community/mathlib/pull/2488))
I was just adding a docstring, and I saw some duplication so I removed it too.
<br>
<br>
<br>
#### Estimated changes
Modified src/tactic/auto_cases.lean




## [2020-04-22 12:16:58](https://github.com/leanprover-community/mathlib/commit/f760ad5)
chore(meta/expr): add a docstring ([#2487](https://github.com/leanprover-community/mathlib/pull/2487))
Add a docstring.
<br>
<br>
<br>
#### Estimated changes
Modified src/meta/expr.lean




## [2020-04-22 12:16:56](https://github.com/leanprover-community/mathlib/commit/62a613f)
feat(data/option): add `option.mmap` and `option.maybe` ([#2484](https://github.com/leanprover-community/mathlib/pull/2484))
Please let me know if something like this exists already! Over the last few days I've wanted it multiple times, and it is used in [#2485](https://github.com/leanprover-community/mathlib/pull/2485).
<br>
<br>
<br>
#### Estimated changes
Modified src/data/option/defs.lean
- \+ *def* {u



## [2020-04-22 12:16:54](https://github.com/leanprover-community/mathlib/commit/e4abced)
chore(data/polynomial): rename type vars ([#2483](https://github.com/leanprover-community/mathlib/pull/2483))
Rename `α` to `R` etc; use `ι` for index types
No other changes
#### Estimated changes
Modified src/data/polynomial.lean
- \+/\- *lemma* support_zero
- \+/\- *lemma* coeff_mk
- \+/\- *lemma* ext
- \+/\- *lemma* degree_lt_wf
- \+/\- *lemma* sum_C_mul_X_eq
- \+/\- *lemma* C_0
- \+/\- *lemma* C_1
- \+/\- *lemma* nat_cast_eq_C
- \+/\- *lemma* coeff_zero
- \+/\- *lemma* coeff_one_zero
- \+/\- *lemma* coeff_add
- \+/\- *lemma* coeff_X_one
- \+/\- *lemma* coeff_X_zero
- \+/\- *lemma* coeff_X
- \+/\- *lemma* coeff_C_mul_X
- \+/\- *lemma* coeff_sum
- \+/\- *lemma* coeff_C_mul
- \+/\- *lemma* coeff_smul
- \+/\- *lemma* C_mul'
- \+/\- *lemma* coeff_one
- \+/\- *lemma* coeff_mul
- \+/\- *lemma* eval₂_zero
- \+/\- *lemma* eval₂_one
- \+/\- *lemma* coe_eval₂_ring_hom
- \+/\- *lemma* eval₂_sum
- \+/\- *lemma* eval_zero
- \+/\- *lemma* eval_one
- \+/\- *lemma* eval_sum
- \+/\- *lemma* eval₂_hom
- \+/\- *lemma* root_mul_left_of_is_root
- \+/\- *lemma* root_mul_right_of_is_root
- \+/\- *lemma* coeff_zero_eq_eval_zero
- \+/\- *lemma* zero_is_root_of_coeff_zero_eq_zero
- \+/\- *lemma* eval₂_comp
- \+/\- *lemma* comp_zero
- \+/\- *lemma* zero_comp
- \+/\- *lemma* one_comp
- \+/\- *lemma* monic.leading_coeff
- \+/\- *lemma* degree_zero
- \+/\- *lemma* nat_degree_zero
- \+/\- *lemma* degree_one_le
- \+/\- *lemma* degree_eq_iff_nat_degree_eq
- \+/\- *lemma* degree_eq_iff_nat_degree_eq_of_pos
- \+/\- *lemma* nat_degree_eq_of_degree_eq_some
- \+/\- *lemma* nat_degree_eq_of_degree_eq
- \+/\- *lemma* nat_degree_C
- \+/\- *lemma* nat_degree_one
- \+/\- *lemma* nat_degree_nat_cast
- \+/\- *lemma* degree_monomial_le
- \+/\- *lemma* coeff_eq_zero_of_nat_degree_lt
- \+/\- *lemma* finset_sum_coeff
- \+/\- *lemma* ite_le_nat_degree_coeff
- \+/\- *lemma* as_sum
- \+/\- *lemma* monic.as_sum
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_one
- \+/\- *lemma* map_map
- \+/\- *lemma* eval₂_map
- \+/\- *lemma* eval_map
- \+/\- *lemma* mem_map_range
- \+/\- *lemma* hom_eval₂
- \+/\- *lemma* degree_add_le
- \+/\- *lemma* leading_coeff_zero
- \+/\- *lemma* degree_erase_le
- \+/\- *lemma* degree_sum_le
- \+/\- *lemma* degree_mul_le
- \+/\- *lemma* degree_pow_le
- \+/\- *lemma* leading_coeff_monomial
- \+/\- *lemma* leading_coeff_C
- \+/\- *lemma* leading_coeff_X
- \+/\- *lemma* monic_X
- \+/\- *lemma* leading_coeff_one
- \+/\- *lemma* monic_one
- \+/\- *lemma* monic.ne_zero_of_zero_ne_one
- \+/\- *lemma* monic.ne_zero
- \+/\- *lemma* coeff_mul_degree_add_degree
- \+/\- *lemma* leading_coeff_X_pow
- \+/\- *lemma* degree_map_le
- \+/\- *lemma* subsingleton_of_monic_zero
- \+/\- *lemma* degree_map_eq_of_leading_coeff_ne_zero
- \+/\- *lemma* monic_map
- \+/\- *lemma* zero_le_degree_iff
- \+/\- *lemma* coeff_mul_X_zero
- \+/\- *lemma* ne_zero_of_monic_of_zero_ne_one
- \+/\- *lemma* degree_map_eq_of_injective
- \+/\- *lemma* degree_map'
- \+/\- *lemma* nat_degree_map'
- \+/\- *lemma* map_injective
- \+/\- *lemma* leading_coeff_of_injective
- \+/\- *lemma* monic_of_injective
- \+/\- *lemma* degree_one
- \+/\- *lemma* degree_X
- \+/\- *lemma* X_ne_zero
- \+/\- *lemma* degree_X_pow
- \+/\- *lemma* not_monic_zero
- \+/\- *lemma* div_X_mul_X_add
- \+/\- *lemma* div_X_C
- \+/\- *lemma* lcoeff_apply
- \+/\- *lemma* int_cast_eq_C
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg
- \+/\- *lemma* degree_neg
- \+/\- *lemma* nat_degree_neg
- \+/\- *lemma* nat_degree_int_cast
- \+/\- *lemma* coeff_neg
- \+/\- *lemma* coeff_sub
- \+/\- *lemma* eval₂_neg
- \+/\- *lemma* eval₂_sub
- \+/\- *lemma* eval_neg
- \+/\- *lemma* eval_sub
- \+/\- *lemma* degree_mod_by_monic_lt
- \+/\- *lemma* mod_by_monic_eq_sub_mul_div
- \+/\- *lemma* mod_by_monic_add_div
- \+/\- *lemma* zero_mod_by_monic
- \+/\- *lemma* zero_div_by_monic
- \+/\- *lemma* mod_by_monic_zero
- \+/\- *lemma* div_by_monic_zero
- \+/\- *lemma* div_by_monic_eq_of_not_monic
- \+/\- *lemma* mod_by_monic_eq_of_not_monic
- \+/\- *lemma* degree_div_by_monic_le
- \+/\- *lemma* degree_div_by_monic_lt
- \+/\- *lemma* div_mod_by_monic_unique
- \+/\- *lemma* map_mod_div_by_monic
- \+/\- *lemma* map_div_by_monic
- \+/\- *lemma* map_mod_by_monic
- \+/\- *lemma* mod_by_monic_one
- \+/\- *lemma* div_by_monic_one
- \+/\- *lemma* degree_X_sub_C
- \+/\- *lemma* degree_X_pow_sub_C
- \+/\- *lemma* X_pow_sub_C_ne_zero
- \+/\- *lemma* mod_by_monic_X_sub_C_eq_C_eval
- \+/\- *lemma* mod_by_monic_X
- \+/\- *lemma* multiplicity_X_sub_C_finite
- \+/\- *lemma* root_multiplicity_eq_multiplicity
- \+/\- *lemma* pow_root_multiplicity_dvd
- \+/\- *lemma* degree_pow_eq
- \+/\- *lemma* leading_coeff_mul
- \+/\- *lemma* leading_coeff_pow
- \+/\- *lemma* nat_degree_pow_eq
- \+/\- *lemma* degree_le_mul_left
- \+/\- *lemma* exists_finset_roots
- \+/\- *lemma* card_roots'
- \+/\- *lemma* card_roots_sub_C
- \+/\- *lemma* card_roots_sub_C'
- \+/\- *lemma* mem_roots_sub_C
- \+/\- *lemma* card_roots_X_pow_sub_C
- \+/\- *lemma* mem_nth_roots
- \+/\- *lemma* card_nth_roots
- \+/\- *lemma* degree_coe_units
- \+/\- *lemma* nat_degree_coe_units
- \+/\- *lemma* coeff_coe_units_zero_ne_zero
- \+/\- *lemma* degree_eq_one_of_irreducible_of_root
- \+/\- *lemma* degree_mul_leading_coeff_inv
- \+/\- *lemma* mod_by_monic_eq_mod
- \+/\- *lemma* div_by_monic_eq_div
- \+/\- *lemma* mod_X_sub_C_eq_C_eval
- \+/\- *lemma* degree_div_le
- \+/\- *lemma* degree_map
- \+/\- *lemma* nat_degree_map
- \+/\- *lemma* leading_coeff_map
- \+/\- *lemma* map_div
- \+/\- *lemma* map_mod
- \+/\- *lemma* map_eq_zero
- \+/\- *lemma* coeff_inv_units
- \+/\- *lemma* coe_norm_unit
- \+/\- *lemma* coeff_derivative
- \+/\- *lemma* derivative_zero
- \+/\- *lemma* derivative_monomial
- \+/\- *lemma* derivative_C
- \+/\- *lemma* derivative_X
- \+/\- *lemma* derivative_one
- \+/\- *lemma* derivative_add
- \+/\- *lemma* derivative_sum
- \+/\- *lemma* derivative_mul
- \+/\- *lemma* derivative_eval
- \+/\- *lemma* mem_support_derivative
- \+/\- *lemma* degree_derivative_eq
- \+/\- *lemma* polynomial
- \+/\- *theorem* ext_iff
- \+/\- *theorem* coeff_mul_X_pow
- \+/\- *theorem* coeff_mul_X
- \+/\- *theorem* mul_X_pow_eq_zero
- \+/\- *theorem* degree_C_mul_X_pow_le
- \+/\- *theorem* degree_X_pow_le
- \+/\- *theorem* degree_X_le
- \+/\- *theorem* monic_X_add_C
- \+/\- *theorem* degree_le_iff_coeff_zero
- \+/\- *theorem* nat_degree_le_of_degree_le
- \+/\- *theorem* leading_coeff_mul_X_pow
- \+/\- *theorem* monic_X_sub_C
- \+/\- *theorem* degree_mod_by_monic_le
- \+/\- *def* polynomial
- \+/\- *def* coeff_coe_to_fun
- \+/\- *def* monomial
- \+/\- *def* C
- \+/\- *def* X
- \+/\- *def* coeff
- \+/\- *def* degree
- \+/\- *def* nat_degree
- \+/\- *def* eval₂
- \+/\- *def* eval₂_ring_hom
- \+/\- *def* eval
- \+/\- *def* is_root
- \+/\- *def* comp
- \+/\- *def* leading_coeff
- \+/\- *def* monic
- \+/\- *def* map
- \+/\- *def* div_X
- \+/\- *def* nonzero_comm_semiring.of_polynomial_ne
- \+/\- *def* lcoeff
- \+/\- *def* div_by_monic
- \+/\- *def* mod_by_monic
- \+/\- *def* nonzero_comm_ring.of_polynomial_ne
- \+/\- *def* decidable_dvd_monic
- \+/\- *def* root_multiplicity
- \+/\- *def* nth_roots
- \+/\- *def* div
- \+/\- *def* mod
- \+/\- *def* derivative
- \+/\- *def* pow_add_expansion
- \+/\- *def* binom_expansion
- \+/\- *def* pow_sub_pow_factor
- \+/\- *def* eval_sub_factor

Modified src/ring_theory/adjoin.lean




## [2020-04-22 12:16:52](https://github.com/leanprover-community/mathlib/commit/5965370)
feat(data/monoid_algebra): algebra structure, lift of morphisms ([#2366](https://github.com/leanprover-community/mathlib/pull/2366))
Prove that for a monoid homomorphism `f : G →* R` from a monoid `G` to a `k`-algebra `R` there exists a unique algebra morphism `g : k[G] →ₐ[k] R` such that `∀ x : G, g (single x 1) = f x`.
This is expressed as `def lift : (G →* R) ≃ (monoid_algebra k G →ₐ[k] R)`.
I want to use this to define `aeval` and `eval₂` for polynomials. This way we'll have many properties for free.
#### Estimated changes
Modified src/algebra/ring.lean
- \+/\- *lemma* coe_monoid_hom
- \+/\- *lemma* coe_add_monoid_hom
- \+/\- *lemma* coe_monoid_hom'
- \+/\- *lemma* coe_add_monoid_hom'

Modified src/data/monoid_algebra.lean
- \+ *lemma* mul_apply_antidiagonal
- \+/\- *lemma* single_mul_single
- \+ *lemma* single_pow
- \+ *lemma* of_apply
- \+ *lemma* mul_single_apply_aux
- \+ *lemma* mul_single_one_apply
- \+ *lemma* single_mul_apply_aux
- \+ *lemma* single_one_mul_apply
- \+ *lemma* coe_algebra_map
- \+ *lemma* single_eq_algebra_map_mul_of
- \+ *lemma* lift_apply
- \+ *lemma* lift_symm_apply
- \+ *lemma* lift_of
- \+ *lemma* lift_single
- \+ *lemma* lift_unique'
- \+ *lemma* lift_unique
- \+ *lemma* alg_hom_ext
- \+/\- *lemma* mul_apply_left
- \+/\- *lemma* mul_apply_right
- \+ *lemma* mul_apply
- \+ *lemma* mul_single_zero_apply
- \+ *lemma* single_zero_mul_apply
- \+ *def* of
- \+ *def* lift

Modified src/data/padics/padic_integers.lean


Modified src/data/polynomial.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* coe_mk
- \+ *lemma* coe_to_ring_hom
- \+ *lemma* coe_to_monoid_hom
- \+ *lemma* map_smul
- \+ *lemma* map_pow
- \+ *lemma* map_sum
- \+ *lemma* map_prod
- \+ *def* ring_hom.to_algebra'
- \+/\- *def* ring_hom.to_algebra

Modified src/ring_theory/localization.lean


Modified src/topology/algebra/module.lean




## [2020-04-22 09:12:07](https://github.com/leanprover-community/mathlib/commit/142f001)
chore(cmd/where): remove unused argument ([#2486](https://github.com/leanprover-community/mathlib/pull/2486))
Just remove an unused argument from the `#where` declaration, satisfying the linter.
<br>
<br>
<br>
#### Estimated changes
Modified src/tactic/where.lean




## [2020-04-22 03:48:09](https://github.com/leanprover-community/mathlib/commit/5e2025f)
feat(group_theory/bundled_subgroup): bundled subgroup ([#2140](https://github.com/leanprover-community/mathlib/pull/2140))
Add bundled subgroups. While `is_subgroup` is a class taking `s : set G` as an argument, `subgroup G` is a structure with a field `carrier : set G` and a coercion to `set G`.
#### Estimated changes
Created src/group_theory/bundled_subgroup.lean
- \+ *lemma* mem_coe
- \+ *lemma* coe_coe
- \+ *lemma* list_prod_mem
- \+ *lemma* multiset_prod_mem
- \+ *lemma* prod_mem
- \+ *lemma* pow_mem
- \+ *lemma* gpow_mem
- \+ *lemma* coe_mul
- \+ *lemma* coe_one
- \+ *lemma* coe_inv
- \+ *lemma* le_def
- \+ *lemma* coe_subset_coe
- \+ *lemma* coe_ssubset_coe
- \+ *lemma* mem_bot
- \+ *lemma* mem_top
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_inf
- \+ *lemma* mem_inf
- \+ *lemma* coe_Inf
- \+ *lemma* mem_Inf
- \+ *lemma* mem_closure
- \+ *lemma* subset_closure
- \+ *lemma* closure_le
- \+ *lemma* closure_mono
- \+ *lemma* closure_eq_of_le
- \+ *lemma* closure_induction
- \+ *lemma* closure_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_union
- \+ *lemma* closure_Union
- \+ *lemma* mem_closure_singleton
- \+ *lemma* mem_supr_of_directed
- \+ *lemma* mem_Sup_of_directed_on
- \+ *lemma* coe_comap
- \+ *lemma* mem_comap
- \+ *lemma* comap_comap
- \+ *lemma* coe_map
- \+ *lemma* mem_map
- \+ *lemma* map_map
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* comap_inf
- \+ *lemma* comap_infi
- \+ *lemma* map_bot
- \+ *lemma* comap_top
- \+ *lemma* coe_prod
- \+ *lemma* mem_prod
- \+ *lemma* prod_mono
- \+ *lemma* prod_mono_right
- \+ *lemma* prod_mono_left
- \+ *lemma* prod_top
- \+ *lemma* top_prod
- \+ *lemma* top_prod_top
- \+ *lemma* bot_prod_bot
- \+ *lemma* gsmul_mem
- \+ *lemma* coe_range
- \+ *lemma* mem_range
- \+ *lemma* map_range
- \+ *lemma* range_top_iff_surjective
- \+ *lemma* rang_top_of_surjective
- \+ *lemma* mem_ker
- \+ *lemma* comap_ker
- \+ *lemma* eq_on_closure
- \+ *lemma* eq_of_eq_on_top
- \+ *lemma* eq_of_eq_on_dense
- \+ *lemma* gclosure_preimage_le
- \+ *lemma* map_closure
- \+ *theorem* ext'
- \+ *theorem* ext
- \+ *theorem* one_mem
- \+ *theorem* mul_mem
- \+ *theorem* inv_mem
- \+ *theorem* coe_subtype
- \+ *def* subgroup.of
- \+ *def* subgroup.to_add_subgroup
- \+ *def* subgroup.of_add_subgroup
- \+ *def* add_subgroup.to_subgroup
- \+ *def* add_subgroup.of_subgroup
- \+ *def* subgroup.add_subgroup_equiv
- \+ *def* subtype
- \+ *def* closure
- \+ *def* comap
- \+ *def* map
- \+ *def* prod
- \+ *def* prod_equiv
- \+ *def* range
- \+ *def* ker
- \+ *def* eq_locus
- \+ *def* subgroup_congr



## [2020-04-21 20:46:05](https://github.com/leanprover-community/mathlib/commit/585d77a)
chore(scripts): update nolints.txt ([#2482](https://github.com/leanprover-community/mathlib/pull/2482))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-21 17:16:35](https://github.com/leanprover-community/mathlib/commit/ffa97d0)
fix(tactic/where): remove hackery from `#where`, using Lean 3c APIs ([#2465](https://github.com/leanprover-community/mathlib/pull/2465))
We remove almost all of the hackery from `#where`, using the Lean 3c APIs exposed by @cipher1024. In doing so we add pair of library functions which make this a tad more convenient.
The last "hack" which remains is by far the most mild; we expose `lean.parser.get_current_namespace`, which creates a dummy definition in the environment in order to obtain the current namespace. Of course this should be replaced with an exposed C++ function when the time comes (crossref with the leanprover-community/lean issue here: https://github.com/leanprover-community/lean/issues/196).
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified src/tactic/where.lean
- \- *def* inflate

Created test/where.lean




## [2020-04-21 10:37:45](https://github.com/leanprover-community/mathlib/commit/533a552)
feat(tactic/hint): if hint can solve the goal, say so ([#2474](https://github.com/leanprover-community/mathlib/pull/2474))
It used to be that `hint` would print:
```
the following tactics make progress:
----
tac1
tac2
tac3
```
with the tactics listed in order of number of resulting goals. In particular, if `tac1` and `tac2` actually solve the goal, while `tac3` only makes progress, this isn't explained.
With this PR, if any of those tactics actually close the goal, we only print those tactics, with text:
```
the following tactics solve the goal:
----
tac1
tac2
```
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/hint.lean


Modified test/hint.lean




## [2020-04-21 10:37:42](https://github.com/leanprover-community/mathlib/commit/15d35b1)
feat(tactic/#simp): a user_command for #simp ([#2446](https://github.com/leanprover-community/mathlib/pull/2446))
```lean
#simp 5 - 5
```
prints `0`.
If anyone knows how to get access to local `variables` while parsing an expression, that would be awesome. Then we could write 
```lean
variable (x : ℝ)
#simp [exp_ne_zero] : deriv (λ x, (sin x) / (exp x)) x
```
as well as
```lean
#simp [exp_ne_zero] : λ x, deriv (λ x, (sin x) / (exp x)) x
```
#### Estimated changes
Modified src/tactic/basic.lean


Created src/tactic/simp_command.lean


Created test/simp_command.lean
- \+ *def* f



## [2020-04-21 07:42:40](https://github.com/leanprover-community/mathlib/commit/df84064)
fix(tactic/clear): don't use rb_map unnecessarily ([#2325](https://github.com/leanprover-community/mathlib/pull/2325))
The `clear_dependent` tactic seems to unnecessarily convert `list` back and forth to an `rb_map`, for no purpose, and this makes the internal tactic unnecessarily difficult to call.
#### Estimated changes
Modified src/tactic/clear.lean


Modified src/tactic/equiv_rw.lean


Modified test/tactics.lean




## [2020-04-21 05:12:16](https://github.com/leanprover-community/mathlib/commit/3edb6a4)
fix(category_theory/concrete): access the carrier type by the coercion ([#2473](https://github.com/leanprover-community/mathlib/pull/2473))
This should marginally reduce the pain of using concrete categories, as the underlying types of a bundled object should more uniformly described via a coercion, rather than the `.α` projection.
(There's still some separate pain involving `bundled.map`, but it has an orthogonal fix which I'm working on in another branch.)
#### Estimated changes
Modified src/category_theory/concrete_category/bundled.lean
- \+ *lemma* coe_mk

Modified src/category_theory/concrete_category/bundled_hom.lean




## [2020-04-21 01:17:00](https://github.com/leanprover-community/mathlib/commit/7a13a11)
chore(category_theory): delete two empty files ([#2472](https://github.com/leanprover-community/mathlib/pull/2472))
#### Estimated changes
Deleted src/category_theory/limits/shapes/constructions/finite_products.lean


Deleted src/category_theory/limits/shapes/constructions/sums.lean




## [2020-04-20 18:19:41](https://github.com/leanprover-community/mathlib/commit/5d0a724)
chore(docs/naming): update ([#2468](https://github.com/leanprover-community/mathlib/pull/2468))
This file has been bit-rotting.
#### Estimated changes
Modified docs/contribute/naming.md




## [2020-04-20 15:36:57](https://github.com/leanprover-community/mathlib/commit/7626763)
fix(algebra/category/*/colimits): cleaning up ([#2469](https://github.com/leanprover-community/mathlib/pull/2469))
With the passage of time, it seems some difficulties have dissolved away, and steps in the semi-automated construction of colimits in algebraic categories which previously required `rw` or even `erw`, can now be handled by `simp`. Yay!
#### Estimated changes
Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/category/Mon/colimits.lean




## [2020-04-20 15:36:55](https://github.com/leanprover-community/mathlib/commit/8adfafd)
feat(data/nat,data/int): add some modular arithmetic lemmas ([#2460](https://github.com/leanprover-community/mathlib/pull/2460))
These lemmas (a) were found useful in formalising solutions to some
olympiad problems, see
<https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Some.20olympiad.20formalisations>;
(b) seem more generally relevant than to just those particular
problems; (c) do not show up through library_search as being already
present.
#### Estimated changes
Modified src/data/int/basic.lean
- \+ *lemma* dvd_sub_of_mod_eq
- \+ *lemma* eq_zero_of_dvd_of_nat_abs_lt_nat_abs
- \+ *lemma* eq_of_mod_eq_of_nat_abs_sub_lt_nat_abs

Modified src/data/nat/basic.lean
- \+ *lemma* sub_mod_eq_zero_of_mod_eq
- \+ *lemma* eq_zero_of_dvd_of_lt



## [2020-04-20 15:36:53](https://github.com/leanprover-community/mathlib/commit/d1ba87a)
feat(category_theory/faithful): faithful.of_iso ([#2453](https://github.com/leanprover-community/mathlib/pull/2453))
A minor useful lemma, about to be abandoned on another branch.
#### Estimated changes
Modified src/category_theory/fully_faithful.lean
- \+ *lemma* faithful.of_iso
- \+ *lemma* faithful.of_comp_iso



## [2020-04-20 15:36:51](https://github.com/leanprover-community/mathlib/commit/51e03aa)
feat(data/monoid_algebra): the distrib_mul_action ([#2417](https://github.com/leanprover-community/mathlib/pull/2417))
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* comap_smul_single
- \+ *lemma* comap_smul_apply
- \+ *def* comap_has_scalar
- \+ *def* comap_mul_action
- \+ *def* comap_distrib_mul_action
- \+ *def* comap_distrib_mul_action_self

Modified src/data/monoid_algebra.lean


Modified src/group_theory/group_action.lean
- \+ *def* regular



## [2020-04-20 14:24:18](https://github.com/leanprover-community/mathlib/commit/036b038)
chore(category_theory/opposites): typo fix ([#2466](https://github.com/leanprover-community/mathlib/pull/2466))
As mentioned in [#2464](https://github.com/leanprover-community/mathlib/pull/2464).
#### Estimated changes
Modified src/category_theory/opposites.lean




## [2020-04-20 13:15:51](https://github.com/leanprover-community/mathlib/commit/59a767e)
chore(scripts): update nolints.txt ([#2467](https://github.com/leanprover-community/mathlib/pull/2467))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-20 11:18:14](https://github.com/leanprover-community/mathlib/commit/4474382)
feat(category_theory/opposites): some opposite category properties ([#2464](https://github.com/leanprover-community/mathlib/pull/2464))
Add some more basic properties relating to the opposite category.
Make sure you have:
  * [x] reviewed and applied the coding style: [coding](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/style.md), [naming](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/naming.md)
  * [x] reviewed and applied [the documentation requirements](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/doc.md)
  * [x] make sure definitions and lemmas are put in the right files
  * [x] make sure definitions and lemmas are not redundant
For reviewers: [code review check list](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/code-review.md)
If you're confused by comments on your PR like `bors r+` or `bors d+`, please see our [notes on bors](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/bors.md) for information on our merging workflow.
#### Estimated changes
Modified src/category_theory/opposites.lean
- \+ *def* unop_unop
- \+ *def* op_op_equivalence



## [2020-04-20 08:26:52](https://github.com/leanprover-community/mathlib/commit/58088cc)
fix(tactic/delta_instance): handle universe metavariables ([#2463](https://github.com/leanprover-community/mathlib/pull/2463))
#### Estimated changes
Modified src/meta/expr.lean


Modified src/tactic/core.lean


Modified test/delta_instance.lean




## [2020-04-20 07:17:35](https://github.com/leanprover-community/mathlib/commit/9b25578)
fix(category_theory/limits): avoid a rewrite in a definition ([#2458](https://github.com/leanprover-community/mathlib/pull/2458))
The proof that every equalizer of `f` and `g` is an isomorphism if `f = g` had an ugly rewrite in a definition (introduced by yours truly). This PR reformulates the proof in a cleaner way by working with two morphisms `f` and `g` and a proof of `f = g` right from the start, which is easy to specialze to the case `(f, f)`, instead of trying to reduce the `(f, g)` case to the `(f, f)` case by rewriting.
This also lets us get rid of `fork.eq_of_ι_ι`, unless someone wants to keep it, but personally I don't think that using it is ever a good idea.
#### Estimated changes
Modified src/category_theory/limits/shapes/equalizers.lean
- \- *lemma* fork.eq_of_ι_ι
- \- *lemma* cofork.eq_of_π_π
- \- *lemma* cone_parallel_pair_self_π_app_zero
- \- *lemma* cone_parallel_pair_self_X
- \- *lemma* cocone_parallel_pair_self_ι_app_one
- \- *lemma* cocone_parallel_pair_self_X
- \+ *def* id_fork
- \+ *def* is_limit_id_fork
- \+ *def* is_iso_limit_cone_parallel_pair_of_eq
- \+ *def* equalizer.ι_of_eq
- \+ *def* is_iso_limit_cone_parallel_pair_of_self
- \+ *def* is_iso_limit_cone_parallel_pair_of_epi
- \+/\- *def* equalizer.ι_of_self
- \+ *def* id_cofork
- \+ *def* is_colimit_id_cofork
- \+ *def* is_iso_colimit_cocone_parallel_pair_of_eq
- \+ *def* coequalizer.π_of_eq
- \+ *def* is_iso_colimit_cocone_parallel_pair_of_self
- \+ *def* is_iso_limit_cocone_parallel_pair_of_epi
- \+/\- *def* coequalizer.π_of_self
- \- *def* cone_parallel_pair_self
- \- *def* is_limit_cone_parallel_pair_self
- \- *def* limit_cone_parallel_pair_self_is_iso
- \- *def* limit_cone_parallel_pair_self_is_iso'
- \- *def* equalizer.ι_of_self'
- \- *def* epi_limit_cone_parallel_pair_is_iso
- \- *def* cocone_parallel_pair_self
- \- *def* is_colimit_cocone_parallel_pair_self
- \- *def* colimit_cocone_parallel_pair_self_is_iso
- \- *def* colimit_cocone_parallel_pair_self_is_iso'
- \- *def* coequalizer.π_of_self'
- \- *def* mono_limit_cocone_parallel_pair_is_iso

Modified src/category_theory/limits/shapes/kernels.lean




## [2020-04-20 01:36:42](https://github.com/leanprover-community/mathlib/commit/c0afa80)
chore(tactic/simp_result): forgot to import in tactic.basic ([#2462](https://github.com/leanprover-community/mathlib/pull/2462))
When I write a new tactic, I tend not to import it into `tactic.basic` or `tactic.interactive` while testing it and PR'ing it, to save having to recompile the whole library every time I tweak the tactic.
But then, inevitably, I forget to add the import before the review process is finished.
This imports `simp_result`, from [#2356](https://github.com/leanprover-community/mathlib/pull/2356), into `tactic.basic`.
#### Estimated changes
Modified src/tactic/basic.lean




## [2020-04-19 15:18:08](https://github.com/leanprover-community/mathlib/commit/a8edb5e)
fix(category_theory/limits): make image.map_comp a simp lemma ([#2456](https://github.com/leanprover-community/mathlib/pull/2456))
This was not possible in Lean 3.8. Many thanks to @gebner for tracking down and fixing leanprover-community/lean[#181](https://github.com/leanprover-community/mathlib/pull/181) in Lean 3.9.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean




## [2020-04-19 15:18:06](https://github.com/leanprover-community/mathlib/commit/e6aa533)
fix(category_theory/limits): remove an unnecessary axiom in has_image_map ([#2455](https://github.com/leanprover-community/mathlib/pull/2455))
I somehow missed the fact that `has_image_map.factor_map` is actually a consequence of `has_image_map.map_ι` together with the fact that `image.ι` is always a monomorphism.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* has_image_map.factor_map



## [2020-04-19 14:00:03](https://github.com/leanprover-community/mathlib/commit/aa55f8b)
feat(category_theory/eq_to_iso): missing simp lemma ([#2454](https://github.com/leanprover-community/mathlib/pull/2454))
A missing simp lemma.
#### Estimated changes
Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* eq_to_iso.inv



## [2020-04-19 14:00:01](https://github.com/leanprover-community/mathlib/commit/9801c1c)
feat(continued_fractions) add stabilisation under termination lemmas ([#2451](https://github.com/leanprover-community/mathlib/pull/2451))
- continued fractions: add lemmas for stabilisation of computations under termination and add them to default exports
- seq: make argument in seq.terminated_stable explicit
#### Estimated changes
Modified src/algebra/continued_fractions/default.lean


Created src/algebra/continued_fractions/terminated_stable.lean
- \+ *lemma* terminated_stable
- \+ *lemma* continuants_aux_stable_step_of_terminated
- \+ *lemma* continuants_aux_stable_of_terminated
- \+ *lemma* convergents'_aux_stable_step_of_terminated
- \+ *lemma* convergents'_aux_stable_of_terminated
- \+ *lemma* continuants_stable_of_terminated
- \+ *lemma* numerators_stable_of_terminated
- \+ *lemma* denominators_stable_of_terminated
- \+ *lemma* convergents_stable_of_terminated
- \+ *lemma* convergents'_stable_of_terminated

Modified src/data/seq/seq.lean
- \+/\- *lemma* terminated_stable



## [2020-04-19 13:02:57](https://github.com/leanprover-community/mathlib/commit/6054f7c)
chore(number_theory/sum_four_squares): slightly shorten proof ([#2457](https://github.com/leanprover-community/mathlib/pull/2457))
This proof was unnecessarily long due to a ring bug which has now been fixed.
#### Estimated changes
Modified src/number_theory/sum_four_squares.lean




## [2020-04-19 19:50:13+10:00](https://github.com/leanprover-community/mathlib/commit/d344310)
chore(category_theory/monoidal): some arguments that need to be made explicit in 3.8
#### Estimated changes
Modified src/category_theory/monoidal/functorial.lean




## [2020-04-19 07:58:32](https://github.com/leanprover-community/mathlib/commit/11d89a2)
chore(algebra/module): replace typeclass arguments with inferred arguments ([#2444](https://github.com/leanprover-community/mathlib/pull/2444))
This doesn't change the explicit type signature of any functions, but makes some inferable typeclass arguments implicit.
Beyond the potential performance improvement, my motivation for doing this was that in `monoid_algebra` we currently have two possible `module k (monoid_algebra k G)` instances: one directly from `monoid_algebra.module`, and another one via `restrict_scalars`. These are equal, but not definitionally. In another experimental branch, I couldn't even express the isomorphism between these module structures, because type inference was filling in the `monoid_algebra.module` instance in composition of linear maps, and then failing because one of the linear maps was actually using the other module structure...
This change fixes this.
#### Estimated changes
Modified src/algebra/module.lean
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* to_add_monoid_hom_coe
- \+/\- *lemma* comp_apply
- \+/\- *lemma* id_apply
- \+/\- *lemma* subtype_eq_val
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* ext'
- \+/\- *theorem* mem_coe
- \+/\- *def* to_add_monoid_hom
- \+/\- *def* comp
- \+/\- *def* id

Modified src/linear_algebra/basic.lean
- \+/\- *lemma* ext
- \+/\- *lemma* refl_apply
- \+/\- *lemma* prod_symm
- \+/\- *lemma* prod_apply
- \+/\- *lemma* coe_prod
- \+/\- *lemma* skew_prod_apply
- \+/\- *lemma* skew_prod_symm_apply
- \+/\- *lemma* eq_bot_of_equiv
- \+/\- *theorem* coe_apply
- \+/\- *theorem* trans_apply
- \+/\- *theorem* apply_symm_apply
- \+/\- *theorem* symm_apply_apply
- \+/\- *theorem* map_add
- \+/\- *theorem* map_zero
- \+/\- *theorem* map_neg
- \+/\- *theorem* map_sub
- \+/\- *theorem* map_smul
- \+/\- *theorem* map_eq_zero_iff
- \+/\- *theorem* map_ne_zero_iff
- \+/\- *theorem* symm_symm
- \+/\- *theorem* symm_symm_apply
- \+/\- *theorem* of_bijective_apply
- \+/\- *theorem* of_linear_apply
- \+/\- *theorem* of_linear_symm_apply
- \+/\- *theorem* of_top_apply
- \+/\- *theorem* of_top_symm_apply
- \+/\- *def* refl
- \+/\- *def* symm
- \+/\- *def* trans
- \+/\- *def* to_add_equiv
- \+/\- *def* of_linear
- \+/\- *def* of_top



## [2020-04-19 01:55:09](https://github.com/leanprover-community/mathlib/commit/0ceac44)
feat(data/nat/prime) factors of a prime number is the list [p] ([#2452](https://github.com/leanprover-community/mathlib/pull/2452))
The factors of a prime number are [p].
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* factors_prime



## [2020-04-18 23:47:08](https://github.com/leanprover-community/mathlib/commit/99245b3)
chore(*): switch to lean 3.9.0 ([#2449](https://github.com/leanprover-community/mathlib/pull/2449))
It's been too long since the last Lean release.
#### Estimated changes
Modified leanpkg.toml


Modified src/data/array/lemmas.lean
- \+/\- *theorem* read_map
- \- *theorem* read_foreach_aux

Modified src/meta/expr.lean




## [2020-04-18 23:47:06](https://github.com/leanprover-community/mathlib/commit/d76a882)
feat(category_theory/limits/over): over category has connected limits ([#2438](https://github.com/leanprover-community/mathlib/pull/2438))
Show that the forgetful functor from the over category creates connected limits.
The key consequence of this is that the over category has equalizers, which we will use to show that it has all (finite) limits if the base category does.
I've also moved the connected category examples into `category_theory/connected.lean`.
Also I removed the proof of
`instance {B : C} [has_pullbacks.{v} C] : has_pullbacks.{v} (over B)`
which I wrote and semorrison massively improved, as the new instances generalise it. 
I also added a `reassoc` for `is_limit.fac`, which simplified one of the proofs I had.
#### Estimated changes
Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/comma.lean


Modified src/category_theory/connected.lean


Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/limits.lean


Modified src/category_theory/limits/over.lean
- \+ *lemma* raised_cone_lowers_to_original
- \+ *def* nat_trans_in_over
- \+ *def* raise_cone
- \+ *def* raised_cone_is_limit



## [2020-04-18 21:59:03](https://github.com/leanprover-community/mathlib/commit/8ec447d)
fix(*): remove `@[nolint simp_nf]` ([#2450](https://github.com/leanprover-community/mathlib/pull/2450))
This removes a couple more nolints:
 - `coe_units_equiv_ne_zero` doesn't cause any problems anymore
 - `coe_mk` is redundant
 - `mk_eq_div` was not in simp-normal form (previously the linter timed out instead of reporting it as an error)
 - `factor_set.coe_add` is redundant
#### Estimated changes
Modified src/data/equiv/ring.lean


Modified src/data/real/nnreal.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/unique_factorization_domain.lean




## [2020-04-18 17:48:38](https://github.com/leanprover-community/mathlib/commit/5107c2b)
fix(docs/extra/calc.md): remove extra space ([#2448](https://github.com/leanprover-community/mathlib/pull/2448))
This was breaking the rendered doc at https://leanprover-community.github.io/mathlib_docs/calc.html#using-more-than-one-operator
#### Estimated changes
Modified docs/extras/calc.md




## [2020-04-18 17:48:36](https://github.com/leanprover-community/mathlib/commit/16552e6)
fix(group_theory/submonoid): looping simp lemma ([#2447](https://github.com/leanprover-community/mathlib/pull/2447))
Removes a `@[nolint simp_nf]`.  I have no idea why I didn't notice this earlier, but `coe_coe` loops due to `coe_sort_coe_base` since `submonoid` doesn't have it's own `has_coe_to_sort` instance.
#### Estimated changes
Modified src/group_theory/submonoid.lean




## [2020-04-18 15:15:21](https://github.com/leanprover-community/mathlib/commit/4e87223)
feat(tactic/transport): transport structures across equivalences ([#2251](https://github.com/leanprover-community/mathlib/pull/2251))
~~Blocked by [#2246](https://github.com/leanprover-community/mathlib/pull/2246).~~
~~Blocked on [#2319](https://github.com/leanprover-community/mathlib/pull/2319) and [#2334](https://github.com/leanprover-community/mathlib/pull/2334), which both fix lower tactic layers used by `transport`.~~
From the doc-string:
---
Given a goal `⊢ S β` for some parametrized structure type `S`,
`transport` will look for a hypothesis `s : S α` and an equivalence `e : α ≃ β`,
and attempt to close the goal by transporting `s` across the equivalence `e`.
```lean
example {α : Type} [ring α] {β : Type} (e : α ≃ β) : ring β :=
by transport.
```
You can specify the object to transport using `transport s`,
and the equivalence to transport across using `transport s using e`.
---
You can just as easily transport a [`semilattice_sup_top`](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/lattice.20with.20antiautomorphism) or a `lie_ring`.
In the `test/transport.lean` file we transport `semiring` from `nat` to `mynat`, and verify that it's possible to do simple things with the transported structure.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *theorem* apply_eq_iff_eq_symm_apply

Modified src/tactic/core.lean


Created src/tactic/transport.lean


Modified test/equiv_rw.lean
- \+/\- *def* monoid.map

Created test/transport/basic.lean
- \+ *lemma* mynat_equiv_apply_zero
- \+ *lemma* mynat_equiv_apply_succ
- \+ *lemma* mynat_equiv_symm_apply_zero
- \+ *lemma* mynat_equiv_symm_apply_succ
- \+ *lemma* mynat_add_def
- \+ *lemma* mynat_zero_def
- \+ *lemma* mynat_one_def
- \+ *lemma* mynat_mul_def
- \+ *def* semiring.map
- \+ *def* sup_top.map
- \+ *def* lie_ring.map
- \+ *def* mynat_equiv



## [2020-04-18 12:23:55](https://github.com/leanprover-community/mathlib/commit/ffb99a3)
chore(algebra/group/type_tags): add `additive.to_mul` etc ([#2363](https://github.com/leanprover-community/mathlib/pull/2363))
Don't make `additive` and `multiplicative` irreducible (yet?) because
it breaks compilation here and there.
Also prove that homomorphisms from `ℕ`, `ℤ` and their `multiplicative`
versions are defined by the image of `1`.
#### Estimated changes
Modified src/algebra/group/type_tags.lean
- \+ *lemma* of_mul_inj
- \+ *lemma* to_mul_inj
- \+ *lemma* of_add_inj
- \+ *lemma* to_add_inj
- \+ *lemma* to_add_of_add
- \+ *lemma* of_add_to_add
- \+ *lemma* to_mul_of_mul
- \+ *lemma* of_mul_to_mul
- \+ *lemma* of_add_add
- \+ *lemma* to_add_mul
- \+ *lemma* of_mul_mul
- \+ *lemma* to_mul_add
- \+ *lemma* of_mul_one
- \+ *lemma* to_mul_zero
- \+ *lemma* of_add_zero
- \+ *lemma* to_add_one
- \+ *lemma* of_mul_inv
- \+ *lemma* to_mul_neg
- \+ *lemma* of_add_neg
- \+ *lemma* to_add_inv
- \+ *def* additive.of_mul
- \+ *def* additive.to_mul
- \+ *def* multiplicative.of_add
- \+ *def* multiplicative.to_add

Modified src/algebra/group_power.lean
- \+ *lemma* pow_of_add
- \+ *lemma* gpow_of_add
- \+ *def* powers_hom
- \+ *def* gpowers_hom
- \+ *def* multiples_hom
- \+ *def* gmultiples_hom

Modified src/group_theory/submonoid.lean
- \+ *lemma* closure_singleton_eq
- \+/\- *lemma* mem_closure_singleton
- \+/\- *lemma* smul_mem



## [2020-04-18 10:03:42](https://github.com/leanprover-community/mathlib/commit/8b21231)
chore(data/mv_polynomial): adding a comment about a T50000 regression ([#2442](https://github.com/leanprover-community/mathlib/pull/2442))
#### Estimated changes
Modified src/data/mv_polynomial.lean




## [2020-04-18 07:33:17](https://github.com/leanprover-community/mathlib/commit/a530a81)
refactor(data/nat/fib): simplify proof of fib_succ_succ ([#2443](https://github.com/leanprover-community/mathlib/pull/2443))
By tweaking some of the lemmas, I managed to shorten `fib_succ_succ` from 7 complicated lines to a single call to `simp`.
An alternative expression would be:
```lean
unfold fib,
repeat { rw fib_aux_stream_succ },
unfold fib_aux_step,
```
I can change to that if you think the `simp` is too pithy.
#### Estimated changes
Modified src/data/nat/fib.lean




## [2020-04-18 04:12:58](https://github.com/leanprover-community/mathlib/commit/1ef989f)
docs(install/*): put extra emphasis ([#2439](https://github.com/leanprover-community/mathlib/pull/2439))
Put extra emphasis on creating and working with projects
If people like this change I'll also make it on the other pages.
#### Estimated changes
Modified docs/install/debian.md


Modified docs/install/debian_details.md


Modified docs/install/linux.md


Modified docs/install/macos.md


Modified docs/install/windows.md




## [2020-04-18 00:48:02](https://github.com/leanprover-community/mathlib/commit/6b09575)
feat(tactic/lint): lint for missing has_coe_to_fun instances ([#2437](https://github.com/leanprover-community/mathlib/pull/2437))
Enforces the library note "function coercion":
https://github.com/leanprover-community/mathlib/blob/715be9f7466f30f1d4cbff4e870530af43767fba/src/logic/basic.lean#L69-L94
See [#2434](https://github.com/leanprover-community/mathlib/pull/2434) for a recent PR where this issue popped up.
#### Estimated changes
Modified src/algebraic_geometry/presheafed_space.lean
- \+ *lemma* id_coe_fn

Modified src/tactic/abel.lean


Modified src/tactic/lint/default.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/ring.lean


Created test/lint_coe_to_fun.lean




## [2020-04-17 21:00:09](https://github.com/leanprover-community/mathlib/commit/24d464c)
fix(github/workflows): ignore new bors branch ([#2441](https://github.com/leanprover-community/mathlib/pull/2441))
Two hours ago, bors renamed the temporary branches. https://github.com/bors-ng/bors-ng/pull/933  :roll_eyes:
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-04-17 19:48:56](https://github.com/leanprover-community/mathlib/commit/da29275)
chore(scripts): update nolints.txt ([#2440](https://github.com/leanprover-community/mathlib/pull/2440))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-17 16:30:37](https://github.com/leanprover-community/mathlib/commit/64f6903)
chore(*): migrate `nat/int/rat.eq_cast` to bundled homs ([#2427](https://github.com/leanprover-community/mathlib/pull/2427))
Now it is `ring_hom.eq_*_cast`, `ring_hom.map_*_cast`, `add_monoid_hom.eq_int/nat_cast`.
Also turn `complex.of_real` into a `ring_hom`.
#### Estimated changes
Modified src/algebra/group_power.lean


Modified src/data/complex/basic.lean
- \+/\- *lemma* of_real_eq_coe
- \+/\- *def* of_real

Modified src/data/int/basic.lean
- \+ *theorem* add_monoid_hom.eq_int_cast
- \+ *theorem* int.cast_id
- \- *theorem* eq_cast
- \- *theorem* cast_id
- \+ *def* of_nat_hom

Modified src/data/nat/cast.lean
- \+ *lemma* add_monoid_hom.eq_nat_cast
- \+ *lemma* ring_hom.eq_nat_cast
- \+/\- *lemma* ring_hom.map_nat_cast
- \+ *theorem* nat.cast_id
- \- *theorem* eq_cast
- \- *theorem* eq_cast'
- \- *theorem* cast_id

Modified src/data/polynomial.lean


Modified src/data/rat/cast.lean
- \+ *lemma* ring_hom.eq_rat_cast
- \+ *lemma* ring_hom.map_rat_cast
- \- *theorem* eq_cast_of_ne_zero
- \- *theorem* eq_cast

Modified src/data/real/basic.lean
- \+/\- *def* of_rat
- \+/\- *def* mk



## [2020-04-17 13:44:40](https://github.com/leanprover-community/mathlib/commit/855e70b)
feat(data/nat): Results about nat.choose ([#2421](https://github.com/leanprover-community/mathlib/pull/2421))
A convenience lemma for symmetry of choose and inequalities about choose.
More results from my combinatorics project.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* choose_symm_of_eq_add
- \+ *lemma* choose_symm_add

Modified src/data/nat/choose.lean
- \+ *lemma* choose_le_succ_of_lt_half_left
- \+ *lemma* choose_le_middle



## [2020-04-17 09:39:01](https://github.com/leanprover-community/mathlib/commit/0bc15f8)
feat(analysis/analytic/composition): the composition of analytic functions is analytic ([#2399](https://github.com/leanprover-community/mathlib/pull/2399))
The composition of analytic functions is analytic. 
The argument is the following. Assume `g z = ∑ qₙ (z, ..., z)` and `f y = ∑ pₖ (y, ..., y)`. Then
```
g (f y) = ∑ qₙ (∑ pₖ (y, ..., y), ..., ∑ pₖ (y, ..., y))
= ∑ qₙ (p_{i₁} (y, ..., y), ..., p_{iₙ} (y, ..., y)).
```
For each `n` and `i₁, ..., iₙ`, define a `i₁ + ... + iₙ` multilinear function mapping
`(y₀, ..., y_{i₁ + ... + iₙ - 1})` to
`qₙ (p_{i₁} (y₀, ..., y_{i₁-1}), p_{i₂} (y_{i₁}, ..., y_{i₁ + i₂ - 1}), ..., p_{iₙ} (....)))`.
Then `g ∘ f` is obtained by summing all these multilinear functions.
The main difficulty is to make sense of this (especially the ellipsis) in a way that Lean understands. For this, this PR uses a structure containing a decomposition of `n` as a sum `i_1 + ... i_k` (called `composition`), and a whole interface around it developed in [#2398](https://github.com/leanprover-community/mathlib/pull/2398). Once it is available, the main proof is not too hard.
This supersedes [#2328](https://github.com/leanprover-community/mathlib/pull/2328), after a new start implementing compositions using sequences.
#### Estimated changes
Created src/analysis/analytic/composition.lean
- \+ *lemma* apply_composition_update
- \+ *lemma* comp_along_composition_multilinear_bound
- \+ *lemma* comp_along_composition_norm
- \+ *lemma* comp_along_composition_nnnorm
- \+ *lemma* mem_comp_partial_sum_source_iff
- \+ *lemma* comp_change_of_variables_length
- \+ *lemma* comp_change_of_variables_blocks_fun
- \+ *lemma* comp_partial_sum_target_subset_image_comp_partial_sum_source
- \+ *lemma* mem_comp_partial_sum_target_iff
- \+ *lemma* comp_partial_sum_target_tendsto_at_top
- \+ *lemma* comp_partial_sum
- \+ *theorem* comp_summable_nnreal
- \+ *theorem* le_comp_radius_of_summable
- \+ *theorem* has_fpower_series_at.comp
- \+ *theorem* analytic_at.comp
- \+ *def* apply_composition
- \+ *def* comp_along_composition_multilinear
- \+ *def* comp_along_composition
- \+ *def* comp_partial_sum_source
- \+ *def* comp_change_of_variables
- \+ *def* comp_partial_sum_target_set
- \+ *def* comp_partial_sum_target

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnnorm_sum_le

Modified src/data/real/ennreal.lean
- \+ *lemma* pow_le_pow

Modified src/data/set/function.lean
- \+ *lemma* update_comp_eq_of_not_mem_range
- \+ *lemma* update_comp_eq_of_injective

Modified src/order/filter/basic.lean
- \+ *lemma* monotone.tendsto_at_top_finset



## [2020-04-17 06:57:05](https://github.com/leanprover-community/mathlib/commit/715be9f)
chore(scripts): update nolints.txt ([#2436](https://github.com/leanprover-community/mathlib/pull/2436))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-17 05:53:51](https://github.com/leanprover-community/mathlib/commit/0567b7f)
feat(category_theory/limits): strong epimorphisms and strong epi-mono factorizations ([#2433](https://github.com/leanprover-community/mathlib/pull/2433))
This PR contains the changes I mentioned in [#2374](https://github.com/leanprover-community/mathlib/pull/2374). It contains:
* the definition of a lift of a commutative square
* the definition of a strong epimorphism
* a proof that every regular epimorphism is strong
* the definition of a strong epi-mono factorization
* the class `has_strong_epi_images`
* the construction `has_strong_epi_images` -> `has_image_maps`
* a small number of changes which should have been part of [#2423](https://github.com/leanprover-community/mathlib/pull/2423)
#### Estimated changes
Modified src/category_theory/comma.lean
- \+ *lemma* w
- \+ *lemma* lift.fac_left
- \+ *lemma* lift.fac_right
- \+ *lemma* lift_mk'_left
- \+ *lemma* lift_mk'_right

Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* is_image.fac_lift
- \+ *lemma* image.fac_lift
- \+ *def* strong_epi_mono_factorisation.to_mono_is_image

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* cokernel_cofork.is_colimit.desc'
- \- *def* cokernel_cofork.is_limit.desc'

Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *def* regular_mono.lift'
- \+ *def* normal_mono.lift'
- \+ *def* regular_epi.desc'
- \+ *def* normal_epi.desc'

Created src/category_theory/limits/shapes/strong_epi.lean
- \+ *def* strong_epi_comp
- \+ *def* strong_epi_of_strong_epi
- \+ *def* mono_strong_epi_is_iso



## [2020-04-17 04:14:01](https://github.com/leanprover-community/mathlib/commit/f347147)
feat(category_theory):  creation of limits and reflection of isomorphisms ([#2426](https://github.com/leanprover-community/mathlib/pull/2426))
Define creation of limits and reflection of isomorphisms.
Part 2 of a sequence of PRs aiming to resolve my TODO [here](https://github.com/leanprover-community/mathlib/blob/cf89963e14cf535783cefba471247ae4470fa8c3/src/category_theory/limits/over.lean#L143) - that the forgetful functor from the over category creates connected limits.
Remaining:
- [x] Add an instance or def which gives that if `F` creates limits and `K ⋙ F` `has_limit` then `has_limit K` as well.
- [x] Move the forget creates limits proof to limits/over, and remove the existing proof since this one is strictly stronger - make sure to keep the statement there though using the previous point.
- [x] Add more docstrings
Probably relevant to @semorrison and @TwoFX.
#### Estimated changes
Modified src/category_theory/adjunction/limits.lean
- \+/\- *def* functoriality_unit
- \+/\- *def* functoriality_counit
- \+/\- *def* functoriality_unit'
- \+/\- *def* functoriality_counit'

Modified src/category_theory/limits/cones.lean
- \- *lemma* map_cone_inv_X
- \+/\- *def* map_cone
- \+/\- *def* map_cocone
- \+/\- *def* map_cone_morphism
- \+/\- *def* map_cocone_morphism
- \+ *def* map_cone_map_cone_inv

Created src/category_theory/limits/creates.lean
- \+ *def* lift_limit
- \+ *def* lifted_limit_maps_to_original
- \+ *def* lifted_limit_is_limit
- \+ *def* has_limit_of_created
- \+ *def* lift_colimit
- \+ *def* lifted_colimit_maps_to_original
- \+ *def* lifted_colimit_is_colimit
- \+ *def* has_colimit_of_created
- \+ *def* creates_limit_of_reflects_iso
- \+ *def* creates_colimit_of_reflects_iso
- \+ *def* lifts_to_limit_of_creates
- \+ *def* lifts_to_colimit_of_creates
- \+ *def* id_lifts_cone
- \+ *def* id_lifts_cocone

Modified src/category_theory/limits/limits.lean
- \+ *def* map_cone_equiv

Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/monad/algebra.lean
- \+ *def* algebra_iso_of_iso

Modified src/category_theory/monad/limits.lean
- \+ *def* new_cone
- \+/\- *def* cone_point
- \+ *def* lifted_cone
- \+ *def* lifted_cone_is_limit
- \+ *def* has_limit_of_comp_forget_has_limit
- \+ *def* new_cocone
- \+/\- *def* lambda
- \+ *def* lifted_cocone
- \+ *def* lifted_cocone_is_colimit
- \- *def* c
- \- *def* forget_creates_limits

Created src/category_theory/reflect_isomorphisms.lean
- \+ *def* is_iso_of_reflects_iso
- \+ *def* cone_iso_of_hom_iso
- \+ *def* cocone_iso_of_hom_iso



## [2020-04-17 02:42:19](https://github.com/leanprover-community/mathlib/commit/0d3e546)
chore(scripts): update nolints.txt ([#2435](https://github.com/leanprover-community/mathlib/pull/2435))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-17 01:11:58](https://github.com/leanprover-community/mathlib/commit/d2db3e8)
chore(algebra/lie_algebra): add function coercion for morphisms ([#2434](https://github.com/leanprover-community/mathlib/pull/2434))
In fact three different changes are being made here:
 1. Adding direct function coercion for `lie_algebra.morphism`, allowing us to tidy up `map_lie` and increase simp scope
 2. Providing a zero element for `lie_subalgebra`, thus allowing removal of a `has_inhabited_instance` exception in nolints.txt
 3. Providing a zero element for `lie_submodule`, thus allowing removal of a `has_inhabited_instance` exception in nolints.txt
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+/\- *lemma* map_lie
- \- *lemma* map_lie'



## [2020-04-16 14:03:47](https://github.com/leanprover-community/mathlib/commit/c3d943e)
feat(computability): strong reducibility and degrees ([#1203](https://github.com/leanprover-community/mathlib/pull/1203))
#### Estimated changes
Modified docs/references.bib


Modified src/computability/halting.lean


Modified src/computability/partrec.lean


Modified src/computability/partrec_code.lean
- \+ *theorem* injective_const
- \+ *theorem* injective_curry
- \+ *theorem* smn

Modified src/computability/primrec.lean


Created src/computability/reduce.lean
- \+ *theorem* many_one_reducible.mk
- \+ *theorem* many_one_reducible_refl
- \+ *theorem* many_one_reducible.trans
- \+ *theorem* reflexive_many_one_reducible
- \+ *theorem* transitive_many_one_reducible
- \+ *theorem* one_one_reducible.mk
- \+ *theorem* one_one_reducible_refl
- \+ *theorem* one_one_reducible.trans
- \+ *theorem* one_one_reducible.to_many_one
- \+ *theorem* one_one_reducible.of_equiv
- \+ *theorem* one_one_reducible.of_equiv_symm
- \+ *theorem* reflexive_one_one_reducible
- \+ *theorem* transitive_one_one_reducible
- \+ *theorem* computable_of_many_one_reducible
- \+ *theorem* computable_of_one_one_reducible
- \+ *theorem* many_one_equiv_refl
- \+ *theorem* many_one_equiv.symm
- \+ *theorem* many_one_equiv.trans
- \+ *theorem* equivalence_of_many_one_equiv
- \+ *theorem* one_one_equiv_refl
- \+ *theorem* one_one_equiv.symm
- \+ *theorem* one_one_equiv.trans
- \+ *theorem* equivalence_of_one_one_equiv
- \+ *theorem* one_one_equiv.to_many_one
- \+ *theorem* equiv.computable.symm
- \+ *theorem* equiv.computable.trans
- \+ *theorem* computable.eqv
- \+ *theorem* computable.equiv₂
- \+ *theorem* one_one_equiv.of_equiv
- \+ *theorem* many_one_equiv.of_equiv
- \+ *theorem* many_one_equiv.le_congr_left
- \+ *theorem* many_one_equiv.le_congr_right
- \+ *theorem* one_one_equiv.le_congr_left
- \+ *theorem* one_one_equiv.le_congr_right
- \+ *theorem* many_one_equiv.congr_left
- \+ *theorem* many_one_equiv.congr_right
- \+ *theorem* one_one_equiv.congr_left
- \+ *theorem* one_one_equiv.congr_right
- \+ *theorem* one_one_reducible.disjoin_left
- \+ *theorem* one_one_reducible.disjoin_right
- \+ *theorem* disjoin_many_one_reducible
- \+ *theorem* disjoin_le
- \+ *theorem* many_one_degree.of_le_of
- \+ *theorem* many_one_degree.of_le_of'
- \+ *theorem* many_one_degree.le_refl
- \+ *theorem* many_one_degree.le_antisymm
- \+ *theorem* many_one_degree.le_trans
- \+ *theorem* many_one_degree.le_comap_left
- \+ *theorem* many_one_degree.le_comap_right
- \+ *theorem* many_one_degree.add_le
- \+ *theorem* many_one_degree.le_add_left
- \+ *theorem* many_one_degree.le_add_right
- \+ *theorem* many_one_degree.add_le'
- \+ *theorem* many_one_degree.le_add_left'
- \+ *theorem* many_one_degree.le_add_right'
- \+ *def* many_one_reducible
- \+ *def* one_one_reducible
- \+ *def* many_one_equiv
- \+ *def* one_one_equiv
- \+ *def* many_one_equiv_setoid
- \+ *def* equiv.computable
- \+ *def* many_one_degree
- \+ *def* many_one_degree.le
- \+ *def* many_one_degree.of
- \+ *def* many_one_degree.comap
- \+ *def* many_one_degree.add



## [2020-04-16 12:26:28](https://github.com/leanprover-community/mathlib/commit/a113d6e)
chore(scripts): update nolints.txt ([#2432](https://github.com/leanprover-community/mathlib/pull/2432))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-16 11:10:10](https://github.com/leanprover-community/mathlib/commit/846cbab)
feat(analysis/calculus): let simp compute derivatives ([#2422](https://github.com/leanprover-community/mathlib/pull/2422))
After this PR:
```lean
example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }
```
Excerpts from the docstrings:
The simplifier is set up to prove automatically that some functions are differentiable, or differentiable at a point (but not differentiable on a set or within a set at a point, as checking automatically that the good domains are mapped one to the other when using composition is not something the simplifier can easily do). This means that one can write
`example (x : ℝ) : differentiable ℝ (λ x, sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : differentiable_at ℝ (λ x, exp x / (1 + sin x)) x :=
by simp [h]
```
The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general complicated multidimensional linear maps), but it will compute one-dimensional derivatives.
To make sure that the simplifier can prove automatically that functions are differentiable, we tag many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable functions is differentiable, as well as their product, their cartesian product, and so on. A notable exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are differentiable, then their composition also is: `simp` would always be able to match this lemma, by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`), we add a lemma that if `f` is differentiable then so is `(λ x, exp (f x))`. This means adding some boilerplate lemmas, but these can also be useful in their own right. 
Tests for this ability of the simplifier (with more examples) are provided in `tests/differentiable.lean`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_id''
- \+/\- *lemma* deriv_add
- \+/\- *lemma* deriv_sub
- \+/\- *lemma* deriv_mul
- \+ *lemma* has_deriv_within_at.inv
- \+ *lemma* has_deriv_at.inv
- \+ *lemma* differentiable_within_at.inv
- \+ *lemma* differentiable_at.inv
- \+ *lemma* differentiable_on.inv
- \+ *lemma* differentiable.inv
- \+ *lemma* deriv_within_inv'
- \+ *lemma* deriv_inv'
- \+/\- *lemma* differentiable_at.div
- \+/\- *lemma* differentiable.div
- \+/\- *lemma* deriv_div
- \+ *lemma* has_deriv_within_at.pow
- \+ *lemma* has_deriv_at.pow
- \+ *lemma* differentiable_within_at.pow
- \+ *lemma* differentiable_at.pow
- \+ *lemma* differentiable_on.pow
- \+ *lemma* differentiable.pow
- \+ *lemma* deriv_within_pow'
- \+ *lemma* deriv_pow''
- \+ *theorem* has_deriv_at_id'

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* differentiable_at_id
- \+ *lemma* differentiable_at_id'
- \+/\- *lemma* differentiable_id
- \+ *lemma* differentiable_id'
- \+/\- *lemma* differentiable_at_const
- \+/\- *lemma* differentiable_const
- \+/\- *lemma* differentiable_at.fst
- \+/\- *lemma* differentiable.fst
- \+/\- *lemma* differentiable_at.snd
- \+/\- *lemma* differentiable.snd
- \+/\- *lemma* differentiable_at.add
- \+/\- *lemma* differentiable.add
- \+/\- *lemma* differentiable_at.neg
- \+/\- *lemma* differentiable.neg
- \+/\- *lemma* differentiable_at.sub
- \+/\- *lemma* differentiable.sub
- \+/\- *lemma* differentiable_at.smul
- \+/\- *lemma* differentiable.smul
- \+/\- *lemma* differentiable_at.mul
- \+/\- *lemma* differentiable.mul
- \+/\- *theorem* differentiable_at.prod_map

Modified src/analysis/complex/exponential.lean
- \+ *lemma* differentiable_at_exp
- \+/\- *lemma* has_deriv_at.cexp
- \+/\- *lemma* has_deriv_within_at.cexp
- \+ *lemma* differentiable_within_at.cexp
- \+ *lemma* differentiable_at.cexp
- \+ *lemma* differentiable_on.cexp
- \+ *lemma* differentiable.cexp
- \+ *lemma* deriv_within_cexp
- \+ *lemma* deriv_cexp
- \+ *lemma* differentiable_at_sin
- \+ *lemma* differentiable_at_cos
- \+ *lemma* differentiable_at_sinh
- \+ *lemma* differentiable_at_cosh
- \+ *lemma* has_deriv_at.ccos
- \+ *lemma* has_deriv_within_at.ccos
- \+ *lemma* differentiable_within_at.ccos
- \+ *lemma* differentiable_at.ccos
- \+ *lemma* differentiable_on.ccos
- \+ *lemma* differentiable.ccos
- \+ *lemma* deriv_within_ccos
- \+ *lemma* deriv_ccos
- \+ *lemma* has_deriv_at.csin
- \+ *lemma* has_deriv_within_at.csin
- \+ *lemma* differentiable_within_at.csin
- \+ *lemma* differentiable_at.csin
- \+ *lemma* differentiable_on.csin
- \+ *lemma* differentiable.csin
- \+ *lemma* deriv_within_csin
- \+ *lemma* deriv_csin
- \+ *lemma* has_deriv_at.ccosh
- \+ *lemma* has_deriv_within_at.ccosh
- \+ *lemma* differentiable_within_at.ccosh
- \+ *lemma* differentiable_at.ccosh
- \+ *lemma* differentiable_on.ccosh
- \+ *lemma* differentiable.ccosh
- \+ *lemma* deriv_within_ccosh
- \+ *lemma* deriv_ccosh
- \+ *lemma* has_deriv_at.csinh
- \+ *lemma* has_deriv_within_at.csinh
- \+ *lemma* differentiable_within_at.csinh
- \+ *lemma* differentiable_at.csinh
- \+ *lemma* differentiable_on.csinh
- \+ *lemma* differentiable.csinh
- \+ *lemma* deriv_within_csinh
- \+ *lemma* deriv_csinh
- \+ *lemma* has_deriv_at.exp
- \+ *lemma* has_deriv_within_at.exp
- \+ *lemma* differentiable_within_at.exp
- \+ *lemma* differentiable_at.exp
- \+ *lemma* differentiable_on.exp
- \+ *lemma* differentiable.exp
- \+ *lemma* deriv_within_exp
- \+ *lemma* deriv_exp
- \+ *lemma* has_deriv_at.cos
- \+ *lemma* has_deriv_within_at.cos
- \+ *lemma* differentiable_within_at.cos
- \+ *lemma* differentiable_at.cos
- \+ *lemma* differentiable_on.cos
- \+ *lemma* differentiable.cos
- \+ *lemma* deriv_within_cos
- \+ *lemma* deriv_cos
- \+ *lemma* has_deriv_at.sin
- \+ *lemma* has_deriv_within_at.sin
- \+ *lemma* differentiable_within_at.sin
- \+ *lemma* differentiable_at.sin
- \+ *lemma* differentiable_on.sin
- \+ *lemma* differentiable.sin
- \+ *lemma* deriv_within_sin
- \+ *lemma* deriv_sin
- \+ *lemma* has_deriv_at.cosh
- \+ *lemma* has_deriv_within_at.cosh
- \+ *lemma* differentiable_within_at.cosh
- \+ *lemma* differentiable_at.cosh
- \+ *lemma* differentiable_on.cosh
- \+ *lemma* differentiable.cosh
- \+ *lemma* deriv_within_cosh
- \+ *lemma* deriv_cosh
- \+ *lemma* has_deriv_at.sinh
- \+ *lemma* has_deriv_within_at.sinh
- \+ *lemma* differentiable_within_at.sinh
- \+ *lemma* differentiable_at.sinh
- \+ *lemma* differentiable_on.sinh
- \+ *lemma* differentiable.sinh
- \+ *lemma* deriv_within_sinh
- \+ *lemma* deriv_sinh

Modified src/analysis/convex/specific_functions.lean


Created test/differentiable.lean




## [2020-04-16 11:10:08](https://github.com/leanprover-community/mathlib/commit/ec80061)
refactor(analysis/asymptotics): make is_o irreducible ([#2416](https://github.com/leanprover-community/mathlib/pull/2416))
`is_o` is currently not irreducible. Since it is a complicated type, Lean can have trouble checking if two types with `is_o` are defeq or not, leading to timeouts as described in https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/undergraduate.20calculus/near/193776607
This PR makes `is_o` irreducible.
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *lemma* is_O_with_iff
- \+ *lemma* is_O_with.of_bound
- \+ *lemma* is_O_iff_is_O_with
- \+ *lemma* is_O_iff
- \+ *lemma* is_O.of_bound
- \+ *lemma* is_o_iff_forall_is_O_with
- \+ *lemma* is_o_iff
- \+ *lemma* is_o.def

Modified src/analysis/calculus/extend_deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean




## [2020-04-16 08:33:27](https://github.com/leanprover-community/mathlib/commit/5fd4afc)
refactor(tactic/norm_cast): simplified attributes and numeral support ([#2407](https://github.com/leanprover-community/mathlib/pull/2407))
This is @pnmadelaine's work, I'm just updating it to work with current mathlib.
New and improved version of `norm_cast` as described in the paper "normalizing casts and coercions": https://arxiv.org/abs/2001.10594
The main new user-facing feature are the simplified attributes.  There is now only the `@[norm_cast]` attribute which subsumes the previous `norm_cast`, `elim_cast`, `squash_cast`, and `move_cast` attributes.
There is a new `set_option trace.norm_cast true` option to enable debugging output.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_eq_zero
- \+/\- *theorem* cast_ne_zero

Modified src/algebra/continued_fractions/basic.lean


Modified src/algebra/field_power.lean
- \+/\- *theorem* rat.cast_fpow

Modified src/algebra/group_power.lean
- \+/\- *theorem* nat.cast_pow
- \+/\- *theorem* int.coe_nat_pow
- \+/\- *theorem* int.cast_pow

Modified src/algebra/module.lean
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_mk
- \+/\- *lemma* coe_sub

Modified src/algebra/ring.lean
- \+/\- *lemma* coe_monoid_hom
- \+/\- *lemma* coe_add_monoid_hom
- \+ *lemma* coe_monoid_hom'
- \+ *lemma* coe_add_monoid_hom'

Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* coe_rpow

Modified src/analysis/convex/cone.lean
- \+/\- *lemma* mem_coe

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* int.norm_cast_real
- \+/\- *lemma* rat.norm_cast_real
- \+/\- *lemma* int.norm_cast_rat

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* linear_map.mk_continuous_coe
- \+/\- *lemma* linear_map.mk_continuous_of_exists_bound_coe
- \+/\- *lemma* restrict_scalars_coe_eq_coe
- \+/\- *lemma* restrict_scalars_coe_eq_coe'

Modified src/data/complex/basic.lean
- \+/\- *lemma* of_real_re
- \+/\- *lemma* of_real_im
- \+/\- *lemma* of_real_zero
- \+/\- *lemma* of_real_one
- \+/\- *lemma* of_real_add
- \+/\- *lemma* of_real_bit0
- \+/\- *lemma* of_real_bit1
- \+/\- *lemma* of_real_neg
- \+/\- *lemma* of_real_mul
- \+/\- *lemma* of_real_sub
- \+/\- *lemma* of_real_pow
- \+/\- *lemma* of_real_inv
- \+/\- *lemma* of_real_div
- \+/\- *lemma* of_real_fpow
- \+/\- *lemma* nat_cast_re
- \+/\- *lemma* nat_cast_im
- \+/\- *lemma* int_cast_re
- \+/\- *lemma* int_cast_im
- \+/\- *lemma* rat_cast_re
- \+/\- *lemma* rat_cast_im
- \+/\- *lemma* abs_cast_nat
- \+/\- *theorem* of_real_inj
- \+/\- *theorem* of_real_int_cast
- \+/\- *theorem* of_real_nat_cast
- \+/\- *theorem* of_real_rat_cast

Modified src/data/equiv/ring.lean
- \+/\- *lemma* coe_mul_equiv
- \+/\- *lemma* coe_add_equiv

Modified src/data/fin.lean
- \+/\- *lemma* coe_mk
- \+/\- *lemma* coe_last

Modified src/data/finset.lean
- \+/\- *lemma* coe_nonempty
- \+/\- *lemma* piecewise_coe

Modified src/data/int/basic.lean
- \+/\- *lemma* bodd_coe
- \+/\- *theorem* coe_nat_le
- \+/\- *theorem* coe_nat_lt
- \+/\- *theorem* coe_nat_inj'
- \+/\- *theorem* coe_nat_abs
- \+/\- *theorem* coe_nat_div
- \+/\- *theorem* coe_nat_dvd
- \+/\- *theorem* cast_zero
- \+/\- *theorem* cast_coe_nat
- \+/\- *theorem* cast_neg_succ_of_nat
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_sub_nat_nat
- \+/\- *theorem* cast_neg_of_nat
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_neg
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_mul
- \+/\- *theorem* coe_nat_bit0
- \+/\- *theorem* coe_nat_bit1
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_id
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs

Modified src/data/nat/cast.lean
- \+/\- *theorem* cast_zero
- \+/\- *theorem* cast_succ
- \+/\- *theorem* cast_ite
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_pred
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_id
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* abs_cast

Modified src/data/nat/enat.lean
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_add
- \+/\- *lemma* get_coe
- \+/\- *lemma* coe_get
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* coe_lt_coe

Modified src/data/nat/multiplicity.lean


Modified src/data/num/basic.lean


Modified src/data/num/bitwise.lean
- \+ *def* bits
- \+ *def* cadd

Modified src/data/num/lemmas.lean


Modified src/data/padics/padic_integers.lean
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* cast_pow

Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_div
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_inj

Modified src/data/rat/basic.lean
- \+/\- *theorem* coe_int_num
- \+/\- *theorem* coe_int_denom
- \+/\- *theorem* coe_nat_num
- \+/\- *theorem* coe_nat_denom

Modified src/data/rat/cast.lean
- \+/\- *theorem* cast_coe_int
- \+/\- *theorem* cast_coe_nat
- \+/\- *theorem* cast_zero
- \+/\- *theorem* cast_one
- \+/\- *theorem* cast_mk_of_ne_zero
- \+/\- *theorem* cast_add_of_ne_zero
- \+/\- *theorem* cast_neg
- \+/\- *theorem* cast_sub_of_ne_zero
- \+/\- *theorem* cast_mul_of_ne_zero
- \+/\- *theorem* cast_inv_of_ne_zero
- \+/\- *theorem* cast_div_of_ne_zero
- \+/\- *theorem* cast_inj
- \+/\- *theorem* cast_add
- \+/\- *theorem* cast_sub
- \+/\- *theorem* cast_mul
- \+/\- *theorem* cast_bit0
- \+/\- *theorem* cast_bit1
- \+/\- *theorem* cast_inv
- \+/\- *theorem* cast_div
- \+/\- *theorem* cast_mk
- \+/\- *theorem* cast_pow
- \+/\- *theorem* cast_nonneg
- \+/\- *theorem* cast_le
- \+/\- *theorem* cast_lt
- \+/\- *theorem* cast_id
- \+/\- *theorem* cast_min
- \+/\- *theorem* cast_max
- \+/\- *theorem* cast_abs

Modified src/data/real/ennreal.lean
- \+/\- *lemma* to_nnreal_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_eq_coe
- \+/\- *lemma* coe_le_coe
- \+/\- *lemma* coe_lt_coe
- \+/\- *lemma* coe_eq_zero
- \+/\- *lemma* zero_eq_coe
- \+/\- *lemma* coe_eq_one
- \+/\- *lemma* one_eq_coe
- \+/\- *lemma* coe_nonneg
- \+/\- *lemma* coe_pos
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_bit0
- \+/\- *lemma* coe_bit1
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_finset_sum
- \+/\- *lemma* coe_finset_prod
- \+/\- *lemma* one_le_coe_iff
- \+/\- *lemma* coe_le_one_iff
- \+/\- *lemma* coe_lt_one_iff
- \+/\- *lemma* one_lt_coe_iff
- \+/\- *lemma* coe_nat
- \+/\- *lemma* coe_nat_lt_coe_nat
- \+/\- *lemma* coe_nat_le_coe_nat
- \+/\- *lemma* coe_min
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_inv
- \+/\- *lemma* coe_inv_two
- \+/\- *lemma* coe_div

Modified src/data/real/ereal.lean


Modified src/data/real/hyperreal.lean


Modified src/data/real/nnreal.lean
- \+/\- *lemma* coe_ne_zero
- \+/\- *lemma* coe_pow
- \+/\- *lemma* coe_list_sum
- \+/\- *lemma* coe_list_prod
- \+/\- *lemma* coe_multiset_sum
- \+/\- *lemma* coe_multiset_prod
- \+/\- *lemma* coe_sum
- \+/\- *lemma* coe_prod
- \+/\- *lemma* smul_coe
- \+/\- *lemma* coe_max
- \+/\- *lemma* coe_min

Modified src/group_theory/submonoid.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* coe_prod

Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_pos_part
- \+/\- *lemma* coe_neg_part
- \+/\- *lemma* simple_func.integral_eq_integral

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_pos_part

Modified src/meta/expr.lean


Modified src/order/filter/filter_product.lean
- \+/\- *lemma* of_zero
- \+/\- *lemma* of_add
- \+/\- *lemma* of_bit0
- \+/\- *lemma* of_bit1
- \+/\- *lemma* of_neg
- \+/\- *lemma* of_sub
- \+/\- *lemma* of_one
- \+/\- *lemma* of_mul
- \+/\- *lemma* of_inv
- \+/\- *lemma* of_div

Modified src/ring_theory/algebra.lean
- \+/\- *lemma* linear_map.coe_restrict_scalars_eq_coe

Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/power_series.lean
- \+/\- *lemma* coeff_coe
- \+/\- *lemma* coe_monomial
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_one
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_mul
- \+/\- *lemma* coe_C
- \+/\- *lemma* coe_X

Modified src/set_theory/cardinal.lean
- \+/\- *theorem* nat_cast_pow
- \+/\- *theorem* nat_cast_le
- \+/\- *theorem* nat_cast_lt
- \+/\- *theorem* nat_cast_inj
- \+/\- *theorem* nat_succ

Modified src/set_theory/ordinal.lean


Modified src/tactic/core.lean


Modified src/tactic/norm_cast.lean
- \+/\- *lemma* ite_cast
- \+ *lemma* nat_cast_re
- \- *lemma* ge_from_le
- \- *lemma* gt_from_lt
- \- *lemma* ne_from_not_eq
- \+ *theorem* coe_nat_inj'
- \+ *theorem* coe_int_denom
- \+ *theorem* cast_id
- \+ *theorem* coe_nat_add
- \+ *theorem* cast_sub
- \+ *theorem* coe_nat_bit0
- \+ *theorem* cast_coe_nat
- \+ *theorem* cast_one
- \+ *def* of_string

Modified src/topology/algebra/group_completion.lean
- \+/\- *lemma* uniform_space.completion.coe_zero

Modified src/topology/algebra/module.lean
- \+/\- *lemma* coe_coe
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_zero'
- \+/\- *lemma* coe_id
- \+/\- *lemma* coe_id'
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_add'
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_neg'
- \+/\- *lemma* coe_sub
- \+/\- *lemma* coe_sub'
- \+/\- *lemma* coe_comp
- \+/\- *lemma* coe_comp'
- \+/\- *lemma* coe_prod
- \+/\- *lemma* prod_apply
- \+/\- *lemma* coe_fst
- \+/\- *lemma* coe_fst'
- \+/\- *lemma* coe_snd
- \+/\- *lemma* coe_snd'
- \+/\- *lemma* coe_prod_map
- \+/\- *lemma* prod_map_apply
- \+/\- *lemma* coe_apply
- \+/\- *lemma* coe_apply'
- \+/\- *lemma* coe_refl
- \+/\- *lemma* coe_refl'

Modified src/topology/algebra/uniform_ring.lean
- \+/\- *lemma* coe_one

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* tendsto_coe

Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* has_sum_coe
- \+/\- *lemma* summable_coe
- \+/\- *lemma* coe_tsum

Modified src/topology/instances/real.lean
- \+/\- *lemma* rat.dist_cast
- \+/\- *theorem* int.dist_cast_real
- \+/\- *theorem* int.dist_cast_rat

Modified src/topology/metric_space/basic.lean


Modified test/norm_cast.lean
- \+ *lemma* coe_one
- \+ *lemma* coe_inj
- \+ *lemma* mul_coe
- \+ *lemma* half_lt_self_bis
- \+ *def* with_zero

Created test/norm_cast_cardinal.lean
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1

Created test/norm_cast_coe_fn.lean
- \+ *lemma* hom_plus.coe_fn
- \+ *lemma* coe_f1
- \+ *def* f1
- \+ *def* f2

Created test/norm_cast_int.lean


Created test/norm_cast_lemma_order.lean


Created test/norm_cast_sum_lambda.lean




## [2020-04-16 04:20:38](https://github.com/leanprover-community/mathlib/commit/7270af9)
chore(scripts): update nolints.txt ([#2430](https://github.com/leanprover-community/mathlib/pull/2430))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-16 01:05:50](https://github.com/leanprover-community/mathlib/commit/5ac2b48)
feat(category_theory): connected categories ([#2413](https://github.com/leanprover-community/mathlib/pull/2413))
- Define connected categories (using the convention that they must be nonempty) by asserting every functor to a discrete category is isomorphic to a constant functor. We also give some equivalent conditions which are more useful in practice: for instance that any function which is constant for objects which have a single morphism between them is constant everywhere.
- Give the definition of connected category as specified on wikipedia, and show it's equivalent. (This is more intuitive but it seems harder to both prove and use in lean, it also seems nicer stated with `head'`. If reviewers believe this should be removed, I have no objection, but I include it for now since it is the more familiar definition).
- Give three examples of connected categories.
- Prove that `X × -` preserves connected limits.
This PR is the first of three PRs aiming to resolve my TODO [here](https://github.com/leanprover-community/mathlib/blob/cf89963e14cf535783cefba471247ae4470fa8c3/src/category_theory/limits/over.lean#L143) - that the forgetful functor from the over category creates connected limits.
Make sure you have:
  * [x] reviewed and applied the coding style: [coding](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/style.md), [naming](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/naming.md)
  * [x] reviewed and applied [the documentation requirements](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/doc.md)
  * [x] make sure definitions and lemmas are put in the right files
  * [x] make sure definitions and lemmas are not redundant
If this PR is related to a discussion on Zulip, please include a link in the discussion.
For reviewers: [code review check list](https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/code-review.md)
#### Estimated changes
Created src/category_theory/connected.lean
- \+ *lemma* any_functor_const_on_obj
- \+ *lemma* constant_of_preserves_morphisms
- \+ *lemma* induct_on_objects
- \+ *lemma* equiv_relation
- \+ *lemma* connected_zigzag
- \+ *lemma* exists_zigzag'
- \+ *lemma* nat_trans_from_connected
- \+ *def* connected.of_any_functor_const_on_obj
- \+ *def* connected.of_constant_of_preserves_morphisms
- \+ *def* connected.of_induct
- \+ *def* zag
- \+ *def* zigzag
- \+ *def* zigzag_connected
- \+ *def* connected_of_zigzag

Created src/category_theory/limits/connected.lean
- \+ *def* γ₂
- \+ *def* γ₁
- \+ *def* forget_cone
- \+ *def* prod_preserves_connected_limits

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* prod_functor

Modified src/data/list/chain.lean
- \+ *lemma* exists_chain_of_relation_refl_trans_gen
- \+ *lemma* chain.induction

Modified src/data/list/defs.lean




## [2020-04-15 22:29:29](https://github.com/leanprover-community/mathlib/commit/66cc298)
feat(data/finset): existence of a smaller set ([#2420](https://github.com/leanprover-community/mathlib/pull/2420))
Show the existence of a smaller finset contained in a given finset.
The next in my series of lemmas for my combinatorics project.
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* exists_intermediate_set
- \+ *lemma* exists_smaller_set



## [2020-04-15 18:44:26](https://github.com/leanprover-community/mathlib/commit/8510f07)
chore(scripts): update nolints.txt ([#2425](https://github.com/leanprover-community/mathlib/pull/2425))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-15 17:53:24](https://github.com/leanprover-community/mathlib/commit/1e212d7)
fix(data/zmod/basic): typo ([#2424](https://github.com/leanprover-community/mathlib/pull/2424))
#### Estimated changes
Modified src/data/zmod/basic.lean




## [2020-04-15 16:47:40](https://github.com/leanprover-community/mathlib/commit/ce72cde)
feat(category_theory/limits): special shapes API cleanup ([#2423](https://github.com/leanprover-community/mathlib/pull/2423))
This is the 2.5th PR in a series of most likely three PRs about the cohomology functor. This PR has nothing to do with cohomology, but I'm going to need a lemma from this pull request in the final PR in the series.
In this PR, I
* perform various documentation and cleanup tasks
* add lemmas similar to the ones seen in [#2396](https://github.com/leanprover-community/mathlib/pull/2396) for equalizers, kernels and pullbacks (NB: these are not needed for biproducts since the `simp` and `ext` lemmas for products and coproducts readily fire)
* generalize `prod.hom_ext` to the situation where we have a `binary_fan X Y` and an `is_limit` for that specific fan (and similar for the other shapes)
* add "bundled" versions of lift and desc. Here is the most important example:
```lean
def kernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : {l : W ⟶ kernel f // l ≫ kernel.ι f = k} :=
⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩
```
This definition doesn't really do anything by itself, but it makes proofs comforable and readable. For example, if you say `obtain ⟨t, ht⟩ := kernel.lift' g p hpg`, then the interesting property of `t` is right there in the tactic view, which I find helpful in keeping track of things when a proof invokes a lot of universal properties.
#### Estimated changes
Modified src/algebra/category/Module/basic.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* binary_fan.is_limit.hom_ext
- \+ *lemma* binary_cofan.is_colimit.hom_ext
- \+/\- *lemma* prod.hom_ext
- \+/\- *lemma* coprod.hom_ext
- \+/\- *lemma* prod.lift_fst
- \+/\- *lemma* prod.lift_snd
- \+/\- *lemma* coprod.inl_desc
- \+/\- *lemma* coprod.inr_desc
- \+ *lemma* prod.map_fst
- \+ *lemma* prod.map_snd
- \+ *lemma* coprod.inl_map
- \+ *lemma* coprod.inr_map
- \+ *def* binary_fan.is_limit.lift'
- \+ *def* binary_cofan.is_colimit.desc'
- \+ *def* prod.lift'
- \+ *def* coprod.desc'

Modified src/category_theory/limits/shapes/constructions/pullbacks.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \+ *lemma* fork.app_zero_left
- \+ *lemma* fork.app_zero_right
- \+ *lemma* cofork.left_app_one
- \+ *lemma* cofork.right_app_one
- \+ *lemma* fork.equalizer_ext
- \+ *lemma* cofork.coequalizer_ext
- \+ *lemma* fork.is_limit.hom_ext
- \+ *lemma* cofork.is_colimit.hom_ext
- \+ *lemma* equalizer.lift_ι
- \+/\- *lemma* mono_of_is_limit_parallel_pair
- \+ *lemma* coequalizer.π_desc
- \+/\- *lemma* epi_of_is_colimit_parallel_pair
- \- *lemma* cone_parallel_pair_left
- \- *lemma* cone_parallel_pair_right
- \- *lemma* cocone_parallel_pair_left
- \- *lemma* cocone_parallel_pair_right
- \- *lemma* cone_parallel_pair_ext
- \- *lemma* cocone_parallel_pair_ext
- \+ *def* fork.is_limit.lift'
- \+ *def* cofork.is_colimit.desc'
- \+ *def* equalizer.lift'
- \+ *def* coequalizer.desc'
- \- *def* fork.ι
- \- *def* cofork.π

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *lemma* kernel.lift_ι
- \+ *lemma* cokernel.π_desc
- \+ *def* kernel_fork.is_limit.lift'
- \+ *def* kernel.lift'
- \+ *def* cokernel_cofork.is_limit.desc'
- \+ *def* cokernel.desc'

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* is_limit.hom_ext
- \+ *lemma* is_colimit.hom_ext
- \+ *lemma* pullback.lift_fst
- \+ *lemma* pullback.lift_snd
- \+ *lemma* pushout.inl_desc
- \+ *lemma* pushout.inr_desc
- \+ *def* is_limit.lift'
- \+ *def* is_colimit.desc'
- \+ *def* pullback.lift'
- \+ *def* pullback.desc'



## [2020-04-15 13:54:37](https://github.com/leanprover-community/mathlib/commit/9b797ee)
feat(library_search): (efficiently) try calling symmetry before searching the library ([#2415](https://github.com/leanprover-community/mathlib/pull/2415))
This fixes a gap in `library_search` we've known about for a long time: it misses lemmas stated "the other way round" than what you were looking for.
This PR fixes that. I cache the `tactic_state` after calling `symmetry`, so it is only called once, regardless of how much of the library we're searching.
When `library_search` was already succeeding, it should still succeed, with the same run time.
When it was failing, it will now either succeed (because it found a lemma after calling `symmetry`), or fail (in the same time, if `symmetry` fails, or approximately twice the time, if `symmetry` succeeds). I think this is a reasonable time trade-off for better search results.
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean




## [2020-04-15 07:41:54](https://github.com/leanprover-community/mathlib/commit/8e8037f)
chore(category_theory/limits): remove dependency on concrete_categories ([#2411](https://github.com/leanprover-community/mathlib/pull/2411))
Just move some content around, so that `category_theory/limits/cones.lean` doesn't need to depend on the development of `concrete_category`.
#### Estimated changes
Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/category/Mon/colimits.lean


Modified src/category_theory/differential_object.lean


Modified src/category_theory/graded_object.lean


Created src/category_theory/limits/concrete_category.lean
- \+ *lemma* naturality_concrete

Modified src/category_theory/limits/cones.lean
- \- *lemma* naturality_concrete



## [2020-04-14 12:45:29](https://github.com/leanprover-community/mathlib/commit/fd0dc27)
chore(scripts): update nolints.txt ([#2418](https://github.com/leanprover-community/mathlib/pull/2418))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-14 11:02:03](https://github.com/leanprover-community/mathlib/commit/96a07a7)
refactor(analysis/calculus/deriv): split comp and scomp ([#2410](https://github.com/leanprover-community/mathlib/pull/2410))
The derivative of the composition of a function and a scalar function was written using `smul`, regardless of the fact that the first function was vector-valued (in which case `smul` is not avoidable)  or scalar-valued (in which case it can be replaced by `mul`). Instead, this PR introduces two sets of lemmas (named `scomp` for the first type and `comp` for the second type) to get the usual multiplication in the formula for the derivative of the composition of two scalar functions.
#### Estimated changes
Modified src/analysis/ODE/gronwall.lean


Modified src/analysis/calculus/deriv.lean
- \+ *lemma* deriv_within.scomp
- \+ *lemma* deriv.scomp
- \+/\- *lemma* deriv_within.comp
- \+/\- *lemma* deriv.comp
- \+ *theorem* has_deriv_at_filter.scomp
- \+ *theorem* has_deriv_within_at.scomp
- \+ *theorem* has_deriv_at.scomp
- \+ *theorem* has_deriv_at.scomp_has_deriv_within_at
- \+/\- *theorem* has_deriv_at_filter.comp
- \+/\- *theorem* has_deriv_within_at.comp
- \+/\- *theorem* has_deriv_at.comp
- \+/\- *theorem* has_deriv_at.comp_has_deriv_within_at

Modified src/analysis/complex/exponential.lean




## [2020-04-14 11:02:02](https://github.com/leanprover-community/mathlib/commit/15fcb8a)
feat(algebra/lie_algebra): define equivalences, direct sums of Lie algebras ([#2404](https://github.com/leanprover-community/mathlib/pull/2404))
This pull request does two things:
1. Defines equivalences of Lie algebras (and proves that these do indeed form an equivalence relation)
2. Defines direct sums of Lie algebras
The intention is to knock another chip off https://github.com/leanprover-community/mathlib/issues/1093
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+/\- *lemma* map_lie
- \+/\- *lemma* map_lie'
- \+ *lemma* morphism.comp_apply
- \+ *lemma* bracket_apply
- \+ *def* morphism.comp
- \+ *def* morphism.inverse
- \+ *def* refl
- \+ *def* symm
- \+ *def* trans



## [2020-04-14 08:19:33](https://github.com/leanprover-community/mathlib/commit/ba154bc)
fix(library_search): find id ([#2414](https://github.com/leanprover-community/mathlib/pull/2414))
Previously `library_search` could not find theorems that did not have a head symbol (e.g. were function types with source and target both "variables all the way down"). Now it can, so it solves:
```lean
example (α : Prop) : α → α :=
by library_search -- says: `exact id`
example (p : Prop) [decidable p] : (¬¬p) → p :=
by library_search -- says: `exact not_not.mp`
example (a b : Prop) (h : a ∧ b) : a := 
by library_search -- says: `exact h.left`
example (P Q : Prop) [decidable P] [decidable Q]: (¬ Q → ¬ P) → (P → Q) :=
by library_search -- says: `exact not_imp_not.mp`
```
#### Estimated changes
Modified src/tactic/suggest.lean


Modified test/library_search/basic.lean




## [2020-04-14 07:18:15](https://github.com/leanprover-community/mathlib/commit/af27ee3)
chore(analysis): two more -T50000 challenges ([#2393](https://github.com/leanprover-community/mathlib/pull/2393))
Refactor two proofs to bring them under `-T50000`, in the hope that we can later add this requirement to CI, per [#2276](https://github.com/leanprover-community/mathlib/pull/2276).
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+ *lemma* change_origin_summable_aux_j_inj
- \+ *def* change_origin_summable_aux_j

Modified src/analysis/complex/basic.lean
- \+ *lemma* has_deriv_at_real_of_complex_aux
- \+/\- *theorem* has_deriv_at_real_of_complex



## [2020-04-13 17:33:51](https://github.com/leanprover-community/mathlib/commit/8356b79)
feat(logic/basic): a few simp lemmas about `and` and `or` ([#2408](https://github.com/leanprover-community/mathlib/pull/2408))
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* and_self_left
- \+ *lemma* and_self_right
- \+ *lemma* or_self_left
- \+ *lemma* or_self_right



## [2020-04-13 17:33:49](https://github.com/leanprover-community/mathlib/commit/fe878ea)
feat(algebra/big-operators): some big operator lemmas ([#2152](https://github.com/leanprover-community/mathlib/pull/2152))
Lemmas I found useful in my [combinatorics](https://b-mehta.github.io/combinatorics/) project
Make sure you have:
  * [x] reviewed and applied the coding style: [coding](https://github.com/leanprover/mathlib/blob/master/docs/contribute/style.md), [naming](https://github.com/leanprover/mathlib/blob/master/docs/contribute/naming.md)
  * [x] reviewed and applied [the documentation requirements](https://github.com/leanprover/mathlib/blob/master/docs/contribute/doc.md)
  * [x] make sure definitions and lemmas are put in the right files
  * [x] make sure definitions and lemmas are not redundant
If this PR is related to a discussion on Zulip, please include a link in the discussion.
For reviewers: [code review check list](https://github.com/leanprover/mathlib/blob/master/docs/contribute/code-review.md)
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* prod_flip
- \+ *lemma* sum_const_nat
- \+ *lemma* sum_flip
- \+ *lemma* sum_div
- \+ *lemma* sum_lt_sum_of_nonempty



## [2020-04-13 17:33:47](https://github.com/leanprover-community/mathlib/commit/67e363f)
feat(data/finset): finset lemmas from combinatorics ([#2149](https://github.com/leanprover-community/mathlib/pull/2149))
The beginnings of moving results from my combinatorics project
Make sure you have:
  * [x] reviewed and applied the coding style: [coding](https://github.com/leanprover/mathlib/blob/master/docs/contribute/style.md), [naming](https://github.com/leanprover/mathlib/blob/master/docs/contribute/naming.md)
  * [x] reviewed and applied [the documentation requirements](https://github.com/leanprover/mathlib/blob/master/docs/contribute/doc.md)
  * [x] make sure definitions and lemmas are put in the right files
  * [x] make sure definitions and lemmas are not redundant
For reviewers: [code review check list](https://github.com/leanprover/mathlib/blob/master/docs/contribute/code-review.md)
#### Estimated changes
Modified archive/cubing_a_cube.lean


Modified src/data/finset.lean
- \+ *lemma* inter_union_self
- \+ *lemma* union_eq_empty_iff
- \+ *lemma* not_mem_sdiff_of_mem_right
- \+ *lemma* sdiff_union_inter
- \+ *lemma* sdiff_idem
- \+ *lemma* union_sdiff_distrib
- \+ *lemma* sdiff_union_distrib
- \+ *lemma* union_sdiff_self
- \+ *lemma* sdiff_singleton_eq_erase
- \+ *lemma* sdiff_sdiff_self_left
- \+ *lemma* inter_eq_inter_of_sdiff_eq_sdiff
- \+ *lemma* bind_subset_bind_of_subset_left
- \+ *lemma* min'_lt_max'_of_card
- \+ *lemma* exists_max_image
- \+ *lemma* exists_min_image
- \+ *lemma* disjoint_sdiff_inter
- \+ *lemma* sdiff_eq_self_iff_disjoint
- \+ *lemma* sdiff_eq_self_of_disjoint
- \+ *lemma* disjoint_self_iff_empty
- \- *lemma* exists_min

Modified src/data/set/finite.lean
- \+ *lemma* exists_min_image
- \+ *lemma* exists_max_image
- \- *lemma* exists_min



## [2020-04-13 14:53:40](https://github.com/leanprover-community/mathlib/commit/f3ac7b7)
feat(combinatorics/composition): introduce compositions of an integer ([#2398](https://github.com/leanprover-community/mathlib/pull/2398))
A composition of an integer `n` is a decomposition of `{0, ..., n-1}` into blocks of consecutive
integers. Equivalently, it is a decomposition `n = i₀ + ... + i_{k-1}` into a sum of positive
integers. We define compositions in this PR, and introduce a whole interface around it. The goal is to use this as a tool in the proof that the composition of analytic functions is analytic
#### Estimated changes
Modified src/algebra/group/basic.lean


Created src/combinatorics/composition.lean
- \+ *lemma* blocks_sum
- \+ *lemma* blocks_length
- \+ *lemma* blocks_pnat_length
- \+ *lemma* sum_blocks_fun
- \+ *lemma* one_le_blocks
- \+ *lemma* blocks_pos
- \+ *lemma* one_le_blocks'
- \+ *lemma* blocks_pos'
- \+ *lemma* length_le
- \+ *lemma* length_pos_of_pos
- \+ *lemma* size_up_to_zero
- \+ *lemma* size_up_to_of_length_le
- \+ *lemma* size_up_to_length
- \+ *lemma* size_up_to_le
- \+ *lemma* size_up_to_succ
- \+ *lemma* size_up_to_succ'
- \+ *lemma* size_up_to_strict_mono
- \+ *lemma* boundary_zero
- \+ *lemma* boundary_last
- \+ *lemma* strict_mono_boundary
- \+ *lemma* card_boundaries_eq_succ_length
- \+ *lemma* mono_of_fin_boundaries
- \+ *lemma* embedding_inj
- \+ *lemma* index_exists
- \+ *lemma* lt_size_up_to_index_succ
- \+ *lemma* size_up_to_index_le
- \+ *lemma* embedding_comp_inv
- \+ *lemma* mem_range_embedding_iff
- \+ *lemma* disjoint_range
- \+ *lemma* mem_range_embedding
- \+ *lemma* mem_range_embedding_iff'
- \+ *lemma* sigma_eq_iff_blocks_pnat_eq
- \+ *lemma* sigma_eq_iff_blocks_eq
- \+ *lemma* composition_as_set_card
- \+ *lemma* boundaries_nonempty
- \+ *lemma* card_boundaries_pos
- \+ *lemma* length_lt_card_boundaries
- \+ *lemma* lt_length
- \+ *lemma* lt_length'
- \+ *lemma* boundary_length
- \+ *lemma* blocks_fun_pos
- \+ *lemma* blocks_partial_sum
- \+ *lemma* mem_boundaries_iff_exists_blocks_sum_take_eq
- \+ *lemma* coe_blocks_pnat_eq_blocks
- \+ *lemma* composition.to_composition_as_set_length
- \+ *lemma* composition_as_set.to_composition_length
- \+ *lemma* composition.to_composition_as_set_blocks
- \+ *lemma* composition.to_composition_as_set_blocks_pnat
- \+ *lemma* composition_as_set.to_composition_blocks_pnat
- \+ *lemma* composition_as_set.to_composition_blocks
- \+ *lemma* composition_as_set.to_composition_boundaries
- \+ *lemma* composition.to_composition_as_set_boundaries
- \+ *lemma* composition_card
- \+ *def* blocks
- \+ *def* length
- \+ *def* blocks_fun
- \+ *def* size_up_to
- \+ *def* boundary
- \+ *def* boundaries
- \+ *def* to_composition_as_set
- \+ *def* embedding
- \+ *def* index
- \+ *def* inv_embedding
- \+ *def* composition_as_set_equiv
- \+ *def* blocks_pnat
- \+ *def* to_composition
- \+ *def* composition_equiv

Modified src/data/fin.lean
- \+/\- *lemma* coe_mk
- \+ *lemma* coe_last
- \+ *lemma* strict_mono_iff_lt_succ

Modified src/data/finset.lean
- \+ *lemma* mono_of_fin_bij_on
- \+ *lemma* mono_of_fin_injective
- \+ *lemma* mono_of_fin_eq_mono_of_fin_iff
- \- *lemma* bij_on_mono_of_fin

Modified src/data/fintype/basic.lean


Modified src/data/fintype/card.lean
- \+ *lemma* of_fn_prod_take
- \+ *lemma* of_fn_sum_take
- \+ *lemma* of_fn_prod

Modified src/data/list/basic.lean
- \+ *lemma* eq_of_sum_take_eq
- \+ *lemma* monotone_sum_take
- \+ *lemma* length_le_sum_of_one_le

Modified src/data/list/of_fn.lean
- \+ *lemma* map_of_fn
- \+/\- *theorem* nth_le_of_fn
- \+ *theorem* nth_le_of_fn'

Modified src/data/set/finite.lean
- \+ *lemma* finite_dependent_image



## [2020-04-13 13:52:21](https://github.com/leanprover-community/mathlib/commit/01ac691)
feat(category_theory/limits/shapes/binary_products): add some basic API for prod and coprod ([#2396](https://github.com/leanprover-community/mathlib/pull/2396))
Adding explicit proofs of some basic results about maps into A x B and maps from A coprod B
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* prod.hom_ext
- \+ *lemma* prod.lift_fst
- \+ *lemma* prod.lift_snd
- \+ *lemma* coprod.hom_ext
- \+ *lemma* coprod.inl_desc
- \+ *lemma* coprod.inr_desc



## [2020-04-13 12:55:12](https://github.com/leanprover-community/mathlib/commit/cf89963)
chore(scripts): update nolints.txt ([#2405](https://github.com/leanprover-community/mathlib/pull/2405))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-13 08:52:34](https://github.com/leanprover-community/mathlib/commit/17b2d06)
refactor(order/filter): refactor filters infi and bases ([#2384](https://github.com/leanprover-community/mathlib/pull/2384))
This PR expands what Yury wrote about filter bases, and takes the opportunity to bring long overdue clarification to our treatment of infimums of filters (and also improve documentation and ordering in
filter.basic). I'm sorry it mixes reorganization and some new content, but this was hard to avoid (I do keep what motivated all this for a later PR).
The fundamental problem is that the infimum construction remained mysterious in filter.basic. All lemmas about it assume a directed family of filters. Yet there are many uses of infimums without this condition, notatably things like `⨅ i, principal (s i)` without condition on the indexed family of sets `s`.
Related to this, `filter.generate` stayed mysterious. It was used only as a technical device to lift the complete lattice structure from `set (set a)`. However it has a perfectly valid mathematical existence,
as explained by the lemma 
```lean
lemma sets_iff_generate {s : set (set α)} {f : filter α} : f ≤ filter.generate s ↔ s ⊆ f.sets
```
which justifies the docstring of `generate`: `generate g` is the smallest filter containing the sets `g`.
As an example of the mess this created, consider:
https://github.com/leanprover-community/mathlib/blob/e758263/src/topology/bases.lean#L25 
```lean
def has_countable_basis (f : filter α) : Prop :=
∃ s : set (set α), countable s ∧ f = ⨅ t ∈ s, principal t
```
As it stands, this definition is not clearly related to asking for the existence of a countable `s` such that `f = generate s`.
Here the main mathematical content this PR adds in this direction:
```lean
lemma mem_generate_iff (s : set $ set α) {U : set α} : U ∈ generate s ↔
∃ t ⊆ s, finite t ∧ ⋂₀ t ⊆ U
lemma infi_eq_generate (s : ι → filter α) : infi s = generate (⋃ i, (s
i).sets) 
lemma mem_infi_iff {ι} {s : ι → filter α} {U : set α} : (U ∈ ⨅ i, s i) ↔
  ∃ I : set ι, finite I ∧ ∃ V : {i | i ∈ I} → set α, (∀ i, V i ∈ s i) ∧
  (⋂ i, V i) ⊆ U
```
All the other changes in filter.basic are either:
* moving out stuff that should have been in other files (such as the lemmas that used to be at
the very top of this file)
* reordering lemmas so that we can have section headers and things are easier to find, 
* adding to the module docstring. This module docstring contains more mathematical explanation than our usual ones. I feel this is needed because many people think filters are exotic (whereas I'm more and more convinced we should teach filters).
The reordering stuff makes it clear we could split this file into a linear chain of files, like we did with topology, but this is open for discussion.
Next I added a lot to `filter.bases`. Here the issue is filter bases are used in two different ways. If you already have a filter, but you want to point out it suffices to use certain sets in it. Here you want to use Yury's `has_basis`. Or you can start with a (small) family of sets having nice properties, and build a filter out of it. Currently we don't have this in mathlib, but this is crucial for incoming PRs from the perfectoid project. For instance, in order to define the I-adic topology, you start with powers of I, make a filter and then make a topology. This also reduces the gap with Bourbaki which uses filter bases everywhere.
I turned `has_basis` into a single field structure. It makes it very slightly less convenient to prove (you need an extra pair of angle brackets) but much easier to extend when you want to record more
properties of the basis, like being countable or decreasing. Also I proved the fundamental property that `f.has_basis p s` implies that `s` (filtered by `p`) actually *is* a filter basis. This is of course easy but crucial to connect with real world maths.
At the end of this file, I moved the countable filter basis stuff that is currently in topology.bases (aiming for first countable topologies) except that I used the foundational work on filter.basic to clearly prove all different formulations. In particular:
```lean
lemma generate_eq_generate_inter (s : set (set α)) : generate s = generate (sInter '' { t | finite t ∧ t ⊆ s})
```
clarifies things because the right-hand colleciton is countable if `s` is, and has the nice directedness condition.
I also took the opportunity to simplify a proof in topology.sequences, showcasing the power of the newly introduced
```lean
lemma has_antimono_basis.tendsto [semilattice_sup ι] [nonempty ι] {l :
filter α} {p : ι → Prop} {s : ι → set α} (hl : l.has_antimono_basis p s)
{φ : ι → α} (h : ∀ i : ι, φ i ∈ s i) : tendsto φ at_top l
```
(I will add more to that sequences file in the next PR).
#### Estimated changes
Modified docs/theories/topology.md


Modified src/data/set/finite.lean
- \+ *lemma* eq_finite_Union_of_finite_subset_Union

Modified src/data/set/lattice.lean
- \+ *lemma* directed_on_Union
- \+ *theorem* sInter_Union

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/set_integral.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* infi_subtype''

Modified src/order/filter/bases.lean
- \+ *lemma* mem_filter_basis_iff
- \+ *lemma* mem_filter_iff
- \+ *lemma* mem_filter_of_mem
- \+ *lemma* eq_infi_principal
- \+ *lemma* filter_eq_generate
- \+ *lemma* has_basis_generate
- \+ *lemma* has_basis.is_basis
- \+ *lemma* has_basis.filter_eq
- \+ *lemma* has_basis.eq_generate
- \+ *lemma* generate_eq_generate_inter
- \+ *lemma* of_sets_filter_eq_generate
- \+/\- *lemma* has_basis.eventually_iff
- \+ *lemma* has_antimono_basis.tendsto
- \+ *lemma* antimono_seq_of_seq
- \+ *lemma* countable_binfi_eq_infi_seq
- \+ *lemma* countable_binfi_eq_infi_seq'
- \+ *lemma* countable_binfi_principal_eq_seq_infi
- \+ *lemma* countable_generating_set
- \+ *lemma* eq_generate
- \+ *lemma* filter_basis_filter
- \+ *lemma* has_countable_basis
- \+ *lemma* exists_countable_infi_principal
- \+ *lemma* exists_seq
- \+ *lemma* exists_antimono_seq
- \+ *lemma* has_antimono_basis
- \+ *lemma* is_countably_generated_seq
- \+ *lemma* is_countably_generated_of_seq
- \+ *lemma* is_countably_generated_binfi_principal
- \+ *lemma* is_countably_generated_iff_exists_antimono_basis
- \+ *lemma* exists_antimono_seq'
- \+ *lemma* tendsto_iff_seq_tendsto
- \+ *lemma* tendsto_of_seq_tendsto
- \+ *lemma* is_countably_generated_at_top_finset_nat
- \+ *def* filter_basis.of_sets
- \+ *def* is_countably_generated
- \+ *def* generating_set
- \+ *def* countable_filter_basis

Modified src/order/filter/basic.lean
- \+ *lemma* sInter_mem_sets_of_finite
- \+ *lemma* mem_generate_iff
- \+ *lemma* infi_eq_generate
- \+ *lemma* mem_infi_iff
- \+/\- *lemma* principal_univ
- \+/\- *lemma* principal_empty
- \+/\- *lemma* infi_ne_bot_of_directed'
- \+/\- *lemma* infi_ne_bot_of_directed
- \+/\- *lemma* infi_ne_bot_iff_of_directed'
- \+/\- *lemma* infi_ne_bot_iff_of_directed
- \+/\- *lemma* mem_infi_sets
- \+/\- *lemma* infi_sets_induct
- \+/\- *lemma* inf_principal
- \+/\- *lemma* sup_principal
- \+/\- *lemma* supr_principal
- \+/\- *lemma* principal_eq_bot_iff
- \+/\- *lemma* principal_ne_bot_iff
- \+/\- *lemma* inf_principal_eq_bot
- \+/\- *lemma* infi_principal_finset
- \+/\- *lemma* infi_principal_fintype
- \+/\- *lemma* sequence_mono
- \+/\- *lemma* mem_traverse_sets
- \+/\- *lemma* mem_traverse_sets_iff
- \+ *lemma* map_at_top_inf_ne_bot_iff
- \+/\- *lemma* mem_cofinite
- \+/\- *lemma* cofinite_ne_bot
- \+/\- *lemma* frequently_cofinite_iff_infinite
- \+/\- *lemma* set.infinite_iff_frequently_cofinite
- \+/\- *lemma* nat.cofinite_eq_at_top
- \- *lemma* directed_on_Union
- \+/\- *theorem* mem_inf_principal
- \- *theorem* directed_of_chain
- \+/\- *def* cofinite

Modified src/order/zorn.lean
- \+ *theorem* directed_of_chain

Modified src/topology/bases.lean
- \- *lemma* has_countable_basis_of_seq
- \- *lemma* seq_of_has_countable_basis
- \- *lemma* has_countable_basis_iff_seq
- \- *lemma* mono_seq_of_has_countable_basis
- \- *lemma* has_countable_basis_iff_mono_seq
- \- *lemma* has_countable_basis_iff_mono_seq'
- \- *lemma* has_countable_basis.comap
- \- *lemma* has_countable_basis_at_top_finset_nat
- \- *lemma* has_countable_basis.tendsto_iff_seq_tendsto
- \- *lemma* has_countable_basis.tendsto_of_seq_tendsto
- \- *def* has_countable_basis

Modified src/topology/basic.lean


Modified src/topology/continuous_on.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* uniformity_has_countable_basis
- \+/\- *theorem* mem_nhds_iff

Modified src/topology/sequences.lean


Modified src/topology/uniform_space/cauchy.lean




## [2020-04-13 08:52:32](https://github.com/leanprover-community/mathlib/commit/92c8d93)
feat(algebra/homology): the cohomology functor ([#2374](https://github.com/leanprover-community/mathlib/pull/2374))
This is the second in a series of most likely three PRs about the cohomology functor. As such, this PR depends on [#2373](https://github.com/leanprover-community/mathlib/pull/2373).
In the project laid out in `homology.lean`, @semorrison asks what the minimal assumptions are that are needed to get induced maps on images. In this PR, I offer a tautologial answer to this question: We get induced maps on images when there are induced maps on images. In this way, we can let type class resolution answer the question whether cohomology is functorial.
In particular, the third PR will contain the fact that if our images are strong epi-mono factorizations, then we get induced maps on images. Since the regular coimage construction in regular categories is a strong epi-mono factorization, the approach in this PR generalizes the previous suggestion of requiring `V` to be regular.
A quick remark about cohomology and dependent types: As you can see, at one point Lean forces us to write `i - 1 + 1` instead of `i` because these two things are not definitionally equal. I am afraid, as we do more with cohomology, there will be many cases of this issue, and to compose morphisms whose types contain different incarnations of the same integer, we will have to insert some `eq_to_hom`-esque glue and pray that we will be able to rewrite them all away in the proofs without getting the beloved `motive is not type correct` error. Maybe there is some better way to solve this problem? (Or am I overthinking this and it is not actually going to be an issue at all?)
#### Estimated changes
Modified src/algebra/homology/homology.lean
- \+ *lemma* image_map_ι
- \+ *lemma* image_to_kernel_map_condition
- \+ *lemma* induced_maps_commute
- \+ *lemma* cohomology_map_condition
- \+ *lemma* cohomology_map_id
- \+ *lemma* cohomology_map_comp
- \+ *def* cohomology_map
- \+ *def* cohomology_functor



## [2020-04-13 07:55:23](https://github.com/leanprover-community/mathlib/commit/ca98659)
chore(scripts): update nolints.txt ([#2403](https://github.com/leanprover-community/mathlib/pull/2403))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-13 05:19:08](https://github.com/leanprover-community/mathlib/commit/51f7319)
chore(algebra/module): rename type vars, minor cleanup, add module docstring ([#2392](https://github.com/leanprover-community/mathlib/pull/2392))
* Use `R`, `S` for rings, `k` for a field, `M`, `M₂` etc for modules;
* Add a `semiring` version of `ring_hom.to_module`;
* Stop using `{rα : ring α}` trick as Lean 3.7 tries unification before class search;
* Add a short module docstring
#### Estimated changes
Modified src/algebra/module.lean
- \+/\- *lemma* semimodule.eq_zero_of_zero_eq_one
- \+/\- *lemma* list.sum_smul
- \+/\- *lemma* multiset.sum_smul
- \+/\- *lemma* finset.sum_smul
- \+/\- *lemma* smul_eq_mul
- \+/\- *lemma* coe_mk
- \+/\- *lemma* to_fun_eq_coe
- \+/\- *lemma* map_add
- \+/\- *lemma* map_smul
- \+/\- *lemma* to_add_monoid_hom_coe
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_sum
- \+/\- *lemma* comp_apply
- \+/\- *lemma* id_apply
- \+/\- *lemma* is_linear_map_neg
- \+/\- *lemma* is_linear_map_smul
- \+/\- *lemma* is_linear_map_smul'
- \+/\- *lemma* map_zero
- \+/\- *lemma* zero_mem
- \+/\- *lemma* smul_mem
- \+/\- *lemma* neg_mem
- \+/\- *lemma* sum_mem
- \+/\- *lemma* smul_mem_iff'
- \+/\- *lemma* coe_add
- \+/\- *lemma* coe_zero
- \+/\- *lemma* coe_neg
- \+/\- *lemma* coe_smul
- \+/\- *lemma* coe_sub
- \+/\- *lemma* subtype_eq_val
- \+/\- *lemma* semimodule.add_monoid_smul_eq_smul
- \+/\- *lemma* module.gsmul_eq_smul
- \+/\- *lemma* sum_const'
- \+/\- *theorem* zero_smul
- \+/\- *theorem* neg_one_smul
- \+/\- *theorem* smul_sub
- \+/\- *theorem* sub_smul
- \+/\- *theorem* is_linear
- \+/\- *theorem* ext
- \+/\- *theorem* ext_iff
- \+/\- *theorem* mk'_apply
- \+/\- *theorem* mem_coe
- \+/\- *theorem* ext'
- \+/\- *def* module.of_core
- \+ *def* ring_hom.to_semimodule
- \+/\- *def* ring_hom.to_module
- \+/\- *def* to_add_monoid_hom
- \+/\- *def* comp
- \+/\- *def* id
- \+/\- *def* mk'
- \+/\- *def* ideal
- \+/\- *def* subspace
- \+/\- *def* add_monoid_hom.to_int_linear_map
- \+/\- *def* add_monoid_hom.to_rat_linear_map



## [2020-04-13 03:08:38](https://github.com/leanprover-community/mathlib/commit/64fa9a2)
chore(*): futureproof import syntax ([#2402](https://github.com/leanprover-community/mathlib/pull/2402))
The next community version of Lean will treat a line starting in the first column
after an import as a new command, not a continuation of the import.
#### Estimated changes
Modified src/analysis/analytic/basic.lean


Modified src/topology/metric_space/gromov_hausdorff.lean


Modified src/topology/metric_space/gromov_hausdorff_realized.lean


Modified src/topology/metric_space/isometry.lean




## [2020-04-12 20:36:49](https://github.com/leanprover-community/mathlib/commit/ef4d235)
feat(category_theory): biproducts, and biproducts in AddCommGroup ([#2187](https://github.com/leanprover-community/mathlib/pull/2187))
This PR
1. adds typeclasses `has_biproducts` (implicitly restricting to finite biproducts, which is the only interesting case) and `has_binary_biproducts`, and the usual tooling for special shapes of limits.
2. provides customised `has_products` and `has_coproducts` instances for `AddCommGroup`, which are both just dependent functions (for `has_coproducts` we have to assume the indexed type is finite and decidable)
3. because these custom instances have identical underlying objects, it's trivial to put them together to get a `has_biproducts AddCommGroup`.
4. as for 2 & 3 with binary biproducts for AddCommGroup, implemented simply as the cartesian group.
#### Estimated changes
Created src/algebra/category/Group/biproducts.lean
- \+ *lemma* lift_apply
- \+ *lemma* desc_apply
- \+ *def* lift
- \+ *def* desc

Modified src/algebra/pi_instances.lean
- \+/\- *lemma* add_monoid_hom.single_apply

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Created src/category_theory/limits/shapes/biproducts.lean
- \+ *def* to_cone
- \+ *def* to_cocone
- \+ *def* biproduct_iso
- \+ *def* biprod_iso



## [2020-04-12 18:17:30](https://github.com/leanprover-community/mathlib/commit/1433f05)
fix(tactic/norm_cast): typo ([#2400](https://github.com/leanprover-community/mathlib/pull/2400))
#### Estimated changes
Modified src/tactic/norm_cast.lean




## [2020-04-12 06:01:35](https://github.com/leanprover-community/mathlib/commit/d84de80)
feat(set_theory/game): short games, boards, and domineering ([#1540](https://github.com/leanprover-community/mathlib/pull/1540))
This is a do-over of my previous attempt to implement the combinatorial game of domineering. This time, we get a nice clean definition, and it computes!
To achieve this, I follow Reid's advice: generalise! We define 
```
class state (S : Type u) :=
(turn_bound : S → ℕ)
(L : S → finset S)
(R : S → finset S)
(left_bound : ∀ {s t : S} (m : t ∈ L s), turn_bound t < turn_bound s)
(right_bound : ∀ {s t : S} (m : t ∈ R s), turn_bound t < turn_bound s)
```
a typeclass describing `S` as "the state of a game", and provide `pgame.of [state S] : S \to pgame`.
This allows a short and straightforward definition of Domineering:
```lean
/-- A Domineering board is an arbitrary finite subset of `ℤ × ℤ`. -/
def board := finset (ℤ × ℤ)
...
/-- The instance describing allowed moves on a Domineering board. -/
instance state : state board :=
{ turn_bound := λ s, s.card / 2,
  L := λ s, (left s).image (move_left s),
  R := λ s, (right s).image (move_right s),
  left_bound := _
  right_bound := _, }
```
which computes:
```
example : (domineering ([(0,0), (0,1), (1,0), (1,1)].to_finset) ≈ pgame.of_lists [1] [-1]) := dec_trivial
```
#### Estimated changes
Modified src/algebra/ring.lean
- \+ *lemma* succ_ne_self
- \+ *lemma* pred_ne_self

Created src/set_theory/game/domineering.lean
- \+ *lemma* card_of_mem_left
- \+ *lemma* card_of_mem_right
- \+ *lemma* move_left_card
- \+ *lemma* move_right_card
- \+ *lemma* move_left_smaller
- \+ *lemma* move_right_smaller
- \+ *def* shift_up
- \+ *def* shift_right
- \+ *def* board
- \+ *def* left
- \+ *def* right
- \+ *def* move_left
- \+ *def* move_right
- \+ *def* domineering
- \+ *def* domineering.one
- \+ *def* domineering.L

Created src/set_theory/game/short.lean
- \+ *def* short.mk'
- \+ *def* fintype_left
- \+ *def* fintype_right
- \+ *def* move_left_short'
- \+ *def* move_right_short'
- \+ *def* short_of_relabelling
- \+ *def* short_of_equiv_empty
- \+ *def* le_lt_decidable

Created src/set_theory/game/state.lean
- \+ *lemma* turn_bound_ne_zero_of_left_move
- \+ *lemma* turn_bound_ne_zero_of_right_move
- \+ *lemma* turn_bound_of_left
- \+ *lemma* turn_bound_of_right
- \+ *def* of_aux
- \+ *def* of_aux_relabelling
- \+ *def* of
- \+ *def* left_moves_of_aux
- \+ *def* left_moves_of
- \+ *def* right_moves_of_aux
- \+ *def* right_moves_of
- \+ *def* relabelling_move_left_aux
- \+ *def* relabelling_move_left
- \+ *def* relabelling_move_right_aux
- \+ *def* relabelling_move_right

Modified src/set_theory/pgame.lean
- \+/\- *lemma* relabel_move_left'
- \+/\- *lemma* relabel_move_left
- \+/\- *lemma* relabel_move_right'
- \+/\- *lemma* relabel_move_right
- \+ *def* relabelling.trans



## [2020-04-12 00:32:35](https://github.com/leanprover-community/mathlib/commit/0f89392)
chore(scripts): update nolints.txt ([#2395](https://github.com/leanprover-community/mathlib/pull/2395))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-11 22:53:11](https://github.com/leanprover-community/mathlib/commit/ee8cb15)
feat(category_theory): functorial images ([#2373](https://github.com/leanprover-community/mathlib/pull/2373))
This is the first in a series of most likely three PRs about the cohomology functor. In this PR, I
* add documentation for `comma.lean`,
* introduce the arrow category as a special case of the comma construction, and
* introduce the notion of functorial images, which means that commutative squares induce morphisms on images making the obvious diagram commute.
#### Estimated changes
Modified src/category_theory/comma.lean
- \+ *lemma* id_left
- \+ *lemma* id_right
- \+ *lemma* mk_hom
- \+ *lemma* hom_mk_left
- \+ *lemma* hom_mk_right
- \+ *lemma* hom_mk'_left
- \+ *lemma* hom_mk'_right
- \+/\- *def* map_right_comp
- \+ *def* arrow
- \+ *def* mk
- \+ *def* hom_mk
- \+ *def* hom_mk'

Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* image.factor_map
- \+ *lemma* image.map_ι
- \+ *lemma* image.map_hom_mk'_ι
- \+ *lemma* image.map_comp
- \+ *lemma* image.map_id
- \+ *def* has_image_map_comp
- \+ *def* has_image_map_id
- \+ *def* im



## [2020-04-11 21:19:21](https://github.com/leanprover-community/mathlib/commit/aa42f3b)
chore(scripts): update nolints.txt ([#2391](https://github.com/leanprover-community/mathlib/pull/2391))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-11 18:44:17](https://github.com/leanprover-community/mathlib/commit/5f1bfcf)
chore(tactic/lean_core_docs): add API docs for core Lean tactics ([#2371](https://github.com/leanprover-community/mathlib/pull/2371))
This is an attempt to get some documentation of most core Lean tactics into the API docs.
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/undocumented.20core.20tactics (and the link in my second message in that thread) for background.
Co-Authored-By: Rob Lewis <Rob.y.lewis@gmail.com>
Co-Authored-By: Scott Morrison <scott@tqft.net>
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Created src/tactic/lean_core_docs.lean




## [2020-04-11 18:44:15](https://github.com/leanprover-community/mathlib/commit/80340d8)
feat(category_theory): define action_category ([#2358](https://github.com/leanprover-community/mathlib/pull/2358))
This is a simple construction that I couldn't find anywhere else: given a monoid/group action on X, we get a category/groupoid structure on X. The plan is to use to use the action groupoid in the proof of Nielsen-Schreier, where the projection onto the single object groupoid is thought of as a covering map.
To make sense of "stabilizer is mul_equiv to End", I added the simple fact that the stabilizer of any multiplicative action is a submonoid. This already existed for group actions. As far as I can tell, this instance shouldn't cause any problems as it is a Prop.
#### Estimated changes
Created src/category_theory/action.lean
- \+ *lemma* π_map
- \+ *lemma* π_obj
- \+ *lemma* hom_as_subtype
- \+ *lemma* stabilizer_iso_End_apply
- \+ *lemma* stabilizer_iso_End_symm_apply
- \+ *def* action_as_functor
- \+ *def* action_category
- \+ *def* π
- \+ *def* obj_equiv
- \+ *def* stabilizer_iso_End

Modified src/category_theory/elements.lean
- \+/\- *def* functor.elements

Modified src/group_theory/group_action.lean




## [2020-04-11 16:16:28](https://github.com/leanprover-community/mathlib/commit/e1feab4)
refactor(*): rename ordered groups/monoids to ordered add_ groups/monoids ([#2347](https://github.com/leanprover-community/mathlib/pull/2347))
In the perfectoid project we need ordered commutative monoids, and they are multiplicative. So the additive versions should be renamed to make some place.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/archimedean.lean


Modified src/algebra/big_operators.lean
- \+/\- *lemma* le_sum_of_subadditive
- \+/\- *lemma* sum_lt_top
- \+/\- *lemma* sum_lt_top_iff

Modified src/algebra/group_power.lean
- \+/\- *theorem* add_monoid.smul_nonneg

Modified src/algebra/order_functions.lean


Modified src/algebra/ordered_group.lean
- \+/\- *lemma* zero_lt_top
- \+/\- *lemma* zero_lt_coe
- \+/\- *lemma* add_top
- \+/\- *lemma* top_add
- \+/\- *lemma* add_eq_top
- \+/\- *lemma* add_lt_top
- \+/\- *lemma* bot_add
- \+/\- *lemma* add_bot
- \+ *def* ordered_add_comm_monoid
- \+ *def* ordered_add_comm_group.mk'
- \- *def* ordered_comm_monoid
- \- *def* ordered_comm_group.mk'

Modified src/algebra/ordered_ring.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/punit_instances.lean


Modified src/data/finsupp.lean
- \+/\- *lemma* le_iff
- \+/\- *lemma* add_eq_zero_iff

Modified src/data/multiset.lean
- \+/\- *lemma* le_sum_of_subadditive

Modified src/data/nat/enat.lean


Modified src/data/pnat/factors.lean


Modified src/data/rat/order.lean


Modified src/data/real/basic.lean


Modified src/data/real/nnreal.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/set/intervals/unordered_interval.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/extr.lean


Modified src/set_theory/cardinal.lean


Modified src/set_theory/game.lean


Modified src/set_theory/surreal.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/algebra/ordered.lean
- \+ *lemma* decidable_linear_ordered_add_comm_group.tendsto_nhds
- \- *lemma* decidable_linear_ordered_comm_group.tendsto_nhds

Modified src/topology/local_extr.lean




## [2020-04-11 14:27:08](https://github.com/leanprover-community/mathlib/commit/c9fca15)
chore(algebra/category): remove some [reducible] after Lean 3.8 ([#2389](https://github.com/leanprover-community/mathlib/pull/2389))
Now that Lean 3.8 has arrived, we can essentially revert [#2290](https://github.com/leanprover-community/mathlib/pull/2290), but leave in the examples verifying that everything still works.
Lovely!
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/category_theory/concrete_category/bundled.lean


Modified src/category_theory/full_subcategory.lean




## [2020-04-11 13:00:39](https://github.com/leanprover-community/mathlib/commit/83359d1)
chore(scripts): update nolints.txt ([#2390](https://github.com/leanprover-community/mathlib/pull/2390))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-11 09:58:11](https://github.com/leanprover-community/mathlib/commit/4fa2924)
chore(scripts): update nolints.txt ([#2388](https://github.com/leanprover-community/mathlib/pull/2388))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-11 09:58:09](https://github.com/leanprover-community/mathlib/commit/81d8104)
feat(actions): manage labels on PR review ([#2387](https://github.com/leanprover-community/mathlib/pull/2387))
Github actions will now add "ready-to-merge" to PRs that are approved by writing "bors r+" / "bors merge" in a PR reviews. It will also remove the "request-review" label, if present.
#### Estimated changes
Renamed .github/workflows/add_label.yml to .github/workflows/add_label_from_comment.yml


Created .github/workflows/add_label_from_review.yml




## [2020-04-11 09:58:07](https://github.com/leanprover-community/mathlib/commit/c68f23d)
chore(category_theory/types): add documentation, remove bad simp lemmas and instances, add notation for functions as morphisms ([#2383](https://github.com/leanprover-community/mathlib/pull/2383))
* Add module doc and doc strings for `src/category_theory/types.lean`.
* Remove some bad simp lemmas and instances in that file and `src/category_theory/category/default.lean`.
* Add a notation `↾f` which enables Lean to see a function `f : α → β` as a morphism `α ⟶ β` in the category of types.
#### Estimated changes
Modified src/algebra/category/Group/adjunctions.lean


Modified src/category_theory/category/default.lean
- \+ *lemma* epi_comp
- \+ *lemma* mono_comp

Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/types.lean
- \+/\- *lemma* types_hom
- \+/\- *lemma* types_id
- \+/\- *lemma* types_comp
- \+ *lemma* types_id_apply
- \+ *lemma* types_comp_apply
- \+ *lemma* map_comp_apply
- \+ *lemma* map_id_apply
- \- *lemma* map_comp
- \- *lemma* map_id

Modified src/category_theory/yoneda.lean


Modified src/topology/metric_space/lipschitz.lean




## [2020-04-11 09:58:05](https://github.com/leanprover-community/mathlib/commit/00b510e)
perf(data/*): add inline attributes ([#2380](https://github.com/leanprover-community/mathlib/pull/2380))
This is part of an effort to bring `rewrite_search` to mathlib. Depends on [#2375](https://github.com/leanprover-community/mathlib/pull/2375).
#### Estimated changes
Modified src/data/list/basic.lean


Modified src/data/option/defs.lean




## [2020-04-11 09:58:03](https://github.com/leanprover-community/mathlib/commit/690643a)
fix(tactic/equiv_rw): don't use `subst` unnecessarily ([#2334](https://github.com/leanprover-community/mathlib/pull/2334))
This removes an unnecessary `subst` from the algorithm in `equiv_rw`, which was responsible for inserting `eq.rec`'s in data terms.
#### Estimated changes
Modified src/tactic/cache.lean


Modified src/tactic/equiv_rw.lean


Modified test/equiv_rw.lean




## [2020-04-11 07:17:19](https://github.com/leanprover-community/mathlib/commit/8556499)
feat(category_theory): make defining groupoids easier ([#2360](https://github.com/leanprover-community/mathlib/pull/2360))
The point of this PR is to lower the burden of proof in showing that a category is a groupoid. Rather than constructing well-defined two-sided inverses everywhere, with `groupoid.of_trunc_split_mono` you'll only need to show that every morphism has some retraction. This makes defining the free groupoid painless. There the retractions are defined by recursion on a quotient, so this saves the work of showing that all the retractions agree.
I used `trunc` instead of `nonempty` to avoid choice / noncomputability.
I don't understand why the @'s are needed: it seems Lean doesn't know what category structure C has without specifying it?
#### Estimated changes
Modified src/category_theory/epi_mono.lean
- \+ *def* is_iso.of_mono_retraction
- \+ *def* is_iso.of_epi_section

Modified src/category_theory/groupoid.lean
- \+ *def* groupoid.of_is_iso
- \+ *def* groupoid.of_trunc_split_mono

Modified src/tactic/basic.lean




## [2020-04-11 04:27:56](https://github.com/leanprover-community/mathlib/commit/597704a)
chore(*): switch to lean 3.8.0 ([#2361](https://github.com/leanprover-community/mathlib/pull/2361))
Switch to Lean 3.8.
#### Estimated changes
Modified archive/sensitivity.lean


Modified docs/tutorial/category_theory/intro.lean


Modified leanpkg.toml


Modified src/algebra/archimedean.lean


Modified src/algebra/big_operators.lean


Modified src/algebra/category/CommRing/colimits.lean


Modified src/algebra/category/Group/colimits.lean


Modified src/algebra/category/Module/basic.lean
- \+/\- *def* of

Modified src/algebra/category/Mon/colimits.lean


Modified src/algebra/char_p.lean


Modified src/algebra/char_zero.lean


Modified src/algebra/direct_limit.lean


Modified src/algebra/euclidean_domain.lean


Modified src/algebra/field.lean


Modified src/algebra/group/anti_hom.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group_power.lean


Modified src/algebra/group_with_zero.lean


Modified src/algebra/homology/homology.lean


Modified src/algebra/lie_algebra.lean


Modified src/algebra/module.lean
- \+/\- *theorem* zero_smul

Modified src/algebra/order_functions.lean
- \+/\- *lemma* min_add
- \+/\- *lemma* min_sub
- \+/\- *theorem* abs_le_abs

Modified src/algebra/ordered_group.lean
- \+/\- *lemma* neg_neg_iff_pos
- \+ *def* to_decidable_linear_ordered_add_comm_group
- \- *def* to_decidable_linear_ordered_comm_group

Modified src/algebra/ordered_ring.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/punit_instances.lean


Modified src/algebra/ring.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/mean_value.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/normed_space/basic.lean


Modified src/category/basic.lean


Modified src/category/equiv_functor.lean


Modified src/category/monad/writer.lean


Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/concrete_category/basic.lean


Modified src/category_theory/concrete_category/unbundled_hom.lean


Modified src/category_theory/core.lean


Modified src/category_theory/endomorphism.lean


Modified src/category_theory/epi_mono.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/fully_faithful.lean


Modified src/category_theory/functor.lean


Modified src/category_theory/functor_category.lean


Modified src/category_theory/functorial.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/limits.lean
- \+/\- *def* limit.cone
- \+/\- *def* colimit.cocone

Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/images.lean
- \+/\- *def* image.mono_factorisation
- \+/\- *def* image.is_image

Modified src/category_theory/limits/shapes/kernels.lean


Modified src/category_theory/limits/shapes/regular_mono.lean


Modified src/category_theory/limits/shapes/zero.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/algebra.lean


Modified src/category_theory/monad/basic.lean


Modified src/category_theory/monad/limits.lean


Modified src/category_theory/monad/types.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/shift.lean
- \+/\- *def* shift

Modified src/computability/primrec.lean


Modified src/computability/turing_machine.lean


Modified src/data/equiv/denumerable.lean


Modified src/data/equiv/encodable.lean


Modified src/data/fin_enum.lean


Modified src/data/finset.lean


Modified src/data/finsupp.lean


Modified src/data/fintype/basic.lean


Modified src/data/holor.lean


Modified src/data/list/basic.lean
- \+/\- *lemma* length_pos_of_sum_pos
- \+/\- *lemma* exists_lt_of_sum_lt
- \+/\- *lemma* exists_le_of_sum_le

Modified src/data/list/defs.lean


Modified src/data/list/forall2.lean


Modified src/data/list/min_max.lean


Modified src/data/list/perm.lean


Modified src/data/matrix/pequiv.lean


Modified src/data/mllist.lean


Modified src/data/monoid_algebra.lean


Modified src/data/multiset.lean


Modified src/data/mv_polynomial.lean


Modified src/data/nat/basic.lean


Modified src/data/num/lemmas.lean


Modified src/data/option/defs.lean


Modified src/data/polynomial.lean


Modified src/data/prod.lean
- \+ *lemma* map_mk
- \+/\- *lemma* map_fst
- \+/\- *lemma* map_snd

Modified src/data/rat/meta_defs.lean


Modified src/data/rat/order.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/nnreal.lean
- \+/\- *lemma* inv_inv

Modified src/data/seq/wseq.lean


Modified src/data/set/basic.lean


Modified src/data/set/function.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/set/intervals/unordered_interval.lean


Modified src/data/sum.lean


Modified src/data/tree.lean


Modified src/data/zmod/basic.lean


Modified src/data/zsqrtd/basic.lean


Modified src/deprecated/group.lean


Modified src/field_theory/perfect_closure.lean


Modified src/field_theory/subfield.lean


Modified src/geometry/manifold/manifold.lean


Modified src/geometry/manifold/mfderiv.lean


Modified src/group_theory/congruence.lean


Modified src/group_theory/free_group.lean


Modified src/group_theory/group_action.lean
- \+/\- *theorem* one_smul

Modified src/group_theory/order_of_element.lean


Modified src/group_theory/subgroup.lean


Modified src/group_theory/submonoid.lean


Modified src/group_theory/sylow.lean


Modified src/linear_algebra/basis.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/linear_action.lean


Modified src/logic/relation.lean


Modified src/measure_theory/borel_space.lean


Modified src/measure_theory/l1_space.lean


Modified src/measure_theory/measurable_space.lean


Modified src/measure_theory/measure_space.lean


Modified src/measure_theory/simple_func_dense.lean


Modified src/meta/expr.lean


Modified src/order/basic.lean


Modified src/order/bounded_lattice.lean


Modified src/order/conditionally_complete_lattice.lean


Modified src/order/filter/basic.lean


Modified src/order/filter/extr.lean


Modified src/order/filter/filter_product.lean
- \+/\- *lemma* abs_def
- \+/\- *lemma* of_abs

Modified src/order/lattice.lean


Modified src/order/lexicographic.lean


Modified src/order/pilex.lean


Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra.lean


Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/maps.lean


Modified src/ring_theory/polynomial.lean


Modified src/ring_theory/principal_ideal_domain.lean


Modified src/ring_theory/subring.lean


Modified src/set_theory/cofinality.lean


Modified src/set_theory/game.lean
- \+ *def* ordered_add_comm_group_game
- \- *def* ordered_comm_group_game

Modified src/set_theory/lists.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/surreal.lean


Modified src/tactic/ext.lean


Modified src/tactic/lift.lean


Modified src/tactic/norm_num.lean
- \+/\- *lemma* lt_add_of_pos_helper

Modified src/tactic/ring_exp.lean


Modified src/topology/algebra/continuous_functions.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/module.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/algebra/open_subgroup.lean


Modified src/topology/algebra/ordered.lean
- \+/\- *lemma* tendsto_abs_at_top_at_top

Modified src/topology/algebra/uniform_group.lean


Modified src/topology/bases.lean


Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean


Modified src/topology/local_extr.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean


Modified src/topology/metric_space/hausdorff_distance.lean


Modified src/topology/metric_space/isometry.lean


Modified src/topology/order.lean


Modified src/topology/sheaves/presheaf_of_functions.lean


Modified src/topology/subset_properties.lean


Modified test/coinductive.lean


Modified test/delta_instance.lean


Modified test/monotonicity/test_cases.lean


Modified test/tactics.lean
- \+/\- *def* dummy
- \+/\- *def* wrong_param
- \+/\- *def* right_param

Modified test/traversable.lean


Modified test/trunc_cases.lean
- \+/\- *def* u



## [2020-04-10 20:56:06](https://github.com/leanprover-community/mathlib/commit/ebdeb3b)
chore(scripts): update nolints.txt ([#2386](https://github.com/leanprover-community/mathlib/pull/2386))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-10 18:03:50](https://github.com/leanprover-community/mathlib/commit/29080c8)
feat(data/list/range): add sum lemmas ([#2385](https://github.com/leanprover-community/mathlib/pull/2385))
Adding the proof that left and right multiplication in a ring commute with list sum.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *theorem* map_sub
- \- *theorem* add_monoid_hom.map_sub
- \+ *def* mul_left
- \+ *def* mul_right

Modified src/data/list/basic.lean
- \+ *theorem* prod_map_hom
- \+ *theorem* sum_map_mul_left
- \+ *theorem* sum_map_mul_right

Modified src/data/list/range.lean
- \+ *theorem* prod_range_succ'



## [2020-04-10 18:03:48](https://github.com/leanprover-community/mathlib/commit/61fa489)
feat(tactic/trunc_cases): a tactic for case analysis on trunc hypotheses ([#2368](https://github.com/leanprover-community/mathlib/pull/2368))
```
/--
Perform case analysis on a `trunc` expression, 
preferentially using the recursor `trunc.rec_on_subsingleton` 
when the goal is a subsingleton, 
and using `trunc.rec` otherwise.
Additionally, if the new hypothesis is a type class, 
reset the instance cache.
-/
```
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/equiv_rw.lean


Modified src/tactic/finish.lean


Modified src/tactic/interval_cases.lean


Created src/tactic/trunc_cases.lean


Created test/trunc_cases.lean
- \+ *lemma* eq_rec_prod
- \+ *def* u



## [2020-04-10 15:39:37](https://github.com/leanprover-community/mathlib/commit/3cc7a32)
feat(order/complete_lattice): add a constructor from `partial_order` and `Inf` ([#2359](https://github.com/leanprover-community/mathlib/pull/2359))
Also use `∃!` in `data/setoid`.
#### Estimated changes
Modified src/data/setoid.lean
- \+/\- *lemma* eq_of_mem_eqv_class
- \+ *lemma* rel_iff_exists_classes
- \+/\- *lemma* classes_eqv_classes
- \+/\- *lemma* eqv_class_mem
- \+/\- *lemma* eqv_classes_disjoint
- \- *lemma* Inf_le
- \- *lemma* le_Inf
- \+/\- *def* mk_classes

Modified src/group_theory/congruence.lean
- \+/\- *lemma* con_gen_of_con
- \- *lemma* le_Inf
- \- *lemma* Inf_le

Modified src/order/bounded_lattice.lean


Modified src/order/bounds.lean
- \+/\- *lemma* upper_bounds_singleton
- \+/\- *lemma* lower_bounds_singleton
- \+/\- *lemma* upper_bounds_insert
- \+/\- *lemma* lower_bounds_insert

Modified src/order/complete_lattice.lean
- \+ *def* complete_lattice_of_Inf



## [2020-04-10 13:48:32](https://github.com/leanprover-community/mathlib/commit/5169595)
chore(tactic/omega): add trace.omega option to show internal representation ([#2377](https://github.com/leanprover-community/mathlib/pull/2377))
This is helpful when debugging issues such as [#2376](https://github.com/leanprover-community/mathlib/pull/2376) and [#1484](https://github.com/leanprover-community/mathlib/pull/1484).
#### Estimated changes
Modified src/tactic/omega/int/main.lean


Modified src/tactic/omega/main.lean


Modified src/tactic/omega/nat/main.lean




## [2020-04-10 13:48:30](https://github.com/leanprover-community/mathlib/commit/bf8f25a)
feat(algebra/lie_algebra): quotients of Lie modules are Lie modules ([#2335](https://github.com/leanprover-community/mathlib/pull/2335))
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+ *lemma* lie_quotient_action_apply
- \+ *def* lie_submodule_invariant

Modified src/linear_algebra/basic.lean
- \+ *lemma* comap_le_comap_smul
- \+ *lemma* inf_comap_le_comap_add
- \+ *def* compatible_maps
- \+ *def* mapq_linear



## [2020-04-10 12:54:03](https://github.com/leanprover-community/mathlib/commit/1a099b3)
chore(scripts): update nolints.txt ([#2381](https://github.com/leanprover-community/mathlib/pull/2381))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-10 12:54:02](https://github.com/leanprover-community/mathlib/commit/a714245)
feat(group_theory/order_of_element): order_of_dvd_iff_pow_eq_one ([#2364](https://github.com/leanprover-community/mathlib/pull/2364))
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* order_of_dvd_iff_pow_eq_one



## [2020-04-10 11:53:26](https://github.com/leanprover-community/mathlib/commit/55814dc)
fix(.github/workflows/add_label): add missing outputs ([#2379](https://github.com/leanprover-community/mathlib/pull/2379))
I hope this fixes the `add_label` workflow.
#### Estimated changes
Modified .github/workflows/add_label.yml




## [2020-04-10 11:53:24](https://github.com/leanprover-community/mathlib/commit/808fa8d)
chore(.github): remove linebreaks from pull request template ([#2378](https://github.com/leanprover-community/mathlib/pull/2378))
github treats a newline in the markdown text as a linebreak.
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md




## [2020-04-10 10:19:59](https://github.com/leanprover-community/mathlib/commit/e758263)
refactor(ring_theory/algebra): use bundled homs, allow semirings ([#2303](https://github.com/leanprover-community/mathlib/pull/2303))
Fixes [#2297](https://github.com/leanprover-community/mathlib/pull/2297)
Build fails because of some class instance problems, asked [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Need.20help.20with.20class.20instance.20resolution), no answer yet.
#### Estimated changes
Modified src/algebra/lie_algebra.lean


Modified src/analysis/normed_space/basic.lean


Modified src/data/matrix/basic.lean


Modified src/data/mv_polynomial.lean
- \+/\- *lemma* aeval_C
- \+/\- *theorem* aeval_def

Modified src/data/padics/padic_integers.lean


Modified src/data/polynomial.lean
- \+ *lemma* coe_eval₂_ring_hom
- \+/\- *lemma* map_map
- \+/\- *lemma* map_id
- \+/\- *lemma* degree_map_le
- \+/\- *lemma* degree_map_eq_of_leading_coeff_ne_zero
- \+/\- *lemma* monic_map
- \+/\- *lemma* map_injective
- \+/\- *lemma* map_sub
- \+/\- *lemma* map_neg
- \+/\- *lemma* aeval_C
- \+/\- *lemma* map_mod_div_by_monic
- \+/\- *lemma* map_div_by_monic
- \+/\- *lemma* map_mod_by_monic
- \+/\- *lemma* degree_map
- \+/\- *lemma* nat_degree_map
- \+/\- *lemma* leading_coeff_map
- \+/\- *lemma* map_div
- \+/\- *lemma* map_mod
- \+/\- *lemma* map_eq_zero
- \+/\- *theorem* aeval_def
- \+ *def* eval₂_ring_hom

Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/splitting_field.lean
- \+/\- *lemma* splits_map_iff
- \+/\- *lemma* splits_of_splits_id
- \+/\- *lemma* splits_comp_of_splits

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* eval₂_root
- \+/\- *lemma* is_root_root

Modified src/ring_theory/algebra.lean
- \+/\- *lemma* smul_def''
- \+/\- *lemma* smul_def
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+/\- *lemma* to_linear_map_apply
- \+/\- *lemma* comp_to_linear_map
- \+/\- *lemma* range_le
- \+/\- *lemma* map_eq_self
- \- *lemma* map_add
- \- *lemma* map_mul
- \- *lemma* map_zero
- \- *lemma* map_one
- \- *lemma* id_to_linear_map
- \+/\- *theorem* commutes
- \+/\- *theorem* left_comm
- \+/\- *theorem* ext
- \+ *theorem* comp_algebra_map
- \+/\- *theorem* to_linear_map_inj
- \+/\- *theorem* to_comap_apply
- \+/\- *theorem* of_id_apply
- \+/\- *theorem* mem_bot
- \+/\- *def* algebra_map
- \+ *def* ring_hom.to_algebra
- \+/\- *def* to_linear_map
- \+/\- *def* comap
- \+/\- *def* comap.to_comap
- \+/\- *def* comap.of_comap
- \+/\- *def* of_id
- \- *def* of_ring_hom

Modified src/ring_theory/algebraic.lean


Modified src/ring_theory/integral_closure.lean
- \+/\- *theorem* is_integral_algebra_map

Modified src/ring_theory/localization.lean


Modified src/ring_theory/power_series.lean


Modified src/topology/algebra/module.lean


Modified src/topology/metric_space/isometry.lean




## [2020-04-10 07:02:46](https://github.com/leanprover-community/mathlib/commit/f723f37)
feat(ci): switch from mergify to bors ([#2322](https://github.com/leanprover-community/mathlib/pull/2322))
This PR (joint work with @gebner) changes the automation that merges our PRs from mergify to a service called [bors](https://bors.tech/). Currently, the "time-to-master" of an approved PR grows linearly with the number of currently queued PRs, since mergify builds PRs against master one at a time. bors batches approved PRs together before building them against master so that most PRs should merge within 2*(current build time).
As far as day-to-day use goes, the main difference is that maintainers will approve PRs by commenting with the magic words "`bors r+`" instead of "approving" on Github and adding the "ready-to-merge" label. Contributors should be aware that pushing additional commits to an approved PR will now require a new approval.
Some longer notes on bors and mathlib can be found [here](https://github.com/leanprover-community/mathlib/blob/2ea15d65c32574aaf513e27feb24424354340eea/docs/contribute/bors.md).
#### Estimated changes
Modified .github/PULL_REQUEST_TEMPLATE.md


Created .github/workflows/add_label.yml


Modified .github/workflows/build.yml


Deleted .mergify.yml


Modified README.md


Created bors.toml


Created docs/contribute/bors.md


Modified docs/contribute/index.md


Modified scripts/fetch_olean_cache.sh


Deleted scripts/look_up_olean_hash.py


Modified scripts/update_nolints.sh


Deleted scripts/write_azure_table_entry.py
- \- *def* add_entry(file_hash,



## [2020-04-10 06:01:10](https://github.com/leanprover-community/mathlib/commit/495deb9)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-10 05:27:11](https://github.com/leanprover-community/mathlib/commit/6152d45)
refactor(field_theory/perfect_closure): use bundled homs, review ([#2357](https://github.com/leanprover-community/mathlib/pull/2357))
* refactor(field_theory/perfect_closure): use bundled homs, review
Also add lemmas like `monoid_hom.iterate_map_mul`.
* Fix a typo spotted by `lint`
* Apply suggestions from code review
Co-Authored-By: Johan Commelin <johan@commelin.net>
#### Estimated changes
Modified src/algebra/char_p.lean
- \+/\- *theorem* frobenius_def
- \+/\- *theorem* frobenius_mul
- \+/\- *theorem* frobenius_one
- \+ *theorem* monoid_hom.map_frobenius
- \+ *theorem* ring_hom.map_frobenius
- \+ *theorem* monoid_hom.map_iterate_frobenius
- \+ *theorem* ring_hom.map_iterate_frobenius
- \+ *theorem* monoid_hom.iterate_map_frobenius
- \+ *theorem* ring_hom.iterate_map_frobenius
- \+/\- *theorem* frobenius_zero
- \+/\- *theorem* frobenius_add
- \+/\- *theorem* frobenius_neg
- \+/\- *theorem* frobenius_sub
- \+/\- *theorem* frobenius_nat_cast
- \+/\- *theorem* frobenius_inj
- \- *theorem* is_monoid_hom.map_frobenius
- \+/\- *def* frobenius

Modified src/algebra/group_power.lean
- \+ *lemma* map_pow
- \+ *lemma* iterate_map_pow
- \+ *lemma* iterate_map_smul
- \- *lemma* ring_hom.map_pow
- \+ *theorem* monoid_hom.iterate_map_pow
- \+ *theorem* add_monoid_hom.iterate_map_smul

Modified src/data/nat/basic.lean
- \+ *theorem* iterate_map_one
- \+ *theorem* iterate_map_mul
- \+ *theorem* iterate_map_inv
- \+ *theorem* iterate_map_sub
- \+ *theorem* iterate_map_zero
- \+ *theorem* iterate_map_add
- \+ *theorem* iterate_map_neg

Modified src/field_theory/perfect_closure.lean
- \+ *lemma* coe_frobenius_equiv
- \+ *lemma* quot_mk_eq_mk
- \+ *lemma* lift_on_mk
- \+ *lemma* induction_on
- \+ *lemma* mk_mul_mk
- \+ *lemma* one_def
- \+ *lemma* mk_add_mk
- \+ *lemma* neg_mk
- \+ *lemma* zero_def
- \+ *lemma* of_apply
- \+/\- *theorem* frobenius_pth_root
- \+/\- *theorem* pth_root_frobenius
- \+ *theorem* eq_pth_root_iff
- \+ *theorem* pth_root_eq_iff
- \+ *theorem* monoid_hom.map_pth_root
- \+ *theorem* monoid_hom.map_iterate_pth_root
- \+ *theorem* ring_hom.map_pth_root
- \+ *theorem* ring_hom.map_iterate_pth_root
- \+/\- *theorem* mk_zero
- \+/\- *theorem* r.sound
- \+/\- *theorem* eq_iff'
- \+/\- *theorem* nat_cast
- \+/\- *theorem* int_cast
- \+/\- *theorem* nat_cast_eq_iff
- \+/\- *theorem* frobenius_mk
- \+/\- *theorem* eq_iff
- \+/\- *theorem* eq_pth_root
- \- *theorem* is_ring_hom.pth_root
- \- *theorem* frobenius_equiv_apply
- \+/\- *def* frobenius_equiv
- \+ *def* pth_root
- \+/\- *def* perfect_closure
- \+ *def* mk
- \+ *def* lift_on
- \+/\- *def* of
- \+ *def* lift
- \- *def* UMP



## [2020-04-10 02:46:37](https://github.com/leanprover-community/mathlib/commit/b15c213)
chore(*): replace uses of `---` delimiter in tactic docs ([#2372](https://github.com/leanprover-community/mathlib/pull/2372))
* update abel doc string
the tactic doc entry seems completely fine as the doc string,
I don't know why these were separated
* replace uses of --- in docs
#### Estimated changes
Modified src/tactic/abel.lean


Modified src/tactic/clear.lean


Modified src/tactic/doc_commands.lean
- \+/\- *def* f

Modified src/tactic/hint.lean


Modified src/tactic/interval_cases.lean


Modified src/tactic/linarith.lean


Modified src/tactic/omega/main.lean


Modified src/tactic/reassoc_axiom.lean
- \+/\- *theorem* category_theory.reassoc_of

Modified src/tactic/rename.lean


Modified src/tactic/rename_var.lean


Modified src/tactic/suggest.lean


Modified src/tactic/tauto.lean


Modified src/tactic/tfae.lean




## [2020-04-09 23:56:46](https://github.com/leanprover-community/mathlib/commit/19e1a96)
doc(add_tactic_doc): slight improvement to docs ([#2365](https://github.com/leanprover-community/mathlib/pull/2365))
* doc(add_tactic_doc): slight improvement to docs
* Update docs/contribute/doc.md
Co-Authored-By: Yury G. Kudryashov <urkud@urkud.name>
* sentence
* update add_tactic_doc doc entry
#### Estimated changes
Modified docs/contribute/doc.md


Modified src/tactic/doc_commands.lean




## [2020-04-09 21:05:16](https://github.com/leanprover-community/mathlib/commit/4a1dc42)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-09 20:31:33](https://github.com/leanprover-community/mathlib/commit/6a7db27)
feat(tactic/ring_exp) allow ring_exp inside of conv blocks ([#2369](https://github.com/leanprover-community/mathlib/pull/2369))
* allow ring_exp inside of conv blocks
* Update test/ring_exp.lean
* Update test/ring_exp.lean
* Update test/ring_exp.lean
* add docstrings
#### Estimated changes
Modified src/tactic/doc_commands.lean


Modified src/tactic/ring.lean


Modified src/tactic/ring_exp.lean


Modified test/ring_exp.lean




## [2020-04-09 17:41:23](https://github.com/leanprover-community/mathlib/commit/d240f38)
feat(tactic/simp_result): tactics for simplifying the results of other tactics ([#2356](https://github.com/leanprover-community/mathlib/pull/2356))
* feat(tactic/simp_result): tactics for simplifying the results of other tactics
* word
* better tests
* order of arguments
* Revert "order of arguments"
This reverts commit 38cfec6867459fcc4c5ef2d41f5313a5b0466c53.
* fix add_tactic_doc
* slightly robustify testing
* improve documentation
#### Estimated changes
Created src/tactic/simp_result.lean


Created test/simp_result.lean




## [2020-04-09 12:44:49](https://github.com/leanprover-community/mathlib/commit/63fc23a)
feat(data/list): chain_iff_nth_le ([#2354](https://github.com/leanprover-community/mathlib/pull/2354))
* feat(data/list): chain_iff_nth_le
* Update src/data/list/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* move
* fix
#### Estimated changes
Modified src/data/list/chain.lean
- \+ *theorem* chain_iff_nth_le
- \+ *theorem* chain'_iff_nth_le

Modified src/data/nat/basic.lean
- \+ *lemma* lt_of_lt_pred



## [2020-04-09 10:08:54](https://github.com/leanprover-community/mathlib/commit/bda8a05)
doc(docs/extras/tactic_writing) add cheap method ([#2198](https://github.com/leanprover-community/mathlib/pull/2198))
* doc(docs/extras/tactic_writing) add cheap method
About 50% of my personal use cases for writing tactics are just because I want a simple way of stringing several tactics together, so I propose adding this so I will know where to look when I realise I can't remember the syntax.
* style fixes
* Update tactic_writing.md
* Update tactic_writing.md
* Update docs/extras/tactic_writing.md
#### Estimated changes
Modified docs/extras/tactic_writing.md




## [2020-04-09 09:03:53](https://github.com/leanprover-community/mathlib/commit/a8797ce)
feat(data/set/basic): add lemmata ([#2353](https://github.com/leanprover-community/mathlib/pull/2353))
* feat(data/set/basic): add lemmata
* switch to term mode proof
* removing dupe
* make linter happy
* Update src/data/set/basic.lean
Co-Authored-By: sgouezel <sebastien.gouezel@univ-rennes1.fr>
* change proof
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* mem_compl_singleton_iff
- \+ *lemma* subset_compl_singleton_iff
- \+ *lemma* exists_range_iff'



## [2020-04-09 06:10:23](https://github.com/leanprover-community/mathlib/commit/80d3ed8)
fix(algebra/euclidean_domain): remove decidable_eq assumption ([#2362](https://github.com/leanprover-community/mathlib/pull/2362))
This PR removes the `decidable_eq` assumption on the `field.to_euclidean_domain` instance.  Decidable equality was only used to define the remainder with an if-then-else, but this can also be done by exploiting the fact that `0⁻¹ = 0`.
The current instance is a bit problematic since it can cause `a + b : ℝ` to be noncomputable if type-class inference happens to choose the wrong instance (going through `euclidean_domain` instead of "directly" through some kind of ring).
#### Estimated changes
Modified src/algebra/euclidean_domain.lean




## [2020-04-09 03:16:05](https://github.com/leanprover-community/mathlib/commit/67b121e)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-09 02:50:30](https://github.com/leanprover-community/mathlib/commit/fbc9592)
chore(data/list): move some sections to separate files ([#2341](https://github.com/leanprover-community/mathlib/pull/2341))
* move list.func namespace to its own file
* move erase_dup to its own file
* move rotate to its own file
* move tfae to its own file
* move bag_inter and intervals
* move range out
* move nodup
* move chain and pairwise
* move zip
* move forall2
* move of_fn
* add copyright headers
* remove unnecessary sections, move defns to func.set and tfae
* fixes
* oops, forgot to add file
#### Estimated changes
Modified src/category/traversable/instances.lean


Modified src/data/int/basic.lean


Created src/data/list/antidiagonal.lean
- \+ *lemma* mem_antidiagonal
- \+ *lemma* length_antidiagonal
- \+ *lemma* antidiagonal_zero
- \+ *lemma* nodup_antidiagonal
- \+ *def* antidiagonal

Created src/data/list/bag_inter.lean
- \+ *theorem* nil_bag_inter
- \+ *theorem* bag_inter_nil
- \+ *theorem* cons_bag_inter_of_pos
- \+ *theorem* cons_bag_inter_of_neg
- \+ *theorem* mem_bag_inter
- \+ *theorem* count_bag_inter
- \+ *theorem* bag_inter_sublist_left
- \+ *theorem* bag_inter_nil_iff_inter_nil

Modified src/data/list/basic.lean
- \+/\- *lemma* choose_spec
- \+/\- *lemma* choose_mem
- \+/\- *lemma* choose_property
- \- *lemma* forall₂.mp
- \- *lemma* forall₂.flip
- \- *lemma* forall₂_same
- \- *lemma* forall₂_refl
- \- *lemma* forall₂_eq_eq_eq
- \- *lemma* forall₂_nil_left_iff
- \- *lemma* forall₂_nil_right_iff
- \- *lemma* forall₂_cons_left_iff
- \- *lemma* forall₂_cons_right_iff
- \- *lemma* forall₂_and_left
- \- *lemma* forall₂_map_left_iff
- \- *lemma* forall₂_map_right_iff
- \- *lemma* left_unique_forall₂
- \- *lemma* right_unique_forall₂
- \- *lemma* bi_unique_forall₂
- \- *lemma* rel_mem
- \- *lemma* rel_map
- \- *lemma* rel_append
- \- *lemma* rel_join
- \- *lemma* rel_bind
- \- *lemma* rel_foldl
- \- *lemma* rel_foldr
- \- *lemma* rel_filter
- \- *lemma* rel_filter_map
- \- *lemma* rel_prod
- \- *lemma* rel_sections
- \- *lemma* forall_of_pairwise
- \- *lemma* rel_nodup
- \- *lemma* nodup_sublists_len
- \- *lemma* diff_eq_filter_of_nodup
- \- *lemma* mem_diff_iff_of_nodup
- \- *lemma* nodup_update_nth
- \- *lemma* mem_fin_range
- \- *lemma* nodup_fin_range
- \- *lemma* length_fin_range
- \- *lemma* append_consecutive
- \- *lemma* inter_consecutive
- \- *lemma* bag_inter_consecutive
- \- *lemma* filter_lt_of_top_le
- \- *lemma* filter_lt_of_le_bot
- \- *lemma* filter_lt_of_ge
- \- *lemma* filter_lt
- \- *lemma* filter_le_of_le_bot
- \- *lemma* filter_le_of_top_le
- \- *lemma* filter_le_of_le
- \- *lemma* filter_le
- \- *lemma* trichotomy
- \- *lemma* nth_le_range
- \- *lemma* rotate_mod
- \- *lemma* rotate_nil
- \- *lemma* rotate_zero
- \- *lemma* rotate'_nil
- \- *lemma* rotate'_zero
- \- *lemma* rotate'_cons_succ
- \- *lemma* length_rotate'
- \- *lemma* rotate'_eq_take_append_drop
- \- *lemma* rotate'_rotate'
- \- *lemma* rotate'_length
- \- *lemma* rotate'_length_mul
- \- *lemma* rotate'_mod
- \- *lemma* rotate_eq_rotate'
- \- *lemma* rotate_cons_succ
- \- *lemma* mem_rotate
- \- *lemma* length_rotate
- \- *lemma* rotate_eq_take_append_drop
- \- *lemma* rotate_rotate
- \- *lemma* rotate_length
- \- *lemma* rotate_length_mul
- \- *lemma* prod_rotate_eq_one_of_prod_eq_one
- \- *lemma* length_set
- \- *lemma* get_nil
- \- *lemma* get_eq_default_of_le
- \- *lemma* get_set
- \- *lemma* eq_get_of_mem
- \- *lemma* mem_get_of_le
- \- *lemma* mem_get_of_ne_zero
- \- *lemma* get_set_eq_of_ne
- \- *lemma* get_map
- \- *lemma* get_map'
- \- *lemma* forall_val_of_forall_mem
- \- *lemma* equiv_refl
- \- *lemma* equiv_symm
- \- *lemma* equiv_trans
- \- *lemma* equiv_of_eq
- \- *lemma* eq_of_equiv
- \- *lemma* get_neg
- \- *lemma* length_neg
- \- *lemma* nil_pointwise
- \- *lemma* pointwise_nil
- \- *lemma* get_pointwise
- \- *lemma* length_pointwise
- \- *lemma* get_add
- \- *lemma* length_add
- \- *lemma* nil_add
- \- *lemma* add_nil
- \- *lemma* map_add_map
- \- *lemma* get_sub
- \- *lemma* length_sub
- \- *lemma* nil_sub
- \- *lemma* sub_nil
- \- *lemma* mem_antidiagonal
- \- *lemma* length_antidiagonal
- \- *lemma* antidiagonal_zero
- \- *lemma* nodup_antidiagonal
- \- *theorem* forall₂_cons
- \- *theorem* forall₂.imp
- \- *theorem* forall₂_length_eq
- \- *theorem* forall₂_zip
- \- *theorem* forall₂_iff_zip
- \- *theorem* forall₂_take
- \- *theorem* forall₂_drop
- \- *theorem* forall₂_take_append
- \- *theorem* forall₂_drop_append
- \- *theorem* filter_map_cons
- \- *theorem* mem_sections
- \- *theorem* mem_sections_length
- \- *theorem* zip_cons_cons
- \- *theorem* zip_nil_left
- \- *theorem* zip_nil_right
- \- *theorem* zip_swap
- \- *theorem* length_zip
- \- *theorem* zip_append
- \- *theorem* zip_map
- \- *theorem* zip_map_left
- \- *theorem* zip_map_right
- \- *theorem* zip_map'
- \- *theorem* mem_zip
- \- *theorem* unzip_nil
- \- *theorem* unzip_cons
- \- *theorem* unzip_eq_map
- \- *theorem* unzip_left
- \- *theorem* unzip_right
- \- *theorem* unzip_swap
- \- *theorem* zip_unzip
- \- *theorem* unzip_zip_left
- \- *theorem* unzip_zip_right
- \- *theorem* unzip_zip
- \- *theorem* length_revzip
- \- *theorem* unzip_revzip
- \- *theorem* revzip_map_fst
- \- *theorem* revzip_map_snd
- \- *theorem* reverse_revzip
- \- *theorem* revzip_swap
- \- *theorem* length_of_fn_aux
- \- *theorem* length_of_fn
- \- *theorem* nth_of_fn_aux
- \- *theorem* nth_of_fn
- \- *theorem* nth_le_of_fn
- \- *theorem* array_eq_of_fn
- \- *theorem* of_fn_zero
- \- *theorem* of_fn_succ
- \- *theorem* of_fn_nth_le
- \- *theorem* nil_bag_inter
- \- *theorem* bag_inter_nil
- \- *theorem* cons_bag_inter_of_pos
- \- *theorem* cons_bag_inter_of_neg
- \- *theorem* mem_bag_inter
- \- *theorem* count_bag_inter
- \- *theorem* bag_inter_sublist_left
- \- *theorem* bag_inter_nil_iff_inter_nil
- \- *theorem* rel_of_pairwise_cons
- \- *theorem* pairwise_of_pairwise_cons
- \- *theorem* pairwise.imp_of_mem
- \- *theorem* pairwise.imp
- \- *theorem* pairwise.and
- \- *theorem* pairwise.imp₂
- \- *theorem* pairwise.iff_of_mem
- \- *theorem* pairwise.iff
- \- *theorem* pairwise_of_forall
- \- *theorem* pairwise.and_mem
- \- *theorem* pairwise.imp_mem
- \- *theorem* pairwise_of_sublist
- \- *theorem* forall_of_forall_of_pairwise
- \- *theorem* pairwise_singleton
- \- *theorem* pairwise_pair
- \- *theorem* pairwise_append
- \- *theorem* pairwise_append_comm
- \- *theorem* pairwise_middle
- \- *theorem* pairwise_map
- \- *theorem* pairwise_of_pairwise_map
- \- *theorem* pairwise_map_of_pairwise
- \- *theorem* pairwise_filter_map
- \- *theorem* pairwise_filter_map_of_pairwise
- \- *theorem* pairwise_filter
- \- *theorem* pairwise_filter_of_pairwise
- \- *theorem* pairwise_join
- \- *theorem* pairwise_reverse
- \- *theorem* pairwise_iff_nth_le
- \- *theorem* pairwise_sublists'
- \- *theorem* pairwise_sublists
- \- *theorem* pw_filter_nil
- \- *theorem* pw_filter_cons_of_pos
- \- *theorem* pw_filter_cons_of_neg
- \- *theorem* pw_filter_map
- \- *theorem* pw_filter_sublist
- \- *theorem* pw_filter_subset
- \- *theorem* pairwise_pw_filter
- \- *theorem* pw_filter_eq_self
- \- *theorem* pw_filter_idempotent
- \- *theorem* forall_mem_pw_filter
- \- *theorem* rel_of_chain_cons
- \- *theorem* chain_of_chain_cons
- \- *theorem* chain.imp'
- \- *theorem* chain.imp
- \- *theorem* chain.iff
- \- *theorem* chain.iff_mem
- \- *theorem* chain_singleton
- \- *theorem* chain_split
- \- *theorem* chain_map
- \- *theorem* chain_of_chain_map
- \- *theorem* chain_map_of_chain
- \- *theorem* chain_of_pairwise
- \- *theorem* chain_iff_pairwise
- \- *theorem* chain'.imp
- \- *theorem* chain'.iff
- \- *theorem* chain'.iff_mem
- \- *theorem* chain'_nil
- \- *theorem* chain'_singleton
- \- *theorem* chain'_split
- \- *theorem* chain'_map
- \- *theorem* chain'_of_chain'_map
- \- *theorem* chain'_map_of_chain'
- \- *theorem* pairwise.chain'
- \- *theorem* chain'_iff_pairwise
- \- *theorem* chain'_cons
- \- *theorem* chain'.cons
- \- *theorem* chain'.tail
- \- *theorem* chain'_pair
- \- *theorem* chain'_reverse
- \- *theorem* forall_mem_ne
- \- *theorem* nodup_nil
- \- *theorem* nodup_cons
- \- *theorem* nodup_cons_of_nodup
- \- *theorem* nodup_singleton
- \- *theorem* nodup_of_nodup_cons
- \- *theorem* not_mem_of_nodup_cons
- \- *theorem* not_nodup_cons_of_mem
- \- *theorem* nodup_of_sublist
- \- *theorem* not_nodup_pair
- \- *theorem* nodup_iff_sublist
- \- *theorem* nodup_iff_nth_le_inj
- \- *theorem* nth_le_index_of
- \- *theorem* nodup_iff_count_le_one
- \- *theorem* nodup_repeat
- \- *theorem* count_eq_one_of_mem
- \- *theorem* nodup_of_nodup_append_left
- \- *theorem* nodup_of_nodup_append_right
- \- *theorem* nodup_append
- \- *theorem* disjoint_of_nodup_append
- \- *theorem* nodup_append_of_nodup
- \- *theorem* nodup_append_comm
- \- *theorem* nodup_middle
- \- *theorem* nodup_of_nodup_map
- \- *theorem* nodup_map_on
- \- *theorem* nodup_map
- \- *theorem* nodup_map_iff
- \- *theorem* nodup_attach
- \- *theorem* nodup_pmap
- \- *theorem* nodup_filter
- \- *theorem* nodup_reverse
- \- *theorem* nodup_erase_eq_filter
- \- *theorem* nodup_erase_of_nodup
- \- *theorem* nodup_diff
- \- *theorem* mem_erase_iff_of_nodup
- \- *theorem* mem_erase_of_nodup
- \- *theorem* nodup_join
- \- *theorem* nodup_bind
- \- *theorem* nodup_product
- \- *theorem* nodup_sigma
- \- *theorem* nodup_filter_map
- \- *theorem* nodup_concat
- \- *theorem* nodup_insert
- \- *theorem* nodup_union
- \- *theorem* nodup_inter_of_nodup
- \- *theorem* nodup_sublists
- \- *theorem* nodup_sublists'
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
- \- *theorem* length_range'
- \- *theorem* mem_range'
- \- *theorem* map_add_range'
- \- *theorem* map_sub_range'
- \- *theorem* chain_succ_range'
- \- *theorem* chain_lt_range'
- \- *theorem* pairwise_lt_range'
- \- *theorem* nodup_range'
- \- *theorem* range'_append
- \- *theorem* range'_sublist_right
- \- *theorem* range'_subset_right
- \- *theorem* nth_range'
- \- *theorem* range'_concat
- \- *theorem* range_core_range'
- \- *theorem* range_eq_range'
- \- *theorem* range_succ_eq_map
- \- *theorem* range'_eq_map_range
- \- *theorem* length_range
- \- *theorem* pairwise_lt_range
- \- *theorem* nodup_range
- \- *theorem* range_sublist
- \- *theorem* range_subset
- \- *theorem* mem_range
- \- *theorem* not_mem_range_self
- \- *theorem* nth_range
- \- *theorem* range_concat
- \- *theorem* iota_eq_reverse_range'
- \- *theorem* length_iota
- \- *theorem* pairwise_gt_iota
- \- *theorem* nodup_iota
- \- *theorem* mem_iota
- \- *theorem* reverse_range'
- \- *theorem* prod_range_succ
- \- *theorem* zero_bot
- \- *theorem* length
- \- *theorem* pairwise_lt
- \- *theorem* nodup
- \- *theorem* mem
- \- *theorem* eq_nil_of_le
- \- *theorem* map_add
- \- *theorem* map_sub
- \- *theorem* self_empty
- \- *theorem* eq_empty_iff
- \- *theorem* succ_singleton
- \- *theorem* succ_top
- \- *theorem* eq_cons
- \- *theorem* pred_singleton
- \- *theorem* chain'_succ
- \- *theorem* not_mem_top
- \- *theorem* enum_from_map_fst
- \- *theorem* enum_map_fst
- \- *theorem* of_fn_eq_pmap
- \- *theorem* nodup_of_fn
- \- *theorem* tfae_nil
- \- *theorem* tfae_singleton
- \- *theorem* tfae_cons_of_mem
- \- *theorem* tfae_cons_cons
- \- *theorem* tfae_of_forall
- \- *theorem* tfae_of_cycle
- \- *theorem* tfae.out
- \- *theorem* option.to_list_nodup
- \- *def* fin_range
- \- *def* Ico
- \- *def* antidiagonal

Created src/data/list/chain.lean
- \+ *theorem* rel_of_chain_cons
- \+ *theorem* chain_of_chain_cons
- \+ *theorem* chain.imp'
- \+ *theorem* chain.imp
- \+ *theorem* chain.iff
- \+ *theorem* chain.iff_mem
- \+ *theorem* chain_singleton
- \+ *theorem* chain_split
- \+ *theorem* chain_map
- \+ *theorem* chain_of_chain_map
- \+ *theorem* chain_map_of_chain
- \+ *theorem* chain_of_pairwise
- \+ *theorem* chain_iff_pairwise
- \+ *theorem* chain'.imp
- \+ *theorem* chain'.iff
- \+ *theorem* chain'.iff_mem
- \+ *theorem* chain'_nil
- \+ *theorem* chain'_singleton
- \+ *theorem* chain'_split
- \+ *theorem* chain'_map
- \+ *theorem* chain'_of_chain'_map
- \+ *theorem* chain'_map_of_chain'
- \+ *theorem* pairwise.chain'
- \+ *theorem* chain'_iff_pairwise
- \+ *theorem* chain'_cons
- \+ *theorem* chain'.cons
- \+ *theorem* chain'.tail
- \+ *theorem* chain'_pair
- \+ *theorem* chain'_reverse

Modified src/data/list/defs.lean
- \- *def* tfae
- \- *def* neg
- \- *def* set
- \- *def* get
- \- *def* equiv
- \- *def* pointwise
- \- *def* add
- \- *def* sub

Created src/data/list/erase_dup.lean
- \+ *theorem* erase_dup_nil
- \+ *theorem* erase_dup_cons_of_mem'
- \+ *theorem* erase_dup_cons_of_not_mem'
- \+ *theorem* mem_erase_dup
- \+ *theorem* erase_dup_cons_of_mem
- \+ *theorem* erase_dup_cons_of_not_mem
- \+ *theorem* erase_dup_sublist
- \+ *theorem* erase_dup_subset
- \+ *theorem* subset_erase_dup
- \+ *theorem* nodup_erase_dup
- \+ *theorem* erase_dup_eq_self
- \+ *theorem* erase_dup_idempotent
- \+ *theorem* erase_dup_append

Created src/data/list/forall2.lean
- \+ *lemma* forall₂.mp
- \+ *lemma* forall₂.flip
- \+ *lemma* forall₂_same
- \+ *lemma* forall₂_refl
- \+ *lemma* forall₂_eq_eq_eq
- \+ *lemma* forall₂_nil_left_iff
- \+ *lemma* forall₂_nil_right_iff
- \+ *lemma* forall₂_cons_left_iff
- \+ *lemma* forall₂_cons_right_iff
- \+ *lemma* forall₂_and_left
- \+ *lemma* forall₂_map_left_iff
- \+ *lemma* forall₂_map_right_iff
- \+ *lemma* left_unique_forall₂
- \+ *lemma* right_unique_forall₂
- \+ *lemma* bi_unique_forall₂
- \+ *lemma* rel_mem
- \+ *lemma* rel_map
- \+ *lemma* rel_append
- \+ *lemma* rel_join
- \+ *lemma* rel_bind
- \+ *lemma* rel_foldl
- \+ *lemma* rel_foldr
- \+ *lemma* rel_filter
- \+ *lemma* rel_filter_map
- \+ *lemma* rel_prod
- \+ *theorem* forall₂_cons
- \+ *theorem* forall₂.imp
- \+ *theorem* forall₂_length_eq
- \+ *theorem* forall₂_zip
- \+ *theorem* forall₂_iff_zip
- \+ *theorem* forall₂_take
- \+ *theorem* forall₂_drop
- \+ *theorem* forall₂_take_append
- \+ *theorem* forall₂_drop_append
- \+ *theorem* filter_map_cons

Created src/data/list/func.lean
- \+ *lemma* length_set
- \+ *lemma* get_nil
- \+ *lemma* get_eq_default_of_le
- \+ *lemma* get_set
- \+ *lemma* eq_get_of_mem
- \+ *lemma* mem_get_of_le
- \+ *lemma* mem_get_of_ne_zero
- \+ *lemma* get_set_eq_of_ne
- \+ *lemma* get_map
- \+ *lemma* get_map'
- \+ *lemma* forall_val_of_forall_mem
- \+ *lemma* equiv_refl
- \+ *lemma* equiv_symm
- \+ *lemma* equiv_trans
- \+ *lemma* equiv_of_eq
- \+ *lemma* eq_of_equiv
- \+ *lemma* get_neg
- \+ *lemma* length_neg
- \+ *lemma* nil_pointwise
- \+ *lemma* pointwise_nil
- \+ *lemma* get_pointwise
- \+ *lemma* length_pointwise
- \+ *lemma* get_add
- \+ *lemma* length_add
- \+ *lemma* nil_add
- \+ *lemma* add_nil
- \+ *lemma* map_add_map
- \+ *lemma* get_sub
- \+ *lemma* length_sub
- \+ *lemma* nil_sub
- \+ *lemma* sub_nil
- \+ *def* neg
- \+ *def* set
- \+ *def* get
- \+ *def* equiv
- \+ *def* pointwise
- \+ *def* add
- \+ *def* sub

Created src/data/list/intervals.lean
- \+ *lemma* append_consecutive
- \+ *lemma* inter_consecutive
- \+ *lemma* bag_inter_consecutive
- \+ *lemma* filter_lt_of_top_le
- \+ *lemma* filter_lt_of_le_bot
- \+ *lemma* filter_lt_of_ge
- \+ *lemma* filter_lt
- \+ *lemma* filter_le_of_le_bot
- \+ *lemma* filter_le_of_top_le
- \+ *lemma* filter_le_of_le
- \+ *lemma* filter_le
- \+ *lemma* trichotomy
- \+ *theorem* zero_bot
- \+ *theorem* length
- \+ *theorem* pairwise_lt
- \+ *theorem* nodup
- \+ *theorem* mem
- \+ *theorem* eq_nil_of_le
- \+ *theorem* map_add
- \+ *theorem* map_sub
- \+ *theorem* self_empty
- \+ *theorem* eq_empty_iff
- \+ *theorem* succ_singleton
- \+ *theorem* succ_top
- \+ *theorem* eq_cons
- \+ *theorem* pred_singleton
- \+ *theorem* chain'_succ
- \+ *theorem* not_mem_top
- \+ *def* Ico

Created src/data/list/nodup.lean
- \+ *lemma* rel_nodup
- \+ *lemma* nodup_sublists_len
- \+ *lemma* diff_eq_filter_of_nodup
- \+ *lemma* mem_diff_iff_of_nodup
- \+ *lemma* nodup_update_nth
- \+ *theorem* forall_mem_ne
- \+ *theorem* nodup_nil
- \+ *theorem* nodup_cons
- \+ *theorem* nodup_cons_of_nodup
- \+ *theorem* nodup_singleton
- \+ *theorem* nodup_of_nodup_cons
- \+ *theorem* not_mem_of_nodup_cons
- \+ *theorem* not_nodup_cons_of_mem
- \+ *theorem* nodup_of_sublist
- \+ *theorem* not_nodup_pair
- \+ *theorem* nodup_iff_sublist
- \+ *theorem* nodup_iff_nth_le_inj
- \+ *theorem* nth_le_index_of
- \+ *theorem* nodup_iff_count_le_one
- \+ *theorem* nodup_repeat
- \+ *theorem* count_eq_one_of_mem
- \+ *theorem* nodup_of_nodup_append_left
- \+ *theorem* nodup_of_nodup_append_right
- \+ *theorem* nodup_append
- \+ *theorem* disjoint_of_nodup_append
- \+ *theorem* nodup_append_of_nodup
- \+ *theorem* nodup_append_comm
- \+ *theorem* nodup_middle
- \+ *theorem* nodup_of_nodup_map
- \+ *theorem* nodup_map_on
- \+ *theorem* nodup_map
- \+ *theorem* nodup_map_iff
- \+ *theorem* nodup_attach
- \+ *theorem* nodup_pmap
- \+ *theorem* nodup_filter
- \+ *theorem* nodup_reverse
- \+ *theorem* nodup_erase_eq_filter
- \+ *theorem* nodup_erase_of_nodup
- \+ *theorem* nodup_diff
- \+ *theorem* mem_erase_iff_of_nodup
- \+ *theorem* mem_erase_of_nodup
- \+ *theorem* nodup_join
- \+ *theorem* nodup_bind
- \+ *theorem* nodup_product
- \+ *theorem* nodup_sigma
- \+ *theorem* nodup_filter_map
- \+ *theorem* nodup_concat
- \+ *theorem* nodup_insert
- \+ *theorem* nodup_union
- \+ *theorem* nodup_inter_of_nodup
- \+ *theorem* nodup_sublists
- \+ *theorem* nodup_sublists'
- \+ *theorem* option.to_list_nodup

Created src/data/list/of_fn.lean
- \+ *theorem* length_of_fn_aux
- \+ *theorem* length_of_fn
- \+ *theorem* nth_of_fn_aux
- \+ *theorem* nth_of_fn
- \+ *theorem* nth_le_of_fn
- \+ *theorem* array_eq_of_fn
- \+ *theorem* of_fn_zero
- \+ *theorem* of_fn_succ
- \+ *theorem* of_fn_nth_le

Created src/data/list/pairwise.lean
- \+ *lemma* forall_of_pairwise
- \+ *theorem* rel_of_pairwise_cons
- \+ *theorem* pairwise_of_pairwise_cons
- \+ *theorem* pairwise.imp_of_mem
- \+ *theorem* pairwise.imp
- \+ *theorem* pairwise.and
- \+ *theorem* pairwise.imp₂
- \+ *theorem* pairwise.iff_of_mem
- \+ *theorem* pairwise.iff
- \+ *theorem* pairwise_of_forall
- \+ *theorem* pairwise.and_mem
- \+ *theorem* pairwise.imp_mem
- \+ *theorem* pairwise_of_sublist
- \+ *theorem* forall_of_forall_of_pairwise
- \+ *theorem* pairwise_singleton
- \+ *theorem* pairwise_pair
- \+ *theorem* pairwise_append
- \+ *theorem* pairwise_append_comm
- \+ *theorem* pairwise_middle
- \+ *theorem* pairwise_map
- \+ *theorem* pairwise_of_pairwise_map
- \+ *theorem* pairwise_map_of_pairwise
- \+ *theorem* pairwise_filter_map
- \+ *theorem* pairwise_filter_map_of_pairwise
- \+ *theorem* pairwise_filter
- \+ *theorem* pairwise_filter_of_pairwise
- \+ *theorem* pairwise_join
- \+ *theorem* pairwise_reverse
- \+ *theorem* pairwise_iff_nth_le
- \+ *theorem* pairwise_sublists'
- \+ *theorem* pairwise_sublists
- \+ *theorem* pw_filter_nil
- \+ *theorem* pw_filter_cons_of_pos
- \+ *theorem* pw_filter_cons_of_neg
- \+ *theorem* pw_filter_map
- \+ *theorem* pw_filter_sublist
- \+ *theorem* pw_filter_subset
- \+ *theorem* pairwise_pw_filter
- \+ *theorem* pw_filter_eq_self
- \+ *theorem* pw_filter_idempotent
- \+ *theorem* forall_mem_pw_filter

Modified src/data/list/perm.lean


Created src/data/list/range.lean
- \+ *lemma* mem_fin_range
- \+ *lemma* nodup_fin_range
- \+ *lemma* length_fin_range
- \+ *lemma* nth_le_range
- \+ *theorem* length_range'
- \+ *theorem* mem_range'
- \+ *theorem* map_add_range'
- \+ *theorem* map_sub_range'
- \+ *theorem* chain_succ_range'
- \+ *theorem* chain_lt_range'
- \+ *theorem* pairwise_lt_range'
- \+ *theorem* nodup_range'
- \+ *theorem* range'_append
- \+ *theorem* range'_sublist_right
- \+ *theorem* range'_subset_right
- \+ *theorem* nth_range'
- \+ *theorem* range'_concat
- \+ *theorem* range_core_range'
- \+ *theorem* range_eq_range'
- \+ *theorem* range_succ_eq_map
- \+ *theorem* range'_eq_map_range
- \+ *theorem* length_range
- \+ *theorem* pairwise_lt_range
- \+ *theorem* nodup_range
- \+ *theorem* range_sublist
- \+ *theorem* range_subset
- \+ *theorem* mem_range
- \+ *theorem* not_mem_range_self
- \+ *theorem* nth_range
- \+ *theorem* range_concat
- \+ *theorem* iota_eq_reverse_range'
- \+ *theorem* length_iota
- \+ *theorem* pairwise_gt_iota
- \+ *theorem* nodup_iota
- \+ *theorem* mem_iota
- \+ *theorem* reverse_range'
- \+ *theorem* prod_range_succ
- \+ *theorem* enum_from_map_fst
- \+ *theorem* enum_map_fst
- \+ *theorem* of_fn_eq_pmap
- \+ *theorem* nodup_of_fn
- \+ *def* fin_range

Created src/data/list/rotate.lean
- \+ *lemma* rotate_mod
- \+ *lemma* rotate_nil
- \+ *lemma* rotate_zero
- \+ *lemma* rotate'_nil
- \+ *lemma* rotate'_zero
- \+ *lemma* rotate'_cons_succ
- \+ *lemma* length_rotate'
- \+ *lemma* rotate'_eq_take_append_drop
- \+ *lemma* rotate'_rotate'
- \+ *lemma* rotate'_length
- \+ *lemma* rotate'_length_mul
- \+ *lemma* rotate'_mod
- \+ *lemma* rotate_eq_rotate'
- \+ *lemma* rotate_cons_succ
- \+ *lemma* mem_rotate
- \+ *lemma* length_rotate
- \+ *lemma* rotate_eq_take_append_drop
- \+ *lemma* rotate_rotate
- \+ *lemma* rotate_length
- \+ *lemma* rotate_length_mul
- \+ *lemma* prod_rotate_eq_one_of_prod_eq_one

Created src/data/list/sections.lean
- \+ *lemma* rel_sections
- \+ *theorem* mem_sections
- \+ *theorem* mem_sections_length

Modified src/data/list/sigma.lean


Created src/data/list/tfae.lean
- \+ *theorem* tfae_nil
- \+ *theorem* tfae_singleton
- \+ *theorem* tfae_cons_of_mem
- \+ *theorem* tfae_cons_cons
- \+ *theorem* tfae_of_forall
- \+ *theorem* tfae_of_cycle
- \+ *theorem* tfae.out
- \+ *def* tfae

Created src/data/list/zip.lean
- \+ *theorem* zip_cons_cons
- \+ *theorem* zip_nil_left
- \+ *theorem* zip_nil_right
- \+ *theorem* zip_swap
- \+ *theorem* length_zip
- \+ *theorem* zip_append
- \+ *theorem* zip_map
- \+ *theorem* zip_map_left
- \+ *theorem* zip_map_right
- \+ *theorem* zip_map'
- \+ *theorem* mem_zip
- \+ *theorem* unzip_nil
- \+ *theorem* unzip_cons
- \+ *theorem* unzip_eq_map
- \+ *theorem* unzip_left
- \+ *theorem* unzip_right
- \+ *theorem* unzip_swap
- \+ *theorem* zip_unzip
- \+ *theorem* unzip_zip_left
- \+ *theorem* unzip_zip_right
- \+ *theorem* unzip_zip
- \+ *theorem* length_revzip
- \+ *theorem* unzip_revzip
- \+ *theorem* revzip_map_fst
- \+ *theorem* revzip_map_snd
- \+ *theorem* reverse_revzip
- \+ *theorem* revzip_swap

Modified src/data/multiset.lean


Modified src/data/nat/modeq.lean


Modified src/data/vector2.lean


Modified src/group_theory/sylow.lean


Modified src/tactic/omega/coeffs.lean


Modified src/tactic/tfae.lean




## [2020-04-09 00:00:42](https://github.com/leanprover-community/mathlib/commit/e4e483e)
Bugfix for norm num when testing divisibility of integers ([#2355](https://github.com/leanprover-community/mathlib/pull/2355))
they were assumed nats somehow
#### Estimated changes
Modified src/tactic/norm_num.lean


Modified test/norm_num.lean




## [2020-04-08 21:12:22](https://github.com/leanprover-community/mathlib/commit/c3d9cf9)
feat(analysis/analytic/basic): change origin of power series ([#2327](https://github.com/leanprover-community/mathlib/pull/2327))
* feat(analysis/analytic/basic): move basepoint of power series
* docstring
* Update src/analysis/analytic/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/analytic/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/analysis/analytic/basic.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+ *lemma* change_origin_summable_aux1
- \+ *lemma* change_origin_summable_aux2
- \+ *lemma* change_origin_summable_aux3
- \+ *lemma* change_origin_radius
- \+ *lemma* change_origin_has_sum
- \+ *lemma* has_fpower_series_on_ball.analytic_at_of_mem
- \+ *lemma* is_open_analytic_at
- \+ *theorem* change_origin_eval
- \+ *theorem* has_fpower_series_on_ball.change_origin
- \+ *def* change_origin

Modified src/topology/instances/ennreal.lean




## [2020-04-08 18:19:54](https://github.com/leanprover-community/mathlib/commit/dae7154)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-08 17:46:11](https://github.com/leanprover-community/mathlib/commit/55d430c)
feat(tactic/linter): add decidable_classical linter ([#2352](https://github.com/leanprover-community/mathlib/pull/2352))
* feat(tactic/linter): add decidable_classical linter
* docstring
* cleanup
* fix build, cleanup
* fix test
* Update src/tactic/lint/type_classes.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/tactic/lint/type_classes.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/tactic/lint/default.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/tactic/lint/type_classes.lean
Co-Authored-By: Scott Morrison <scott@tqft.net>
* Update src/data/dfinsupp.lean
Co-Authored-By: Yury G. Kudryashov <urkud@urkud.name>
#### Estimated changes
Modified src/algebra/big_operators.lean


Modified src/algebra/euclidean_domain.lean
- \+/\- *theorem* gcd.induction

Modified src/algebra/floor.lean
- \+/\- *lemma* ceil_nonneg
- \+/\- *theorem* lt_nat_ceil
- \+/\- *theorem* nat_ceil_lt_add_one

Modified src/algebra/module.lean
- \+/\- *lemma* sum_mem

Modified src/algebra/order.lean
- \+/\- *lemma* lt_or_eq_of_le
- \+/\- *lemma* eq_or_lt_of_le
- \+/\- *lemma* le_iff_lt_or_eq
- \+/\- *lemma* le_of_not_lt
- \+/\- *lemma* not_lt
- \+/\- *lemma* lt_or_le
- \+/\- *lemma* le_or_lt
- \+/\- *lemma* lt_trichotomy
- \+/\- *lemma* lt_or_gt_of_ne
- \+/\- *lemma* ne_iff_lt_or_gt
- \+/\- *lemma* le_imp_le_of_lt_imp_lt
- \+/\- *lemma* le_imp_le_iff_lt_imp_lt
- \+/\- *lemma* le_iff_le_iff_lt_iff_lt

Modified src/algebra/pi_instances.lean
- \+/\- *lemma* finset.prod_apply

Modified src/analysis/convex/specific_functions.lean


Modified src/category_theory/graded_object.lean


Modified src/computability/halting.lean


Modified src/data/dfinsupp.lean
- \+/\- *lemma* map_range_def
- \+/\- *lemma* support_map_range
- \+/\- *lemma* zip_with_def
- \+/\- *lemma* support_zip_with
- \+/\- *lemma* subtype_domain_sum

Modified src/data/equiv/denumerable.lean


Modified src/data/finset.lean
- \+/\- *lemma* subset_union_elim
- \+/\- *lemma* subset_image_iff
- \+/\- *lemma* card_eq_of_bijective
- \+/\- *lemma* card_le_card_of_inj_on
- \+/\- *lemma* card_le_of_inj_on
- \+/\- *lemma* singleton_bind
- \+/\- *lemma* fold_op_rel_iff_and
- \+/\- *lemma* fold_op_rel_iff_or
- \+/\- *lemma* disjoint_bind_left
- \+/\- *lemma* disjoint_bind_right
- \+/\- *theorem* filter_singleton

Modified src/data/hash_map.lean
- \+/\- *theorem* mk_as_list

Modified src/data/int/basic.lean
- \+/\- *theorem* div_eq_div_of_mul_eq_mul
- \+/\- *theorem* eq_mul_div_of_mul_eq_mul_of_dvd_left
- \+/\- *theorem* exists_least_of_bdd
- \+/\- *theorem* exists_greatest_of_bdd

Modified src/data/list/sigma.lean
- \+/\- *lemma* mem_ext

Modified src/data/matrix/pequiv.lean
- \+/\- *lemma* mul_matrix_apply
- \+/\- *lemma* to_matrix_symm
- \+/\- *lemma* to_matrix_refl
- \+/\- *lemma* matrix_mul_apply
- \+/\- *lemma* to_pequiv_mul_matrix
- \+/\- *lemma* to_matrix_trans
- \+/\- *lemma* to_matrix_bot
- \+/\- *lemma* to_matrix_injective
- \+/\- *lemma* to_matrix_swap
- \+/\- *lemma* single_mul_single
- \+/\- *lemma* single_mul_single_of_ne
- \+/\- *lemma* single_mul_single_right
- \+/\- *lemma* equiv_to_pequiv_to_matrix
- \+/\- *def* to_matrix

Modified src/data/multiset.lean
- \+/\- *lemma* sup_le
- \+/\- *lemma* le_sup
- \+/\- *lemma* sup_mono
- \+/\- *lemma* le_inf
- \+/\- *lemma* inf_le
- \+/\- *lemma* inf_mono
- \+/\- *theorem* length_ndinsert_of_mem
- \+/\- *theorem* length_ndinsert_of_not_mem

Modified src/data/pequiv.lean
- \+/\- *lemma* trans_single_of_eq_none
- \+/\- *lemma* single_trans_of_eq_none

Modified src/data/rat/basic.lean


Modified src/data/real/basic.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* sum_lt_top
- \+/\- *lemma* sum_lt_top_iff
- \+/\- *lemma* to_nnreal_sum
- \+/\- *lemma* to_real_sum

Modified src/data/set/basic.lean
- \+/\- *theorem* not_not_mem

Modified src/field_theory/finite.lean
- \+/\- *lemma* card_nth_roots_subgroup_units
- \+/\- *lemma* card_units
- \+/\- *lemma* prod_univ_units_id_eq_neg_one
- \+/\- *lemma* pow_card_sub_one_eq_one

Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* card_trivial
- \+/\- *lemma* order_of_pos

Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finsupp.lean
- \+/\- *lemma* supported_eq_span_single

Modified src/linear_algebra/multilinear.lean
- \+/\- *lemma* sum_apply

Modified src/logic/basic.lean
- \+/\- *theorem* not_not
- \+/\- *theorem* not_imp
- \+/\- *theorem* not_forall_not
- \+/\- *theorem* not_exists_not

Modified src/ring_theory/adjoin.lean
- \+/\- *theorem* adjoin_eq_range
- \+/\- *theorem* adjoin_singleton_eq_range

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean
- \+/\- *theorem* symm

Modified src/ring_theory/multiplicity.lean
- \+/\- *lemma* multiplicity_self
- \+/\- *lemma* get_multiplicity_self
- \+/\- *lemma* finset.prod

Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* factor_set.sup_add_inf_eq_add
- \+/\- *theorem* factor_set.coe_add
- \+/\- *theorem* prod_top
- \+/\- *theorem* prod_coe
- \+/\- *theorem* prod_add
- \+/\- *theorem* prod_mono
- \+/\- *def* {u}
- \+/\- *def* factor_set.prod

Modified src/tactic/lint/default.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/tactic/push_neg.lean
- \+/\- *lemma* imp_of_not_imp_not

Modified src/topology/algebra/multilinear.lean
- \+/\- *lemma* sum_apply

Modified src/topology/separation.lean
- \+/\- *theorem* exists_open_singleton_of_fintype

Modified test/push_neg.lean




## [2020-04-08 15:10:31](https://github.com/leanprover-community/mathlib/commit/65a5dc0)
feat(data/support): define support of a function and prove some properties ([#2340](https://github.com/leanprover-community/mathlib/pull/2340))
* feat(data/support): define support of a function and prove some properties
* Add `support_mul'` for `group_with_zero`
#### Estimated changes
Modified src/data/indicator_function.lean
- \+ *lemma* support_indicator

Created src/data/support.lean
- \+ *lemma* nmem_support
- \+ *lemma* support_binop_subset
- \+ *lemma* support_add
- \+ *lemma* support_neg
- \+ *lemma* support_sub
- \+ *lemma* support_mul
- \+ *lemma* support_mul'
- \+ *lemma* support_inv
- \+ *lemma* support_div
- \+ *lemma* support_sup
- \+ *lemma* support_inf
- \+ *lemma* support_max
- \+ *lemma* support_min
- \+ *lemma* support_supr
- \+ *lemma* support_infi
- \+ *lemma* support_sum
- \+ *lemma* support_prod
- \+ *lemma* support_comp
- \+ *lemma* support_comp'
- \+ *lemma* support_comp_eq
- \+ *lemma* support_comp_eq'
- \+ *def* support



## [2020-04-08 12:29:19](https://github.com/leanprover-community/mathlib/commit/b550c16)
fix(tactic/solve_by_elim): fix metavariable bug from [#2269](https://github.com/leanprover-community/mathlib/pull/2269) ([#2289](https://github.com/leanprover-community/mathlib/pull/2289))
* chore(tactic/solve_by_elim): fix metavariable bug from [#2269](https://github.com/leanprover-community/mathlib/pull/2269)
* tests
* forgot to save file?
* fix bug, and tweak docs
* fix
* oops, remove stray
* provide both `lemmas` and `lemma_thunks` fields
* fix
* fix
* remove code duplication
* fix indenting
* add comments about evaluating thunks in mk_assumption_set
#### Estimated changes
Modified src/tactic/core.lean


Modified src/tactic/monotonicity/interactive.lean


Modified src/tactic/solve_by_elim.lean


Modified test/solve_by_elim.lean




## [2020-04-08 09:55:55](https://github.com/leanprover-community/mathlib/commit/bd21cff)
feat(data/list/basic): some lemmas about sum/head/tail for list ℕ ([#2342](https://github.com/leanprover-community/mathlib/pull/2342))
* feat(data/list/basic): some lemmas about sum/head/tail for list ℕ
* Add comment
* remove lemma, moving to another PR
* suggestion from review
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* head_mul_tail_prod'
- \+ *lemma* head_add_tail_sum
- \+ *lemma* head_le_sum
- \+ *lemma* tail_sum

Modified src/data/option/basic.lean
- \+ *lemma* get_or_else_some



## [2020-04-08 07:20:14](https://github.com/leanprover-community/mathlib/commit/cb8d8ac)
feat (data/list/basic): lemmas about prod and take ([#2345](https://github.com/leanprover-community/mathlib/pull/2345))
* feat (data/list/basic): lemmas about prod and take
* move lemma
* one more
* using to_additive properly
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* prod_take_mul_prod_drop
- \+ *lemma* prod_take_succ
- \+ *lemma* length_pos_of_prod_ne_one
- \+ *lemma* sum_take_add_sum_drop
- \+ *lemma* sum_take_succ
- \+ *lemma* length_pos_of_sum_ne_zero
- \+ *lemma* length_pos_of_sum_pos



## [2020-04-08 01:12:13](https://github.com/leanprover-community/mathlib/commit/732f710)
feat(data/list/basic): nth_le 0 = head ([#2350](https://github.com/leanprover-community/mathlib/pull/2350))
* feat(data/list/basic): nth_le 0 = head
* oops
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* nth_le_zero



## [2020-04-07 22:38:07](https://github.com/leanprover-community/mathlib/commit/0e2970c)
feat(algebra/group/basic.lean): add inv_mul_eq_one ([#2349](https://github.com/leanprover-community/mathlib/pull/2349))
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *theorem* inv_mul_eq_one



## [2020-04-07 19:50:30](https://github.com/leanprover-community/mathlib/commit/34ae62a)
feat(algebra/homology): functoriality of induced maps on cycles ([#2338](https://github.com/leanprover-community/mathlib/pull/2338))
* feat(algebra/homology): Functoriality of induced maps on cycles
* Rename cycles to cocycles, induced_maps_on_cocycles_functor to kernels_functor
* update names
#### Estimated changes
Modified src/algebra/homology/homology.lean
- \+ *lemma* kernel_map_condition
- \+ *lemma* kernel_map_id
- \+ *lemma* kernel_map_comp
- \+ *def* kernel_map
- \+ *def* kernel_functor
- \- *def* induced_map_on_cycles

Modified src/category_theory/differential_object.lean
- \+ *lemma* zero_f

Modified src/category_theory/graded_object.lean
- \+ *lemma* zero_apply



## [2020-04-07 17:07:59](https://github.com/leanprover-community/mathlib/commit/e2fa8b2)
chore(test/refine_struct): remove dead code ([#2348](https://github.com/leanprover-community/mathlib/pull/2348))
#### Estimated changes
Modified test/refine_struct.lean




## [2020-04-07 16:06:37](https://github.com/leanprover-community/mathlib/commit/abccc30)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-07 15:31:37](https://github.com/leanprover-community/mathlib/commit/6f75c57)
refactor(measure_theory/borel): `borel` is not an `instance` ([#2326](https://github.com/leanprover-community/mathlib/pull/2326))
Redo Borel spaces in a way similar to `closed_order_topology`/`order_topology`.
* `borel` is no longer an `instance`;
* define typeclass `opens_measurable_space` for a space with `measurable_space` and `topological_space` structures such that all open sets are measurable;
* define typeclass `borel_space` for a space with `measurable_space` and `topological_space` structures such that `measurable_space` structure is equal to `borel`;
* use dot syntax in more cases;
* review some proofs that started to fail because of this change.
#### Estimated changes
Modified src/data/equiv/basic.lean
- \+ *def* option_is_some_equiv

Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *lemma* smul_mk

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/borel_space.lean
- \+ *lemma* borel_eq_top_of_discrete
- \+ *lemma* borel_eq_top_of_encodable
- \+ *lemma* continuous.borel_measurable
- \+ *lemma* is_open.is_measurable
- \+/\- *lemma* is_measurable_interior
- \+ *lemma* is_closed.is_measurable
- \+ *lemma* is_measurable_eq
- \+/\- *lemma* is_measurable_Ici
- \+/\- *lemma* is_measurable_Iic
- \+/\- *lemma* is_measurable_Icc
- \+/\- *lemma* is_measurable_Iio
- \+/\- *lemma* is_measurable_Ioi
- \+/\- *lemma* is_measurable_Ioo
- \+/\- *lemma* is_measurable_Ioc
- \+/\- *lemma* is_measurable_Ico
- \+/\- *lemma* is_measurable_interval
- \+ *lemma* continuous.measurable
- \+ *lemma* measurable_of_continuous_on_compl_singleton
- \+ *lemma* continuous.measurable2
- \+/\- *lemma* measurable.smul
- \+ *lemma* measurable.const_smul
- \+ *lemma* measurable_const_smul_iff
- \+ *lemma* is_measurable_le'
- \+/\- *lemma* is_measurable_le
- \+/\- *lemma* measurable.max
- \+/\- *lemma* measurable.min
- \+ *lemma* prod_le_borel_prod
- \+ *lemma* measurable_mul
- \+/\- *lemma* measurable.mul
- \+ *lemma* finset.measurable_prod
- \+ *lemma* measurable_inv
- \+ *lemma* measurable.inv
- \+ *lemma* measurable_inv'
- \+ *lemma* measurable.inv'
- \+ *lemma* measurable.of_inv
- \+ *lemma* measurable_inv_iff
- \+/\- *lemma* measurable.sub
- \+/\- *lemma* measurable.is_lub
- \+/\- *lemma* measurable.is_glb
- \+ *lemma* measurable_supr
- \+ *lemma* measurable_infi
- \+/\- *lemma* measurable.supr_Prop
- \+/\- *lemma* measurable.infi_Prop
- \+ *lemma* measurable_bsupr
- \+ *lemma* measurable_binfi
- \+/\- *lemma* is_measurable_ball
- \+ *lemma* is_measurable_closed_ball
- \+/\- *lemma* measurable_dist
- \+/\- *lemma* measurable.dist
- \+/\- *lemma* measurable_nndist
- \+/\- *lemma* measurable.nndist
- \+ *lemma* is_measurable_eball
- \+/\- *lemma* measurable_edist
- \+/\- *lemma* measurable.edist
- \+ *lemma* measurable.sub_nnreal
- \+ *lemma* measurable.nnreal_of_real
- \+ *lemma* measurable.nnreal_coe
- \+ *lemma* measurable.ennreal_coe
- \+ *lemma* measurable.ennreal_of_real
- \+/\- *lemma* measurable_of_real
- \+ *lemma* measurable.ennreal_mul
- \+ *lemma* measurable.ennreal_add
- \+ *lemma* measurable.ennreal_sub
- \+/\- *lemma* measurable_norm
- \+/\- *lemma* measurable.norm
- \+/\- *lemma* measurable_nnnorm
- \+/\- *lemma* measurable.nnnorm
- \+ *lemma* measurable.ennnorm
- \- *lemma* is_measurable_of_is_open
- \- *lemma* is_measurable_of_is_closed
- \- *lemma* measurable_of_continuous
- \- *lemma* borel_prod_le
- \- *lemma* borel_induced
- \- *lemma* borel_eq_subtype
- \- *lemma* borel_prod
- \- *lemma* measurable_of_continuous2
- \- *lemma* measurable.add
- \- *lemma* measurable_finset_sum
- \- *lemma* measurable.neg
- \- *lemma* measurable_neg_iff
- \- *lemma* measurable_coe_int_real
- \- *lemma* measurable.supr
- \- *lemma* measurable.infi
- \- *lemma* measurable.smul'
- \- *lemma* measurable_smul_iff
- \- *lemma* measurable.coe_nnnorm
- \+/\- *def* borel
- \+ *def* homeomorph.to_measurable_equiv
- \+/\- *def* homemorph.to_measurable_equiv
- \+ *def* measurable_equiv.ennreal_equiv_nnreal
- \- *def* ennreal_equiv_nnreal

Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/indicator_function.lean


Modified src/measure_theory/integration.lean
- \+/\- *lemma* approx_apply
- \+/\- *lemma* approx_comp
- \+ *lemma* lintegral_mono
- \+ *lemma* monotone_lintegral
- \+ *lemma* lintegral_congr
- \+ *lemma* mul_volume_ge_le_lintegral
- \+ *lemma* volume_ge_le_lintegral_div
- \+ *lemma* lintegral_infi
- \- *lemma* lintegral_le_lintegral
- \+ *theorem* supr_lintegral_le
- \+ *theorem* supr2_lintegral_le
- \+ *theorem* le_infi_lintegral
- \+ *theorem* le_infi2_lintegral

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* lintegral_edist_triangle
- \+/\- *lemma* lintegral_edist_lt_top
- \+/\- *lemma* lintegral_nnnorm_add
- \+/\- *lemma* integrable.add
- \+/\- *lemma* integrable_finset_sum
- \+/\- *lemma* integrable.sub
- \+/\- *lemma* tendsto_lintegral_norm_of_dominated_convergence
- \+/\- *lemma* integrable_mk
- \+/\- *lemma* of_fun_smul
- \+/\- *def* l1

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable.of_compl
- \+ *lemma* subsingleton.is_measurable
- \+ *lemma* is_measurable.congr
- \+ *lemma* subsingleton.measurable
- \+ *lemma* measurable_from_top
- \+ *lemma* measurable.mono
- \+ *lemma* measurable_to_encodable
- \+ *lemma* measurable.subtype_coe
- \+ *lemma* measurable_of_measurable_on_compl_singleton
- \+ *lemma* is_measurable.prod
- \- *lemma* measurable.subtype_val
- \- *lemma* is_measurable_set_prod

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* measurable_on_singleton
- \+/\- *lemma* integrable_on.add
- \+/\- *lemma* integrable_on.sub
- \+/\- *lemma* integrable_on.union

Modified src/measure_theory/simple_func_dense.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* monotone.map_supr_ge
- \+ *lemma* monotone.map_supr2_ge
- \+ *lemma* monotone.map_infi_le
- \+ *lemma* monotone.map_infi2_le

Modified src/topology/homeomorph.lean
- \+ *def* set_congr

Modified src/topology/instances/ennreal.lean
- \+ *lemma* continuous_on_to_nnreal
- \+ *def* ne_top_homeomorph_nnreal
- \+ *def* lt_top_homeomorph_nnreal



## [2020-04-07 12:40:05](https://github.com/leanprover-community/mathlib/commit/97c4302)
feat(data/list/basic): add map_take/drop_take ([#2344](https://github.com/leanprover-community/mathlib/pull/2344))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* map_take
- \+ *lemma* map_drop



## [2020-04-07 10:10:41](https://github.com/leanprover-community/mathlib/commit/2f2e016)
chore(data/list/basic): rename take_all -> take_length ([#2343](https://github.com/leanprover-community/mathlib/pull/2343))
* chore(data/list/basic): rename take_all -> take_length
* also rename drop_all
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* drop_length
- \- *lemma* drop_all
- \+ *theorem* take_length
- \- *theorem* take_all



## [2020-04-07 08:48:42](https://github.com/leanprover-community/mathlib/commit/d936c28)
feat(data/real/nnreal): coe_max and coe_min ([#2346](https://github.com/leanprover-community/mathlib/pull/2346))
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* coe_max
- \+ *lemma* coe_min



## [2020-04-07 06:44:18](https://github.com/leanprover-community/mathlib/commit/c85453d)
fix(tactic/refine_struct): don't add unnecessary `eq.mpr` or `id` ([#2319](https://github.com/leanprover-community/mathlib/pull/2319))
* fix(tactic/interactive): don't unfold non-Prop goals
The old behaviour caused `eq.mpr`'s in `pi_instance` output.
* add a test file
* move test
* actually move test
* Update test/refine_struct.lean
* test: fix compile
* Apply suggestions from code review
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Try a fix by @gebner and @cipher1024
* Update test/refine_struct.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* apply Gabriel's suggestion
#### Estimated changes
Modified src/tactic/interactive.lean


Modified test/refine_struct.lean




## [2020-04-07 04:14:25](https://github.com/leanprover-community/mathlib/commit/df64ea9)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-07 03:42:42](https://github.com/leanprover-community/mathlib/commit/60d1457)
chore(algebra/big_operators): drop some `decidable_eq` assumptions ([#2332](https://github.com/leanprover-community/mathlib/pull/2332))
* chore(algebra/big_operators): drop some `decidable_eq` assumptions
I wonder why `lint` didn't report them.
* Drop unused arguments
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/big_operators.lean
- \+/\- *lemma* prod_union_inter
- \+/\- *lemma* prod_comm
- \+/\- *lemma* prod_sum
- \+/\- *lemma* sum_le_sum_of_ne_zero

Modified src/data/finset.lean
- \+/\- *theorem* filter_or
- \+/\- *theorem* filter_and
- \+/\- *theorem* filter_not
- \+/\- *theorem* filter_union_filter_neg_eq

Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* mul_to_lin
- \+/\- *lemma* trace_transpose_mul
- \+/\- *lemma* trace_mul_comm
- \+/\- *lemma* rank_vec_mul_vec



## [2020-04-06 23:32:14](https://github.com/leanprover-community/mathlib/commit/7628c6c)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-06 23:05:14](https://github.com/leanprover-community/mathlib/commit/48cc0c8)
feat(algebra/group_with_zero): groups with a zero element adjoined ([#2242](https://github.com/leanprover-community/mathlib/pull/2242))
* feat(algebra/group_with_zero*): Basics on groups with a zero adjoined
* feat(algebra/group_with_zero*): Basics on groups with a zero adjoined
* Make argument implicit
* Move inv_eq_zero out of gwz namespace
* Partial refactor
* Remove open_locale classical
* Fix build
* Factor out monoid_with_zero
* Fix linter errors, hopefully
* Fix build
* Fix tests
* Replace G with G0
* Add spaces around `^`
* Add spaces and backticks in docstrings
* Fix docstring of `mk0`
* Fix statement of inv_eq_iff
* Golf inv_injective
* Golf inv_eq_zero
* Remove the gwz namespace
* Fix build
#### Estimated changes
Modified src/algebra/archimedean.lean


Modified src/algebra/field.lean
- \- *lemma* inv_inv''
- \- *lemma* inv_involutive'
- \- *lemma* mk0_coe
- \- *lemma* mk0_inj
- \- *lemma* div_eq_mul_inv
- \- *lemma* inv_div
- \- *lemma* inv_div_left
- \- *lemma* division_ring.inv_comm_of_comm
- \- *lemma* div_ne_zero
- \- *lemma* div_ne_zero_iff
- \- *lemma* div_eq_zero_iff
- \- *lemma* div_right_inj
- \- *lemma* div_eq_iff_mul_eq
- \- *lemma* inv_eq_zero
- \- *lemma* div_mul_div_cancel
- \- *lemma* div_eq_iff
- \- *lemma* eq_div_iff
- \- *lemma* div_eq_inv_mul
- \- *lemma* mul_div_right_comm
- \- *lemma* mul_comm_div
- \- *lemma* div_mul_comm
- \- *lemma* mul_div_comm
- \- *lemma* field.div_right_comm
- \- *lemma* field.div_div_div_cancel_right
- \- *lemma* div_eq_div_iff
- \- *lemma* field.div_div_cancel
- \+/\- *theorem* inv_one
- \- *theorem* inv_eq_inv
- \- *theorem* mk0_val
- \- *theorem* divp_eq_div
- \- *theorem* divp_mk0
- \- *def* mk0

Modified src/algebra/field_power.lean
- \- *lemma* zero_gpow
- \- *lemma* fpow_of_nat
- \- *lemma* fpow_neg_succ_of_nat
- \- *lemma* unit_pow
- \- *lemma* fpow_eq_gpow
- \- *lemma* fpow_inv
- \- *lemma* fpow_ne_zero_of_ne_zero
- \- *lemma* fpow_zero
- \- *lemma* fpow_add
- \- *lemma* one_fpow
- \- *lemma* fpow_one
- \- *lemma* zero_fpow
- \- *lemma* fpow_neg
- \- *lemma* fpow_sub
- \- *lemma* fpow_mul
- \- *lemma* mul_fpow
- \- *lemma* fpow_eq_zero
- \- *theorem* fpow_neg_mul_fpow_self
- \- *def* fpow

Modified src/algebra/geom_sum.lean


Modified src/algebra/group_power.lean
- \- *lemma* inv_pow'
- \- *lemma* pow_div
- \- *lemma* pow_inv
- \- *lemma* div_sq_cancel
- \- *theorem* one_div_pow
- \- *theorem* division_ring.inv_pow
- \- *theorem* div_pow
- \+/\- *def* monoid.pow
- \+/\- *def* add_monoid.smul

Created src/algebra/group_with_zero.lean
- \+ *lemma* div_eq_mul_inv
- \+ *lemma* inv_zero'
- \+ *lemma* mul_inv_cancel'
- \+ *lemma* mul_inv_cancel_assoc_left
- \+ *lemma* mul_inv_cancel_assoc_right
- \+ *lemma* inv_ne_zero'
- \+ *lemma* inv_mul_cancel'
- \+ *lemma* inv_mul_cancel_assoc_left
- \+ *lemma* inv_mul_cancel_assoc_right
- \+ *lemma* inv_inv''
- \+ *lemma* inv_involutive'
- \+ *lemma* ne_zero_of_mul_right_eq_one'
- \+ *lemma* ne_zero_of_mul_left_eq_one'
- \+ *lemma* eq_inv_of_mul_right_eq_one'
- \+ *lemma* eq_inv_of_mul_left_eq_one'
- \+ *lemma* inv_one'
- \+ *lemma* inv_injective'
- \+ *lemma* inv_inj''
- \+ *lemma* inv_eq_iff
- \+ *lemma* coe_unit_mul_inv'
- \+ *lemma* coe_unit_inv_mul'
- \+ *lemma* unit_ne_zero
- \+ *lemma* coe_mk0
- \+ *lemma* mk0_coe
- \+ *lemma* mk0_inj
- \+ *lemma* mul_eq_zero'
- \+ *lemma* mul_eq_zero_iff'
- \+ *lemma* mul_ne_zero''
- \+ *lemma* mul_ne_zero_iff
- \+ *lemma* mul_left_cancel'
- \+ *lemma* mul_right_cancel'
- \+ *lemma* mul_inv_eq_of_eq_mul'
- \+ *lemma* eq_mul_inv_of_mul_eq'
- \+ *lemma* mul_inv_rev'
- \+ *lemma* div_self'
- \+ *lemma* div_one'
- \+ *lemma* one_div
- \+ *lemma* zero_div'
- \+ *lemma* div_zero'
- \+ *lemma* div_mul_cancel'
- \+ *lemma* mul_div_cancel''
- \+ *lemma* mul_div_assoc''
- \+ *lemma* div_eq_mul_one_div'
- \+ *lemma* mul_one_div_cancel'
- \+ *lemma* one_div_mul_cancel'
- \+ *lemma* one_div_one'
- \+ *lemma* one_div_ne_zero'
- \+ *lemma* mul_ne_zero_comm''
- \+ *lemma* eq_one_div_of_mul_eq_one'
- \+ *lemma* eq_one_div_of_mul_eq_one_left'
- \+ *lemma* one_div_div'
- \+ *lemma* one_div_one_div'
- \+ *lemma* eq_of_one_div_eq_one_div'
- \+ *lemma* inv_eq_zero
- \+ *lemma* one_div_mul_one_div_rev
- \+ *lemma* inv_div
- \+ *lemma* inv_div_left
- \+ *lemma* div_ne_zero
- \+ *lemma* div_ne_zero_iff
- \+ *lemma* div_eq_zero_iff
- \+ *lemma* div_right_inj'
- \+ *lemma* mul_right_inj'
- \+ *lemma* div_eq_iff_mul_eq
- \+ *lemma* mul_inv''
- \+ *lemma* one_div_mul_one_div'
- \+ *lemma* div_mul_right'
- \+ *lemma* div_mul_left'
- \+ *lemma* mul_div_cancel_left'
- \+ *lemma* mul_div_cancel'''
- \+ *lemma* div_mul_div'
- \+ *lemma* mul_div_mul_left'
- \+ *lemma* mul_div_mul_right'
- \+ *lemma* div_mul_eq_mul_div'
- \+ *lemma* div_mul_eq_mul_div_comm'
- \+ *lemma* mul_eq_mul_of_div_eq_div'
- \+ *lemma* div_div_eq_mul_div'
- \+ *lemma* div_div_eq_div_mul'
- \+ *lemma* div_div_div_div_eq'
- \+ *lemma* div_mul_eq_div_mul_one_div'
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_left'
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_right'
- \+ *lemma* ne_zero_of_one_div_ne_zero'
- \+ *lemma* eq_zero_of_one_div_eq_zero'
- \+ *lemma* div_helper'
- \+ *lemma* div_eq_inv_mul'
- \+ *lemma* mul_div_right_comm
- \+ *lemma* mul_comm_div'
- \+ *lemma* div_mul_comm'
- \+ *lemma* mul_div_comm
- \+ *lemma* div_right_comm'
- \+ *lemma* div_div_div_cancel_right'
- \+ *lemma* div_mul_div_cancel'
- \+ *lemma* div_eq_div_iff
- \+ *lemma* div_eq_iff
- \+ *lemma* eq_div_iff
- \+ *lemma* div_div_cancel'
- \+ *theorem* inv_eq_inv
- \+ *theorem* inv_comm_of_comm'
- \+ *theorem* divp_eq_div
- \+ *theorem* divp_mk0
- \+ *def* mk0

Created src/algebra/group_with_zero_power.lean
- \+ *lemma* zero_pow'
- \+ *lemma* zero_fpow
- \+ *lemma* fpow_inv
- \+ *lemma* unit_pow
- \+ *lemma* fpow_neg_succ_of_nat
- \+ *lemma* unit_gpow
- \+ *lemma* fpow_ne_zero_of_ne_zero
- \+ *lemma* fpow_sub
- \+ *lemma* mul_fpow
- \+ *lemma* fpow_eq_zero
- \+ *lemma* fpow_ne_zero
- \+ *lemma* div_sq_cancel
- \+ *theorem* inv_pow'
- \+ *theorem* pow_eq_zero'
- \+ *theorem* pow_ne_zero'
- \+ *theorem* pow_sub'
- \+ *theorem* pow_inv_comm'
- \+ *theorem* fpow_coe_nat
- \+ *theorem* fpow_of_nat
- \+ *theorem* fpow_neg_succ
- \+ *theorem* fpow_zero
- \+ *theorem* fpow_one
- \+ *theorem* one_fpow
- \+ *theorem* fpow_neg
- \+ *theorem* fpow_neg_one
- \+ *theorem* inv_fpow
- \+ *theorem* fpow_add
- \+ *theorem* fpow_add_one
- \+ *theorem* fpow_one_add
- \+ *theorem* fpow_mul_comm
- \+ *theorem* fpow_mul
- \+ *theorem* fpow_mul'
- \+ *theorem* fpow_neg_mul_fpow_self
- \+ *theorem* one_div_pow
- \+ *theorem* one_div_fpow
- \+ *theorem* div_pow
- \+ *theorem* div_fpow
- \+ *def* fpow

Modified src/algebra/ordered_field.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/complex/exponential.lean


Modified src/analysis/convex/basic.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/specific_limits.lean


Modified src/data/complex/basic.lean


Modified src/data/complex/exponential.lean


Modified src/data/rat/cast.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/ennreal.lean


Modified src/data/real/irrational.lean


Modified src/data/real/nnreal.lean
- \+ *lemma* ne_iff

Modified src/data/zmod/quadratic_reciprocity.lean


Modified src/field_theory/finite.lean


Modified src/measure_theory/probability_mass_function.lean


Modified src/topology/metric_space/antilipschitz.lean


Modified src/topology/metric_space/closeds.lean


Modified test/ring_exp.lean




## [2020-04-06 21:01:55](https://github.com/leanprover-community/mathlib/commit/89fdec6)
fix(data/finset): add comment ([#2336](https://github.com/leanprover-community/mathlib/pull/2336))
* doc(data/finset): adding comment
* fix(topology/metric_space/basic): comment typo
#### Estimated changes
Modified src/data/finset.lean


Modified src/topology/metric_space/basic.lean




## [2020-04-06 18:20:25](https://github.com/leanprover-community/mathlib/commit/7b120a3)
feat(data/mv_polynomial): add pderivative_eq_zero_of_not_mem_vars ([#2324](https://github.com/leanprover-community/mathlib/pull/2324))
* feat(data/mv_polynomial): add pderivative_eq_zero_of_not_mem_vars
* Added doc comment for `pderivative.add_monoid_hom`
* Fix formatting
* fixed issues from review
* change begin end to braces.
* fix issues from review
#### Estimated changes
Modified src/data/mv_polynomial.lean
- \+ *lemma* support_sum_monomial_coeff
- \+ *lemma* as_sum
- \+ *lemma* mem_support_not_mem_vars_zero
- \+ *lemma* pderivative.add_monoid_hom_apply
- \+ *lemma* pderivative_eq_zero_of_not_mem_vars
- \+ *def* pderivative.add_monoid_hom



## [2020-04-06 15:34:03](https://github.com/leanprover-community/mathlib/commit/ff910dc)
feat(topology/bounded_continuous_function): composition of limits when uniform convergence ([#2260](https://github.com/leanprover-community/mathlib/pull/2260))
* feat(topology/bounded_continuous_function): composition of limits when uniform convergence
* better statement
* uniform space version
* cleanup
* fix linter
* reviewer's comments
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+ *lemma* has_fpower_series_on_ball.uniform_geometric_approx
- \+ *lemma* has_fpower_series_on_ball.tendsto_uniformly_on
- \+ *lemma* has_fpower_series_on_ball.tendsto_locally_uniformly_on
- \+ *lemma* has_fpower_series_on_ball.tendsto_uniformly_on'
- \+ *lemma* has_fpower_series_on_ball.tendsto_locally_uniformly_on'
- \- *lemma* has_fpower_series_on_ball.uniform_limit

Modified src/data/real/nnreal.lean
- \+ *lemma* val_eq_coe

Modified src/topology/basic.lean
- \+ *lemma* filter.eventually.self_of_nhds

Modified src/topology/bounded_continuous_function.lean
- \- *lemma* continuous_within_at_of_locally_uniform_limit_of_continuous_within_at
- \- *lemma* continuous_at_of_locally_uniform_limit_of_continuous_at
- \- *lemma* continuous_on_of_locally_uniform_limit_of_continuous_on
- \- *lemma* continuous_on_of_uniform_limit_of_continuous_on
- \- *lemma* continuous_of_locally_uniform_limit_of_continuous
- \- *lemma* continuous_of_uniform_limit_of_continuous

Modified src/topology/continuous_on.lean
- \+ *lemma* filter.eventually.self_of_nhds_within

Modified src/topology/metric_space/basic.lean
- \+ *lemma* tendsto_locally_uniformly_on_iff
- \+ *lemma* tendsto_uniformly_on_iff
- \+ *lemma* tendsto_locally_uniformly_iff
- \+ *lemma* tendsto_uniformly_iff
- \+ *lemma* metric.emetric_ball_nnreal
- \+ *lemma* metric.emetric_closed_ball_nnreal

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* tendsto_locally_uniformly_on_iff
- \+ *lemma* tendsto_uniformly_on_iff
- \+ *lemma* tendsto_locally_uniformly_iff
- \+ *lemma* tendsto_uniformly_iff

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* mem_nhds_uniformity_iff_right
- \+ *lemma* mem_nhds_uniformity_iff_left
- \- *lemma* mem_nhds_uniformity_iff
- \+ *theorem* tendsto_nhds_right
- \+ *theorem* tendsto_nhds_left
- \+ *theorem* continuous_at_iff'_right
- \+ *theorem* continuous_at_iff'_left
- \+ *theorem* continuous_within_at_iff'_right
- \+ *theorem* continuous_within_at_iff'_left
- \+ *theorem* continuous_on_iff'_right
- \+ *theorem* continuous_on_iff'_left
- \+ *theorem* continuous_iff'_right
- \+ *theorem* continuous_iff'_left

Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/separation.lean


Created src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_uniformly_on_univ
- \+ *lemma* tendsto_uniformly_on.mono
- \+ *lemma* tendsto_uniformly.tendsto_uniformly_on
- \+ *lemma* tendsto_uniformly_on.comp
- \+ *lemma* tendsto_uniformly.comp
- \+ *lemma* tendsto_uniformly_on.tendsto_locally_uniformly_on
- \+ *lemma* tendsto_uniformly.tendsto_locally_uniformly
- \+ *lemma* tendsto_locally_uniformly_on.mono
- \+ *lemma* tendsto_locally_uniformly_on_univ
- \+ *lemma* tendsto_locally_uniformly_on.comp
- \+ *lemma* tendsto_locally_uniformly.comp
- \+ *lemma* continuous_within_at_of_locally_uniform_approx_of_continuous_within_at
- \+ *lemma* continuous_at_of_locally_uniform_approx_of_continuous_at
- \+ *lemma* continuous_on_of_locally_uniform_approx_of_continuous_on
- \+ *lemma* continuous_on_of_uniform_approx_of_continuous_on
- \+ *lemma* continuous_of_locally_uniform_approx_of_continuous
- \+ *lemma* continuous_of_uniform_approx_of_continuous
- \+ *lemma* tendsto_locally_uniformly_on.continuous_on
- \+ *lemma* tendsto_uniformly_on.continuous_on
- \+ *lemma* tendsto_locally_uniformly.continuous
- \+ *lemma* tendsto_uniformly.continuous
- \+ *lemma* tendsto_comp_of_locally_uniform_limit_within
- \+ *lemma* tendsto_comp_of_locally_uniform_limit
- \+ *lemma* tendsto_locally_uniformly_on.tendsto_comp
- \+ *lemma* tendsto_uniformly_on.tendsto_comp
- \+ *lemma* tendsto_locally_uniformly.tendsto_comp
- \+ *lemma* tendsto_uniformly.tendsto_comp
- \+ *def* tendsto_uniformly_on
- \+ *def* tendsto_uniformly
- \+ *def* tendsto_locally_uniformly_on
- \+ *def* tendsto_locally_uniformly



## [2020-04-06 12:39:52](https://github.com/leanprover-community/mathlib/commit/572fad1)
chore(topology/instances/ennreal): prove `tendsto_iff_edist_tendsto_0` ([#2333](https://github.com/leanprover-community/mathlib/pull/2333))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* tendsto_iff_edist_tendsto_0



## [2020-04-06 10:15:13](https://github.com/leanprover-community/mathlib/commit/3d60e13)
chore(algebra/field): move some lemmas from `field` to `division_ring` ([#2331](https://github.com/leanprover-community/mathlib/pull/2331))
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* inv_eq_zero
- \+/\- *lemma* div_mul_div_cancel
- \+/\- *lemma* div_eq_iff
- \+/\- *lemma* eq_div_iff



## [2020-04-05 23:39:22](https://github.com/leanprover-community/mathlib/commit/a2e7639)
feat(order/filter): more eventually/frequently API ([#2330](https://github.com/leanprover-community/mathlib/pull/2330))
* feat(order/filter): more eventually/frequently API
* Update after review
* Add simp attribute
* Update src/order/filter/basic.lean
Co-Authored-By: Yury G. Kudryashov <urkud@urkud.name>
* Update src/order/filter/basic.lean
Co-Authored-By: Yury G. Kudryashov <urkud@urkud.name>
#### Estimated changes
Modified src/order/filter/basic.lean
- \+ *lemma* inf_ne_bot_iff
- \+ *lemma* eventually_iff
- \+ *lemma* eventually_of_mem
- \+ *lemma* frequently_iff
- \+ *lemma* inf_ne_bot_iff_frequently_left
- \+ *lemma* inf_ne_bot_iff_frequently_right
- \+ *lemma* eventually_map
- \+ *lemma* frequently_map
- \+ *lemma* eventually_comap
- \+ *lemma* frequently_comap
- \+ *lemma* frequently_at_top'



## [2020-04-05 17:46:07](https://github.com/leanprover-community/mathlib/commit/26bf273)
feat(logic/embedding): embedding punit/prod ([#2315](https://github.com/leanprover-community/mathlib/pull/2315))
* feat(logic/embedding): embedding punit/prod
* renaming to sectl
* Revert disambiguations no longer needed
#### Estimated changes
Modified src/category_theory/products/basic.lean
- \+/\- *lemma* prod_id_fst
- \+/\- *lemma* prod_id_snd
- \+ *def* sectl
- \+ *def* sectr
- \- *def* inl
- \- *def* inr

Modified src/logic/embedding.lean
- \+ *lemma* equiv_to_embedding_trans_symm_to_embedding
- \+ *lemma* equiv_symm_to_embedding_trans_to_embedding
- \+ *def* punit
- \+ *def* sectl
- \+ *def* sectr



## [2020-04-05 05:53:08](https://github.com/leanprover-community/mathlib/commit/23681c3)
feat(tactic/linarith): split conjunctions in hypotheses ([#2320](https://github.com/leanprover-community/mathlib/pull/2320))
* feat(tactic/linarith): split conjunctions in hypotheses
* update doc
#### Estimated changes
Modified src/tactic/linarith.lean


Modified test/linarith.lean




## [2020-04-04 17:59:00](https://github.com/leanprover-community/mathlib/commit/dea8bd4)
feat(*/multilinear): more material ([#2197](https://github.com/leanprover-community/mathlib/pull/2197))
* feat(*/multilinear): more material
* improvements
* docstring
* elaboration strategy
* remove begin ... end
* fix build
* linter
#### Estimated changes
Modified src/analysis/normed_space/multilinear.lean
- \+ *lemma* restr_norm_le
- \+ *lemma* continuous_eval_left
- \+ *lemma* has_sum_eval
- \+ *lemma* norm_restr
- \+ *def* restr

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* sum_apply
- \+ *lemma* map_sum_finset_aux
- \+ *lemma* map_sum_finset
- \+ *lemma* map_sum
- \+/\- *lemma* map_piecewise_smul
- \+/\- *lemma* map_smul_univ

Modified src/topology/algebra/multilinear.lean
- \+ *lemma* sum_apply
- \+/\- *lemma* map_piecewise_add
- \+/\- *lemma* map_add_univ
- \+ *lemma* map_sum_finset
- \+ *lemma* map_sum



## [2020-04-04 16:43:46](https://github.com/leanprover-community/mathlib/commit/8406896)
chore(ci): always push release to azure ([#2321](https://github.com/leanprover-community/mathlib/pull/2321))
PR [#2048](https://github.com/leanprover-community/mathlib/pull/2048) changed the CI so that olean caches are not pushed to Azure if a later commit on the same branch occurs. The reasoning was that it was unlikely that anyone would fetch those caches. That's changed as of [#2278](https://github.com/leanprover-community/mathlib/pull/2278), since `fetch_olean_cache.sh` now looks for caches from commits earlier in the history. This means that currently, we can observe the following wasteful sequence of events in several PRs (e.g. [#2258](https://github.com/leanprover-community/mathlib/pull/2258)):
1. commit A gets pushed to a certain branch and CI_A starts.
2. While CI_A is still running the `leanpkg build` step, commit B is pushed and CI_B starts.
3. CI_A finishes `leanpkg build` but doesn't upload its cache to Azure because of [#2048](https://github.com/leanprover-community/mathlib/pull/2048) 
4. Now commit C is pushed and can't use the results of CI_A
5. CI_B finishes `leanpkg build` but doesn't upload its cache
6. Commit D is pushed and can't use the results of CI_A or CI_B ...
(This can keep happening as long as the next commit arrives before the most recent CI uploads to Azure).
I also cleaned up some stuff that was left over from when we ran the build on both "pr" and "push" events.
#### Estimated changes
Modified .github/workflows/build.yml




## [2020-04-04 08:11:40](https://github.com/leanprover-community/mathlib/commit/63aa8b1)
feat(data/mv_polynomial): add partial derivatives ([#2298](https://github.com/leanprover-community/mathlib/pull/2298))
* feat(data/mv_polynomial): add partial derivatives
* Added suggestions from PR.
* trying to placate simp linter
* Updated implementation of `pderivative`
* formatting suggestions from Bryan
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
* Suggestions from review.
* rearrange aux lemmas
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *lemma* erase_single
- \+ *lemma* erase_single_ne
- \+ *lemma* erase_add
- \+/\- *lemma* nat_sub_apply
- \+ *lemma* single_sub
- \+ *lemma* sub_single_one_add
- \+ *lemma* add_sub_single_one

Modified src/data/mv_polynomial.lean
- \+ *lemma* single_eq_C_mul_X
- \+ *lemma* monomial_add
- \+ *lemma* monomial_mul
- \+ *lemma* monomial_zero
- \+ *lemma* sum_monomial
- \+ *lemma* pderivative_add
- \+ *lemma* pderivative_monomial
- \+ *lemma* pderivative_C
- \+ *lemma* pderivative_zero
- \+ *lemma* pderivative_monomial_single
- \+ *lemma* pderivative_monomial_mul
- \+ *lemma* pderivative_mul
- \+ *lemma* pderivative_C_mul
- \+ *theorem* induction_on'
- \+ *def* pderivative

Modified src/data/nat/basic.lean
- \+ *lemma* add_succ_sub_one
- \+ *lemma* succ_add_sub_one



## [2020-04-04 05:20:52](https://github.com/leanprover-community/mathlib/commit/906874e)
feat(category_theory): quotient categories ([#2310](https://github.com/leanprover-community/mathlib/pull/2310))
This constructs the quotient of a category by an arbitrary family of relations on its hom-sets. Analogous to "quotient of a group by the normal closure of a subset", as opposed to "quotient of a group by a normal subgroup".
The plan is to eventually use this together with the path category to construct the free groupoid on a graph.
#### Estimated changes
Created src/category_theory/quotient.lean
- \+ *lemma* comp_left
- \+ *lemma* comp_right
- \+ *lemma* comp_mk
- \+ *lemma* lift.is_lift_hom
- \+ *lemma* lift.is_lift_inv
- \+ *def* hom
- \+ *def* comp
- \+ *def* functor
- \+ *def* lift
- \+ *def* lift.is_lift



## [2020-04-03 12:34:08](https://github.com/leanprover-community/mathlib/commit/a590d4b)
feat(group_theory/monoid_localization): some homs induced on localizations: lift, map ([#2118](https://github.com/leanprover-community/mathlib/pull/2118))
* should I be changing and committing toml idk
* initial monoid loc lemmas
* responding to PR comments
* removing bad @[simp]
* inhabited instances
* remove #lint
* additive inhabited instance
* using is_unit & is_add_unit
* doc string
* remove simp
* submonoid.monoid_loc... -> submonoid.localization
* submonoid.monoid_loc... -> submonoid.localization
* generalize inhabited instance
* remove inhabited instance
* 2nd section
* docs and linting
* removing questionable `@[simp]s`
* removing away
* adding lemmas, removing 'include'
* removing import
* responding to PR comments
* use eq_of_eq to prove comp_eq_of_eq
* name change
* trying to update mathlib
* make lemma names consistent
* Update src/algebra/group/is_unit.lean
* Update src/algebra/group/is_unit.lean
* fix build
* documentation and minor changes
* spacing
* fix build
* applying comments
#### Estimated changes
Modified src/algebra/group/is_unit.lean
- \+/\- *lemma* is_unit_unit
- \+/\- *lemma* is_unit.map
- \+/\- *lemma* is_unit.coe_lift_right
- \+ *lemma* is_unit.mul_lift_right_inv
- \+ *lemma* is_unit.lift_right_inv_mul
- \+ *theorem* is_unit_of_mul_eq_one
- \+/\- *theorem* is_unit_iff_exists_inv
- \+/\- *theorem* is_unit_iff_exists_inv'
- \- *theorem* is_unit_of_mul_one

Modified src/algebra/group/units_hom.lean
- \+/\- *lemma* coe_lift_right
- \+ *lemma* mul_lift_right_inv
- \+ *lemma* lift_right_inv_mul

Modified src/group_theory/monoid_localization.lean
- \+ *lemma* ext
- \+ *lemma* ext_iff
- \+ *lemma* to_fun_inj
- \+/\- *lemma* sec_spec
- \+/\- *lemma* sec_spec'
- \+/\- *lemma* mul_inv_left
- \+/\- *lemma* mul_inv_right
- \+/\- *lemma* mul_inv
- \+/\- *lemma* inv_inj
- \+/\- *lemma* inv_unique
- \+/\- *lemma* mk'_mul
- \+/\- *lemma* mk'_sec
- \+/\- *lemma* exists_of_sec_mk'
- \+/\- *lemma* mul_mk'_eq_mk'_of_mul
- \+/\- *lemma* mk'_mul_eq_mk'_of_mul
- \+/\- *lemma* mul_mk'_one_eq_mk'
- \+/\- *lemma* mk'_mul_cancel_right
- \+/\- *lemma* mk'_mul_cancel_left
- \+ *lemma* is_unit_comp
- \+ *lemma* eq_of_eq
- \+ *lemma* comp_eq_of_eq
- \+ *lemma* lift_mk'
- \+ *lemma* lift_spec
- \+ *lemma* lift_spec_mul
- \+ *lemma* lift_mk'_spec
- \+ *lemma* lift_mul_right
- \+ *lemma* lift_mul_left
- \+ *lemma* lift_eq
- \+ *lemma* lift_eq_iff
- \+ *lemma* lift_of_comp
- \+ *lemma* epic_of_localization_map
- \+ *lemma* lift_unique
- \+ *lemma* lift_id
- \+ *lemma* lift_left_inverse
- \+ *lemma* lift_surjective_iff
- \+ *lemma* lift_injective_iff
- \+ *lemma* map_eq
- \+ *lemma* map_comp
- \+ *lemma* map_mk'
- \+ *lemma* map_spec
- \+ *lemma* map_mul_right
- \+ *lemma* map_mul_left
- \+ *lemma* map_id
- \+ *lemma* map_comp_map
- \+ *lemma* map_map
- \+ *lemma* mul_equiv_of_localizations_apply
- \+ *lemma* mul_equiv_of_localizations_symm_apply
- \+ *lemma* to_mul_equiv_apply
- \+ *lemma* to_mul_equiv_eq
- \+ *lemma* symm_to_mul_equiv_apply
- \+ *lemma* comp_mul_equiv_symm_map_apply
- \+ *lemma* to_mul_equiv_eq_iff_eq
- \+ *lemma* mul_equiv_of_to_mul_equiv
- \+ *lemma* mul_equiv_of_to_mul_equiv_apply
- \+ *lemma* to_mul_equiv_of_mul_equiv
- \+ *lemma* to_mul_equiv_of_mul_equiv_apply
- \+ *lemma* to_mul_equiv_id
- \+ *lemma* to_mul_equiv_comp
- \+ *lemma* of_mul_equiv_apply
- \+ *lemma* of_mul_equiv_eq
- \+ *lemma* symm_of_mul_equiv_apply
- \+ *lemma* comp_mul_equiv_symm_comap_apply
- \+ *lemma* of_mul_equiv_id
- \+ *lemma* mul_equiv_of_mul_equiv_eq_map_apply
- \+ *lemma* mul_equiv_of_mul_equiv_eq_map
- \+ *lemma* mul_equiv_of_mul_equiv_eq
- \+ *lemma* mul_equiv_of_mul_equiv_mk'
- \+ *lemma* to_mul_equiv_of_mul_equiv_of_mul_equiv_apply
- \+ *lemma* to_mul_equiv_of_mul_equiv_of_mul_equiv
- \- *lemma* exists_of_sec
- \+/\- *theorem* eq_mk'_iff_mul_eq
- \+/\- *theorem* mk'_eq_iff_eq_mul
- \+ *def* to_mul_equiv
- \+ *def* of_mul_equiv

Modified src/group_theory/submonoid.lean
- \+ *lemma* restrict_eq

Modified src/ring_theory/ideals.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/power_series.lean




## [2020-04-03 08:57:48](https://github.com/leanprover-community/mathlib/commit/6af5901)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-03 08:24:57](https://github.com/leanprover-community/mathlib/commit/8af4bb8)
refactor(tactic/lint): split into multiple files ([#2299](https://github.com/leanprover-community/mathlib/pull/2299))
The `lint.lean` file is getting too long for me to comfortably navigate.  This PR splits the file up into several parts:
 * `tactic.lint.basic` defining the `linter` structure and the `@[linter]` and `@[nolint]` attributes
 * `tactic.lint.frontend` defined the functions to run the linters and the various `#lint` commands
 * The linters are split into three separate files, the simp linters, the type class linters, and the rest.
 * `tactic.lint` imports all of the files above so `import tactic.lint` still works as before
#### Estimated changes
Deleted src/tactic/lint.lean


Created src/tactic/lint/basic.lean


Created src/tactic/lint/default.lean


Created src/tactic/lint/frontend.lean


Created src/tactic/lint/misc.lean


Created src/tactic/lint/simp.lean


Created src/tactic/lint/type_classes.lean


Modified test/lint.lean




## [2020-04-03 06:55:45](https://github.com/leanprover-community/mathlib/commit/cb0a1b5)
feat(order/filter): add lemmas about `∀ᶠ`, `∃ᶠ` and logic operations ([#2314](https://github.com/leanprover-community/mathlib/pull/2314))
* feat(order/filter): add lemmas about `∀ᶠ`, `∃ᶠ` and logic operations
* Remove `@[congr]`
* Apply suggestions from code review
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* volume_zero_iff_all_ae_nmem
- \+ *lemma* all_ae_and_iff
- \+ *lemma* all_ae_imp_distrib_left
- \+ *lemma* all_ae_or_distrib_left
- \+ *lemma* all_ae_or_distrib_right

Modified src/order/filter/basic.lean
- \+/\- *lemma* eventually_false_iff_eq_bot
- \+ *lemma* eventually_const
- \+ *lemma* eventually_and
- \+/\- *lemma* eventually.congr
- \+ *lemma* eventually_congr
- \+ *lemma* eventually_or_distrib_left
- \+ *lemma* eventually_or_distrib_right
- \+ *lemma* eventually_imp_distrib_left
- \+/\- *lemma* frequently_true_iff_ne_bot
- \+/\- *lemma* frequently_false
- \+ *lemma* frequently_const
- \+ *lemma* frequently_or_distrib
- \+ *lemma* frequently_or_distrib_left
- \+ *lemma* frequently_or_distrib_right
- \+ *lemma* frequently_imp_distrib
- \+ *lemma* frequently_imp_distrib_left
- \+ *lemma* frequently_imp_distrib_right
- \+ *lemma* eventually_imp_distrib_right
- \+/\- *lemma* frequently_bot
- \- *lemma* eventually.congr_iff

Modified src/order/liminf_limsup.lean




## [2020-04-03 04:11:38](https://github.com/leanprover-community/mathlib/commit/1b24e0a)
chore(test/*): move tests into individual files ([#2317](https://github.com/leanprover-community/mathlib/pull/2317))
#### Estimated changes
Created test/back_chaining.lean
- \+ *theorem* subset_def
- \+ *theorem* union_def
- \+ *theorem* inter_def
- \+ *theorem* union_subset
- \+ *theorem* subset_inter

Created test/choose.lean


Modified test/coinductive.lean


Modified test/examples.lean
- \- *theorem* subset_def
- \- *theorem* union_def
- \- *theorem* inter_def
- \- *theorem* union_subset
- \- *theorem* subset_inter
- \- *def* x
- \- *def* ex

Modified test/ext.lean
- \- *def* my_foo
- \- *def* my_bar

Created test/refine_struct.lean
- \+ *def* my_foo
- \+ *def* my_bar

Created test/traversable.lean
- \+ *def* x
- \+ *def* ex



## [2020-04-02 19:25:32](https://github.com/leanprover-community/mathlib/commit/d3b8622)
fix(tactic/lint): simp_nf: do not ignore errors ([#2266](https://github.com/leanprover-community/mathlib/pull/2266))
This PR fixes some bugs in the `simp_nf` linter.  Previously it ignored all errors (from failing tactics).  I've changed this so that errors from linters are handled centrally and reported as linter warnings.  The `simp_is_conditional` function was also broken.
As usual, new linters find new issues:
 1. Apparently Lean sometimes throws away simp lemmas.  https://github.com/leanprover-community/lean/issues/163
 2. Some types define `has_coe` but have an incorrect `has_coe_to_fun`, causing the simplifier to loop `⇑f a = ⇑↑f a = ⇑f a`.  See the new library note:
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* map_ne_zero
- \+/\- *lemma* map_eq_zero

Modified src/category_theory/monoidal/functorial.lean


Modified src/data/indicator_function.lean
- \+/\- *lemma* indicator_apply

Modified src/data/set/basic.lean
- \+/\- *theorem* ne_empty_iff_nonempty

Modified src/linear_algebra/basic.lean


Modified src/logic/basic.lean


Modified src/order/order_iso.lean
- \+ *lemma* coe_coe_fn
- \- *theorem* coe_coe_fn

Modified src/set_theory/ordinal.lean
- \- *theorem* of_iso_apply

Modified src/tactic/core.lean


Modified src/tactic/lint.lean


Modified src/topology/algebra/module.lean


Modified src/topology/basic.lean
- \- *lemma* subsingleton.is_open
- \- *lemma* subsingleton.is_closed

Modified src/topology/order.lean
- \+ *lemma* is_closed_discrete



## [2020-04-02 16:19:33](https://github.com/leanprover-community/mathlib/commit/654533f)
feat(logic/basic): a few lemmas about `exists_unique` ([#2283](https://github.com/leanprover-community/mathlib/pull/2283))
The goal is to be able to deal with formulas like `∃! x ∈ s, p x`. Lean parses them as `∃! x, ∃! (hx : x ∈ s), p x`. While this is equivalent to `∃! x, x ∈ s ∧ p x`, it is not defeq to this formula.
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* exists_unique.exists
- \+ *lemma* exists_unique.unique
- \+ *lemma* exists_unique_iff_exists
- \+ *lemma* exists_unique.elim2
- \+ *lemma* exists_unique.intro2
- \+ *lemma* exists_unique.exists2
- \+ *lemma* exists_unique.unique2



## [2020-04-02 13:55:30](https://github.com/leanprover-community/mathlib/commit/a88356f)
chore(topology/metric_space): use dot notation ([#2313](https://github.com/leanprover-community/mathlib/pull/2313))
* in `continuous.dist` and `continuous.edist`;
* in `tendsto.dist` and `tendsto.edist`.
#### Estimated changes
Modified src/measure_theory/borel_space.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/ennreal.lean
- \+/\- *theorem* continuous_edist
- \+ *theorem* continuous.edist
- \+ *theorem* filter.tendsto.edist
- \- *theorem* continuous_edist'
- \- *theorem* tendsto_edist

Modified src/topology/metric_space/basic.lean
- \+ *lemma* uniform_continuous_nndist
- \+/\- *lemma* continuous_nndist
- \+ *lemma* continuous.nndist
- \- *lemma* uniform_continuous_nndist'
- \- *lemma* continuous_nndist'
- \- *lemma* tendsto_nndist'
- \+/\- *theorem* continuous_dist
- \+ *theorem* continuous.dist
- \+ *theorem* filter.tendsto.dist
- \+ *theorem* filter.tendsto.nndist
- \- *theorem* continuous_dist'
- \- *theorem* tendsto_dist



## [2020-04-02 11:19:51](https://github.com/leanprover-community/mathlib/commit/3c27d28)
feat(algebra/pi_instances): bundled homs for apply and single ([#2186](https://github.com/leanprover-community/mathlib/pull/2186))
feat(algebra/pi_instances): bundled homs for apply and single ([#2186](https://github.com/leanprover-community/mathlib/pull/2186))
This adds some bundled monoid homomorphisms, in particular
```
def monoid_hom.apply (i : I) : (Π i, f i) →* f i := ...
```
and
```
def add_monoid_hom.single (i : I) : f i →+ Π i, f i :=
```
and supporting lemmas.
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+/\- *lemma* ring_hom.map_sum

Modified src/algebra/group/prod.lean


Modified src/algebra/pi_instances.lean
- \+ *lemma* single_eq_same
- \+ *lemma* single_eq_of_ne
- \+ *lemma* monoid_hom.apply_apply
- \+ *lemma* ring_hom.apply_apply
- \+ *lemma* finset.prod_apply
- \+ *lemma* finset.univ_sum_single
- \+ *lemma* add_monoid_hom.single_apply
- \+ *lemma* add_monoid_hom.functions_ext
- \+ *lemma* ring_hom.functions_ext
- \+ *def* single
- \+ *def* monoid_hom.apply
- \+ *def* ring_hom.apply
- \+ *def* add_monoid_hom.single



## [2020-04-02 08:17:59](https://github.com/leanprover-community/mathlib/commit/313cc2f)
chore(category_theory/concrete_category): take an instance, rather than extending, category ([#2195](https://github.com/leanprover-community/mathlib/pull/2195))
chore(category_theory/concrete_category): take an instance, rather than extending, category ([#2195](https://github.com/leanprover-community/mathlib/pull/2195))
Our current design for `concrete_category` has it extend `category`.
This PR changes that so that is takes an instance, instead.
I want to do this because I ran into a problem defining `concrete_monoidal_category`, which is meant to be a monoidal category, whose faithful functor to Type is lax monoidal. (The prime example here is `Module R`, where there's a map `F(X) \otimes F(Y) \to F(X \otimes Y)`, but not the other way: here `F(X) \otimes F(Y)` is just the monoidal product in Type, i.e. cartesian product, and the function here is `(x, y) \mapsto x \otimes y`.)
Now, `monoidal_category` does not extend `category`, but instead takes a typeclass, so with the old design `concrete_monoidal_category` was going to be a Frankenstein, extending `concrete_category` and taking a `[monoidal_category]` type class. However, when 3.7 landed this went horribly wrong, and even defining `concrete_monoidal_category` caused an unbounded typeclass search.
So.... I've made everything simpler, and just not used `extends` at all. It's all just typeclasses. This makes some places a bit more verbose, as we have to summon lots of separate typeclasses, but besides that everything works smoothly.
(Note, this PR makes the change to `concrete_category`, but does not yet introduce `concrete_monoidal_category`.)
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Module/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/category_theory/concrete_category/basic.lean
- \+/\- *def* forget
- \+/\- *def* concrete_category.has_coe_to_sort
- \+/\- *def* forget₂
- \+/\- *def* has_forget₂.mk'

Modified src/category_theory/differential_object.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/limits/cones.lean


Modified src/topology/category/TopCommRing.lean


Modified src/topology/category/UniformSpace.lean




## [2020-04-02 05:51:39](https://github.com/leanprover-community/mathlib/commit/f55e3ce)
refactor(*): move `algebra` below `polynomial` in the `import` chain ([#2294](https://github.com/leanprover-community/mathlib/pull/2294))
* Move `algebra` below `polynomial` in the `import` chain
This PR only moves code and slightly generalizes
`mv_polynomial.aeval`.
* Fix compile
* Update src/data/mv_polynomial.lean
* Apply suggestions from code review
* Apply suggestions from code review
Co-Authored-By: Bryan Gin-ge Chen <bryangingechen@gmail.com>
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/data/mv_polynomial.lean
- \+ *lemma* aeval_X
- \+ *lemma* aeval_C
- \+ *theorem* aeval_def
- \+ *theorem* eval_unique
- \+ *def* aeval

Modified src/data/polynomial.lean
- \+ *lemma* aeval_X
- \+ *lemma* aeval_C
- \+ *theorem* aeval_def
- \+ *theorem* eval_unique
- \+ *def* aeval

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra.lean
- \- *lemma* aeval_X
- \- *lemma* aeval_C
- \- *theorem* aeval_def
- \- *theorem* eval_unique
- \- *def* aeval

Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/free_comm_ring.lean




## [2020-04-02 03:27:11](https://github.com/leanprover-community/mathlib/commit/652fc17)
chore(data/set/lattice): add `set_of_exists` and `set_of_forall` ([#2312](https://github.com/leanprover-community/mathlib/pull/2312))
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *theorem* set_of_exists
- \+ *theorem* set_of_forall



## [2020-04-01 22:05:57](https://github.com/leanprover-community/mathlib/commit/5b972be)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-01 21:30:30](https://github.com/leanprover-community/mathlib/commit/33764ab)
chore(tactic/transport): rename to transform_decl ([#2308](https://github.com/leanprover-community/mathlib/pull/2308))
* chore(tactic/transport): rename to transform_decl
* satisfying the linter
* oops, wrong comment format
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Created src/tactic/transform_decl.lean


Deleted src/tactic/transport.lean




## [2020-04-01 18:42:34](https://github.com/leanprover-community/mathlib/commit/badc615)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-01 18:06:00](https://github.com/leanprover-community/mathlib/commit/a8076b2)
refactor(data/real/irrational): review ([#2304](https://github.com/leanprover-community/mathlib/pull/2304))
* refactor(data/real/irrational): review
* Update src/data/real/irrational.lean
* Update src/data/real/irrational.lean
* Apply suggestions from code review
#### Estimated changes
Modified src/data/real/irrational.lean
- \+ *lemma* rat.not_irrational
- \+ *theorem* irrational_nrt_of_notint_nrt
- \+ *theorem* irrational_nrt_of_n_not_dvd_multiplicity
- \+ *theorem* irrational_sqrt_of_multiplicity_odd
- \+ *theorem* nat.prime.irrational_sqrt
- \+ *theorem* irrational_sqrt_two
- \+ *theorem* irrational_sqrt_rat_iff
- \+ *theorem* add_cases
- \+ *theorem* of_rat_add
- \+ *theorem* rat_add
- \+ *theorem* of_add_rat
- \+ *theorem* add_rat
- \+ *theorem* of_neg
- \+ *theorem* sub_rat
- \+ *theorem* rat_sub
- \+ *theorem* of_sub_rat
- \+ *theorem* of_rat_sub
- \+ *theorem* mul_cases
- \+ *theorem* of_mul_rat
- \+ *theorem* mul_rat
- \+ *theorem* of_rat_mul
- \+ *theorem* rat_mul
- \+ *theorem* of_mul_self
- \+ *theorem* of_inv
- \+ *theorem* div_cases
- \+ *theorem* of_rat_div
- \+ *theorem* of_one_div
- \+ *theorem* of_pow
- \+ *theorem* of_fpow
- \+ *theorem* irrational_rat_add_iff
- \+ *theorem* irrational_add_rat_iff
- \+ *theorem* irrational_rat_sub_iff
- \+ *theorem* irrational_sub_rat_iff
- \+ *theorem* irrational_neg_iff
- \+ *theorem* irrational_inv_iff
- \- *theorem* irr_nrt_of_notint_nrt
- \- *theorem* irr_nrt_of_n_not_dvd_multiplicity
- \- *theorem* irr_sqrt_of_multiplicity_odd
- \- *theorem* irr_sqrt_of_prime
- \- *theorem* irr_sqrt_two
- \- *theorem* irr_sqrt_rat_iff
- \- *theorem* irr_rat_add_of_irr
- \- *theorem* irr_rat_add_iff_irr
- \- *theorem* irr_add_rat_iff_irr
- \- *theorem* irr_mul_rat_iff_irr
- \- *theorem* irr_of_irr_mul_self
- \- *theorem* irr_neg
- \+/\- *def* irrational



## [2020-04-01 13:29:58](https://github.com/leanprover-community/mathlib/commit/203ebb2)
feat(tactic/simp_rw): support `<-` in `simp_rw` ([#2309](https://github.com/leanprover-community/mathlib/pull/2309))
#### Estimated changes
Modified src/tactic/simp_rw.lean


Modified test/simp_rw.lean




## [2020-04-01 10:26:28](https://github.com/leanprover-community/mathlib/commit/fb658ac)
chore(scripts): update nolints.txt
#### Estimated changes
Modified scripts/nolints.txt




## [2020-04-01 09:50:28](https://github.com/leanprover-community/mathlib/commit/003141c)
chore(algebra/module): cleanup `is_linear_map` ([#2296](https://github.com/leanprover-community/mathlib/pull/2296))
* reuse facts about `→+`;
* add `map_smul`
* add a few docstrings
#### Estimated changes
Modified src/algebra/module.lean
- \+/\- *lemma* map_zero
- \+/\- *lemma* map_add
- \+/\- *lemma* map_neg
- \+/\- *lemma* map_sub
- \+ *lemma* map_smul
- \+/\- *def* id



## [2020-04-01 06:47:48](https://github.com/leanprover-community/mathlib/commit/c7fb84b)
refactor(group_theory/submonoid): review API ([#2173](https://github.com/leanprover-community/mathlib/pull/2173))
The old API was mirroring the API for unbundled submonoids, while the
new one is based on the API of `submodule`.
Also move some facts about `monoid`/`group` structure on `M × N` to
`algebra/group/prod`.
#### Estimated changes
Modified src/algebra/free_monoid.lean
- \+ *lemma* lift_apply
- \+ *lemma* lift_comp_of
- \+ *lemma* comp_lift

Modified src/algebra/group/default.lean


Modified src/algebra/group/hom.lean
- \+ *lemma* comp_id
- \+ *lemma* id_comp

Created src/algebra/group/prod.lean
- \+ *lemma* fst_mul
- \+ *lemma* snd_mul
- \+ *lemma* mk_mul_mk
- \+ *lemma* fst_one
- \+ *lemma* snd_one
- \+ *lemma* one_eq_mk
- \+ *lemma* fst_mul_snd
- \+ *lemma* fst_inv
- \+ *lemma* snd_inv
- \+ *lemma* inv_mk
- \+ *lemma* fst_sub
- \+ *lemma* snd_sub
- \+ *lemma* mk_sub_mk
- \+ *lemma* coe_fst
- \+ *lemma* coe_snd
- \+ *lemma* inl_apply
- \+ *lemma* inr_apply
- \+ *lemma* fst_comp_inl
- \+ *lemma* snd_comp_inl
- \+ *lemma* fst_comp_inr
- \+ *lemma* snd_comp_inr
- \+ *lemma* prod_apply
- \+ *lemma* fst_comp_prod
- \+ *lemma* snd_comp_prod
- \+ *lemma* prod_unique
- \+ *lemma* prod_map_def
- \+ *lemma* coe_prod_map
- \+ *lemma* prod_comp_prod_map
- \+ *lemma* coprod_apply
- \+ *lemma* coprod_comp_inl
- \+ *lemma* coprod_comp_inr
- \+ *lemma* coprod_unique
- \+ *lemma* coprod_inl_inr
- \+ *lemma* comp_coprod
- \+ *def* fst
- \+ *def* snd
- \+ *def* inl
- \+ *def* inr
- \+ *def* prod_map
- \+ *def* coprod

Modified src/algebra/pi_instances.lean
- \- *lemma* fst_mul
- \- *lemma* snd_mul
- \- *lemma* mk_mul_mk
- \- *lemma* fst_one
- \- *lemma* snd_one
- \- *lemma* one_eq_mk
- \- *lemma* fst_inv
- \- *lemma* snd_inv
- \- *lemma* inv_mk
- \- *lemma* fst_sub
- \- *lemma* snd_sub
- \- *lemma* mk_sub_mk
- \- *def* monoid_hom.fst
- \- *def* monoid_hom.snd
- \- *def* monoid_hom.inl
- \- *def* monoid_hom.inr
- \- *def* prod

Modified src/data/prod.lean
- \+ *lemma* fst_surjective
- \+ *lemma* snd_surjective
- \+ *lemma* fst_injective
- \+ *lemma* snd_injective

Modified src/group_theory/congruence.lean
- \+/\- *lemma* ker_lift_range_eq
- \+/\- *theorem* lift_range

Modified src/group_theory/submonoid.lean
- \+/\- *lemma* mem_coe
- \+ *lemma* coe_coe
- \+/\- *lemma* list_prod_mem
- \+/\- *lemma* multiset_prod_mem
- \+/\- *lemma* pow_mem
- \+/\- *lemma* le_def
- \+ *lemma* coe_subset_coe
- \+ *lemma* coe_ssubset_coe
- \+ *lemma* coe_top
- \+ *lemma* coe_bot
- \+ *lemma* coe_inf
- \+/\- *lemma* mem_inf
- \+ *lemma* coe_Inf
- \+ *lemma* mem_closure
- \+ *lemma* subset_closure
- \+ *lemma* closure_le
- \+ *lemma* closure_mono
- \+ *lemma* closure_eq_of_le
- \+ *lemma* closure_induction
- \+ *lemma* closure_eq
- \+ *lemma* closure_empty
- \+ *lemma* closure_univ
- \+ *lemma* closure_union
- \+ *lemma* closure_Union
- \+ *lemma* mem_closure_singleton
- \+ *lemma* mem_supr_of_directed
- \+ *lemma* mem_Sup_of_directed_on
- \+ *lemma* coe_comap
- \+ *lemma* mem_comap
- \+ *lemma* comap_comap
- \+ *lemma* coe_map
- \+ *lemma* mem_map
- \+ *lemma* map_map
- \+ *lemma* map_le_iff_le_comap
- \+ *lemma* gc_map_comap
- \+ *lemma* map_sup
- \+ *lemma* map_supr
- \+ *lemma* comap_inf
- \+ *lemma* comap_infi
- \+ *lemma* map_bot
- \+ *lemma* comap_top
- \+ *lemma* coe_prod
- \+ *lemma* mem_prod
- \+ *lemma* prod_mono
- \+ *lemma* prod_mono_right
- \+ *lemma* prod_mono_left
- \+ *lemma* prod_top
- \+ *lemma* top_prod
- \+ *lemma* top_prod_top
- \+ *lemma* bot_prod_bot
- \+/\- *lemma* smul_mem
- \+ *lemma* coe_mrange
- \+ *lemma* mem_mrange
- \+ *lemma* map_mrange
- \+ *lemma* restrict_apply
- \+ *lemma* coe_range_restrict
- \+ *lemma* mrange_top_iff_surjective
- \+ *lemma* mrange_top_of_surjective
- \+ *lemma* eq_on_mclosure
- \+ *lemma* eq_of_eq_on_mtop
- \+ *lemma* eq_of_eq_on_mdense
- \+ *lemma* closure_preimage_le
- \+ *lemma* map_mclosure
- \+ *lemma* range_subtype
- \+ *lemma* closure_eq_mrange
- \+ *lemma* exists_list_of_mem_closure
- \+ *lemma* map_inl
- \+ *lemma* map_inr
- \+ *lemma* range_inl
- \+ *lemma* range_inr
- \+ *lemma* range_inl'
- \+ *lemma* range_inr'
- \+ *lemma* range_fst
- \+ *lemma* range_snd
- \+ *lemma* prod_bot_sup_bot_prod
- \+ *lemma* range_inl_sup_range_inr
- \+ *lemma* sup_eq_range
- \+ *lemma* mem_sup
- \- *lemma* subtype_eq_val
- \- *lemma* powers.self_mem
- \- *lemma* powers_subset
- \- *lemma* coe_pow
- \- *lemma* multiples.self_mem
- \- *lemma* multiples_subset
- \- *lemma* coe_smul
- \- *lemma* Inf_le'
- \- *lemma* le_Inf'
- \- *lemma* finset_prod_mem
- \- *lemma* range_top_of_surjective
- \- *lemma* image_closure'
- \+ *theorem* coe_subtype
- \+ *theorem* closure_range_of
- \- *theorem* subtype_apply
- \- *theorem* le_closure'
- \- *theorem* closure'_le
- \- *theorem* closure'_mono
- \- *theorem* closure'_singleton
- \- *theorem* exists_list_of_mem_closure'
- \- *theorem* mem_closure'_union_iff
- \+ *def* submonoid.of
- \+/\- *def* subtype
- \+ *def* closure
- \+/\- *def* comap
- \+/\- *def* map
- \+ *def* prod
- \+ *def* prod_equiv
- \+ *def* mrange
- \+/\- *def* restrict
- \+ *def* cod_restrict
- \+ *def* range_restrict
- \+ *def* eq_mlocus
- \+ *def* inclusion
- \- *def* Union_of_directed
- \- *def* powers
- \- *def* multiples
- \- *def* univ
- \- *def* bot
- \- *def* inf
- \- *def* range
- \- *def* subtype_mk
- \- *def* range_mk
- \- *def* set_inclusion
- \- *def* closure'

Modified src/order/galois_connection.lean




## [2020-04-01 04:05:06](https://github.com/leanprover-community/mathlib/commit/67e7f90)
fix(algebra/category): make has_coe_to_sort instances for bundled categories reducible ([#2290](https://github.com/leanprover-community/mathlib/pull/2290))
* fix(algebra/category): make has_coe_to_sort instances for bundled categories reducible
* fix library notes
* fix import
* Update src/algebra/category/CommRing/basic.lean
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* fix notes
#### Estimated changes
Modified src/algebra/category/CommRing/basic.lean


Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/category_theory/concrete_category/bundled.lean


Modified src/category_theory/full_subcategory.lean




## [2020-04-01 01:14:10](https://github.com/leanprover-community/mathlib/commit/cc20a86)
feat(data/nat/basic): `simp` lemmas about inequalities with `bit*` ([#2207](https://github.com/leanprover-community/mathlib/pull/2207))
* feat(data/nat/basic): `simp` lemmas about inequalities with `bit*`
* Fix compile of `computability/partrec_code`
* Fix `nat.bit_cases` to work for `Type*` too
* Generalize some lemmas to `linear_ordered_semiring`s
* Apply suggestions from code review
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
* Apply suggestions from code review
Co-Authored-By: Scott Morrison <scott@tqft.net>
* fixing a proof
#### Estimated changes
Modified src/algebra/ordered_ring.lean
- \+ *lemma* zero_le_mul_left
- \+ *lemma* zero_le_mul_right
- \+ *lemma* zero_lt_mul_left
- \+ *lemma* zero_lt_mul_right
- \+ *lemma* bit0_le_bit0
- \+ *lemma* bit0_lt_bit0
- \+ *lemma* bit1_le_bit1
- \+ *lemma* bit1_lt_bit1
- \+ *lemma* one_le_bit1
- \+ *lemma* one_lt_bit1
- \+ *lemma* zero_le_bit0
- \+ *lemma* zero_lt_bit0

Modified src/computability/partrec_code.lean


Modified src/data/nat/basic.lean
- \+ *lemma* bit0_le_bit1_iff
- \+ *lemma* bit0_lt_bit1_iff
- \+ *lemma* bit1_le_bit0_iff
- \+ *lemma* bit1_lt_bit0_iff
- \+ *lemma* one_le_bit0_iff
- \+ *lemma* one_lt_bit0_iff
- \+ *lemma* bit_le_bit_iff
- \+ *lemma* bit_lt_bit_iff
- \+ *lemma* bit_le_bit1_iff
- \+ *def* bit_cases

Modified src/data/real/pi.lean


