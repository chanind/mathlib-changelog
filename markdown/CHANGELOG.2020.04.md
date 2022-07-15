## [2020-04-30 21:10:46](https://github.com/leanprover-community/mathlib/commit/c568bb4)
fix(scripts): stop updating mathlib-nightly repository ([#2576](https://github.com/leanprover-community/mathlib/pull/2576))
The `gothub` tool that we've used to push the nightlies doesn't build at the moment.  Now that we have `leanproject`, we no longer need the separate nightlies repository.
#### Estimated changes
Modified .github/workflows/build.yml


Deleted scripts/deploy_nightly.sh


Added scripts/update_branch.sh




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
- \+ *lemma* finset.sum_mul_sum

Modified src/algebra/group_with_zero.lean
- \+ *lemma* is_unit.mk0
- \+ *lemma* is_unit_iff_ne_zero
- \+ *lemma* units.exists_iff_ne_zero

Modified src/data/fintype/basic.lean
- \+ *lemma* finset.inter_univ
- \+ *lemma* finset.univ_inter
- \+ *lemma* set.to_finset_univ

Modified src/data/fintype/card.lean
- \+ *lemma* fintype.prod_extend_by_one

Modified src/group_theory/order_of_element.lean
- \+ *lemma* image_range_order_of
- \+ *lemma* is_cyclic.image_range_card
- \+ *lemma* is_cyclic.image_range_order_of



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
- \+/\- *lemma* ennreal.tsum_geometric
- \+/\- *lemma* tsum_geometric
- \+/\- *lemma* tsum_geometric_nnreal
- \+/\- *lemma* tsum_geometric_two'
- \+/\- *lemma* tsum_geometric_two

Modified src/data/real/cardinality.lean
- \+/\- *def* cardinal.cantor_function

Modified src/measure_theory/integration.lean


Modified src/measure_theory/lebesgue_measure.lean


Modified src/measure_theory/measure_space.lean
- \+/\- *theorem* measure_theory.measure_Union_le

Modified src/measure_theory/outer_measure.lean


Modified src/measure_theory/probability_mass_function.lean
- \+/\- *lemma* pmf.bind_apply
- \+/\- *lemma* pmf.tsum_coe

Modified src/measure_theory/set_integral.lean


Modified src/number_theory/bernoulli.lean


Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* summable.has_sum
- \+/\- *lemma* summable.has_sum_iff
- \+/\- *lemma* tsum_add
- \+/\- *lemma* tsum_eq_has_sum
- \+/\- *lemma* tsum_eq_zero_add
- \+/\- *lemma* tsum_eq_zero_of_not_summable
- \+/\- *lemma* tsum_equiv
- \+/\- *lemma* tsum_fintype
- \+/\- *lemma* tsum_ite_eq
- \+/\- *lemma* tsum_le_tsum
- \+/\- *lemma* tsum_mul_left
- \+/\- *lemma* tsum_mul_right
- \+/\- *lemma* tsum_neg
- \+/\- *lemma* tsum_nonneg
- \+/\- *lemma* tsum_nonpos
- \+/\- *lemma* tsum_sub
- \+/\- *lemma* tsum_zero

Modified src/topology/instances/ennreal.lean


Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* nnreal.coe_tsum



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


Added test/inhabit.lean
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


Added src/analysis/special_functions/exp_log.lean
- \+ *lemma* complex.continuous_exp
- \+ *lemma* complex.deriv_exp
- \+ *lemma* complex.differentiable_at_exp
- \+ *lemma* complex.differentiable_exp
- \+ *lemma* complex.has_deriv_at_exp
- \+ *lemma* complex.iter_deriv_exp
- \+ *lemma* deriv_cexp
- \+ *lemma* deriv_exp
- \+ *lemma* deriv_log'
- \+ *lemma* deriv_within_cexp
- \+ *lemma* deriv_within_exp
- \+ *lemma* deriv_within_log'
- \+ *lemma* differentiable.cexp
- \+ *lemma* differentiable.exp
- \+ *lemma* differentiable.log
- \+ *lemma* differentiable_at.cexp
- \+ *lemma* differentiable_at.exp
- \+ *lemma* differentiable_at.log
- \+ *lemma* differentiable_on.cexp
- \+ *lemma* differentiable_on.exp
- \+ *lemma* differentiable_on.log
- \+ *lemma* differentiable_within_at.cexp
- \+ *lemma* differentiable_within_at.exp
- \+ *lemma* differentiable_within_at.log
- \+ *lemma* has_deriv_at.cexp
- \+ *lemma* has_deriv_at.exp
- \+ *lemma* has_deriv_at.log
- \+ *lemma* has_deriv_within_at.cexp
- \+ *lemma* has_deriv_within_at.exp
- \+ *lemma* has_deriv_within_at.log
- \+ *lemma* real.continuous_at_log
- \+ *lemma* real.continuous_exp
- \+ *lemma* real.continuous_log'
- \+ *lemma* real.continuous_log
- \+ *lemma* real.deriv_exp
- \+ *lemma* real.differentiable_at_exp
- \+ *lemma* real.differentiable_exp
- \+ *lemma* real.exists_exp_eq_of_pos
- \+ *lemma* real.exp_log
- \+ *lemma* real.exp_log_eq_abs
- \+ *lemma* real.has_deriv_at_exp
- \+ *lemma* real.has_deriv_at_log
- \+ *lemma* real.has_deriv_at_log_of_pos
- \+ *lemma* real.iter_deriv_exp
- \+ *lemma* real.log_abs
- \+ *lemma* real.log_exp
- \+ *lemma* real.log_le_log
- \+ *lemma* real.log_lt_log
- \+ *lemma* real.log_lt_log_iff
- \+ *lemma* real.log_mul
- \+ *lemma* real.log_neg
- \+ *lemma* real.log_neg_eq_log
- \+ *lemma* real.log_neg_iff
- \+ *lemma* real.log_nonneg
- \+ *lemma* real.log_nonpos
- \+ *lemma* real.log_one
- \+ *lemma* real.log_pos
- \+ *lemma* real.log_pos_iff
- \+ *lemma* real.log_zero
- \+ *lemma* real.tendsto_exp_at_top
- \+ *lemma* real.tendsto_exp_div_pow_at_top
- \+ *lemma* real.tendsto_exp_neg_at_top_nhds_0
- \+ *lemma* real.tendsto_log_one_zero
- \+ *lemma* real.tendsto_pow_mul_exp_neg_at_top_nhds_0

Added src/analysis/special_functions/pow.lean
- \+ *lemma* complex.abs_cpow_inv_nat
- \+ *lemma* complex.abs_cpow_real
- \+ *lemma* complex.cpow_add
- \+ *lemma* complex.cpow_def
- \+ *lemma* complex.cpow_eq_pow
- \+ *lemma* complex.cpow_eq_zero_iff
- \+ *lemma* complex.cpow_int_cast
- \+ *lemma* complex.cpow_mul
- \+ *lemma* complex.cpow_nat_cast
- \+ *lemma* complex.cpow_nat_inv_pow
- \+ *lemma* complex.cpow_neg
- \+ *lemma* complex.cpow_one
- \+ *lemma* complex.cpow_zero
- \+ *lemma* complex.of_real_cpow
- \+ *lemma* complex.one_cpow
- \+ *lemma* complex.zero_cpow
- \+ *lemma* filter.tendsto.nnrpow
- \+ *lemma* nnreal.coe_rpow
- \+ *lemma* nnreal.continuous_at_rpow
- \+ *lemma* nnreal.mul_rpow
- \+ *lemma* nnreal.one_le_rpow
- \+ *lemma* nnreal.one_lt_rpow
- \+ *lemma* nnreal.one_rpow
- \+ *lemma* nnreal.pow_nat_rpow_nat_inv
- \+ *lemma* nnreal.rpow_add
- \+ *lemma* nnreal.rpow_eq_pow
- \+ *lemma* nnreal.rpow_eq_zero_iff
- \+ *lemma* nnreal.rpow_le_one
- \+ *lemma* nnreal.rpow_le_rpow
- \+ *lemma* nnreal.rpow_le_rpow_of_exponent_ge
- \+ *lemma* nnreal.rpow_le_rpow_of_exponent_le
- \+ *lemma* nnreal.rpow_lt_one
- \+ *lemma* nnreal.rpow_lt_rpow
- \+ *lemma* nnreal.rpow_lt_rpow_of_exponent_gt
- \+ *lemma* nnreal.rpow_lt_rpow_of_exponent_lt
- \+ *lemma* nnreal.rpow_mul
- \+ *lemma* nnreal.rpow_nat_cast
- \+ *lemma* nnreal.rpow_nat_inv_pow_nat
- \+ *lemma* nnreal.rpow_neg
- \+ *lemma* nnreal.rpow_one
- \+ *lemma* nnreal.rpow_zero
- \+ *lemma* nnreal.zero_rpow
- \+ *lemma* real.abs_rpow_le_abs_rpow
- \+ *lemma* real.continuous_at_rpow
- \+ *lemma* real.continuous_at_rpow_of_ne_zero
- \+ *lemma* real.continuous_at_rpow_of_pos
- \+ *lemma* real.continuous_rpow
- \+ *lemma* real.continuous_rpow_aux1
- \+ *lemma* real.continuous_rpow_aux2
- \+ *lemma* real.continuous_rpow_aux3
- \+ *lemma* real.continuous_rpow_of_ne_zero
- \+ *lemma* real.continuous_rpow_of_pos
- \+ *lemma* real.continuous_sqrt
- \+ *lemma* real.mul_rpow
- \+ *lemma* real.one_le_rpow
- \+ *lemma* real.one_lt_rpow
- \+ *lemma* real.one_rpow
- \+ *lemma* real.pow_nat_rpow_nat_inv
- \+ *lemma* real.rpow_add
- \+ *lemma* real.rpow_def
- \+ *lemma* real.rpow_def_of_neg
- \+ *lemma* real.rpow_def_of_nonneg
- \+ *lemma* real.rpow_def_of_nonpos
- \+ *lemma* real.rpow_def_of_pos
- \+ *lemma* real.rpow_eq_pow
- \+ *lemma* real.rpow_eq_zero_iff_of_nonneg
- \+ *lemma* real.rpow_int_cast
- \+ *lemma* real.rpow_le_one
- \+ *lemma* real.rpow_le_rpow
- \+ *lemma* real.rpow_le_rpow_of_exponent_ge
- \+ *lemma* real.rpow_le_rpow_of_exponent_le
- \+ *lemma* real.rpow_lt_one
- \+ *lemma* real.rpow_lt_rpow
- \+ *lemma* real.rpow_lt_rpow_of_exponent_gt
- \+ *lemma* real.rpow_lt_rpow_of_exponent_lt
- \+ *lemma* real.rpow_mul
- \+ *lemma* real.rpow_nat_cast
- \+ *lemma* real.rpow_nat_inv_pow_nat
- \+ *lemma* real.rpow_neg
- \+ *lemma* real.rpow_nonneg_of_nonneg
- \+ *lemma* real.rpow_one
- \+ *lemma* real.rpow_pos_of_pos
- \+ *lemma* real.rpow_zero
- \+ *lemma* real.sqrt_eq_rpow
- \+ *lemma* real.zero_rpow

Renamed src/analysis/complex/exponential.lean to src/analysis/special_functions/trigonometric.lean
- \- *lemma* complex.abs_cpow_inv_nat
- \- *lemma* complex.abs_cpow_real
- \- *lemma* complex.continuous_exp
- \- *lemma* complex.cpow_add
- \- *lemma* complex.cpow_def
- \- *lemma* complex.cpow_eq_pow
- \- *lemma* complex.cpow_eq_zero_iff
- \- *lemma* complex.cpow_int_cast
- \- *lemma* complex.cpow_mul
- \- *lemma* complex.cpow_nat_cast
- \- *lemma* complex.cpow_nat_inv_pow
- \- *lemma* complex.cpow_neg
- \- *lemma* complex.cpow_one
- \- *lemma* complex.cpow_zero
- \- *lemma* complex.deriv_exp
- \- *lemma* complex.differentiable_at_exp
- \- *lemma* complex.differentiable_exp
- \- *lemma* complex.has_deriv_at_exp
- \- *lemma* complex.iter_deriv_exp
- \- *lemma* complex.of_real_cpow
- \- *lemma* complex.one_cpow
- \- *lemma* complex.zero_cpow
- \- *lemma* deriv_cexp
- \- *lemma* deriv_exp
- \- *lemma* deriv_log'
- \- *lemma* deriv_within_cexp
- \- *lemma* deriv_within_exp
- \- *lemma* deriv_within_log'
- \- *lemma* differentiable.cexp
- \- *lemma* differentiable.exp
- \- *lemma* differentiable.log
- \- *lemma* differentiable_at.cexp
- \- *lemma* differentiable_at.exp
- \- *lemma* differentiable_at.log
- \- *lemma* differentiable_on.cexp
- \- *lemma* differentiable_on.exp
- \- *lemma* differentiable_on.log
- \- *lemma* differentiable_within_at.cexp
- \- *lemma* differentiable_within_at.exp
- \- *lemma* differentiable_within_at.log
- \- *lemma* filter.tendsto.nnrpow
- \- *lemma* has_deriv_at.cexp
- \- *lemma* has_deriv_at.exp
- \- *lemma* has_deriv_at.log
- \- *lemma* has_deriv_at.rexp
- \- *lemma* has_deriv_within_at.cexp
- \- *lemma* has_deriv_within_at.exp
- \- *lemma* has_deriv_within_at.log
- \- *lemma* has_deriv_within_at.rexp
- \- *lemma* nnreal.coe_rpow
- \- *lemma* nnreal.continuous_at_rpow
- \- *lemma* nnreal.mul_rpow
- \- *lemma* nnreal.one_le_rpow
- \- *lemma* nnreal.one_lt_rpow
- \- *lemma* nnreal.one_rpow
- \- *lemma* nnreal.pow_nat_rpow_nat_inv
- \- *lemma* nnreal.rpow_add
- \- *lemma* nnreal.rpow_eq_pow
- \- *lemma* nnreal.rpow_eq_zero_iff
- \- *lemma* nnreal.rpow_le_one
- \- *lemma* nnreal.rpow_le_rpow
- \- *lemma* nnreal.rpow_le_rpow_of_exponent_ge
- \- *lemma* nnreal.rpow_le_rpow_of_exponent_le
- \- *lemma* nnreal.rpow_lt_one
- \- *lemma* nnreal.rpow_lt_rpow
- \- *lemma* nnreal.rpow_lt_rpow_of_exponent_gt
- \- *lemma* nnreal.rpow_lt_rpow_of_exponent_lt
- \- *lemma* nnreal.rpow_mul
- \- *lemma* nnreal.rpow_nat_cast
- \- *lemma* nnreal.rpow_nat_inv_pow_nat
- \- *lemma* nnreal.rpow_neg
- \- *lemma* nnreal.rpow_one
- \- *lemma* nnreal.rpow_zero
- \- *lemma* nnreal.zero_rpow
- \- *lemma* real.abs_rpow_le_abs_rpow
- \- *lemma* real.continuous_at_log
- \- *lemma* real.continuous_at_rpow
- \- *lemma* real.continuous_at_rpow_of_ne_zero
- \- *lemma* real.continuous_at_rpow_of_pos
- \- *lemma* real.continuous_exp
- \- *lemma* real.continuous_log'
- \- *lemma* real.continuous_log
- \- *lemma* real.continuous_rpow
- \- *lemma* real.continuous_rpow_aux1
- \- *lemma* real.continuous_rpow_aux2
- \- *lemma* real.continuous_rpow_aux3
- \- *lemma* real.continuous_rpow_of_ne_zero
- \- *lemma* real.continuous_rpow_of_pos
- \- *lemma* real.continuous_sqrt
- \- *lemma* real.deriv_exp
- \- *lemma* real.differentiable_at_exp
- \- *lemma* real.differentiable_exp
- \- *lemma* real.exists_exp_eq_of_pos
- \- *lemma* real.exp_log
- \- *lemma* real.exp_log_eq_abs
- \- *lemma* real.has_deriv_at_exp
- \- *lemma* real.has_deriv_at_log
- \- *lemma* real.has_deriv_at_log_of_pos
- \- *lemma* real.iter_deriv_exp
- \- *lemma* real.log_abs
- \- *lemma* real.log_exp
- \- *lemma* real.log_le_log
- \- *lemma* real.log_lt_log
- \- *lemma* real.log_lt_log_iff
- \- *lemma* real.log_mul
- \- *lemma* real.log_neg
- \- *lemma* real.log_neg_eq_log
- \- *lemma* real.log_neg_iff
- \- *lemma* real.log_nonneg
- \- *lemma* real.log_nonpos
- \- *lemma* real.log_one
- \- *lemma* real.log_pos
- \- *lemma* real.log_pos_iff
- \- *lemma* real.log_zero
- \- *lemma* real.mul_rpow
- \- *lemma* real.one_le_rpow
- \- *lemma* real.one_lt_rpow
- \- *lemma* real.one_rpow
- \- *lemma* real.pow_nat_rpow_nat_inv
- \- *lemma* real.rpow_add
- \- *lemma* real.rpow_def
- \- *lemma* real.rpow_def_of_neg
- \- *lemma* real.rpow_def_of_nonneg
- \- *lemma* real.rpow_def_of_nonpos
- \- *lemma* real.rpow_def_of_pos
- \- *lemma* real.rpow_eq_pow
- \- *lemma* real.rpow_eq_zero_iff_of_nonneg
- \- *lemma* real.rpow_int_cast
- \- *lemma* real.rpow_le_one
- \- *lemma* real.rpow_le_rpow
- \- *lemma* real.rpow_le_rpow_of_exponent_ge
- \- *lemma* real.rpow_le_rpow_of_exponent_le
- \- *lemma* real.rpow_lt_one
- \- *lemma* real.rpow_lt_rpow
- \- *lemma* real.rpow_lt_rpow_of_exponent_gt
- \- *lemma* real.rpow_lt_rpow_of_exponent_lt
- \- *lemma* real.rpow_mul
- \- *lemma* real.rpow_nat_cast
- \- *lemma* real.rpow_nat_inv_pow_nat
- \- *lemma* real.rpow_neg
- \- *lemma* real.rpow_nonneg_of_nonneg
- \- *lemma* real.rpow_one
- \- *lemma* real.rpow_pos_of_pos
- \- *lemma* real.rpow_zero
- \- *lemma* real.sqrt_eq_rpow
- \- *lemma* real.tendsto_exp_at_top
- \- *lemma* real.tendsto_exp_div_pow_at_top
- \- *lemma* real.tendsto_exp_neg_at_top_nhds_0
- \- *lemma* real.tendsto_log_one_zero
- \- *lemma* real.tendsto_pow_mul_exp_neg_at_top_nhds_0
- \- *lemma* real.zero_rpow

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
- \+ *lemma* complex.log_of_real_re
- \+ *lemma* deriv_log'
- \+ *lemma* deriv_within_log'
- \+ *lemma* differentiable.log
- \+ *lemma* differentiable_at.log
- \+ *lemma* differentiable_on.log
- \+ *lemma* differentiable_within_at.log
- \+ *lemma* has_deriv_at.log
- \+ *lemma* has_deriv_within_at.log
- \+/\- *lemma* real.exp_log
- \+ *lemma* real.exp_log_eq_abs
- \+/\- *lemma* real.has_deriv_at_log
- \+ *lemma* real.has_deriv_at_log_of_pos
- \+ *lemma* real.log_abs
- \+/\- *lemma* real.log_le_log
- \+/\- *lemma* real.log_mul
- \+ *lemma* real.log_neg_eq_log
- \+/\- *lemma* real.log_nonpos
- \+/\- *lemma* real.log_pos
- \+/\- *lemma* real.log_pos_iff
- \+/\- *lemma* real.rpow_def_of_neg

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
- \+ *theorem* function.bijective.iterate
- \+ *theorem* function.injective.iterate
- \+ *theorem* function.surjective.iterate
- \+ *theorem* nat.iterate_ind
- \- *theorem* nat.iterate_inj

Modified src/field_theory/perfect_closure.lean




## [2020-04-29 07:43:15](https://github.com/leanprover-community/mathlib/commit/f8fe596)
chore(algebra/*): missing `simp`/`inj` lemmas ([#2557](https://github.com/leanprover-community/mathlib/pull/2557))
Sometimes I have a specialized `ext` lemma for `A →+ B` that uses structure of `A` (e.g., `A = monoid_algebra α R`) and want to apply it to `A →+* B` or `A →ₐ[R] B`. These `coe_*_inj` lemmas make it easier.
Also add missing `simp` lemmas for bundled multiplication and rename `pow_of_add` and `gpow_of_add` to `of_add_smul` and `of_add_gsmul`, respectively.
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *lemma* add_monoid_hom.coe_mul_left
- \+ *lemma* add_monoid_hom.mul_right_apply

Modified src/algebra/group_power.lean
- \- *lemma* gpow_of_add
- \+ *lemma* mnat_monoid_hom_eq
- \+ *lemma* mnat_monoid_hom_ext
- \+ *lemma* of_add_gsmul
- \+ *lemma* of_add_smul
- \- *lemma* pow_of_add
- \+ *lemma* powers_hom_apply
- \+ *lemma* powers_hom_symm_apply

Modified src/algebra/ring.lean
- \- *lemma* coe_add_monoid_hom'
- \+/\- *lemma* coe_add_monoid_hom
- \- *lemma* coe_monoid_hom'
- \+/\- *lemma* coe_monoid_hom
- \+ *theorem* ring_hom.coe_add_monoid_hom_inj
- \+ *theorem* ring_hom.coe_monoid_hom_inj

Modified src/ring_theory/algebra.lean
- \+ *theorem* alg_hom.coe_add_monoid_hom_inj
- \+ *theorem* alg_hom.coe_fn_inj
- \+ *theorem* alg_hom.coe_monoid_hom_inj
- \+ *theorem* alg_hom.coe_ring_hom_inj
- \+ *lemma* alg_hom.coe_to_add_monoid_hom



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


Added src/control/traversable/default.lean


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
- \+ *lemma* asymptotics.is_o.def'
- \+ *theorem* asymptotics.is_o.right_is_O_add
- \+ *theorem* asymptotics.is_o.right_is_O_sub

Modified src/analysis/calculus/deriv.lean
- \+ *theorem* has_deriv_at.has_fderiv_at_equiv
- \+ *theorem* has_deriv_at.of_local_left_inverse
- \+ *theorem* has_strict_deriv_at.has_strict_fderiv_at_equiv
- \+ *theorem* has_strict_deriv_at.of_local_left_inverse

Modified src/analysis/calculus/fderiv.lean
- \+ *theorem* has_fderiv_at.of_local_left_inverse
- \+ *lemma* has_fderiv_at_filter.is_O_sub_rev
- \- *lemma* has_strict_fderiv_at.comp
- \- *lemma* has_strict_fderiv_at.continuous_at
- \- *lemma* has_strict_fderiv_at.differentiable_at
- \- *lemma* has_strict_fderiv_at.has_fderiv_at
- \+ *lemma* has_strict_fderiv_at.is_O_sub_rev
- \+ *theorem* has_strict_fderiv_at.of_local_left_inverse
- \- *lemma* has_strict_fderiv_at.prod

Added src/analysis/calculus/inverse.lean
- \+ *lemma* approximates_linear_on.closed_ball_subset_target
- \+ *def* approximates_linear_on.inverse_approx_map
- \+ *lemma* approximates_linear_on.inverse_approx_map_contracts_on
- \+ *lemma* approximates_linear_on.inverse_approx_map_dist_self
- \+ *lemma* approximates_linear_on.inverse_approx_map_dist_self_le
- \+ *lemma* approximates_linear_on.inverse_approx_map_fixed_iff
- \+ *lemma* approximates_linear_on.inverse_approx_map_maps_to
- \+ *lemma* approximates_linear_on.inverse_approx_map_sub
- \+ *lemma* approximates_linear_on.inverse_continuous_on
- \+ *lemma* approximates_linear_on.lipschitz_sub
- \+ *theorem* approximates_linear_on.mono_num
- \+ *theorem* approximates_linear_on.mono_set
- \+ *theorem* approximates_linear_on.surj_on_closed_ball
- \+ *def* approximates_linear_on.to_local_equiv
- \+ *def* approximates_linear_on.to_local_homeomorph
- \+ *lemma* approximates_linear_on.to_local_homeomorph_source
- \+ *lemma* approximates_linear_on.to_local_homeomorph_target
- \+ *lemma* approximates_linear_on.to_local_homeomorph_to_fun
- \+ *def* approximates_linear_on
- \+ *def* has_strict_deriv_at.local_inverse
- \+ *theorem* has_strict_deriv_at.to_local_inverse
- \+ *theorem* has_strict_deriv_at.to_local_left_inverse
- \+ *lemma* has_strict_fderiv_at.approximates_deriv_on_nhds
- \+ *lemma* has_strict_fderiv_at.approximates_deriv_on_open_nhds
- \+ *lemma* has_strict_fderiv_at.eventually_left_inverse
- \+ *lemma* has_strict_fderiv_at.eventually_right_inverse
- \+ *lemma* has_strict_fderiv_at.image_mem_to_local_homeomorph_target
- \+ *def* has_strict_fderiv_at.local_inverse
- \+ *lemma* has_strict_fderiv_at.local_inverse_apply_image
- \+ *lemma* has_strict_fderiv_at.local_inverse_continuous_at
- \+ *lemma* has_strict_fderiv_at.mem_to_local_homeomorph_source
- \+ *def* has_strict_fderiv_at.to_local_homeomorph
- \+ *lemma* has_strict_fderiv_at.to_local_homeomorph_to_fun
- \+ *theorem* has_strict_fderiv_at.to_local_inverse
- \+ *theorem* has_strict_fderiv_at.to_local_left_inverse

Modified src/analysis/complex/exponential.lean
- \+ *lemma* real.has_deriv_at_log

Modified src/analysis/normed_space/operator_norm.lean
- \+ *theorem* continuous_linear_equiv.is_O_comp
- \+ *theorem* continuous_linear_equiv.is_O_comp_rev
- \+ *theorem* continuous_linear_equiv.is_O_sub
- \+ *theorem* continuous_linear_equiv.is_O_sub_rev

Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.inv_fun_tendsto

Modified src/topology/metric_space/antilipschitz.lean




## [2020-04-28 17:54:30](https://github.com/leanprover-community/mathlib/commit/3c02800)
chore(data/dfinsupp): use more precise `decidable` requirement ([#2535](https://github.com/leanprover-community/mathlib/pull/2535))
Removed `decidable_zero_symm` and replaced all `[Π i, decidable_pred (eq (0 : β i))]` with `[Π i (x : β i), decidable (x ≠ 0)]`. This should work better with `open_locale classical` because now the lemmas and definitions don't assume that `[Π i (x : β i), decidable (x ≠ 0)]` comes from `decidable_zero_symm`.
#### Estimated changes
Modified src/data/dfinsupp.lean
- \- *def* decidable_zero_symm
- \+/\- *theorem* dfinsupp.eq_mk_support
- \+/\- *lemma* dfinsupp.map_range_def
- \+/\- *def* dfinsupp.prod
- \+/\- *lemma* dfinsupp.prod_add_index
- \+/\- *lemma* dfinsupp.prod_neg_index
- \+/\- *lemma* dfinsupp.prod_single_index
- \+/\- *lemma* dfinsupp.prod_subtype_domain_index
- \+/\- *lemma* dfinsupp.prod_zero_index
- \+/\- *lemma* dfinsupp.single_apply
- \+/\- *lemma* dfinsupp.smul_apply
- \+/\- *lemma* dfinsupp.sub_apply
- \+/\- *lemma* dfinsupp.subtype_domain_add
- \+/\- *lemma* dfinsupp.subtype_domain_neg
- \+/\- *lemma* dfinsupp.subtype_domain_sub
- \+/\- *def* dfinsupp.sum
- \+/\- *lemma* dfinsupp.sum_add
- \+/\- *lemma* dfinsupp.sum_neg
- \+/\- *lemma* dfinsupp.sum_sub_index
- \+/\- *lemma* dfinsupp.sum_zero
- \+/\- *lemma* dfinsupp.support_add
- \+/\- *theorem* dfinsupp.support_mk_subset
- \+/\- *lemma* dfinsupp.support_neg
- \+/\- *def* dfinsupp.to_has_scalar
- \+/\- *def* dfinsupp.to_module
- \+/\- *def* dfinsupp.zip_with
- \+/\- *def* dfinsupp



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
- \+ *lemma* fin.coe_coe_eq_self
- \+ *lemma* fin.coe_coe_of_lt
- \+ *lemma* fin.coe_fin_le
- \+ *lemma* fin.coe_fin_lt
- \+ *lemma* fin.coe_val_eq_self
- \+ *lemma* fin.coe_val_of_lt
- \+ *lemma* fin.of_nat_eq_coe
- \+ *lemma* fin.one_val
- \+ *lemma* fin.val_add
- \+ *lemma* fin.val_mul
- \+ *lemma* fin.zero_val

Modified src/data/nat/basic.lean
- \+ *lemma* nat.add_mod
- \+ *lemma* nat.mul_mod

Modified src/data/nat/modeq.lean
- \- *lemma* nat.add_mod
- \- *lemma* nat.mul_mod

Modified src/data/zmod/basic.lean
- \- *lemma* fin.of_nat_eq_coe
- \- *lemma* fin.one_val
- \- *lemma* fin.val_add
- \- *lemma* fin.val_mul
- \- *lemma* fin.zero_val



## [2020-04-28 12:08:15](https://github.com/leanprover-community/mathlib/commit/f567962)
feat(data/complex/basic): inv_I and div_I ([#2550](https://github.com/leanprover-community/mathlib/pull/2550))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *lemma* complex.div_I
- \+ *lemma* complex.inv_I



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
- \+/\- *def* CommRing
- \+/\- *def* CommSemiRing
- \+/\- *def* Ring

Modified src/algebra/category/Group/Z_Module_equivalence.lean


Modified src/algebra/category/Group/basic.lean
- \+/\- *def* CommGroup
- \+/\- *def* Group

Modified src/algebra/category/Mon/basic.lean
- \+/\- *def* CommMon

Modified src/category_theory/concrete_category/bundled_hom.lean
- \+ *def* category_theory.bundled_hom.map
- \+ *def* category_theory.bundled_hom.map_hom

Modified src/tactic/interactive.lean




## [2020-04-27 16:34:48](https://github.com/leanprover-community/mathlib/commit/fd3afb4)
chore(ring_theory/algebra): move instances about complex to get rid of dependency ([#2549](https://github.com/leanprover-community/mathlib/pull/2549))
Previously `ring_theory.algebra` imported the complex numbers. This PR moves some instances in order to get rid of that dependency.
#### Estimated changes
Modified src/analysis/convex/basic.lean


Added src/data/complex/module.lean


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
- \+ *def* algebra.of_semimodule'
- \+ *def* algebra.of_semimodule

Modified src/topology/algebra/module.lean
- \+ *lemma* continuous_linear_map.mul_apply



## [2020-04-27 05:41:19](https://github.com/leanprover-community/mathlib/commit/2fc9b15)
chore(data/real/*): use bundled homs to prove `coe_sum` etc ([#2533](https://github.com/leanprover-community/mathlib/pull/2533))
#### Estimated changes
Modified src/algebra/big_operators.lean
- \+ *lemma* ring_hom.map_list_prod
- \+ *lemma* ring_hom.map_list_sum
- \+ *lemma* ring_hom.map_multiset_prod
- \+ *lemma* ring_hom.map_multiset_sum

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.coe_of_nnreal_hom
- \+ *def* ennreal.of_nnreal_hom

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.coe_to_real_hom
- \+ *def* nnreal.to_real_hom



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
- \+ *lemma* measure_theory.exists_nonempty_inter_of_volume_univ_lt_sum_volume
- \+ *lemma* measure_theory.exists_nonempty_inter_of_volume_univ_lt_tsum_volume
- \+ *lemma* measure_theory.sum_volume_le_volume_univ
- \+ *lemma* measure_theory.tsum_volume_le_volume_univ



## [2020-04-26 09:29:30](https://github.com/leanprover-community/mathlib/commit/c170ce3)
chore(data/finset): add `coe_map`, `coe_image_subset_range`, and `coe_map_subset_range` ([#2530](https://github.com/leanprover-community/mathlib/pull/2530))
#### Estimated changes
Modified src/data/finset.lean
- \+ *theorem* finset.coe_image_subset_range
- \+ *theorem* finset.coe_map
- \+ *theorem* finset.coe_map_subset_range



## [2020-04-26 09:29:28](https://github.com/leanprover-community/mathlib/commit/40e97d3)
feat(topology/algebra/module): ker, range, cod_restrict, subtype_val, coprod ([#2525](https://github.com/leanprover-community/mathlib/pull/2525))
Also move `smul_right` to `general_ring` and define some
maps/equivalences useful for the inverse/implicit function theorem.
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* units.coe_mk

Modified src/topology/algebra/module.lean
- \+ *def* continuous_linear_equiv.equiv_of_inverse
- \+ *lemma* continuous_linear_equiv.equiv_of_inverse_apply
- \+ *def* continuous_linear_equiv.equiv_of_right_inverse
- \+ *lemma* continuous_linear_equiv.equiv_of_right_inverse_symm_apply
- \+ *lemma* continuous_linear_equiv.ext₁
- \+ *lemma* continuous_linear_equiv.fst_equiv_of_right_inverse
- \+ *lemma* continuous_linear_equiv.snd_equiv_of_right_inverse
- \+ *lemma* continuous_linear_equiv.symm_equiv_of_inverse
- \+ *def* continuous_linear_equiv.units_equiv_aut
- \+ *lemma* continuous_linear_equiv.units_equiv_aut_apply
- \+ *lemma* continuous_linear_equiv.units_equiv_aut_apply_symm
- \+ *lemma* continuous_linear_equiv.units_equiv_aut_symm_apply
- \+ *lemma* continuous_linear_map.apply_ker
- \+ *def* continuous_linear_map.cod_restrict
- \+ *lemma* continuous_linear_map.coe_cod_restrict
- \+ *lemma* continuous_linear_map.coe_cod_restrict_apply
- \+ *lemma* continuous_linear_map.coe_coprod
- \+ *lemma* continuous_linear_map.coe_prod_map'
- \+ *lemma* continuous_linear_map.coe_proj_ker_of_right_inverse_apply
- \+ *lemma* continuous_linear_map.coe_subtype_val
- \+ *def* continuous_linear_map.coprod
- \+ *lemma* continuous_linear_map.coprod_apply
- \+ *lemma* continuous_linear_map.is_closed_ker
- \+ *def* continuous_linear_map.ker
- \+ *lemma* continuous_linear_map.ker_coe
- \+ *lemma* continuous_linear_map.mem_ker
- \+ *lemma* continuous_linear_map.mem_range
- \- *lemma* continuous_linear_map.prod_map_apply
- \+ *def* continuous_linear_map.proj_ker_of_right_inverse
- \+ *lemma* continuous_linear_map.proj_ker_of_right_inverse_apply_idem
- \+ *lemma* continuous_linear_map.proj_ker_of_right_inverse_comp_inv
- \+ *def* continuous_linear_map.range
- \+ *lemma* continuous_linear_map.range_coe
- \+ *lemma* continuous_linear_map.smul_right_comp
- \+ *def* continuous_linear_map.subtype_val
- \+ *lemma* continuous_linear_map.subtype_val_apply



## [2020-04-26 09:29:26](https://github.com/leanprover-community/mathlib/commit/11ccc1b)
feat(analysis/calculus/deriv): define `has_strict_deriv_at` ([#2524](https://github.com/leanprover-community/mathlib/pull/2524))
Also make more proofs explicitly use their `has_fderiv*` counterparts
and mark some lemmas in `fderiv` as `protected`.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+ *lemma* continuous_linear_map.deriv
- \+ *lemma* continuous_linear_map.deriv_within
- \+ *lemma* continuous_linear_map.has_deriv_at
- \+ *lemma* continuous_linear_map.has_deriv_at_filter
- \+ *lemma* continuous_linear_map.has_deriv_within_at
- \+ *lemma* continuous_linear_map.has_strict_deriv_at
- \- *lemma* has_deriv_at_inv_one
- \+ *lemma* has_fderiv_at.has_deriv_at
- \+ *lemma* has_fderiv_at_filter.has_deriv_at_filter
- \+ *lemma* has_fderiv_within_at.has_deriv_within_at
- \+ *theorem* has_strict_deriv_at.add
- \+ *theorem* has_strict_deriv_at.comp
- \+ *theorem* has_strict_deriv_at.has_deriv_at
- \+ *theorem* has_strict_deriv_at.mul
- \+ *theorem* has_strict_deriv_at.neg
- \+ *theorem* has_strict_deriv_at.scomp
- \+ *theorem* has_strict_deriv_at.smul
- \+ *theorem* has_strict_deriv_at.sub
- \+ *def* has_strict_deriv_at
- \+ *theorem* has_strict_deriv_at_const
- \+ *lemma* has_strict_deriv_at_fpow
- \+ *theorem* has_strict_deriv_at_id
- \+ *theorem* has_strict_deriv_at_inv
- \+ *lemma* has_strict_deriv_at_pow
- \+ *lemma* has_strict_fderiv_at.has_strict_deriv_at
- \+ *lemma* has_strict_fderiv_at_iff_has_strict_deriv_at
- \- *lemma* is_linear_map.deriv
- \- *lemma* is_linear_map.deriv_within
- \- *lemma* is_linear_map.differentiable
- \- *lemma* is_linear_map.differentiable_at
- \- *lemma* is_linear_map.differentiable_on
- \- *lemma* is_linear_map.differentiable_within_at
- \- *lemma* is_linear_map.has_deriv_at
- \- *lemma* is_linear_map.has_deriv_at_filter
- \- *lemma* is_linear_map.has_deriv_within_at
- \+ *lemma* linear_map.deriv
- \+ *lemma* linear_map.deriv_within
- \+ *lemma* linear_map.has_deriv_at
- \+ *lemma* linear_map.has_deriv_at_filter
- \+ *lemma* linear_map.has_deriv_within_at
- \+ *lemma* linear_map.has_strict_deriv_at

Modified src/analysis/calculus/fderiv.lean
- \- *lemma* differentiable.fst
- \- *lemma* differentiable.snd
- \- *lemma* differentiable_at.fst
- \- *theorem* differentiable_at.prod_map
- \- *lemma* differentiable_at.snd
- \- *lemma* differentiable_on.fst
- \- *lemma* differentiable_on.snd
- \- *lemma* differentiable_within_at.fst
- \- *lemma* differentiable_within_at.snd
- \- *lemma* has_fderiv_at.fst
- \- *theorem* has_fderiv_at.prod_map
- \- *lemma* has_fderiv_at.snd
- \- *lemma* has_fderiv_at_filter.fst
- \- *lemma* has_fderiv_at_filter.snd
- \- *lemma* has_fderiv_within_at.fst
- \- *lemma* has_fderiv_within_at.snd
- \+ *theorem* has_strict_fderiv_at.congr_of_mem_sets
- \- *lemma* has_strict_fderiv_at.fst
- \- *theorem* has_strict_fderiv_at.prod_map

Modified src/analysis/normed_space/operator_norm.lean
- \+ *def* linear_map.to_continuous_linear_map₁
- \+ *lemma* linear_map.to_continuous_linear_map₁_apply
- \+ *lemma* linear_map.to_continuous_linear_map₁_coe

Modified src/linear_algebra/basic.lean




## [2020-04-26 06:46:28](https://github.com/leanprover-community/mathlib/commit/21b7292)
feat(data/nat/basic): add `iterate_one` and `iterate_mul` ([#2540](https://github.com/leanprover-community/mathlib/pull/2540))
#### Estimated changes
Modified src/data/nat/basic.lean
- \+/\- *theorem* nat.iterate_cancel
- \+ *lemma* nat.iterate_mul
- \+ *theorem* nat.iterate_one
- \+/\- *theorem* nat.iterate₂



## [2020-04-26 06:46:26](https://github.com/leanprover-community/mathlib/commit/21d8e0a)
chore(data/real/ennreal): +2 simple lemmas ([#2539](https://github.com/leanprover-community/mathlib/pull/2539))
Extracted from [#2311](https://github.com/leanprover-community/mathlib/pull/2311)
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.exists_nat_mul_gt



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
Added src/meta/expr_lens.lean
- \+ *def* expr_lens.dir.to_string

Modified src/tactic/doc_commands.lean


Added src/tactic/nth_rewrite/basic.lean


Added src/tactic/nth_rewrite/congr.lean


Added src/tactic/nth_rewrite/default.lean


Deleted src/tactic/rewrite_all/congr.lean


Deleted src/tactic/rewrite_all/default.lean


Added test/expr_lens.lean


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
- \+ *lemma* option.get_or_else_of_ne_none

Modified src/order/bounded_lattice.lean
- \+/\- *lemma* with_bot.bot_lt_coe
- \+/\- *lemma* with_bot.bot_lt_some
- \+ *lemma* with_bot.le_coe_get_or_else



## [2020-04-26 03:56:06](https://github.com/leanprover-community/mathlib/commit/ee6f20a)
chore(algebra/module): use bundled homs for `smul_sum` and `sum_smul` ([#2529](https://github.com/leanprover-community/mathlib/pull/2529))
#### Estimated changes
Modified src/algebra/group/hom.lean
- \+ *def* monoid_hom.flip
- \+ *lemma* monoid_hom.flip_apply
- \+ *lemma* monoid_hom.inv_apply
- \+ *lemma* monoid_hom.mul_apply
- \+ *lemma* monoid_hom.one_apply

Modified src/algebra/module.lean
- \+ *def* smul_add_hom
- \+ *lemma* smul_add_hom_apply

Modified src/group_theory/group_action.lean
- \+ *def* const_smul_hom
- \+ *lemma* const_smul_hom_apply

Modified src/ring_theory/noetherian.lean




## [2020-04-25 23:03:27](https://github.com/leanprover-community/mathlib/commit/5219ca1)
doc(data/nat/modeq): add module docstring and lemma ([#2528](https://github.com/leanprover-community/mathlib/pull/2528))
I add a simple docstrong and also a lemma which I found useful for a codewars kata.
#### Estimated changes
Modified src/data/nat/modeq.lean
- \+ *theorem* nat.modeq.modeq_iff_dvd'



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
- \+ *lemma* bool.bnot_band
- \+ *lemma* bool.bnot_bor
- \+ *lemma* bool.bnot_inj



## [2020-04-25 19:55:51](https://github.com/leanprover-community/mathlib/commit/94fd41a)
refactor(data/padics/*): use [fact p.prime] to assume that p is prime ([#2519](https://github.com/leanprover-community/mathlib/pull/2519))
#### Estimated changes
Modified docs/theories/padics.md


Modified src/data/padics/hensel.lean
- \+/\- *lemma* padic_polynomial_dist

Modified src/data/padics/padic_integers.lean
- \+/\- *def* padic_int

Modified src/data/padics/padic_norm.lean
- \+/\- *lemma* padic_val_rat.finite_int_prime_iff
- \+/\- *lemma* padic_val_rat_def

Modified src/data/padics/padic_numbers.lean
- \+/\- *theorem* padic.rat_dense'
- \+/\- *theorem* padic.rat_dense
- \+/\- *def* padic
- \+/\- *lemma* padic_norm_e.eq_of_norm_add_lt_left
- \+/\- *lemma* padic_norm_e.eq_of_norm_add_lt_right
- \+/\- *def* padic_norm_e
- \+/\- *def* padic_seq

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
- \+/\- *def* generalized_continued_fraction.continuants
- \+/\- *def* generalized_continued_fraction.continuants_aux
- \+/\- *def* generalized_continued_fraction.convergents'
- \+/\- *def* generalized_continued_fraction.convergents'_aux
- \+/\- *def* generalized_continued_fraction.convergents
- \+/\- *def* generalized_continued_fraction.denominators
- \+/\- *def* generalized_continued_fraction.next_continuants
- \+/\- *def* generalized_continued_fraction.next_denominator
- \+/\- *def* generalized_continued_fraction.next_numerator
- \+/\- *def* generalized_continued_fraction.numerators

Modified src/algebra/continued_fractions/continuants_recurrence.lean
- \+/\- *lemma* generalized_continued_fraction.continuants_aux_recurrence
- \+/\- *theorem* generalized_continued_fraction.continuants_recurrence
- \+/\- *lemma* generalized_continued_fraction.continuants_recurrence_aux
- \+/\- *lemma* generalized_continued_fraction.denominators_recurrence
- \+/\- *lemma* generalized_continued_fraction.numerators_recurrence

Added src/algebra/continued_fractions/convergents_equiv.lean
- \+ *theorem* continued_fraction.convergents_eq_convergents'
- \+ *lemma* generalized_continued_fraction.continuants_aux_eq_continuants_aux_squash_gcf_of_le
- \+ *theorem* generalized_continued_fraction.convergents_eq_convergents'
- \+ *def* generalized_continued_fraction.squash_gcf
- \+ *lemma* generalized_continued_fraction.squash_gcf_eq_self_of_terminated
- \+ *lemma* generalized_continued_fraction.squash_gcf_nth_of_lt
- \+ *def* generalized_continued_fraction.squash_seq
- \+ *lemma* generalized_continued_fraction.squash_seq_eq_self_of_terminated
- \+ *lemma* generalized_continued_fraction.squash_seq_nth_of_lt
- \+ *lemma* generalized_continued_fraction.squash_seq_nth_of_not_terminated
- \+ *lemma* generalized_continued_fraction.squash_seq_succ_n_tail_eq_squash_seq_tail_n
- \+ *lemma* generalized_continued_fraction.succ_nth_convergent'_eq_squash_gcf_nth_convergent'
- \+ *lemma* generalized_continued_fraction.succ_nth_convergent_eq_squash_gcf_nth_convergent
- \+ *lemma* generalized_continued_fraction.succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq

Modified src/algebra/continued_fractions/default.lean


Modified src/algebra/continued_fractions/terminated_stable.lean
- \+/\- *lemma* generalized_continued_fraction.convergents'_aux_stable_of_terminated
- \+/\- *lemma* generalized_continued_fraction.convergents'_aux_stable_step_of_terminated

Modified src/algebra/continued_fractions/translations.lean
- \+/\- *lemma* generalized_continued_fraction.obtain_conts_a_of_num
- \+/\- *lemma* generalized_continued_fraction.obtain_conts_b_of_denom
- \+/\- *lemma* generalized_continued_fraction.zeroth_convergent'_aux_eq_zero



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
- \+/\- *theorem* frobenius_inj
- \+/\- *theorem* monoid_hom.iterate_map_frobenius
- \+/\- *theorem* ring_hom.iterate_map_frobenius

Modified src/field_theory/perfect_closure.lean
- \+/\- *lemma* coe_frobenius_equiv
- \+/\- *lemma* coe_frobenius_equiv_symm
- \+/\- *theorem* eq_pth_root_iff
- \+/\- *def* frobenius_equiv
- \+/\- *theorem* frobenius_pth_root
- \+/\- *theorem* monoid_hom.map_iterate_pth_root
- \+/\- *theorem* monoid_hom.map_pth_root
- \+/\- *theorem* perfect_closure.eq_iff'
- \+/\- *theorem* perfect_closure.eq_iff
- \+/\- *theorem* perfect_closure.eq_pth_root
- \+/\- *theorem* perfect_closure.frobenius_mk
- \+/\- *lemma* perfect_closure.induction_on
- \+/\- *theorem* perfect_closure.int_cast
- \+/\- *def* perfect_closure.lift
- \+/\- *def* perfect_closure.lift_on
- \+/\- *lemma* perfect_closure.lift_on_mk
- \+/\- *def* perfect_closure.mk
- \+/\- *lemma* perfect_closure.mk_add_mk
- \+/\- *lemma* perfect_closure.mk_mul_mk
- \+/\- *theorem* perfect_closure.mk_zero
- \+/\- *theorem* perfect_closure.nat_cast
- \+/\- *theorem* perfect_closure.nat_cast_eq_iff
- \+/\- *lemma* perfect_closure.neg_mk
- \+/\- *def* perfect_closure.of
- \+/\- *lemma* perfect_closure.of_apply
- \+/\- *lemma* perfect_closure.one_def
- \+/\- *lemma* perfect_closure.quot_mk_eq_mk
- \+/\- *theorem* perfect_closure.r.sound
- \+/\- *lemma* perfect_closure.zero_def
- \+/\- *def* perfect_closure
- \+/\- *def* pth_root
- \+/\- *theorem* pth_root_eq_iff
- \+/\- *theorem* pth_root_frobenius
- \+/\- *theorem* ring_hom.map_iterate_pth_root
- \+/\- *theorem* ring_hom.map_pth_root



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
- \+ *lemma* filter.has_basis.exists_iff
- \+ *lemma* filter.has_basis.forall_iff



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
- \+ *def* test.library_search.map_from_sum



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
- \+/\- *theorem* char_p.char_is_prime
- \+ *lemma* char_p.char_is_prime_of_pos
- \+ *lemma* char_p.false_of_nonzero_of_char_one
- \+ *lemma* char_p.int_cast_eq_zero_iff
- \- *def* zmod.cast_hom

Modified src/data/nat/basic.lean
- \+ *lemma* nat.dvd_sub_mod

Modified src/data/nat/modeq.lean
- \+ *lemma* nat.add_mod
- \+ *lemma* nat.mul_mod

Modified src/data/nat/prime.lean


Modified src/data/nat/totient.lean
- \- *lemma* zmod.card_units_eq_totient

Modified src/data/zmod/basic.lean
- \+ *def* fin.add_comm_semigroup
- \+ *def* fin.comm_ring
- \+ *def* fin.comm_semigroup
- \+ *def* fin.has_neg
- \+ *lemma* fin.of_nat_eq_coe
- \+ *lemma* fin.one_val
- \+ *lemma* fin.val_add
- \+ *lemma* fin.val_mul
- \+ *lemma* fin.zero_val
- \- *lemma* zmod.add_val
- \+ *lemma* zmod.card
- \+ *lemma* zmod.card_units_eq_totient
- \- *lemma* zmod.card_zmod
- \+/\- *def* zmod.cast
- \+ *lemma* zmod.cast_add
- \+ *def* zmod.cast_hom
- \+ *lemma* zmod.cast_hom_apply
- \+ *lemma* zmod.cast_id
- \+ *lemma* zmod.cast_int_cast
- \- *lemma* zmod.cast_mod_int'
- \- *lemma* zmod.cast_mod_int
- \- *lemma* zmod.cast_mod_nat'
- \+/\- *lemma* zmod.cast_mod_nat
- \+ *lemma* zmod.cast_mul
- \- *lemma* zmod.cast_mul_left_val_cast
- \- *lemma* zmod.cast_mul_right_val_cast
- \+/\- *lemma* zmod.cast_nat_abs_val_min_abs
- \+ *lemma* zmod.cast_nat_cast
- \+ *lemma* zmod.cast_one
- \+ *lemma* zmod.cast_self'
- \+ *lemma* zmod.cast_self
- \- *lemma* zmod.cast_self_eq_zero
- \+/\- *lemma* zmod.cast_unit_of_coprime
- \+/\- *lemma* zmod.cast_val
- \- *lemma* zmod.cast_val_cast_of_dvd
- \+ *lemma* zmod.cast_zero
- \+ *lemma* zmod.coe_mul_inv_eq_one
- \- *lemma* zmod.coe_val_cast_int
- \+/\- *lemma* zmod.coe_val_min_abs
- \- *lemma* zmod.eq_iff_modeq_int'
- \- *lemma* zmod.eq_iff_modeq_int
- \- *lemma* zmod.eq_iff_modeq_nat'
- \+/\- *lemma* zmod.eq_iff_modeq_nat
- \- *lemma* zmod.eq_zero_iff_dvd_int
- \- *lemma* zmod.eq_zero_iff_dvd_nat
- \+ *lemma* zmod.int_cast_surjective
- \+ *def* zmod.inv
- \+ *lemma* zmod.inv_coe_unit
- \+ *lemma* zmod.inv_mul_of_unit
- \+ *lemma* zmod.inv_zero
- \+/\- *lemma* zmod.le_div_two_iff_lt_neg
- \- *lemma* zmod.mk_eq_cast
- \+ *lemma* zmod.mul_inv_eq_gcd
- \+ *lemma* zmod.mul_inv_of_unit
- \- *lemma* zmod.mul_val
- \+/\- *lemma* zmod.nat_abs_val_min_abs_le
- \+/\- *lemma* zmod.nat_abs_val_min_abs_neg
- \+ *lemma* zmod.nat_cast_surjective
- \+ *lemma* zmod.nat_cast_val
- \+/\- *lemma* zmod.ne_neg_self
- \+/\- *lemma* zmod.neg_eq_self_mod_two
- \+ *lemma* zmod.neg_one_ne_one
- \+/\- *lemma* zmod.neg_val'
- \+/\- *lemma* zmod.neg_val
- \- *lemma* zmod.one_val
- \+ *lemma* zmod.prime_ne_zero
- \+/\- *def* zmod.unit_of_coprime
- \+/\- *def* zmod.units_equiv_coprime
- \+ *def* zmod.val
- \+ *lemma* zmod.val_add
- \- *lemma* zmod.val_cast_int
- \+/\- *lemma* zmod.val_cast_nat
- \+/\- *lemma* zmod.val_cast_of_lt
- \+ *lemma* zmod.val_coe_unit_coprime
- \+/\- *lemma* zmod.val_eq_ite_val_min_abs
- \+ *lemma* zmod.val_eq_zero
- \+ *lemma* zmod.val_injective
- \+ *lemma* zmod.val_lt
- \+/\- *def* zmod.val_min_abs
- \+ *lemma* zmod.val_min_abs_def_pos
- \+ *lemma* zmod.val_min_abs_def_zero
- \+/\- *lemma* zmod.val_min_abs_eq_zero
- \+/\- *lemma* zmod.val_min_abs_zero
- \+ *lemma* zmod.val_mul
- \+ *lemma* zmod.val_one
- \+ *lemma* zmod.val_one_eq_one_mod
- \+ *lemma* zmod.val_zero
- \- *lemma* zmod.zero_val
- \+/\- *def* zmod
- \- *lemma* zmodp.add_val
- \- *lemma* zmodp.card_zmodp
- \- *lemma* zmodp.cast_mod_int
- \- *lemma* zmodp.cast_mod_nat
- \- *lemma* zmodp.cast_nat_abs_val_min_abs
- \- *lemma* zmodp.cast_self_eq_zero:
- \- *lemma* zmodp.cast_val
- \- *lemma* zmodp.coe_val_cast_int
- \- *lemma* zmodp.coe_val_min_abs
- \- *lemma* zmodp.eq_iff_modeq_int
- \- *lemma* zmodp.eq_iff_modeq_nat
- \- *lemma* zmodp.eq_zero_iff_dvd_int
- \- *lemma* zmodp.eq_zero_iff_dvd_nat
- \- *lemma* zmodp.le_div_two_iff_lt_neg
- \- *lemma* zmodp.mk_eq_cast
- \- *lemma* zmodp.mul_inv_eq_gcd
- \- *lemma* zmodp.mul_val
- \- *lemma* zmodp.nat_abs_val_min_abs_le
- \- *lemma* zmodp.nat_abs_val_min_abs_neg
- \- *lemma* zmodp.ne_neg_self
- \- *lemma* zmodp.one_val
- \- *lemma* zmodp.prime_ne_zero
- \- *lemma* zmodp.val_cast_int
- \- *lemma* zmodp.val_cast_nat
- \- *lemma* zmodp.val_cast_of_lt
- \- *lemma* zmodp.val_eq_ite_val_min_abs
- \- *def* zmodp.val_min_abs
- \- *lemma* zmodp.val_min_abs_eq_zero
- \- *lemma* zmodp.val_min_abs_zero
- \- *lemma* zmodp.zero_val
- \- *def* zmodp

Modified src/data/zmod/quadratic_reciprocity.lean
- \+ *lemma* zmod.card_units
- \+ *lemma* zmod.eisenstein_lemma
- \+ *lemma* zmod.euler_criterion
- \+ *lemma* zmod.euler_criterion_units
- \+ *lemma* zmod.exists_pow_two_eq_neg_one_iff_mod_four_ne_three
- \+ *lemma* zmod.exists_pow_two_eq_prime_iff_of_mod_four_eq_one
- \+ *lemma* zmod.exists_pow_two_eq_prime_iff_of_mod_four_eq_three
- \+ *lemma* zmod.exists_pow_two_eq_two_iff
- \+ *theorem* zmod.fermat_little
- \+ *theorem* zmod.fermat_little_units
- \+ *lemma* zmod.gauss_lemma
- \+ *def* zmod.legendre_sym
- \+ *lemma* zmod.legendre_sym_eq_one_iff
- \+ *lemma* zmod.legendre_sym_eq_one_or_neg_one
- \+ *lemma* zmod.legendre_sym_eq_pow
- \+ *lemma* zmod.legendre_sym_eq_zero_iff
- \+ *lemma* zmod.legendre_sym_two
- \+ *lemma* zmod.pow_div_two_eq_neg_one_or_one
- \+ *lemma* zmod.prod_Ico_one_prime
- \+ *theorem* zmod.quadratic_reciprocity
- \+ *lemma* zmod.wilsons_lemma
- \- *lemma* zmodp.card_units_zmodp
- \- *lemma* zmodp.eisenstein_lemma
- \- *lemma* zmodp.euler_criterion
- \- *lemma* zmodp.euler_criterion_units
- \- *lemma* zmodp.exists_pow_two_eq_neg_one_iff_mod_four_ne_three
- \- *lemma* zmodp.exists_pow_two_eq_prime_iff_of_mod_four_eq_one
- \- *lemma* zmodp.exists_pow_two_eq_prime_iff_of_mod_four_eq_three
- \- *lemma* zmodp.exists_pow_two_eq_two_iff
- \- *theorem* zmodp.fermat_little
- \- *lemma* zmodp.gauss_lemma
- \- *def* zmodp.legendre_sym
- \- *lemma* zmodp.legendre_sym_eq_one_iff
- \- *lemma* zmodp.legendre_sym_eq_one_or_neg_one
- \- *lemma* zmodp.legendre_sym_eq_pow
- \- *lemma* zmodp.legendre_sym_two
- \- *lemma* zmodp.pow_div_two_eq_neg_one_or_one
- \- *lemma* zmodp.prod_Ico_one_prime
- \- *theorem* zmodp.quadratic_reciprocity
- \- *lemma* zmodp.wilsons_lemma

Modified src/data/zsqrtd/gaussian_int.lean
- \+/\- *lemma* gaussian_int.mod_four_eq_three_of_nat_prime_of_prime
- \+/\- *lemma* gaussian_int.prime_iff_mod_four_eq_three_of_nat_prime
- \+/\- *lemma* gaussian_int.prime_of_nat_prime_of_mod_four_eq_three
- \+/\- *lemma* gaussian_int.sum_two_squares_of_nat_prime_of_not_irreducible

Modified src/field_theory/finite.lean
- \+/\- *lemma* char_p.sum_two_squares
- \+/\- *lemma* zmod.pow_totient
- \+ *lemma* zmod.sum_two_squares
- \- *lemma* zmodp.sum_two_squares

Modified src/field_theory/finite_card.lean
- \+/\- *theorem* finite_field.card'
- \+/\- *theorem* finite_field.card

Modified src/group_theory/order_of_element.lean


Modified src/group_theory/sylow.lean
- \+/\- *lemma* sylow.exists_prime_order_of_dvd_card
- \+/\- *lemma* sylow.exists_subgroup_card_pow_prime
- \+/\- *lemma* sylow.one_mem_fixed_points_rotate
- \+/\- *def* sylow.rotate_vectors_prod_eq_one

Modified src/logic/basic.lean
- \+ *def* fact

Modified src/number_theory/sum_four_squares.lean
- \+/\- *lemma* int.exists_sum_two_squares_add_one_eq_k

Modified src/number_theory/sum_two_squares.lean
- \+/\- *lemma* nat.prime.sum_two_squares



## [2020-04-24 23:37:01](https://github.com/leanprover-community/mathlib/commit/3e54e97)
chore(topology/separation): prove that `{y | y ≠ x}` is open ([#2506](https://github.com/leanprover-community/mathlib/pull/2506))
#### Estimated changes
Modified src/analysis/calculus/deriv.lean


Modified src/data/set/basic.lean
- \+ *lemma* set.compl_singleton_eq

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* ennreal.is_open_ne_top

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
- \+ *lemma* finset.sum_range_sub_of_monotone

Modified src/analysis/analytic/composition.lean


Modified src/combinatorics/composition.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* finset.univ_sigma_univ

Modified src/data/fintype/card.lean
- \+ *lemma* fin.prod_univ_eq_prod_range
- \- *lemma* list.of_fn_prod
- \- *lemma* list.of_fn_prod_take
- \- *lemma* list.of_fn_sum_take
- \+ *lemma* list.prod_of_fn
- \+ *lemma* list.prod_take_of_fn
- \+ *lemma* list.sum_take_of_fn
- \+ *lemma* prod_equiv

Modified src/data/list/basic.lean
- \+ *lemma* list.drop_append
- \+ *lemma* list.drop_sum_join
- \+ *lemma* list.drop_take_succ_eq_cons_nth_le
- \+ *lemma* list.drop_take_succ_join_eq_nth_le
- \+ *lemma* list.eq_cons_of_length_one
- \+ *theorem* list.eq_iff_join_eq
- \+ *lemma* list.forall_mem_map_iff
- \+ *lemma* list.nth_le_drop'
- \+ *lemma* list.nth_le_drop
- \+ *lemma* list.nth_le_join
- \+ *lemma* list.nth_le_of_eq
- \+/\- *lemma* list.nth_le_repeat
- \+ *lemma* list.nth_le_take'
- \+ *lemma* list.nth_le_take
- \+ *lemma* list.sum_take_map_length_lt1
- \+ *lemma* list.sum_take_map_length_lt2
- \+ *lemma* list.take_append
- \+ *theorem* list.take_repeat
- \+ *lemma* list.take_sum_join

Modified src/data/list/of_fn.lean
- \+ *lemma* list.forall_mem_of_fn_iff
- \+ *lemma* list.mem_of_fn

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
- \+/\- *theorem* has_fderiv_at_id
- \- *lemma* has_strict_fderiv_at.snd

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* continuous_linear_map.norm_id
- \+/\- *lemma* continuous_linear_map.norm_id_le

Modified src/geometry/manifold/basic_smooth_bundle.lean


Modified src/geometry/manifold/mfderiv.lean
- \+/\- *lemma* mfderiv_id

Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous_linear_map.coe_id'
- \+/\- *lemma* continuous_linear_map.coe_id
- \+/\- *theorem* continuous_linear_map.comp_id
- \+/\- *lemma* continuous_linear_map.id_apply
- \+/\- *theorem* continuous_linear_map.id_comp



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
- \+/\- *theorem* alist.entries_to_alist
- \+/\- *theorem* alist.insert_insert
- \+/\- *lemma* alist.insert_singleton_eq
- \+/\- *theorem* alist.to_alist_cons
- \+/\- *theorem* alist.union_comm_of_disjoint

Modified src/data/list/basic.lean
- \- *theorem* list.append_sublist_append
- \- *theorem* list.append_sublist_append_of_sublist_right
- \- *theorem* list.diff_sublist_of_sublist
- \- *theorem* list.erase_sublist_erase
- \- *theorem* list.erasep_sublist_erasep
- \- *theorem* list.filter_map_sublist_filter_map
- \- *theorem* list.map_sublist_map
- \- *theorem* list.reverse_sublist
- \+/\- *theorem* list.span_eq_take_drop
- \+ *theorem* list.sublist.antisymm
- \+ *theorem* list.sublist.append
- \+ *theorem* list.sublist.append_right
- \+ *theorem* list.sublist.diff_right
- \+ *theorem* list.sublist.erase
- \+ *theorem* list.sublist.erasep
- \+ *theorem* list.sublist.filter_map
- \+ *theorem* list.sublist.map
- \+ *theorem* list.sublist.reverse
- \+ *theorem* list.sublist.subset
- \- *theorem* list.sublist_antisymm
- \- *theorem* list.subset_of_sublist
- \+/\- *theorem* list.take_while_append_drop

Modified src/data/list/pairwise.lean


Modified src/data/list/perm.lean
- \- *theorem* list.count_le_of_subperm
- \- *theorem* list.countp_le_of_subperm
- \- *theorem* list.eq_nil_of_perm_nil
- \- *theorem* list.eq_singleton_of_perm
- \- *theorem* list.eq_singleton_of_perm_inv
- \+ *theorem* list.erase_cons_subperm_cons_erase
- \- *theorem* list.erase_perm_erase
- \- *theorem* list.erase_subperm_erase
- \- *theorem* list.exists_perm_append_of_sublist
- \- *lemma* list.fold_op_eq_of_perm
- \- *theorem* list.foldl_eq_of_perm
- \- *theorem* list.foldr_eq_of_perm
- \- *theorem* list.length_le_of_subperm
- \- *theorem* list.mem_of_perm
- \+ *theorem* list.nodup.sublist_ext
- \+ *theorem* list.perm.append
- \+ *theorem* list.perm.append_cons
- \+ *theorem* list.perm.append_left
- \+ *theorem* list.perm.append_right
- \+ *theorem* list.perm.bag_inter
- \+ *theorem* list.perm.bag_inter_left
- \+ *theorem* list.perm.bag_inter_right
- \+ *theorem* list.perm.bind_left
- \+ *theorem* list.perm.bind_right
- \+ *theorem* list.perm.cons_inv
- \+ *theorem* list.perm.count_eq
- \+ *theorem* list.perm.countp_eq
- \+ *theorem* list.perm.diff
- \+ *theorem* list.perm.diff_left
- \+ *theorem* list.perm.diff_right
- \+ *theorem* list.perm.eq_nil
- \+ *theorem* list.perm.eq_singleton
- \+ *theorem* list.perm.erase
- \+ *theorem* list.perm.erase_dup
- \+ *theorem* list.perm.erasep
- \+ *theorem* list.perm.filter
- \+ *theorem* list.perm.filter_map
- \+ *lemma* list.perm.fold_op_eq
- \+ *theorem* list.perm.foldl_eq'
- \+ *theorem* list.perm.foldl_eq
- \+ *theorem* list.perm.foldr_eq
- \+ *theorem* list.perm.insert
- \+ *theorem* list.perm.inter
- \+ *theorem* list.perm.inter_left
- \+ *theorem* list.perm.inter_right
- \+ *theorem* list.perm.length_eq
- \+ *theorem* list.perm.map
- \+ *theorem* list.perm.mem_iff
- \+ *theorem* list.perm.nil_eq
- \+ *theorem* list.perm.nodup_iff
- \+ *theorem* list.perm.pairwise_iff
- \+ *theorem* list.perm.pmap
- \+ *lemma* list.perm.prod_eq'
- \+ *lemma* list.perm.prod_eq
- \+ *theorem* list.perm.product
- \+ *theorem* list.perm.product_left
- \+ *theorem* list.perm.product_right
- \+ *lemma* list.perm.rec_heq
- \+ *theorem* list.perm.singleton_eq
- \+ *theorem* list.perm.subperm
- \+ *theorem* list.perm.subset
- \+ *theorem* list.perm.union
- \+ *theorem* list.perm.union_left
- \+ *theorem* list.perm.union_right
- \- *theorem* list.perm_app
- \- *theorem* list.perm_app_comm
- \- *theorem* list.perm_app_cons
- \- *theorem* list.perm_app_left
- \- *theorem* list.perm_app_left_iff
- \- *theorem* list.perm_app_right
- \- *theorem* list.perm_app_right_iff
- \+ *theorem* list.perm_append_comm
- \+ *theorem* list.perm_append_left_iff
- \+ *theorem* list.perm_append_right_iff
- \+ *theorem* list.perm_append_singleton
- \- *theorem* list.perm_bag_inter_left
- \- *theorem* list.perm_bag_inter_right
- \- *theorem* list.perm_bind_left
- \- *theorem* list.perm_bind_right
- \+ *theorem* list.perm_comm
- \+/\- *theorem* list.perm_cons
- \- *theorem* list.perm_cons_app
- \- *theorem* list.perm_cons_app_cons
- \+ *theorem* list.perm_cons_append_cons
- \+ *theorem* list.perm_cons_erase
- \- *theorem* list.perm_cons_inv
- \- *theorem* list.perm_count
- \- *theorem* list.perm_countp
- \- *theorem* list.perm_diff_left
- \- *theorem* list.perm_diff_right
- \- *theorem* list.perm_erase
- \- *theorem* list.perm_erase_dup_of_perm
- \- *theorem* list.perm_erasep
- \+/\- *theorem* list.perm_ext
- \- *theorem* list.perm_ext_sublist_nodup
- \- *theorem* list.perm_filter
- \- *theorem* list.perm_filter_map
- \- *theorem* list.perm_insert
- \- *theorem* list.perm_inter
- \- *theorem* list.perm_inter_left
- \- *theorem* list.perm_inter_right
- \- *theorem* list.perm_length
- \- *theorem* list.perm_map
- \- *theorem* list.perm_nodup
- \- *theorem* list.perm_pairwise
- \- *theorem* list.perm_pmap
- \- *theorem* list.perm_product
- \- *theorem* list.perm_product_left
- \- *theorem* list.perm_product_right
- \+/\- *theorem* list.perm_repeat
- \+ *theorem* list.perm_singleton
- \- *theorem* list.perm_subset
- \- *theorem* list.perm_union
- \- *theorem* list.perm_union_left
- \- *theorem* list.perm_union_right
- \- *lemma* list.prod_eq_of_perm
- \- *lemma* list.rec_heq_of_perm
- \+ *theorem* list.repeat_perm
- \+ *theorem* list.singleton_perm
- \+ *theorem* list.singleton_perm_singleton
- \+ *theorem* list.sublist.exists_perm_append
- \+ *theorem* list.sublist.subperm
- \+ *theorem* list.subperm.count_le
- \+ *theorem* list.subperm.countp_le
- \+ *theorem* list.subperm.diff_right
- \+ *theorem* list.subperm.erase
- \+ *theorem* list.subperm.length_le
- \+/\- *theorem* list.subperm.refl
- \+ *theorem* list.subperm.subset
- \+/\- *theorem* list.subperm.trans
- \- *theorem* list.subperm_app_left
- \- *theorem* list.subperm_app_right
- \+ *theorem* list.subperm_append_left
- \+ *theorem* list.subperm_append_right
- \+ *theorem* list.subperm_cons_erase
- \- *theorem* list.subperm_of_perm
- \- *theorem* list.subperm_of_sublist
- \- *theorem* list.subset_of_subperm

Modified src/data/list/range.lean


Modified src/data/list/sigma.lean
- \+/\- *lemma* list.erase_dupkeys_cons
- \+/\- *theorem* list.kerase_kerase
- \+ *theorem* list.nodupkeys.pairwise_ne
- \+/\- *theorem* list.nodupkeys_of_sublist
- \+ *theorem* list.perm.kerase
- \+ *theorem* list.perm.kinsert
- \+ *theorem* list.perm.kreplace
- \+ *theorem* list.perm.kunion
- \+ *theorem* list.perm.kunion_left
- \+ *theorem* list.perm.kunion_right
- \- *theorem* list.perm_kerase
- \- *theorem* list.perm_kinsert
- \- *theorem* list.perm_kreplace
- \- *theorem* list.perm_kunion
- \- *theorem* list.perm_kunion_left
- \- *theorem* list.perm_kunion_right

Modified src/data/list/sort.lean


Modified src/data/multiset.lean
- \+/\- *theorem* multiset.card_erase_of_mem
- \+/\- *theorem* multiset.coe_filter_map
- \+/\- *theorem* multiset.cons_ndunion
- \+/\- *theorem* multiset.erase_add_left_neg
- \+/\- *theorem* multiset.erase_add_right_neg
- \+/\- *theorem* multiset.erase_add_right_pos

Modified src/data/nat/prime.lean


Modified src/group_theory/perm/cycles.lean


Modified src/group_theory/perm/sign.lean




## [2020-04-24 11:13:59](https://github.com/leanprover-community/mathlib/commit/3ae22de)
feat(linear_algebra): quadratic forms ([#2480](https://github.com/leanprover-community/mathlib/pull/2480))
Define quadratic forms over a module, maps from quadratic forms to bilinear forms and matrices, positive definite quadratic forms and the discriminant of quadratic forms.
Along the way, I added some definitions to `data/matrix/basic.lean` and `linear_algebra/bilinear_form.lean` and did some cleaning up.
#### Estimated changes
Modified src/algebra/module.lean
- \+ *lemma* linear_map.coe_fn_congr

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.col_add
- \+ *lemma* matrix.col_mul_vec
- \+ *lemma* matrix.col_smul
- \+ *lemma* matrix.col_val
- \+ *lemma* matrix.col_vec_mul
- \+ *lemma* matrix.mul_vec_mul_vec
- \+ *lemma* matrix.mul_vec_zero
- \+ *lemma* matrix.row_add
- \+ *lemma* matrix.row_mul_vec
- \+ *lemma* matrix.row_smul
- \+ *lemma* matrix.row_val
- \+ *lemma* matrix.row_vec_mul
- \+ *lemma* matrix.transpose_col
- \+ *lemma* matrix.transpose_row
- \+ *lemma* matrix.vec_mul_diagonal
- \+ *lemma* matrix.vec_mul_one
- \+ *lemma* matrix.vec_mul_vec_mul
- \+ *lemma* matrix.vec_mul_zero

Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.coe_fn_sum

Modified src/linear_algebra/bilinear_form.lean
- \+ *lemma* bilin_form.add_apply
- \+ *lemma* bilin_form.coe_fn_congr
- \+ *lemma* bilin_form.coe_fn_mk
- \+ *lemma* bilin_form.coe_fn_to_linear_map
- \+ *def* bilin_form.comp
- \+ *lemma* bilin_form.comp_apply
- \+ *def* bilin_form.comp_left
- \+ *lemma* bilin_form.comp_left_apply
- \+ *lemma* bilin_form.comp_left_comp_right
- \+ *def* bilin_form.comp_right
- \+ *lemma* bilin_form.comp_right_apply
- \+ *lemma* bilin_form.comp_right_comp_left
- \+ *lemma* bilin_form.map_sum_left
- \+ *lemma* bilin_form.map_sum_right
- \+ *lemma* bilin_form.mul_to_matrix
- \+ *lemma* bilin_form.mul_to_matrix_mul
- \+ *lemma* bilin_form.smul_apply
- \+ *def* bilin_form.to_matrix
- \+ *lemma* bilin_form.to_matrix_apply
- \+ *lemma* bilin_form.to_matrix_comp
- \+ *lemma* bilin_form.to_matrix_comp_left
- \+ *lemma* bilin_form.to_matrix_comp_right
- \+ *lemma* bilin_form.to_matrix_mul
- \+ *lemma* bilin_form.to_matrix_smul
- \+ *def* bilin_form.to_matrixₗ
- \+ *def* bilin_form_equiv_matrix
- \+ *def* matrix.to_bilin_form
- \+ *lemma* matrix.to_bilin_form_apply
- \+ *def* matrix.to_bilin_formₗ

Modified src/linear_algebra/matrix.lean
- \+ *lemma* linear_map.to_matrix_id

Added src/linear_algebra/quadratic_form.lean
- \+ *lemma* bilin_form.polar_to_quadratic_form
- \+ *def* bilin_form.to_quadratic_form
- \+ *lemma* bilin_form.to_quadratic_form_apply
- \+ *def* matrix.to_quadratic_form
- \+ *def* quadratic_form.associated
- \+ *lemma* quadratic_form.associated_apply
- \+ *lemma* quadratic_form.associated_comp
- \+ *lemma* quadratic_form.associated_is_sym
- \+ *lemma* quadratic_form.associated_left_inverse
- \+ *lemma* quadratic_form.associated_right_inverse
- \+ *lemma* quadratic_form.associated_smul
- \+ *lemma* quadratic_form.associated_to_quadratic_form
- \+ *def* quadratic_form.comp
- \+ *lemma* quadratic_form.comp_apply
- \+ *def* quadratic_form.discr
- \+ *lemma* quadratic_form.discr_comp
- \+ *lemma* quadratic_form.discr_smul
- \+ *lemma* quadratic_form.ext
- \+ *lemma* quadratic_form.map_add_self
- \+ *lemma* quadratic_form.map_neg
- \+ *lemma* quadratic_form.map_smul
- \+ *lemma* quadratic_form.map_sub
- \+ *lemma* quadratic_form.map_zero
- \+ *def* quadratic_form.polar
- \+ *def* quadratic_form.pos_def
- \+ *lemma* quadratic_form.smul_apply
- \+ *lemma* quadratic_form.smul_pos_def_of_nonzero
- \+ *lemma* quadratic_form.smul_pos_def_of_smul_nonzero
- \+ *lemma* quadratic_form.to_fun_eq_apply
- \+ *def* quadratic_form.to_matrix
- \+ *lemma* quadratic_form.to_matrix_comp
- \+ *lemma* quadratic_form.to_matrix_smul



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

Added src/algebra/invertible.lean
- \+ *lemma* div_mul_cancel_of_invertible
- \+ *lemma* div_self_of_invertible
- \+ *lemma* inv_mul_cancel_of_invertible
- \+ *lemma* inv_of_div
- \+ *lemma* inv_of_eq_group_inv
- \+ *lemma* inv_of_eq_inv
- \+ *lemma* inv_of_eq_right_inv
- \+ *lemma* inv_of_inv_of
- \+ *lemma* inv_of_mul
- \+ *lemma* inv_of_mul_self
- \+ *lemma* inv_of_neg
- \+ *lemma* inv_of_one
- \+ *def* invertible_div
- \+ *def* invertible_inv
- \+ *def* invertible_inv_of
- \+ *def* invertible_mul
- \+ *def* invertible_neg
- \+ *def* invertible_of_group
- \+ *def* invertible_of_nonzero
- \+ *def* invertible_one
- \+ *lemma* is_unit_of_invertible
- \+ *lemma* mul_div_cancel_of_invertible
- \+ *lemma* mul_inv_cancel_of_invertible
- \+ *lemma* mul_inv_of_mul_self_cancel
- \+ *lemma* mul_inv_of_self
- \+ *lemma* mul_mul_inv_of_self_cancel
- \+ *lemma* nonzero_of_invertible



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
- \+/\- *def* f
- \+ *theorem* inst.spell'



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
- \+/\- *def* string.map_tokens
- \- *def* string.over_list
- \+/\- *def* string.split_on

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
- \+ *lemma* category_theory.adjunction.eq_hom_equiv_apply
- \+ *lemma* category_theory.adjunction.hom_equiv_apply_eq

Modified src/category_theory/limits/connected.lean


Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_limit.of_cone_equiv

Modified src/category_theory/limits/over.lean
- \+ *def* category_theory.over.construct_products.cones_equiv
- \+ *def* category_theory.over.construct_products.cones_equiv_functor
- \+ *def* category_theory.over.construct_products.cones_equiv_inverse
- \+ *def* category_theory.over.construct_products.has_over_limit_discrete_of_wide_pullback_limit
- \+ *def* category_theory.over.construct_products.over_binary_product_of_pullback
- \+ *def* category_theory.over.construct_products.over_finite_products_of_finite_wide_pullbacks
- \+ *def* category_theory.over.construct_products.over_product_of_wide_pullback
- \+ *def* category_theory.over.construct_products.over_products_of_wide_pullbacks
- \+ *def* category_theory.over.construct_products.wide_pullback_diagram_of_diagram_over
- \- *lemma* category_theory.over.over_prod_fst_left
- \- *lemma* category_theory.over.over_prod_map_left
- \- *lemma* category_theory.over.over_prod_pair_hom
- \- *lemma* category_theory.over.over_prod_pair_left
- \- *lemma* category_theory.over.over_prod_snd_left
- \- *def* category_theory.over.over_product_of_pullbacks

Modified src/category_theory/limits/shapes/pullbacks.lean
- \- *lemma* category_theory.limits.cocone.of_pushout_cocone_ι
- \- *lemma* category_theory.limits.cone.of_pullback_cone_π
- \- *lemma* category_theory.limits.pullback_cone.of_cone_π
- \- *lemma* category_theory.limits.pushout_cocone.of_cocone_ι
- \- *def* category_theory.limits.walking_cospan.hom.comp
- \- *lemma* category_theory.limits.walking_cospan.hom_id
- \- *def* category_theory.limits.walking_span.hom.comp
- \- *lemma* category_theory.limits.walking_span.hom_id

Added src/category_theory/limits/shapes/wide_pullbacks.lean
- \+ *def* has_finite_wide_pullbacks_of_has_finite_limits
- \+ *def* has_finite_wide_pushouts_of_has_finite_limits
- \+ *def* wide_pullback_shape.diagram_iso_wide_cospan
- \+ *lemma* wide_pullback_shape.hom_id
- \+ *def* wide_pullback_shape.wide_cospan
- \+ *def* wide_pullback_shape
- \+ *def* wide_pushout_shape.diagram_iso_wide_span
- \+ *lemma* wide_pushout_shape.hom_id
- \+ *def* wide_pushout_shape.wide_span
- \+ *def* wide_pushout_shape



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
- \+/\- *lemma* nat.factors_prime

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
- \+ *def* option.{u



## [2020-04-22 12:16:54](https://github.com/leanprover-community/mathlib/commit/e4abced)
chore(data/polynomial): rename type vars ([#2483](https://github.com/leanprover-community/mathlib/pull/2483))
Rename `α` to `R` etc; use `ι` for index types
No other changes
#### Estimated changes
Modified src/data/polynomial.lean
- \+/\- *lemma* is_integral_domain.polynomial
- \+/\- *def* polynomial.C
- \+/\- *lemma* polynomial.C_0
- \+/\- *lemma* polynomial.C_1
- \+/\- *lemma* polynomial.C_mul'
- \+/\- *def* polynomial.X
- \+/\- *lemma* polynomial.X_ne_zero
- \+/\- *lemma* polynomial.X_pow_sub_C_ne_zero
- \+/\- *lemma* polynomial.as_sum
- \+/\- *def* polynomial.binom_expansion
- \+/\- *lemma* polynomial.card_nth_roots
- \+/\- *lemma* polynomial.card_roots'
- \+/\- *lemma* polynomial.card_roots_X_pow_sub_C
- \+/\- *lemma* polynomial.card_roots_sub_C'
- \+/\- *lemma* polynomial.card_roots_sub_C
- \+/\- *lemma* polynomial.coe_eval₂_ring_hom
- \+/\- *lemma* polynomial.coe_norm_unit
- \+/\- *def* polynomial.coeff
- \+/\- *lemma* polynomial.coeff_C_mul
- \+/\- *lemma* polynomial.coeff_C_mul_X
- \+/\- *lemma* polynomial.coeff_X
- \+/\- *lemma* polynomial.coeff_X_one
- \+/\- *lemma* polynomial.coeff_X_zero
- \+/\- *lemma* polynomial.coeff_add
- \+/\- *def* polynomial.coeff_coe_to_fun
- \+/\- *lemma* polynomial.coeff_coe_units_zero_ne_zero
- \+/\- *lemma* polynomial.coeff_derivative
- \+/\- *lemma* polynomial.coeff_eq_zero_of_nat_degree_lt
- \+/\- *lemma* polynomial.coeff_inv_units
- \+/\- *lemma* polynomial.coeff_mk
- \+/\- *lemma* polynomial.coeff_mul
- \+/\- *theorem* polynomial.coeff_mul_X
- \+/\- *theorem* polynomial.coeff_mul_X_pow
- \+/\- *lemma* polynomial.coeff_mul_X_zero
- \+/\- *lemma* polynomial.coeff_mul_degree_add_degree
- \+/\- *lemma* polynomial.coeff_neg
- \+/\- *lemma* polynomial.coeff_one
- \+/\- *lemma* polynomial.coeff_one_zero
- \+/\- *lemma* polynomial.coeff_smul
- \+/\- *lemma* polynomial.coeff_sub
- \+/\- *lemma* polynomial.coeff_sum
- \+/\- *lemma* polynomial.coeff_zero
- \+/\- *lemma* polynomial.coeff_zero_eq_eval_zero
- \+/\- *def* polynomial.comp
- \+/\- *lemma* polynomial.comp_zero
- \+/\- *def* polynomial.decidable_dvd_monic
- \+/\- *def* polynomial.degree
- \+/\- *theorem* polynomial.degree_C_mul_X_pow_le
- \+/\- *lemma* polynomial.degree_X
- \+/\- *theorem* polynomial.degree_X_le
- \+/\- *lemma* polynomial.degree_X_pow
- \+/\- *theorem* polynomial.degree_X_pow_le
- \+/\- *lemma* polynomial.degree_X_pow_sub_C
- \+/\- *lemma* polynomial.degree_X_sub_C
- \+/\- *lemma* polynomial.degree_add_le
- \+/\- *lemma* polynomial.degree_coe_units
- \+/\- *lemma* polynomial.degree_derivative_eq
- \+/\- *lemma* polynomial.degree_div_by_monic_le
- \+/\- *lemma* polynomial.degree_div_by_monic_lt
- \+/\- *lemma* polynomial.degree_div_le
- \+/\- *lemma* polynomial.degree_eq_iff_nat_degree_eq
- \+/\- *lemma* polynomial.degree_eq_iff_nat_degree_eq_of_pos
- \+/\- *lemma* polynomial.degree_eq_one_of_irreducible_of_root
- \+/\- *lemma* polynomial.degree_erase_le
- \+/\- *theorem* polynomial.degree_le_iff_coeff_zero
- \+/\- *lemma* polynomial.degree_le_mul_left
- \+/\- *lemma* polynomial.degree_lt_wf
- \+/\- *lemma* polynomial.degree_map'
- \+/\- *lemma* polynomial.degree_map
- \+/\- *lemma* polynomial.degree_map_eq_of_injective
- \+/\- *lemma* polynomial.degree_map_eq_of_leading_coeff_ne_zero
- \+/\- *lemma* polynomial.degree_map_le
- \+/\- *theorem* polynomial.degree_mod_by_monic_le
- \+/\- *lemma* polynomial.degree_mod_by_monic_lt
- \+/\- *lemma* polynomial.degree_monomial_le
- \+/\- *lemma* polynomial.degree_mul_le
- \+/\- *lemma* polynomial.degree_mul_leading_coeff_inv
- \+/\- *lemma* polynomial.degree_neg
- \+/\- *lemma* polynomial.degree_one
- \+/\- *lemma* polynomial.degree_one_le
- \+/\- *lemma* polynomial.degree_pow_eq
- \+/\- *lemma* polynomial.degree_pow_le
- \+/\- *lemma* polynomial.degree_sum_le
- \+/\- *lemma* polynomial.degree_zero
- \+/\- *def* polynomial.derivative
- \+/\- *lemma* polynomial.derivative_C
- \+/\- *lemma* polynomial.derivative_X
- \+/\- *lemma* polynomial.derivative_add
- \+/\- *lemma* polynomial.derivative_eval
- \+/\- *lemma* polynomial.derivative_monomial
- \+/\- *lemma* polynomial.derivative_mul
- \+/\- *lemma* polynomial.derivative_one
- \+/\- *lemma* polynomial.derivative_sum
- \+/\- *lemma* polynomial.derivative_zero
- \+/\- *def* polynomial.div
- \+/\- *def* polynomial.div_X
- \+/\- *lemma* polynomial.div_X_C
- \+/\- *lemma* polynomial.div_X_mul_X_add
- \+/\- *def* polynomial.div_by_monic
- \+/\- *lemma* polynomial.div_by_monic_eq_div
- \+/\- *lemma* polynomial.div_by_monic_eq_of_not_monic
- \+/\- *lemma* polynomial.div_by_monic_one
- \+/\- *lemma* polynomial.div_by_monic_zero
- \+/\- *lemma* polynomial.div_mod_by_monic_unique
- \+/\- *def* polynomial.eval
- \+/\- *lemma* polynomial.eval_map
- \+/\- *lemma* polynomial.eval_neg
- \+/\- *lemma* polynomial.eval_one
- \+/\- *lemma* polynomial.eval_sub
- \+/\- *def* polynomial.eval_sub_factor
- \+/\- *lemma* polynomial.eval_sum
- \+/\- *lemma* polynomial.eval_zero
- \+/\- *def* polynomial.eval₂
- \+/\- *lemma* polynomial.eval₂_comp
- \+/\- *lemma* polynomial.eval₂_hom
- \+/\- *lemma* polynomial.eval₂_map
- \+/\- *lemma* polynomial.eval₂_neg
- \+/\- *lemma* polynomial.eval₂_one
- \+/\- *def* polynomial.eval₂_ring_hom
- \+/\- *lemma* polynomial.eval₂_sub
- \+/\- *lemma* polynomial.eval₂_sum
- \+/\- *lemma* polynomial.eval₂_zero
- \+/\- *lemma* polynomial.exists_finset_roots
- \+/\- *lemma* polynomial.ext
- \+/\- *theorem* polynomial.ext_iff
- \+/\- *lemma* polynomial.finset_sum_coeff
- \+/\- *lemma* polynomial.hom_eval₂
- \+/\- *lemma* polynomial.int_cast_eq_C
- \+/\- *def* polynomial.is_root
- \+/\- *lemma* polynomial.ite_le_nat_degree_coeff
- \+/\- *def* polynomial.lcoeff
- \+/\- *lemma* polynomial.lcoeff_apply
- \+/\- *def* polynomial.leading_coeff
- \+/\- *lemma* polynomial.leading_coeff_C
- \+/\- *lemma* polynomial.leading_coeff_X
- \+/\- *lemma* polynomial.leading_coeff_X_pow
- \+/\- *lemma* polynomial.leading_coeff_map
- \+/\- *lemma* polynomial.leading_coeff_monomial
- \+/\- *lemma* polynomial.leading_coeff_mul
- \+/\- *theorem* polynomial.leading_coeff_mul_X_pow
- \+/\- *lemma* polynomial.leading_coeff_of_injective
- \+/\- *lemma* polynomial.leading_coeff_one
- \+/\- *lemma* polynomial.leading_coeff_pow
- \+/\- *lemma* polynomial.leading_coeff_zero
- \+/\- *def* polynomial.map
- \+/\- *lemma* polynomial.map_div
- \+/\- *lemma* polynomial.map_div_by_monic
- \+/\- *lemma* polynomial.map_eq_zero
- \+/\- *lemma* polynomial.map_injective
- \+/\- *lemma* polynomial.map_map
- \+/\- *lemma* polynomial.map_mod
- \+/\- *lemma* polynomial.map_mod_by_monic
- \+/\- *lemma* polynomial.map_mod_div_by_monic
- \+/\- *lemma* polynomial.map_neg
- \+/\- *lemma* polynomial.map_one
- \+/\- *lemma* polynomial.map_sub
- \+/\- *lemma* polynomial.map_zero
- \+/\- *lemma* polynomial.mem_map_range
- \+/\- *lemma* polynomial.mem_nth_roots
- \+/\- *lemma* polynomial.mem_roots_sub_C
- \+/\- *lemma* polynomial.mem_support_derivative
- \+/\- *def* polynomial.mod
- \+/\- *lemma* polynomial.mod_X_sub_C_eq_C_eval
- \+/\- *def* polynomial.mod_by_monic
- \+/\- *lemma* polynomial.mod_by_monic_X
- \+/\- *lemma* polynomial.mod_by_monic_X_sub_C_eq_C_eval
- \+/\- *lemma* polynomial.mod_by_monic_add_div
- \+/\- *lemma* polynomial.mod_by_monic_eq_mod
- \+/\- *lemma* polynomial.mod_by_monic_eq_of_not_monic
- \+/\- *lemma* polynomial.mod_by_monic_eq_sub_mul_div
- \+/\- *lemma* polynomial.mod_by_monic_one
- \+/\- *lemma* polynomial.mod_by_monic_zero
- \+/\- *lemma* polynomial.monic.as_sum
- \+/\- *lemma* polynomial.monic.leading_coeff
- \+/\- *lemma* polynomial.monic.ne_zero
- \+/\- *lemma* polynomial.monic.ne_zero_of_zero_ne_one
- \+/\- *def* polynomial.monic
- \+/\- *lemma* polynomial.monic_X
- \+/\- *theorem* polynomial.monic_X_add_C
- \+/\- *theorem* polynomial.monic_X_sub_C
- \+/\- *lemma* polynomial.monic_map
- \+/\- *lemma* polynomial.monic_of_injective
- \+/\- *lemma* polynomial.monic_one
- \+/\- *def* polynomial.monomial
- \+/\- *theorem* polynomial.mul_X_pow_eq_zero
- \+/\- *lemma* polynomial.multiplicity_X_sub_C_finite
- \+/\- *lemma* polynomial.nat_cast_eq_C
- \+/\- *def* polynomial.nat_degree
- \+/\- *lemma* polynomial.nat_degree_C
- \+/\- *lemma* polynomial.nat_degree_coe_units
- \+/\- *lemma* polynomial.nat_degree_eq_of_degree_eq
- \+/\- *lemma* polynomial.nat_degree_eq_of_degree_eq_some
- \+/\- *lemma* polynomial.nat_degree_int_cast
- \+/\- *theorem* polynomial.nat_degree_le_of_degree_le
- \+/\- *lemma* polynomial.nat_degree_map'
- \+/\- *lemma* polynomial.nat_degree_map
- \+/\- *lemma* polynomial.nat_degree_nat_cast
- \+/\- *lemma* polynomial.nat_degree_neg
- \+/\- *lemma* polynomial.nat_degree_one
- \+/\- *lemma* polynomial.nat_degree_pow_eq
- \+/\- *lemma* polynomial.nat_degree_zero
- \+/\- *lemma* polynomial.ne_zero_of_monic_of_zero_ne_one
- \+/\- *def* polynomial.nonzero_comm_ring.of_polynomial_ne
- \+/\- *def* polynomial.nonzero_comm_semiring.of_polynomial_ne
- \+/\- *lemma* polynomial.not_monic_zero
- \+/\- *def* polynomial.nth_roots
- \+/\- *lemma* polynomial.one_comp
- \+/\- *def* polynomial.pow_add_expansion
- \+/\- *lemma* polynomial.pow_root_multiplicity_dvd
- \+/\- *def* polynomial.pow_sub_pow_factor
- \+/\- *lemma* polynomial.root_mul_left_of_is_root
- \+/\- *lemma* polynomial.root_mul_right_of_is_root
- \+/\- *def* polynomial.root_multiplicity
- \+/\- *lemma* polynomial.root_multiplicity_eq_multiplicity
- \+/\- *lemma* polynomial.subsingleton_of_monic_zero
- \+/\- *lemma* polynomial.sum_C_mul_X_eq
- \+/\- *lemma* polynomial.support_zero
- \+/\- *lemma* polynomial.zero_comp
- \+/\- *lemma* polynomial.zero_div_by_monic
- \+/\- *lemma* polynomial.zero_is_root_of_coeff_zero_eq_zero
- \+/\- *lemma* polynomial.zero_le_degree_iff
- \+/\- *lemma* polynomial.zero_mod_by_monic
- \+/\- *def* polynomial

Modified src/ring_theory/adjoin.lean




## [2020-04-22 12:16:52](https://github.com/leanprover-community/mathlib/commit/5965370)
feat(data/monoid_algebra): algebra structure, lift of morphisms ([#2366](https://github.com/leanprover-community/mathlib/pull/2366))
Prove that for a monoid homomorphism `f : G →* R` from a monoid `G` to a `k`-algebra `R` there exists a unique algebra morphism `g : k[G] →ₐ[k] R` such that `∀ x : G, g (single x 1) = f x`.
This is expressed as `def lift : (G →* R) ≃ (monoid_algebra k G →ₐ[k] R)`.
I want to use this to define `aeval` and `eval₂` for polynomials. This way we'll have many properties for free.
#### Estimated changes
Modified src/algebra/ring.lean
- \+/\- *lemma* coe_add_monoid_hom'
- \+/\- *lemma* coe_add_monoid_hom
- \+/\- *lemma* coe_monoid_hom'
- \+/\- *lemma* coe_monoid_hom

Modified src/data/monoid_algebra.lean
- \+ *lemma* add_monoid_algebra.coe_algebra_map
- \+ *def* add_monoid_algebra.lift
- \+ *lemma* add_monoid_algebra.mul_apply
- \+ *lemma* add_monoid_algebra.mul_single_apply_aux
- \+ *lemma* add_monoid_algebra.mul_single_zero_apply
- \+ *def* add_monoid_algebra.of
- \+ *lemma* add_monoid_algebra.of_apply
- \+ *lemma* add_monoid_algebra.single_mul_apply_aux
- \+/\- *lemma* add_monoid_algebra.single_mul_single
- \+ *lemma* add_monoid_algebra.single_zero_mul_apply
- \+ *lemma* monoid_algebra.alg_hom_ext
- \+ *lemma* monoid_algebra.coe_algebra_map
- \+ *def* monoid_algebra.lift
- \+ *lemma* monoid_algebra.lift_apply
- \+ *lemma* monoid_algebra.lift_of
- \+ *lemma* monoid_algebra.lift_single
- \+ *lemma* monoid_algebra.lift_symm_apply
- \+ *lemma* monoid_algebra.lift_unique'
- \+ *lemma* monoid_algebra.lift_unique
- \+ *lemma* monoid_algebra.mul_apply_antidiagonal
- \+ *lemma* monoid_algebra.mul_single_apply_aux
- \+ *lemma* monoid_algebra.mul_single_one_apply
- \+ *def* monoid_algebra.of
- \+ *lemma* monoid_algebra.of_apply
- \+ *lemma* monoid_algebra.single_eq_algebra_map_mul_of
- \+ *lemma* monoid_algebra.single_mul_apply_aux
- \+/\- *lemma* monoid_algebra.single_mul_single
- \+ *lemma* monoid_algebra.single_one_mul_apply
- \+ *lemma* monoid_algebra.single_pow

Modified src/data/padics/padic_integers.lean


Modified src/data/polynomial.lean


Modified src/ring_theory/algebra.lean
- \+ *lemma* alg_hom.coe_mk
- \+ *lemma* alg_hom.coe_to_monoid_hom
- \+ *lemma* alg_hom.coe_to_ring_hom
- \+ *lemma* alg_hom.map_pow
- \+ *lemma* alg_hom.map_prod
- \+ *lemma* alg_hom.map_smul
- \+ *lemma* alg_hom.map_sum
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
Added src/group_theory/bundled_subgroup.lean
- \+ *lemma* add_subgroup.gsmul_mem
- \+ *lemma* add_subgroup.mem_closure_singleton
- \+ *def* add_subgroup.of_subgroup
- \+ *def* add_subgroup.to_subgroup
- \+ *lemma* monoid_hom.coe_range
- \+ *lemma* monoid_hom.comap_ker
- \+ *def* monoid_hom.eq_locus
- \+ *lemma* monoid_hom.eq_of_eq_on_dense
- \+ *lemma* monoid_hom.eq_of_eq_on_top
- \+ *lemma* monoid_hom.eq_on_closure
- \+ *lemma* monoid_hom.gclosure_preimage_le
- \+ *def* monoid_hom.ker
- \+ *lemma* monoid_hom.map_closure
- \+ *lemma* monoid_hom.map_range
- \+ *lemma* monoid_hom.mem_ker
- \+ *lemma* monoid_hom.mem_range
- \+ *lemma* monoid_hom.rang_top_of_surjective
- \+ *def* monoid_hom.range
- \+ *lemma* monoid_hom.range_top_iff_surjective
- \+ *def* mul_equiv.subgroup_congr
- \+ *def* subgroup.add_subgroup_equiv
- \+ *lemma* subgroup.bot_prod_bot
- \+ *def* subgroup.closure
- \+ *lemma* subgroup.closure_Union
- \+ *lemma* subgroup.closure_empty
- \+ *lemma* subgroup.closure_eq
- \+ *lemma* subgroup.closure_eq_of_le
- \+ *lemma* subgroup.closure_induction
- \+ *lemma* subgroup.closure_le
- \+ *lemma* subgroup.closure_mono
- \+ *lemma* subgroup.closure_union
- \+ *lemma* subgroup.closure_univ
- \+ *lemma* subgroup.coe_Inf
- \+ *lemma* subgroup.coe_bot
- \+ *lemma* subgroup.coe_coe
- \+ *lemma* subgroup.coe_comap
- \+ *lemma* subgroup.coe_inf
- \+ *lemma* subgroup.coe_inv
- \+ *lemma* subgroup.coe_map
- \+ *lemma* subgroup.coe_mul
- \+ *lemma* subgroup.coe_one
- \+ *lemma* subgroup.coe_prod
- \+ *lemma* subgroup.coe_ssubset_coe
- \+ *lemma* subgroup.coe_subset_coe
- \+ *theorem* subgroup.coe_subtype
- \+ *lemma* subgroup.coe_top
- \+ *def* subgroup.comap
- \+ *lemma* subgroup.comap_comap
- \+ *lemma* subgroup.comap_inf
- \+ *lemma* subgroup.comap_infi
- \+ *lemma* subgroup.comap_top
- \+ *theorem* subgroup.ext'
- \+ *theorem* subgroup.ext
- \+ *lemma* subgroup.gc_map_comap
- \+ *lemma* subgroup.gpow_mem
- \+ *theorem* subgroup.inv_mem
- \+ *lemma* subgroup.le_def
- \+ *lemma* subgroup.list_prod_mem
- \+ *def* subgroup.map
- \+ *lemma* subgroup.map_bot
- \+ *lemma* subgroup.map_le_iff_le_comap
- \+ *lemma* subgroup.map_map
- \+ *lemma* subgroup.map_sup
- \+ *lemma* subgroup.map_supr
- \+ *lemma* subgroup.mem_Inf
- \+ *lemma* subgroup.mem_Sup_of_directed_on
- \+ *lemma* subgroup.mem_bot
- \+ *lemma* subgroup.mem_closure
- \+ *lemma* subgroup.mem_closure_singleton
- \+ *lemma* subgroup.mem_coe
- \+ *lemma* subgroup.mem_comap
- \+ *lemma* subgroup.mem_inf
- \+ *lemma* subgroup.mem_map
- \+ *lemma* subgroup.mem_prod
- \+ *lemma* subgroup.mem_supr_of_directed
- \+ *lemma* subgroup.mem_top
- \+ *theorem* subgroup.mul_mem
- \+ *lemma* subgroup.multiset_prod_mem
- \+ *def* subgroup.of
- \+ *def* subgroup.of_add_subgroup
- \+ *theorem* subgroup.one_mem
- \+ *lemma* subgroup.pow_mem
- \+ *def* subgroup.prod
- \+ *def* subgroup.prod_equiv
- \+ *lemma* subgroup.prod_mem
- \+ *lemma* subgroup.prod_mono
- \+ *lemma* subgroup.prod_mono_left
- \+ *lemma* subgroup.prod_mono_right
- \+ *lemma* subgroup.prod_top
- \+ *lemma* subgroup.subset_closure
- \+ *def* subgroup.subtype
- \+ *def* subgroup.to_add_subgroup
- \+ *lemma* subgroup.top_prod
- \+ *lemma* subgroup.top_prod_top



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
- \- *def* where.inflate

Added test/where.lean




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


Added src/tactic/simp_command.lean


Added test/simp_command.lean
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
- \+ *lemma* category_theory.bundled.coe_mk

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
- \+ *lemma* int.dvd_sub_of_mod_eq
- \+ *lemma* int.eq_of_mod_eq_of_nat_abs_sub_lt_nat_abs
- \+ *lemma* int.eq_zero_of_dvd_of_nat_abs_lt_nat_abs

Modified src/data/nat/basic.lean
- \+ *lemma* nat.eq_zero_of_dvd_of_lt
- \+ *lemma* nat.sub_mod_eq_zero_of_mod_eq



## [2020-04-20 15:36:53](https://github.com/leanprover-community/mathlib/commit/d1ba87a)
feat(category_theory/faithful): faithful.of_iso ([#2453](https://github.com/leanprover-community/mathlib/pull/2453))
A minor useful lemma, about to be abandoned on another branch.
#### Estimated changes
Modified src/category_theory/fully_faithful.lean
- \+ *lemma* category_theory.faithful.of_comp_iso
- \+ *lemma* category_theory.faithful.of_iso



## [2020-04-20 15:36:51](https://github.com/leanprover-community/mathlib/commit/51e03aa)
feat(data/monoid_algebra): the distrib_mul_action ([#2417](https://github.com/leanprover-community/mathlib/pull/2417))
#### Estimated changes
Modified src/data/finsupp.lean
- \+ *def* finsupp.comap_distrib_mul_action
- \+ *def* finsupp.comap_distrib_mul_action_self
- \+ *def* finsupp.comap_has_scalar
- \+ *def* finsupp.comap_mul_action
- \+ *lemma* finsupp.comap_smul_apply
- \+ *lemma* finsupp.comap_smul_single

Modified src/data/monoid_algebra.lean


Modified src/group_theory/group_action.lean
- \+ *def* mul_action.regular



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
- \+ *def* category_theory.op_op_equivalence
- \+ *def* category_theory.unop_unop



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
- \- *def* category_theory.limits.cocone_parallel_pair_self
- \- *lemma* category_theory.limits.cocone_parallel_pair_self_X
- \- *lemma* category_theory.limits.cocone_parallel_pair_self_ι_app_one
- \+ *def* category_theory.limits.coequalizer.π_of_eq
- \- *def* category_theory.limits.coequalizer.π_of_self'
- \- *lemma* category_theory.limits.cofork.eq_of_π_π
- \- *def* category_theory.limits.colimit_cocone_parallel_pair_self_is_iso'
- \- *def* category_theory.limits.colimit_cocone_parallel_pair_self_is_iso
- \- *def* category_theory.limits.cone_parallel_pair_self
- \- *lemma* category_theory.limits.cone_parallel_pair_self_X
- \- *lemma* category_theory.limits.cone_parallel_pair_self_π_app_zero
- \- *def* category_theory.limits.epi_limit_cone_parallel_pair_is_iso
- \+ *def* category_theory.limits.equalizer.ι_of_eq
- \- *def* category_theory.limits.equalizer.ι_of_self'
- \- *lemma* category_theory.limits.fork.eq_of_ι_ι
- \+ *def* category_theory.limits.id_cofork
- \+ *def* category_theory.limits.id_fork
- \- *def* category_theory.limits.is_colimit_cocone_parallel_pair_self
- \+ *def* category_theory.limits.is_colimit_id_cofork
- \+ *def* category_theory.limits.is_iso_colimit_cocone_parallel_pair_of_eq
- \+ *def* category_theory.limits.is_iso_colimit_cocone_parallel_pair_of_self
- \+ *def* category_theory.limits.is_iso_limit_cocone_parallel_pair_of_epi
- \+ *def* category_theory.limits.is_iso_limit_cone_parallel_pair_of_epi
- \+ *def* category_theory.limits.is_iso_limit_cone_parallel_pair_of_eq
- \+ *def* category_theory.limits.is_iso_limit_cone_parallel_pair_of_self
- \- *def* category_theory.limits.is_limit_cone_parallel_pair_self
- \+ *def* category_theory.limits.is_limit_id_fork
- \- *def* category_theory.limits.limit_cone_parallel_pair_self_is_iso'
- \- *def* category_theory.limits.limit_cone_parallel_pair_self_is_iso
- \- *def* category_theory.limits.mono_limit_cocone_parallel_pair_is_iso

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
- \+ *lemma* category_theory.limits.has_image_map.factor_map



## [2020-04-19 14:00:03](https://github.com/leanprover-community/mathlib/commit/aa55f8b)
feat(category_theory/eq_to_iso): missing simp lemma ([#2454](https://github.com/leanprover-community/mathlib/pull/2454))
A missing simp lemma.
#### Estimated changes
Modified src/category_theory/eq_to_hom.lean
- \+ *lemma* category_theory.eq_to_iso.inv



## [2020-04-19 14:00:01](https://github.com/leanprover-community/mathlib/commit/9801c1c)
feat(continued_fractions) add stabilisation under termination lemmas ([#2451](https://github.com/leanprover-community/mathlib/pull/2451))
- continued fractions: add lemmas for stabilisation of computations under termination and add them to default exports
- seq: make argument in seq.terminated_stable explicit
#### Estimated changes
Modified src/algebra/continued_fractions/default.lean


Added src/algebra/continued_fractions/terminated_stable.lean
- \+ *lemma* generalized_continued_fraction.continuants_aux_stable_of_terminated
- \+ *lemma* generalized_continued_fraction.continuants_aux_stable_step_of_terminated
- \+ *lemma* generalized_continued_fraction.continuants_stable_of_terminated
- \+ *lemma* generalized_continued_fraction.convergents'_aux_stable_of_terminated
- \+ *lemma* generalized_continued_fraction.convergents'_aux_stable_step_of_terminated
- \+ *lemma* generalized_continued_fraction.convergents'_stable_of_terminated
- \+ *lemma* generalized_continued_fraction.convergents_stable_of_terminated
- \+ *lemma* generalized_continued_fraction.denominators_stable_of_terminated
- \+ *lemma* generalized_continued_fraction.numerators_stable_of_terminated
- \+ *lemma* generalized_continued_fraction.terminated_stable

Modified src/data/seq/seq.lean
- \+/\- *lemma* seq.terminated_stable



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
- \+/\- *def* linear_map.comp
- \+/\- *lemma* linear_map.comp_apply
- \+/\- *theorem* linear_map.ext
- \+/\- *theorem* linear_map.ext_iff
- \+/\- *def* linear_map.id
- \+/\- *lemma* linear_map.id_apply
- \+/\- *def* linear_map.to_add_monoid_hom
- \+/\- *lemma* linear_map.to_add_monoid_hom_coe
- \+/\- *lemma* linear_map.to_fun_eq_coe
- \+/\- *theorem* submodule.ext'
- \+/\- *theorem* submodule.ext
- \+/\- *lemma* submodule.subtype_eq_val

Modified src/linear_algebra/basic.lean
- \+/\- *theorem* linear_equiv.apply_symm_apply
- \+/\- *theorem* linear_equiv.coe_apply
- \+/\- *lemma* linear_equiv.coe_prod
- \+/\- *lemma* linear_equiv.eq_bot_of_equiv
- \+/\- *lemma* linear_equiv.ext
- \+/\- *theorem* linear_equiv.map_add
- \+/\- *theorem* linear_equiv.map_eq_zero_iff
- \+/\- *theorem* linear_equiv.map_ne_zero_iff
- \+/\- *theorem* linear_equiv.map_neg
- \+/\- *theorem* linear_equiv.map_smul
- \+/\- *theorem* linear_equiv.map_sub
- \+/\- *theorem* linear_equiv.map_zero
- \+/\- *theorem* linear_equiv.of_bijective_apply
- \+/\- *def* linear_equiv.of_linear
- \+/\- *theorem* linear_equiv.of_linear_apply
- \+/\- *theorem* linear_equiv.of_linear_symm_apply
- \+/\- *def* linear_equiv.of_top
- \+/\- *theorem* linear_equiv.of_top_apply
- \+/\- *theorem* linear_equiv.of_top_symm_apply
- \+/\- *lemma* linear_equiv.prod_apply
- \+/\- *lemma* linear_equiv.prod_symm
- \+/\- *def* linear_equiv.refl
- \+/\- *lemma* linear_equiv.refl_apply
- \+/\- *lemma* linear_equiv.skew_prod_apply
- \+/\- *lemma* linear_equiv.skew_prod_symm_apply
- \+/\- *def* linear_equiv.symm
- \+/\- *theorem* linear_equiv.symm_apply_apply
- \+/\- *theorem* linear_equiv.symm_symm
- \+/\- *theorem* linear_equiv.symm_symm_apply
- \+/\- *def* linear_equiv.to_add_equiv
- \+/\- *def* linear_equiv.trans
- \+/\- *theorem* linear_equiv.trans_apply



## [2020-04-19 01:55:09](https://github.com/leanprover-community/mathlib/commit/0ceac44)
feat(data/nat/prime) factors of a prime number is the list [p] ([#2452](https://github.com/leanprover-community/mathlib/pull/2452))
The factors of a prime number are [p].
#### Estimated changes
Modified src/data/nat/prime.lean
- \+ *lemma* nat.factors_prime



## [2020-04-18 23:47:08](https://github.com/leanprover-community/mathlib/commit/99245b3)
chore(*): switch to lean 3.9.0 ([#2449](https://github.com/leanprover-community/mathlib/pull/2449))
It's been too long since the last Lean release.
#### Estimated changes
Modified leanpkg.toml


Modified src/data/array/lemmas.lean
- \- *theorem* array.read_foreach_aux
- \+/\- *theorem* array.read_map

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
- \+ *def* category_theory.over.creates_connected.nat_trans_in_over
- \+ *def* category_theory.over.creates_connected.raise_cone
- \+ *def* category_theory.over.creates_connected.raised_cone_is_limit
- \+ *lemma* category_theory.over.creates_connected.raised_cone_lowers_to_original



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
- \+ *theorem* equiv.apply_eq_iff_eq_symm_apply

Modified src/tactic/core.lean


Added src/tactic/transport.lean


Modified test/equiv_rw.lean
- \+/\- *def* monoid.map

Added test/transport/basic.lean
- \+ *def* lie_ring.map
- \+ *lemma* mynat_add_def
- \+ *def* mynat_equiv
- \+ *lemma* mynat_equiv_apply_succ
- \+ *lemma* mynat_equiv_apply_zero
- \+ *lemma* mynat_equiv_symm_apply_succ
- \+ *lemma* mynat_equiv_symm_apply_zero
- \+ *lemma* mynat_mul_def
- \+ *lemma* mynat_one_def
- \+ *lemma* mynat_zero_def
- \+ *def* semiring.map
- \+ *def* sup_top.map



## [2020-04-18 12:23:55](https://github.com/leanprover-community/mathlib/commit/ffb99a3)
chore(algebra/group/type_tags): add `additive.to_mul` etc ([#2363](https://github.com/leanprover-community/mathlib/pull/2363))
Don't make `additive` and `multiplicative` irreducible (yet?) because
it breaks compilation here and there.
Also prove that homomorphisms from `ℕ`, `ℤ` and their `multiplicative`
versions are defined by the image of `1`.
#### Estimated changes
Modified src/algebra/group/type_tags.lean
- \+ *def* additive.of_mul
- \+ *def* additive.to_mul
- \+ *def* multiplicative.of_add
- \+ *def* multiplicative.to_add
- \+ *lemma* of_add_add
- \+ *lemma* of_add_inj
- \+ *lemma* of_add_neg
- \+ *lemma* of_add_to_add
- \+ *lemma* of_add_zero
- \+ *lemma* of_mul_inj
- \+ *lemma* of_mul_inv
- \+ *lemma* of_mul_mul
- \+ *lemma* of_mul_one
- \+ *lemma* of_mul_to_mul
- \+ *lemma* to_add_inj
- \+ *lemma* to_add_inv
- \+ *lemma* to_add_mul
- \+ *lemma* to_add_of_add
- \+ *lemma* to_add_one
- \+ *lemma* to_mul_add
- \+ *lemma* to_mul_inj
- \+ *lemma* to_mul_neg
- \+ *lemma* to_mul_of_mul
- \+ *lemma* to_mul_zero

Modified src/algebra/group_power.lean
- \+ *def* gmultiples_hom
- \+ *lemma* gpow_of_add
- \+ *def* gpowers_hom
- \+ *def* multiples_hom
- \+ *lemma* pow_of_add
- \+ *def* powers_hom

Modified src/group_theory/submonoid.lean
- \+ *lemma* add_submonoid.closure_singleton_eq
- \+/\- *lemma* add_submonoid.mem_closure_singleton
- \+ *lemma* submonoid.closure_singleton_eq



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
- \+ *lemma* algebraic_geometry.PresheafedSpace.id_coe_fn

Modified src/tactic/abel.lean


Modified src/tactic/lint/default.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/ring.lean


Added test/lint_coe_to_fun.lean




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
- \+/\- *def* complex.of_real

Modified src/data/int/basic.lean
- \+ *theorem* add_monoid_hom.eq_int_cast
- \+/\- *theorem* int.cast_id
- \- *theorem* int.eq_cast
- \+ *def* int.of_nat_hom

Modified src/data/nat/cast.lean
- \+ *lemma* add_monoid_hom.eq_nat_cast
- \+/\- *theorem* nat.cast_id
- \- *theorem* nat.eq_cast'
- \- *theorem* nat.eq_cast
- \+ *lemma* ring_hom.eq_nat_cast
- \+/\- *lemma* ring_hom.map_nat_cast

Modified src/data/polynomial.lean


Modified src/data/rat/cast.lean
- \- *theorem* rat.eq_cast
- \- *theorem* rat.eq_cast_of_ne_zero
- \+ *lemma* ring_hom.eq_rat_cast
- \+ *lemma* ring_hom.map_rat_cast

Modified src/data/real/basic.lean
- \+/\- *def* real.of_rat



## [2020-04-17 13:44:40](https://github.com/leanprover-community/mathlib/commit/855e70b)
feat(data/nat): Results about nat.choose ([#2421](https://github.com/leanprover-community/mathlib/pull/2421))
A convenience lemma for symmetry of choose and inequalities about choose.
More results from my combinatorics project.
#### Estimated changes
Modified src/data/nat/basic.lean
- \+ *lemma* nat.choose_symm_add
- \+ *lemma* nat.choose_symm_of_eq_add

Modified src/data/nat/choose.lean
- \+ *lemma* choose_le_middle
- \+ *lemma* choose_le_succ_of_lt_half_left



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
Added src/analysis/analytic/composition.lean
- \+ *theorem* analytic_at.comp
- \+ *def* formal_multilinear_series.apply_composition
- \+ *lemma* formal_multilinear_series.apply_composition_update
- \+ *def* formal_multilinear_series.comp_along_composition
- \+ *def* formal_multilinear_series.comp_along_composition_multilinear
- \+ *lemma* formal_multilinear_series.comp_along_composition_multilinear_bound
- \+ *lemma* formal_multilinear_series.comp_along_composition_nnnorm
- \+ *lemma* formal_multilinear_series.comp_along_composition_norm
- \+ *def* formal_multilinear_series.comp_change_of_variables
- \+ *lemma* formal_multilinear_series.comp_change_of_variables_blocks_fun
- \+ *lemma* formal_multilinear_series.comp_change_of_variables_length
- \+ *lemma* formal_multilinear_series.comp_partial_sum
- \+ *def* formal_multilinear_series.comp_partial_sum_source
- \+ *def* formal_multilinear_series.comp_partial_sum_target
- \+ *def* formal_multilinear_series.comp_partial_sum_target_set
- \+ *lemma* formal_multilinear_series.comp_partial_sum_target_subset_image_comp_partial_sum_source
- \+ *lemma* formal_multilinear_series.comp_partial_sum_target_tendsto_at_top
- \+ *theorem* formal_multilinear_series.comp_summable_nnreal
- \+ *theorem* formal_multilinear_series.le_comp_radius_of_summable
- \+ *lemma* formal_multilinear_series.mem_comp_partial_sum_source_iff
- \+ *lemma* formal_multilinear_series.mem_comp_partial_sum_target_iff
- \+ *theorem* has_fpower_series_at.comp

Modified src/analysis/normed_space/basic.lean
- \+ *lemma* nnnorm_sum_le

Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.pow_le_pow

Modified src/data/set/function.lean
- \+ *lemma* function.update_comp_eq_of_injective
- \+ *lemma* function.update_comp_eq_of_not_mem_range

Modified src/order/filter/basic.lean
- \+ *lemma* filter.monotone.tendsto_at_top_finset



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
- \+ *lemma* category_theory.arrow.lift.fac_left
- \+ *lemma* category_theory.arrow.lift.fac_right
- \+ *lemma* category_theory.arrow.lift_mk'_left
- \+ *lemma* category_theory.arrow.lift_mk'_right
- \+ *lemma* category_theory.arrow.w

Modified src/category_theory/limits/shapes/images.lean
- \+ *lemma* category_theory.limits.image.fac_lift
- \+ *lemma* category_theory.limits.is_image.fac_lift
- \+ *def* category_theory.limits.strong_epi_mono_factorisation.to_mono_is_image

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel_cofork.is_colimit.desc'
- \- *def* category_theory.limits.cokernel_cofork.is_limit.desc'

Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/limits/shapes/regular_mono.lean
- \+ *def* category_theory.normal_epi.desc'
- \+ *def* category_theory.normal_mono.lift'
- \+ *def* category_theory.regular_epi.desc'
- \+ *def* category_theory.regular_mono.lift'

Added src/category_theory/limits/shapes/strong_epi.lean
- \+ *def* category_theory.mono_strong_epi_is_iso
- \+ *def* category_theory.strong_epi_comp
- \+ *def* category_theory.strong_epi_of_strong_epi



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
- \+/\- *def* category_theory.adjunction.functoriality_counit'
- \+/\- *def* category_theory.adjunction.functoriality_counit
- \+/\- *def* category_theory.adjunction.functoriality_unit'
- \+/\- *def* category_theory.adjunction.functoriality_unit

Modified src/category_theory/limits/cones.lean
- \+/\- *def* category_theory.functor.map_cocone
- \+/\- *def* category_theory.functor.map_cocone_morphism
- \+/\- *def* category_theory.functor.map_cone
- \- *lemma* category_theory.functor.map_cone_inv_X
- \+ *def* category_theory.functor.map_cone_map_cone_inv
- \+/\- *def* category_theory.functor.map_cone_morphism

Added src/category_theory/limits/creates.lean
- \+ *def* category_theory.creates_colimit_of_reflects_iso
- \+ *def* category_theory.creates_limit_of_reflects_iso
- \+ *def* category_theory.has_colimit_of_created
- \+ *def* category_theory.has_limit_of_created
- \+ *def* category_theory.id_lifts_cocone
- \+ *def* category_theory.id_lifts_cone
- \+ *def* category_theory.lift_colimit
- \+ *def* category_theory.lift_limit
- \+ *def* category_theory.lifted_colimit_is_colimit
- \+ *def* category_theory.lifted_colimit_maps_to_original
- \+ *def* category_theory.lifted_limit_is_limit
- \+ *def* category_theory.lifted_limit_maps_to_original
- \+ *def* category_theory.lifts_to_colimit_of_creates
- \+ *def* category_theory.lifts_to_limit_of_creates

Modified src/category_theory/limits/limits.lean
- \+ *def* category_theory.limits.is_limit.map_cone_equiv

Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/monad/algebra.lean
- \+ *def* category_theory.monad.algebra_iso_of_iso

Modified src/category_theory/monad/limits.lean
- \- *def* category_theory.monad.forget_creates_colimits.c
- \+/\- *def* category_theory.monad.forget_creates_colimits.lambda
- \+ *def* category_theory.monad.forget_creates_colimits.lifted_cocone
- \+ *def* category_theory.monad.forget_creates_colimits.lifted_cocone_is_colimit
- \+ *def* category_theory.monad.forget_creates_colimits.new_cocone
- \- *def* category_theory.monad.forget_creates_limits.c
- \+/\- *def* category_theory.monad.forget_creates_limits.cone_point
- \+ *def* category_theory.monad.forget_creates_limits.lifted_cone
- \+ *def* category_theory.monad.forget_creates_limits.lifted_cone_is_limit
- \+ *def* category_theory.monad.forget_creates_limits.new_cone
- \- *def* category_theory.monad.forget_creates_limits
- \+ *def* category_theory.monad.has_limit_of_comp_forget_has_limit

Added src/category_theory/reflect_isomorphisms.lean
- \+ *def* category_theory.cocone_iso_of_hom_iso
- \+ *def* category_theory.cone_iso_of_hom_iso
- \+ *def* category_theory.is_iso_of_reflects_iso



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
- \- *lemma* lie_algebra.map_lie'
- \+/\- *lemma* lie_algebra.map_lie



## [2020-04-16 14:03:47](https://github.com/leanprover-community/mathlib/commit/c3d943e)
feat(computability): strong reducibility and degrees ([#1203](https://github.com/leanprover-community/mathlib/pull/1203))
#### Estimated changes
Modified docs/references.bib


Modified src/computability/halting.lean


Modified src/computability/partrec.lean


Modified src/computability/partrec_code.lean
- \+ *theorem* nat.partrec.code.injective_const
- \+ *theorem* nat.partrec.code.injective_curry
- \+ *theorem* nat.partrec.code.smn

Modified src/computability/primrec.lean


Added src/computability/reduce.lean
- \+ *theorem* computable.equiv₂
- \+ *theorem* computable.eqv
- \+ *theorem* computable_pred.computable_of_many_one_reducible
- \+ *theorem* computable_pred.computable_of_one_one_reducible
- \+ *theorem* disjoin_le
- \+ *theorem* disjoin_many_one_reducible
- \+ *theorem* equiv.computable.symm
- \+ *theorem* equiv.computable.trans
- \+ *def* equiv.computable
- \+ *theorem* equivalence_of_many_one_equiv
- \+ *theorem* equivalence_of_one_one_equiv
- \+ *def* many_one_degree.add
- \+ *theorem* many_one_degree.add_le'
- \+ *theorem* many_one_degree.add_le
- \+ *def* many_one_degree.comap
- \+ *def* many_one_degree.le
- \+ *theorem* many_one_degree.le_add_left'
- \+ *theorem* many_one_degree.le_add_left
- \+ *theorem* many_one_degree.le_add_right'
- \+ *theorem* many_one_degree.le_add_right
- \+ *theorem* many_one_degree.le_antisymm
- \+ *theorem* many_one_degree.le_comap_left
- \+ *theorem* many_one_degree.le_comap_right
- \+ *theorem* many_one_degree.le_refl
- \+ *theorem* many_one_degree.le_trans
- \+ *def* many_one_degree.of
- \+ *theorem* many_one_degree.of_le_of'
- \+ *theorem* many_one_degree.of_le_of
- \+ *def* many_one_degree
- \+ *theorem* many_one_equiv.congr_left
- \+ *theorem* many_one_equiv.congr_right
- \+ *theorem* many_one_equiv.le_congr_left
- \+ *theorem* many_one_equiv.le_congr_right
- \+ *theorem* many_one_equiv.of_equiv
- \+ *theorem* many_one_equiv.symm
- \+ *theorem* many_one_equiv.trans
- \+ *def* many_one_equiv
- \+ *theorem* many_one_equiv_refl
- \+ *def* many_one_equiv_setoid
- \+ *theorem* many_one_reducible.mk
- \+ *theorem* many_one_reducible.trans
- \+ *def* many_one_reducible
- \+ *theorem* many_one_reducible_refl
- \+ *theorem* one_one_equiv.congr_left
- \+ *theorem* one_one_equiv.congr_right
- \+ *theorem* one_one_equiv.le_congr_left
- \+ *theorem* one_one_equiv.le_congr_right
- \+ *theorem* one_one_equiv.of_equiv
- \+ *theorem* one_one_equiv.symm
- \+ *theorem* one_one_equiv.to_many_one
- \+ *theorem* one_one_equiv.trans
- \+ *def* one_one_equiv
- \+ *theorem* one_one_equiv_refl
- \+ *theorem* one_one_reducible.disjoin_left
- \+ *theorem* one_one_reducible.disjoin_right
- \+ *theorem* one_one_reducible.mk
- \+ *theorem* one_one_reducible.of_equiv
- \+ *theorem* one_one_reducible.of_equiv_symm
- \+ *theorem* one_one_reducible.to_many_one
- \+ *theorem* one_one_reducible.trans
- \+ *def* one_one_reducible
- \+ *theorem* one_one_reducible_refl
- \+ *theorem* reflexive_many_one_reducible
- \+ *theorem* reflexive_one_one_reducible
- \+ *theorem* transitive_many_one_reducible
- \+ *theorem* transitive_one_one_reducible



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
- \+/\- *lemma* deriv_add
- \+/\- *lemma* deriv_div
- \+ *lemma* deriv_id''
- \+ *lemma* deriv_inv'
- \+/\- *lemma* deriv_mul
- \+ *lemma* deriv_pow''
- \+/\- *lemma* deriv_sub
- \+ *lemma* deriv_within_inv'
- \+ *lemma* deriv_within_pow'
- \+/\- *lemma* differentiable.div
- \+ *lemma* differentiable.inv
- \+ *lemma* differentiable.pow
- \+/\- *lemma* differentiable_at.div
- \+ *lemma* differentiable_at.inv
- \+ *lemma* differentiable_at.pow
- \+ *lemma* differentiable_on.inv
- \+ *lemma* differentiable_on.pow
- \+ *lemma* differentiable_within_at.inv
- \+ *lemma* differentiable_within_at.pow
- \+ *lemma* has_deriv_at.inv
- \+ *lemma* has_deriv_at.pow
- \+ *theorem* has_deriv_at_id'
- \+ *lemma* has_deriv_within_at.inv
- \+ *lemma* has_deriv_within_at.pow

Modified src/analysis/calculus/fderiv.lean
- \+/\- *lemma* differentiable.add
- \+/\- *lemma* differentiable.fst
- \+/\- *lemma* differentiable.mul
- \+/\- *lemma* differentiable.neg
- \+/\- *lemma* differentiable.smul
- \+/\- *lemma* differentiable.snd
- \+/\- *lemma* differentiable.sub
- \+/\- *lemma* differentiable_at.add
- \+/\- *lemma* differentiable_at.fst
- \+/\- *lemma* differentiable_at.mul
- \+/\- *lemma* differentiable_at.neg
- \+/\- *theorem* differentiable_at.prod_map
- \+/\- *lemma* differentiable_at.smul
- \+/\- *lemma* differentiable_at.snd
- \+/\- *lemma* differentiable_at.sub
- \+/\- *lemma* differentiable_at_const
- \+ *lemma* differentiable_at_id'
- \+/\- *lemma* differentiable_at_id
- \+/\- *lemma* differentiable_const
- \+ *lemma* differentiable_id'
- \+/\- *lemma* differentiable_id

Modified src/analysis/complex/exponential.lean
- \+ *lemma* complex.differentiable_at_cos
- \+ *lemma* complex.differentiable_at_cosh
- \+ *lemma* complex.differentiable_at_exp
- \+ *lemma* complex.differentiable_at_sin
- \+ *lemma* complex.differentiable_at_sinh
- \+ *lemma* deriv_ccos
- \+ *lemma* deriv_ccosh
- \+ *lemma* deriv_cexp
- \+ *lemma* deriv_cos
- \+ *lemma* deriv_cosh
- \+ *lemma* deriv_csin
- \+ *lemma* deriv_csinh
- \+ *lemma* deriv_exp
- \+ *lemma* deriv_sin
- \+ *lemma* deriv_sinh
- \+ *lemma* deriv_within_ccos
- \+ *lemma* deriv_within_ccosh
- \+ *lemma* deriv_within_cexp
- \+ *lemma* deriv_within_cos
- \+ *lemma* deriv_within_cosh
- \+ *lemma* deriv_within_csin
- \+ *lemma* deriv_within_csinh
- \+ *lemma* deriv_within_exp
- \+ *lemma* deriv_within_sin
- \+ *lemma* deriv_within_sinh
- \+ *lemma* differentiable.ccos
- \+ *lemma* differentiable.ccosh
- \+ *lemma* differentiable.cexp
- \+ *lemma* differentiable.cos
- \+ *lemma* differentiable.cosh
- \+ *lemma* differentiable.csin
- \+ *lemma* differentiable.csinh
- \+ *lemma* differentiable.exp
- \+ *lemma* differentiable.sin
- \+ *lemma* differentiable.sinh
- \+ *lemma* differentiable_at.ccos
- \+ *lemma* differentiable_at.ccosh
- \+ *lemma* differentiable_at.cexp
- \+ *lemma* differentiable_at.cos
- \+ *lemma* differentiable_at.cosh
- \+ *lemma* differentiable_at.csin
- \+ *lemma* differentiable_at.csinh
- \+ *lemma* differentiable_at.exp
- \+ *lemma* differentiable_at.sin
- \+ *lemma* differentiable_at.sinh
- \+ *lemma* differentiable_on.ccos
- \+ *lemma* differentiable_on.ccosh
- \+ *lemma* differentiable_on.cexp
- \+ *lemma* differentiable_on.cos
- \+ *lemma* differentiable_on.cosh
- \+ *lemma* differentiable_on.csin
- \+ *lemma* differentiable_on.csinh
- \+ *lemma* differentiable_on.exp
- \+ *lemma* differentiable_on.sin
- \+ *lemma* differentiable_on.sinh
- \+ *lemma* differentiable_within_at.ccos
- \+ *lemma* differentiable_within_at.ccosh
- \+ *lemma* differentiable_within_at.cexp
- \+ *lemma* differentiable_within_at.cos
- \+ *lemma* differentiable_within_at.cosh
- \+ *lemma* differentiable_within_at.csin
- \+ *lemma* differentiable_within_at.csinh
- \+ *lemma* differentiable_within_at.exp
- \+ *lemma* differentiable_within_at.sin
- \+ *lemma* differentiable_within_at.sinh
- \+ *lemma* has_deriv_at.ccos
- \+ *lemma* has_deriv_at.ccosh
- \+/\- *lemma* has_deriv_at.cexp
- \+ *lemma* has_deriv_at.cos
- \+ *lemma* has_deriv_at.cosh
- \+ *lemma* has_deriv_at.csin
- \+ *lemma* has_deriv_at.csinh
- \+ *lemma* has_deriv_at.exp
- \+ *lemma* has_deriv_at.sin
- \+ *lemma* has_deriv_at.sinh
- \+ *lemma* has_deriv_within_at.ccos
- \+ *lemma* has_deriv_within_at.ccosh
- \+/\- *lemma* has_deriv_within_at.cexp
- \+ *lemma* has_deriv_within_at.cos
- \+ *lemma* has_deriv_within_at.cosh
- \+ *lemma* has_deriv_within_at.csin
- \+ *lemma* has_deriv_within_at.csinh
- \+ *lemma* has_deriv_within_at.exp
- \+ *lemma* has_deriv_within_at.sin
- \+ *lemma* has_deriv_within_at.sinh
- \+ *lemma* real.differentiable_at_cos
- \+ *lemma* real.differentiable_at_cosh
- \+ *lemma* real.differentiable_at_exp
- \+ *lemma* real.differentiable_at_sin
- \+ *lemma* real.differentiable_at_sinh

Modified src/analysis/convex/specific_functions.lean


Added test/differentiable.lean




## [2020-04-16 11:10:08](https://github.com/leanprover-community/mathlib/commit/ec80061)
refactor(analysis/asymptotics): make is_o irreducible ([#2416](https://github.com/leanprover-community/mathlib/pull/2416))
`is_o` is currently not irreducible. Since it is a complicated type, Lean can have trouble checking if two types with `is_o` are defeq or not, leading to timeouts as described in https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/undergraduate.20calculus/near/193776607
This PR makes `is_o` irreducible.
#### Estimated changes
Modified src/analysis/asymptotics.lean
- \+ *lemma* asymptotics.is_O.of_bound
- \+ *lemma* asymptotics.is_O_iff
- \+ *lemma* asymptotics.is_O_iff_is_O_with
- \+ *lemma* asymptotics.is_O_with.of_bound
- \+ *lemma* asymptotics.is_O_with_iff
- \+ *lemma* asymptotics.is_o.def
- \+ *lemma* asymptotics.is_o_iff
- \+ *lemma* asymptotics.is_o_iff_forall_is_O_with

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
- \+/\- *theorem* nat.cast_eq_zero
- \+/\- *theorem* nat.cast_inj
- \+/\- *theorem* nat.cast_ne_zero

Modified src/algebra/continued_fractions/basic.lean


Modified src/algebra/field_power.lean
- \+/\- *theorem* rat.cast_fpow

Modified src/algebra/group_power.lean
- \+/\- *theorem* int.cast_pow
- \+/\- *theorem* int.coe_nat_pow
- \+/\- *theorem* nat.cast_pow

Modified src/algebra/module.lean
- \+/\- *lemma* submodule.coe_add
- \+/\- *lemma* submodule.coe_mk
- \+/\- *lemma* submodule.coe_neg
- \+/\- *lemma* submodule.coe_smul
- \+/\- *lemma* submodule.coe_sub
- \+/\- *lemma* submodule.coe_zero

Modified src/algebra/ring.lean
- \+ *lemma* coe_add_monoid_hom'
- \+/\- *lemma* coe_add_monoid_hom
- \+ *lemma* coe_monoid_hom'
- \+/\- *lemma* coe_monoid_hom

Modified src/analysis/complex/exponential.lean
- \+/\- *lemma* nnreal.coe_rpow

Modified src/analysis/convex/cone.lean
- \+/\- *lemma* convex_cone.mem_coe

Modified src/analysis/normed_space/basic.lean
- \+/\- *lemma* int.norm_cast_rat
- \+/\- *lemma* int.norm_cast_real
- \+/\- *lemma* rat.norm_cast_real

Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *lemma* continuous_linear_map.restrict_scalars_coe_eq_coe'
- \+/\- *lemma* continuous_linear_map.restrict_scalars_coe_eq_coe
- \+/\- *lemma* linear_map.mk_continuous_coe
- \+/\- *lemma* linear_map.mk_continuous_of_exists_bound_coe

Modified src/data/complex/basic.lean
- \+/\- *lemma* complex.abs_cast_nat
- \+/\- *lemma* complex.int_cast_im
- \+/\- *lemma* complex.int_cast_re
- \+/\- *lemma* complex.nat_cast_im
- \+/\- *lemma* complex.nat_cast_re
- \+/\- *lemma* complex.of_real_add
- \+/\- *lemma* complex.of_real_bit0
- \+/\- *lemma* complex.of_real_bit1
- \+/\- *lemma* complex.of_real_div
- \+/\- *lemma* complex.of_real_fpow
- \+/\- *lemma* complex.of_real_im
- \+/\- *theorem* complex.of_real_inj
- \+/\- *theorem* complex.of_real_int_cast
- \+/\- *lemma* complex.of_real_inv
- \+/\- *lemma* complex.of_real_mul
- \+/\- *theorem* complex.of_real_nat_cast
- \+/\- *lemma* complex.of_real_neg
- \+/\- *lemma* complex.of_real_one
- \+/\- *lemma* complex.of_real_pow
- \+/\- *theorem* complex.of_real_rat_cast
- \+/\- *lemma* complex.of_real_re
- \+/\- *lemma* complex.of_real_sub
- \+/\- *lemma* complex.of_real_zero
- \+/\- *lemma* complex.rat_cast_im
- \+/\- *lemma* complex.rat_cast_re

Modified src/data/equiv/ring.lean
- \+/\- *lemma* ring_equiv.coe_add_equiv
- \+/\- *lemma* ring_equiv.coe_mul_equiv

Modified src/data/fin.lean
- \+/\- *lemma* fin.coe_last
- \+/\- *lemma* fin.coe_mk

Modified src/data/finset.lean
- \+/\- *lemma* finset.coe_nonempty
- \+/\- *lemma* finset.piecewise_coe

Modified src/data/int/basic.lean
- \+/\- *lemma* int.bodd_coe
- \+/\- *theorem* int.cast_abs
- \+/\- *theorem* int.cast_add
- \+/\- *theorem* int.cast_bit0
- \+/\- *theorem* int.cast_bit1
- \+/\- *theorem* int.cast_coe_nat
- \+/\- *theorem* int.cast_id
- \+/\- *theorem* int.cast_inj
- \+/\- *theorem* int.cast_le
- \+/\- *theorem* int.cast_lt
- \+/\- *theorem* int.cast_max
- \+/\- *theorem* int.cast_min
- \+/\- *theorem* int.cast_mul
- \+/\- *theorem* int.cast_neg
- \+/\- *theorem* int.cast_neg_of_nat
- \+/\- *theorem* int.cast_neg_succ_of_nat
- \+/\- *theorem* int.cast_one
- \+/\- *theorem* int.cast_sub
- \+/\- *theorem* int.cast_sub_nat_nat
- \+/\- *theorem* int.cast_zero
- \+/\- *theorem* int.coe_nat_abs
- \+/\- *theorem* int.coe_nat_bit0
- \+/\- *theorem* int.coe_nat_bit1
- \+/\- *theorem* int.coe_nat_div
- \+/\- *theorem* int.coe_nat_dvd
- \+/\- *theorem* int.coe_nat_inj'
- \+/\- *theorem* int.coe_nat_le
- \+/\- *theorem* int.coe_nat_lt

Modified src/data/nat/cast.lean
- \+/\- *theorem* nat.abs_cast
- \+/\- *theorem* nat.cast_add
- \+/\- *theorem* nat.cast_bit0
- \+/\- *theorem* nat.cast_bit1
- \+/\- *theorem* nat.cast_id
- \+/\- *theorem* nat.cast_ite
- \+/\- *theorem* nat.cast_le
- \+/\- *theorem* nat.cast_lt
- \+/\- *theorem* nat.cast_max
- \+/\- *theorem* nat.cast_min
- \+/\- *theorem* nat.cast_mul
- \+/\- *theorem* nat.cast_one
- \+/\- *theorem* nat.cast_pred
- \+/\- *theorem* nat.cast_sub
- \+/\- *theorem* nat.cast_succ
- \+/\- *theorem* nat.cast_zero

Modified src/data/nat/enat.lean
- \+/\- *lemma* enat.coe_add
- \+/\- *lemma* enat.coe_get
- \+/\- *lemma* enat.coe_le_coe
- \+/\- *lemma* enat.coe_lt_coe
- \+/\- *lemma* enat.coe_one
- \+/\- *lemma* enat.coe_zero
- \+/\- *lemma* enat.get_coe

Modified src/data/nat/multiplicity.lean


Modified src/data/num/basic.lean
- \- *def* int.of_snum
- \- *def* nzsnum.bit0
- \- *def* nzsnum.bit1
- \- *def* nzsnum.drec'
- \- *def* nzsnum.head
- \- *def* nzsnum.not
- \- *def* nzsnum.sign
- \- *def* nzsnum.tail
- \- *def* snum.bit0
- \- *def* snum.bit1
- \- *def* snum.bit
- \- *theorem* snum.bit_one
- \- *theorem* snum.bit_zero
- \- *def* snum.bits
- \- *def* snum.cadd
- \- *def* snum.czadd
- \- *def* snum.drec'
- \- *def* snum.head
- \- *def* snum.not
- \- *def* snum.pred
- \- *def* snum.rec'
- \- *def* snum.sign
- \- *def* snum.succ
- \- *def* snum.tail
- \- *def* snum.test_bit

Modified src/data/num/bitwise.lean
- \+ *def* nzsnum.bit0
- \+ *def* nzsnum.bit1
- \+ *def* nzsnum.drec'
- \+ *def* nzsnum.head
- \+ *def* nzsnum.not
- \+ *def* nzsnum.sign
- \+ *def* nzsnum.tail
- \+ *def* snum.bit0
- \+ *def* snum.bit1
- \+ *def* snum.bit
- \+ *theorem* snum.bit_one
- \+ *theorem* snum.bit_zero
- \+ *def* snum.bits
- \+ *def* snum.cadd
- \+ *def* snum.czadd
- \+ *def* snum.drec'
- \+ *def* snum.head
- \+ *def* snum.not
- \+ *def* snum.pred
- \+ *def* snum.rec'
- \+ *def* snum.sign
- \+ *def* snum.succ
- \+ *def* snum.tail
- \+ *def* snum.test_bit

Modified src/data/num/lemmas.lean
- \+ *def* int.of_snum
- \+/\- *theorem* num.add_of_nat
- \+/\- *theorem* num.cast_add
- \+/\- *theorem* num.cast_bit0
- \+/\- *theorem* num.cast_bit1
- \+/\- *theorem* num.cast_mul
- \+/\- *theorem* num.cast_one
- \+/\- *theorem* num.cast_to_int
- \+/\- *theorem* num.cast_to_nat
- \+/\- *theorem* num.cast_to_znum
- \+/\- *theorem* num.cast_zero
- \+/\- *theorem* num.div_to_nat
- \+/\- *theorem* num.land_to_nat
- \+/\- *theorem* num.ldiff_to_nat
- \+/\- *theorem* num.lor_to_nat
- \+/\- *theorem* num.lxor_to_nat
- \+/\- *theorem* num.mod_to_nat
- \+/\- *theorem* num.of_nat_inj
- \+/\- *theorem* num.of_to_nat
- \+/\- *theorem* num.shiftl_to_nat
- \+/\- *theorem* num.shiftr_to_nat
- \+/\- *theorem* num.sub_to_nat
- \+/\- *theorem* num.to_nat_inj
- \+/\- *theorem* num.to_nat_to_int
- \+/\- *theorem* pos_num.cast_bit0
- \+/\- *theorem* pos_num.cast_bit1
- \+/\- *theorem* pos_num.cast_one
- \+/\- *theorem* pos_num.cast_to_int
- \+/\- *theorem* pos_num.cast_to_nat
- \+/\- *theorem* pos_num.to_nat_inj
- \+/\- *theorem* pos_num.to_nat_to_int
- \+/\- *theorem* znum.cast_add
- \+/\- *theorem* znum.cast_bit0
- \+/\- *theorem* znum.cast_bit1
- \+/\- *theorem* znum.cast_one
- \+/\- *theorem* znum.cast_to_int
- \+/\- *theorem* znum.cast_zero
- \+/\- *theorem* znum.cast_zneg
- \+/\- *theorem* znum.div_to_int
- \+/\- *theorem* znum.dvd_to_int
- \+/\- *theorem* znum.mod_to_int
- \+/\- *theorem* znum.mul_to_int
- \+/\- *theorem* znum.neg_of_int
- \+/\- *theorem* znum.of_int_cast
- \+/\- *theorem* znum.of_nat_cast
- \+/\- *theorem* znum.of_to_int

Modified src/data/padics/padic_integers.lean
- \+/\- *lemma* padic_int.cast_pow
- \+/\- *lemma* padic_int.coe_add
- \+/\- *lemma* padic_int.coe_coe
- \+/\- *lemma* padic_int.coe_mul
- \+/\- *lemma* padic_int.coe_neg
- \+/\- *lemma* padic_int.coe_one
- \+/\- *lemma* padic_int.coe_sub
- \+/\- *lemma* padic_int.coe_zero

Modified src/data/padics/padic_norm.lean


Modified src/data/padics/padic_numbers.lean
- \+/\- *lemma* padic.coe_add
- \+/\- *lemma* padic.coe_div
- \+/\- *lemma* padic.coe_inj
- \+/\- *lemma* padic.coe_mul
- \+/\- *lemma* padic.coe_neg
- \+/\- *lemma* padic.coe_one
- \+/\- *lemma* padic.coe_sub
- \+/\- *lemma* padic.coe_zero

Modified src/data/rat/basic.lean
- \+/\- *theorem* rat.coe_int_denom
- \+/\- *theorem* rat.coe_int_num
- \+/\- *theorem* rat.coe_nat_denom
- \+/\- *theorem* rat.coe_nat_num

Modified src/data/rat/cast.lean
- \+/\- *theorem* rat.cast_abs
- \+/\- *theorem* rat.cast_add
- \+/\- *theorem* rat.cast_add_of_ne_zero
- \+/\- *theorem* rat.cast_bit0
- \+/\- *theorem* rat.cast_bit1
- \+/\- *theorem* rat.cast_coe_int
- \+/\- *theorem* rat.cast_coe_nat
- \+/\- *theorem* rat.cast_div
- \+/\- *theorem* rat.cast_div_of_ne_zero
- \+/\- *theorem* rat.cast_id
- \+/\- *theorem* rat.cast_inj
- \+/\- *theorem* rat.cast_inv
- \+/\- *theorem* rat.cast_inv_of_ne_zero
- \+/\- *theorem* rat.cast_le
- \+/\- *theorem* rat.cast_lt
- \+/\- *theorem* rat.cast_max
- \+/\- *theorem* rat.cast_min
- \+/\- *theorem* rat.cast_mk
- \+/\- *theorem* rat.cast_mk_of_ne_zero
- \+/\- *theorem* rat.cast_mul
- \+/\- *theorem* rat.cast_mul_of_ne_zero
- \+/\- *theorem* rat.cast_neg
- \+/\- *theorem* rat.cast_nonneg
- \+/\- *theorem* rat.cast_one
- \+/\- *theorem* rat.cast_pow
- \+/\- *theorem* rat.cast_sub
- \+/\- *theorem* rat.cast_sub_of_ne_zero
- \+/\- *theorem* rat.cast_zero

Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.coe_add
- \+/\- *lemma* ennreal.coe_bit0
- \+/\- *lemma* ennreal.coe_bit1
- \+/\- *lemma* ennreal.coe_div
- \+/\- *lemma* ennreal.coe_eq_coe
- \+/\- *lemma* ennreal.coe_eq_one
- \+/\- *lemma* ennreal.coe_eq_zero
- \+/\- *lemma* ennreal.coe_finset_prod
- \+/\- *lemma* ennreal.coe_finset_sum
- \+/\- *lemma* ennreal.coe_inv
- \+/\- *lemma* ennreal.coe_inv_two
- \+/\- *lemma* ennreal.coe_le_coe
- \+/\- *lemma* ennreal.coe_le_one_iff
- \+/\- *lemma* ennreal.coe_lt_coe
- \+/\- *lemma* ennreal.coe_lt_one_iff
- \+/\- *lemma* ennreal.coe_max
- \+/\- *lemma* ennreal.coe_min
- \+/\- *lemma* ennreal.coe_mul
- \+/\- *lemma* ennreal.coe_nat
- \+/\- *lemma* ennreal.coe_nat_le_coe_nat
- \+/\- *lemma* ennreal.coe_nat_lt_coe_nat
- \+/\- *lemma* ennreal.coe_nonneg
- \+/\- *lemma* ennreal.coe_one
- \+/\- *lemma* ennreal.coe_pos
- \+/\- *lemma* ennreal.coe_pow
- \+/\- *lemma* ennreal.coe_sub
- \+/\- *lemma* ennreal.coe_zero
- \+/\- *lemma* ennreal.one_eq_coe
- \+/\- *lemma* ennreal.one_le_coe_iff
- \+/\- *lemma* ennreal.one_lt_coe_iff
- \+/\- *lemma* ennreal.to_nnreal_coe
- \+/\- *lemma* ennreal.zero_eq_coe

Modified src/data/real/ereal.lean


Modified src/data/real/hyperreal.lean


Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.coe_list_prod
- \+/\- *lemma* nnreal.coe_list_sum
- \+/\- *lemma* nnreal.coe_max
- \+/\- *lemma* nnreal.coe_min
- \+/\- *lemma* nnreal.coe_multiset_prod
- \+/\- *lemma* nnreal.coe_multiset_sum
- \+/\- *lemma* nnreal.coe_ne_zero
- \+/\- *lemma* nnreal.coe_pow
- \+/\- *lemma* nnreal.coe_prod
- \+/\- *lemma* nnreal.coe_sum
- \+/\- *lemma* nnreal.smul_coe

Modified src/group_theory/submonoid.lean


Modified src/linear_algebra/basic.lean
- \+/\- *lemma* linear_equiv.coe_prod

Modified src/measure_theory/bochner_integration.lean
- \+/\- *lemma* measure_theory.l1.simple_func.coe_add
- \+/\- *lemma* measure_theory.l1.simple_func.coe_neg
- \+/\- *lemma* measure_theory.l1.simple_func.coe_neg_part
- \+/\- *lemma* measure_theory.l1.simple_func.coe_pos_part
- \+/\- *lemma* measure_theory.l1.simple_func.coe_smul
- \+/\- *lemma* measure_theory.l1.simple_func.coe_sub
- \+/\- *lemma* measure_theory.l1.simple_func.coe_zero
- \+/\- *lemma* measure_theory.l1.simple_func.integral_eq_integral

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* measure_theory.l1.coe_add
- \+/\- *lemma* measure_theory.l1.coe_neg
- \+/\- *lemma* measure_theory.l1.coe_pos_part
- \+/\- *lemma* measure_theory.l1.coe_smul
- \+/\- *lemma* measure_theory.l1.coe_sub
- \+/\- *lemma* measure_theory.l1.coe_zero

Modified src/meta/expr.lean


Modified src/order/filter/filter_product.lean
- \+/\- *lemma* filter.filter_product.of_add
- \+/\- *lemma* filter.filter_product.of_bit0
- \+/\- *lemma* filter.filter_product.of_bit1
- \+/\- *lemma* filter.filter_product.of_div
- \+/\- *lemma* filter.filter_product.of_inv
- \+/\- *lemma* filter.filter_product.of_mul
- \+/\- *lemma* filter.filter_product.of_neg
- \+/\- *lemma* filter.filter_product.of_one
- \+/\- *lemma* filter.filter_product.of_sub
- \+/\- *lemma* filter.filter_product.of_zero

Modified src/ring_theory/algebra.lean
- \+/\- *lemma* linear_map.coe_restrict_scalars_eq_coe

Modified src/ring_theory/free_comm_ring.lean


Modified src/ring_theory/multiplicity.lean


Modified src/ring_theory/power_series.lean
- \+/\- *lemma* mv_polynomial.coe_C
- \+/\- *lemma* mv_polynomial.coe_X
- \+/\- *lemma* mv_polynomial.coe_add
- \+/\- *lemma* mv_polynomial.coe_monomial
- \+/\- *lemma* mv_polynomial.coe_mul
- \+/\- *lemma* mv_polynomial.coe_one
- \+/\- *lemma* mv_polynomial.coe_zero
- \+/\- *lemma* mv_polynomial.coeff_coe
- \+/\- *lemma* polynomial.coe_C
- \+/\- *lemma* polynomial.coe_X
- \+/\- *lemma* polynomial.coe_add
- \+/\- *lemma* polynomial.coe_monomial
- \+/\- *lemma* polynomial.coe_mul
- \+/\- *lemma* polynomial.coe_one
- \+/\- *lemma* polynomial.coe_zero
- \+/\- *lemma* polynomial.coeff_coe

Modified src/set_theory/cardinal.lean
- \+/\- *theorem* cardinal.nat_cast_inj
- \+/\- *theorem* cardinal.nat_cast_le
- \+/\- *theorem* cardinal.nat_cast_lt
- \+/\- *theorem* cardinal.nat_cast_pow
- \+/\- *theorem* cardinal.nat_succ

Modified src/set_theory/ordinal.lean


Modified src/tactic/core.lean


Modified src/tactic/norm_cast.lean
- \- *lemma* ge_from_le
- \- *lemma* gt_from_lt
- \+/\- *lemma* ite_cast
- \- *lemma* ne_from_not_eq
- \+ *def* norm_cast.label.of_string

Modified src/topology/algebra/group_completion.lean
- \+/\- *lemma* uniform_space.completion.coe_zero

Modified src/topology/algebra/module.lean
- \+/\- *lemma* continuous_linear_equiv.coe_coe
- \+/\- *lemma* continuous_linear_equiv.coe_prod
- \+/\- *lemma* continuous_linear_equiv.coe_refl'
- \+/\- *lemma* continuous_linear_equiv.coe_refl
- \+/\- *lemma* continuous_linear_equiv.prod_apply
- \+/\- *lemma* continuous_linear_map.coe_add'
- \+/\- *lemma* continuous_linear_map.coe_add
- \+/\- *lemma* continuous_linear_map.coe_apply'
- \+/\- *lemma* continuous_linear_map.coe_apply
- \+/\- *lemma* continuous_linear_map.coe_coe
- \+/\- *lemma* continuous_linear_map.coe_comp'
- \+/\- *lemma* continuous_linear_map.coe_comp
- \+/\- *lemma* continuous_linear_map.coe_fst'
- \+/\- *lemma* continuous_linear_map.coe_fst
- \+/\- *lemma* continuous_linear_map.coe_id'
- \+/\- *lemma* continuous_linear_map.coe_id
- \+/\- *lemma* continuous_linear_map.coe_neg'
- \+/\- *lemma* continuous_linear_map.coe_neg
- \+/\- *lemma* continuous_linear_map.coe_prod
- \+/\- *lemma* continuous_linear_map.coe_prod_map
- \+/\- *lemma* continuous_linear_map.coe_snd'
- \+/\- *lemma* continuous_linear_map.coe_snd
- \+/\- *lemma* continuous_linear_map.coe_sub'
- \+/\- *lemma* continuous_linear_map.coe_sub
- \+/\- *lemma* continuous_linear_map.coe_zero'
- \+/\- *lemma* continuous_linear_map.coe_zero
- \+/\- *lemma* continuous_linear_map.prod_apply
- \+/\- *lemma* continuous_linear_map.prod_map_apply

Modified src/topology/algebra/uniform_ring.lean
- \+/\- *lemma* uniform_space.completion.coe_one

Modified src/topology/instances/ennreal.lean
- \+/\- *lemma* ennreal.tendsto_coe

Modified src/topology/instances/nnreal.lean
- \+/\- *lemma* nnreal.coe_tsum
- \+/\- *lemma* nnreal.has_sum_coe
- \+/\- *lemma* nnreal.summable_coe

Modified src/topology/instances/real.lean
- \+/\- *theorem* int.dist_cast_rat
- \+/\- *theorem* int.dist_cast_real
- \+/\- *lemma* rat.dist_cast

Modified src/topology/metric_space/basic.lean


Modified test/norm_cast.lean
- \+ *lemma* ennreal.half_lt_self_bis
- \+ *lemma* hidden.coe_inj
- \+ *lemma* hidden.coe_one
- \+ *lemma* hidden.mul_coe
- \+ *def* hidden.with_zero

Added test/norm_cast_cardinal.lean
- \+ *lemma* coe_bit0
- \+ *lemma* coe_bit1

Added test/norm_cast_coe_fn.lean
- \+ *lemma* coe_f1
- \+ *def* f1
- \+ *def* f2
- \+ *lemma* hom_plus.coe_fn

Added test/norm_cast_int.lean


Added test/norm_cast_lemma_order.lean


Added test/norm_cast_sum_lambda.lean




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
Added src/category_theory/connected.lean
- \+ *lemma* category_theory.any_functor_const_on_obj
- \+ *def* category_theory.connected.of_any_functor_const_on_obj
- \+ *def* category_theory.connected.of_constant_of_preserves_morphisms
- \+ *def* category_theory.connected.of_induct
- \+ *def* category_theory.connected_of_zigzag
- \+ *lemma* category_theory.connected_zigzag
- \+ *lemma* category_theory.constant_of_preserves_morphisms
- \+ *lemma* category_theory.equiv_relation
- \+ *lemma* category_theory.exists_zigzag'
- \+ *lemma* category_theory.induct_on_objects
- \+ *lemma* category_theory.nat_trans_from_connected
- \+ *def* category_theory.zag
- \+ *def* category_theory.zigzag
- \+ *def* category_theory.zigzag_connected

Added src/category_theory/limits/connected.lean
- \+ *def* category_theory.prod_preserves_connected_limits.forget_cone
- \+ *def* category_theory.prod_preserves_connected_limits.γ₁
- \+ *def* category_theory.prod_preserves_connected_limits.γ₂
- \+ *def* category_theory.prod_preserves_connected_limits

Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *def* category_theory.limits.prod_functor

Modified src/data/list/chain.lean
- \+ *lemma* list.chain.induction
- \+ *lemma* list.exists_chain_of_relation_refl_trans_gen

Modified src/data/list/defs.lean




## [2020-04-15 22:29:29](https://github.com/leanprover-community/mathlib/commit/66cc298)
feat(data/finset): existence of a smaller set ([#2420](https://github.com/leanprover-community/mathlib/pull/2420))
Show the existence of a smaller finset contained in a given finset.
The next in my series of lemmas for my combinatorics project.
#### Estimated changes
Modified src/data/finset.lean
- \+ *lemma* finset.exists_intermediate_set
- \+ *lemma* finset.exists_smaller_set



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
- \+ *def* category_theory.limits.binary_cofan.is_colimit.desc'
- \+ *lemma* category_theory.limits.binary_cofan.is_colimit.hom_ext
- \+ *lemma* category_theory.limits.binary_fan.is_limit.hom_ext
- \+ *def* category_theory.limits.binary_fan.is_limit.lift'
- \+ *def* category_theory.limits.coprod.desc'
- \+/\- *lemma* category_theory.limits.coprod.hom_ext
- \+/\- *lemma* category_theory.limits.coprod.inl_desc
- \+ *lemma* category_theory.limits.coprod.inl_map
- \+/\- *lemma* category_theory.limits.coprod.inr_desc
- \+ *lemma* category_theory.limits.coprod.inr_map
- \+/\- *lemma* category_theory.limits.prod.hom_ext
- \+ *def* category_theory.limits.prod.lift'
- \+/\- *lemma* category_theory.limits.prod.lift_fst
- \+/\- *lemma* category_theory.limits.prod.lift_snd
- \+ *lemma* category_theory.limits.prod.map_fst
- \+ *lemma* category_theory.limits.prod.map_snd

Modified src/category_theory/limits/shapes/constructions/pullbacks.lean


Modified src/category_theory/limits/shapes/equalizers.lean
- \- *lemma* category_theory.limits.cocone_parallel_pair_ext
- \- *lemma* category_theory.limits.cocone_parallel_pair_left
- \- *lemma* category_theory.limits.cocone_parallel_pair_right
- \+ *def* category_theory.limits.coequalizer.desc'
- \+ *lemma* category_theory.limits.coequalizer.π_desc
- \+ *lemma* category_theory.limits.cofork.coequalizer_ext
- \+ *def* category_theory.limits.cofork.is_colimit.desc'
- \+ *lemma* category_theory.limits.cofork.is_colimit.hom_ext
- \+ *lemma* category_theory.limits.cofork.left_app_one
- \+ *lemma* category_theory.limits.cofork.right_app_one
- \- *def* category_theory.limits.cofork.π
- \- *lemma* category_theory.limits.cone_parallel_pair_ext
- \- *lemma* category_theory.limits.cone_parallel_pair_left
- \- *lemma* category_theory.limits.cone_parallel_pair_right
- \+/\- *lemma* category_theory.limits.epi_of_is_colimit_parallel_pair
- \+ *def* category_theory.limits.equalizer.lift'
- \+ *lemma* category_theory.limits.equalizer.lift_ι
- \+ *lemma* category_theory.limits.fork.app_zero_left
- \+ *lemma* category_theory.limits.fork.app_zero_right
- \+ *lemma* category_theory.limits.fork.equalizer_ext
- \+ *lemma* category_theory.limits.fork.is_limit.hom_ext
- \+ *def* category_theory.limits.fork.is_limit.lift'
- \- *def* category_theory.limits.fork.ι
- \+/\- *lemma* category_theory.limits.mono_of_is_limit_parallel_pair

Modified src/category_theory/limits/shapes/kernels.lean
- \+ *def* category_theory.limits.cokernel.desc'
- \+ *lemma* category_theory.limits.cokernel.π_desc
- \+ *def* category_theory.limits.cokernel_cofork.is_limit.desc'
- \+ *def* category_theory.limits.kernel.lift'
- \+ *lemma* category_theory.limits.kernel.lift_ι
- \+ *def* category_theory.limits.kernel_fork.is_limit.lift'

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.pullback.desc'
- \+ *def* category_theory.limits.pullback.lift'
- \+ *lemma* category_theory.limits.pullback.lift_fst
- \+ *lemma* category_theory.limits.pullback.lift_snd
- \+ *lemma* category_theory.limits.pullback_cone.is_limit.hom_ext
- \+ *def* category_theory.limits.pullback_cone.is_limit.lift'
- \+ *lemma* category_theory.limits.pushout.inl_desc
- \+ *lemma* category_theory.limits.pushout.inr_desc
- \+ *def* category_theory.limits.pushout_cocone.is_colimit.desc'
- \+ *lemma* category_theory.limits.pushout_cocone.is_colimit.hom_ext



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


Added src/category_theory/limits/concrete_category.lean
- \+ *lemma* category_theory.limits.cocone.naturality_concrete
- \+ *lemma* category_theory.limits.cone.naturality_concrete

Modified src/category_theory/limits/cones.lean
- \- *lemma* category_theory.limits.cocone.naturality_concrete
- \- *lemma* category_theory.limits.cone.naturality_concrete



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
- \+ *lemma* deriv.scomp
- \+ *lemma* deriv_within.scomp
- \+ *theorem* has_deriv_at.scomp
- \+ *theorem* has_deriv_at.scomp_has_deriv_within_at
- \+ *theorem* has_deriv_at_filter.scomp
- \+ *theorem* has_deriv_within_at.scomp

Modified src/analysis/complex/exponential.lean




## [2020-04-14 11:02:02](https://github.com/leanprover-community/mathlib/commit/15fcb8a)
feat(algebra/lie_algebra): define equivalences, direct sums of Lie algebras ([#2404](https://github.com/leanprover-community/mathlib/pull/2404))
This pull request does two things:
1. Defines equivalences of Lie algebras (and proves that these do indeed form an equivalence relation)
2. Defines direct sums of Lie algebras
The intention is to knock another chip off https://github.com/leanprover-community/mathlib/issues/1093
#### Estimated changes
Modified src/algebra/lie_algebra.lean
- \+ *lemma* lie_algebra.direct_sum.bracket_apply
- \+ *def* lie_algebra.equiv.refl
- \+ *def* lie_algebra.equiv.symm
- \+ *def* lie_algebra.equiv.trans
- \+/\- *lemma* lie_algebra.map_lie'
- \+/\- *lemma* lie_algebra.map_lie
- \+ *def* lie_algebra.morphism.comp
- \+ *lemma* lie_algebra.morphism.comp_apply
- \+ *def* lie_algebra.morphism.inverse



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
- \+ *def* formal_multilinear_series.change_origin_summable_aux_j
- \+ *lemma* formal_multilinear_series.change_origin_summable_aux_j_inj

Modified src/analysis/complex/basic.lean
- \+ *lemma* has_deriv_at_real_of_complex_aux



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
- \+ *lemma* finset.prod_flip
- \+ *lemma* finset.sum_const_nat
- \+ *lemma* finset.sum_div
- \+ *lemma* finset.sum_flip
- \+ *lemma* finset.sum_lt_sum_of_nonempty



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
- \+ *lemma* finset.bind_subset_bind_of_subset_left
- \+ *lemma* finset.disjoint_sdiff_inter
- \+ *lemma* finset.disjoint_self_iff_empty
- \+ *lemma* finset.exists_max_image
- \- *lemma* finset.exists_min
- \+ *lemma* finset.exists_min_image
- \+ *lemma* finset.inter_eq_inter_of_sdiff_eq_sdiff
- \+ *lemma* finset.inter_union_self
- \+ *lemma* finset.min'_lt_max'_of_card
- \+ *lemma* finset.not_mem_sdiff_of_mem_right
- \+ *lemma* finset.sdiff_eq_self_iff_disjoint
- \+ *lemma* finset.sdiff_eq_self_of_disjoint
- \+ *lemma* finset.sdiff_idem
- \+ *lemma* finset.sdiff_sdiff_self_left
- \+ *lemma* finset.sdiff_singleton_eq_erase
- \+ *lemma* finset.sdiff_union_distrib
- \+ *lemma* finset.sdiff_union_inter
- \+ *lemma* finset.union_eq_empty_iff
- \+ *lemma* finset.union_sdiff_distrib
- \+ *lemma* finset.union_sdiff_self

Modified src/data/set/finite.lean
- \+ *lemma* set.exists_max_image
- \- *lemma* set.exists_min
- \+ *lemma* set.exists_min_image



## [2020-04-13 14:53:40](https://github.com/leanprover-community/mathlib/commit/f3ac7b7)
feat(combinatorics/composition): introduce compositions of an integer ([#2398](https://github.com/leanprover-community/mathlib/pull/2398))
A composition of an integer `n` is a decomposition of `{0, ..., n-1}` into blocks of consecutive
integers. Equivalently, it is a decomposition `n = i₀ + ... + i_{k-1}` into a sum of positive
integers. We define compositions in this PR, and introduce a whole interface around it. The goal is to use this as a tool in the proof that the composition of analytic functions is analytic
#### Estimated changes
Modified src/algebra/group/basic.lean


Added src/combinatorics/composition.lean
- \+ *def* composition.blocks
- \+ *def* composition.blocks_fun
- \+ *lemma* composition.blocks_length
- \+ *lemma* composition.blocks_pnat_length
- \+ *lemma* composition.blocks_pos'
- \+ *lemma* composition.blocks_pos
- \+ *lemma* composition.blocks_sum
- \+ *def* composition.boundaries
- \+ *def* composition.boundary
- \+ *lemma* composition.boundary_last
- \+ *lemma* composition.boundary_zero
- \+ *lemma* composition.card_boundaries_eq_succ_length
- \+ *lemma* composition.disjoint_range
- \+ *def* composition.embedding
- \+ *lemma* composition.embedding_comp_inv
- \+ *lemma* composition.embedding_inj
- \+ *def* composition.index
- \+ *lemma* composition.index_exists
- \+ *def* composition.inv_embedding
- \+ *def* composition.length
- \+ *lemma* composition.length_le
- \+ *lemma* composition.length_pos_of_pos
- \+ *lemma* composition.lt_size_up_to_index_succ
- \+ *lemma* composition.mem_range_embedding
- \+ *lemma* composition.mem_range_embedding_iff'
- \+ *lemma* composition.mem_range_embedding_iff
- \+ *lemma* composition.mono_of_fin_boundaries
- \+ *lemma* composition.one_le_blocks'
- \+ *lemma* composition.one_le_blocks
- \+ *lemma* composition.sigma_eq_iff_blocks_eq
- \+ *lemma* composition.sigma_eq_iff_blocks_pnat_eq
- \+ *def* composition.size_up_to
- \+ *lemma* composition.size_up_to_index_le
- \+ *lemma* composition.size_up_to_le
- \+ *lemma* composition.size_up_to_length
- \+ *lemma* composition.size_up_to_of_length_le
- \+ *lemma* composition.size_up_to_strict_mono
- \+ *lemma* composition.size_up_to_succ'
- \+ *lemma* composition.size_up_to_succ
- \+ *lemma* composition.size_up_to_zero
- \+ *lemma* composition.strict_mono_boundary
- \+ *lemma* composition.sum_blocks_fun
- \+ *def* composition.to_composition_as_set
- \+ *lemma* composition.to_composition_as_set_blocks
- \+ *lemma* composition.to_composition_as_set_blocks_pnat
- \+ *lemma* composition.to_composition_as_set_boundaries
- \+ *lemma* composition.to_composition_as_set_length
- \+ *def* composition_as_set.blocks
- \+ *def* composition_as_set.blocks_fun
- \+ *lemma* composition_as_set.blocks_fun_pos
- \+ *lemma* composition_as_set.blocks_length
- \+ *lemma* composition_as_set.blocks_partial_sum
- \+ *def* composition_as_set.blocks_pnat
- \+ *lemma* composition_as_set.blocks_pnat_length
- \+ *lemma* composition_as_set.blocks_sum
- \+ *lemma* composition_as_set.boundaries_nonempty
- \+ *def* composition_as_set.boundary
- \+ *lemma* composition_as_set.boundary_length
- \+ *lemma* composition_as_set.boundary_zero
- \+ *lemma* composition_as_set.card_boundaries_eq_succ_length
- \+ *lemma* composition_as_set.card_boundaries_pos
- \+ *lemma* composition_as_set.coe_blocks_pnat_eq_blocks
- \+ *def* composition_as_set.length
- \+ *lemma* composition_as_set.length_lt_card_boundaries
- \+ *lemma* composition_as_set.lt_length'
- \+ *lemma* composition_as_set.lt_length
- \+ *lemma* composition_as_set.mem_boundaries_iff_exists_blocks_sum_take_eq
- \+ *def* composition_as_set.to_composition
- \+ *lemma* composition_as_set.to_composition_blocks
- \+ *lemma* composition_as_set.to_composition_blocks_pnat
- \+ *lemma* composition_as_set.to_composition_boundaries
- \+ *lemma* composition_as_set.to_composition_length
- \+ *lemma* composition_as_set_card
- \+ *def* composition_as_set_equiv
- \+ *lemma* composition_card
- \+ *def* composition_equiv

Modified src/data/fin.lean
- \+ *lemma* fin.coe_last
- \+/\- *lemma* fin.coe_mk
- \+ *lemma* fin.strict_mono_iff_lt_succ

Modified src/data/finset.lean
- \- *lemma* finset.bij_on_mono_of_fin
- \+ *lemma* finset.mono_of_fin_bij_on
- \+ *lemma* finset.mono_of_fin_eq_mono_of_fin_iff
- \+ *lemma* finset.mono_of_fin_injective

Modified src/data/fintype/basic.lean


Modified src/data/fintype/card.lean
- \+ *lemma* list.of_fn_prod
- \+ *lemma* list.of_fn_prod_take
- \+ *lemma* list.of_fn_sum_take

Modified src/data/list/basic.lean
- \+ *lemma* list.eq_of_sum_take_eq
- \+ *lemma* list.length_le_sum_of_one_le
- \+ *lemma* list.monotone_sum_take

Modified src/data/list/of_fn.lean
- \+ *lemma* list.map_of_fn
- \+ *theorem* list.nth_le_of_fn'
- \+/\- *theorem* list.nth_le_of_fn

Modified src/data/set/finite.lean
- \+ *lemma* set.finite_dependent_image



## [2020-04-13 13:52:21](https://github.com/leanprover-community/mathlib/commit/01ac691)
feat(category_theory/limits/shapes/binary_products): add some basic API for prod and coprod ([#2396](https://github.com/leanprover-community/mathlib/pull/2396))
Adding explicit proofs of some basic results about maps into A x B and maps from A coprod B
#### Estimated changes
Modified src/category_theory/limits/shapes/binary_products.lean
- \+ *lemma* category_theory.limits.coprod.hom_ext
- \+ *lemma* category_theory.limits.coprod.inl_desc
- \+ *lemma* category_theory.limits.coprod.inr_desc
- \+ *lemma* category_theory.limits.prod.hom_ext
- \+ *lemma* category_theory.limits.prod.lift_fst
- \+ *lemma* category_theory.limits.prod.lift_snd



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
- \+ *lemma* set.eq_finite_Union_of_finite_subset_Union

Modified src/data/set/lattice.lean
- \+ *lemma* set.directed_on_Union
- \+ *theorem* set.sInter_Union

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/integration.lean


Modified src/measure_theory/set_integral.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* infi_subtype''

Modified src/order/filter/bases.lean
- \+ *lemma* filter.antimono_seq_of_seq
- \+ *lemma* filter.countable_binfi_eq_infi_seq'
- \+ *lemma* filter.countable_binfi_eq_infi_seq
- \+ *lemma* filter.countable_binfi_principal_eq_seq_infi
- \+ *def* filter.filter_basis.of_sets
- \+ *lemma* filter.generate_eq_generate_inter
- \+ *lemma* filter.has_antimono_basis.tendsto
- \+ *lemma* filter.has_basis.eq_generate
- \+ *lemma* filter.has_basis.filter_eq
- \+ *lemma* filter.has_basis.is_basis
- \+ *lemma* filter.has_basis_generate
- \+ *lemma* filter.is_basis.filter_eq_generate
- \+ *lemma* filter.is_basis.mem_filter_basis_iff
- \+ *def* filter.is_countably_generated.countable_filter_basis
- \+ *lemma* filter.is_countably_generated.countable_generating_set
- \+ *lemma* filter.is_countably_generated.eq_generate
- \+ *lemma* filter.is_countably_generated.exists_antimono_seq'
- \+ *lemma* filter.is_countably_generated.exists_antimono_seq
- \+ *lemma* filter.is_countably_generated.exists_countable_infi_principal
- \+ *lemma* filter.is_countably_generated.exists_seq
- \+ *lemma* filter.is_countably_generated.filter_basis_filter
- \+ *def* filter.is_countably_generated.generating_set
- \+ *lemma* filter.is_countably_generated.has_antimono_basis
- \+ *lemma* filter.is_countably_generated.has_countable_basis
- \+ *lemma* filter.is_countably_generated.tendsto_iff_seq_tendsto
- \+ *lemma* filter.is_countably_generated.tendsto_of_seq_tendsto
- \+ *def* filter.is_countably_generated
- \+ *lemma* filter.is_countably_generated_at_top_finset_nat
- \+ *lemma* filter.is_countably_generated_binfi_principal
- \+ *lemma* filter.is_countably_generated_iff_exists_antimono_basis
- \+ *lemma* filter.is_countably_generated_of_seq
- \+ *lemma* filter.is_countably_generated_seq
- \+ *lemma* filter.of_sets_filter_eq_generate
- \+ *lemma* filter_basis.eq_infi_principal
- \+ *lemma* filter_basis.mem_filter_iff
- \+ *lemma* filter_basis.mem_filter_of_mem

Modified src/order/filter/basic.lean
- \- *theorem* directed_of_chain
- \- *lemma* directed_on_Union
- \+ *lemma* filter.infi_eq_generate
- \+ *lemma* filter.map_at_top_inf_ne_bot_iff
- \+ *lemma* filter.mem_generate_iff
- \+ *lemma* filter.mem_infi_iff
- \+/\- *lemma* filter.mem_traverse_sets_iff
- \+ *lemma* filter.nat.cofinite_eq_at_top
- \+ *lemma* filter.sInter_mem_sets_of_finite
- \+ *lemma* filter.set.infinite_iff_frequently_cofinite
- \- *lemma* nat.cofinite_eq_at_top
- \- *lemma* set.infinite_iff_frequently_cofinite

Modified src/order/zorn.lean
- \+ *theorem* directed_of_chain

Modified src/topology/bases.lean
- \- *lemma* filter.has_countable_basis.comap
- \- *lemma* filter.has_countable_basis.tendsto_iff_seq_tendsto
- \- *lemma* filter.has_countable_basis.tendsto_of_seq_tendsto
- \- *def* filter.has_countable_basis
- \- *lemma* filter.has_countable_basis_at_top_finset_nat
- \- *lemma* filter.has_countable_basis_iff_mono_seq'
- \- *lemma* filter.has_countable_basis_iff_mono_seq
- \- *lemma* filter.has_countable_basis_iff_seq
- \- *lemma* filter.has_countable_basis_of_seq
- \- *lemma* filter.mono_seq_of_has_countable_basis
- \- *lemma* filter.seq_of_has_countable_basis

Modified src/topology/basic.lean


Modified src/topology/continuous_on.lean


Modified src/topology/metric_space/basic.lean


Modified src/topology/metric_space/emetric_space.lean
- \+/\- *theorem* emetric.mem_nhds_iff
- \+/\- *theorem* emetric.uniformity_has_countable_basis

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
- \+ *def* cochain_complex.cohomology_functor
- \+ *def* cochain_complex.cohomology_map
- \+ *lemma* cochain_complex.cohomology_map_comp
- \+ *lemma* cochain_complex.cohomology_map_condition
- \+ *lemma* cochain_complex.cohomology_map_id
- \+ *lemma* cochain_complex.image_map_ι
- \+ *lemma* cochain_complex.image_to_kernel_map_condition
- \+ *lemma* cochain_complex.induced_maps_commute



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
- \+/\- *def* add_monoid_hom.to_int_linear_map
- \+/\- *def* add_monoid_hom.to_rat_linear_map
- \+/\- *lemma* finset.sum_const'
- \+/\- *lemma* finset.sum_smul
- \+/\- *def* ideal
- \+/\- *lemma* is_linear_map.is_linear_map_neg
- \+/\- *lemma* is_linear_map.is_linear_map_smul'
- \+/\- *lemma* is_linear_map.is_linear_map_smul
- \+/\- *lemma* is_linear_map.map_neg
- \+/\- *lemma* is_linear_map.map_smul
- \+/\- *lemma* is_linear_map.map_sub
- \+/\- *lemma* is_linear_map.map_zero
- \+/\- *def* is_linear_map.mk'
- \+/\- *theorem* is_linear_map.mk'_apply
- \+/\- *lemma* linear_map.coe_mk
- \+/\- *def* linear_map.comp
- \+/\- *lemma* linear_map.comp_apply
- \+/\- *theorem* linear_map.ext
- \+/\- *theorem* linear_map.ext_iff
- \+/\- *def* linear_map.id
- \+/\- *lemma* linear_map.id_apply
- \+/\- *theorem* linear_map.is_linear
- \+/\- *lemma* linear_map.map_add
- \+/\- *lemma* linear_map.map_neg
- \+/\- *lemma* linear_map.map_smul
- \+/\- *lemma* linear_map.map_sub
- \+/\- *lemma* linear_map.map_sum
- \+/\- *def* linear_map.to_add_monoid_hom
- \+/\- *lemma* linear_map.to_add_monoid_hom_coe
- \+/\- *lemma* linear_map.to_fun_eq_coe
- \+/\- *lemma* list.sum_smul
- \+/\- *lemma* module.gsmul_eq_smul
- \+/\- *def* module.of_core
- \+/\- *lemma* multiset.sum_smul
- \+/\- *theorem* neg_one_smul
- \+/\- *def* ring_hom.to_module
- \+ *def* ring_hom.to_semimodule
- \+/\- *lemma* semimodule.add_monoid_smul_eq_smul
- \+/\- *lemma* semimodule.eq_zero_of_zero_eq_one
- \+/\- *lemma* smul_eq_mul
- \+/\- *theorem* smul_sub
- \+/\- *theorem* sub_smul
- \+/\- *lemma* submodule.coe_add
- \+/\- *lemma* submodule.coe_mk
- \+/\- *lemma* submodule.coe_neg
- \+/\- *lemma* submodule.coe_smul
- \+/\- *lemma* submodule.coe_sub
- \+/\- *lemma* submodule.coe_zero
- \+/\- *theorem* submodule.ext'
- \+/\- *theorem* submodule.ext
- \+/\- *theorem* submodule.mem_coe
- \+/\- *lemma* submodule.neg_mem
- \+/\- *lemma* submodule.smul_mem
- \+/\- *lemma* submodule.smul_mem_iff'
- \+/\- *lemma* submodule.subtype_eq_val
- \+/\- *lemma* submodule.sum_mem
- \+/\- *lemma* submodule.zero_mem
- \+/\- *def* subspace
- \+/\- *theorem* zero_smul



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
Added src/algebra/category/Group/biproducts.lean
- \+ *def* AddCommGroup.has_colimit.desc
- \+ *lemma* AddCommGroup.has_colimit.desc_apply
- \+ *def* AddCommGroup.has_limit.lift
- \+ *lemma* AddCommGroup.has_limit.lift_apply

Modified src/algebra/pi_instances.lean
- \+/\- *lemma* add_monoid_hom.single_apply

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Added src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.bicone.to_cocone
- \+ *def* category_theory.limits.bicone.to_cone
- \+ *def* category_theory.limits.binary_bicone.to_cocone
- \+ *def* category_theory.limits.binary_bicone.to_cone
- \+ *def* category_theory.limits.biprod_iso
- \+ *def* category_theory.limits.biproduct_iso



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
- \+ *lemma* pred_ne_self
- \+ *lemma* succ_ne_self

Added src/set_theory/game/domineering.lean
- \+ *def* pgame.domineering.L
- \+ *def* pgame.domineering.board
- \+ *lemma* pgame.domineering.card_of_mem_left
- \+ *lemma* pgame.domineering.card_of_mem_right
- \+ *def* pgame.domineering.left
- \+ *def* pgame.domineering.move_left
- \+ *lemma* pgame.domineering.move_left_card
- \+ *lemma* pgame.domineering.move_left_smaller
- \+ *def* pgame.domineering.move_right
- \+ *lemma* pgame.domineering.move_right_card
- \+ *lemma* pgame.domineering.move_right_smaller
- \+ *def* pgame.domineering.one
- \+ *def* pgame.domineering.right
- \+ *def* pgame.domineering.shift_right
- \+ *def* pgame.domineering.shift_up
- \+ *def* pgame.domineering

Added src/set_theory/game/short.lean
- \+ *def* pgame.fintype_left
- \+ *def* pgame.fintype_right
- \+ *def* pgame.le_lt_decidable
- \+ *def* pgame.move_left_short'
- \+ *def* pgame.move_right_short'
- \+ *def* pgame.short.mk'
- \+ *def* pgame.short_of_equiv_empty
- \+ *def* pgame.short_of_relabelling

Added src/set_theory/game/state.lean
- \+ *def* game.of
- \+ *def* pgame.left_moves_of
- \+ *def* pgame.left_moves_of_aux
- \+ *def* pgame.of
- \+ *def* pgame.of_aux
- \+ *def* pgame.of_aux_relabelling
- \+ *def* pgame.relabelling_move_left
- \+ *def* pgame.relabelling_move_left_aux
- \+ *def* pgame.relabelling_move_right
- \+ *def* pgame.relabelling_move_right_aux
- \+ *def* pgame.right_moves_of
- \+ *def* pgame.right_moves_of_aux
- \+ *lemma* pgame.turn_bound_ne_zero_of_left_move
- \+ *lemma* pgame.turn_bound_ne_zero_of_right_move
- \+ *lemma* pgame.turn_bound_of_left
- \+ *lemma* pgame.turn_bound_of_right

Modified src/set_theory/pgame.lean
- \+/\- *lemma* pgame.relabel_move_left'
- \+/\- *lemma* pgame.relabel_move_left
- \+/\- *lemma* pgame.relabel_move_right'
- \+/\- *lemma* pgame.relabel_move_right
- \+ *def* pgame.relabelling.trans



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
- \+ *def* category_theory.arrow.hom_mk'
- \+ *lemma* category_theory.arrow.hom_mk'_left
- \+ *lemma* category_theory.arrow.hom_mk'_right
- \+ *def* category_theory.arrow.hom_mk
- \+ *lemma* category_theory.arrow.hom_mk_left
- \+ *lemma* category_theory.arrow.hom_mk_right
- \+ *lemma* category_theory.arrow.id_left
- \+ *lemma* category_theory.arrow.id_right
- \+ *def* category_theory.arrow.mk
- \+ *lemma* category_theory.arrow.mk_hom
- \+ *def* category_theory.arrow
- \+ *lemma* category_theory.comma.id_left
- \+ *lemma* category_theory.comma.id_right
- \+/\- *def* category_theory.comma.map_right_comp

Modified src/category_theory/limits/shapes/images.lean
- \+ *def* category_theory.limits.has_image_map_comp
- \+ *def* category_theory.limits.has_image_map_id
- \+ *def* category_theory.limits.im
- \+ *lemma* category_theory.limits.image.factor_map
- \+ *lemma* category_theory.limits.image.map_comp
- \+ *lemma* category_theory.limits.image.map_hom_mk'_ι
- \+ *lemma* category_theory.limits.image.map_id
- \+ *lemma* category_theory.limits.image.map_ι



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


Added src/tactic/lean_core_docs.lean




## [2020-04-11 18:44:15](https://github.com/leanprover-community/mathlib/commit/80340d8)
feat(category_theory): define action_category ([#2358](https://github.com/leanprover-community/mathlib/pull/2358))
This is a simple construction that I couldn't find anywhere else: given a monoid/group action on X, we get a category/groupoid structure on X. The plan is to use to use the action groupoid in the proof of Nielsen-Schreier, where the projection onto the single object groupoid is thought of as a covering map.
To make sense of "stabilizer is mul_equiv to End", I added the simple fact that the stabilizer of any multiplicative action is a submonoid. This already existed for group actions. As far as I can tell, this instance shouldn't cause any problems as it is a Prop.
#### Estimated changes
Added src/category_theory/action.lean
- \+ *def* category_theory.action_as_functor
- \+ *lemma* category_theory.action_category.hom_as_subtype
- \+ *def* category_theory.action_category.obj_equiv
- \+ *def* category_theory.action_category.stabilizer_iso_End
- \+ *lemma* category_theory.action_category.stabilizer_iso_End_apply
- \+ *lemma* category_theory.action_category.stabilizer_iso_End_symm_apply
- \+ *def* category_theory.action_category.π
- \+ *lemma* category_theory.action_category.π_map
- \+ *lemma* category_theory.action_category.π_obj
- \+ *def* category_theory.action_category

Modified src/category_theory/elements.lean
- \+/\- *def* category_theory.functor.elements

Modified src/group_theory/group_action.lean




## [2020-04-11 16:16:28](https://github.com/leanprover-community/mathlib/commit/e1feab4)
refactor(*): rename ordered groups/monoids to ordered add_ groups/monoids ([#2347](https://github.com/leanprover-community/mathlib/pull/2347))
In the perfectoid project we need ordered commutative monoids, and they are multiplicative. So the additive versions should be renamed to make some place.
#### Estimated changes
Modified scripts/nolints.txt


Modified src/algebra/archimedean.lean


Modified src/algebra/big_operators.lean
- \+/\- *lemma* finset.le_sum_of_subadditive
- \+/\- *lemma* with_top.sum_lt_top
- \+/\- *lemma* with_top.sum_lt_top_iff

Modified src/algebra/group_power.lean
- \+/\- *theorem* add_monoid.smul_nonneg

Modified src/algebra/order_functions.lean


Modified src/algebra/ordered_group.lean
- \+ *theorem* nonneg_add_comm_group.nonneg_def
- \+ *theorem* nonneg_add_comm_group.nonneg_total_iff
- \+ *theorem* nonneg_add_comm_group.not_zero_pos
- \+ *theorem* nonneg_add_comm_group.pos_def
- \+ *def* nonneg_add_comm_group.to_decidable_linear_ordered_add_comm_group
- \+ *theorem* nonneg_add_comm_group.zero_lt_iff_nonneg_nonneg
- \- *theorem* nonneg_comm_group.nonneg_def
- \- *theorem* nonneg_comm_group.nonneg_total_iff
- \- *theorem* nonneg_comm_group.not_zero_pos
- \- *theorem* nonneg_comm_group.pos_def
- \- *def* nonneg_comm_group.to_decidable_linear_ordered_add_comm_group
- \- *theorem* nonneg_comm_group.zero_lt_iff_nonneg_nonneg
- \+ *def* ordered_add_comm_group.mk'
- \- *def* ordered_comm_group.mk'
- \+/\- *lemma* with_bot.add_bot
- \+/\- *lemma* with_bot.bot_add
- \+/\- *lemma* with_top.add_eq_top
- \+/\- *lemma* with_top.add_lt_top
- \+/\- *lemma* with_top.add_top
- \+/\- *lemma* with_top.top_add
- \+/\- *lemma* with_top.zero_lt_coe
- \+/\- *lemma* with_top.zero_lt_top
- \+ *def* with_zero.ordered_add_comm_monoid
- \- *def* with_zero.ordered_comm_monoid

Modified src/algebra/ordered_ring.lean


Modified src/algebra/pi_instances.lean


Modified src/algebra/punit_instances.lean


Modified src/data/finsupp.lean
- \+/\- *lemma* finsupp.add_eq_zero_iff
- \+/\- *lemma* finsupp.le_iff

Modified src/data/multiset.lean
- \+/\- *lemma* multiset.le_sum_of_subadditive

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


Added .github/workflows/add_label_from_review.yml




## [2020-04-11 09:58:07](https://github.com/leanprover-community/mathlib/commit/c68f23d)
chore(category_theory/types): add documentation, remove bad simp lemmas and instances, add notation for functions as morphisms ([#2383](https://github.com/leanprover-community/mathlib/pull/2383))
* Add module doc and doc strings for `src/category_theory/types.lean`.
* Remove some bad simp lemmas and instances in that file and `src/category_theory/category/default.lean`.
* Add a notation `↾f` which enables Lean to see a function `f : α → β` as a morphism `α ⟶ β` in the category of types.
#### Estimated changes
Modified src/algebra/category/Group/adjunctions.lean


Modified src/category_theory/category/default.lean
- \+ *lemma* category_theory.epi_comp
- \+ *lemma* category_theory.mono_comp

Modified src/category_theory/limits/shapes/images.lean


Modified src/category_theory/types.lean
- \- *lemma* category_theory.functor_to_types.map_comp
- \+ *lemma* category_theory.functor_to_types.map_comp_apply
- \- *lemma* category_theory.functor_to_types.map_id
- \+ *lemma* category_theory.functor_to_types.map_id_apply
- \+/\- *lemma* category_theory.types_comp
- \+ *lemma* category_theory.types_comp_apply
- \+/\- *lemma* category_theory.types_hom
- \+/\- *lemma* category_theory.types_id
- \+ *lemma* category_theory.types_id_apply

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
- \+ *def* category_theory.is_iso.of_epi_section
- \+ *def* category_theory.is_iso.of_mono_retraction

Modified src/category_theory/groupoid.lean
- \+ *def* category_theory.groupoid.of_is_iso
- \+ *def* category_theory.groupoid.of_trunc_split_mono

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
- \+/\- *def* Module.of

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
- \+/\- *theorem* abs_le_abs
- \+/\- *lemma* min_add
- \+/\- *lemma* min_sub

Modified src/algebra/ordered_group.lean
- \+ *lemma* decidable_linear_ordered_add_comm_group.eq_of_abs_sub_nonpos
- \- *lemma* decidable_linear_ordered_comm_group.eq_of_abs_sub_nonpos
- \+/\- *lemma* neg_neg_iff_pos
- \+ *def* nonneg_comm_group.to_decidable_linear_ordered_add_comm_group
- \- *def* nonneg_comm_group.to_decidable_linear_ordered_comm_group

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
- \+/\- *def* category_theory.limits.colimit.cocone
- \+/\- *def* category_theory.limits.limit.cone

Modified src/category_theory/limits/preserves.lean


Modified src/category_theory/limits/shapes/equalizers.lean


Modified src/category_theory/limits/shapes/images.lean
- \+/\- *def* category_theory.limits.image.is_image
- \+/\- *def* category_theory.limits.image.mono_factorisation

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
- \+/\- *def* category_theory.shift

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
- \+/\- *lemma* list.exists_le_of_sum_le
- \+/\- *lemma* list.exists_lt_of_sum_lt
- \+/\- *lemma* list.length_pos_of_sum_pos

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
- \+/\- *lemma* prod.map_fst
- \+ *lemma* prod.map_mk
- \+/\- *lemma* prod.map_snd

Modified src/data/rat/meta_defs.lean


Modified src/data/rat/order.lean


Modified src/data/real/basic.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/nnreal.lean
- \+/\- *lemma* nnreal.inv_inv

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
- \+/\- *lemma* filter.filter_product.abs_def
- \+/\- *lemma* filter.filter_product.of_abs

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
- \+ *def* game.ordered_add_comm_group_game
- \- *def* game.ordered_comm_group_game

Modified src/set_theory/lists.lean


Modified src/set_theory/ordinal.lean


Modified src/set_theory/surreal.lean


Modified src/tactic/ext.lean


Modified src/tactic/lift.lean


Modified src/tactic/norm_num.lean
- \+/\- *lemma* norm_num.lt_add_of_pos_helper

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
- \+/\- *def* right_param
- \+/\- *def* wrong_param

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
- \+/\- *theorem* add_monoid_hom.map_sub
- \+ *def* add_monoid_hom.mul_left
- \+ *def* add_monoid_hom.mul_right

Modified src/data/list/basic.lean
- \+ *theorem* list.prod_map_hom
- \+ *theorem* list.sum_map_mul_left
- \+ *theorem* list.sum_map_mul_right

Modified src/data/list/range.lean
- \+ *theorem* list.prod_range_succ'



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


Added src/tactic/trunc_cases.lean


Added test/trunc_cases.lean
- \+ *lemma* eq_rec_prod
- \+ *def* u



## [2020-04-10 15:39:37](https://github.com/leanprover-community/mathlib/commit/3cc7a32)
feat(order/complete_lattice): add a constructor from `partial_order` and `Inf` ([#2359](https://github.com/leanprover-community/mathlib/pull/2359))
Also use `∃!` in `data/setoid`.
#### Estimated changes
Modified src/data/setoid.lean
- \- *lemma* setoid.Inf_le
- \+/\- *lemma* setoid.classes_eqv_classes
- \+/\- *lemma* setoid.eq_of_mem_eqv_class
- \+/\- *lemma* setoid.eqv_class_mem
- \+/\- *lemma* setoid.eqv_classes_disjoint
- \- *lemma* setoid.le_Inf
- \+/\- *def* setoid.mk_classes
- \+ *lemma* setoid.rel_iff_exists_classes

Modified src/group_theory/congruence.lean
- \- *lemma* con.Inf_le
- \+/\- *lemma* con.con_gen_of_con
- \- *lemma* con.le_Inf

Modified src/order/bounded_lattice.lean


Modified src/order/bounds.lean
- \+/\- *lemma* lower_bounds_insert
- \+/\- *lemma* lower_bounds_singleton
- \+/\- *lemma* upper_bounds_insert
- \+/\- *lemma* upper_bounds_singleton

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
- \+ *lemma* lie_submodule.quotient.lie_quotient_action_apply
- \+ *def* lie_submodule.quotient.lie_submodule_invariant

Modified src/linear_algebra/basic.lean
- \+ *lemma* submodule.comap_le_comap_smul
- \+ *def* submodule.compatible_maps
- \+ *lemma* submodule.inf_comap_le_comap_add
- \+ *def* submodule.mapq_linear



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
- \+/\- *lemma* mv_polynomial.aeval_C
- \+/\- *theorem* mv_polynomial.aeval_def

Modified src/data/padics/padic_integers.lean


Modified src/data/polynomial.lean
- \+/\- *lemma* polynomial.aeval_C
- \+/\- *theorem* polynomial.aeval_def
- \+ *lemma* polynomial.coe_eval₂_ring_hom
- \+/\- *lemma* polynomial.degree_map
- \+/\- *lemma* polynomial.degree_map_eq_of_leading_coeff_ne_zero
- \+/\- *lemma* polynomial.degree_map_le
- \+ *def* polynomial.eval₂_ring_hom
- \+/\- *lemma* polynomial.leading_coeff_map
- \+/\- *lemma* polynomial.map_div
- \+/\- *lemma* polynomial.map_div_by_monic
- \+/\- *lemma* polynomial.map_eq_zero
- \+/\- *lemma* polynomial.map_id
- \+/\- *lemma* polynomial.map_injective
- \+/\- *lemma* polynomial.map_map
- \+/\- *lemma* polynomial.map_mod
- \+/\- *lemma* polynomial.map_mod_by_monic
- \+/\- *lemma* polynomial.map_mod_div_by_monic
- \+/\- *lemma* polynomial.map_neg
- \+/\- *lemma* polynomial.map_sub
- \+/\- *lemma* polynomial.monic_map
- \+/\- *lemma* polynomial.nat_degree_map

Modified src/field_theory/minimal_polynomial.lean


Modified src/field_theory/splitting_field.lean
- \+/\- *lemma* polynomial.splits_comp_of_splits
- \+/\- *lemma* polynomial.splits_map_iff
- \+/\- *lemma* polynomial.splits_of_splits_id

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/adjoin_root.lean
- \+/\- *lemma* adjoin_root.eval₂_root
- \+/\- *lemma* adjoin_root.is_root_root

Modified src/ring_theory/algebra.lean
- \+/\- *theorem* alg_hom.commutes
- \+ *theorem* alg_hom.comp_algebra_map
- \+/\- *theorem* alg_hom.ext
- \- *lemma* alg_hom.id_to_linear_map
- \+/\- *def* algebra.comap.of_comap
- \+/\- *def* algebra.comap.to_comap
- \+/\- *def* algebra.comap
- \+/\- *theorem* algebra.commutes
- \+/\- *lemma* algebra.id.map_eq_self
- \+/\- *theorem* algebra.left_comm
- \- *lemma* algebra.map_add
- \- *lemma* algebra.map_mul
- \- *lemma* algebra.map_neg
- \- *lemma* algebra.map_one
- \- *lemma* algebra.map_sub
- \- *lemma* algebra.map_zero
- \+/\- *theorem* algebra.mem_bot
- \+/\- *def* algebra.of_id
- \+/\- *theorem* algebra.of_id_apply
- \- *def* algebra.of_ring_hom
- \+/\- *lemma* algebra.smul_def''
- \+/\- *lemma* algebra.smul_def
- \+/\- *theorem* algebra.to_comap_apply
- \+/\- *def* algebra_map
- \+ *def* ring_hom.to_algebra
- \+/\- *lemma* subalgebra.range_le

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


Added .github/workflows/add_label.yml


Modified .github/workflows/build.yml


Deleted .mergify.yml


Modified README.md


Added bors.toml


Added docs/contribute/bors.md


Modified docs/contribute/index.md


Modified scripts/fetch_olean_cache.sh


Deleted scripts/look_up_olean_hash.py


Modified scripts/update_nolints.sh


Deleted scripts/write_azure_table_entry.py




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
- \+/\- *def* frobenius
- \+/\- *theorem* frobenius_add
- \+/\- *theorem* frobenius_def
- \+/\- *theorem* frobenius_inj
- \+/\- *theorem* frobenius_mul
- \+/\- *theorem* frobenius_nat_cast
- \+/\- *theorem* frobenius_neg
- \+/\- *theorem* frobenius_one
- \+/\- *theorem* frobenius_sub
- \+/\- *theorem* frobenius_zero
- \- *theorem* is_monoid_hom.map_frobenius
- \+ *theorem* monoid_hom.iterate_map_frobenius
- \+ *theorem* monoid_hom.map_frobenius
- \+ *theorem* monoid_hom.map_iterate_frobenius
- \+ *theorem* ring_hom.iterate_map_frobenius
- \+ *theorem* ring_hom.map_frobenius
- \+ *theorem* ring_hom.map_iterate_frobenius

Modified src/algebra/group_power.lean
- \+ *theorem* add_monoid_hom.iterate_map_smul
- \+ *theorem* monoid_hom.iterate_map_pow
- \+ *lemma* ring_hom.iterate_map_pow
- \+ *lemma* ring_hom.iterate_map_smul
- \+/\- *lemma* ring_hom.map_pow

Modified src/data/nat/basic.lean
- \+ *theorem* monoid_hom.iterate_map_inv
- \+ *theorem* monoid_hom.iterate_map_mul
- \+ *theorem* monoid_hom.iterate_map_one
- \+ *theorem* monoid_hom.iterate_map_sub
- \+ *theorem* ring_hom.iterate_map_add
- \+ *theorem* ring_hom.iterate_map_mul
- \+ *theorem* ring_hom.iterate_map_neg
- \+ *theorem* ring_hom.iterate_map_one
- \+ *theorem* ring_hom.iterate_map_sub
- \+ *theorem* ring_hom.iterate_map_zero

Modified src/field_theory/perfect_closure.lean
- \+ *lemma* coe_frobenius_equiv
- \+ *lemma* coe_frobenius_equiv_symm
- \+ *theorem* eq_pth_root_iff
- \+ *def* frobenius_equiv
- \+/\- *theorem* frobenius_pth_root
- \- *theorem* is_ring_hom.pth_root
- \+ *theorem* monoid_hom.map_iterate_pth_root
- \+ *theorem* monoid_hom.map_pth_root
- \- *def* perfect_closure.UMP
- \+/\- *theorem* perfect_closure.eq_iff'
- \+/\- *theorem* perfect_closure.eq_pth_root
- \- *def* perfect_closure.frobenius_equiv
- \- *theorem* perfect_closure.frobenius_equiv_apply
- \+/\- *theorem* perfect_closure.frobenius_mk
- \+ *lemma* perfect_closure.induction_on
- \+/\- *theorem* perfect_closure.int_cast
- \+ *def* perfect_closure.lift
- \+ *def* perfect_closure.lift_on
- \+ *lemma* perfect_closure.lift_on_mk
- \+ *def* perfect_closure.mk
- \+ *lemma* perfect_closure.mk_add_mk
- \+ *lemma* perfect_closure.mk_mul_mk
- \+/\- *theorem* perfect_closure.mk_zero
- \+/\- *theorem* perfect_closure.nat_cast
- \+/\- *theorem* perfect_closure.nat_cast_eq_iff
- \+ *lemma* perfect_closure.neg_mk
- \+/\- *def* perfect_closure.of
- \+ *lemma* perfect_closure.of_apply
- \+ *lemma* perfect_closure.one_def
- \+ *lemma* perfect_closure.quot_mk_eq_mk
- \+/\- *theorem* perfect_closure.r.sound
- \+ *lemma* perfect_closure.zero_def
- \+/\- *def* perfect_closure
- \+ *def* pth_root
- \+ *theorem* pth_root_eq_iff
- \+/\- *theorem* pth_root_frobenius
- \+ *theorem* ring_hom.map_iterate_pth_root
- \+ *theorem* ring_hom.map_pth_root



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


Modified src/tactic/hint.lean


Modified src/tactic/interval_cases.lean


Modified src/tactic/linarith.lean


Modified src/tactic/omega/main.lean


Modified src/tactic/reassoc_axiom.lean


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
Added src/tactic/simp_result.lean


Added test/simp_result.lean




## [2020-04-09 12:44:49](https://github.com/leanprover-community/mathlib/commit/63fc23a)
feat(data/list): chain_iff_nth_le ([#2354](https://github.com/leanprover-community/mathlib/pull/2354))
* feat(data/list): chain_iff_nth_le
* Update src/data/list/basic.lean
Co-Authored-By: Johan Commelin <johan@commelin.net>
* move
* fix
#### Estimated changes
Modified src/data/list/chain.lean
- \+ *theorem* list.chain'_iff_nth_le
- \+ *theorem* list.chain_iff_nth_le

Modified src/data/nat/basic.lean
- \+ *lemma* nat.lt_of_lt_pred



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
- \+ *lemma* set.exists_range_iff'
- \+ *lemma* set.mem_compl_singleton_iff
- \+ *lemma* set.subset_compl_singleton_iff



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


Added src/data/list/antidiagonal.lean
- \+ *def* list.nat.antidiagonal
- \+ *lemma* list.nat.antidiagonal_zero
- \+ *lemma* list.nat.length_antidiagonal
- \+ *lemma* list.nat.mem_antidiagonal
- \+ *lemma* list.nat.nodup_antidiagonal

Added src/data/list/bag_inter.lean
- \+ *theorem* list.bag_inter_nil
- \+ *theorem* list.bag_inter_nil_iff_inter_nil
- \+ *theorem* list.bag_inter_sublist_left
- \+ *theorem* list.cons_bag_inter_of_neg
- \+ *theorem* list.cons_bag_inter_of_pos
- \+ *theorem* list.count_bag_inter
- \+ *theorem* list.mem_bag_inter
- \+ *theorem* list.nil_bag_inter

Modified src/data/list/basic.lean
- \- *lemma* list.Ico.append_consecutive
- \- *lemma* list.Ico.bag_inter_consecutive
- \- *theorem* list.Ico.chain'_succ
- \- *theorem* list.Ico.eq_cons
- \- *theorem* list.Ico.eq_empty_iff
- \- *theorem* list.Ico.eq_nil_of_le
- \- *lemma* list.Ico.filter_le
- \- *lemma* list.Ico.filter_le_of_le
- \- *lemma* list.Ico.filter_le_of_le_bot
- \- *lemma* list.Ico.filter_le_of_top_le
- \- *lemma* list.Ico.filter_lt
- \- *lemma* list.Ico.filter_lt_of_ge
- \- *lemma* list.Ico.filter_lt_of_le_bot
- \- *lemma* list.Ico.filter_lt_of_top_le
- \- *lemma* list.Ico.inter_consecutive
- \- *theorem* list.Ico.length
- \- *theorem* list.Ico.map_add
- \- *theorem* list.Ico.map_sub
- \- *theorem* list.Ico.mem
- \- *theorem* list.Ico.nodup
- \- *theorem* list.Ico.not_mem_top
- \- *theorem* list.Ico.pairwise_lt
- \- *theorem* list.Ico.pred_singleton
- \- *theorem* list.Ico.self_empty
- \- *theorem* list.Ico.succ_singleton
- \- *theorem* list.Ico.succ_top
- \- *lemma* list.Ico.trichotomy
- \- *theorem* list.Ico.zero_bot
- \- *def* list.Ico
- \- *theorem* list.array_eq_of_fn
- \- *theorem* list.bag_inter_nil
- \- *theorem* list.bag_inter_nil_iff_inter_nil
- \- *theorem* list.bag_inter_sublist_left
- \- *lemma* list.bi_unique_forall₂
- \- *theorem* list.chain'.cons
- \- *theorem* list.chain'.iff
- \- *theorem* list.chain'.iff_mem
- \- *theorem* list.chain'.imp
- \- *theorem* list.chain'.tail
- \- *theorem* list.chain'_cons
- \- *theorem* list.chain'_iff_pairwise
- \- *theorem* list.chain'_map
- \- *theorem* list.chain'_map_of_chain'
- \- *theorem* list.chain'_nil
- \- *theorem* list.chain'_of_chain'_map
- \- *theorem* list.chain'_pair
- \- *theorem* list.chain'_reverse
- \- *theorem* list.chain'_singleton
- \- *theorem* list.chain'_split
- \- *theorem* list.chain.iff
- \- *theorem* list.chain.iff_mem
- \- *theorem* list.chain.imp'
- \- *theorem* list.chain.imp
- \- *theorem* list.chain_iff_pairwise
- \- *theorem* list.chain_lt_range'
- \- *theorem* list.chain_map
- \- *theorem* list.chain_map_of_chain
- \- *theorem* list.chain_of_chain_cons
- \- *theorem* list.chain_of_chain_map
- \- *theorem* list.chain_of_pairwise
- \- *theorem* list.chain_singleton
- \- *theorem* list.chain_split
- \- *theorem* list.chain_succ_range'
- \- *theorem* list.cons_bag_inter_of_neg
- \- *theorem* list.cons_bag_inter_of_pos
- \- *theorem* list.count_bag_inter
- \- *theorem* list.count_eq_one_of_mem
- \- *lemma* list.diff_eq_filter_of_nodup
- \- *theorem* list.disjoint_of_nodup_append
- \- *theorem* list.enum_from_map_fst
- \- *theorem* list.enum_map_fst
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
- \- *theorem* list.filter_map_cons
- \- *def* list.fin_range
- \- *theorem* list.forall_mem_ne
- \- *theorem* list.forall_mem_pw_filter
- \- *theorem* list.forall_of_forall_of_pairwise
- \- *lemma* list.forall_of_pairwise
- \- *lemma* list.forall₂.flip
- \- *theorem* list.forall₂.imp
- \- *lemma* list.forall₂.mp
- \- *lemma* list.forall₂_and_left
- \- *theorem* list.forall₂_cons
- \- *lemma* list.forall₂_cons_left_iff
- \- *lemma* list.forall₂_cons_right_iff
- \- *theorem* list.forall₂_drop
- \- *theorem* list.forall₂_drop_append
- \- *lemma* list.forall₂_eq_eq_eq
- \- *theorem* list.forall₂_iff_zip
- \- *theorem* list.forall₂_length_eq
- \- *lemma* list.forall₂_map_left_iff
- \- *lemma* list.forall₂_map_right_iff
- \- *lemma* list.forall₂_nil_left_iff
- \- *lemma* list.forall₂_nil_right_iff
- \- *lemma* list.forall₂_refl
- \- *lemma* list.forall₂_same
- \- *theorem* list.forall₂_take
- \- *theorem* list.forall₂_take_append
- \- *theorem* list.forall₂_zip
- \- *lemma* list.func.add_nil
- \- *lemma* list.func.eq_get_of_mem
- \- *lemma* list.func.eq_of_equiv
- \- *lemma* list.func.equiv_of_eq
- \- *lemma* list.func.equiv_refl
- \- *lemma* list.func.equiv_symm
- \- *lemma* list.func.equiv_trans
- \- *lemma* list.func.forall_val_of_forall_mem
- \- *lemma* list.func.get_add
- \- *lemma* list.func.get_eq_default_of_le
- \- *lemma* list.func.get_map'
- \- *lemma* list.func.get_map
- \- *lemma* list.func.get_neg
- \- *lemma* list.func.get_nil
- \- *lemma* list.func.get_pointwise
- \- *lemma* list.func.get_set
- \- *lemma* list.func.get_set_eq_of_ne
- \- *lemma* list.func.get_sub
- \- *lemma* list.func.length_add
- \- *lemma* list.func.length_neg
- \- *lemma* list.func.length_pointwise
- \- *lemma* list.func.length_set
- \- *lemma* list.func.length_sub
- \- *lemma* list.func.map_add_map
- \- *lemma* list.func.mem_get_of_le
- \- *lemma* list.func.mem_get_of_ne_zero
- \- *lemma* list.func.nil_add
- \- *lemma* list.func.nil_pointwise
- \- *lemma* list.func.nil_sub
- \- *lemma* list.func.pointwise_nil
- \- *lemma* list.func.sub_nil
- \- *theorem* list.iota_eq_reverse_range'
- \- *lemma* list.left_unique_forall₂
- \- *lemma* list.length_fin_range
- \- *theorem* list.length_iota
- \- *theorem* list.length_of_fn
- \- *theorem* list.length_of_fn_aux
- \- *theorem* list.length_range'
- \- *theorem* list.length_range
- \- *theorem* list.length_revzip
- \- *lemma* list.length_rotate'
- \- *lemma* list.length_rotate
- \- *theorem* list.length_zip
- \- *theorem* list.map_add_range'
- \- *theorem* list.map_sub_range'
- \- *theorem* list.mem_bag_inter
- \- *lemma* list.mem_diff_iff_of_nodup
- \- *theorem* list.mem_erase_dup
- \- *theorem* list.mem_erase_iff_of_nodup
- \- *theorem* list.mem_erase_of_nodup
- \- *lemma* list.mem_fin_range
- \- *theorem* list.mem_iota
- \- *theorem* list.mem_range'
- \- *theorem* list.mem_range
- \- *lemma* list.mem_rotate
- \- *theorem* list.mem_sections
- \- *theorem* list.mem_sections_length
- \- *theorem* list.mem_zip
- \- *def* list.nat.antidiagonal
- \- *lemma* list.nat.antidiagonal_zero
- \- *lemma* list.nat.length_antidiagonal
- \- *lemma* list.nat.mem_antidiagonal
- \- *lemma* list.nat.nodup_antidiagonal
- \- *theorem* list.nil_bag_inter
- \- *theorem* list.nodup_append
- \- *theorem* list.nodup_append_comm
- \- *theorem* list.nodup_append_of_nodup
- \- *theorem* list.nodup_attach
- \- *theorem* list.nodup_bind
- \- *theorem* list.nodup_concat
- \- *theorem* list.nodup_cons
- \- *theorem* list.nodup_cons_of_nodup
- \- *theorem* list.nodup_diff
- \- *theorem* list.nodup_erase_dup
- \- *theorem* list.nodup_erase_eq_filter
- \- *theorem* list.nodup_erase_of_nodup
- \- *theorem* list.nodup_filter
- \- *theorem* list.nodup_filter_map
- \- *lemma* list.nodup_fin_range
- \- *theorem* list.nodup_iff_count_le_one
- \- *theorem* list.nodup_iff_nth_le_inj
- \- *theorem* list.nodup_iff_sublist
- \- *theorem* list.nodup_insert
- \- *theorem* list.nodup_inter_of_nodup
- \- *theorem* list.nodup_iota
- \- *theorem* list.nodup_join
- \- *theorem* list.nodup_map
- \- *theorem* list.nodup_map_iff
- \- *theorem* list.nodup_map_on
- \- *theorem* list.nodup_middle
- \- *theorem* list.nodup_nil
- \- *theorem* list.nodup_of_fn
- \- *theorem* list.nodup_of_nodup_append_left
- \- *theorem* list.nodup_of_nodup_append_right
- \- *theorem* list.nodup_of_nodup_cons
- \- *theorem* list.nodup_of_nodup_map
- \- *theorem* list.nodup_of_sublist
- \- *theorem* list.nodup_pmap
- \- *theorem* list.nodup_product
- \- *theorem* list.nodup_range'
- \- *theorem* list.nodup_range
- \- *theorem* list.nodup_repeat
- \- *theorem* list.nodup_reverse
- \- *theorem* list.nodup_sigma
- \- *theorem* list.nodup_singleton
- \- *theorem* list.nodup_sublists'
- \- *theorem* list.nodup_sublists
- \- *lemma* list.nodup_sublists_len
- \- *theorem* list.nodup_union
- \- *lemma* list.nodup_update_nth
- \- *theorem* list.not_mem_of_nodup_cons
- \- *theorem* list.not_mem_range_self
- \- *theorem* list.not_nodup_cons_of_mem
- \- *theorem* list.not_nodup_pair
- \- *theorem* list.nth_le_index_of
- \- *theorem* list.nth_le_of_fn
- \- *lemma* list.nth_le_range
- \- *theorem* list.nth_of_fn
- \- *theorem* list.nth_of_fn_aux
- \- *theorem* list.nth_range'
- \- *theorem* list.nth_range
- \- *theorem* list.of_fn_eq_pmap
- \- *theorem* list.of_fn_nth_le
- \- *theorem* list.of_fn_succ
- \- *theorem* list.of_fn_zero
- \- *theorem* list.pairwise.and
- \- *theorem* list.pairwise.and_mem
- \- *theorem* list.pairwise.chain'
- \- *theorem* list.pairwise.iff
- \- *theorem* list.pairwise.iff_of_mem
- \- *theorem* list.pairwise.imp
- \- *theorem* list.pairwise.imp_mem
- \- *theorem* list.pairwise.imp_of_mem
- \- *theorem* list.pairwise.imp₂
- \- *theorem* list.pairwise_append
- \- *theorem* list.pairwise_append_comm
- \- *theorem* list.pairwise_filter
- \- *theorem* list.pairwise_filter_map
- \- *theorem* list.pairwise_filter_map_of_pairwise
- \- *theorem* list.pairwise_filter_of_pairwise
- \- *theorem* list.pairwise_gt_iota
- \- *theorem* list.pairwise_iff_nth_le
- \- *theorem* list.pairwise_join
- \- *theorem* list.pairwise_lt_range'
- \- *theorem* list.pairwise_lt_range
- \- *theorem* list.pairwise_map
- \- *theorem* list.pairwise_map_of_pairwise
- \- *theorem* list.pairwise_middle
- \- *theorem* list.pairwise_of_forall
- \- *theorem* list.pairwise_of_pairwise_cons
- \- *theorem* list.pairwise_of_pairwise_map
- \- *theorem* list.pairwise_of_sublist
- \- *theorem* list.pairwise_pair
- \- *theorem* list.pairwise_pw_filter
- \- *theorem* list.pairwise_reverse
- \- *theorem* list.pairwise_singleton
- \- *theorem* list.pairwise_sublists'
- \- *theorem* list.pairwise_sublists
- \- *theorem* list.prod_range_succ
- \- *lemma* list.prod_rotate_eq_one_of_prod_eq_one
- \- *theorem* list.pw_filter_cons_of_neg
- \- *theorem* list.pw_filter_cons_of_pos
- \- *theorem* list.pw_filter_eq_self
- \- *theorem* list.pw_filter_idempotent
- \- *theorem* list.pw_filter_map
- \- *theorem* list.pw_filter_nil
- \- *theorem* list.pw_filter_sublist
- \- *theorem* list.pw_filter_subset
- \- *theorem* list.range'_append
- \- *theorem* list.range'_concat
- \- *theorem* list.range'_eq_map_range
- \- *theorem* list.range'_sublist_right
- \- *theorem* list.range'_subset_right
- \- *theorem* list.range_concat
- \- *theorem* list.range_core_range'
- \- *theorem* list.range_eq_range'
- \- *theorem* list.range_sublist
- \- *theorem* list.range_subset
- \- *theorem* list.range_succ_eq_map
- \- *lemma* list.rel_append
- \- *lemma* list.rel_bind
- \- *lemma* list.rel_filter
- \- *lemma* list.rel_filter_map
- \- *lemma* list.rel_foldl
- \- *lemma* list.rel_foldr
- \- *lemma* list.rel_join
- \- *lemma* list.rel_map
- \- *lemma* list.rel_mem
- \- *lemma* list.rel_nodup
- \- *theorem* list.rel_of_chain_cons
- \- *theorem* list.rel_of_pairwise_cons
- \- *lemma* list.rel_prod
- \- *lemma* list.rel_sections
- \- *theorem* list.reverse_range'
- \- *theorem* list.reverse_revzip
- \- *theorem* list.revzip_map_fst
- \- *theorem* list.revzip_map_snd
- \- *theorem* list.revzip_swap
- \- *lemma* list.right_unique_forall₂
- \- *lemma* list.rotate'_cons_succ
- \- *lemma* list.rotate'_eq_take_append_drop
- \- *lemma* list.rotate'_length
- \- *lemma* list.rotate'_length_mul
- \- *lemma* list.rotate'_mod
- \- *lemma* list.rotate'_nil
- \- *lemma* list.rotate'_rotate'
- \- *lemma* list.rotate'_zero
- \- *lemma* list.rotate_cons_succ
- \- *lemma* list.rotate_eq_rotate'
- \- *lemma* list.rotate_eq_take_append_drop
- \- *lemma* list.rotate_length
- \- *lemma* list.rotate_length_mul
- \- *lemma* list.rotate_mod
- \- *lemma* list.rotate_nil
- \- *lemma* list.rotate_rotate
- \- *lemma* list.rotate_zero
- \- *theorem* list.subset_erase_dup
- \- *theorem* list.tfae.out
- \- *theorem* list.tfae_cons_cons
- \- *theorem* list.tfae_cons_of_mem
- \- *theorem* list.tfae_nil
- \- *theorem* list.tfae_of_cycle
- \- *theorem* list.tfae_of_forall
- \- *theorem* list.tfae_singleton
- \- *theorem* list.unzip_cons
- \- *theorem* list.unzip_eq_map
- \- *theorem* list.unzip_left
- \- *theorem* list.unzip_nil
- \- *theorem* list.unzip_revzip
- \- *theorem* list.unzip_right
- \- *theorem* list.unzip_swap
- \- *theorem* list.unzip_zip
- \- *theorem* list.unzip_zip_left
- \- *theorem* list.unzip_zip_right
- \- *theorem* list.zip_append
- \- *theorem* list.zip_cons_cons
- \- *theorem* list.zip_map'
- \- *theorem* list.zip_map
- \- *theorem* list.zip_map_left
- \- *theorem* list.zip_map_right
- \- *theorem* list.zip_nil_left
- \- *theorem* list.zip_nil_right
- \- *theorem* list.zip_swap
- \- *theorem* list.zip_unzip
- \- *theorem* option.to_list_nodup

Added src/data/list/chain.lean
- \+ *theorem* list.chain'.cons
- \+ *theorem* list.chain'.iff
- \+ *theorem* list.chain'.iff_mem
- \+ *theorem* list.chain'.imp
- \+ *theorem* list.chain'.tail
- \+ *theorem* list.chain'_cons
- \+ *theorem* list.chain'_iff_pairwise
- \+ *theorem* list.chain'_map
- \+ *theorem* list.chain'_map_of_chain'
- \+ *theorem* list.chain'_nil
- \+ *theorem* list.chain'_of_chain'_map
- \+ *theorem* list.chain'_pair
- \+ *theorem* list.chain'_reverse
- \+ *theorem* list.chain'_singleton
- \+ *theorem* list.chain'_split
- \+ *theorem* list.chain.iff
- \+ *theorem* list.chain.iff_mem
- \+ *theorem* list.chain.imp'
- \+ *theorem* list.chain.imp
- \+ *theorem* list.chain_iff_pairwise
- \+ *theorem* list.chain_map
- \+ *theorem* list.chain_map_of_chain
- \+ *theorem* list.chain_of_chain_cons
- \+ *theorem* list.chain_of_chain_map
- \+ *theorem* list.chain_of_pairwise
- \+ *theorem* list.chain_singleton
- \+ *theorem* list.chain_split
- \+ *theorem* list.pairwise.chain'
- \+ *theorem* list.rel_of_chain_cons

Modified src/data/list/defs.lean
- \- *def* list.func.add
- \- *def* list.func.equiv
- \- *def* list.func.get
- \- *def* list.func.neg
- \- *def* list.func.pointwise
- \- *def* list.func.set
- \- *def* list.func.sub
- \- *def* list.tfae

Added src/data/list/erase_dup.lean
- \+ *theorem* list.erase_dup_append
- \+ *theorem* list.erase_dup_cons_of_mem'
- \+ *theorem* list.erase_dup_cons_of_mem
- \+ *theorem* list.erase_dup_cons_of_not_mem'
- \+ *theorem* list.erase_dup_cons_of_not_mem
- \+ *theorem* list.erase_dup_eq_self
- \+ *theorem* list.erase_dup_idempotent
- \+ *theorem* list.erase_dup_nil
- \+ *theorem* list.erase_dup_sublist
- \+ *theorem* list.erase_dup_subset
- \+ *theorem* list.mem_erase_dup
- \+ *theorem* list.nodup_erase_dup
- \+ *theorem* list.subset_erase_dup

Added src/data/list/forall2.lean
- \+ *lemma* list.bi_unique_forall₂
- \+ *theorem* list.filter_map_cons
- \+ *lemma* list.forall₂.flip
- \+ *theorem* list.forall₂.imp
- \+ *lemma* list.forall₂.mp
- \+ *lemma* list.forall₂_and_left
- \+ *theorem* list.forall₂_cons
- \+ *lemma* list.forall₂_cons_left_iff
- \+ *lemma* list.forall₂_cons_right_iff
- \+ *theorem* list.forall₂_drop
- \+ *theorem* list.forall₂_drop_append
- \+ *lemma* list.forall₂_eq_eq_eq
- \+ *theorem* list.forall₂_iff_zip
- \+ *theorem* list.forall₂_length_eq
- \+ *lemma* list.forall₂_map_left_iff
- \+ *lemma* list.forall₂_map_right_iff
- \+ *lemma* list.forall₂_nil_left_iff
- \+ *lemma* list.forall₂_nil_right_iff
- \+ *lemma* list.forall₂_refl
- \+ *lemma* list.forall₂_same
- \+ *theorem* list.forall₂_take
- \+ *theorem* list.forall₂_take_append
- \+ *theorem* list.forall₂_zip
- \+ *lemma* list.left_unique_forall₂
- \+ *lemma* list.rel_append
- \+ *lemma* list.rel_bind
- \+ *lemma* list.rel_filter
- \+ *lemma* list.rel_filter_map
- \+ *lemma* list.rel_foldl
- \+ *lemma* list.rel_foldr
- \+ *lemma* list.rel_join
- \+ *lemma* list.rel_map
- \+ *lemma* list.rel_mem
- \+ *lemma* list.rel_prod
- \+ *lemma* list.right_unique_forall₂

Added src/data/list/func.lean
- \+ *def* list.func.add
- \+ *lemma* list.func.add_nil
- \+ *lemma* list.func.eq_get_of_mem
- \+ *lemma* list.func.eq_of_equiv
- \+ *def* list.func.equiv
- \+ *lemma* list.func.equiv_of_eq
- \+ *lemma* list.func.equiv_refl
- \+ *lemma* list.func.equiv_symm
- \+ *lemma* list.func.equiv_trans
- \+ *lemma* list.func.forall_val_of_forall_mem
- \+ *def* list.func.get
- \+ *lemma* list.func.get_add
- \+ *lemma* list.func.get_eq_default_of_le
- \+ *lemma* list.func.get_map'
- \+ *lemma* list.func.get_map
- \+ *lemma* list.func.get_neg
- \+ *lemma* list.func.get_nil
- \+ *lemma* list.func.get_pointwise
- \+ *lemma* list.func.get_set
- \+ *lemma* list.func.get_set_eq_of_ne
- \+ *lemma* list.func.get_sub
- \+ *lemma* list.func.length_add
- \+ *lemma* list.func.length_neg
- \+ *lemma* list.func.length_pointwise
- \+ *lemma* list.func.length_set
- \+ *lemma* list.func.length_sub
- \+ *lemma* list.func.map_add_map
- \+ *lemma* list.func.mem_get_of_le
- \+ *lemma* list.func.mem_get_of_ne_zero
- \+ *def* list.func.neg
- \+ *lemma* list.func.nil_add
- \+ *lemma* list.func.nil_pointwise
- \+ *lemma* list.func.nil_sub
- \+ *def* list.func.pointwise
- \+ *lemma* list.func.pointwise_nil
- \+ *def* list.func.set
- \+ *def* list.func.sub
- \+ *lemma* list.func.sub_nil

Added src/data/list/intervals.lean
- \+ *lemma* list.Ico.append_consecutive
- \+ *lemma* list.Ico.bag_inter_consecutive
- \+ *theorem* list.Ico.chain'_succ
- \+ *theorem* list.Ico.eq_cons
- \+ *theorem* list.Ico.eq_empty_iff
- \+ *theorem* list.Ico.eq_nil_of_le
- \+ *lemma* list.Ico.filter_le
- \+ *lemma* list.Ico.filter_le_of_le
- \+ *lemma* list.Ico.filter_le_of_le_bot
- \+ *lemma* list.Ico.filter_le_of_top_le
- \+ *lemma* list.Ico.filter_lt
- \+ *lemma* list.Ico.filter_lt_of_ge
- \+ *lemma* list.Ico.filter_lt_of_le_bot
- \+ *lemma* list.Ico.filter_lt_of_top_le
- \+ *lemma* list.Ico.inter_consecutive
- \+ *theorem* list.Ico.length
- \+ *theorem* list.Ico.map_add
- \+ *theorem* list.Ico.map_sub
- \+ *theorem* list.Ico.mem
- \+ *theorem* list.Ico.nodup
- \+ *theorem* list.Ico.not_mem_top
- \+ *theorem* list.Ico.pairwise_lt
- \+ *theorem* list.Ico.pred_singleton
- \+ *theorem* list.Ico.self_empty
- \+ *theorem* list.Ico.succ_singleton
- \+ *theorem* list.Ico.succ_top
- \+ *lemma* list.Ico.trichotomy
- \+ *theorem* list.Ico.zero_bot
- \+ *def* list.Ico

Added src/data/list/nodup.lean
- \+ *theorem* list.count_eq_one_of_mem
- \+ *lemma* list.diff_eq_filter_of_nodup
- \+ *theorem* list.disjoint_of_nodup_append
- \+ *theorem* list.forall_mem_ne
- \+ *lemma* list.mem_diff_iff_of_nodup
- \+ *theorem* list.mem_erase_iff_of_nodup
- \+ *theorem* list.mem_erase_of_nodup
- \+ *theorem* list.nodup_append
- \+ *theorem* list.nodup_append_comm
- \+ *theorem* list.nodup_append_of_nodup
- \+ *theorem* list.nodup_attach
- \+ *theorem* list.nodup_bind
- \+ *theorem* list.nodup_concat
- \+ *theorem* list.nodup_cons
- \+ *theorem* list.nodup_cons_of_nodup
- \+ *theorem* list.nodup_diff
- \+ *theorem* list.nodup_erase_eq_filter
- \+ *theorem* list.nodup_erase_of_nodup
- \+ *theorem* list.nodup_filter
- \+ *theorem* list.nodup_filter_map
- \+ *theorem* list.nodup_iff_count_le_one
- \+ *theorem* list.nodup_iff_nth_le_inj
- \+ *theorem* list.nodup_iff_sublist
- \+ *theorem* list.nodup_insert
- \+ *theorem* list.nodup_inter_of_nodup
- \+ *theorem* list.nodup_join
- \+ *theorem* list.nodup_map
- \+ *theorem* list.nodup_map_iff
- \+ *theorem* list.nodup_map_on
- \+ *theorem* list.nodup_middle
- \+ *theorem* list.nodup_nil
- \+ *theorem* list.nodup_of_nodup_append_left
- \+ *theorem* list.nodup_of_nodup_append_right
- \+ *theorem* list.nodup_of_nodup_cons
- \+ *theorem* list.nodup_of_nodup_map
- \+ *theorem* list.nodup_of_sublist
- \+ *theorem* list.nodup_pmap
- \+ *theorem* list.nodup_product
- \+ *theorem* list.nodup_repeat
- \+ *theorem* list.nodup_reverse
- \+ *theorem* list.nodup_sigma
- \+ *theorem* list.nodup_singleton
- \+ *theorem* list.nodup_sublists'
- \+ *theorem* list.nodup_sublists
- \+ *lemma* list.nodup_sublists_len
- \+ *theorem* list.nodup_union
- \+ *lemma* list.nodup_update_nth
- \+ *theorem* list.not_mem_of_nodup_cons
- \+ *theorem* list.not_nodup_cons_of_mem
- \+ *theorem* list.not_nodup_pair
- \+ *theorem* list.nth_le_index_of
- \+ *lemma* list.rel_nodup
- \+ *theorem* option.to_list_nodup

Added src/data/list/of_fn.lean
- \+ *theorem* list.array_eq_of_fn
- \+ *theorem* list.length_of_fn
- \+ *theorem* list.length_of_fn_aux
- \+ *theorem* list.nth_le_of_fn
- \+ *theorem* list.nth_of_fn
- \+ *theorem* list.nth_of_fn_aux
- \+ *theorem* list.of_fn_nth_le
- \+ *theorem* list.of_fn_succ
- \+ *theorem* list.of_fn_zero

Added src/data/list/pairwise.lean
- \+ *theorem* list.forall_mem_pw_filter
- \+ *theorem* list.forall_of_forall_of_pairwise
- \+ *lemma* list.forall_of_pairwise
- \+ *theorem* list.pairwise.and
- \+ *theorem* list.pairwise.and_mem
- \+ *theorem* list.pairwise.iff
- \+ *theorem* list.pairwise.iff_of_mem
- \+ *theorem* list.pairwise.imp
- \+ *theorem* list.pairwise.imp_mem
- \+ *theorem* list.pairwise.imp_of_mem
- \+ *theorem* list.pairwise.imp₂
- \+ *theorem* list.pairwise_append
- \+ *theorem* list.pairwise_append_comm
- \+ *theorem* list.pairwise_filter
- \+ *theorem* list.pairwise_filter_map
- \+ *theorem* list.pairwise_filter_map_of_pairwise
- \+ *theorem* list.pairwise_filter_of_pairwise
- \+ *theorem* list.pairwise_iff_nth_le
- \+ *theorem* list.pairwise_join
- \+ *theorem* list.pairwise_map
- \+ *theorem* list.pairwise_map_of_pairwise
- \+ *theorem* list.pairwise_middle
- \+ *theorem* list.pairwise_of_forall
- \+ *theorem* list.pairwise_of_pairwise_cons
- \+ *theorem* list.pairwise_of_pairwise_map
- \+ *theorem* list.pairwise_of_sublist
- \+ *theorem* list.pairwise_pair
- \+ *theorem* list.pairwise_pw_filter
- \+ *theorem* list.pairwise_reverse
- \+ *theorem* list.pairwise_singleton
- \+ *theorem* list.pairwise_sublists'
- \+ *theorem* list.pairwise_sublists
- \+ *theorem* list.pw_filter_cons_of_neg
- \+ *theorem* list.pw_filter_cons_of_pos
- \+ *theorem* list.pw_filter_eq_self
- \+ *theorem* list.pw_filter_idempotent
- \+ *theorem* list.pw_filter_map
- \+ *theorem* list.pw_filter_nil
- \+ *theorem* list.pw_filter_sublist
- \+ *theorem* list.pw_filter_subset
- \+ *theorem* list.rel_of_pairwise_cons

Modified src/data/list/perm.lean


Added src/data/list/range.lean
- \+ *theorem* list.chain_lt_range'
- \+ *theorem* list.chain_succ_range'
- \+ *theorem* list.enum_from_map_fst
- \+ *theorem* list.enum_map_fst
- \+ *def* list.fin_range
- \+ *theorem* list.iota_eq_reverse_range'
- \+ *lemma* list.length_fin_range
- \+ *theorem* list.length_iota
- \+ *theorem* list.length_range'
- \+ *theorem* list.length_range
- \+ *theorem* list.map_add_range'
- \+ *theorem* list.map_sub_range'
- \+ *lemma* list.mem_fin_range
- \+ *theorem* list.mem_iota
- \+ *theorem* list.mem_range'
- \+ *theorem* list.mem_range
- \+ *lemma* list.nodup_fin_range
- \+ *theorem* list.nodup_iota
- \+ *theorem* list.nodup_of_fn
- \+ *theorem* list.nodup_range'
- \+ *theorem* list.nodup_range
- \+ *theorem* list.not_mem_range_self
- \+ *lemma* list.nth_le_range
- \+ *theorem* list.nth_range'
- \+ *theorem* list.nth_range
- \+ *theorem* list.of_fn_eq_pmap
- \+ *theorem* list.pairwise_gt_iota
- \+ *theorem* list.pairwise_lt_range'
- \+ *theorem* list.pairwise_lt_range
- \+ *theorem* list.prod_range_succ
- \+ *theorem* list.range'_append
- \+ *theorem* list.range'_concat
- \+ *theorem* list.range'_eq_map_range
- \+ *theorem* list.range'_sublist_right
- \+ *theorem* list.range'_subset_right
- \+ *theorem* list.range_concat
- \+ *theorem* list.range_core_range'
- \+ *theorem* list.range_eq_range'
- \+ *theorem* list.range_sublist
- \+ *theorem* list.range_subset
- \+ *theorem* list.range_succ_eq_map
- \+ *theorem* list.reverse_range'

Added src/data/list/rotate.lean
- \+ *lemma* list.length_rotate'
- \+ *lemma* list.length_rotate
- \+ *lemma* list.mem_rotate
- \+ *lemma* list.prod_rotate_eq_one_of_prod_eq_one
- \+ *lemma* list.rotate'_cons_succ
- \+ *lemma* list.rotate'_eq_take_append_drop
- \+ *lemma* list.rotate'_length
- \+ *lemma* list.rotate'_length_mul
- \+ *lemma* list.rotate'_mod
- \+ *lemma* list.rotate'_nil
- \+ *lemma* list.rotate'_rotate'
- \+ *lemma* list.rotate'_zero
- \+ *lemma* list.rotate_cons_succ
- \+ *lemma* list.rotate_eq_rotate'
- \+ *lemma* list.rotate_eq_take_append_drop
- \+ *lemma* list.rotate_length
- \+ *lemma* list.rotate_length_mul
- \+ *lemma* list.rotate_mod
- \+ *lemma* list.rotate_nil
- \+ *lemma* list.rotate_rotate
- \+ *lemma* list.rotate_zero

Added src/data/list/sections.lean
- \+ *theorem* list.mem_sections
- \+ *theorem* list.mem_sections_length
- \+ *lemma* list.rel_sections

Modified src/data/list/sigma.lean


Added src/data/list/tfae.lean
- \+ *theorem* list.tfae.out
- \+ *def* list.tfae
- \+ *theorem* list.tfae_cons_cons
- \+ *theorem* list.tfae_cons_of_mem
- \+ *theorem* list.tfae_nil
- \+ *theorem* list.tfae_of_cycle
- \+ *theorem* list.tfae_of_forall
- \+ *theorem* list.tfae_singleton

Added src/data/list/zip.lean
- \+ *theorem* list.length_revzip
- \+ *theorem* list.length_zip
- \+ *theorem* list.mem_zip
- \+ *theorem* list.reverse_revzip
- \+ *theorem* list.revzip_map_fst
- \+ *theorem* list.revzip_map_snd
- \+ *theorem* list.revzip_swap
- \+ *theorem* list.unzip_cons
- \+ *theorem* list.unzip_eq_map
- \+ *theorem* list.unzip_left
- \+ *theorem* list.unzip_nil
- \+ *theorem* list.unzip_revzip
- \+ *theorem* list.unzip_right
- \+ *theorem* list.unzip_swap
- \+ *theorem* list.unzip_zip
- \+ *theorem* list.unzip_zip_left
- \+ *theorem* list.unzip_zip_right
- \+ *theorem* list.zip_append
- \+ *theorem* list.zip_cons_cons
- \+ *theorem* list.zip_map'
- \+ *theorem* list.zip_map
- \+ *theorem* list.zip_map_left
- \+ *theorem* list.zip_map_right
- \+ *theorem* list.zip_nil_left
- \+ *theorem* list.zip_nil_right
- \+ *theorem* list.zip_swap
- \+ *theorem* list.zip_unzip

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
- \+ *def* formal_multilinear_series.change_origin
- \+ *theorem* formal_multilinear_series.change_origin_eval
- \+ *lemma* formal_multilinear_series.change_origin_has_sum
- \+ *lemma* formal_multilinear_series.change_origin_radius
- \+ *lemma* formal_multilinear_series.change_origin_summable_aux1
- \+ *lemma* formal_multilinear_series.change_origin_summable_aux2
- \+ *lemma* formal_multilinear_series.change_origin_summable_aux3
- \+ *lemma* has_fpower_series_on_ball.analytic_at_of_mem
- \+ *theorem* has_fpower_series_on_ball.change_origin
- \+ *lemma* is_open_analytic_at

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


Modified src/algebra/floor.lean
- \+/\- *lemma* ceil_nonneg
- \+/\- *theorem* lt_nat_ceil
- \+/\- *theorem* nat_ceil_lt_add_one

Modified src/algebra/module.lean
- \+/\- *lemma* submodule.sum_mem

Modified src/algebra/order.lean
- \+/\- *lemma* decidable.eq_or_lt_of_le
- \+/\- *lemma* decidable.le_iff_le_iff_lt_iff_lt
- \+/\- *lemma* decidable.le_iff_lt_or_eq
- \+/\- *lemma* decidable.le_imp_le_iff_lt_imp_lt
- \+/\- *lemma* decidable.le_imp_le_of_lt_imp_lt
- \+/\- *lemma* decidable.le_of_not_lt
- \+/\- *lemma* decidable.le_or_lt
- \+/\- *lemma* decidable.lt_or_eq_of_le
- \+/\- *lemma* decidable.lt_or_gt_of_ne
- \+/\- *lemma* decidable.lt_or_le
- \+/\- *lemma* decidable.lt_trichotomy
- \+/\- *lemma* decidable.ne_iff_lt_or_gt
- \+/\- *lemma* decidable.not_lt

Modified src/algebra/pi_instances.lean
- \+/\- *lemma* finset.prod_apply

Modified src/analysis/convex/specific_functions.lean


Modified src/category_theory/graded_object.lean


Modified src/computability/halting.lean


Modified src/data/dfinsupp.lean
- \+/\- *lemma* dfinsupp.map_range_def
- \+/\- *lemma* dfinsupp.subtype_domain_sum
- \+/\- *lemma* dfinsupp.support_zip_with
- \+/\- *lemma* dfinsupp.zip_with_def

Modified src/data/equiv/denumerable.lean


Modified src/data/finset.lean
- \+/\- *lemma* finset.card_eq_of_bijective
- \+/\- *lemma* finset.card_le_card_of_inj_on
- \+/\- *lemma* finset.card_le_of_inj_on
- \+/\- *lemma* finset.disjoint_bind_left
- \+/\- *lemma* finset.disjoint_bind_right
- \+/\- *lemma* finset.fold_op_rel_iff_and
- \+/\- *lemma* finset.fold_op_rel_iff_or
- \+/\- *lemma* finset.singleton_bind
- \+/\- *lemma* finset.subset_image_iff
- \+/\- *lemma* finset.subset_union_elim

Modified src/data/hash_map.lean
- \+/\- *theorem* hash_map.valid.modify

Modified src/data/int/basic.lean
- \+/\- *theorem* int.div_eq_div_of_mul_eq_mul
- \+/\- *theorem* int.eq_mul_div_of_mul_eq_mul_of_dvd_left
- \+/\- *theorem* int.exists_greatest_of_bdd
- \+/\- *theorem* int.exists_least_of_bdd

Modified src/data/list/sigma.lean


Modified src/data/matrix/pequiv.lean
- \+/\- *lemma* pequiv.equiv_to_pequiv_to_matrix
- \+/\- *lemma* pequiv.matrix_mul_apply
- \+/\- *lemma* pequiv.mul_matrix_apply
- \+/\- *lemma* pequiv.single_mul_single
- \+/\- *lemma* pequiv.single_mul_single_of_ne
- \+/\- *lemma* pequiv.single_mul_single_right
- \+/\- *def* pequiv.to_matrix
- \+/\- *lemma* pequiv.to_matrix_bot
- \+/\- *lemma* pequiv.to_matrix_injective
- \+/\- *lemma* pequiv.to_matrix_refl
- \+/\- *lemma* pequiv.to_matrix_swap
- \+/\- *lemma* pequiv.to_matrix_symm
- \+/\- *lemma* pequiv.to_matrix_trans
- \+/\- *lemma* pequiv.to_pequiv_mul_matrix

Modified src/data/multiset.lean
- \+/\- *theorem* multiset.length_ndinsert_of_mem
- \+/\- *theorem* multiset.length_ndinsert_of_not_mem

Modified src/data/pequiv.lean
- \+/\- *lemma* pequiv.single_trans_of_eq_none
- \+/\- *lemma* pequiv.trans_single_of_eq_none

Modified src/data/rat/basic.lean


Modified src/data/real/basic.lean


Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.sum_lt_top
- \+/\- *lemma* ennreal.sum_lt_top_iff
- \+/\- *lemma* ennreal.to_nnreal_sum
- \+/\- *lemma* ennreal.to_real_sum

Modified src/data/set/basic.lean
- \+/\- *theorem* set.not_not_mem

Modified src/field_theory/finite.lean
- \+/\- *lemma* card_nth_roots_subgroup_units
- \+/\- *lemma* finite_field.card_units
- \+/\- *lemma* finite_field.pow_card_sub_one_eq_one
- \+/\- *lemma* finite_field.prod_univ_units_id_eq_neg_one

Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* order_of_pos

Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/finsupp.lean
- \+/\- *lemma* finsupp.supported_eq_span_single

Modified src/linear_algebra/multilinear.lean
- \+/\- *lemma* multilinear_map.sum_apply

Modified src/logic/basic.lean
- \+/\- *theorem* not_exists_not
- \+/\- *theorem* not_forall_not
- \+/\- *theorem* not_imp
- \+/\- *theorem* not_not

Modified src/ring_theory/adjoin.lean
- \+/\- *theorem* algebra.adjoin_eq_range
- \+/\- *theorem* algebra.adjoin_singleton_eq_range

Modified src/ring_theory/integral_closure.lean


Modified src/ring_theory/localization.lean


Modified src/ring_theory/multiplicity.lean
- \+/\- *lemma* multiplicity.finset.prod

Modified src/ring_theory/unique_factorization_domain.lean
- \+/\- *lemma* associates.factor_set.sup_add_inf_eq_add
- \+/\- *def* associates.{u}

Modified src/tactic/lint/default.lean


Modified src/tactic/lint/type_classes.lean


Modified src/tactic/monotonicity/lemmas.lean


Modified src/tactic/push_neg.lean
- \+/\- *lemma* imp_of_not_imp_not

Modified src/topology/algebra/multilinear.lean
- \+/\- *lemma* continuous_multilinear_map.sum_apply

Modified src/topology/separation.lean
- \+/\- *theorem* exists_open_singleton_of_fintype

Modified test/push_neg.lean




## [2020-04-08 15:10:31](https://github.com/leanprover-community/mathlib/commit/65a5dc0)
feat(data/support): define support of a function and prove some properties ([#2340](https://github.com/leanprover-community/mathlib/pull/2340))
* feat(data/support): define support of a function and prove some properties
* Add `support_mul'` for `group_with_zero`
#### Estimated changes
Modified src/data/indicator_function.lean
- \+ *lemma* set.support_indicator

Added src/data/support.lean
- \+ *lemma* function.nmem_support
- \+ *def* function.support
- \+ *lemma* function.support_add
- \+ *lemma* function.support_binop_subset
- \+ *lemma* function.support_comp'
- \+ *lemma* function.support_comp
- \+ *lemma* function.support_comp_eq'
- \+ *lemma* function.support_comp_eq
- \+ *lemma* function.support_div
- \+ *lemma* function.support_inf
- \+ *lemma* function.support_infi
- \+ *lemma* function.support_inv
- \+ *lemma* function.support_max
- \+ *lemma* function.support_min
- \+ *lemma* function.support_mul'
- \+ *lemma* function.support_mul
- \+ *lemma* function.support_neg
- \+ *lemma* function.support_prod
- \+ *lemma* function.support_sub
- \+ *lemma* function.support_sum
- \+ *lemma* function.support_sup
- \+ *lemma* function.support_supr



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
- \+ *lemma* list.head_add_tail_sum
- \+ *lemma* list.head_le_sum
- \+ *lemma* list.head_mul_tail_prod'
- \+ *lemma* list.tail_sum

Modified src/data/option/basic.lean
- \+ *lemma* option.get_or_else_some



## [2020-04-08 07:20:14](https://github.com/leanprover-community/mathlib/commit/cb8d8ac)
feat (data/list/basic): lemmas about prod and take ([#2345](https://github.com/leanprover-community/mathlib/pull/2345))
* feat (data/list/basic): lemmas about prod and take
* move lemma
* one more
* using to_additive properly
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.length_pos_of_prod_ne_one
- \+ *lemma* list.length_pos_of_sum_ne_zero
- \+ *lemma* list.length_pos_of_sum_pos
- \+ *lemma* list.prod_take_mul_prod_drop
- \+ *lemma* list.prod_take_succ
- \+ *lemma* list.sum_take_add_sum_drop
- \+ *lemma* list.sum_take_succ



## [2020-04-08 01:12:13](https://github.com/leanprover-community/mathlib/commit/732f710)
feat(data/list/basic): nth_le 0 = head ([#2350](https://github.com/leanprover-community/mathlib/pull/2350))
* feat(data/list/basic): nth_le 0 = head
* oops
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.nth_le_zero



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
- \- *def* cochain_complex.induced_map_on_cycles
- \+ *def* cochain_complex.kernel_functor
- \+ *def* cochain_complex.kernel_map
- \+ *lemma* cochain_complex.kernel_map_comp
- \+ *lemma* cochain_complex.kernel_map_condition
- \+ *lemma* cochain_complex.kernel_map_id

Modified src/category_theory/differential_object.lean
- \+ *lemma* category_theory.differential_object.zero_f

Modified src/category_theory/graded_object.lean
- \+ *lemma* category_theory.graded_object.zero_apply



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
- \+ *def* equiv.option_is_some_equiv

Modified src/measure_theory/ae_eq_fun.lean
- \+/\- *lemma* measure_theory.ae_eq_fun.smul_mk

Modified src/measure_theory/bochner_integration.lean


Modified src/measure_theory/borel_space.lean
- \+/\- *def* borel
- \- *lemma* borel_eq_subtype
- \+ *lemma* borel_eq_top_of_discrete
- \+ *lemma* borel_eq_top_of_encodable
- \- *lemma* borel_induced
- \- *lemma* borel_prod
- \- *lemma* borel_prod_le
- \+ *lemma* continuous.borel_measurable
- \+ *lemma* continuous.measurable2
- \+ *lemma* continuous.measurable
- \- *def* ennreal.ennreal_equiv_nnreal
- \- *lemma* ennreal.measurable.add
- \- *lemma* ennreal.measurable.mul
- \- *lemma* ennreal.measurable.sub
- \+ *lemma* finset.measurable_prod
- \+/\- *def* homemorph.to_measurable_equiv
- \+ *def* homeomorph.to_measurable_equiv
- \+ *lemma* is_closed.is_measurable
- \+/\- *lemma* is_measurable_Icc
- \+/\- *lemma* is_measurable_Ici
- \+/\- *lemma* is_measurable_Iic
- \+/\- *lemma* is_measurable_Iio
- \+/\- *lemma* is_measurable_Ioi
- \+/\- *lemma* is_measurable_Ioo
- \+/\- *lemma* is_measurable_ball
- \+ *lemma* is_measurable_closed_ball
- \+ *lemma* is_measurable_eball
- \+ *lemma* is_measurable_eq
- \+/\- *lemma* is_measurable_interior
- \+/\- *lemma* is_measurable_interval
- \+ *lemma* is_measurable_le'
- \+/\- *lemma* is_measurable_le
- \- *lemma* is_measurable_of_is_closed
- \- *lemma* is_measurable_of_is_open
- \+ *lemma* is_open.is_measurable
- \- *lemma* measurable.add
- \- *lemma* measurable.coe_nnnorm
- \+ *lemma* measurable.const_smul
- \+/\- *lemma* measurable.dist
- \+/\- *lemma* measurable.edist
- \+ *lemma* measurable.ennnorm
- \+ *lemma* measurable.ennreal_add
- \+ *lemma* measurable.ennreal_coe
- \+ *lemma* measurable.ennreal_mul
- \+ *lemma* measurable.ennreal_of_real
- \+ *lemma* measurable.ennreal_sub
- \- *lemma* measurable.infi
- \+/\- *lemma* measurable.infi_Prop
- \+ *lemma* measurable.inv'
- \+ *lemma* measurable.inv
- \+/\- *lemma* measurable.is_glb
- \+/\- *lemma* measurable.is_lub
- \+/\- *lemma* measurable.max
- \+/\- *lemma* measurable.min
- \+/\- *lemma* measurable.mul
- \- *lemma* measurable.neg
- \+/\- *lemma* measurable.nndist
- \+/\- *lemma* measurable.nnnorm
- \+ *lemma* measurable.nnreal_coe
- \+ *lemma* measurable.nnreal_of_real
- \+/\- *lemma* measurable.norm
- \+ *lemma* measurable.of_inv
- \- *lemma* measurable.smul'
- \+/\- *lemma* measurable.smul
- \+/\- *lemma* measurable.sub
- \+ *lemma* measurable.sub_nnreal
- \- *lemma* measurable.supr
- \+/\- *lemma* measurable.supr_Prop
- \+ *lemma* measurable_binfi
- \+ *lemma* measurable_bsupr
- \- *lemma* measurable_coe_int_real
- \+ *lemma* measurable_const_smul_iff
- \+/\- *lemma* measurable_dist
- \+/\- *lemma* measurable_edist
- \+ *def* measurable_equiv.ennreal_equiv_nnreal
- \- *lemma* measurable_finset_sum
- \+ *lemma* measurable_infi
- \+ *lemma* measurable_inv'
- \+ *lemma* measurable_inv
- \+ *lemma* measurable_inv_iff
- \+ *lemma* measurable_mul
- \- *lemma* measurable_neg_iff
- \+/\- *lemma* measurable_nndist
- \+/\- *lemma* measurable_nnnorm
- \+/\- *lemma* measurable_norm
- \- *lemma* measurable_of_continuous2
- \- *lemma* measurable_of_continuous
- \+ *lemma* measurable_of_continuous_on_compl_singleton
- \- *lemma* measurable_smul_iff
- \+ *lemma* measurable_supr
- \- *lemma* nnreal.measurable.add
- \- *lemma* nnreal.measurable.mul
- \- *lemma* nnreal.measurable.sub
- \- *lemma* nnreal.measurable_of_real
- \+ *lemma* prod_le_borel_prod

Modified src/measure_theory/category/Meas.lean


Modified src/measure_theory/giry_monad.lean


Modified src/measure_theory/indicator_function.lean


Modified src/measure_theory/integration.lean
- \+ *theorem* measure_theory.le_infi2_lintegral
- \+ *theorem* measure_theory.le_infi_lintegral
- \+ *lemma* measure_theory.lintegral_congr
- \+ *lemma* measure_theory.lintegral_infi
- \- *lemma* measure_theory.lintegral_le_lintegral
- \+ *lemma* measure_theory.lintegral_mono
- \+ *lemma* measure_theory.monotone_lintegral
- \+ *lemma* measure_theory.mul_volume_ge_le_lintegral
- \+/\- *lemma* measure_theory.simple_func.approx_apply
- \+/\- *lemma* measure_theory.simple_func.approx_comp
- \+ *theorem* measure_theory.supr2_lintegral_le
- \+ *theorem* measure_theory.supr_lintegral_le
- \+ *lemma* measure_theory.volume_ge_le_lintegral_div

Modified src/measure_theory/l1_space.lean
- \+/\- *lemma* measure_theory.ae_eq_fun.integrable.add
- \+/\- *lemma* measure_theory.ae_eq_fun.integrable.sub
- \+/\- *lemma* measure_theory.ae_eq_fun.integrable_mk
- \+/\- *lemma* measure_theory.integrable.add
- \+/\- *lemma* measure_theory.integrable.sub
- \+/\- *lemma* measure_theory.integrable_finset_sum
- \+/\- *lemma* measure_theory.l1.of_fun_smul
- \+/\- *def* measure_theory.l1
- \+/\- *lemma* measure_theory.lintegral_edist_lt_top
- \+/\- *lemma* measure_theory.lintegral_edist_triangle
- \+/\- *lemma* measure_theory.lintegral_nnnorm_add
- \+/\- *lemma* measure_theory.tendsto_lintegral_norm_of_dominated_convergence

Modified src/measure_theory/measurable_space.lean
- \+ *lemma* is_measurable.congr
- \+ *lemma* is_measurable.of_compl
- \+ *lemma* is_measurable.prod
- \- *lemma* is_measurable_set_prod
- \+ *lemma* measurable.mono
- \+ *lemma* measurable.subtype_coe
- \- *lemma* measurable.subtype_val
- \+ *lemma* measurable_from_top
- \+ *lemma* measurable_of_measurable_on_compl_singleton
- \+ *lemma* measurable_to_encodable
- \+ *lemma* subsingleton.is_measurable
- \+ *lemma* subsingleton.measurable

Modified src/measure_theory/set_integral.lean
- \+/\- *lemma* integrable_on.add
- \+/\- *lemma* integrable_on.sub
- \+/\- *lemma* integrable_on.union
- \+/\- *lemma* measurable_on_singleton

Modified src/measure_theory/simple_func_dense.lean


Modified src/order/complete_lattice.lean
- \+ *lemma* monotone.map_infi2_le
- \+ *lemma* monotone.map_infi_le
- \+ *lemma* monotone.map_supr2_ge
- \+ *lemma* monotone.map_supr_ge

Modified src/topology/homeomorph.lean
- \+ *def* homeomorph.set_congr

Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.continuous_on_to_nnreal
- \+ *def* ennreal.lt_top_homeomorph_nnreal
- \+ *def* ennreal.ne_top_homeomorph_nnreal



## [2020-04-07 12:40:05](https://github.com/leanprover-community/mathlib/commit/97c4302)
feat(data/list/basic): add map_take/drop_take ([#2344](https://github.com/leanprover-community/mathlib/pull/2344))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.map_drop
- \+ *lemma* list.map_take



## [2020-04-07 10:10:41](https://github.com/leanprover-community/mathlib/commit/2f2e016)
chore(data/list/basic): rename take_all -> take_length ([#2343](https://github.com/leanprover-community/mathlib/pull/2343))
* chore(data/list/basic): rename take_all -> take_length
* also rename drop_all
#### Estimated changes
Modified src/data/list/basic.lean
- \- *lemma* list.drop_all
- \+ *lemma* list.drop_length
- \- *theorem* list.take_all
- \+ *theorem* list.take_length



## [2020-04-07 08:48:42](https://github.com/leanprover-community/mathlib/commit/d936c28)
feat(data/real/nnreal): coe_max and coe_min ([#2346](https://github.com/leanprover-community/mathlib/pull/2346))
#### Estimated changes
Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.coe_max
- \+ *lemma* nnreal.coe_min



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
- \+/\- *lemma* finset.prod_comm
- \+/\- *lemma* finset.prod_sum
- \+/\- *lemma* finset.prod_union_inter
- \+/\- *lemma* finset.sum_le_sum_of_ne_zero

Modified src/data/finset.lean
- \+/\- *theorem* finset.filter_and
- \+/\- *theorem* finset.filter_not
- \+/\- *theorem* finset.filter_or
- \+/\- *theorem* finset.filter_union_filter_neg_eq

Modified src/linear_algebra/matrix.lean
- \+/\- *lemma* matrix.mul_to_lin
- \+/\- *lemma* matrix.rank_vec_mul_vec
- \+/\- *lemma* matrix.trace_mul_comm
- \+/\- *lemma* matrix.trace_transpose_mul



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
- \- *lemma* div_eq_div_iff
- \- *lemma* div_eq_iff
- \- *lemma* div_eq_iff_mul_eq
- \- *lemma* div_eq_inv_mul
- \- *lemma* div_eq_mul_inv
- \- *lemma* div_eq_zero_iff
- \- *lemma* div_mul_comm
- \- *lemma* div_mul_div_cancel
- \- *lemma* div_ne_zero
- \- *lemma* div_ne_zero_iff
- \- *lemma* div_right_inj
- \- *lemma* division_ring.inv_comm_of_comm
- \- *theorem* divp_eq_div
- \- *theorem* divp_mk0
- \- *lemma* eq_div_iff
- \- *lemma* field.div_div_cancel
- \- *lemma* field.div_div_div_cancel_right
- \- *lemma* field.div_right_comm
- \- *lemma* inv_div
- \- *lemma* inv_div_left
- \- *lemma* inv_eq_zero
- \- *lemma* inv_inv''
- \- *lemma* inv_involutive'
- \- *lemma* mul_comm_div
- \- *lemma* mul_div_comm
- \- *lemma* mul_div_right_comm
- \- *theorem* units.inv_eq_inv
- \- *def* units.mk0
- \- *lemma* units.mk0_coe
- \- *lemma* units.mk0_inj
- \- *theorem* units.mk0_val

Modified src/algebra/field_power.lean
- \- *def* fpow
- \- *lemma* fpow_add
- \- *lemma* fpow_eq_gpow
- \- *lemma* fpow_eq_zero
- \- *lemma* fpow_inv
- \- *lemma* fpow_mul
- \- *lemma* fpow_ne_zero_of_ne_zero
- \- *lemma* fpow_neg
- \- *theorem* fpow_neg_mul_fpow_self
- \- *lemma* fpow_neg_succ_of_nat
- \- *lemma* fpow_of_nat
- \- *lemma* fpow_one
- \- *lemma* fpow_sub
- \- *lemma* fpow_zero
- \- *lemma* mul_fpow
- \- *lemma* one_fpow
- \- *lemma* unit_pow
- \- *lemma* zero_fpow
- \- *lemma* zero_gpow

Modified src/algebra/geom_sum.lean


Modified src/algebra/group_power.lean
- \+/\- *def* add_monoid.smul
- \- *theorem* div_pow
- \- *lemma* div_sq_cancel
- \- *theorem* division_ring.inv_pow
- \- *lemma* inv_pow'
- \+/\- *def* monoid.pow
- \- *theorem* one_div_pow
- \- *lemma* pow_div
- \- *lemma* pow_inv

Added src/algebra/group_with_zero.lean
- \+ *lemma* coe_unit_inv_mul'
- \+ *lemma* coe_unit_mul_inv'
- \+ *lemma* div_div_cancel'
- \+ *lemma* div_div_div_cancel_right'
- \+ *lemma* div_div_div_div_eq'
- \+ *lemma* div_div_eq_div_mul'
- \+ *lemma* div_div_eq_mul_div'
- \+ *lemma* div_eq_div_iff
- \+ *lemma* div_eq_iff
- \+ *lemma* div_eq_iff_mul_eq
- \+ *lemma* div_eq_inv_mul'
- \+ *lemma* div_eq_mul_inv
- \+ *lemma* div_eq_mul_one_div'
- \+ *lemma* div_eq_zero_iff
- \+ *lemma* div_helper'
- \+ *lemma* div_mul_cancel'
- \+ *lemma* div_mul_comm'
- \+ *lemma* div_mul_div'
- \+ *lemma* div_mul_div_cancel'
- \+ *lemma* div_mul_eq_div_mul_one_div'
- \+ *lemma* div_mul_eq_mul_div'
- \+ *lemma* div_mul_eq_mul_div_comm'
- \+ *lemma* div_mul_left'
- \+ *lemma* div_mul_right'
- \+ *lemma* div_ne_zero
- \+ *lemma* div_ne_zero_iff
- \+ *lemma* div_one'
- \+ *lemma* div_right_comm'
- \+ *lemma* div_right_inj'
- \+ *lemma* div_self'
- \+ *lemma* div_zero'
- \+ *theorem* divp_eq_div
- \+ *theorem* divp_mk0
- \+ *lemma* eq_div_iff
- \+ *lemma* eq_inv_of_mul_left_eq_one'
- \+ *lemma* eq_inv_of_mul_right_eq_one'
- \+ *lemma* eq_mul_inv_of_mul_eq'
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_left'
- \+ *lemma* eq_of_mul_eq_mul_of_nonzero_right'
- \+ *lemma* eq_of_one_div_eq_one_div'
- \+ *lemma* eq_one_div_of_mul_eq_one'
- \+ *lemma* eq_one_div_of_mul_eq_one_left'
- \+ *lemma* eq_zero_of_one_div_eq_zero'
- \+ *theorem* inv_comm_of_comm'
- \+ *lemma* inv_div
- \+ *lemma* inv_div_left
- \+ *lemma* inv_eq_iff
- \+ *lemma* inv_eq_zero
- \+ *lemma* inv_inj''
- \+ *lemma* inv_injective'
- \+ *lemma* inv_inv''
- \+ *lemma* inv_involutive'
- \+ *lemma* inv_mul_cancel'
- \+ *lemma* inv_mul_cancel_assoc_left
- \+ *lemma* inv_mul_cancel_assoc_right
- \+ *lemma* inv_ne_zero'
- \+ *lemma* inv_one'
- \+ *lemma* inv_zero'
- \+ *lemma* mul_comm_div'
- \+ *lemma* mul_div_assoc''
- \+ *lemma* mul_div_cancel'''
- \+ *lemma* mul_div_cancel''
- \+ *lemma* mul_div_cancel_left'
- \+ *lemma* mul_div_comm
- \+ *lemma* mul_div_mul_left'
- \+ *lemma* mul_div_mul_right'
- \+ *lemma* mul_div_right_comm
- \+ *lemma* mul_eq_mul_of_div_eq_div'
- \+ *lemma* mul_eq_zero'
- \+ *lemma* mul_eq_zero_iff'
- \+ *lemma* mul_inv''
- \+ *lemma* mul_inv_cancel'
- \+ *lemma* mul_inv_cancel_assoc_left
- \+ *lemma* mul_inv_cancel_assoc_right
- \+ *lemma* mul_inv_eq_of_eq_mul'
- \+ *lemma* mul_inv_rev'
- \+ *lemma* mul_left_cancel'
- \+ *lemma* mul_ne_zero''
- \+ *lemma* mul_ne_zero_comm''
- \+ *lemma* mul_ne_zero_iff
- \+ *lemma* mul_one_div_cancel'
- \+ *lemma* mul_right_cancel'
- \+ *lemma* mul_right_inj'
- \+ *lemma* ne_zero_of_mul_left_eq_one'
- \+ *lemma* ne_zero_of_mul_right_eq_one'
- \+ *lemma* ne_zero_of_one_div_ne_zero'
- \+ *lemma* one_div
- \+ *lemma* one_div_div'
- \+ *lemma* one_div_mul_cancel'
- \+ *lemma* one_div_mul_one_div'
- \+ *lemma* one_div_mul_one_div_rev
- \+ *lemma* one_div_ne_zero'
- \+ *lemma* one_div_one'
- \+ *lemma* one_div_one_div'
- \+ *lemma* unit_ne_zero
- \+ *lemma* units.coe_mk0
- \+ *theorem* units.inv_eq_inv
- \+ *def* units.mk0
- \+ *lemma* units.mk0_coe
- \+ *lemma* units.mk0_inj
- \+ *lemma* zero_div'

Added src/algebra/group_with_zero_power.lean
- \+ *theorem* div_fpow
- \+ *theorem* div_pow
- \+ *lemma* div_sq_cancel
- \+ *def* fpow
- \+ *theorem* fpow_add
- \+ *theorem* fpow_add_one
- \+ *theorem* fpow_coe_nat
- \+ *lemma* fpow_eq_zero
- \+ *lemma* fpow_inv
- \+ *theorem* fpow_mul'
- \+ *theorem* fpow_mul
- \+ *theorem* fpow_mul_comm
- \+ *lemma* fpow_ne_zero
- \+ *lemma* fpow_ne_zero_of_ne_zero
- \+ *theorem* fpow_neg
- \+ *theorem* fpow_neg_mul_fpow_self
- \+ *theorem* fpow_neg_one
- \+ *theorem* fpow_neg_succ
- \+ *lemma* fpow_neg_succ_of_nat
- \+ *theorem* fpow_of_nat
- \+ *theorem* fpow_one
- \+ *theorem* fpow_one_add
- \+ *lemma* fpow_sub
- \+ *theorem* fpow_zero
- \+ *theorem* inv_fpow
- \+ *theorem* inv_pow'
- \+ *lemma* mul_fpow
- \+ *theorem* one_div_fpow
- \+ *theorem* one_div_pow
- \+ *theorem* one_fpow
- \+ *theorem* pow_eq_zero'
- \+ *theorem* pow_inv_comm'
- \+ *theorem* pow_ne_zero'
- \+ *theorem* pow_sub'
- \+ *lemma* unit_gpow
- \+ *lemma* unit_pow
- \+ *lemma* zero_fpow
- \+ *lemma* zero_pow'

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
- \+ *lemma* nnreal.ne_iff

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
- \+ *lemma* mv_polynomial.as_sum
- \+ *lemma* mv_polynomial.mem_support_not_mem_vars_zero
- \+ *def* mv_polynomial.pderivative.add_monoid_hom
- \+ *lemma* mv_polynomial.pderivative.add_monoid_hom_apply
- \+ *lemma* mv_polynomial.pderivative_eq_zero_of_not_mem_vars
- \+ *lemma* mv_polynomial.support_sum_monomial_coeff



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
- \+ *lemma* has_fpower_series_on_ball.tendsto_locally_uniformly_on'
- \+ *lemma* has_fpower_series_on_ball.tendsto_locally_uniformly_on
- \+ *lemma* has_fpower_series_on_ball.tendsto_uniformly_on'
- \+ *lemma* has_fpower_series_on_ball.tendsto_uniformly_on
- \+ *lemma* has_fpower_series_on_ball.uniform_geometric_approx
- \- *lemma* has_fpower_series_on_ball.uniform_limit

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.val_eq_coe

Modified src/topology/basic.lean
- \+ *lemma* filter.eventually.self_of_nhds

Modified src/topology/bounded_continuous_function.lean
- \- *lemma* continuous_at_of_locally_uniform_limit_of_continuous_at
- \- *lemma* continuous_of_locally_uniform_limit_of_continuous
- \- *lemma* continuous_of_uniform_limit_of_continuous
- \- *lemma* continuous_on_of_locally_uniform_limit_of_continuous_on
- \- *lemma* continuous_on_of_uniform_limit_of_continuous_on
- \- *lemma* continuous_within_at_of_locally_uniform_limit_of_continuous_within_at

Modified src/topology/continuous_on.lean
- \+ *lemma* filter.eventually.self_of_nhds_within

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.emetric_ball_nnreal
- \+ *lemma* metric.emetric_closed_ball_nnreal
- \+ *lemma* metric.tendsto_locally_uniformly_iff
- \+ *lemma* metric.tendsto_locally_uniformly_on_iff
- \+ *lemma* metric.tendsto_uniformly_iff
- \+ *lemma* metric.tendsto_uniformly_on_iff

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* emetric.tendsto_locally_uniformly_iff
- \+ *lemma* emetric.tendsto_locally_uniformly_on_iff
- \+ *lemma* emetric.tendsto_uniformly_iff
- \+ *lemma* emetric.tendsto_uniformly_on_iff

Modified src/topology/uniform_space/basic.lean
- \- *lemma* mem_nhds_uniformity_iff
- \+ *lemma* mem_nhds_uniformity_iff_left
- \+ *lemma* mem_nhds_uniformity_iff_right
- \+ *theorem* uniform.continuous_at_iff'_left
- \+ *theorem* uniform.continuous_at_iff'_right
- \+ *theorem* uniform.continuous_iff'_left
- \+ *theorem* uniform.continuous_iff'_right
- \+ *theorem* uniform.continuous_on_iff'_left
- \+ *theorem* uniform.continuous_on_iff'_right
- \+ *theorem* uniform.continuous_within_at_iff'_left
- \+ *theorem* uniform.continuous_within_at_iff'_right
- \+ *theorem* uniform.tendsto_nhds_left
- \+ *theorem* uniform.tendsto_nhds_right

Modified src/topology/uniform_space/cauchy.lean


Modified src/topology/uniform_space/separation.lean


Added src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* continuous_at_of_locally_uniform_approx_of_continuous_at
- \+ *lemma* continuous_of_locally_uniform_approx_of_continuous
- \+ *lemma* continuous_of_uniform_approx_of_continuous
- \+ *lemma* continuous_on_of_locally_uniform_approx_of_continuous_on
- \+ *lemma* continuous_on_of_uniform_approx_of_continuous_on
- \+ *lemma* continuous_within_at_of_locally_uniform_approx_of_continuous_within_at
- \+ *lemma* tendsto_comp_of_locally_uniform_limit
- \+ *lemma* tendsto_comp_of_locally_uniform_limit_within
- \+ *lemma* tendsto_locally_uniformly.comp
- \+ *lemma* tendsto_locally_uniformly.continuous
- \+ *lemma* tendsto_locally_uniformly.tendsto_comp
- \+ *def* tendsto_locally_uniformly
- \+ *lemma* tendsto_locally_uniformly_on.comp
- \+ *lemma* tendsto_locally_uniformly_on.continuous_on
- \+ *lemma* tendsto_locally_uniformly_on.mono
- \+ *lemma* tendsto_locally_uniformly_on.tendsto_comp
- \+ *def* tendsto_locally_uniformly_on
- \+ *lemma* tendsto_locally_uniformly_on_univ
- \+ *lemma* tendsto_uniformly.comp
- \+ *lemma* tendsto_uniformly.continuous
- \+ *lemma* tendsto_uniformly.tendsto_comp
- \+ *lemma* tendsto_uniformly.tendsto_locally_uniformly
- \+ *lemma* tendsto_uniformly.tendsto_uniformly_on
- \+ *def* tendsto_uniformly
- \+ *lemma* tendsto_uniformly_on.comp
- \+ *lemma* tendsto_uniformly_on.continuous_on
- \+ *lemma* tendsto_uniformly_on.mono
- \+ *lemma* tendsto_uniformly_on.tendsto_comp
- \+ *lemma* tendsto_uniformly_on.tendsto_locally_uniformly_on
- \+ *def* tendsto_uniformly_on
- \+ *lemma* tendsto_uniformly_on_univ



## [2020-04-06 12:39:52](https://github.com/leanprover-community/mathlib/commit/572fad1)
chore(topology/instances/ennreal): prove `tendsto_iff_edist_tendsto_0` ([#2333](https://github.com/leanprover-community/mathlib/pull/2333))
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* tendsto_iff_edist_tendsto_0



## [2020-04-06 10:15:13](https://github.com/leanprover-community/mathlib/commit/3d60e13)
chore(algebra/field): move some lemmas from `field` to `division_ring` ([#2331](https://github.com/leanprover-community/mathlib/pull/2331))
#### Estimated changes
Modified src/algebra/field.lean




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
- \+ *lemma* filter.eventually_comap
- \+ *lemma* filter.eventually_iff
- \+ *lemma* filter.eventually_map
- \+ *lemma* filter.eventually_of_mem
- \+ *lemma* filter.frequently_at_top'
- \+ *lemma* filter.frequently_comap
- \+ *lemma* filter.frequently_iff
- \+ *lemma* filter.frequently_map
- \+ *lemma* filter.inf_ne_bot_iff
- \+ *lemma* filter.inf_ne_bot_iff_frequently_left
- \+ *lemma* filter.inf_ne_bot_iff_frequently_right



## [2020-04-05 17:46:07](https://github.com/leanprover-community/mathlib/commit/26bf273)
feat(logic/embedding): embedding punit/prod ([#2315](https://github.com/leanprover-community/mathlib/pull/2315))
* feat(logic/embedding): embedding punit/prod
* renaming to sectl
* Revert disambiguations no longer needed
#### Estimated changes
Modified src/category_theory/products/basic.lean
- \- *def* category_theory.prod.inl
- \- *def* category_theory.prod.inr
- \+ *def* category_theory.prod.sectl
- \+ *def* category_theory.prod.sectr
- \+/\- *lemma* category_theory.prod_id_fst
- \+/\- *lemma* category_theory.prod_id_snd

Modified src/logic/embedding.lean
- \+ *lemma* function.embedding.equiv_symm_to_embedding_trans_to_embedding
- \+ *lemma* function.embedding.equiv_to_embedding_trans_symm_to_embedding
- \+ *def* function.embedding.punit
- \+ *def* function.embedding.sectl
- \+ *def* function.embedding.sectr



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
- \+ *lemma* continuous_multilinear_map.continuous_eval_left
- \+ *lemma* continuous_multilinear_map.has_sum_eval
- \+ *lemma* continuous_multilinear_map.norm_restr
- \+ *def* continuous_multilinear_map.restr
- \+ *lemma* multilinear_map.restr_norm_le

Modified src/linear_algebra/multilinear.lean
- \+ *lemma* multilinear_map.map_sum
- \+ *lemma* multilinear_map.map_sum_finset
- \+ *lemma* multilinear_map.map_sum_finset_aux
- \+ *lemma* multilinear_map.sum_apply

Modified src/topology/algebra/multilinear.lean
- \+ *lemma* continuous_multilinear_map.map_sum
- \+ *lemma* continuous_multilinear_map.map_sum_finset
- \+ *lemma* continuous_multilinear_map.sum_apply



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
- \+ *lemma* finsupp.add_sub_single_one
- \+ *lemma* finsupp.erase_add
- \+ *lemma* finsupp.erase_single
- \+ *lemma* finsupp.erase_single_ne
- \+ *lemma* finsupp.single_sub
- \+ *lemma* finsupp.sub_single_one_add

Modified src/data/mv_polynomial.lean
- \+ *theorem* mv_polynomial.induction_on'
- \+ *lemma* mv_polynomial.monomial_add
- \+ *lemma* mv_polynomial.monomial_mul
- \+ *lemma* mv_polynomial.monomial_zero
- \+ *def* mv_polynomial.pderivative
- \+ *lemma* mv_polynomial.pderivative_C
- \+ *lemma* mv_polynomial.pderivative_C_mul
- \+ *lemma* mv_polynomial.pderivative_add
- \+ *lemma* mv_polynomial.pderivative_monomial
- \+ *lemma* mv_polynomial.pderivative_monomial_mul
- \+ *lemma* mv_polynomial.pderivative_monomial_single
- \+ *lemma* mv_polynomial.pderivative_mul
- \+ *lemma* mv_polynomial.pderivative_zero
- \+ *lemma* mv_polynomial.single_eq_C_mul_X
- \+ *lemma* mv_polynomial.sum_monomial

Modified src/data/nat/basic.lean
- \+ *lemma* nat.add_succ_sub_one
- \+ *lemma* nat.succ_add_sub_one



## [2020-04-04 05:20:52](https://github.com/leanprover-community/mathlib/commit/906874e)
feat(category_theory): quotient categories ([#2310](https://github.com/leanprover-community/mathlib/pull/2310))
This constructs the quotient of a category by an arbitrary family of relations on its hom-sets. Analogous to "quotient of a group by the normal closure of a subset", as opposed to "quotient of a group by a normal subgroup".
The plan is to eventually use this together with the path category to construct the free groupoid on a graph.
#### Estimated changes
Added src/category_theory/quotient.lean
- \+ *def* category_theory.quotient.comp
- \+ *lemma* category_theory.quotient.comp_left
- \+ *lemma* category_theory.quotient.comp_mk
- \+ *lemma* category_theory.quotient.comp_right
- \+ *def* category_theory.quotient.functor
- \+ *def* category_theory.quotient.hom
- \+ *def* category_theory.quotient.lift.is_lift
- \+ *lemma* category_theory.quotient.lift.is_lift_hom
- \+ *lemma* category_theory.quotient.lift.is_lift_inv
- \+ *def* category_theory.quotient.lift



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
- \+/\- *lemma* is_unit.coe_lift_right
- \+ *lemma* is_unit.lift_right_inv_mul
- \+/\- *lemma* is_unit.map
- \+ *lemma* is_unit.mul_lift_right_inv
- \+/\- *theorem* is_unit_iff_exists_inv'
- \+/\- *theorem* is_unit_iff_exists_inv
- \+ *theorem* is_unit_of_mul_eq_one
- \- *theorem* is_unit_of_mul_one
- \+/\- *lemma* is_unit_unit

Modified src/algebra/group/units_hom.lean
- \+/\- *lemma* units.coe_lift_right
- \+ *lemma* units.lift_right_inv_mul
- \+ *lemma* units.mul_lift_right_inv

Modified src/group_theory/monoid_localization.lean
- \+ *lemma* submonoid.localization_map.comp_eq_of_eq
- \+ *lemma* submonoid.localization_map.comp_mul_equiv_symm_comap_apply
- \+ *lemma* submonoid.localization_map.comp_mul_equiv_symm_map_apply
- \+ *lemma* submonoid.localization_map.epic_of_localization_map
- \+/\- *theorem* submonoid.localization_map.eq_mk'_iff_mul_eq
- \+ *lemma* submonoid.localization_map.eq_of_eq
- \- *lemma* submonoid.localization_map.exists_of_sec
- \+/\- *lemma* submonoid.localization_map.exists_of_sec_mk'
- \+ *lemma* submonoid.localization_map.ext
- \+ *lemma* submonoid.localization_map.ext_iff
- \+/\- *lemma* submonoid.localization_map.inv_inj
- \+/\- *lemma* submonoid.localization_map.inv_unique
- \+ *lemma* submonoid.localization_map.is_unit_comp
- \+ *lemma* submonoid.localization_map.lift_comp
- \+ *lemma* submonoid.localization_map.lift_eq
- \+ *lemma* submonoid.localization_map.lift_eq_iff
- \+ *lemma* submonoid.localization_map.lift_id
- \+ *lemma* submonoid.localization_map.lift_injective_iff
- \+ *lemma* submonoid.localization_map.lift_left_inverse
- \+ *lemma* submonoid.localization_map.lift_mk'
- \+ *lemma* submonoid.localization_map.lift_mk'_spec
- \+ *lemma* submonoid.localization_map.lift_mul_left
- \+ *lemma* submonoid.localization_map.lift_mul_right
- \+ *lemma* submonoid.localization_map.lift_of_comp
- \+ *lemma* submonoid.localization_map.lift_spec
- \+ *lemma* submonoid.localization_map.lift_spec_mul
- \+ *lemma* submonoid.localization_map.lift_surjective_iff
- \+ *lemma* submonoid.localization_map.lift_unique
- \+ *lemma* submonoid.localization_map.map_comp
- \+ *lemma* submonoid.localization_map.map_comp_map
- \+ *lemma* submonoid.localization_map.map_eq
- \+ *lemma* submonoid.localization_map.map_id
- \+ *lemma* submonoid.localization_map.map_map
- \+ *lemma* submonoid.localization_map.map_mk'
- \+ *lemma* submonoid.localization_map.map_mul_left
- \+ *lemma* submonoid.localization_map.map_mul_right
- \+ *lemma* submonoid.localization_map.map_spec
- \+/\- *theorem* submonoid.localization_map.mk'_eq_iff_eq_mul
- \+/\- *lemma* submonoid.localization_map.mk'_mul
- \+/\- *lemma* submonoid.localization_map.mk'_mul_cancel_left
- \+/\- *lemma* submonoid.localization_map.mk'_mul_cancel_right
- \+/\- *lemma* submonoid.localization_map.mk'_mul_eq_mk'_of_mul
- \+/\- *lemma* submonoid.localization_map.mk'_sec
- \+ *lemma* submonoid.localization_map.mul_equiv_of_localizations_apply
- \+ *lemma* submonoid.localization_map.mul_equiv_of_localizations_symm_apply
- \+ *lemma* submonoid.localization_map.mul_equiv_of_mul_equiv_eq
- \+ *lemma* submonoid.localization_map.mul_equiv_of_mul_equiv_eq_map
- \+ *lemma* submonoid.localization_map.mul_equiv_of_mul_equiv_eq_map_apply
- \+ *lemma* submonoid.localization_map.mul_equiv_of_mul_equiv_mk'
- \+ *lemma* submonoid.localization_map.mul_equiv_of_to_mul_equiv
- \+ *lemma* submonoid.localization_map.mul_equiv_of_to_mul_equiv_apply
- \+/\- *lemma* submonoid.localization_map.mul_inv
- \+/\- *lemma* submonoid.localization_map.mul_inv_left
- \+/\- *lemma* submonoid.localization_map.mul_inv_right
- \+/\- *lemma* submonoid.localization_map.mul_mk'_eq_mk'_of_mul
- \+/\- *lemma* submonoid.localization_map.mul_mk'_one_eq_mk'
- \+ *def* submonoid.localization_map.of_mul_equiv
- \+ *lemma* submonoid.localization_map.of_mul_equiv_apply
- \+ *lemma* submonoid.localization_map.of_mul_equiv_eq
- \+ *lemma* submonoid.localization_map.of_mul_equiv_id
- \+/\- *lemma* submonoid.localization_map.sec_spec'
- \+/\- *lemma* submonoid.localization_map.sec_spec
- \+ *lemma* submonoid.localization_map.symm_of_mul_equiv_apply
- \+ *lemma* submonoid.localization_map.symm_to_mul_equiv_apply
- \+ *lemma* submonoid.localization_map.to_fun_inj
- \+ *def* submonoid.localization_map.to_mul_equiv
- \+ *lemma* submonoid.localization_map.to_mul_equiv_apply
- \+ *lemma* submonoid.localization_map.to_mul_equiv_comp
- \+ *lemma* submonoid.localization_map.to_mul_equiv_eq
- \+ *lemma* submonoid.localization_map.to_mul_equiv_eq_iff_eq
- \+ *lemma* submonoid.localization_map.to_mul_equiv_id
- \+ *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv
- \+ *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv_apply
- \+ *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv_of_mul_equiv
- \+ *lemma* submonoid.localization_map.to_mul_equiv_of_mul_equiv_of_mul_equiv_apply

Modified src/group_theory/submonoid.lean
- \+ *lemma* monoid_hom.restrict_eq

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
- \- *lemma* add_zero
- \- *lemma* zero_add_zero

Added src/tactic/lint/basic.lean


Added src/tactic/lint/default.lean


Added src/tactic/lint/frontend.lean


Added src/tactic/lint/misc.lean


Added src/tactic/lint/simp.lean
- \+ *lemma* add_zero
- \+ *lemma* zero_add_zero

Added src/tactic/lint/type_classes.lean


Modified test/lint.lean




## [2020-04-03 06:55:45](https://github.com/leanprover-community/mathlib/commit/cb0a1b5)
feat(order/filter): add lemmas about `∀ᶠ`, `∃ᶠ` and logic operations ([#2314](https://github.com/leanprover-community/mathlib/pull/2314))
* feat(order/filter): add lemmas about `∀ᶠ`, `∃ᶠ` and logic operations
* Remove `@[congr]`
* Apply suggestions from code review
Co-Authored-By: Gabriel Ebner <gebner@gebner.org>
#### Estimated changes
Modified src/measure_theory/measure_space.lean
- \+ *lemma* measure_theory.all_ae_and_iff
- \+ *lemma* measure_theory.all_ae_imp_distrib_left
- \+ *lemma* measure_theory.all_ae_or_distrib_left
- \+ *lemma* measure_theory.all_ae_or_distrib_right
- \+ *lemma* measure_theory.volume_zero_iff_all_ae_nmem

Modified src/order/filter/basic.lean
- \+/\- *lemma* filter.eventually.congr
- \- *lemma* filter.eventually.congr_iff
- \+ *lemma* filter.eventually_and
- \+ *lemma* filter.eventually_congr
- \+ *lemma* filter.eventually_const
- \+/\- *lemma* filter.eventually_false_iff_eq_bot
- \+ *lemma* filter.eventually_imp_distrib_left
- \+ *lemma* filter.eventually_imp_distrib_right
- \+ *lemma* filter.eventually_or_distrib_left
- \+ *lemma* filter.eventually_or_distrib_right
- \+/\- *lemma* filter.frequently_bot
- \+ *lemma* filter.frequently_const
- \+/\- *lemma* filter.frequently_false
- \+ *lemma* filter.frequently_imp_distrib
- \+ *lemma* filter.frequently_imp_distrib_left
- \+ *lemma* filter.frequently_imp_distrib_right
- \+ *lemma* filter.frequently_or_distrib
- \+ *lemma* filter.frequently_or_distrib_left
- \+ *lemma* filter.frequently_or_distrib_right
- \+/\- *lemma* filter.frequently_true_iff_ne_bot

Modified src/order/liminf_limsup.lean




## [2020-04-03 04:11:38](https://github.com/leanprover-community/mathlib/commit/1b24e0a)
chore(test/*): move tests into individual files ([#2317](https://github.com/leanprover-community/mathlib/pull/2317))
#### Estimated changes
Added test/back_chaining.lean
- \+ *theorem* inter_def
- \+ *theorem* subset_def
- \+ *theorem* subset_inter
- \+ *theorem* union_def
- \+ *theorem* union_subset

Added test/choose.lean


Modified test/coinductive.lean


Modified test/examples.lean
- \- *def* ex
- \- *theorem* inter_def
- \- *theorem* subset_def
- \- *theorem* subset_inter
- \- *theorem* union_def
- \- *theorem* union_subset
- \- *def* x

Modified test/ext.lean
- \- *def* my_bar
- \- *def* my_foo

Added test/refine_struct.lean
- \+ *def* my_bar
- \+ *def* my_foo

Added test/traversable.lean
- \+ *def* ex
- \+ *def* x



## [2020-04-02 19:25:32](https://github.com/leanprover-community/mathlib/commit/d3b8622)
fix(tactic/lint): simp_nf: do not ignore errors ([#2266](https://github.com/leanprover-community/mathlib/pull/2266))
This PR fixes some bugs in the `simp_nf` linter.  Previously it ignored all errors (from failing tactics).  I've changed this so that errors from linters are handled centrally and reported as linter warnings.  The `simp_is_conditional` function was also broken.
As usual, new linters find new issues:
 1. Apparently Lean sometimes throws away simp lemmas.  https://github.com/leanprover-community/lean/issues/163
 2. Some types define `has_coe` but have an incorrect `has_coe_to_fun`, causing the simplifier to loop `⇑f a = ⇑↑f a = ⇑f a`.  See the new library note:
#### Estimated changes
Modified src/algebra/field.lean
- \+/\- *lemma* is_ring_hom.map_eq_zero
- \+/\- *lemma* is_ring_hom.map_ne_zero

Modified src/category_theory/monoidal/functorial.lean


Modified src/data/indicator_function.lean
- \+/\- *lemma* set.indicator_apply

Modified src/data/set/basic.lean
- \+/\- *theorem* set.ne_empty_iff_nonempty

Modified src/linear_algebra/basic.lean


Modified src/logic/basic.lean


Modified src/order/order_iso.lean
- \+ *lemma* order_iso.coe_coe_fn
- \- *theorem* order_iso.coe_coe_fn

Modified src/set_theory/ordinal.lean
- \- *theorem* initial_seg.of_iso_apply

Modified src/tactic/core.lean


Modified src/tactic/lint.lean


Modified src/topology/algebra/module.lean


Modified src/topology/basic.lean
- \- *lemma* subsingleton.is_closed
- \- *lemma* subsingleton.is_open

Modified src/topology/order.lean
- \+ *lemma* is_closed_discrete



## [2020-04-02 16:19:33](https://github.com/leanprover-community/mathlib/commit/654533f)
feat(logic/basic): a few lemmas about `exists_unique` ([#2283](https://github.com/leanprover-community/mathlib/pull/2283))
The goal is to be able to deal with formulas like `∃! x ∈ s, p x`. Lean parses them as `∃! x, ∃! (hx : x ∈ s), p x`. While this is equivalent to `∃! x, x ∈ s ∧ p x`, it is not defeq to this formula.
#### Estimated changes
Modified src/logic/basic.lean
- \+ *lemma* exists_unique.elim2
- \+ *lemma* exists_unique.exists2
- \+ *lemma* exists_unique.exists
- \+ *lemma* exists_unique.intro2
- \+ *lemma* exists_unique.unique2
- \+ *lemma* exists_unique.unique
- \+ *lemma* exists_unique_iff_exists



## [2020-04-02 13:55:30](https://github.com/leanprover-community/mathlib/commit/a88356f)
chore(topology/metric_space): use dot notation ([#2313](https://github.com/leanprover-community/mathlib/pull/2313))
* in `continuous.dist` and `continuous.edist`;
* in `tendsto.dist` and `tendsto.edist`.
#### Estimated changes
Modified src/measure_theory/borel_space.lean


Modified src/topology/algebra/infinite_sum.lean


Modified src/topology/bounded_continuous_function.lean


Modified src/topology/instances/ennreal.lean
- \+ *theorem* continuous.edist
- \- *theorem* continuous_edist'
- \+/\- *theorem* continuous_edist
- \+ *theorem* filter.tendsto.edist
- \- *theorem* tendsto_edist

Modified src/topology/metric_space/basic.lean
- \+ *theorem* continuous.dist
- \+ *lemma* continuous.nndist
- \- *theorem* continuous_dist'
- \+/\- *theorem* continuous_dist
- \- *lemma* continuous_nndist'
- \+/\- *lemma* continuous_nndist
- \+ *theorem* filter.tendsto.dist
- \+ *theorem* filter.tendsto.nndist
- \- *theorem* tendsto_dist
- \- *lemma* tendsto_nndist'
- \- *lemma* uniform_continuous_nndist'
- \+ *lemma* uniform_continuous_nndist



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
- \+ *lemma* add_monoid_hom.functions_ext
- \+ *def* add_monoid_hom.single
- \+ *lemma* add_monoid_hom.single_apply
- \+ *lemma* finset.prod_apply
- \+ *lemma* finset.univ_sum_single
- \+ *def* monoid_hom.apply
- \+ *lemma* monoid_hom.apply_apply
- \+ *def* pi.single
- \+ *lemma* pi.single_eq_of_ne
- \+ *lemma* pi.single_eq_same
- \+ *def* ring_hom.apply
- \+ *lemma* ring_hom.apply_apply
- \+ *lemma* ring_hom.functions_ext



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
- \+/\- *def* category_theory.concrete_category.has_coe_to_sort
- \+/\- *def* category_theory.forget
- \+/\- *def* category_theory.forget₂
- \+/\- *def* category_theory.has_forget₂.mk'

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
- \+ *def* mv_polynomial.aeval
- \+ *lemma* mv_polynomial.aeval_C
- \+ *lemma* mv_polynomial.aeval_X
- \+ *theorem* mv_polynomial.aeval_def
- \+ *theorem* mv_polynomial.eval_unique

Modified src/data/polynomial.lean
- \+ *def* polynomial.aeval
- \+ *lemma* polynomial.aeval_C
- \+ *lemma* polynomial.aeval_X
- \+ *theorem* polynomial.aeval_def
- \+ *theorem* polynomial.eval_unique

Modified src/ring_theory/adjoin.lean


Modified src/ring_theory/algebra.lean
- \- *def* mv_polynomial.aeval
- \- *lemma* mv_polynomial.aeval_C
- \- *lemma* mv_polynomial.aeval_X
- \- *theorem* mv_polynomial.aeval_def
- \- *theorem* mv_polynomial.eval_unique
- \- *def* polynomial.aeval
- \- *lemma* polynomial.aeval_C
- \- *lemma* polynomial.aeval_X
- \- *theorem* polynomial.aeval_def
- \- *theorem* polynomial.eval_unique

Modified src/ring_theory/algebra_operations.lean


Modified src/ring_theory/free_comm_ring.lean




## [2020-04-02 03:27:11](https://github.com/leanprover-community/mathlib/commit/652fc17)
chore(data/set/lattice): add `set_of_exists` and `set_of_forall` ([#2312](https://github.com/leanprover-community/mathlib/pull/2312))
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *theorem* set.set_of_exists
- \+ *theorem* set.set_of_forall



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


Added src/tactic/transform_decl.lean


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
- \- *theorem* irr_add_rat_iff_irr
- \- *theorem* irr_mul_rat_iff_irr
- \- *theorem* irr_neg
- \- *theorem* irr_nrt_of_n_not_dvd_multiplicity
- \- *theorem* irr_nrt_of_notint_nrt
- \- *theorem* irr_of_irr_mul_self
- \- *theorem* irr_rat_add_iff_irr
- \- *theorem* irr_rat_add_of_irr
- \- *theorem* irr_sqrt_of_multiplicity_odd
- \- *theorem* irr_sqrt_of_prime
- \- *theorem* irr_sqrt_rat_iff
- \- *theorem* irr_sqrt_two
- \+ *theorem* irrational.add_cases
- \+ *theorem* irrational.add_rat
- \+ *theorem* irrational.div_cases
- \+ *theorem* irrational.mul_cases
- \+ *theorem* irrational.mul_rat
- \+ *theorem* irrational.of_add_rat
- \+ *theorem* irrational.of_fpow
- \+ *theorem* irrational.of_inv
- \+ *theorem* irrational.of_mul_rat
- \+ *theorem* irrational.of_mul_self
- \+ *theorem* irrational.of_neg
- \+ *theorem* irrational.of_one_div
- \+ *theorem* irrational.of_pow
- \+ *theorem* irrational.of_rat_add
- \+ *theorem* irrational.of_rat_div
- \+ *theorem* irrational.of_rat_mul
- \+ *theorem* irrational.of_rat_sub
- \+ *theorem* irrational.of_sub_rat
- \+ *theorem* irrational.rat_add
- \+ *theorem* irrational.rat_mul
- \+ *theorem* irrational.rat_sub
- \+ *theorem* irrational.sub_rat
- \+/\- *def* irrational
- \+ *theorem* irrational_add_rat_iff
- \+ *theorem* irrational_inv_iff
- \+ *theorem* irrational_neg_iff
- \+ *theorem* irrational_nrt_of_n_not_dvd_multiplicity
- \+ *theorem* irrational_nrt_of_notint_nrt
- \+ *theorem* irrational_rat_add_iff
- \+ *theorem* irrational_rat_sub_iff
- \+ *theorem* irrational_sqrt_of_multiplicity_odd
- \+ *theorem* irrational_sqrt_rat_iff
- \+ *theorem* irrational_sqrt_two
- \+ *theorem* irrational_sub_rat_iff
- \+ *theorem* nat.prime.irrational_sqrt
- \+ *lemma* rat.not_irrational



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
- \+/\- *lemma* is_linear_map.map_add
- \+/\- *lemma* is_linear_map.map_neg
- \+ *lemma* is_linear_map.map_smul
- \+/\- *lemma* is_linear_map.map_sub
- \+/\- *lemma* is_linear_map.map_zero
- \+/\- *def* linear_map.id



## [2020-04-01 06:47:48](https://github.com/leanprover-community/mathlib/commit/c7fb84b)
refactor(group_theory/submonoid): review API ([#2173](https://github.com/leanprover-community/mathlib/pull/2173))
The old API was mirroring the API for unbundled submonoids, while the
new one is based on the API of `submodule`.
Also move some facts about `monoid`/`group` structure on `M × N` to
`algebra/group/prod`.
#### Estimated changes
Modified src/algebra/free_monoid.lean
- \+ *lemma* free_monoid.comp_lift
- \+ *lemma* free_monoid.lift_apply
- \+ *lemma* free_monoid.lift_comp_of

Modified src/algebra/group/default.lean


Modified src/algebra/group/hom.lean
- \+ *lemma* monoid_hom.comp_id
- \+ *lemma* monoid_hom.id_comp

Added src/algebra/group/prod.lean
- \+ *lemma* monoid_hom.coe_fst
- \+ *lemma* monoid_hom.coe_prod_map
- \+ *lemma* monoid_hom.coe_snd
- \+ *lemma* monoid_hom.comp_coprod
- \+ *def* monoid_hom.coprod
- \+ *lemma* monoid_hom.coprod_apply
- \+ *lemma* monoid_hom.coprod_comp_inl
- \+ *lemma* monoid_hom.coprod_comp_inr
- \+ *lemma* monoid_hom.coprod_inl_inr
- \+ *lemma* monoid_hom.coprod_unique
- \+ *def* monoid_hom.fst
- \+ *lemma* monoid_hom.fst_comp_inl
- \+ *lemma* monoid_hom.fst_comp_inr
- \+ *lemma* monoid_hom.fst_comp_prod
- \+ *def* monoid_hom.inl
- \+ *lemma* monoid_hom.inl_apply
- \+ *def* monoid_hom.inr
- \+ *lemma* monoid_hom.inr_apply
- \+ *lemma* monoid_hom.prod_apply
- \+ *lemma* monoid_hom.prod_comp_prod_map
- \+ *def* monoid_hom.prod_map
- \+ *lemma* monoid_hom.prod_map_def
- \+ *lemma* monoid_hom.prod_unique
- \+ *def* monoid_hom.snd
- \+ *lemma* monoid_hom.snd_comp_inl
- \+ *lemma* monoid_hom.snd_comp_inr
- \+ *lemma* monoid_hom.snd_comp_prod
- \+ *lemma* prod.fst_inv
- \+ *lemma* prod.fst_mul
- \+ *lemma* prod.fst_mul_snd
- \+ *lemma* prod.fst_one
- \+ *lemma* prod.fst_sub
- \+ *lemma* prod.inv_mk
- \+ *lemma* prod.mk_mul_mk
- \+ *lemma* prod.mk_sub_mk
- \+ *lemma* prod.one_eq_mk
- \+ *lemma* prod.snd_inv
- \+ *lemma* prod.snd_mul
- \+ *lemma* prod.snd_one
- \+ *lemma* prod.snd_sub

Modified src/algebra/pi_instances.lean
- \- *lemma* prod.fst_inv
- \- *lemma* prod.fst_mul
- \- *lemma* prod.fst_one
- \- *lemma* prod.fst_sub
- \- *lemma* prod.inv_mk
- \- *lemma* prod.mk_mul_mk
- \- *lemma* prod.mk_sub_mk
- \- *def* prod.monoid_hom.fst
- \- *def* prod.monoid_hom.inl
- \- *def* prod.monoid_hom.inr
- \- *def* prod.monoid_hom.snd
- \- *lemma* prod.one_eq_mk
- \- *lemma* prod.snd_inv
- \- *lemma* prod.snd_mul
- \- *lemma* prod.snd_one
- \- *lemma* prod.snd_sub
- \- *def* submonoid.prod

Modified src/data/prod.lean
- \+ *lemma* prod.fst_injective
- \+ *lemma* prod.fst_surjective
- \+ *lemma* prod.snd_injective
- \+ *lemma* prod.snd_surjective

Modified src/group_theory/congruence.lean
- \+/\- *lemma* con.ker_lift_range_eq
- \+/\- *theorem* con.lift_range

Modified src/group_theory/submonoid.lean
- \- *theorem* add_monoid.closure'_singleton
- \- *lemma* add_submonoid.coe_smul
- \+ *lemma* add_submonoid.mem_closure_singleton
- \- *lemma* add_submonoid.multiples.self_mem
- \- *def* add_submonoid.multiples
- \- *lemma* add_submonoid.multiples_subset
- \+/\- *lemma* add_submonoid.smul_mem
- \+ *theorem* free_monoid.closure_range_of
- \- *def* monoid.closure'
- \- *theorem* monoid.closure'_le
- \- *theorem* monoid.closure'_mono
- \- *theorem* monoid.closure'_singleton
- \- *theorem* monoid.exists_list_of_mem_closure'
- \- *lemma* monoid.image_closure'
- \- *theorem* monoid.le_closure'
- \- *theorem* monoid.mem_closure'_union_iff
- \+ *lemma* monoid_hom.closure_preimage_le
- \+ *def* monoid_hom.cod_restrict
- \+ *lemma* monoid_hom.coe_mrange
- \+ *lemma* monoid_hom.coe_range_restrict
- \- *def* monoid_hom.comap
- \+ *def* monoid_hom.eq_mlocus
- \+ *lemma* monoid_hom.eq_of_eq_on_mdense
- \+ *lemma* monoid_hom.eq_of_eq_on_mtop
- \+ *lemma* monoid_hom.eq_on_mclosure
- \- *def* monoid_hom.map
- \+ *lemma* monoid_hom.map_mclosure
- \+ *lemma* monoid_hom.map_mrange
- \+ *lemma* monoid_hom.mem_mrange
- \+ *def* monoid_hom.mrange
- \+ *lemma* monoid_hom.mrange_top_iff_surjective
- \+ *lemma* monoid_hom.mrange_top_of_surjective
- \- *def* monoid_hom.range
- \- *def* monoid_hom.range_mk
- \+ *def* monoid_hom.range_restrict
- \- *lemma* monoid_hom.range_top_of_surjective
- \+/\- *def* monoid_hom.restrict
- \+ *lemma* monoid_hom.restrict_apply
- \- *def* monoid_hom.set_inclusion
- \- *def* monoid_hom.subtype_mk
- \- *lemma* submonoid.Inf_le'
- \- *def* submonoid.Union_of_directed
- \- *def* submonoid.bot
- \+ *lemma* submonoid.bot_prod_bot
- \+ *def* submonoid.closure
- \+ *lemma* submonoid.closure_Union
- \+ *lemma* submonoid.closure_empty
- \+ *lemma* submonoid.closure_eq
- \+ *lemma* submonoid.closure_eq_mrange
- \+ *lemma* submonoid.closure_eq_of_le
- \+ *lemma* submonoid.closure_induction
- \+ *lemma* submonoid.closure_le
- \+ *lemma* submonoid.closure_mono
- \+ *lemma* submonoid.closure_union
- \+ *lemma* submonoid.closure_univ
- \+ *lemma* submonoid.coe_Inf
- \+ *lemma* submonoid.coe_bot
- \+ *lemma* submonoid.coe_coe
- \+ *lemma* submonoid.coe_comap
- \+ *lemma* submonoid.coe_inf
- \+ *lemma* submonoid.coe_map
- \- *lemma* submonoid.coe_pow
- \+ *lemma* submonoid.coe_prod
- \+ *lemma* submonoid.coe_ssubset_coe
- \+ *lemma* submonoid.coe_subset_coe
- \+ *theorem* submonoid.coe_subtype
- \+ *lemma* submonoid.coe_top
- \+ *def* submonoid.comap
- \+ *lemma* submonoid.comap_comap
- \+ *lemma* submonoid.comap_inf
- \+ *lemma* submonoid.comap_infi
- \+ *lemma* submonoid.comap_top
- \+ *lemma* submonoid.exists_list_of_mem_closure
- \- *lemma* submonoid.finset_prod_mem
- \+ *lemma* submonoid.gc_map_comap
- \+ *def* submonoid.inclusion
- \- *def* submonoid.inf
- \- *lemma* submonoid.le_Inf'
- \+/\- *lemma* submonoid.le_def
- \+/\- *lemma* submonoid.list_prod_mem
- \+ *def* submonoid.map
- \+ *lemma* submonoid.map_bot
- \+ *lemma* submonoid.map_inl
- \+ *lemma* submonoid.map_inr
- \+ *lemma* submonoid.map_le_iff_le_comap
- \+ *lemma* submonoid.map_map
- \+ *lemma* submonoid.map_sup
- \+ *lemma* submonoid.map_supr
- \+ *lemma* submonoid.mem_Sup_of_directed_on
- \+ *lemma* submonoid.mem_closure
- \+ *lemma* submonoid.mem_closure_singleton
- \+/\- *lemma* submonoid.mem_coe
- \+ *lemma* submonoid.mem_comap
- \+/\- *lemma* submonoid.mem_inf
- \+ *lemma* submonoid.mem_map
- \+ *lemma* submonoid.mem_prod
- \+ *lemma* submonoid.mem_sup
- \+ *lemma* submonoid.mem_supr_of_directed
- \+ *def* submonoid.of
- \+/\- *lemma* submonoid.pow_mem
- \- *lemma* submonoid.powers.self_mem
- \- *def* submonoid.powers
- \- *lemma* submonoid.powers_subset
- \+ *def* submonoid.prod
- \+ *lemma* submonoid.prod_bot_sup_bot_prod
- \+ *def* submonoid.prod_equiv
- \+ *lemma* submonoid.prod_mono
- \+ *lemma* submonoid.prod_mono_left
- \+ *lemma* submonoid.prod_mono_right
- \+ *lemma* submonoid.prod_top
- \+ *lemma* submonoid.range_fst
- \+ *lemma* submonoid.range_inl'
- \+ *lemma* submonoid.range_inl
- \+ *lemma* submonoid.range_inl_sup_range_inr
- \+ *lemma* submonoid.range_inr'
- \+ *lemma* submonoid.range_inr
- \+ *lemma* submonoid.range_snd
- \+ *lemma* submonoid.range_subtype
- \+ *lemma* submonoid.subset_closure
- \+/\- *def* submonoid.subtype
- \- *theorem* submonoid.subtype_apply
- \- *lemma* submonoid.subtype_eq_val
- \+ *lemma* submonoid.sup_eq_range
- \+ *lemma* submonoid.top_prod
- \+ *lemma* submonoid.top_prod_top
- \- *def* submonoid.univ

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
- \+ *lemma* bit0_le_bit0
- \+ *lemma* bit0_lt_bit0
- \+ *lemma* bit1_le_bit1
- \+ *lemma* bit1_lt_bit1
- \+ *lemma* one_le_bit1
- \+ *lemma* one_lt_bit1
- \+ *lemma* zero_le_bit0
- \+ *lemma* zero_le_mul_left
- \+ *lemma* zero_le_mul_right
- \+ *lemma* zero_lt_bit0
- \+ *lemma* zero_lt_mul_left
- \+ *lemma* zero_lt_mul_right

Modified src/computability/partrec_code.lean


Modified src/data/nat/basic.lean
- \+ *lemma* nat.bit0_le_bit1_iff
- \+ *lemma* nat.bit0_lt_bit1_iff
- \+ *lemma* nat.bit1_le_bit0_iff
- \+ *lemma* nat.bit1_lt_bit0_iff
- \+ *def* nat.bit_cases
- \+ *lemma* nat.bit_le_bit1_iff
- \+ *lemma* nat.bit_le_bit_iff
- \+ *lemma* nat.bit_lt_bit_iff
- \+ *lemma* nat.one_le_bit0_iff
- \+ *lemma* nat.one_lt_bit0_iff

Modified src/data/real/pi.lean


