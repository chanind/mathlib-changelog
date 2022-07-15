## [2022-05-31 22:07:31](https://github.com/leanprover-community/mathlib/commit/bdf3e97)
chore(data/polynomial/laurent): remove unused case distinction ([#14490](https://github.com/leanprover-community/mathlib/pull/14490))
#### Estimated changes
Modified src/data/polynomial/laurent.lean




## [2022-05-31 20:07:53](https://github.com/leanprover-community/mathlib/commit/26a62b0)
fix(topology/algebra/module/multilinear): initialize simps projections ([#14495](https://github.com/leanprover-community/mathlib/pull/14495))
* `continuous_multilinear_map.smul_right` has a `simps` attribute, causing the generation of the simps projections for `continuous_multilinear_map`, but without specific support for apply. We now initialize the simps projections correctly.
* This fixes an error in the sphere eversion project
#### Estimated changes
Modified src/topology/algebra/module/multilinear.lean
- \+ *def* continuous_multilinear_map.simps.apply
- \+/\- *def* continuous_multilinear_map.smul_right
- \- *lemma* continuous_multilinear_map.smul_right_apply



## [2022-05-31 20:07:51](https://github.com/leanprover-community/mathlib/commit/9dc4b8e)
feat(algebra/group_power/basic): `a^2 = b^2 ↔ a = b ∨ a = -b` ([#14431](https://github.com/leanprover-community/mathlib/pull/14431))
Generalize `a ^ 2 = 1 ↔ a = 1 ∨ a = -1` to `ring` + `no_zero_divisors` and prove `a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b` under `comm_ring` + `no_zero_divisors`.
#### Estimated changes
Modified src/algebra/group_power/basic.lean
- \+/\- *lemma* eq_or_eq_neg_of_sq_eq_sq
- \+ *lemma* sq_eq_one_iff
- \+ *lemma* sq_eq_sq_iff_eq_or_eq_neg
- \+ *lemma* sq_ne_one_iff
- \+/\- *lemma* sq_sub_sq
- \- *lemma* units.eq_or_eq_neg_of_sq_eq_sq

Modified src/algebra/group_power/order.lean
- \- *lemma* sq_eq_one_iff
- \- *lemma* sq_ne_one_iff

Modified src/number_theory/legendre_symbol/quadratic_char.lean




## [2022-05-31 18:03:22](https://github.com/leanprover-community/mathlib/commit/8e522f8)
feat(algebra/order/monoid): Missing `has_exists_mul_of_le` instances ([#14476](https://github.com/leanprover-community/mathlib/pull/14476))
Add a few `has_exists_mul_of_le` instances, generalize `has_exists_mul_of_le` to `has_le` + `has_mul`.
#### Estimated changes
Modified src/algebra/order/monoid.lean


Modified src/algebra/order/pi.lean




## [2022-05-31 13:49:17](https://github.com/leanprover-community/mathlib/commit/e0b2ad8)
chore(algebra/lie/quotient): golf some instances ([#14480](https://github.com/leanprover-community/mathlib/pull/14480))
#### Estimated changes
Modified src/algebra/lie/quotient.lean
- \- *def* lie_submodule.quotient.action_as_endo_map_bracket
- \+/\- *lemma* lie_submodule.quotient.is_quotient_mk



## [2022-05-31 13:49:16](https://github.com/leanprover-community/mathlib/commit/806f673)
feat(algebra/star): star_single, star_update ([#14477](https://github.com/leanprover-community/mathlib/pull/14477))
#### Estimated changes
Modified src/algebra/star/pi.lean
- \+ *lemma* function.update_star
- \+ *lemma* pi.single_star



## [2022-05-31 11:57:57](https://github.com/leanprover-community/mathlib/commit/3e79ce4)
chore(combinatorics/simple_graph/basic): remove unnecessary lemma ([#14468](https://github.com/leanprover-community/mathlib/pull/14468))
This lemma was added in [#11371](https://github.com/leanprover-community/mathlib/pull/11371) for the Lean version bump, since the more powerful congr lemmas revealed a bug in fintype instances that were finally corrected in [#14136](https://github.com/leanprover-community/mathlib/pull/14136).
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \- *lemma* simple_graph.mem_neighbor_set'



## [2022-05-31 11:57:56](https://github.com/leanprover-community/mathlib/commit/1eb7339)
feat(topology/algebra/group): add `continuous_of_continuous_at_one` ([#14451](https://github.com/leanprover-community/mathlib/pull/14451))
This lemma is more general than
`uniform_continuous_of_continuous_at_one` because it allows the
codomain to be a monoid.
#### Estimated changes
Modified src/analysis/locally_convex/with_seminorms.lean


Modified src/topology/algebra/group.lean
- \+ *lemma* continuous_of_continuous_at_one

Modified src/topology/algebra/uniform_group.lean
- \+/\- *lemma* uniform_continuous_of_continuous_at_one



## [2022-05-31 11:57:55](https://github.com/leanprover-community/mathlib/commit/0f3e083)
feat(algebra/algebra/basic): relax typeclass assumptions ([#14415](https://github.com/leanprover-community/mathlib/pull/14415))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+/\- *lemma* no_zero_smul_divisors.algebra_map_injective
- \+/\- *lemma* no_zero_smul_divisors.iff_algebra_map_injective



## [2022-05-31 11:57:54](https://github.com/leanprover-community/mathlib/commit/346174e)
feat(data/polynomial/laurent): a Laurent polynomial can be multiplied by a power of `X` to "become" a polynomial ([#14106](https://github.com/leanprover-community/mathlib/pull/14106))
This PR proves two versions of the result mentioned in the title, one involving multiplying by a non-negative power of `T`, the other usable as an induction principle.
#### Estimated changes
Modified src/data/polynomial/laurent.lean
- \+ *lemma* laurent_polynomial.T_sub
- \+ *lemma* laurent_polynomial.exists_T_pow
- \+ *lemma* laurent_polynomial.induction_on_mul_T
- \+ *lemma* laurent_polynomial.reduce_to_polynomial_of_mul_T



## [2022-05-31 09:48:05](https://github.com/leanprover-community/mathlib/commit/87fbbd1)
chore(analysis/asymptotics): golf 2 proofs ([#14473](https://github.com/leanprover-community/mathlib/pull/14473))
Don't go back and forth between `∈ l` and `∀ᶠ l`.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean




## [2022-05-31 09:48:04](https://github.com/leanprover-community/mathlib/commit/9e9cc57)
feat(analysis/asymptotics/asymptotics): add `is_O_const_iff` ([#14472](https://github.com/leanprover-community/mathlib/pull/14472))
* use `f =ᶠ[l] 0` instead of `∀ᶠ x in l, f x = 0` in
  `is_{O_with,O,o}_zero_right_iff`;
* generalize these lemmas from `0` in a `normed_group` to `0` in a `semi_normed_group`;
* add `is_O.is_bounded_under_le`, `is_O_const_of_ne`, and `is_O_const_iff`.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* asymptotics.is_O.is_bounded_under_le
- \+ *theorem* asymptotics.is_O_const_iff
- \+ *theorem* asymptotics.is_O_const_of_ne
- \+/\- *theorem* asymptotics.is_O_zero_right_iff



## [2022-05-31 09:48:03](https://github.com/leanprover-community/mathlib/commit/615baba)
feat(order/monotone): prove `nat.exists_strict_mono` etc ([#14435](https://github.com/leanprover-community/mathlib/pull/14435))
* add `nat.exists_strict_mono`, `nat.exists_strict_anti`, `int.exists_strict_mono`, and `int.exists_strict_anti`;
* move `set.Iic.no_min_order` and `set.Ici.no_max_order` to `data.set.intervals.basic`;
* add `set.Iio.no_min_order` and `set.Ioi.no_max_order`;
* add `no_max_order.infinite` and `no_min_order.infinite`, use them in the proofs;
* rename `set.Ixx.infinite` to `set.Ixx_infinite`;
* add `set.Ixx.infinite` - lemmas and instances about `infinite`, not `set.infinite`.
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/basic.lean


Modified src/data/set/intervals/basic.lean


Modified src/data/set/intervals/infinite.lean
- \+ *lemma* no_max_order.infinite
- \+ *lemma* no_min_order.infinite
- \+/\- *lemma* set.Icc.infinite
- \+ *lemma* set.Icc_infinite
- \- *lemma* set.Ici.infinite
- \+ *lemma* set.Ici_infinite
- \+/\- *lemma* set.Ico.infinite
- \+ *lemma* set.Ico_infinite
- \- *lemma* set.Iic.infinite
- \+ *lemma* set.Iic_infinite
- \- *lemma* set.Iio.infinite
- \+ *lemma* set.Iio_infinite
- \+/\- *lemma* set.Ioc.infinite
- \+ *lemma* set.Ioc_infinite
- \- *lemma* set.Ioi.infinite
- \+ *lemma* set.Ioi_infinite
- \+/\- *lemma* set.Ioo.infinite
- \+ *lemma* set.Ioo_infinite

Modified src/order/lattice_intervals.lean


Modified src/order/monotone.lean
- \+ *lemma* int.exists_strict_anti
- \+ *lemma* int.exists_strict_mono
- \+ *lemma* nat.exists_strict_anti'
- \+ *lemma* nat.exists_strict_anti
- \+ *lemma* nat.exists_strict_mono'
- \+ *lemma* nat.exists_strict_mono



## [2022-05-31 09:48:01](https://github.com/leanprover-community/mathlib/commit/cafeaa3)
feat(data/set/lattice): add lemmas about unions over natural numbers ([#14393](https://github.com/leanprover-community/mathlib/pull/14393))
* Add `Union`/`Inter` versions of lemmas like `supr_ge_eq_supr_nat_add`.
* Make some arguments explicit.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* antitone.Inter_nat_add
- \+ *lemma* monotone.Union_nat_add
- \+ *lemma* set.Inter_ge_eq_Inter_nat_add
- \+ *lemma* set.Union_Inter_ge_nat_add
- \+ *lemma* set.Union_ge_eq_Union_nat_add
- \+ *lemma* set.inter_Inter_nat_succ
- \+ *lemma* set.union_Union_nat_succ

Modified src/order/complete_lattice.lean
- \+ *lemma* antitone.infi_nat_add
- \+/\- *lemma* infi_ge_eq_infi_nat_add
- \+/\- *lemma* supr_ge_eq_supr_nat_add



## [2022-05-31 09:48:00](https://github.com/leanprover-community/mathlib/commit/7127048)
feat(data/polynomial/*): `support_binomial` and `support_trinomial` lemmas ([#14385](https://github.com/leanprover-community/mathlib/pull/14385))
This PR adds lemmas for the support of binomials and trinomials. The trinomial lemmas will be helpful for irreducibility of x^n-x-1.
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.support_binomial'
- \+ *lemma* polynomial.support_trinomial'

Modified src/data/polynomial/coeff.lean
- \+ *lemma* polynomial.card_support_binomial
- \+ *lemma* polynomial.card_support_trinomial
- \+ *lemma* polynomial.support_binomial
- \+ *lemma* polynomial.support_trinomial



## [2022-05-31 09:47:59](https://github.com/leanprover-community/mathlib/commit/8315ad0)
refactor(group_theory/sylow): Move basic API earlier in the file ([#14367](https://github.com/leanprover-community/mathlib/pull/14367))
This PR moves some basic sylow API to earlier in the file, so that it can be used earlier.
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+/\- *lemma* sylow.coe_comap_of_injective
- \+/\- *lemma* sylow.coe_comap_of_ker_is_p_group
- \+/\- *lemma* sylow.coe_subtype
- \+/\- *def* sylow.comap_of_injective
- \+/\- *def* sylow.comap_of_ker_is_p_group
- \+/\- *def* sylow.subtype



## [2022-05-31 09:47:58](https://github.com/leanprover-community/mathlib/commit/111ce5b)
feat(group_theory/subgroup/basic): `comap_le_comap` lemmas ([#14365](https://github.com/leanprover-community/mathlib/pull/14365))
This PR adds some `comap_le_comap` lemmas.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.comap_le_comap_of_le_range
- \+ *lemma* subgroup.comap_le_comap_of_surjective
- \+ *lemma* subgroup.comap_lt_comap_of_surjective



## [2022-05-31 09:47:57](https://github.com/leanprover-community/mathlib/commit/1b49d48)
refactor(group_theory/order_of_element): Remove coercion in `order_eq_card_zpowers` ([#14364](https://github.com/leanprover-community/mathlib/pull/14364))
This PR removes a coercion in `order_eq_card_zpowers`.
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+/\- *lemma* order_eq_card_zpowers

Modified src/group_theory/specific_groups/cyclic.lean




## [2022-05-31 09:47:56](https://github.com/leanprover-community/mathlib/commit/6531c72)
chore(algebra/algebra/restrict_scalars): put a right action on restricted scalars ([#13996](https://github.com/leanprover-community/mathlib/pull/13996))
This provides `module Rᵐᵒᵖ (restrict_scalars R S M)` in terms of a `module Sᵐᵒᵖ M` action, by sending `Rᵐᵒᵖ` to `Sᵐᵒᵖ` through `algebra_map R S`.
This means that `restrict_scalars R S M` now works for right-modules and bi-modules in addition to left-modules.
This will become important if we change `algebra R A` to require `A` to be an `R`-bimodule, as otherwise `restrict_scalars R S A` would no longer be an algebra.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2313996.20right.20actions.20on.20restrict_scalars/near/282045994)
#### Estimated changes
Modified src/algebra/algebra/restrict_scalars.lean
- \+/\- *def* restrict_scalars.lsmul



## [2022-05-31 08:02:43](https://github.com/leanprover-community/mathlib/commit/876cb64)
feat({group,ring}_theory/sub{monoid,group,semiring,ring}): the action by the center is commutative ([#14362](https://github.com/leanprover-community/mathlib/pull/14362))
None of these `smul_comm_class` instances carry data, so they cannot form diamonds.
This action is used to golf the proofs in `quadratic_form.associated`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/center.lean


Modified src/linear_algebra/quadratic_form/basic.lean


Modified src/ring_theory/subring/basic.lean


Modified src/ring_theory/subsemiring/basic.lean




## [2022-05-30 23:53:46](https://github.com/leanprover-community/mathlib/commit/6633283)
fix(tactic/norm_num): fix ge unfolding bug ([#14425](https://github.com/leanprover-community/mathlib/pull/14425))
As reported on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/bug.20in.20norm_num.20handling.20of.20ge.3F).
#### Estimated changes
Modified src/tactic/norm_num.lean
- \+ *theorem* norm_num.ge_intro
- \+ *theorem* norm_num.gt_intro

Modified test/norm_num.lean




## [2022-05-30 22:37:30](https://github.com/leanprover-community/mathlib/commit/e7cc0eb)
feat(group_theory/perm/cycle): improve doc and namespace for cauchy's theorem ([#14471](https://github.com/leanprover-community/mathlib/pull/14471))
Fix a few things in the module docstring, remove namespace, add an additive version and add docstrings for Cauchy's theorem.
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Existence.20of.20elements.20of.20order.20p.20in.20a.20group/near/284399583
#### Estimated changes
Modified src/group_theory/p_group.lean


Modified src/group_theory/perm/cycle/type.lean
- \- *lemma* equiv.perm.exists_prime_order_of_dvd_card
- \+ *lemma* exists_prime_add_order_of_dvd_card
- \+ *lemma* exists_prime_order_of_dvd_card



## [2022-05-30 17:48:15](https://github.com/leanprover-community/mathlib/commit/ba22440)
feat(set_theory/cardinal/cofinality): use `bounded` and `unbounded` ([#14438](https://github.com/leanprover-community/mathlib/pull/14438))
We change `∀ a, ∃ b ∈ s, ¬ r b a` to its def-eq predicate `unbounded r s`, and similarly for `bounded r s`.
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean
- \+/\- *theorem* ordinal.cof_eq
- \+/\- *theorem* ordinal.cof_type_le
- \+/\- *theorem* ordinal.le_cof_type
- \+/\- *theorem* ordinal.lt_cof_type



## [2022-05-30 17:48:15](https://github.com/leanprover-community/mathlib/commit/1de757e)
feat(data/fin/basic): add `iff`lemmas about `nontrivial`/`subsingleton` ([#14390](https://github.com/leanprover-community/mathlib/pull/14390))
#### Estimated changes
Modified src/data/fin/basic.lean
- \+ *lemma* fin.nontrivial_iff_two_le
- \+ *lemma* fin.subsingleton_iff_le_one

Modified src/logic/nontrivial.lean
- \+ *lemma* not_nontrivial



## [2022-05-30 17:10:32](https://github.com/leanprover-community/mathlib/commit/1791ed3)
chore(ring_theory/polynomial/vieta): generalize universe ([#14411](https://github.com/leanprover-community/mathlib/pull/14411))
#### Estimated changes
Modified src/ring_theory/polynomial/vieta.lean




## [2022-05-30 17:10:31](https://github.com/leanprover-community/mathlib/commit/08c1412)
feat(set_theory/game/pgame): `lt_or_equiv_or_gf` ([#14407](https://github.com/leanprover-community/mathlib/pull/14407))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.lt_or_equiv_or_gf



## [2022-05-30 16:30:46](https://github.com/leanprover-community/mathlib/commit/59a1a50)
chore(analysis/normed_space/pi_Lp): add `pi_Lp.linear_equiv` ([#14380](https://github.com/leanprover-community/mathlib/pull/14380))
This is just a more bundled version of the `pi_Lp.equiv` we already have.
Also adds two missing simp lemmas about `pi_Lp.equiv`.
#### Estimated changes
Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* pi_Lp.equiv_single
- \+ *lemma* pi_Lp.equiv_symm_single

Modified src/analysis/normed_space/pi_Lp.lean




## [2022-05-30 13:47:58](https://github.com/leanprover-community/mathlib/commit/01af73a)
feat(alegbra/homology/short_exact/abelian.lean): Right split exact sequences + case of modules ([#14376](https://github.com/leanprover-community/mathlib/pull/14376))
A right split short exact sequence in an abelian category is split.
Also, in the case of the Module category, a version fully expressed in terms of modules and linear maps is provided.
#### Estimated changes
Modified src/algebra/category/Module/biproducts.lean


Modified src/algebra/homology/short_exact/abelian.lean
- \+ *def* category_theory.right_split.splitting
- \+ *def* category_theory.splitting.mk''



## [2022-05-30 12:53:32](https://github.com/leanprover-community/mathlib/commit/3641bf9)
refactor(algebraic_topology/*): use rw instead of erw where possible ([#14320](https://github.com/leanprover-community/mathlib/pull/14320))
#### Estimated changes
Modified src/algebraic_topology/alternating_face_map_complex.lean


Modified src/algebraic_topology/cech_nerve.lean


Modified src/algebraic_topology/dold_kan/homotopies.lean


Modified src/algebraic_topology/simplex_category.lean


Modified src/algebraic_topology/simplicial_object.lean




## [2022-05-30 11:01:47](https://github.com/leanprover-community/mathlib/commit/af70f8e)
feat(number_theory/bernoulli_polynomials): Added some lemmas ([#14282](https://github.com/leanprover-community/mathlib/pull/14282))
Have added some lemmas regarding rearrangements of sums and evaluations of Bernoulli polynomials.
#### Estimated changes
Modified src/data/polynomial/eval.lean
- \+ *lemma* polynomial.eval_monomial_one_add_sub

Modified src/number_theory/bernoulli_polynomials.lean
- \+ *lemma* polynomial.bernoulli_eq_sub_sum
- \+ *lemma* polynomial.bernoulli_eval_one_add
- \+ *lemma* polynomial.bernoulli_succ_eval
- \+ *lemma* polynomial.sum_range_pow_eq_bernoulli_sub



## [2022-05-30 04:06:04](https://github.com/leanprover-community/mathlib/commit/475f18b)
refactor(analysis/asymptotics): make `is_o`/`is_O` work with `calc` ([#14129](https://github.com/leanprover-community/mathlib/pull/14129))
Reorder arguments of `is_O_with`/`is_O`/`is_o` as well as `trans` lemmas so that they work with `calc`.
Also adds `f =O[l] g` notation.
Fixes [#2273](https://github.com/leanprover-community/mathlib/pull/2273)
#### Estimated changes
Modified src/analysis/analytic/basic.lean
- \+/\- *lemma* formal_multilinear_series.le_radius_of_is_O

Modified src/analysis/asymptotics/asymptotic_equivalent.lean
- \+/\- *lemma* asymptotics.is_equivalent.add_is_o
- \+/\- *lemma* asymptotics.is_equivalent.is_O
- \+/\- *lemma* asymptotics.is_equivalent.is_O_symm
- \+/\- *lemma* asymptotics.is_equivalent.is_o
- \+/\- *def* asymptotics.is_equivalent
- \+/\- *lemma* asymptotics.is_equivalent_zero_iff_is_O_zero
- \+/\- *lemma* asymptotics.is_o.is_equivalent

Modified src/analysis/asymptotics/asymptotics.lean
- \+/\- *theorem* asymptotics.bound_of_is_O_cofinite
- \+/\- *theorem* asymptotics.bound_of_is_O_nat_at_top
- \+/\- *theorem* asymptotics.is_O.add
- \+/\- *theorem* asymptotics.is_O.add_is_o
- \+/\- *lemma* asymptotics.is_O.bound
- \+/\- *theorem* asymptotics.is_O.comp_tendsto
- \+/\- *theorem* asymptotics.is_O.congr'
- \+/\- *theorem* asymptotics.is_O.congr
- \+/\- *theorem* asymptotics.is_O.congr_left
- \+/\- *theorem* asymptotics.is_O.congr_of_sub
- \+/\- *theorem* asymptotics.is_O.congr_right
- \+/\- *theorem* asymptotics.is_O.const_mul_left
- \+/\- *theorem* asymptotics.is_O.const_mul_right'
- \+/\- *theorem* asymptotics.is_O.const_mul_right
- \+/\- *lemma* asymptotics.is_O.eq_zero_imp
- \+/\- *lemma* asymptotics.is_O.eventually_mul_div_cancel
- \+/\- *lemma* asymptotics.is_O.exists_mem_basis
- \+/\- *theorem* asymptotics.is_O.exists_nonneg
- \+/\- *theorem* asymptotics.is_O.exists_pos
- \+/\- *theorem* asymptotics.is_O.inv_rev
- \+/\- *lemma* asymptotics.is_O.is_O_with
- \+/\- *theorem* asymptotics.is_O.join
- \+/\- *theorem* asymptotics.is_O.mono
- \+/\- *theorem* asymptotics.is_O.mul
- \+/\- *lemma* asymptotics.is_O.of_bound
- \+/\- *theorem* asymptotics.is_O.of_const_mul_right
- \+/\- *theorem* asymptotics.is_O.pow
- \+/\- *lemma* asymptotics.is_O.prod_left
- \+/\- *lemma* asymptotics.is_O.prod_left_fst
- \+/\- *lemma* asymptotics.is_O.prod_left_snd
- \+/\- *lemma* asymptotics.is_O.prod_rightl
- \+/\- *lemma* asymptotics.is_O.prod_rightr
- \+/\- *theorem* asymptotics.is_O.smul
- \+/\- *theorem* asymptotics.is_O.smul_is_o
- \+/\- *theorem* asymptotics.is_O.sub
- \+/\- *theorem* asymptotics.is_O.sum
- \+/\- *theorem* asymptotics.is_O.symm
- \+/\- *theorem* asymptotics.is_O.trans
- \+ *theorem* asymptotics.is_O.trans_eventually_eq
- \+/\- *theorem* asymptotics.is_O.trans_is_o
- \+/\- *theorem* asymptotics.is_O.trans_le
- \+/\- *theorem* asymptotics.is_O.trans_tendsto
- \+/\- *theorem* asymptotics.is_O.trans_tendsto_nhds
- \+/\- *theorem* asymptotics.is_O.triangle
- \+/\- *def* asymptotics.is_O
- \+/\- *theorem* asymptotics.is_O_bot
- \+/\- *theorem* asymptotics.is_O_comm
- \+/\- *theorem* asymptotics.is_O_congr
- \+/\- *theorem* asymptotics.is_O_const_mul_self
- \+/\- *theorem* asymptotics.is_O_const_one
- \+/\- *lemma* asymptotics.is_O_fst_prod'
- \+/\- *lemma* asymptotics.is_O_fst_prod
- \+/\- *lemma* asymptotics.is_O_iff
- \+/\- *lemma* asymptotics.is_O_iff_eventually
- \+/\- *lemma* asymptotics.is_O_iff_eventually_is_O_with
- \+/\- *lemma* asymptotics.is_O_iff_is_O_with
- \+/\- *theorem* asymptotics.is_O_map
- \+/\- *theorem* asymptotics.is_O_neg_left
- \+/\- *theorem* asymptotics.is_O_neg_right
- \+/\- *theorem* asymptotics.is_O_norm_left
- \+/\- *theorem* asymptotics.is_O_norm_norm
- \+/\- *theorem* asymptotics.is_O_norm_right
- \+/\- *theorem* asymptotics.is_O_of_le'
- \+/\- *theorem* asymptotics.is_O_of_le
- \+/\- *lemma* asymptotics.is_O_of_subsingleton
- \+/\- *lemma* asymptotics.is_O_principal
- \+/\- *lemma* asymptotics.is_O_prod_left
- \+/\- *lemma* asymptotics.is_O_pure
- \+/\- *theorem* asymptotics.is_O_refl
- \+/\- *theorem* asymptotics.is_O_refl_left
- \+/\- *lemma* asymptotics.is_O_snd_prod'
- \+/\- *lemma* asymptotics.is_O_snd_prod
- \+/\- *lemma* asymptotics.is_O_top
- \+/\- *theorem* asymptotics.is_O_with.add
- \+/\- *theorem* asymptotics.is_O_with.add_is_o
- \+/\- *theorem* asymptotics.is_O_with.comp_tendsto
- \+/\- *theorem* asymptotics.is_O_with.congr'
- \+/\- *theorem* asymptotics.is_O_with.congr
- \+/\- *theorem* asymptotics.is_O_with.congr_const
- \+/\- *theorem* asymptotics.is_O_with.congr_left
- \+/\- *theorem* asymptotics.is_O_with.congr_right
- \+/\- *theorem* asymptotics.is_O_with.const_mul_left
- \+/\- *theorem* asymptotics.is_O_with.const_smul_left
- \+/\- *lemma* asymptotics.is_O_with.eq_zero_imp
- \+/\- *lemma* asymptotics.is_O_with.eventually_mul_div_cancel
- \+/\- *lemma* asymptotics.is_O_with.exists_eq_mul
- \+/\- *theorem* asymptotics.is_O_with.exists_nonneg
- \+/\- *theorem* asymptotics.is_O_with.exists_pos
- \+/\- *theorem* asymptotics.is_O_with.inv_rev
- \+/\- *theorem* asymptotics.is_O_with.is_O
- \+/\- *theorem* asymptotics.is_O_with.join'
- \+/\- *theorem* asymptotics.is_O_with.join
- \+/\- *theorem* asymptotics.is_O_with.mono
- \+/\- *theorem* asymptotics.is_O_with.pow'
- \+/\- *theorem* asymptotics.is_O_with.pow
- \+/\- *lemma* asymptotics.is_O_with.prod_left
- \+/\- *lemma* asymptotics.is_O_with.prod_left_fst
- \+/\- *lemma* asymptotics.is_O_with.prod_left_same
- \+/\- *lemma* asymptotics.is_O_with.prod_left_snd
- \+/\- *lemma* asymptotics.is_O_with.prod_rightl
- \+/\- *lemma* asymptotics.is_O_with.prod_rightr
- \+/\- *theorem* asymptotics.is_O_with.right_le_add_of_lt_1
- \+/\- *theorem* asymptotics.is_O_with.right_le_sub_of_lt_1
- \+/\- *theorem* asymptotics.is_O_with.smul
- \+/\- *theorem* asymptotics.is_O_with.sub
- \+/\- *theorem* asymptotics.is_O_with.sub_is_o
- \+/\- *theorem* asymptotics.is_O_with.sum
- \+/\- *theorem* asymptotics.is_O_with.symm
- \+/\- *theorem* asymptotics.is_O_with.trans
- \+/\- *theorem* asymptotics.is_O_with.trans_is_o
- \+/\- *theorem* asymptotics.is_O_with.trans_le
- \+/\- *theorem* asymptotics.is_O_with.triangle
- \+/\- *theorem* asymptotics.is_O_with.weaken
- \+/\- *def* asymptotics.is_O_with
- \+/\- *theorem* asymptotics.is_O_with_bot
- \+/\- *theorem* asymptotics.is_O_with_congr
- \+/\- *theorem* asymptotics.is_O_with_const_one
- \+/\- *lemma* asymptotics.is_O_with_fst_prod
- \+/\- *lemma* asymptotics.is_O_with_iff
- \+/\- *theorem* asymptotics.is_O_with_neg_left
- \+/\- *theorem* asymptotics.is_O_with_neg_right
- \+/\- *theorem* asymptotics.is_O_with_norm_left
- \+/\- *theorem* asymptotics.is_O_with_norm_norm
- \+/\- *theorem* asymptotics.is_O_with_norm_right
- \+/\- *theorem* asymptotics.is_O_with_of_le'
- \+/\- *theorem* asymptotics.is_O_with_of_le
- \+/\- *theorem* asymptotics.is_O_with_pure
- \+/\- *theorem* asymptotics.is_O_with_refl
- \+/\- *lemma* asymptotics.is_O_with_snd_prod
- \+/\- *lemma* asymptotics.is_O_with_top
- \+/\- *theorem* asymptotics.is_O_with_zero'
- \+/\- *theorem* asymptotics.is_O_with_zero
- \+/\- *theorem* asymptotics.is_O_zero
- \+/\- *theorem* asymptotics.is_O_zero_right_iff
- \+/\- *theorem* asymptotics.is_o.add
- \+/\- *theorem* asymptotics.is_o.add_add
- \+/\- *theorem* asymptotics.is_o.add_is_O
- \+/\- *theorem* asymptotics.is_o.add_is_O_with
- \+/\- *theorem* asymptotics.is_o.comp_tendsto
- \+/\- *theorem* asymptotics.is_o.congr'
- \+/\- *theorem* asymptotics.is_o.congr
- \+/\- *theorem* asymptotics.is_o.congr_left
- \+/\- *theorem* asymptotics.is_o.congr_of_sub
- \+/\- *theorem* asymptotics.is_o.congr_right
- \+/\- *theorem* asymptotics.is_o.const_mul_left
- \+/\- *theorem* asymptotics.is_o.const_mul_right'
- \+/\- *theorem* asymptotics.is_o.const_mul_right
- \+/\- *lemma* asymptotics.is_o.def'
- \+/\- *lemma* asymptotics.is_o.def
- \+/\- *lemma* asymptotics.is_o.eventually_mul_div_cancel
- \+/\- *theorem* asymptotics.is_o.inv_rev
- \+/\- *theorem* asymptotics.is_o.is_O
- \+/\- *theorem* asymptotics.is_o.is_O_with
- \+/\- *theorem* asymptotics.is_o.join
- \+/\- *theorem* asymptotics.is_o.mono
- \+/\- *theorem* asymptotics.is_o.mul
- \+/\- *theorem* asymptotics.is_o.mul_is_O
- \+/\- *theorem* asymptotics.is_o.of_const_mul_right
- \+/\- *theorem* asymptotics.is_o.pow
- \+/\- *lemma* asymptotics.is_o.prod_left
- \+/\- *lemma* asymptotics.is_o.prod_left_fst
- \+/\- *lemma* asymptotics.is_o.prod_left_snd
- \+/\- *lemma* asymptotics.is_o.prod_rightl
- \+/\- *lemma* asymptotics.is_o.prod_rightr
- \+/\- *theorem* asymptotics.is_o.right_is_O_add
- \+/\- *theorem* asymptotics.is_o.right_is_O_sub
- \+/\- *theorem* asymptotics.is_o.smul
- \+/\- *theorem* asymptotics.is_o.smul_is_O
- \+/\- *theorem* asymptotics.is_o.sub
- \+/\- *theorem* asymptotics.is_o.sum
- \+/\- *theorem* asymptotics.is_o.symm
- \+/\- *theorem* asymptotics.is_o.tendsto_div_nhds_zero
- \+/\- *theorem* asymptotics.is_o.trans
- \+ *theorem* asymptotics.is_o.trans_eventually_eq
- \+/\- *theorem* asymptotics.is_o.trans_is_O
- \+/\- *theorem* asymptotics.is_o.trans_is_O_with
- \+/\- *theorem* asymptotics.is_o.trans_le
- \+/\- *theorem* asymptotics.is_o.trans_tendsto
- \+/\- *theorem* asymptotics.is_o.triangle
- \+/\- *def* asymptotics.is_o
- \+/\- *theorem* asymptotics.is_o_bot
- \+/\- *theorem* asymptotics.is_o_comm
- \+/\- *theorem* asymptotics.is_o_congr
- \+/\- *lemma* asymptotics.is_o_const_id_at_bot
- \+/\- *lemma* asymptotics.is_o_const_id_at_top
- \+/\- *lemma* asymptotics.is_o_const_id_comap_norm_at_top
- \+/\- *theorem* asymptotics.is_o_const_smul_left
- \+/\- *lemma* asymptotics.is_o_iff
- \+/\- *lemma* asymptotics.is_o_iff_forall_is_O_with
- \+/\- *theorem* asymptotics.is_o_iff_tendsto'
- \+/\- *theorem* asymptotics.is_o_iff_tendsto
- \+/\- *theorem* asymptotics.is_o_map
- \+/\- *theorem* asymptotics.is_o_neg_left
- \+/\- *theorem* asymptotics.is_o_neg_right
- \+/\- *theorem* asymptotics.is_o_norm_left
- \+/\- *theorem* asymptotics.is_o_norm_norm
- \+/\- *theorem* asymptotics.is_o_norm_right
- \+/\- *lemma* asymptotics.is_o_of_subsingleton
- \+/\- *theorem* asymptotics.is_o_one_iff
- \+/\- *lemma* asymptotics.is_o_prod_left
- \+/\- *lemma* asymptotics.is_o_pure
- \+/\- *theorem* asymptotics.is_o_refl_left
- \+/\- *lemma* asymptotics.is_o_top
- \+/\- *theorem* asymptotics.is_o_zero
- \+ *theorem* filter.eventually_eq.trans_is_O
- \+ *theorem* filter.eventually_eq.trans_is_o

Modified src/analysis/asymptotics/specific_asymptotics.lean
- \+/\- *lemma* filter.tendsto.cesaro

Modified src/analysis/asymptotics/superpolynomial_decay.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/fderiv_symmetric.lean


Modified src/analysis/complex/phragmen_lindelof.lean


Modified src/analysis/complex/removable_singularity.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+/\- *theorem* continuous_linear_equiv.is_O_comp
- \+/\- *theorem* continuous_linear_equiv.is_O_comp_rev
- \+/\- *theorem* continuous_linear_equiv.is_O_sub
- \+/\- *theorem* continuous_linear_equiv.is_O_sub_rev
- \+/\- *theorem* continuous_linear_map.is_O_id
- \+/\- *theorem* continuous_linear_map.is_O_with_id

Modified src/analysis/normed_space/spectrum.lean


Modified src/analysis/normed_space/units.lean
- \+/\- *lemma* normed_ring.inverse_add_norm
- \+/\- *lemma* normed_ring.inverse_one_sub_norm

Modified src/analysis/special_functions/exp.lean
- \+/\- *lemma* real.is_o_pow_exp_at_top

Modified src/analysis/special_functions/gamma.lean
- \- *lemma* dGamma_integrand_is_O_at_top
- \+ *lemma* dGamma_integrand_is_o_at_top
- \- *lemma* real.Gamma_integrand_is_O
- \+ *lemma* real.Gamma_integrand_is_o

Modified src/analysis/special_functions/log/basic.lean
- \+/\- *lemma* real.is_o_log_id_at_top
- \+/\- *lemma* real.is_o_pow_log_id_at_top

Modified src/analysis/special_functions/non_integrable.lean


Modified src/analysis/special_functions/polynomials.lean


Modified src/analysis/special_functions/pow.lean
- \+/\- *lemma* asymptotics.is_O.rpow
- \+/\- *lemma* asymptotics.is_O_with.rpow
- \+/\- *lemma* asymptotics.is_o.rpow
- \+/\- *lemma* is_o_log_rpow_at_top
- \+/\- *lemma* is_o_rpow_exp_at_top

Modified src/analysis/specific_limits/normed.lean


Modified src/combinatorics/additive/salem_spencer.lean
- \+/\- *lemma* roth_number_nat_is_O_id

Modified src/measure_theory/integral/exp_decay.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/set_integral.lean


Modified src/probability/strong_law.lean




## [2022-05-29 17:50:03](https://github.com/leanprover-community/mathlib/commit/55f32da)
feat(topology/vector_bundle): the pullback of a vector bundle is a vector bundle ([#8545](https://github.com/leanprover-community/mathlib/pull/8545))
We construct the pullback bundle of a vector bundle.
* Co-authored by: Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>
* Co-authored by: Floris van Doorn <fpvdoorn@gmail.com>
* Co-authored by: Sebastien Gouezel <sebastien.gouezel@univ-rennes1.fr>
#### Estimated changes
Modified src/data/bundle.lean
- \+ *def* bundle.pullback.lift
- \+ *lemma* bundle.pullback.lift_mk
- \+ *lemma* bundle.pullback.proj_lift
- \+ *def* bundle.pullback
- \+ *def* bundle.pullback_total_space_embedding
- \+ *lemma* bundle.pullback_total_space_embedding_snd
- \+/\- *def* bundle.trivial.proj_snd

Modified src/logic/equiv/local_equiv.lean
- \+ *lemma* local_equiv.eq_symm_apply

Modified src/logic/is_empty.lean


Modified src/topology/local_homeomorph.lean
- \+ *lemma* local_homeomorph.eq_symm_apply

Modified src/topology/order.lean
- \+ *lemma* continuous_empty_function

Modified src/topology/vector_bundle.lean
- \+ *lemma* inducing_pullback_total_space_embedding
- \+ *lemma* pullback.continuous_lift
- \+ *lemma* pullback.continuous_proj
- \+ *lemma* pullback.continuous_total_space_mk
- \+ *def* pullback_topology
- \+ *lemma* topological_vector_bundle.trivialization.open_target
- \+ *def* topological_vector_bundle.trivialization.pullback



## [2022-05-29 15:46:51](https://github.com/leanprover-community/mathlib/commit/938eeeb)
feat(algebra/group/with_one): add a recursor and a `no_zero_divisors` instance ([#14434](https://github.com/leanprover-community/mathlib/pull/14434))
#### Estimated changes
Modified src/algebra/group/with_one.lean
- \+ *def* with_one.rec_one_coe



## [2022-05-29 13:40:03](https://github.com/leanprover-community/mathlib/commit/b673ed8)
feat(analysis/normed_space): Geometric Hahn Banach theorems ([#7288](https://github.com/leanprover-community/mathlib/pull/7288))
This proves a range of variants of the Hahn-Banach separation theorems.
#### Estimated changes
Modified counterexamples/phillips.lean


Modified src/analysis/normed_space/dual.lean


Renamed src/analysis/normed_space/hahn_banach.lean to src/analysis/normed_space/hahn_banach/extension.lean


Added src/analysis/normed_space/hahn_banach/separation.lean
- \+ *theorem* geometric_hahn_banach_closed_compact
- \+ *theorem* geometric_hahn_banach_closed_point
- \+ *theorem* geometric_hahn_banach_compact_closed
- \+ *theorem* geometric_hahn_banach_open
- \+ *theorem* geometric_hahn_banach_open_open
- \+ *theorem* geometric_hahn_banach_open_point
- \+ *theorem* geometric_hahn_banach_point_closed
- \+ *theorem* geometric_hahn_banach_point_open
- \+ *theorem* geometric_hahn_banach_point_point
- \+ *lemma* separate_convex_open_set

Modified src/data/set/pointwise.lean




## [2022-05-29 11:50:46](https://github.com/leanprover-community/mathlib/commit/98b7637)
feat(category_theory/limits): monos have images ([#14186](https://github.com/leanprover-community/mathlib/pull/14186))
Turning on an instance for `has_image` for any monomorphism.
#### Estimated changes
Modified src/category_theory/limits/shapes/images.lean
- \+/\- *lemma* category_theory.limits.image.ext

Modified src/category_theory/subobject/limits.lean
- \+ *lemma* category_theory.limits.image_subobject_mono



## [2022-05-29 11:13:23](https://github.com/leanprover-community/mathlib/commit/8d13a2d)
feat(algebra/order/rearrangement): Equality case of the Rearrangement Inequality ([#13245](https://github.com/leanprover-community/mathlib/pull/13245))
This PR deduces the cases of equality and strict inequality of the Rearrangement Inequality as a corollary to the existing statement of the rearrangement inequality.
#### Estimated changes
Modified src/algebra/order/rearrangement.lean
- \+ *lemma* antivary.sum_mul_eq_sum_comp_perm_mul_iff
- \+ *lemma* antivary.sum_mul_eq_sum_mul_comp_perm_iff
- \+ *lemma* antivary.sum_mul_lt_sum_comp_perm_mul_iff
- \+ *lemma* antivary.sum_mul_lt_sum_mul_comp_perm_iff
- \+ *lemma* antivary.sum_smul_eq_sum_comp_perm_smul_iff
- \+ *lemma* antivary.sum_smul_eq_sum_smul_comp_perm_iff
- \+ *lemma* antivary.sum_smul_lt_sum_comp_perm_smul_iff
- \+ *lemma* antivary.sum_smul_lt_sum_smul_comp_perm_iff
- \+ *lemma* antivary_on.sum_mul_eq_sum_comp_perm_mul_iff
- \+ *lemma* antivary_on.sum_mul_eq_sum_mul_comp_perm_iff
- \+ *lemma* antivary_on.sum_mul_lt_sum_comp_perm_mul_iff
- \+ *lemma* antivary_on.sum_mul_lt_sum_mul_comp_perm_iff
- \+ *lemma* antivary_on.sum_smul_eq_sum_comp_perm_smul_iff
- \+ *lemma* antivary_on.sum_smul_eq_sum_smul_comp_perm_iff
- \+ *lemma* antivary_on.sum_smul_lt_sum_comp_perm_smul_iff
- \+ *lemma* antivary_on.sum_smul_lt_sum_smul_comp_perm_iff
- \+ *lemma* monovary.sum_comp_perm_mul_eq_sum_mul_iff
- \+ *lemma* monovary.sum_comp_perm_mul_lt_sum_mul_iff
- \+ *lemma* monovary.sum_comp_perm_smul_eq_sum_smul_iff
- \+ *lemma* monovary.sum_comp_perm_smul_lt_sum_smul_iff
- \+ *lemma* monovary.sum_mul_comp_perm_eq_sum_mul_iff
- \+ *lemma* monovary.sum_mul_comp_perm_lt_sum_mul_iff
- \+ *lemma* monovary.sum_smul_comp_perm_eq_sum_smul_iff
- \+ *lemma* monovary.sum_smul_comp_perm_lt_sum_smul_iff
- \+ *lemma* monovary_on.sum_comp_perm_mul_eq_sum_mul_iff
- \+ *lemma* monovary_on.sum_comp_perm_mul_lt_sum_mul_iff
- \+ *lemma* monovary_on.sum_comp_perm_smul_eq_sum_smul_iff
- \+ *lemma* monovary_on.sum_comp_perm_smul_lt_sum_smul_iff
- \+ *lemma* monovary_on.sum_mul_comp_perm_eq_sum_mul_iff
- \+ *lemma* monovary_on.sum_mul_comp_perm_lt_sum_mul_iff
- \+ *lemma* monovary_on.sum_smul_comp_perm_eq_sum_smul_iff
- \+ *lemma* monovary_on.sum_smul_comp_perm_lt_sum_smul_iff

Modified src/order/monovary.lean
- \+ *lemma* antivary_on_to_dual_left
- \+ *lemma* antivary_on_to_dual_right
- \+ *lemma* antivary_to_dual_left
- \+ *lemma* antivary_to_dual_right
- \+ *lemma* monovary_on_to_dual_left
- \+ *lemma* monovary_on_to_dual_right
- \+ *lemma* monovary_to_dual_left
- \+ *lemma* monovary_to_dual_right



## [2022-05-29 09:04:36](https://github.com/leanprover-community/mathlib/commit/6b936a9)
feat(data/set/basic): simp-normal form for `↥{x | p x}` ([#14441](https://github.com/leanprover-community/mathlib/pull/14441))
We make `{x // p x}` the simp-normal form for `↥{x | p x}`. We also rewrite some lemmas to use the former instead of the latter.
#### Estimated changes
Modified archive/imo/imo1987_q1.lean


Modified src/algebra/algebraic_card.lean
- \+/\- *theorem* algebraic.cardinal_mk_le_max
- \+/\- *theorem* algebraic.cardinal_mk_le_mul
- \+/\- *theorem* algebraic.cardinal_mk_le_of_infinite

Modified src/data/set/basic.lean
- \+ *theorem* set.coe_eq_subtype
- \+ *theorem* set.coe_set_of
- \- *theorem* set.set_coe_eq_subtype

Modified src/set_theory/cardinal/basic.lean
- \+ *lemma* cardinal.mk_subtype_le_omega

Modified src/set_theory/cardinal/cofinality.lean


Modified src/set_theory/cardinal/ordinal.lean


Modified src/tactic/subtype_instance.lean




## [2022-05-29 01:31:29](https://github.com/leanprover-community/mathlib/commit/3e58d9c)
feat(data/nat/enat): `is_well_order` instance for `enat` ([#14416](https://github.com/leanprover-community/mathlib/pull/14416))
#### Estimated changes
Modified src/data/nat/enat.lean
- \+/\- *lemma* enat.lt_wf



## [2022-05-28 20:10:48](https://github.com/leanprover-community/mathlib/commit/ad2baee)
feat(topology/separation): `t0_space` and `t1_space` for `α × β` and `Π i, α i` ([#14418](https://github.com/leanprover-community/mathlib/pull/14418))
#### Estimated changes
Modified src/analysis/normed_space/pi_Lp.lean


Modified src/data/set/prod.lean
- \+ *lemma* set.univ_pi_singleton

Modified src/topology/separation.lean
- \+ *lemma* indistinguishable.map
- \+ *lemma* t0_space_iff_indistinguishable



## [2022-05-28 17:52:57](https://github.com/leanprover-community/mathlib/commit/f13e5df)
refactor(set_theory/*) rename `wf` lemmas to `lt_wf` ([#14417](https://github.com/leanprover-community/mathlib/pull/14417))
This is done for consistency with the rest of `mathlib` (`nat.lt_wf`, `enat.lt_wf`, `finset.lt_wf`, ...)
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean


Modified src/set_theory/cardinal/ordinal.lean


Modified src/set_theory/ordinal/arithmetic.lean


Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* ordinal.lt_wf
- \- *theorem* ordinal.wf

Modified src/set_theory/ordinal/notation.lean
- \+ *theorem* nonote.lt_wf
- \- *theorem* nonote.wf



## [2022-05-28 17:52:56](https://github.com/leanprover-community/mathlib/commit/762fc15)
feat(set_theory/ordinal/arithmetic): Add missing instances for `ordinal` ([#14128](https://github.com/leanprover-community/mathlib/pull/14128))
We add the following instances:
- `monoid_with_zero ordinal`
- `no_zero_divisors ordinal`
- `is_left_distrib_class ordinal`
- `contravariant_class ordinal ordinal (swap (+)) (<)`
- `is_antisymm ordinal (∣)`
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean
- \- *theorem* ordinal.dvd_add
- \- *theorem* ordinal.dvd_zero
- \- *theorem* ordinal.lt_of_add_lt_add_right
- \- *theorem* ordinal.mul_add
- \- *theorem* ordinal.mul_add_one
- \- *theorem* ordinal.mul_eq_zero_iff
- \- *theorem* ordinal.mul_one_add
- \+/\- *theorem* ordinal.mul_succ
- \- *theorem* ordinal.mul_two
- \- *theorem* ordinal.mul_zero
- \- *theorem* ordinal.one_dvd
- \+/\- *theorem* ordinal.succ_zero
- \- *theorem* ordinal.zero_dvd
- \- *theorem* ordinal.zero_mul

Modified src/set_theory/ordinal/basic.lean


Modified src/set_theory/ordinal/fixed_point.lean


Modified src/set_theory/ordinal/notation.lean
- \- *theorem* onote.mul_zero
- \- *theorem* onote.zero_mul



## [2022-05-28 17:52:55](https://github.com/leanprover-community/mathlib/commit/3280d00)
feat(algebra/order/monoid_lemmas_zero_lt): add some lemmas assuming `mul_zero_class` `partial_order`, remove primes ([#14060](https://github.com/leanprover-community/mathlib/pull/14060))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \- *lemma* zero_lt.le_mul_of_le_of_one_le'
- \- *lemma* zero_lt.le_mul_of_one_le_left'
- \+/\- *lemma* zero_lt.le_mul_of_one_le_left
- \- *lemma* zero_lt.le_mul_of_one_le_of_le'
- \- *lemma* zero_lt.le_mul_of_one_le_right'
- \+/\- *lemma* zero_lt.le_mul_of_one_le_right
- \- *lemma* zero_lt.le_of_le_mul_of_le_one_left'
- \- *lemma* zero_lt.le_of_mul_le_of_one_le_left'
- \- *lemma* zero_lt.le_of_mul_le_of_one_le_right'
- \- *lemma* zero_lt.left.mul_le_one_of_le_of_le'
- \- *lemma* zero_lt.left.one_le_mul_of_le_of_le'
- \- *lemma* zero_lt.lt_of_mul_lt_mul_left''
- \+ *lemma* zero_lt.lt_of_mul_lt_mul_left
- \- *lemma* zero_lt.lt_of_mul_lt_mul_right''
- \+ *lemma* zero_lt.lt_of_mul_lt_mul_right
- \+ *lemma* zero_lt.mul_eq_mul_iff_eq_and_eq'
- \+ *lemma* zero_lt.mul_eq_mul_iff_eq_and_eq
- \- *lemma* zero_lt.mul_le_mul_left''
- \+ *lemma* zero_lt.mul_le_mul_left
- \- *lemma* zero_lt.mul_le_mul_right''
- \+ *lemma* zero_lt.mul_le_mul_right
- \- *lemma* zero_lt.mul_le_of_le_of_le_one'
- \- *lemma* zero_lt.mul_le_of_le_one_left'
- \+/\- *lemma* zero_lt.mul_le_of_le_one_left
- \- *lemma* zero_lt.mul_le_of_le_one_of_le'
- \- *lemma* zero_lt.mul_le_of_le_one_right'
- \+/\- *lemma* zero_lt.mul_le_of_le_one_right
- \+ *lemma* zero_lt.mul_left_cancel_iff
- \+ *lemma* zero_lt.mul_right_cancel_iff
- \+ *lemma* zero_lt.preorder.le_mul_of_le_mul_left
- \+ *lemma* zero_lt.preorder.le_mul_of_le_mul_right
- \+ *lemma* zero_lt.preorder.le_mul_of_le_of_one_le
- \+ *lemma* zero_lt.preorder.le_mul_of_one_le_left
- \+ *lemma* zero_lt.preorder.le_mul_of_one_le_of_le
- \+ *lemma* zero_lt.preorder.le_mul_of_one_le_right
- \+ *lemma* zero_lt.preorder.le_of_le_mul_of_le_one_left
- \+ *lemma* zero_lt.preorder.le_of_mul_le_of_one_le_left
- \+ *lemma* zero_lt.preorder.le_of_mul_le_of_one_le_right
- \+ *lemma* zero_lt.preorder.left.mul_le_one_of_le_of_le'
- \+ *lemma* zero_lt.preorder.left.one_le_mul_of_le_of_le
- \+ *lemma* zero_lt.preorder.mul_le_mul_of_le_of_le'
- \+ *lemma* zero_lt.preorder.mul_le_mul_of_le_of_le
- \+ *lemma* zero_lt.preorder.mul_le_of_le_of_le_one
- \+ *lemma* zero_lt.preorder.mul_le_of_le_one_left
- \+ *lemma* zero_lt.preorder.mul_le_of_le_one_of_le
- \+ *lemma* zero_lt.preorder.mul_le_of_le_one_right
- \+ *lemma* zero_lt.preorder.mul_le_of_mul_le_left
- \+ *lemma* zero_lt.preorder.mul_le_of_mul_le_right
- \+ *lemma* zero_lt.preorder.right.mul_le_one_of_le_of_le
- \+ *lemma* zero_lt.preorder.right.one_le_mul_of_le_of_le
- \- *lemma* zero_lt.right.mul_le_one_of_le_of_le'
- \- *lemma* zero_lt.right.one_le_mul_of_le_of_le'



## [2022-05-28 15:49:21](https://github.com/leanprover-community/mathlib/commit/1e46532)
feat(measure_theory/integral/lebesgue): `lintegral_add` holds if 1 function is measurable ([#14278](https://github.com/leanprover-community/mathlib/pull/14278))
* for any function `f` there exists a measurable function `g ≤ f` with the same Lebesgue integral;
* prove `∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ` assuming **one** of the functions is (a.e.-)measurable; split `lintegral_add` into two lemmas `lintegral_add_(left|right)`;
* prove `∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ ≤ ∫⁻ a, f a + g a ∂μ` for any `f`, `g`;
* prove a version of Markov's inequality for `μ {x | f x + ε ≤ g x}` with possibly non-measurable `f`;
* prove `f ≤ᵐ[μ] g → ∫⁻ x, f x ∂μ ≠ ∞ → ∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ → f =ᵐ[μ] g` for an a.e.-measurable function `f`;
* drop one measurability assumption in `lintegral_sub` and `lintegral_sub_le`;
* add `lintegral_strict_mono_of_ae_le_of_frequently_ae_lt`, a version of `lintegral_strict_mono_of_ae_le_of_ae_lt_on`;
* drop one measurability assumption in `lintegral_strict_mono_of_ae_le_of_ae_lt_on`, `lintegral_strict_mono`, and `set_lintegral_strict_mono`;
* prove `with_density_add` assuming measurability of one of the functions; replace it with `with_density_add_(left|right)`;
* drop measurability assumptions here and there in `mean_inequalities`.
#### Estimated changes
Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/function/ae_eq_fun.lean


Modified src/measure_theory/function/ae_eq_of_integral.lean


Modified src/measure_theory/function/jacobian.lean


Modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* measure_theory.integrable.add'
- \- *lemma* measure_theory.lintegral_nnnorm_add
- \+ *lemma* measure_theory.lintegral_nnnorm_add_left
- \+ *lemma* measure_theory.lintegral_nnnorm_add_right

Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.ae_eq_of_ae_le_of_lintegral_le
- \+ *lemma* measure_theory.exists_measurable_le_lintegral_eq
- \+ *lemma* measure_theory.le_lintegral_add
- \- *lemma* measure_theory.lintegral_add'
- \- *lemma* measure_theory.lintegral_add
- \+ *lemma* measure_theory.lintegral_add_aux
- \+ *lemma* measure_theory.lintegral_add_left'
- \+ *lemma* measure_theory.lintegral_add_left
- \+ *lemma* measure_theory.lintegral_add_mul_meas_add_le_le_lintegral
- \+ *lemma* measure_theory.lintegral_add_right'
- \+ *lemma* measure_theory.lintegral_add_right
- \+ *lemma* measure_theory.lintegral_finset_sum'
- \+ *lemma* measure_theory.lintegral_indicator₀
- \+ *lemma* measure_theory.lintegral_strict_mono_of_ae_le_of_frequently_ae_lt
- \+/\- *lemma* measure_theory.lintegral_sub
- \+/\- *lemma* measure_theory.lintegral_sub_le
- \+/\- *lemma* measure_theory.lintegral_zero
- \+/\- *lemma* measure_theory.lintegral_zero_fun
- \- *lemma* measure_theory.with_density_add
- \+ *lemma* measure_theory.with_density_add_left
- \+ *lemma* measure_theory.with_density_add_right

Modified src/measure_theory/integral/mean_inequalities.lean
- \+/\- *lemma* ennreal.ae_eq_zero_of_lintegral_rpow_eq_zero
- \+/\- *lemma* ennreal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero

Modified src/measure_theory/integral/vitali_caratheodory.lean


Modified src/measure_theory/measure/finite_measure_weak_convergence.lean


Modified src/probability/integration.lean




## [2022-05-28 15:49:19](https://github.com/leanprover-community/mathlib/commit/249f107)
feat(algebra/order/monoid_lemmas): remove duplicates, add missing lemmas, fix inconsistencies ([#13494](https://github.com/leanprover-community/mathlib/pull/13494))
Changes in the order:
`mul_lt_mul'''` has asymmetric typeclass assumptions. So I did the following 3 changes.
Rename `mul_lt_mul'''` to `left.mul_lt_mul`
Make an alias `mul_lt_mul'''` of `mul_lt_mul_of_lt_of_lt`
Add `right.mul_lt_mul`
Move `le_mul_of_one_le_left'` and `mul_le_of_le_one_left'` together with similar lemmas.
Move `lt_mul_of_one_lt_left'` together with similar lemmas.
Add `mul_lt_of_lt_one_right'` and `mul_lt_of_lt_one_left'`. These are analogs of other lemmas.
Following are changes of lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`, `b ≤ c → 1 ≤ a → b ≤ c * a`, `a ≤ 1 → b ≤ c → a * b ≤ c` and `1 ≤ a → b ≤ c → b ≤ a * c`. With the following changes, these 4 sections will be very similar.
For `b ≤ c → a ≤ 1 → b * a ≤ c`:
Remove `alias mul_le_of_le_of_le_one ← mul_le_one'`. This naming is not consistent with `left.mul_lt_one`.
Add `mul_lt_of_lt_of_lt_one'`.
Add `left.mul_le_one`.
Add `left.mul_lt_one_of_le_of_lt`.
Add `left.mul_lt_one_of_lt_of_le`.
Add `left.mul_lt_one'`.
For `b ≤ c → 1 ≤ a → b ≤ c * a`:
Rename `le_mul_of_le_of_le_one` to `le_mul_of_le_of_one_le`.
Remove `lt_mul_of_lt_of_one_le'`. It's exactly the same as `lt_mul_of_lt_of_one_le`.
Rename `one_le_mul_right` to `left.one_le_mul`.
Rename `one_le_mul` to `left.one_le_mul`.
Rename `one_lt_mul_of_lt_of_le'` to `left.one_lt_mul_of_lt_of_le'`.
Add `left.one_lt_mul`.
Rename `one_lt_mul'` to `left.one_lt_mul'`.
For `a ≤ 1 → b ≤ c → a * b ≤ c`:
Add `mul_lt_of_lt_one_of_lt'`.
Add `right.mul_le_one`.
Add `right.mul_lt_one_of_lt_of_le`.
Add `right.mul_lt_one'`.
For `1 ≤ a → b ≤ c → b ≤ a * c`:
Rename `lt_mul_of_one_lt_of_lt` to `lt_mul_of_one_lt_of_lt'`.
Add `lt_mul_of_one_lt_of_lt`.
Add `right.one_lt_mul_of_lt_of_le`.
Rename `one_lt_mul_of_le_of_lt'` to `right.one_lt_mul_of_le_of_lt`.
Add `right.one_lt_mul'`.
Then create aliases for all `left` lemmas in these 4 sections.
Rename `mul_eq_mul_iff_eq_and_eq` to `left.mul_eq_mul_iff_eq_and_eq`.
Add `right.mul_eq_mul_iff_eq_and_eq`.
Make an alias `mul_eq_mul_iff_eq_and_eq` of `left.mul_eq_mul_iff_eq_and_eq`.
Same for additive version.
However, the implicit parameter inconsistency has not been resolved. It affects too many files.
#### Estimated changes
Modified src/algebra/group_power/order.lean


Modified src/algebra/order/group.lean


Modified src/algebra/order/monoid.lean


Modified src/algebra/order/monoid_lemmas.lean
- \- *lemma* le_mul_of_le_of_le_one
- \+/\- *lemma* le_mul_of_one_le_right'
- \+ *lemma* left.mul_eq_mul_iff_eq_and_eq
- \+ *lemma* left.mul_le_one
- \+ *lemma* left.mul_lt_mul
- \+ *lemma* left.mul_lt_one'
- \+ *lemma* left.mul_lt_one_of_le_of_lt
- \+ *lemma* left.mul_lt_one_of_lt_of_le
- \+ *lemma* left.one_le_mul
- \+ *lemma* left.one_lt_mul'
- \+ *lemma* left.one_lt_mul
- \+ *lemma* left.one_lt_mul_of_le_of_lt
- \+ *lemma* left.one_lt_mul_of_lt_of_le
- \- *lemma* lt_mul_of_lt_of_one_le'
- \+ *lemma* lt_mul_of_one_lt_of_lt'
- \+/\- *lemma* lt_mul_of_one_lt_of_lt
- \+/\- *lemma* lt_mul_of_one_lt_right'
- \- *lemma* mul_eq_mul_iff_eq_and_eq
- \+/\- *lemma* mul_le_of_le_one_right'
- \- *lemma* mul_lt_mul'''
- \+ *lemma* mul_lt_of_lt_of_lt_one'
- \+ *lemma* mul_lt_of_lt_one_left'
- \+ *lemma* mul_lt_of_lt_one_of_lt'
- \+ *lemma* mul_lt_of_lt_one_right'
- \- *lemma* one_le_mul
- \- *lemma* one_le_mul_right
- \- *lemma* one_lt_mul'
- \- *lemma* one_lt_mul_of_le_of_lt'
- \- *lemma* one_lt_mul_of_lt_of_le'
- \+ *lemma* right.mul_eq_mul_iff_eq_and_eq
- \+ *lemma* right.mul_le_one
- \+ *lemma* right.mul_lt_mul
- \+ *lemma* right.mul_lt_one'
- \+ *lemma* right.mul_lt_one_of_le_of_lt
- \+ *lemma* right.mul_lt_one_of_lt_of_le
- \+ *lemma* right.one_lt_mul'
- \+ *lemma* right.one_lt_mul_of_le_of_lt
- \+ *lemma* right.one_lt_mul_of_lt_of_le

Modified src/combinatorics/additive/salem_spencer.lean


Modified src/number_theory/primes_congruent_one.lean


Modified src/set_theory/ordinal/principal.lean




## [2022-05-28 13:51:33](https://github.com/leanprover-community/mathlib/commit/2ce8482)
feat(computability/regular_expressions): add power operator ([#14261](https://github.com/leanprover-community/mathlib/pull/14261))
We can't make `regular_expression` a monoid, but we can put a power operator on it that's compatible with the power operator on languages.
#### Estimated changes
Modified src/computability/regular_expressions.lean
- \+ *lemma* regular_expression.matches_pow



## [2022-05-28 13:51:32](https://github.com/leanprover-community/mathlib/commit/8a0e712)
feat(category_theory/monoidal/discrete): simps ([#14259](https://github.com/leanprover-community/mathlib/pull/14259))
This is a minuscule change, but it appears to work both on `master` and in the [shift functor refactor](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/trouble.20in.20.60shift_functor.60.20land) I'm aspiring towards, so I'm shipping it off for CI.
#### Estimated changes
Modified src/category_theory/monoidal/discrete.lean




## [2022-05-28 13:51:31](https://github.com/leanprover-community/mathlib/commit/dcd5ebd)
feat({data/{finset,set},order/filter}/pointwise): More lemmas ([#14216](https://github.com/leanprover-community/mathlib/pull/14216))
Lemmas about `s ^ n`, `0 * s` and `1 ∈ s / t`.
Other changes:
* `finset.mul_card_le` → `finset.card_mul_le`
* `finset.card_image_eq_iff_inj_on` → `finset.card_image_iff`.
* `zero_smul_subset` → `zero_smul_set_subset`
* Reorder lemmas slightly
* Add an explicit argument to `finset.coe_smul_finset`
* Remove an explicit argument to `set.empty`
#### Estimated changes
Modified src/analysis/convex/gauge.lean


Modified src/data/finset/basic.lean


Modified src/data/finset/card.lean
- \- *lemma* finset.card_image_eq_iff_inj_on
- \+ *lemma* finset.card_image_iff

Modified src/data/finset/interval.lean


Modified src/data/finset/n_ary.lean
- \+ *lemma* finset.card_image₂_iff
- \+ *lemma* finset.image₂_singleton_left'

Modified src/data/finset/pointwise.lean
- \+ *lemma* finset.card_mul_iff
- \+ *lemma* finset.card_mul_le
- \+ *lemma* finset.empty_pow
- \+ *lemma* finset.image_div
- \+ *lemma* finset.image_mul
- \+/\- *lemma* finset.image_one
- \- *lemma* finset.mul_card_le
- \+ *lemma* finset.mul_univ_of_one_mem
- \+ *lemma* finset.nonempty.one_mem_div
- \+ *lemma* finset.nonempty.subset_one_iff
- \+ *lemma* finset.not_one_mem_div_iff
- \+ *lemma* finset.one_mem_div_iff
- \+ *lemma* finset.pow_mem_pow
- \+ *lemma* finset.pow_subset_pow
- \+ *lemma* finset.pow_subset_pow_of_one_mem
- \+ *lemma* finset.subset_mul_left
- \+ *lemma* finset.subset_mul_right
- \+ *lemma* finset.subset_one_iff_eq
- \+ *lemma* finset.univ_mul_of_one_mem
- \+ *lemma* finset.univ_mul_univ
- \+ *lemma* finset.univ_pow

Modified src/data/set/pointwise.lean
- \+ *lemma* set.div_zero_subset
- \+/\- *lemma* set.empty_pow
- \+ *lemma* set.image_div
- \+/\- *lemma* set.image_mul
- \+ *lemma* set.mul_univ_of_one_mem
- \+ *lemma* set.mul_zero_subset
- \+ *lemma* set.nonempty.div_zero
- \+ *lemma* set.nonempty.mul_zero
- \+ *lemma* set.nonempty.one_mem_div
- \+ *lemma* set.nonempty.smul_zero
- \+ *lemma* set.nonempty.zero_div
- \+ *lemma* set.nonempty.zero_mul
- \+ *lemma* set.nonempty.zero_smul
- \+ *lemma* set.not_one_mem_div_iff
- \+ *lemma* set.nsmul_univ
- \+ *lemma* set.one_mem_div_iff
- \+ *lemma* set.pow_subset_pow_of_one_mem
- \+ *lemma* set.preimage_div_preimage_subset
- \+/\- *lemma* set.preimage_mul_preimage_subset
- \+/\- *lemma* set.smul_mem_smul_set_iff
- \+ *lemma* set.smul_zero_subset
- \+ *lemma* set.univ_mul_of_one_mem
- \+ *lemma* set.univ_pow
- \+ *lemma* set.zero_div_subset
- \+ *lemma* set.zero_mul_subset
- \+ *lemma* set.zero_smul_set_subset
- \+/\- *lemma* set.zero_smul_subset

Modified src/measure_theory/measure/haar.lean


Modified src/order/filter/basic.lean
- \+/\- *theorem* filter.le_def
- \+ *lemma* filter.le_map_iff
- \+ *lemma* filter.ne_bot.not_disjoint
- \+ *lemma* filter.ne_bot.of_map
- \+ *lemma* filter.not_disjoint_self_iff

Modified src/order/filter/pointwise.lean
- \+ *lemma* filter.bot_pow
- \+ *lemma* filter.mem_mul
- \- *lemma* filter.mem_mul_iff
- \+ *lemma* filter.mul_top_of_one_le
- \+ *lemma* filter.ne_bot.div_zero_nonneg
- \+ *lemma* filter.ne_bot.mul_zero_nonneg
- \+ *lemma* filter.ne_bot.of_smul_filter
- \+ *lemma* filter.ne_bot.one_le_div
- \+ *lemma* filter.ne_bot.smul_zero_nonneg
- \+ *lemma* filter.ne_bot.zero_div_nonneg
- \+ *lemma* filter.ne_bot.zero_mul_nonneg
- \+ *lemma* filter.ne_bot.zero_smul_nonneg
- \+ *lemma* filter.not_one_le_div_iff
- \+ *lemma* filter.nsmul_top
- \+ *lemma* filter.top_mul_of_one_le
- \+ *lemma* filter.top_mul_top
- \+ *lemma* filter.top_pow
- \+ *lemma* filter.zero_smul_filter
- \+ *lemma* filter.zero_smul_filter_nonpos

Modified src/ring_theory/chain_of_divisors.lean




## [2022-05-28 11:42:59](https://github.com/leanprover-community/mathlib/commit/15fe782)
doc(set_theory/lists): fix typo ([#14427](https://github.com/leanprover-community/mathlib/pull/14427))
#### Estimated changes
Modified src/set_theory/lists.lean




## [2022-05-28 11:42:58](https://github.com/leanprover-community/mathlib/commit/d0efbcb)
feat(model_theory/elementary_maps): Elementary maps respect all (bounded) formulas ([#14252](https://github.com/leanprover-community/mathlib/pull/14252))
Generalizes `elementary_embedding.map_formula` to more classes of formula.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.inclusion_eq_id

Modified src/model_theory/elementary_maps.lean
- \+ *lemma* first_order.language.elementary_embedding.Theory_model_iff
- \+ *lemma* first_order.language.elementary_embedding.map_bounded_formula
- \+/\- *lemma* first_order.language.elementary_embedding.map_formula
- \+ *lemma* first_order.language.elementary_embedding.map_sentence



## [2022-05-28 11:42:57](https://github.com/leanprover-community/mathlib/commit/599240f)
refactor(order/bounds): general cleanup ([#14127](https://github.com/leanprover-community/mathlib/pull/14127))
Apart from golfing, this PR does the following:
Add the following theorems (which are immediate from the non-self counterparts):
- `monotone_on.mem_upper_bounds_image_self`
- `monotone_on.mem_lower_bounds_image_self`
- `antitone_on.mem_upper_bounds_image_self`
- `antitone_on.mem_lower_bounds_image_self`
Remove the following theorems (as they're just `mem_X_bounds_image` under unnecessarily stronger assumptions):
- `monotone_on.is_lub_image_le`
- `monotone_on.le_is_glb_image`
- `antitone_on.is_lub_image_le`
- `antitone_on.le_is_glb_image`
- `monotone.is_lub_image_le`
- `monotone.le_is_glb_image`
- `antitone.is_lub_image_le`
- `antitone.le_is_glb_image`
Remove a redundant argument `s ⊆ t` from the following (the old theorems follow immediately from the new ones and `monotone_on.mono`):
- `monotone_on.map_is_greatest`
- `monotone_on.map_is_least`
- `antitone_on.map_is_greatest`
- `antitone_on.map_is_least`
#### Estimated changes
Modified src/order/bounds.lean
- \+/\- *lemma* antitone.image_lower_bounds_subset_upper_bounds_image
- \+/\- *lemma* antitone.image_upper_bounds_subset_lower_bounds_image
- \- *lemma* antitone.is_lub_image_le
- \- *lemma* antitone.le_is_glb_image
- \+/\- *lemma* antitone.map_bdd_above
- \+/\- *lemma* antitone.map_bdd_below
- \+/\- *lemma* antitone.map_is_greatest
- \+/\- *lemma* antitone.map_is_least
- \+/\- *lemma* antitone.mem_lower_bounds_image
- \+/\- *lemma* antitone.mem_upper_bounds_image
- \- *lemma* antitone_on.is_lub_image_le
- \- *lemma* antitone_on.le_is_glb_image
- \+/\- *lemma* antitone_on.map_is_greatest
- \+/\- *lemma* antitone_on.map_is_least
- \+/\- *lemma* antitone_on.mem_lower_bounds_image
- \+ *lemma* antitone_on.mem_lower_bounds_image_self
- \+/\- *lemma* antitone_on.mem_upper_bounds_image
- \+ *lemma* antitone_on.mem_upper_bounds_image_self
- \+/\- *lemma* monotone.image_lower_bounds_subset_lower_bounds_image
- \+/\- *lemma* monotone.image_upper_bounds_subset_upper_bounds_image
- \- *lemma* monotone.is_lub_image_le
- \- *lemma* monotone.le_is_glb_image
- \+/\- *lemma* monotone.map_bdd_above
- \+/\- *lemma* monotone.map_bdd_below
- \+/\- *lemma* monotone.mem_lower_bounds_image
- \+/\- *lemma* monotone.mem_upper_bounds_image
- \+/\- *lemma* monotone_on.image_upper_bounds_subset_upper_bounds_image
- \- *lemma* monotone_on.is_lub_image_le
- \- *lemma* monotone_on.le_is_glb_image
- \+/\- *lemma* monotone_on.map_is_greatest
- \+/\- *lemma* monotone_on.map_is_least
- \+ *lemma* monotone_on.mem_lower_bounds_image_self
- \+ *lemma* monotone_on.mem_upper_bounds_image_self

Modified src/order/galois_connection.lean




## [2022-05-28 10:25:26](https://github.com/leanprover-community/mathlib/commit/bb90598)
feat(set_theory/ordinal/basic): Turn various lemmas into `simp` ([#14075](https://github.com/leanprover-community/mathlib/pull/14075))
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean
- \+/\- *lemma* ordinal.card_typein
- \+/\- *theorem* ordinal.enum_inj
- \+/\- *lemma* ordinal.enum_le_enum'
- \+/\- *lemma* ordinal.enum_le_enum
- \+/\- *theorem* ordinal.typein_inj



## [2022-05-28 05:34:51](https://github.com/leanprover-community/mathlib/commit/dccab1c)
feat(algebra/ring/basic): Generalize theorems on distributivity ([#14140](https://github.com/leanprover-community/mathlib/pull/14140))
Many theorems assuming full distributivity only need left or right distributivity. We remedy this by making new `left_distrib_class` and `right_distrib_class` classes.
The main motivation here is to generalize various theorems on ordinals, like [ordinal.mul_add](https://leanprover-community.github.io/mathlib_docs/set_theory/ordinal/arithmetic.html#ordinal.mul_add).
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+/\- *lemma* add_one_mul
- \+/\- *theorem* bit0_eq_two_mul
- \+/\- *lemma* distrib_three_right
- \+/\- *theorem* dvd_add
- \+/\- *lemma* left_distrib
- \+/\- *lemma* mul_add_one
- \+/\- *lemma* mul_one_add
- \+/\- *theorem* mul_two
- \+/\- *lemma* one_add_mul
- \+/\- *lemma* one_add_one_eq_two
- \+/\- *lemma* right_distrib
- \+/\- *theorem* two_mul

Modified src/algebra/ring/boolean_ring.lean


Modified src/algebra/ring/opposite.lean


Modified src/data/num/lemmas.lean


Modified src/ring_theory/coprime/lemmas.lean


Modified src/tactic/omega/eq_elim.lean




## [2022-05-28 04:03:23](https://github.com/leanprover-community/mathlib/commit/15b7e53)
refactor(set_theory/cardinal/*): `cardinal.succ` → `order.succ` ([#14273](https://github.com/leanprover-community/mathlib/pull/14273))
#### Estimated changes
Modified src/data/W/cardinal.lean


Modified src/set_theory/cardinal/basic.lean
- \- *theorem* cardinal.le_of_lt_succ
- \- *theorem* cardinal.le_succ
- \- *theorem* cardinal.lt_succ
- \- *theorem* cardinal.lt_succ_iff
- \+/\- *lemma* cardinal.powerlt_succ
- \- *def* cardinal.succ
- \+ *theorem* cardinal.succ_def
- \- *theorem* cardinal.succ_le_iff
- \- *theorem* cardinal.succ_le_of_lt
- \- *theorem* cardinal.succ_nonempty
- \+/\- *lemma* cardinal.succ_pos
- \+/\- *theorem* cardinal.succ_zero

Modified src/set_theory/cardinal/cofinality.lean
- \+/\- *theorem* cardinal.is_regular_aleph_succ
- \+/\- *lemma* order.cof_le

Modified src/set_theory/cardinal/continuum.lean


Modified src/set_theory/cardinal/ordinal.lean
- \+/\- *theorem* cardinal.aleph'_succ
- \+/\- *theorem* cardinal.aleph_succ

Modified src/set_theory/ordinal/arithmetic.lean
- \+/\- *theorem* ordinal.bmex_lt_ord_succ_card
- \+/\- *theorem* ordinal.mex_lt_ord_succ_mk

Modified src/set_theory/ordinal/basic.lean
- \+/\- *lemma* cardinal.lt_ord_succ_card



## [2022-05-28 00:43:54](https://github.com/leanprover-community/mathlib/commit/5eb68b5)
feat(data/polynomial/mirror): `nat_degree` and `nat_trailing_degree` of `p * p.mirror` ([#14397](https://github.com/leanprover-community/mathlib/pull/14397))
This PR adds lemmas for the `nat_degree` and `nat_trailing_degree` of `p * p.mirror`. These lemmas tell you that you can recover `p.nat_degree` and `p.nat_trailing_degree` from `p * p.mirror`, which will be useful for irreducibility of x^n-x-1.
#### Estimated changes
Modified src/data/polynomial/mirror.lean
- \+ *lemma* polynomial.nat_degree_mul_mirror
- \+ *lemma* polynomial.nat_trailing_degree_mul_mirror



## [2022-05-27 23:26:09](https://github.com/leanprover-community/mathlib/commit/a08d179)
refactor(set_theory/ordinal/*): `ordinal.succ` → `order.succ` ([#14243](https://github.com/leanprover-community/mathlib/pull/14243))
We inline the definition of `ordinal.succ` in the `succ_order` instance. This allows us to comfortably use all of the theorems about `order.succ` to our advantage.
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean
- \+/\- *theorem* cardinal.is_regular_aleph'_succ
- \+/\- *theorem* cardinal.is_regular_aleph_succ

Modified src/set_theory/cardinal/ordinal.lean
- \+/\- *theorem* cardinal.aleph'_succ
- \+/\- *theorem* cardinal.aleph_succ

Modified src/set_theory/game/birthday.lean


Modified src/set_theory/ordinal/arithmetic.lean
- \+/\- *theorem* ordinal.blsub_const
- \+/\- *theorem* ordinal.blsub_le_bsup_succ
- \+/\- *theorem* ordinal.blsub_one
- \+/\- *theorem* ordinal.bsup_id_limit
- \+/\- *theorem* ordinal.is_normal.eq_iff_zero_and_succ
- \+/\- *def* ordinal.lsub
- \+/\- *theorem* ordinal.lsub_const
- \+/\- *theorem* ordinal.lsub_unique
- \+/\- *theorem* ordinal.mul_add_one
- \+/\- *theorem* ordinal.mul_one_add
- \+/\- *theorem* ordinal.mul_succ
- \- *theorem* ordinal.succ_inj
- \- *theorem* ordinal.succ_le_succ
- \+/\- *theorem* ordinal.succ_lt_of_is_limit
- \+/\- *theorem* ordinal.succ_lt_of_not_succ
- \- *theorem* ordinal.succ_lt_succ
- \+/\- *theorem* ordinal.succ_one
- \+/\- *theorem* ordinal.succ_zero
- \+/\- *theorem* ordinal.sup_eq_lsub
- \+/\- *theorem* ordinal.sup_succ_eq_lsub
- \+/\- *theorem* ordinal.sup_succ_le_lsub

Modified src/set_theory/ordinal/basic.lean
- \+ *theorem* ordinal.add_one_eq_succ
- \+/\- *theorem* ordinal.le_enum_succ
- \- *theorem* ordinal.lt_succ
- \- *theorem* ordinal.lt_succ_self
- \- *def* ordinal.succ
- \- *theorem* ordinal.succ_eq_add_one
- \- *theorem* ordinal.succ_le
- \- *theorem* ordinal.succ_ne_self

Modified src/set_theory/ordinal/fixed_point.lean


Modified src/set_theory/ordinal/notation.lean


Modified src/set_theory/ordinal/principal.lean


Modified src/set_theory/ordinal/topology.lean




## [2022-05-27 21:20:28](https://github.com/leanprover-community/mathlib/commit/9919539)
feat(category_theory): more API for isomorphisms ([#14420](https://github.com/leanprover-community/mathlib/pull/14420))
#### Estimated changes
Modified src/category_theory/isomorphism.lean
- \+ *lemma* category_theory.comp_inv_eq_id
- \+ *lemma* category_theory.inv_comp_eq_id
- \+ *lemma* category_theory.is_iso_of_comp_hom_eq_id
- \+ *lemma* category_theory.is_iso_of_hom_comp_eq_id
- \+ *lemma* category_theory.iso.comp_inv_eq_id
- \+ *lemma* category_theory.iso.inv_comp_eq_id



## [2022-05-27 21:20:27](https://github.com/leanprover-community/mathlib/commit/533cbf4)
feat(data/int/{cast, char_zero}): relax typeclass assumptions ([#14413](https://github.com/leanprover-community/mathlib/pull/14413))
#### Estimated changes
Modified src/data/int/cast.lean
- \+/\- *theorem* int.cast_bit0
- \+/\- *theorem* int.cast_bit1
- \+/\- *lemma* int.cast_comm
- \+/\- *lemma* int.cast_commute
- \+/\- *lemma* int.cast_four
- \+/\- *theorem* int.cast_mul
- \+/\- *def* int.cast_ring_hom
- \+/\- *lemma* int.cast_three
- \+/\- *lemma* int.cast_two
- \+/\- *lemma* int.coe_cast_ring_hom
- \+/\- *lemma* int.commute_cast
- \+/\- *lemma* ring_hom.ext_int

Modified src/data/int/char_zero.lean
- \+/\- *lemma* ring_hom.injective_int



## [2022-05-27 19:20:34](https://github.com/leanprover-community/mathlib/commit/f598e58)
feat(topology/vector_bundle): do not require topology on the fibers for topological_vector_prebundle ([#14377](https://github.com/leanprover-community/mathlib/pull/14377))
* Separated from branch `vb-hom`
#### Estimated changes
Modified src/topology/vector_bundle.lean
- \+ *def* topological_vector_prebundle.fiber_topology
- \+ *lemma* topological_vector_prebundle.inducing_total_space_mk
- \- *lemma* topological_vector_prebundle.inducing_total_space_mk_of_inducing_comp



## [2022-05-27 19:20:33](https://github.com/leanprover-community/mathlib/commit/a94ae0c)
feat(data/list/min_max): add le_max_of_le, min_le_of_le  ([#14340](https://github.com/leanprover-community/mathlib/pull/14340))
#### Estimated changes
Modified src/data/list/min_max.lean
- \+ *lemma* list.le_max_of_le
- \+ *lemma* list.min_le_of_le



## [2022-05-27 19:20:32](https://github.com/leanprover-community/mathlib/commit/41ca601)
feat(analysis/convolution): The convolution of two functions ([#13540](https://github.com/leanprover-community/mathlib/pull/13540))
* Define the convolution of two functions.
* Prove that when one of the functions has compact support and is `C^n` and the other function is locally integrable, the convolution is `C^n`.
* Compute the total derivative of the convolution (when one of the functions has compact support).
* Prove that when taking the convolution with functions that "tend to the Dirac delta function", the convolution tends to the original function.
* From the sphere eversion project.
#### Estimated changes
Modified src/analysis/convolution.lean
- \+ *lemma* bdd_above.continuous_convolution_left_of_integrable
- \+ *lemma* bdd_above.continuous_convolution_right_of_integrable
- \+ *lemma* cont_diff_bump_of_inner.convolution_eq_right
- \+ *lemma* cont_diff_bump_of_inner.convolution_tendsto_right'
- \+ *lemma* cont_diff_bump_of_inner.convolution_tendsto_right
- \+ *lemma* cont_diff_bump_of_inner.dist_normed_convolution_le
- \+ *lemma* cont_diff_bump_of_inner.normed_convolution_eq_right
- \+ *lemma* convolution_assoc
- \+ *lemma* convolution_congr
- \+ *lemma* convolution_def
- \+ *lemma* convolution_eq_right'
- \+ *lemma* convolution_eq_swap
- \+ *lemma* convolution_exists.add_distrib
- \+ *lemma* convolution_exists.distrib_add
- \+ *lemma* convolution_exists_at.add_distrib
- \+ *lemma* convolution_exists_at.distrib_add
- \+ *lemma* convolution_flip
- \+ *lemma* convolution_lmul
- \+ *lemma* convolution_lmul_swap
- \+ *lemma* convolution_lsmul
- \+ *lemma* convolution_lsmul_swap
- \+ *lemma* convolution_precompR_apply
- \+ *lemma* convolution_smul
- \+ *lemma* convolution_tendsto_right
- \+ *lemma* convolution_zero
- \+ *lemma* dist_convolution_le'
- \+ *lemma* dist_convolution_le
- \+ *lemma* has_compact_support.cont_diff_convolution_left
- \+ *lemma* has_compact_support.cont_diff_convolution_right
- \+ *lemma* has_compact_support.continuous_convolution_left
- \+ *lemma* has_compact_support.continuous_convolution_left_of_integrable
- \+ *lemma* has_compact_support.continuous_convolution_right
- \+ *lemma* has_compact_support.continuous_convolution_right_of_integrable
- \+ *lemma* has_compact_support.convolution
- \+ *lemma* has_compact_support.has_deriv_at_convolution_left
- \+ *lemma* has_compact_support.has_deriv_at_convolution_right
- \+ *lemma* has_compact_support.has_fderiv_at_convolution_left
- \+ *lemma* has_compact_support.has_fderiv_at_convolution_right
- \+ *lemma* measure_theory.integrable.integrable_convolution
- \+ *lemma* smul_convolution
- \+ *lemma* support_convolution_subset
- \+ *lemma* support_convolution_subset_swap
- \+ *lemma* zero_convolution

Modified src/measure_theory/integral/set_integral.lean




## [2022-05-27 19:20:31](https://github.com/leanprover-community/mathlib/commit/baad002)
feat(analysis/complex/phragmen_lindelof): Phragmen-Lindelöf principle for some shapes ([#13178](https://github.com/leanprover-community/mathlib/pull/13178))
Prove Phragmen-Lindelöf principle
- in a horizontal strip;
- in a vertical strip;
- in a coordinate quadrant;
- in the right half-plane (a few versions).
#### Estimated changes
Modified src/analysis/complex/abs_max.lean
- \+ *lemma* complex.norm_eq_norm_of_is_max_on_of_ball_subset
- \- *lemma* complex.norm_eq_norm_of_is_max_on_of_closed_ball_subset

Added src/analysis/complex/phragmen_lindelof.lean
- \+ *lemma* phragmen_lindelof.eq_on_horizontal_strip
- \+ *lemma* phragmen_lindelof.eq_on_quadrant_I
- \+ *lemma* phragmen_lindelof.eq_on_quadrant_II
- \+ *lemma* phragmen_lindelof.eq_on_quadrant_III
- \+ *lemma* phragmen_lindelof.eq_on_quadrant_IV
- \+ *lemma* phragmen_lindelof.eq_on_right_half_plane_of_superexponential_decay
- \+ *lemma* phragmen_lindelof.eq_on_vertical_strip
- \+ *lemma* phragmen_lindelof.eq_zero_on_horizontal_strip
- \+ *lemma* phragmen_lindelof.eq_zero_on_quadrant_I
- \+ *lemma* phragmen_lindelof.eq_zero_on_quadrant_II
- \+ *lemma* phragmen_lindelof.eq_zero_on_quadrant_III
- \+ *lemma* phragmen_lindelof.eq_zero_on_quadrant_IV
- \+ *lemma* phragmen_lindelof.eq_zero_on_right_half_plane_of_superexponential_decay
- \+ *lemma* phragmen_lindelof.eq_zero_on_vertical_strip
- \+ *lemma* phragmen_lindelof.horizontal_strip
- \+ *lemma* phragmen_lindelof.is_O_sub_exp_exp
- \+ *lemma* phragmen_lindelof.is_O_sub_exp_rpow
- \+ *lemma* phragmen_lindelof.quadrant_I
- \+ *lemma* phragmen_lindelof.quadrant_II
- \+ *lemma* phragmen_lindelof.quadrant_III
- \+ *lemma* phragmen_lindelof.quadrant_IV
- \+ *lemma* phragmen_lindelof.right_half_plane_of_bounded_on_real
- \+ *lemma* phragmen_lindelof.right_half_plane_of_tendsto_zero_on_real
- \+ *lemma* phragmen_lindelof.vertical_strip



## [2022-05-27 17:41:19](https://github.com/leanprover-community/mathlib/commit/1ccb7f0)
feat(model_theory/syntax, semantics): Lemmas about relabeling variables ([#14225](https://github.com/leanprover-community/mathlib/pull/14225))
Proves lemmas about relabeling variables in terms and formulas
Defines `first_order.language.bounded_formula.to_formula`, which turns turns all of the extra variables of a `bounded_formula` into free variables.
#### Estimated changes
Modified src/logic/equiv/fin.lean
- \+ *lemma* fin_sum_fin_equiv_symm_last

Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.bounded_formula.realize_to_formula

Modified src/model_theory/syntax.lean
- \+/\- *def* first_order.language.bounded_formula.cast_le
- \+/\- *def* first_order.language.bounded_formula.relabel
- \+/\- *def* first_order.language.bounded_formula.relabel_aux
- \+ *lemma* first_order.language.bounded_formula.relabel_aux_sum_inl
- \+ *lemma* first_order.language.bounded_formula.relabel_sum_inl
- \+ *def* first_order.language.bounded_formula.to_formula
- \+ *lemma* first_order.language.term.relabel_id
- \+ *lemma* first_order.language.term.relabel_relabel



## [2022-05-27 17:02:33](https://github.com/leanprover-community/mathlib/commit/4b9e57b)
feat(model_theory/satisfiability): Upward Löwenheim–Skolem ([#13982](https://github.com/leanprover-community/mathlib/pull/13982))
`first_order.language.Theory.exists_elementary_embedding_card_eq` proves the Upward Löwenheim–Skolem Theorem: every infinite `L`-structure `M` elementarily embeds into an `L`-structure of a given cardinality if that cardinality is larger than the cardinalities of `L` and `M`.
#### Estimated changes
Modified docs/overview.yaml


Modified src/model_theory/satisfiability.lean
- \+ *theorem* first_order.language.Theory.exists_elementary_embedding_card_eq

Modified src/model_theory/skolem.lean
- \+/\- *theorem* first_order.language.exists_elementary_substructure_card_eq



## [2022-05-27 08:53:16](https://github.com/leanprover-community/mathlib/commit/25f75c4)
chore(filter/pointwise): protect filter.has_involutive_inv ([#14398](https://github.com/leanprover-community/mathlib/pull/14398))
#### Estimated changes
Modified src/order/filter/pointwise.lean
- \- *def* filter.has_involutive_inv



## [2022-05-27 08:04:40](https://github.com/leanprover-community/mathlib/commit/2a9b0f8)
chore(ring_theory/artinian): clarify left/right -ness in doc strings ([#14396](https://github.com/leanprover-community/mathlib/pull/14396))
#### Estimated changes
Modified src/ring_theory/artinian.lean




## [2022-05-27 05:12:29](https://github.com/leanprover-community/mathlib/commit/841aef2)
feat(algebraic_topology): the nerve of a category ([#14304](https://github.com/leanprover-community/mathlib/pull/14304))
#### Estimated changes
Added src/algebraic_topology/nerve.lean
- \+ *def* category_theory.nerve
- \+ *def* category_theory.nerve_functor

Modified src/algebraic_topology/simplex_category.lean
- \+ *def* simplex_category.to_Cat



## [2022-05-27 04:25:55](https://github.com/leanprover-community/mathlib/commit/bae0229)
feat(category_theory/monoidal/subcategory): full monoidal subcategories ([#14311](https://github.com/leanprover-community/mathlib/pull/14311))
We use a type synonym for `{X : C // P X}` when `C` is a monoidal category and the property `P` is closed under the monoidal unit and tensor product so that `full_monoidal_subcategory` can be made an instance.
#### Estimated changes
Modified src/algebra/category/FinVect.lean


Modified src/category_theory/monoidal/category.lean
- \- *def* category_theory.monoidal_category.full_monoidal_subcategory

Added src/category_theory/monoidal/subcategory.lean
- \+ *def* category_theory.monoidal_category.full_braided_subcategory.map
- \+ *def* category_theory.monoidal_category.full_braided_subcategory_inclusion
- \+ *def* category_theory.monoidal_category.full_monoidal_subcategory.map
- \+ *def* category_theory.monoidal_category.full_monoidal_subcategory_inclusion



## [2022-05-27 02:02:29](https://github.com/leanprover-community/mathlib/commit/48d831a)
feat(order/bounded_order): define `with_bot.map` and `with_top.map` ([#14163](https://github.com/leanprover-community/mathlib/pull/14163))
Also define `monotone.with_bot` etc.
#### Estimated changes
Modified src/algebra/order/monoid.lean


Modified src/algebra/order/ring.lean


Modified src/logic/embedding.lean
- \+ *def* function.embedding.option_map

Modified src/order/bounded_order.lean
- \+ *def* with_bot.map
- \+/\- *lemma* with_bot.map_bot
- \+/\- *lemma* with_bot.map_coe
- \+ *def* with_top.map
- \+/\- *lemma* with_top.map_coe
- \+/\- *lemma* with_top.map_top

Modified src/order/hom/basic.lean




## [2022-05-26 22:13:11](https://github.com/leanprover-community/mathlib/commit/8dd4619)
feat(combinatorics/simple_graph/connectivity): deleting edges outside a walk ([#14110](https://github.com/leanprover-community/mathlib/pull/14110))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean


Modified src/combinatorics/simple_graph/connectivity.lean
- \+ *lemma* simple_graph.walk.is_path.to_delete_edges
- \+ *lemma* simple_graph.walk.map_is_path_iff_of_injective
- \+ *lemma* simple_graph.walk.map_to_delete_edges_eq
- \+ *abbreviation* simple_graph.walk.to_delete_edge
- \+ *def* simple_graph.walk.to_delete_edges



## [2022-05-26 20:25:47](https://github.com/leanprover-community/mathlib/commit/27791f9)
feat(data/real/nnreal): add mul csupr/cinfi lemmas ([#13936](https://github.com/leanprover-community/mathlib/pull/13936))
#### Estimated changes
Modified src/algebra/order/with_zero.lean
- \+ *lemma* div_le_div_left₀
- \+ *lemma* mul_le_mul_left₀
- \+ *def* order_iso.mul_left₀'
- \+ *lemma* order_iso.mul_left₀'_symm
- \+ *def* order_iso.mul_right₀'
- \+ *lemma* order_iso.mul_right₀'_symm

Modified src/data/real/basic.lean
- \+ *lemma* real.infi_of_not_bdd_below
- \+ *lemma* real.supr_of_not_bdd_above

Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.Sup_of_not_bdd_above
- \+ *lemma* nnreal.infi_const_zero
- \+ *lemma* nnreal.infi_empty
- \+ *lemma* nnreal.infi_mul
- \+ *lemma* nnreal.le_infi_mul
- \+ *lemma* nnreal.le_infi_mul_infi
- \+ *lemma* nnreal.le_mul_infi
- \+ *lemma* nnreal.le_to_nnreal_of_coe_le
- \+ *lemma* nnreal.mul_infi
- \+ *lemma* nnreal.mul_supr
- \+ *lemma* nnreal.mul_supr_le
- \+ *lemma* nnreal.supr_div
- \+ *lemma* nnreal.supr_mul
- \+ *lemma* nnreal.supr_mul_le
- \+ *lemma* nnreal.supr_mul_supr_le
- \+ *lemma* nnreal.supr_of_not_bdd_above

Modified src/data/set/pointwise.lean
- \+ *lemma* set.inv_range
- \+ *lemma* set.smul_set_range



## [2022-05-26 18:17:05](https://github.com/leanprover-community/mathlib/commit/525cc65)
feat(order/rel_classes): Reflexive relation from irreflexive and viceversa ([#13411](https://github.com/leanprover-community/mathlib/pull/13411))
#### Estimated changes
Modified src/order/boolean_algebra.lean




## [2022-05-26 15:16:47](https://github.com/leanprover-community/mathlib/commit/b2973b1)
feat(logic/function/basic): add `function.const_injective` ([#14388](https://github.com/leanprover-community/mathlib/pull/14388))
Add `function.const_injective` and `function.const_inj`.
#### Estimated changes
Modified src/logic/function/basic.lean
- \+ *lemma* function.const_inj
- \+ *lemma* function.const_injective



## [2022-05-26 15:16:46](https://github.com/leanprover-community/mathlib/commit/d3b155b)
chore(data/stream/defs): add spaces around infix operators ([#14386](https://github.com/leanprover-community/mathlib/pull/14386))
#### Estimated changes
Modified src/data/stream/defs.lean




## [2022-05-26 15:16:44](https://github.com/leanprover-community/mathlib/commit/034cf66)
chore(set_theory/ordinal/topology): add `variables` block ([#14369](https://github.com/leanprover-community/mathlib/pull/14369))
We rename a bunch of variables, but don't fundamentally change any proof.
#### Estimated changes
Modified src/set_theory/ordinal/topology.lean
- \+/\- *theorem* ordinal.enum_ord_is_normal_iff_is_closed
- \+/\- *theorem* ordinal.is_closed_iff_bsup
- \+/\- *theorem* ordinal.is_closed_iff_sup
- \+/\- *theorem* ordinal.is_limit_of_mem_frontier
- \+/\- *theorem* ordinal.is_open_iff
- \+/\- *theorem* ordinal.is_open_singleton_iff
- \+/\- *theorem* ordinal.mem_closed_iff_bsup
- \+/\- *theorem* ordinal.mem_closed_iff_sup
- \+/\- *theorem* ordinal.mem_closure_iff_bsup
- \+/\- *theorem* ordinal.mem_closure_iff_sup



## [2022-05-26 15:16:39](https://github.com/leanprover-community/mathlib/commit/be34b95)
feat(topology/separation): split some proofs ([#14337](https://github.com/leanprover-community/mathlib/pull/14337))
#### Estimated changes
Modified src/topology/separation.lean
- \+ *theorem* minimal_nonempty_closed_subsingleton
- \+ *theorem* minimal_nonempty_open_subsingleton



## [2022-05-26 13:56:36](https://github.com/leanprover-community/mathlib/commit/70e784d)
feat(data/polynomial/*): `(p * q).trailing_degree = p.trailing_degree + q.trailing_degree` ([#14384](https://github.com/leanprover-community/mathlib/pull/14384))
We already had a `nat_trailing_degree_mul` lemma, but this PR does things properly, following the analogous results for `degree`. In particular, we now have some useful intermediate results that do not assume `no_zero_divisors`.
#### Estimated changes
Modified src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* polynomial.coeff_mul_nat_trailing_degree_add_nat_trailing_degree
- \+ *lemma* polynomial.nat_trailing_degree_mul'
- \+ *lemma* polynomial.nat_trailing_degree_mul
- \+ *lemma* polynomial.trailing_degree_mul'

Modified src/data/polynomial/mirror.lean


Modified src/data/polynomial/ring_division.lean
- \- *lemma* polynomial.nat_trailing_degree_mul
- \+ *lemma* polynomial.trailing_degree_mul



## [2022-05-26 11:04:30](https://github.com/leanprover-community/mathlib/commit/5aeafaa)
feat(algebra/order/monoid): add `le_iff_exists_mul'` ([#14387](https://github.com/leanprover-community/mathlib/pull/14387))
Add a version of `le_iff_exists_mul'`/`le_iff_exists_add'`, versions of `le_iff_exists_mul`/`le_iff_exists_add` with multiplication on the other side.
#### Estimated changes
Modified src/algebra/order/monoid.lean
- \+ *lemma* le_iff_exists_mul'



## [2022-05-26 09:28:23](https://github.com/leanprover-community/mathlib/commit/acd0509)
feat(order/succ_pred/interval_succ): new file ([#14294](https://github.com/leanprover-community/mathlib/pull/14294))
Add 2 lemmas about `set.Ioc (f x) (f (order.succ x))`, where `f` is a
monotone function.
#### Estimated changes
Modified src/order/succ_pred/basic.lean
- \+ *lemma* order.Ico_succ_right_eq_insert_of_not_is_max
- \+ *lemma* order.Iio_succ_eq_insert_of_not_is_max
- \+ *lemma* order.Ioo_succ_right_eq_insert_of_not_is_max

Added src/order/succ_pred/interval_succ.lean
- \+ *lemma* antitone.pairwise_disjoint_on_Ico_pred
- \+ *lemma* antitone.pairwise_disjoint_on_Ico_succ
- \+ *lemma* antitone.pairwise_disjoint_on_Ioc_pred
- \+ *lemma* antitone.pairwise_disjoint_on_Ioc_succ
- \+ *lemma* antitone.pairwise_disjoint_on_Ioo_pred
- \+ *lemma* antitone.pairwise_disjoint_on_Ioo_succ
- \+ *lemma* monotone.bUnion_Ico_Ioc_map_succ
- \+ *lemma* monotone.pairwise_disjoint_on_Ico_pred
- \+ *lemma* monotone.pairwise_disjoint_on_Ico_succ
- \+ *lemma* monotone.pairwise_disjoint_on_Ioc_pred
- \+ *lemma* monotone.pairwise_disjoint_on_Ioc_succ
- \+ *lemma* monotone.pairwise_disjoint_on_Ioo_pred
- \+ *lemma* monotone.pairwise_disjoint_on_Ioo_succ



## [2022-05-26 05:56:29](https://github.com/leanprover-community/mathlib/commit/4bf1b02)
feat(category_theory/limits): products give pullback squares ([#14327](https://github.com/leanprover-community/mathlib/pull/14327))
Follow-up to [#14220](https://github.com/leanprover-community/mathlib/pull/14220)
#### Estimated changes
Modified src/category_theory/limits/constructions/binary_products.lean


Modified src/category_theory/limits/shapes/comm_sq.lean
- \+ *lemma* category_theory.is_pullback.of_has_binary_product'
- \+ *lemma* category_theory.is_pullback.of_has_binary_product
- \+ *lemma* category_theory.is_pullback.of_is_product
- \+ *lemma* category_theory.is_pushout.of_has_binary_coproduct'
- \+ *lemma* category_theory.is_pushout.of_has_binary_coproduct
- \+ *lemma* category_theory.is_pushout.of_is_coproduct



## [2022-05-26 02:20:40](https://github.com/leanprover-community/mathlib/commit/634bef9)
feat(topology/continuous_function/stone_weierstrass): generalize the complex Stone-Weierstrass theorem to is_R_or_C fields ([#14374](https://github.com/leanprover-community/mathlib/pull/14374))
This PR generalizes the complex Stone-Weierstrass theorem to hold for an `is_R_or_C` field.
#### Estimated changes
Modified src/analysis/fourier.lean


Modified src/data/complex/is_R_or_C.lean
- \+ *lemma* is_R_or_C.continuous_abs
- \+ *lemma* is_R_or_C.continuous_norm_sq

Modified src/topology/continuous_function/stone_weierstrass.lean
- \+/\- *def* continuous_map.conj_invariant_subalgebra
- \+/\- *lemma* continuous_map.mem_conj_invariant_subalgebra
- \- *theorem* continuous_map.subalgebra_complex_topological_closure_eq_top_of_separates_points
- \+ *theorem* continuous_map.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points
- \- *lemma* subalgebra.separates_points.complex_to_real
- \+ *lemma* subalgebra.separates_points.is_R_or_C_to_real



## [2022-05-25 20:40:47](https://github.com/leanprover-community/mathlib/commit/c5b3de8)
refactor(data/polynomial/*): Make `support_C_mul_X_pow` match `support_monomial` ([#14119](https://github.com/leanprover-community/mathlib/pull/14119))
This PR makes `support_C_mul_X_pow` match `support_monomial`.
#### Estimated changes
Modified src/data/polynomial/basic.lean
- \+ *lemma* polynomial.support_C_mul_X_pow'
- \+ *lemma* polynomial.support_C_mul_X_pow
- \+/\- *lemma* polynomial.support_monomial

Modified src/data/polynomial/coeff.lean
- \- *lemma* polynomial.support_C_mul_X_pow'
- \- *lemma* polynomial.support_mul_X_pow

Modified src/data/polynomial/degree/definitions.lean
- \- *lemma* polynomial.support_C_mul_X_pow
- \- *lemma* polynomial.support_C_mul_X_pow_nonzero

Modified src/data/polynomial/degree/trailing_degree.lean


Modified src/ring_theory/polynomial/content.lean




## [2022-05-25 19:08:50](https://github.com/leanprover-community/mathlib/commit/dc0fadd)
feat(linear_algebra/prod): define the graph of a linear map ([#14266](https://github.com/leanprover-community/mathlib/pull/14266))
#### Estimated changes
Modified src/linear_algebra/prod.lean
- \+ *def* linear_map.graph
- \+ *lemma* linear_map.graph_eq_ker_coprod
- \+ *lemma* linear_map.graph_eq_range_prod
- \+ *lemma* linear_map.mem_graph_iff



## [2022-05-25 19:08:49](https://github.com/leanprover-community/mathlib/commit/fae32b6)
refactor(analysis/normed_space/M_structure): generalize to arbitrary faithful actions ([#14222](https://github.com/leanprover-community/mathlib/pull/14222))
This follows up from a comment in review of [#12173](https://github.com/leanprover-community/mathlib/pull/12173)
The motivation here is to allow `X →L[𝕜] X`, `X →+ X`, and other weaker or stronger endomorphisms to also be used
This also tides up a few proof names and some poorly-rendering LaTeX
#### Estimated changes
Modified src/analysis/normed_space/M_structure.lean
- \+/\- *lemma* is_Lprojection.Lcomplement
- \+/\- *lemma* is_Lprojection.Lcomplement_iff
- \+/\- *lemma* is_Lprojection.coe_bot
- \+/\- *lemma* is_Lprojection.coe_compl
- \+/\- *lemma* is_Lprojection.coe_inf
- \+/\- *lemma* is_Lprojection.coe_one
- \+/\- *lemma* is_Lprojection.coe_sdiff
- \+/\- *lemma* is_Lprojection.coe_sup
- \+/\- *lemma* is_Lprojection.coe_top
- \+/\- *lemma* is_Lprojection.coe_zero
- \+/\- *lemma* is_Lprojection.commute
- \+ *lemma* is_Lprojection.compl_mul
- \- *lemma* is_Lprojection.compl_mul_left
- \- *lemma* is_Lprojection.compl_orthog
- \+/\- *lemma* is_Lprojection.distrib_lattice_lemma
- \+/\- *lemma* is_Lprojection.join
- \+/\- *lemma* is_Lprojection.le_def
- \+/\- *lemma* is_Lprojection.mul
- \+ *lemma* is_Lprojection.mul_compl_self
- \+/\- *structure* is_Lprojection
- \+/\- *structure* is_Mprojection



## [2022-05-25 17:33:44](https://github.com/leanprover-community/mathlib/commit/189e5d1)
feat(data/polynomial/degree/trailing_degree): The trailing degree of a product is at least the sum of the trailing degrees ([#14253](https://github.com/leanprover-community/mathlib/pull/14253))
This PR adds lemmas for `nat_trailing_degree` analogous to `degree_mul_le` and `nat_degree_mul_le`.
#### Estimated changes
Modified src/data/polynomial/degree/trailing_degree.lean
- \+ *lemma* polynomial.le_nat_trailing_degree_mul
- \+ *lemma* polynomial.le_trailing_degree_mul



## [2022-05-25 14:21:08](https://github.com/leanprover-community/mathlib/commit/7e1c126)
move(group_theory/perm/cycle/*): A cycle folder ([#14285](https://github.com/leanprover-community/mathlib/pull/14285))
Move:
* `group_theory.perm.cycles` → `group_theory.perm.cycle.basic`
* `group_theory.perm.cycle_type` → `group_theory.perm.cycle.type`
* `group_theory.perm.concrete_cycle` → `group_theory.perm.cycle.concrete`
#### Estimated changes
Modified src/field_theory/polynomial_galois_group.lean


Modified src/group_theory/p_group.lean


Renamed src/group_theory/perm/cycles.lean to src/group_theory/perm/cycle/basic.lean


Renamed src/group_theory/perm/concrete_cycle.lean to src/group_theory/perm/cycle/concrete.lean


Renamed src/group_theory/perm/cycle_type.lean to src/group_theory/perm/cycle/type.lean


Modified src/group_theory/perm/fin.lean




## [2022-05-25 10:28:06](https://github.com/leanprover-community/mathlib/commit/ba1c3f3)
feat(data/int/log): integer logarithms of linearly ordered fields ([#13913](https://github.com/leanprover-community/mathlib/pull/13913))
Notably, this provides a way to find the position of the most significant digit of a decimal expansion
#### Estimated changes
Modified src/algebra/order/floor.lean
- \+ *lemma* int.ceil_one
- \+ *lemma* nat.ceil_one
- \+ *lemma* nat.floor_le_one_of_le_one
- \+ *lemma* nat.floor_lt_one
- \+ *lemma* nat.lt_one_of_floor_lt_one

Modified src/analysis/special_functions/log/base.lean
- \+ *lemma* real.ceil_logb_nat_cast
- \+ *lemma* real.floor_logb_nat_cast

Added src/data/int/log.lean
- \+ *def* int.clog
- \+ *lemma* int.clog_inv
- \+ *lemma* int.clog_mono_right
- \+ *lemma* int.clog_nat_cast
- \+ *lemma* int.clog_of_left_le_one
- \+ *lemma* int.clog_of_one_le_right
- \+ *lemma* int.clog_of_right_le_one
- \+ *lemma* int.clog_of_right_le_zero
- \+ *lemma* int.clog_one_right
- \+ *lemma* int.clog_zero_right
- \+ *lemma* int.clog_zpow
- \+ *def* int.clog_zpow_gi
- \+ *lemma* int.le_zpow_iff_clog_le
- \+ *def* int.log
- \+ *lemma* int.log_inv
- \+ *lemma* int.log_mono_right
- \+ *lemma* int.log_nat_cast
- \+ *lemma* int.log_of_left_le_one
- \+ *lemma* int.log_of_one_le_right
- \+ *lemma* int.log_of_right_le_one
- \+ *lemma* int.log_of_right_le_zero
- \+ *lemma* int.log_one_right
- \+ *lemma* int.log_zero_right
- \+ *lemma* int.log_zpow
- \+ *lemma* int.lt_zpow_iff_log_lt
- \+ *lemma* int.lt_zpow_succ_log_self
- \+ *lemma* int.neg_clog_inv_eq_log
- \+ *lemma* int.neg_log_inv_eq_clog
- \+ *lemma* int.self_le_zpow_clog
- \+ *lemma* int.zpow_le_iff_le_log
- \+ *def* int.zpow_log_gi
- \+ *lemma* int.zpow_log_le_self
- \+ *lemma* int.zpow_lt_iff_lt_clog
- \+ *lemma* int.zpow_pred_clog_lt_self



## [2022-05-25 09:48:16](https://github.com/leanprover-community/mathlib/commit/f8d5c64)
feat(topology/vector_bundle): use trivialization.symm to simplify the product of vector bundles ([#14361](https://github.com/leanprover-community/mathlib/pull/14361))
#### Estimated changes
Modified src/topology/vector_bundle.lean
- \+/\- *def* topological_vector_bundle.pretrivialization.linear_equiv_at
- \+/\- *def* topological_vector_bundle.trivialization.continuous_linear_equiv_at
- \- *lemma* topological_vector_bundle.trivialization.continuous_linear_equiv_at_apply
- \- *lemma* topological_vector_bundle.trivialization.prod.inv_fun'_apply
- \+/\- *lemma* topological_vector_bundle.trivialization.prod_symm_apply



## [2022-05-25 08:59:21](https://github.com/leanprover-community/mathlib/commit/660918b)
feat(measure_theory/function/conditional_expectation): Conditional expectation of an indicator ([#14058](https://github.com/leanprover-community/mathlib/pull/14058))
The main lemma is this:
```lean
lemma condexp_indicator (hf_int : integrable f μ) (hs : measurable_set[m] s) :
  μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m])
```
We also use it to prove that if two sigma algebras are "equal under an event", then the conditional expectations with respect to those two sigma algebras are equal under the same event.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* measure_theory.ae_strongly_measurable'.ae_strongly_measurable'_of_measurable_space_le_on
- \+ *lemma* measure_theory.condexp_L1_congr_ae
- \+ *lemma* measure_theory.condexp_ae_eq_restrict_of_measurable_space_eq_on
- \+ *lemma* measure_theory.condexp_ae_eq_restrict_zero
- \+ *lemma* measure_theory.condexp_congr_ae
- \+ *lemma* measure_theory.condexp_indicator
- \+ *lemma* measure_theory.condexp_indicator_aux

Modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* measure_theory.strongly_measurable.strongly_measurable_in_set
- \+ *lemma* measure_theory.strongly_measurable.strongly_measurable_of_measurable_space_le_on

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* ae_eq_restrict_iff_indicator_ae_eq
- \+ *lemma* indicator_ae_eq_of_restrict_compl_ae_eq_zero
- \+ *lemma* indicator_ae_eq_zero_of_restrict_ae_eq_zero



## [2022-05-25 07:01:43](https://github.com/leanprover-community/mathlib/commit/5da3731)
feat(measure_theory/integral): add formulas for average over an interval ([#14132](https://github.com/leanprover-community/mathlib/pull/14132))
#### Estimated changes
Added src/measure_theory/integral/interval_average.lean
- \+ *lemma* interval_average_eq
- \+ *lemma* interval_average_eq_div
- \+ *lemma* interval_average_symm



## [2022-05-25 02:04:38](https://github.com/leanprover-community/mathlib/commit/c1e2121)
feat(data/set/finite): set priority for fintype_insert' and document ([#14363](https://github.com/leanprover-community/mathlib/pull/14363))
This follows up with some review comments for [#14136](https://github.com/leanprover-community/mathlib/pull/14136).
#### Estimated changes
Modified src/data/set/finite.lean




## [2022-05-25 00:18:41](https://github.com/leanprover-community/mathlib/commit/f582298)
feat(group_theory/subgroup/basic): `zpowers_eq_bot` ([#14366](https://github.com/leanprover-community/mathlib/pull/14366))
This PR adds a lemma `zpowers_eq_bot`.
#### Estimated changes
Modified src/group_theory/subgroup/basic.lean
- \+ *lemma* subgroup.zpowers_eq_bot



## [2022-05-24 19:56:59](https://github.com/leanprover-community/mathlib/commit/ebb5206)
chore(set_theory/surreal/basic): clarify some proofs ([#14356](https://github.com/leanprover-community/mathlib/pull/14356))
#### Estimated changes
Modified src/set_theory/surreal/basic.lean




## [2022-05-24 19:56:58](https://github.com/leanprover-community/mathlib/commit/cdaa6d2)
refactor(analysis/normed_space/pi_Lp): golf some instances ([#14339](https://github.com/leanprover-community/mathlib/pull/14339))
* drop `pi_Lp.emetric_aux`;
* use `T₀` to get `(e)metric_space` from `pseudo_(e)metric_space`;
* restate `pi_Lp.(anti)lipschitz_with_equiv` with correct `pseudo_emetric_space` instances; while they're defeq, it's better not to leak auxiliary instances unless necessary.
#### Estimated changes
Modified src/analysis/normed_space/pi_Lp.lean
- \+/\- *lemma* pi_Lp.antilipschitz_with_equiv
- \+ *lemma* pi_Lp.antilipschitz_with_equiv_aux
- \+/\- *lemma* pi_Lp.edist_eq
- \- *def* pi_Lp.emetric_aux
- \+/\- *lemma* pi_Lp.lipschitz_with_equiv
- \+ *lemma* pi_Lp.lipschitz_with_equiv_aux



## [2022-05-24 19:02:02](https://github.com/leanprover-community/mathlib/commit/23f30a3)
fix(topology/vector_bundle): squeeze simp, remove non-terminal simp ([#14357](https://github.com/leanprover-community/mathlib/pull/14357))
For some reason I had to mention `trivialization.coe_coe` explicitly, even though it is in `mfld_simps` (maybe because another simp lemma would otherwise apply first?)
#### Estimated changes
Modified src/topology/vector_bundle.lean




## [2022-05-24 16:46:14](https://github.com/leanprover-community/mathlib/commit/88f8de3)
feat(topology/local_homeomorph): define helper definition ([#14360](https://github.com/leanprover-community/mathlib/pull/14360))
* Define `homeomorph.trans_local_homeomorph` and `local_homeomorph.trans_homeomorph`. They are equal to `local_homeomorph.trans`, but with better definitional behavior for `source` and `target`.
* Define similar operations for `local_equiv`.
* Use this to improve the definitional behavior of [`topological_fiber_bundle.trivialization.trans_fiber_homeomorph`](https://leanprover-community.github.io/mathlib_docs/find/topological_fiber_bundle.trivialization.trans_fiber_homeomorph)
* Also use `@[simps]` to generate a couple of extra simp-lemmas.
#### Estimated changes
Modified src/logic/equiv/local_equiv.lean
- \+/\- *def* equiv.to_local_equiv
- \- *lemma* equiv.to_local_equiv_coe
- \- *lemma* equiv.to_local_equiv_source
- \- *lemma* equiv.to_local_equiv_symm_coe
- \- *lemma* equiv.to_local_equiv_target
- \+ *def* equiv.trans_local_equiv
- \+ *lemma* equiv.trans_local_equiv_eq_trans
- \+/\- *def* local_equiv.copy
- \+/\- *def* local_equiv.disjoint_union
- \+/\- *def* local_equiv.is_image.restr
- \- *lemma* local_equiv.pi_coe
- \- *lemma* local_equiv.pi_symm
- \+/\- *def* local_equiv.piecewise
- \+ *def* local_equiv.trans_equiv
- \+ *lemma* local_equiv.trans_equiv_eq_trans

Modified src/topology/fiber_bundle.lean


Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.coe_symm_to_equiv

Modified src/topology/local_homeomorph.lean
- \+/\- *def* homeomorph.to_local_homeomorph
- \- *lemma* homeomorph.to_local_homeomorph_coe_symm
- \+ *def* homeomorph.trans_local_homeomorph
- \+ *lemma* homeomorph.trans_local_homeomorph_eq_trans
- \+ *lemma* local_homeomorph.to_local_equiv_injective
- \+ *lemma* local_homeomorph.trans_equiv_eq_trans
- \+ *def* local_homeomorph.trans_homeomorph



## [2022-05-24 16:46:12](https://github.com/leanprover-community/mathlib/commit/483b54f)
refactor(logic/equiv/set): open set namespace ([#14355](https://github.com/leanprover-community/mathlib/pull/14355))
#### Estimated changes
Modified src/logic/equiv/set.lean
- \+/\- *theorem* equiv.apply_of_injective_symm
- \+/\- *lemma* equiv.range_eq_univ



## [2022-05-24 16:46:11](https://github.com/leanprover-community/mathlib/commit/ec8587f)
chore(data/list/forall2): fix incorrect docstring ([#14276](https://github.com/leanprover-community/mathlib/pull/14276))
The previous docstring was false, this corrects the definition.
#### Estimated changes
Modified src/data/list/forall2.lean




## [2022-05-24 15:53:41](https://github.com/leanprover-community/mathlib/commit/73a6125)
feat(linear_algebra/bilinear_form): generalize scalar instances, fix diamonds ([#14358](https://github.com/leanprover-community/mathlib/pull/14358))
This fixes the zsmul and nsmul diamonds, makes sub definitionally better, and makes the scalar instance apply more generally.
This also adds `linear_map.comp_bilin_form`.
These changes bring the API more in line with `quadratic_form`.
#### Estimated changes
Modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* bilin_form.add_apply
- \+ *lemma* bilin_form.coe_add
- \+ *def* bilin_form.coe_fn_add_monoid_hom
- \+ *lemma* bilin_form.coe_injective
- \+ *lemma* bilin_form.coe_neg
- \+ *lemma* bilin_form.coe_smul
- \+ *lemma* bilin_form.coe_sub
- \+ *lemma* bilin_form.coe_zero
- \+/\- *lemma* bilin_form.neg_apply
- \+/\- *lemma* bilin_form.smul_apply
- \+ *lemma* bilin_form.sub_apply
- \+/\- *lemma* bilin_form.zero_apply
- \+ *def* linear_map.comp_bilin_form



## [2022-05-24 14:54:33](https://github.com/leanprover-community/mathlib/commit/28f7172)
refactor(algebra/direct_sum/basic): use the new polymorphic subobject API   ([#14341](https://github.com/leanprover-community/mathlib/pull/14341))
This doesn't let us deduplicate the lattice lemmas, but does eliminate the duplicate instances and definitions!
This merges:
* `direct_sum.add_submonoid_is_internal`, `direct_sum.add_subgroup_is_internal`, `direct_sum.submodule_is_internal` into `direct_sum.is_internal`
* `direct_sum.add_submonoid_coe`, `direct_sum.add_subgroup_coe` into `direct_sum.coe_add_monoid_hom`
* `direct_sum.add_submonoid_coe_ring_hom`, `direct_sum.add_subgroup_coe_ring_hom` into `direct_sum.coe_ring_hom`
* `add_submonoid.gsemiring`, `add_subgroup.gsemiring`, `submodule.gsemiring` into `set_like.gsemiring`
* `add_submonoid.gcomm_semiring`, `add_subgroup.gcomm_semiring`, `submodule.gcomm_semiring` into `set_like.gcomm_semiring`
Renames
* `direct_sum.submodule_coe` into `direct_sum.coe_linear_map`
* `direct_sum.submodule_coe_alg_hom` into `direct_sum.coe_alg_hom
And adds:
* `set_like.gnon_unital_non_assoc_semiring`, now that it doesn't need to be repeated three times!
A large number of related lemmas are also renamed to match the new definition names.
This was what originally motivated the `set_like` typeclass; thanks to @Vierkantor for doing the subobject follow up I never got around to!
#### Estimated changes
Modified counterexamples/direct_sum_is_internal.lean
- \+/\- *lemma* with_sign.not_internal

Modified counterexamples/homogeneous_prime_not_prime.lean


Modified docs/undergrad.yaml


Modified src/algebra/direct_sum/basic.lean
- \- *def* direct_sum.add_subgroup_coe
- \- *lemma* direct_sum.add_subgroup_coe_of
- \- *lemma* direct_sum.add_subgroup_is_internal.to_add_submonoid
- \- *def* direct_sum.add_subgroup_is_internal
- \- *def* direct_sum.add_submonoid_coe
- \- *lemma* direct_sum.add_submonoid_coe_of
- \- *lemma* direct_sum.add_submonoid_is_internal.supr_eq_top
- \- *def* direct_sum.add_submonoid_is_internal
- \+ *lemma* direct_sum.coe_add_monoid_hom_of
- \- *lemma* direct_sum.coe_of_add_subgroup_apply
- \- *lemma* direct_sum.coe_of_add_submonoid_apply
- \+ *lemma* direct_sum.coe_of_apply
- \+ *lemma* direct_sum.is_internal.add_submonoid_supr_eq_top
- \+ *def* direct_sum.is_internal

Modified src/algebra/direct_sum/internal.lean
- \+ *def* direct_sum.coe_alg_hom
- \+ *lemma* direct_sum.coe_alg_hom_of
- \+ *lemma* direct_sum.coe_mul_apply
- \- *lemma* direct_sum.coe_mul_apply_add_subgroup
- \- *lemma* direct_sum.coe_mul_apply_add_submonoid
- \- *lemma* direct_sum.coe_mul_apply_submodule
- \+ *def* direct_sum.coe_ring_hom
- \+ *lemma* direct_sum.coe_ring_hom_of
- \- *def* direct_sum.subgroup_coe_ring_hom
- \- *lemma* direct_sum.subgroup_coe_ring_hom_of
- \- *def* direct_sum.submodule_coe_alg_hom
- \- *lemma* direct_sum.submodule_coe_alg_hom_of
- \- *def* direct_sum.submonoid_coe_ring_hom
- \- *lemma* direct_sum.submonoid_coe_ring_hom_of

Modified src/algebra/direct_sum/module.lean
- \- *lemma* direct_sum.add_subgroup_is_internal.independent
- \- *lemma* direct_sum.add_submonoid_is_internal.independent
- \+ *def* direct_sum.coe_linear_map
- \+ *lemma* direct_sum.coe_linear_map_of
- \- *lemma* direct_sum.coe_of_submodule_apply
- \+ *lemma* direct_sum.is_internal.add_subgroup_independent
- \+ *lemma* direct_sum.is_internal.add_submonoid_independent
- \+ *lemma* direct_sum.is_internal.collected_basis_coe
- \+ *lemma* direct_sum.is_internal.collected_basis_mem
- \+ *lemma* direct_sum.is_internal.is_compl
- \+ *lemma* direct_sum.is_internal.submodule_independent
- \+ *lemma* direct_sum.is_internal.submodule_supr_eq_top
- \+ *lemma* direct_sum.is_internal_submodule_iff_independent_and_supr_eq_top
- \+ *lemma* direct_sum.is_internal_submodule_iff_is_compl
- \+ *lemma* direct_sum.is_internal_submodule_of_independent_of_supr_eq_top
- \- *def* direct_sum.submodule_coe
- \- *lemma* direct_sum.submodule_coe_of
- \- *lemma* direct_sum.submodule_is_internal.collected_basis_coe
- \- *lemma* direct_sum.submodule_is_internal.collected_basis_mem
- \- *lemma* direct_sum.submodule_is_internal.independent
- \- *lemma* direct_sum.submodule_is_internal.is_compl
- \- *lemma* direct_sum.submodule_is_internal.supr_eq_top
- \- *lemma* direct_sum.submodule_is_internal.to_add_subgroup
- \- *lemma* direct_sum.submodule_is_internal.to_add_submonoid
- \- *def* direct_sum.submodule_is_internal
- \- *lemma* direct_sum.submodule_is_internal_iff_independent_and_supr_eq_top
- \- *lemma* direct_sum.submodule_is_internal_iff_is_compl
- \- *lemma* direct_sum.submodule_is_internal_of_independent_of_supr_eq_top

Modified src/algebra/graded_monoid.lean


Modified src/algebra/module/torsion.lean


Modified src/algebra/monoid_algebra/grading.lean
- \+/\- *lemma* add_monoid_algebra.grade.is_internal
- \+/\- *lemma* add_monoid_algebra.grade_by.is_internal

Modified src/analysis/inner_product_space/basic.lean
- \+ *lemma* direct_sum.is_internal.collected_basis_orthonormal
- \- *lemma* direct_sum.submodule_is_internal.collected_basis_orthonormal

Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *def* direct_sum.is_internal.isometry_L2_of_orthogonal_family
- \+ *lemma* direct_sum.is_internal.isometry_L2_of_orthogonal_family_symm_apply
- \- *def* direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family
- \- *lemma* direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply

Modified src/analysis/inner_product_space/projection.lean
- \+ *def* direct_sum.is_internal.sigma_orthonormal_basis_index_equiv
- \+ *def* direct_sum.is_internal.subordinate_orthonormal_basis
- \+ *def* direct_sum.is_internal.subordinate_orthonormal_basis_index
- \+ *lemma* direct_sum.is_internal.subordinate_orthonormal_basis_orthonormal
- \+ *lemma* direct_sum.is_internal.subordinate_orthonormal_basis_subordinate
- \- *def* direct_sum.submodule_is_internal.sigma_orthonormal_basis_index_equiv
- \- *def* direct_sum.submodule_is_internal.subordinate_orthonormal_basis
- \- *def* direct_sum.submodule_is_internal.subordinate_orthonormal_basis_index
- \- *lemma* direct_sum.submodule_is_internal.subordinate_orthonormal_basis_orthonormal
- \- *lemma* direct_sum.submodule_is_internal.subordinate_orthonormal_basis_subordinate
- \+ *lemma* orthogonal_family.is_internal_iff
- \+ *lemma* orthogonal_family.is_internal_iff_of_is_complete
- \- *lemma* orthogonal_family.submodule_is_internal_iff
- \- *lemma* orthogonal_family.submodule_is_internal_iff_of_is_complete

Modified src/analysis/inner_product_space/spectrum.lean
- \+ *lemma* inner_product_space.is_self_adjoint.direct_sum_is_internal
- \- *lemma* inner_product_space.is_self_adjoint.direct_sum_submodule_is_internal

Modified src/linear_algebra/clifford_algebra/grading.lean


Modified src/linear_algebra/exterior_algebra/grading.lean


Modified src/linear_algebra/tensor_algebra/grading.lean


Modified src/ring_theory/graded_algebra/basic.lean
- \- *lemma* graded_algebra.is_internal

Modified src/ring_theory/graded_algebra/homogeneous_ideal.lean


Modified src/ring_theory/graded_algebra/radical.lean




## [2022-05-24 14:17:37](https://github.com/leanprover-community/mathlib/commit/a07493a)
feat(analysis/convolution): the predicate `convolution_exists` ([#13541](https://github.com/leanprover-community/mathlib/pull/13541))
* This PR defines the predicate that a convolution exists.
* This is not that interesting by itself, but it is a preparation for [#13540](https://github.com/leanprover-community/mathlib/pull/13540)
* I'm using the full module doc for the convolution file, even though not everything promised in the module doc is in this PR.
* From the sphere eversion project
#### Estimated changes
Added src/analysis/convolution.lean
- \+ *lemma* bdd_above.convolution_exists_at'
- \+ *lemma* bdd_above.convolution_exists_at
- \+ *lemma* continuous.convolution_integrand_fst
- \+ *def* convolution_exists
- \+ *lemma* convolution_exists_at.integrable
- \+ *lemma* convolution_exists_at.integrable_swap
- \+ *def* convolution_exists_at
- \+ *lemma* convolution_exists_at_flip
- \+ *lemma* convolution_exists_at_iff_integrable_swap
- \+ *lemma* has_compact_support.convolution_exists_at
- \+ *lemma* has_compact_support.convolution_exists_left
- \+ *lemma* has_compact_support.convolution_exists_left_of_continuous_right
- \+ *lemma* has_compact_support.convolution_exists_right
- \+ *lemma* has_compact_support.convolution_exists_right_of_continuous_left
- \+ *lemma* has_compact_support.convolution_integrand_bound_left
- \+ *lemma* has_compact_support.convolution_integrand_bound_right
- \+ *lemma* measure_theory.ae_strongly_measurable.convolution_integrand'
- \+ *lemma* measure_theory.ae_strongly_measurable.convolution_integrand
- \+ *lemma* measure_theory.ae_strongly_measurable.convolution_integrand_snd'
- \+ *lemma* measure_theory.ae_strongly_measurable.convolution_integrand_snd
- \+ *lemma* measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd'
- \+ *lemma* measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd
- \+ *lemma* measure_theory.integrable.ae_convolution_exists
- \+ *lemma* measure_theory.integrable.convolution_integrand



## [2022-05-24 12:33:08](https://github.com/leanprover-community/mathlib/commit/dc22d65)
doc(100.yaml): add Law of Large Numbers ([#14353](https://github.com/leanprover-community/mathlib/pull/14353))
#### Estimated changes
Modified docs/100.yaml




## [2022-05-24 12:33:07](https://github.com/leanprover-community/mathlib/commit/9d193c5)
feat(category_theory/comm_sq): functors mapping pullback/pushout squares ([#14351](https://github.com/leanprover-community/mathlib/pull/14351))
```
lemma map_is_pullback [preserves_limit (cospan h i) F] (s : is_pullback f g h i) :
  is_pullback (F.map f) (F.map g) (F.map h) (F.map i) := ...
```
#### Estimated changes
Modified src/category_theory/limits/shapes/comm_sq.lean
- \+ *def* category_theory.comm_sq.cocone
- \+ *def* category_theory.comm_sq.cone
- \+ *lemma* category_theory.comm_sq.flip
- \+ *lemma* category_theory.comm_sq.of_arrow
- \+ *structure* category_theory.comm_sq
- \+ *lemma* category_theory.functor.map_comm_sq
- \+ *lemma* category_theory.functor.map_is_pullback
- \+ *lemma* category_theory.functor.map_is_pushout
- \+ *def* category_theory.is_pullback.cone
- \+ *lemma* category_theory.is_pullback.flip
- \+ *def* category_theory.is_pullback.iso_pullback
- \+ *lemma* category_theory.is_pullback.iso_pullback_hom_fst
- \+ *lemma* category_theory.is_pullback.iso_pullback_hom_snd
- \+ *lemma* category_theory.is_pullback.iso_pullback_inv_fst
- \+ *lemma* category_theory.is_pullback.iso_pullback_inv_snd
- \+ *lemma* category_theory.is_pullback.of_bot
- \+ *lemma* category_theory.is_pullback.of_has_pullback
- \+ *lemma* category_theory.is_pullback.of_is_limit'
- \+ *lemma* category_theory.is_pullback.of_is_limit
- \+ *lemma* category_theory.is_pullback.of_iso_pullback
- \+ *lemma* category_theory.is_pullback.of_right
- \+ *lemma* category_theory.is_pullback.paste_horiz
- \+ *lemma* category_theory.is_pullback.paste_vert
- \+ *lemma* category_theory.is_pullback.zero_left
- \+ *lemma* category_theory.is_pullback.zero_top
- \+ *structure* category_theory.is_pullback
- \+ *def* category_theory.is_pushout.cocone
- \+ *lemma* category_theory.is_pushout.flip
- \+ *lemma* category_theory.is_pushout.inl_iso_pushout_hom
- \+ *lemma* category_theory.is_pushout.inl_iso_pushout_inv
- \+ *lemma* category_theory.is_pushout.inr_iso_pushout_hom
- \+ *lemma* category_theory.is_pushout.inr_iso_pushout_inv
- \+ *def* category_theory.is_pushout.iso_pushout
- \+ *lemma* category_theory.is_pushout.of_bot
- \+ *lemma* category_theory.is_pushout.of_has_pushout
- \+ *lemma* category_theory.is_pushout.of_is_colimit'
- \+ *lemma* category_theory.is_pushout.of_is_colimit
- \+ *lemma* category_theory.is_pushout.of_iso_pushout
- \+ *lemma* category_theory.is_pushout.of_right
- \+ *lemma* category_theory.is_pushout.paste_horiz
- \+ *lemma* category_theory.is_pushout.paste_vert
- \+ *lemma* category_theory.is_pushout.zero_bot
- \+ *lemma* category_theory.is_pushout.zero_right
- \+ *structure* category_theory.is_pushout
- \- *lemma* category_theory.limits.comm_sq.flip
- \- *lemma* category_theory.limits.comm_sq.of_arrow
- \- *structure* category_theory.limits.comm_sq
- \- *def* category_theory.limits.is_pullback.cone
- \- *lemma* category_theory.limits.is_pullback.flip
- \- *lemma* category_theory.limits.is_pullback.of_bot
- \- *lemma* category_theory.limits.is_pullback.of_has_pullback
- \- *lemma* category_theory.limits.is_pullback.of_is_limit
- \- *lemma* category_theory.limits.is_pullback.of_right
- \- *lemma* category_theory.limits.is_pullback.paste_horiz
- \- *lemma* category_theory.limits.is_pullback.paste_vert
- \- *lemma* category_theory.limits.is_pullback.zero_left
- \- *lemma* category_theory.limits.is_pullback.zero_top
- \- *structure* category_theory.limits.is_pullback
- \- *def* category_theory.limits.is_pushout.cocone
- \- *lemma* category_theory.limits.is_pushout.flip
- \- *lemma* category_theory.limits.is_pushout.of_bot
- \- *lemma* category_theory.limits.is_pushout.of_has_pushout
- \- *lemma* category_theory.limits.is_pushout.of_is_colimit
- \- *lemma* category_theory.limits.is_pushout.of_right
- \- *lemma* category_theory.limits.is_pushout.paste_horiz
- \- *lemma* category_theory.limits.is_pushout.paste_vert
- \- *lemma* category_theory.limits.is_pushout.zero_bot
- \- *lemma* category_theory.limits.is_pushout.zero_right
- \- *structure* category_theory.limits.is_pushout

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.walking_cospan.ext
- \+ *def* category_theory.limits.walking_span.ext



## [2022-05-24 12:33:06](https://github.com/leanprover-community/mathlib/commit/53a70a0)
feat(linear_algebra/tensor_power): Add notation for tensor powers, and a definition of multiplication ([#14196](https://github.com/leanprover-community/mathlib/pull/14196))
This file introduces the notation `⨂[R]^n M` for `tensor_power R n M`, which in turn is an
abbreviation for `⨂[R] i : fin n, M`.
The proof that this multiplication forms a semiring will come in a later PR ([#10255](https://github.com/leanprover-community/mathlib/pull/10255)).
#### Estimated changes
Added src/linear_algebra/tensor_power.lean
- \+ *lemma* tensor_power.ghas_mul_def
- \+ *lemma* tensor_power.ghas_one_def
- \+ *def* tensor_power.mul_equiv



## [2022-05-24 12:33:05](https://github.com/leanprover-community/mathlib/commit/8e3deff)
feat(representation_theory/invariants): average_map is a projection onto the subspace of invariants ([#14167](https://github.com/leanprover-community/mathlib/pull/14167))
#### Estimated changes
Modified src/linear_algebra/projection.lean
- \+/\- *def* linear_map.is_proj.cod_restrict
- \+/\- *lemma* linear_map.is_proj.cod_restrict_apply
- \+/\- *lemma* linear_map.is_proj.cod_restrict_apply_cod
- \+/\- *lemma* linear_map.is_proj.cod_restrict_ker
- \+/\- *structure* linear_map.is_proj
- \+/\- *lemma* linear_map.is_proj_iff_idempotent

Modified src/representation_theory/invariants.lean
- \+ *theorem* representation.is_proj_average_map



## [2022-05-24 10:24:08](https://github.com/leanprover-community/mathlib/commit/893f480)
feat(group_theory/index): Lemmas for when `relindex` divides `index` ([#14314](https://github.com/leanprover-community/mathlib/pull/14314))
This PR adds two lemmas for when `relindex` divides `index`.
#### Estimated changes
Modified src/group_theory/index.lean
- \+ *lemma* subgroup.relindex_dvd_index_of_le
- \+ *lemma* subgroup.relindex_dvd_index_of_normal



## [2022-05-24 10:24:07](https://github.com/leanprover-community/mathlib/commit/65f1f8e)
feat(linear_algebra/quadratic_form/isometry): extract from `linear_algebra/quadratic_form/basic` ([#14305](https://github.com/leanprover-community/mathlib/pull/14305))
150 lines seems worthy of its own file, especially if this grows `fun_like` boilerplate in future.
No lemmas have been renamed or proofs changed.
#### Estimated changes
Modified src/linear_algebra/clifford_algebra/basic.lean


Modified src/linear_algebra/quadratic_form/basic.lean
- \- *lemma* quadratic_form.equivalent.refl
- \- *lemma* quadratic_form.equivalent.symm
- \- *lemma* quadratic_form.equivalent.trans
- \- *def* quadratic_form.equivalent
- \- *lemma* quadratic_form.equivalent_weighted_sum_squares
- \- *lemma* quadratic_form.equivalent_weighted_sum_squares_units_of_nondegenerate'
- \- *lemma* quadratic_form.isometry.coe_to_linear_equiv
- \- *lemma* quadratic_form.isometry.map_app
- \- *def* quadratic_form.isometry.refl
- \- *def* quadratic_form.isometry.symm
- \- *lemma* quadratic_form.isometry.to_linear_equiv_eq_coe
- \- *def* quadratic_form.isometry.trans
- \- *structure* quadratic_form.isometry
- \- *def* quadratic_form.isometry_of_comp_linear_equiv

Modified src/linear_algebra/quadratic_form/complex.lean


Added src/linear_algebra/quadratic_form/isometry.lean
- \+ *lemma* quadratic_form.equivalent.refl
- \+ *lemma* quadratic_form.equivalent.symm
- \+ *lemma* quadratic_form.equivalent.trans
- \+ *def* quadratic_form.equivalent
- \+ *lemma* quadratic_form.equivalent_weighted_sum_squares
- \+ *lemma* quadratic_form.equivalent_weighted_sum_squares_units_of_nondegenerate'
- \+ *lemma* quadratic_form.isometry.coe_to_linear_equiv
- \+ *lemma* quadratic_form.isometry.map_app
- \+ *def* quadratic_form.isometry.refl
- \+ *def* quadratic_form.isometry.symm
- \+ *lemma* quadratic_form.isometry.to_linear_equiv_eq_coe
- \+ *def* quadratic_form.isometry.trans
- \+ *structure* quadratic_form.isometry
- \+ *def* quadratic_form.isometry_of_comp_linear_equiv

Modified src/linear_algebra/quadratic_form/prod.lean


Modified src/linear_algebra/quadratic_form/real.lean




## [2022-05-24 10:24:06](https://github.com/leanprover-community/mathlib/commit/9870d13)
chore(order/bounded_order): Golf `disjoint` API ([#14194](https://github.com/leanprover-community/mathlib/pull/14194))
Reorder lemmas and golf.
Lemma additions:
* `disjoint.eq_bot_of_ge`
* `is_compl.of_dual`
* `is_compl_to_dual_iff`
* `is_compl_of_dual_iff`
Lemma deletions:
* `eq_bot_of_disjoint_absorbs`: This is an unhelpful combination of `disjoint.eq_bot_of_ge` and `sup_eq_left`
* `inf_eq_bot_iff_le_compl`: This is a worse version of `is_compl.disjoint_left_iff`
Lemma renames:
* `is_compl.to_order_dual` → `is_compl.dual`
#### Estimated changes
Modified src/order/bounded_order.lean
- \+ *lemma* disjoint.comm
- \- *theorem* disjoint.comm
- \+ *lemma* disjoint.eq_bot
- \- *theorem* disjoint.eq_bot
- \+ *lemma* disjoint.eq_bot_of_ge
- \+/\- *lemma* disjoint.eq_bot_of_le
- \+/\- *lemma* disjoint.inf_left'
- \+/\- *lemma* disjoint.inf_left
- \+/\- *lemma* disjoint.inf_right'
- \+/\- *lemma* disjoint.inf_right
- \+/\- *lemma* disjoint.left_le_of_le_sup_left
- \+/\- *lemma* disjoint.left_le_of_le_sup_right
- \+ *lemma* disjoint.mono
- \- *theorem* disjoint.mono
- \+ *lemma* disjoint.mono_left
- \- *theorem* disjoint.mono_left
- \+ *lemma* disjoint.mono_right
- \- *theorem* disjoint.mono_right
- \+/\- *lemma* disjoint.ne
- \+/\- *lemma* disjoint.of_disjoint_inf_of_le'
- \+/\- *lemma* disjoint.of_disjoint_inf_of_le
- \+ *lemma* disjoint.symm
- \- *theorem* disjoint.symm
- \+/\- *lemma* disjoint_assoc
- \+ *lemma* disjoint_bot_left
- \- *theorem* disjoint_bot_left
- \+ *lemma* disjoint_bot_right
- \- *theorem* disjoint_bot_right
- \+ *lemma* disjoint_iff
- \- *theorem* disjoint_iff
- \+/\- *lemma* disjoint_self
- \- *lemma* eq_bot_of_disjoint_absorbs
- \+/\- *lemma* eq_bot_of_is_compl_top
- \+/\- *lemma* eq_bot_of_top_is_compl
- \+/\- *lemma* eq_top_of_bot_is_compl
- \+/\- *lemma* eq_top_of_is_compl_bot
- \- *lemma* inf_eq_bot_iff_le_compl
- \+ *lemma* is_compl.dual
- \+/\- *lemma* is_compl.left_le_iff
- \+ *lemma* is_compl.of_dual
- \+/\- *lemma* is_compl.of_eq
- \- *lemma* is_compl.to_order_dual
- \+/\- *lemma* is_compl_bot_top
- \+ *lemma* is_compl_of_dual_iff
- \+ *lemma* is_compl_to_dual_iff
- \+/\- *lemma* is_compl_top_bot
- \+/\- *lemma* max_bot_left
- \+/\- *lemma* max_bot_right
- \+/\- *lemma* max_top_left
- \+/\- *lemma* max_top_right
- \+/\- *lemma* min_bot_left
- \+/\- *lemma* min_bot_right
- \+/\- *lemma* min_top_left
- \+/\- *lemma* min_top_right

Modified src/ring_theory/artinian.lean


Modified src/ring_theory/noetherian.lean




## [2022-05-24 08:19:34](https://github.com/leanprover-community/mathlib/commit/533c67b)
feat(analysis/sum_integral_comparisons): Comparison lemmas between finite sums and integrals ([#13179](https://github.com/leanprover-community/mathlib/pull/13179))
In this pull request we target the following lemmas:
```lean
lemma antitone_on.integral_le_sum {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ}
   (hf : antitone_on f (Icc x₀ (x₀ + a))) :
   ∫ x in x₀..(x₀ + a), f x ≤ ∑ i in finset.range a, f (x₀ + i)
lemma antitone_on.sum_le_integral
   {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ}
   (hf : antitone_on f (Icc x₀ (x₀ + a))) :
   ∑ i in finset.range a, f (x₀ + i + 1) ≤ ∫ x in x₀..(x₀ + a), f x :=
```
as well as their `monotone_on` equivalents.
These lemmas are critical to many analytic facts, specifically because it so often is the way that error terms end up getting computed.
#### Estimated changes
Modified src/algebra/order/group.lean
- \+ *lemma* antitone.inv
- \+ *lemma* antitone_on.inv
- \+ *lemma* monotone.inv
- \+ *lemma* monotone_on.inv
- \+ *lemma* strict_anti.inv
- \+ *lemma* strict_anti_on.inv
- \+ *lemma* strict_mono.inv
- \+ *lemma* strict_mono_on.inv

Modified src/analysis/special_functions/integrals.lean
- \+ *lemma* integral_const_on_unit_interval

Added src/analysis/sum_integral_comparisons.lean
- \+ *lemma* antitone_on.integral_le_sum
- \+ *lemma* antitone_on.integral_le_sum_Ico
- \+ *lemma* antitone_on.sum_le_integral
- \+ *lemma* antitone_on.sum_le_integral_Ico
- \+ *lemma* monotone_on.integral_le_sum
- \+ *lemma* monotone_on.integral_le_sum_Ico
- \+ *lemma* monotone_on.sum_le_integral
- \+ *lemma* monotone_on.sum_le_integral_Ico



## [2022-05-24 07:08:08](https://github.com/leanprover-community/mathlib/commit/93df724)
feat(measure_theory/integral/integral_eq_improper): Covering finite intervals by finite intervals ([#13514](https://github.com/leanprover-community/mathlib/pull/13514))
Currently, the ability to prove facts about improper integrals only allows for at least one infinite endpoint. However, it is a common need to work with functions that blow up at an end point (e.g., x^r on [0, 1] for r in (-1, 0)). As a step toward allowing that, we introduce `ae_cover`s that allow exhausting finite intervals by finite intervals.
Partially addresses: [#12666](https://github.com/leanprover-community/mathlib/pull/12666)
#### Estimated changes
Modified src/measure_theory/integral/integral_eq_improper.lean
- \+ *lemma* measure_theory.ae_cover_Icc_of_Icc
- \+ *lemma* measure_theory.ae_cover_Icc_of_Ico
- \+ *lemma* measure_theory.ae_cover_Icc_of_Ioc
- \+ *lemma* measure_theory.ae_cover_Icc_of_Ioo
- \+ *lemma* measure_theory.ae_cover_Ico_of_Icc
- \+ *lemma* measure_theory.ae_cover_Ico_of_Ico
- \+ *lemma* measure_theory.ae_cover_Ico_of_Ioc
- \+ *lemma* measure_theory.ae_cover_Ico_of_Ioo
- \+ *lemma* measure_theory.ae_cover_Ioc_of_Icc
- \+ *lemma* measure_theory.ae_cover_Ioc_of_Ico
- \+ *lemma* measure_theory.ae_cover_Ioc_of_Ioc
- \+ *lemma* measure_theory.ae_cover_Ioc_of_Ioo
- \+ *lemma* measure_theory.ae_cover_Ioo_of_Icc
- \+ *lemma* measure_theory.ae_cover_Ioo_of_Ico
- \+ *lemma* measure_theory.ae_cover_Ioo_of_Ioc
- \+ *lemma* measure_theory.ae_cover_Ioo_of_Ioo

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.ae_restrict_congr_set
- \+ *lemma* measure_theory.ae_restrict_of_ae_eq_of_ae_restrict

Modified src/topology/algebra/order/basic.lean
- \+ *lemma* eventually_ge_nhds
- \+ *lemma* eventually_gt_nhds
- \+ *lemma* eventually_le_nhds
- \+ *lemma* eventually_lt_nhds



## [2022-05-24 06:28:33](https://github.com/leanprover-community/mathlib/commit/0973ad4)
feat(probability/strong_law): the strong law of large numbers ([#13690](https://github.com/leanprover-community/mathlib/pull/13690))
We prove the almost sure version of the strong law of large numbers: given an iid sequence of integrable random variables `X_i`, then `(\sum_{i < n} X_i)/n` converges almost surely to `E(X)`. We follow Etemadi's proof, which only requires pairwise independence instead of full independence.
#### Estimated changes
Modified docs/references.bib


Modified docs/undergrad.yaml


Added src/probability/strong_law.lean
- \+ *lemma* measure_theory.ae_strongly_measurable.integrable_truncation
- \+ *lemma* measure_theory.ae_strongly_measurable.mem_ℒp_truncation
- \+ *lemma* measure_theory.ae_strongly_measurable.truncation
- \+ *lemma* probability_theory.abs_truncation_le_abs_self
- \+ *lemma* probability_theory.abs_truncation_le_bound
- \+ *lemma* probability_theory.ident_distrib.truncation
- \+ *lemma* probability_theory.integral_truncation_eq_interval_integral
- \+ *lemma* probability_theory.integral_truncation_eq_interval_integral_of_nonneg
- \+ *lemma* probability_theory.integral_truncation_le_integral_of_nonneg
- \+ *lemma* probability_theory.moment_truncation_eq_interval_integral
- \+ *lemma* probability_theory.moment_truncation_eq_interval_integral_of_nonneg
- \+ *theorem* probability_theory.strong_law_ae
- \+ *lemma* probability_theory.strong_law_aux1
- \+ *lemma* probability_theory.strong_law_aux2
- \+ *lemma* probability_theory.strong_law_aux3
- \+ *lemma* probability_theory.strong_law_aux4
- \+ *lemma* probability_theory.strong_law_aux5
- \+ *lemma* probability_theory.strong_law_aux6
- \+ *lemma* probability_theory.strong_law_aux7
- \+ *lemma* probability_theory.sum_prob_mem_Ioc_le
- \+ *lemma* probability_theory.sum_variance_truncation_le
- \+ *lemma* probability_theory.tendsto_integral_truncation
- \+ *def* probability_theory.truncation
- \+ *lemma* probability_theory.truncation_eq_of_nonneg
- \+ *lemma* probability_theory.truncation_eq_self
- \+ *lemma* probability_theory.truncation_nonneg
- \+ *lemma* probability_theory.truncation_zero
- \+ *lemma* probability_theory.tsum_prob_mem_Ioi_lt_top



## [2022-05-24 05:19:10](https://github.com/leanprover-community/mathlib/commit/0d14ee8)
feat(field_theory/finite/galois_field): Finite fields are Galois ([#14290](https://github.com/leanprover-community/mathlib/pull/14290))
This PR also generalizes a section of `field_theory/finite/basic` from `[char_p K p]` to `[algebra (zmod p) K]`. This is indeed a generalization, due to the presence of the instance `zmod.algebra`.
#### Estimated changes
Modified src/algebra/char_p/algebra.lean
- \+ *lemma* char_p_of_injective_algebra_map'

Modified src/field_theory/finite/basic.lean


Modified src/field_theory/finite/galois_field.lean




## [2022-05-24 03:06:12](https://github.com/leanprover-community/mathlib/commit/179ae9e)
feat(category_theory/preadditive): hom orthogonal families ([#13871](https://github.com/leanprover-community/mathlib/pull/13871))
A family of objects in a category with zero morphisms is "hom orthogonal" if the only
morphism between distinct objects is the zero morphism.
We show that in any category with zero morphisms and finite biproducts,
a morphism between biproducts drawn from a hom orthogonal family `s : ι → C`
can be decomposed into a block diagonal matrix with entries in the endomorphism rings of the `s i`.
When the category is preadditive, this decomposition is an additive equivalence,
and intertwines composition and matrix multiplication.
When the category is `R`-linear, the decomposition is an `R`-linear equivalence.
If every object in the hom orthogonal family has an endomorphism ring with invariant basis number
(e.g. if each object in the family is simple, so its endomorphism ring is a division ring,
or otherwise if each endomorphism ring is commutative),
then decompositions of an object as a biproduct of the family have uniquely defined multiplicities.
We state this as:
```
lemma hom_orthogonal.equiv_of_iso (o : hom_orthogonal s) {f : α → ι} {g : β → ι}
  (i : ⨁ (λ a, s (f a)) ≅ ⨁ (λ b, s (g b))) : ∃ e : α ≃ β, ∀ a, g (e a) = f a
```
This is preliminary to defining semisimple categories.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_congr_set

Modified src/category_theory/linear/default.lean


Added src/category_theory/preadditive/hom_orthogonal.lean
- \+ *lemma* category_theory.hom_orthogonal.eq_zero
- \+ *lemma* category_theory.hom_orthogonal.equiv_of_iso
- \+ *def* category_theory.hom_orthogonal.matrix_decomposition
- \+ *def* category_theory.hom_orthogonal.matrix_decomposition_add_equiv
- \+ *lemma* category_theory.hom_orthogonal.matrix_decomposition_comp
- \+ *lemma* category_theory.hom_orthogonal.matrix_decomposition_id
- \+ *def* category_theory.hom_orthogonal.matrix_decomposition_linear_equiv
- \+ *def* category_theory.hom_orthogonal



## [2022-05-24 01:48:51](https://github.com/leanprover-community/mathlib/commit/c340170)
chore(set_theory/ordinal/*): improve autogenerated instance names for `o.out.α` ([#14342](https://github.com/leanprover-community/mathlib/pull/14342))
#### Estimated changes
Modified src/set_theory/game/nim.lean


Modified src/set_theory/ordinal/arithmetic.lean


Modified src/set_theory/ordinal/basic.lean




## [2022-05-24 00:02:28](https://github.com/leanprover-community/mathlib/commit/10f415a)
feat(set_theory/game/basic): mul_cases lemmas ([#14343](https://github.com/leanprover-community/mathlib/pull/14343))
These are the multiplicative analogs for `{left/right}_moves_add_cases`.
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \+ *lemma* pgame.left_moves_mul_cases
- \+ *lemma* pgame.right_moves_mul_cases



## [2022-05-23 23:25:06](https://github.com/leanprover-community/mathlib/commit/dc36333)
feat(set_theory/surreal/basic): ordinals are numeric ([#14325](https://github.com/leanprover-community/mathlib/pull/14325))
#### Estimated changes
Modified src/set_theory/game/ordinal.lean


Modified src/set_theory/surreal/basic.lean
- \+ *theorem* pgame.numeric_to_pgame



## [2022-05-23 22:05:46](https://github.com/leanprover-community/mathlib/commit/59ef070)
feat(ring_theory/unique_factorization_domain): misc lemmas on factors ([#14333](https://github.com/leanprover-community/mathlib/pull/14333))
Two little lemmas on the set of factors which I needed for [#12287](https://github.com/leanprover-community/mathlib/pull/12287).
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean
- \+ *lemma* unique_factorization_monoid.dvd_of_mem_factors
- \+ *lemma* unique_factorization_monoid.ne_zero_of_mem_factors



## [2022-05-23 20:34:27](https://github.com/leanprover-community/mathlib/commit/3f0a2bb)
feat(set_theory/cardinal/basic): Inline instances ([#14130](https://github.com/leanprover-community/mathlib/pull/14130))
We inline some instances, thus avoiding redundant lemmas. We also clean up the code somewhat.
#### Estimated changes
Modified src/set_theory/cardinal/basic.lean
- \+/\- *lemma* cardinal.pow_cast_right

Modified src/set_theory/cardinal/ordinal.lean
- \+ *lemma* cardinal.mul_eq_max_of_omega_le_right



## [2022-05-23 17:51:44](https://github.com/leanprover-community/mathlib/commit/b3ff79a)
feat(topology/uniform_space/uniform_convergence): Uniform Cauchy sequences ([#14003](https://github.com/leanprover-community/mathlib/pull/14003))
A sequence of functions `f_n` is pointwise Cauchy if `∀x ∀ε ∃N ∀(m, n) > N` we have `|f_m x - f_n x| < ε`. A sequence of functions is _uniformly_ Cauchy if `∀ε ∃N ∀(m, n) > N ∀x` we have `|f_m x - f_n x| < ε`.
As a sequence of functions is pointwise Cauchy if (and when the underlying space is complete, only if) the sequence converges, a sequence of functions is uniformly Cauchy if (and when the underlying space is complete, only if) the sequence uniformly converges. (Note that the parenthetical is not directly covered by this commit, but is an easy consequence of two of its lemmas.)
This notion is commonly used to bootstrap convergence into uniform convergence.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *theorem* metric.uniform_cauchy_seq_on_iff

Modified src/topology/uniform_space/uniform_convergence.lean
- \+ *lemma* tendsto_uniformly_on.uniform_cauchy_seq_on
- \+ *lemma* uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto
- \+ *def* uniform_cauchy_seq_on



## [2022-05-23 16:11:41](https://github.com/leanprover-community/mathlib/commit/dab06b6)
refactor(topology/sequences): rename some `sequential_` to `seq_` ([#14318](https://github.com/leanprover-community/mathlib/pull/14318))
## Rename
* `sequential_closure` → `seq_closure`, similarly rename lemmas;
* `sequentially_continuous` → `seq_continuous`, similarly rename lemmas;
* `is_seq_closed_of_is_closed` → `is_closed.is_seq_closed`;
* `mem_of_is_seq_closed` → `is_seq_closed.mem_of_tendsto`;
* `continuous.to_sequentially_continuous` → `continuous.seq_continuous`;
## Remove
* `mem_of_is_closed_sequential`: was a weaker version of `is_closed.mem_of_tendsto`;
## Add
* `is_seq_closed.is_closed`;
* `seq_continuous.continuous`;
#### Estimated changes
Modified src/topology/sequences.lean
- \- *lemma* continuous.to_sequentially_continuous
- \+ *lemma* continuous_iff_seq_continuous
- \- *lemma* continuous_iff_sequentially_continuous
- \+ *lemma* is_closed.is_seq_closed
- \+ *lemma* is_seq_closed.mem_of_tendsto
- \+/\- *def* is_seq_closed
- \- *lemma* is_seq_closed_of_is_closed
- \- *lemma* mem_of_is_closed_sequential
- \- *lemma* mem_of_is_seq_closed
- \+ *def* seq_closure
- \+ *lemma* seq_closure_subset_closure
- \+ *def* seq_continuous
- \- *def* sequential_closure
- \- *lemma* sequential_closure_subset_closure
- \- *def* sequentially_continuous
- \+ *lemma* subset_seq_closure
- \- *lemma* subset_sequential_closure



## [2022-05-23 16:11:40](https://github.com/leanprover-community/mathlib/commit/bbf5776)
feat(group_theory/sylow): The number of sylow subgroups is indivisible by p ([#14313](https://github.com/leanprover-community/mathlib/pull/14313))
A corollary of Sylow's third theorem is that the number of sylow subgroups is indivisible by p.
#### Estimated changes
Modified src/group_theory/sylow.lean
- \+ *lemma* not_dvd_card_sylow



## [2022-05-23 16:11:39](https://github.com/leanprover-community/mathlib/commit/7a6d850)
feat(probability/stopping): measurability of comparisons of stopping times ([#14061](https://github.com/leanprover-community/mathlib/pull/14061))
Among other related results, prove that `{x | τ x ≤ π x}` is measurable with respect to the sigma algebras generated by each of the two stopping times involved.
#### Estimated changes
Modified src/measure_theory/group/arithmetic.lean
- \+ *lemma* measurable_set_eq_fun_of_encodable

Modified src/probability/stopping.lean
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_eq_stopping_time
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_eq_stopping_time_of_encodable
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_inter_le_iff
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_le_stopping_time
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_min_const_iff
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_stopping_time_le
- \+ *lemma* measure_theory.is_stopping_time.measurable_space_le'
- \+/\- *lemma* measure_theory.is_stopping_time.measurable_space_le
- \+ *lemma* measure_theory.is_stopping_time.measurable_space_le_of_encodable
- \+ *lemma* measure_theory.is_stopping_time.measurable_space_min_const



## [2022-05-23 14:09:34](https://github.com/leanprover-community/mathlib/commit/8df8968)
feat(data/set/function): add `monotone_on.monotone` etc ([#14301](https://github.com/leanprover-community/mathlib/pull/14301))
#### Estimated changes
Modified src/data/set/function.lean




## [2022-05-23 14:09:33](https://github.com/leanprover-community/mathlib/commit/33262e0)
feat(ring_theory/power_series): Added lemmas regarding rescale ([#14283](https://github.com/leanprover-community/mathlib/pull/14283))
Added lemmas `rescale_mk`, `rescale_mul` and `rescale_rescale`.
#### Estimated changes
Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* power_series.rescale_mk
- \+ *lemma* power_series.rescale_mul
- \+ *lemma* power_series.rescale_rescale



## [2022-05-23 14:09:32](https://github.com/leanprover-community/mathlib/commit/15e8bc4)
feat(topology/vector_bundle): define pretrivialization.symm ([#14192](https://github.com/leanprover-community/mathlib/pull/14192))
* Also adds some other useful lemmas about (pre)trivializations
* This splits out the part of [#8545](https://github.com/leanprover-community/mathlib/pull/8545) that is unrelated to pullbacks
- Co-authored by Nicolo Cavalleri <nico@cavalleri.net>
#### Estimated changes
Modified src/data/bundle.lean
- \+ *lemma* bundle.coe_snd
- \+ *lemma* bundle.sigma_mk_eq_total_space_mk
- \+/\- *lemma* bundle.to_total_space_coe
- \+ *lemma* bundle.total_space.eta
- \+ *lemma* bundle.total_space.mk_cast
- \+ *lemma* bundle.total_space.proj_mk

Modified src/topology/fiber_bundle.lean


Modified src/topology/vector_bundle.lean
- \+ *lemma* topological_vector_bundle.continuous_total_space_mk
- \+ *lemma* topological_vector_bundle.pretrivialization.apply_mk_symm
- \+ *lemma* topological_vector_bundle.pretrivialization.apply_symm_apply'
- \+ *lemma* topological_vector_bundle.pretrivialization.apply_symm_apply
- \+ *lemma* topological_vector_bundle.pretrivialization.coe_coe
- \+ *lemma* topological_vector_bundle.pretrivialization.coe_coe_fst
- \+ *lemma* topological_vector_bundle.pretrivialization.coe_fst'
- \+ *lemma* topological_vector_bundle.pretrivialization.coe_fst
- \+ *lemma* topological_vector_bundle.pretrivialization.coe_mem_source
- \+ *lemma* topological_vector_bundle.pretrivialization.linear
- \+ *def* topological_vector_bundle.pretrivialization.linear_equiv_at
- \+ *lemma* topological_vector_bundle.pretrivialization.mem_source
- \+ *lemma* topological_vector_bundle.pretrivialization.mem_target
- \+ *lemma* topological_vector_bundle.pretrivialization.mk_mem_target
- \+ *lemma* topological_vector_bundle.pretrivialization.mk_proj_snd'
- \+ *lemma* topological_vector_bundle.pretrivialization.mk_proj_snd
- \+ *lemma* topological_vector_bundle.pretrivialization.mk_symm
- \+ *lemma* topological_vector_bundle.pretrivialization.preimage_symm_proj_base_set
- \+ *lemma* topological_vector_bundle.pretrivialization.proj_symm_apply'
- \+ *lemma* topological_vector_bundle.pretrivialization.proj_symm_apply
- \+ *lemma* topological_vector_bundle.pretrivialization.symm_apply
- \+ *lemma* topological_vector_bundle.pretrivialization.symm_apply_apply
- \+ *lemma* topological_vector_bundle.pretrivialization.symm_apply_apply_mk
- \+ *lemma* topological_vector_bundle.pretrivialization.symm_apply_mk_proj
- \+ *lemma* topological_vector_bundle.pretrivialization.symm_apply_of_not_mem
- \+ *lemma* topological_vector_bundle.pretrivialization.symm_coe_fst'
- \+ *lemma* topological_vector_bundle.pretrivialization.symm_proj_apply
- \+ *lemma* topological_vector_bundle.trivialization.apply_mk_symm
- \+ *lemma* topological_vector_bundle.trivialization.apply_symm_apply'
- \+ *lemma* topological_vector_bundle.trivialization.apply_symm_apply
- \+/\- *lemma* topological_vector_bundle.trivialization.coe_coe
- \+ *lemma* topological_vector_bundle.trivialization.coe_coe_fst
- \+ *lemma* topological_vector_bundle.trivialization.coe_fst'
- \+/\- *lemma* topological_vector_bundle.trivialization.coe_fst
- \+ *lemma* topological_vector_bundle.trivialization.coe_mem_source
- \+ *lemma* topological_vector_bundle.trivialization.continuous_on_symm
- \+ *lemma* topological_vector_bundle.trivialization.map_target
- \+/\- *lemma* topological_vector_bundle.trivialization.mem_source
- \+ *lemma* topological_vector_bundle.trivialization.mem_target
- \+ *lemma* topological_vector_bundle.trivialization.mk_mem_target
- \+ *lemma* topological_vector_bundle.trivialization.mk_proj_snd'
- \+ *lemma* topological_vector_bundle.trivialization.mk_proj_snd
- \+ *lemma* topological_vector_bundle.trivialization.mk_symm
- \+ *lemma* topological_vector_bundle.trivialization.proj_symm_apply'
- \+ *lemma* topological_vector_bundle.trivialization.proj_symm_apply
- \+ *lemma* topological_vector_bundle.trivialization.source_inter_preimage_target_inter
- \+ *lemma* topological_vector_bundle.trivialization.symm_apply
- \+ *lemma* topological_vector_bundle.trivialization.symm_apply_apply
- \+ *lemma* topological_vector_bundle.trivialization.symm_apply_apply_mk
- \+ *lemma* topological_vector_bundle.trivialization.symm_apply_of_not_mem
- \+ *lemma* topological_vector_bundle.trivialization.symm_coe_fst'
- \+ *lemma* topological_vector_bundle.trivialization.symm_proj_apply
- \+/\- *def* topological_vector_bundle.trivialization.to_pretrivialization



## [2022-05-23 12:13:01](https://github.com/leanprover-community/mathlib/commit/2b35fc7)
refactor(data/set/finite): reorganize and put emphasis on fintype instances ([#14136](https://github.com/leanprover-community/mathlib/pull/14136))
I went through `data/set/finite` and reorganized it by rough topic (and moved some lemmas to their proper homes; closes [#11177](https://github.com/leanprover-community/mathlib/pull/11177)). Two important parts of this module are (1) `fintype` instances for various set constructions and (2) ways to create `set.finite` terms. This change puts the module closer to following a design where the `set.finite` terms are created in a formulaic way from the `fintype` instances. One tool for this is a `set.finite_of_fintype` constructor, which lets typeclass inference do most of the work.
Included in this commit is changing `set.infinite` to be protected so that it does not conflict with `infinite`.
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified src/analysis/locally_convex/weak_dual.lean


Modified src/combinatorics/configuration.lean


Modified src/combinatorics/simple_graph/basic.lean


Modified src/combinatorics/simple_graph/strongly_regular.lean


Modified src/data/fintype/basic.lean
- \+ *lemma* fintype.card_compl_eq_card_compl
- \+ *lemma* fintype.card_subtype_compl
- \+ *def* set.decidable_mem_of_fintype
- \+ *lemma* set.to_finset_diff
- \+ *lemma* set.to_finset_insert
- \+ *lemma* set.to_finset_inter
- \+ *lemma* set.to_finset_ne_eq_erase
- \+/\- *lemma* set.to_finset_range
- \+ *lemma* set.to_finset_singleton
- \+ *lemma* set.to_finset_union
- \+/\- *lemma* set.to_finset_univ

Modified src/data/nat/nth.lean


Modified src/data/set/finite.lean
- \+/\- *lemma* finset.finite_to_set
- \- *lemma* fintype.card_compl_eq_card_compl
- \- *lemma* fintype.card_subtype_compl
- \- *theorem* set.card_fintype_insert'
- \+ *theorem* set.card_fintype_insert_of_not_mem
- \- *def* set.decidable_mem_of_fintype
- \+/\- *lemma* set.eq_finite_Union_of_finite_subset_Union
- \+ *theorem* set.finite.bUnion'
- \+/\- *theorem* set.finite.bUnion
- \+/\- *theorem* set.finite.bind
- \+/\- *lemma* set.finite.coe_sort_to_finset
- \+/\- *lemma* set.finite.coe_to_finset
- \+/\- *lemma* set.finite.dependent_image
- \+ *theorem* set.finite.diff
- \+/\- *theorem* set.finite.dinduction_on
- \+/\- *theorem* set.finite.exists_finset
- \+/\- *theorem* set.finite.exists_finset_coe
- \+/\- *lemma* set.finite.exists_lt_map_eq_of_range_subset
- \+/\- *lemma* set.finite.fin_param
- \+/\- *lemma* set.finite.image2
- \+/\- *theorem* set.finite.image
- \+/\- *theorem* set.finite.induction_on
- \+/\- *lemma* set.finite.infinite_compl
- \+/\- *theorem* set.finite.insert
- \+/\- *theorem* set.finite.inter_of_left
- \+/\- *theorem* set.finite.inter_of_right
- \+/\- *theorem* set.finite.map
- \+/\- *theorem* set.finite.mem_to_finset
- \+ *theorem* set.finite.nonempty_to_finset
- \+ *theorem* set.finite.of_diff
- \- *lemma* set.finite.of_diff
- \+ *theorem* set.finite.of_finite_image
- \+/\- *theorem* set.finite.of_fintype
- \+/\- *theorem* set.finite.of_preimage
- \+/\- *lemma* set.finite.prod
- \+ *theorem* set.finite.sInter
- \- *lemma* set.finite.sInter
- \+/\- *theorem* set.finite.sUnion
- \+ *theorem* set.finite.sep
- \+/\- *theorem* set.finite.seq'
- \+/\- *theorem* set.finite.seq
- \+/\- *theorem* set.finite.subset
- \- *theorem* set.finite.to_finset.nonempty
- \+/\- *lemma* set.finite.to_finset_inj
- \+ *lemma* set.finite.to_finset_insert
- \+/\- *lemma* set.finite.to_finset_mono
- \+/\- *lemma* set.finite.to_finset_strict_mono
- \+/\- *theorem* set.finite.union
- \+/\- *theorem* set.finite_Union
- \+/\- *lemma* set.finite_def
- \+/\- *theorem* set.finite_empty
- \+/\- *lemma* set.finite_empty_to_finset
- \+/\- *lemma* set.finite_le_nat
- \+/\- *lemma* set.finite_lt_nat
- \+/\- *theorem* set.finite_mem_finset
- \- *theorem* set.finite_of_finite_image
- \+ *theorem* set.finite_of_fintype
- \+/\- *lemma* set.finite_option
- \+/\- *theorem* set.finite_pure
- \+/\- *theorem* set.finite_range
- \+/\- *theorem* set.finite_singleton
- \+/\- *lemma* set.finite_to_finset_eq_empty_iff
- \+/\- *lemma* set.finite_union
- \+/\- *theorem* set.finite_univ
- \+/\- *def* set.fintype_bUnion
- \- *def* set.fintype_insert'
- \+ *def* set.fintype_insert_of_mem
- \+ *def* set.fintype_insert_of_not_mem
- \+/\- *lemma* set.infinite.diff
- \+/\- *lemma* set.infinite.exists_nat_lt
- \+/\- *lemma* set.infinite.exists_subset_card_eq
- \+/\- *theorem* set.infinite.to_subtype
- \- *def* set.infinite
- \+/\- *theorem* set.infinite_coe_iff
- \+/\- *lemma* set.infinite_of_finite_compl
- \+/\- *theorem* set.infinite_of_injective_forall_mem
- \+/\- *theorem* set.infinite_range_of_injective
- \+/\- *lemma* set.infinite_union
- \+/\- *theorem* set.infinite_univ
- \+/\- *theorem* set.infinite_univ_iff
- \- *lemma* set.insert_to_finset
- \+ *def* set.nat.fintype_Iio
- \+/\- *lemma* set.not_infinite
- \- *lemma* set.subset_iff_to_finset_subset
- \+/\- *lemma* set.subset_to_finset_iff
- \- *lemma* set.to_finset_insert
- \- *lemma* set.to_finset_inter
- \- *lemma* set.to_finset_ne_eq_erase
- \- *lemma* set.to_finset_sdiff
- \- *lemma* set.to_finset_singleton
- \- *lemma* set.to_finset_union

Modified src/data/set/intervals/infinite.lean
- \+/\- *lemma* set.Icc.infinite
- \+/\- *lemma* set.Ici.infinite
- \+/\- *lemma* set.Ico.infinite
- \+/\- *lemma* set.Iic.infinite
- \+/\- *lemma* set.Iio.infinite
- \+/\- *lemma* set.Ioc.infinite
- \+/\- *lemma* set.Ioi.infinite
- \+/\- *lemma* set.Ioo.infinite

Modified src/logic/equiv/fintype.lean


Modified src/order/well_founded_set.lean


Modified src/ring_theory/hahn_series.lean


Modified src/topology/metric_space/closeds.lean


Modified src/topology/metric_space/emetric_paracompact.lean


Modified src/topology/subset_properties.lean




## [2022-05-23 10:20:39](https://github.com/leanprover-community/mathlib/commit/34e450b)
chore(linear_algebra/quadratic_form/basic): Reorder lemmas ([#14326](https://github.com/leanprover-community/mathlib/pull/14326))
This moves the `fun_like` lemmas up to the top of the file next to the `coe_to_fun` instance, and condenses some sections containing only one lemma.
#### Estimated changes
Modified src/linear_algebra/quadratic_form/basic.lean




## [2022-05-23 10:20:38](https://github.com/leanprover-community/mathlib/commit/275dd0f)
feat(algebra/ne_zero): add helper methods ([#14286](https://github.com/leanprover-community/mathlib/pull/14286))
Also golfs the inspiration for one of these, and cleans up some code around the area.
#### Estimated changes
Modified src/algebra/ne_zero.lean
- \+ *lemma* eq_zero_or_ne_zero
- \+/\- *lemma* ne_zero.of_injective
- \+ *lemma* ne_zero.pos
- \+/\- *lemma* ne_zero.trans

Modified src/data/zmod/basic.lean




## [2022-05-23 10:20:35](https://github.com/leanprover-community/mathlib/commit/15f49ae)
feat(linear_algebra/tensor_algebra/basic): add `tensor_algebra.tprod` ([#14197](https://github.com/leanprover-community/mathlib/pull/14197))
This is related to `exterior_power.ι_multi`.
Note the new import caused a proof to time out, so I squeezed the simps into term mode.
#### Estimated changes
Modified src/linear_algebra/exterior_algebra/basic.lean
- \+/\- *def* exterior_algebra.ι_multi

Modified src/linear_algebra/tensor_algebra/basic.lean
- \+ *def* tensor_algebra.tprod
- \+ *lemma* tensor_algebra.tprod_apply



## [2022-05-23 09:19:36](https://github.com/leanprover-community/mathlib/commit/9288a2d)
feat(linear_algebra/affine_space/affine_equiv): extra lemmas and docstrings ([#14319](https://github.com/leanprover-community/mathlib/pull/14319))
I was struggling to find this definition, so added some more lemmas and a docstring.
#### Estimated changes
Modified src/linear_algebra/affine_space/affine_equiv.lean
- \+ *lemma* affine_equiv.const_vadd_add
- \+ *def* affine_equiv.const_vadd_hom
- \+ *lemma* affine_equiv.const_vadd_nsmul
- \+ *lemma* affine_equiv.const_vadd_symm
- \+ *lemma* affine_equiv.const_vadd_zero
- \+ *lemma* affine_equiv.const_vadd_zsmul



## [2022-05-23 08:30:52](https://github.com/leanprover-community/mathlib/commit/aa6dc57)
chore(measure_theory/function/l1_space): drop `integrable.sub'` ([#14309](https://github.com/leanprover-community/mathlib/pull/14309))
It used to have weaker TC assumptions than `integrable.sub` but now it's just a weaker version of it.
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean
- \- *lemma* measure_theory.integrable.sub'



## [2022-05-23 07:50:19](https://github.com/leanprover-community/mathlib/commit/2962eab)
feat(linear_algebra/trace): trace of transpose map ([#13897](https://github.com/leanprover-community/mathlib/pull/13897))
#### Estimated changes
Modified src/linear_algebra/contraction.lean
- \+ *lemma* transpose_dual_tensor_hom

Modified src/linear_algebra/trace.lean
- \+ *theorem* linear_map.trace_transpose'
- \+ *theorem* linear_map.trace_transpose



## [2022-05-23 06:53:49](https://github.com/leanprover-community/mathlib/commit/b5128b8)
feat(category_theory/limits): pullback squares ([#14220](https://github.com/leanprover-community/mathlib/pull/14220))
Per [zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/pushout.20of.20biprod.2Efst.20and.20biprod.2Esnd.20is.20zero).
#### Estimated changes
Added src/category_theory/limits/shapes/comm_sq.lean
- \+ *lemma* category_theory.limits.comm_sq.flip
- \+ *lemma* category_theory.limits.comm_sq.of_arrow
- \+ *structure* category_theory.limits.comm_sq
- \+ *def* category_theory.limits.is_pullback.cone
- \+ *lemma* category_theory.limits.is_pullback.flip
- \+ *lemma* category_theory.limits.is_pullback.of_bot
- \+ *lemma* category_theory.limits.is_pullback.of_has_pullback
- \+ *lemma* category_theory.limits.is_pullback.of_is_limit
- \+ *lemma* category_theory.limits.is_pullback.of_right
- \+ *lemma* category_theory.limits.is_pullback.paste_horiz
- \+ *lemma* category_theory.limits.is_pullback.paste_vert
- \+ *lemma* category_theory.limits.is_pullback.zero_left
- \+ *lemma* category_theory.limits.is_pullback.zero_top
- \+ *structure* category_theory.limits.is_pullback
- \+ *def* category_theory.limits.is_pushout.cocone
- \+ *lemma* category_theory.limits.is_pushout.flip
- \+ *lemma* category_theory.limits.is_pushout.of_bot
- \+ *lemma* category_theory.limits.is_pushout.of_has_pushout
- \+ *lemma* category_theory.limits.is_pushout.of_is_colimit
- \+ *lemma* category_theory.limits.is_pushout.of_right
- \+ *lemma* category_theory.limits.is_pushout.paste_horiz
- \+ *lemma* category_theory.limits.is_pushout.paste_vert
- \+ *lemma* category_theory.limits.is_pushout.zero_bot
- \+ *lemma* category_theory.limits.is_pushout.zero_right
- \+ *structure* category_theory.limits.is_pushout

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *lemma* category_theory.limits.pullback_cone.condition_one
- \+ *def* category_theory.limits.pullback_cone.ext
- \+ *lemma* category_theory.limits.pushout_cocone.condition_zero
- \+ *def* category_theory.limits.pushout_cocone.ext



## [2022-05-23 04:06:58](https://github.com/leanprover-community/mathlib/commit/94644b7)
chore(scripts): update nolints.txt ([#14321](https://github.com/leanprover-community/mathlib/pull/14321))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-05-23 01:49:47](https://github.com/leanprover-community/mathlib/commit/542d06a)
feat(measure_theory): use `pseudo_metrizable_space` instead of `metrizable_space` ([#14310](https://github.com/leanprover-community/mathlib/pull/14310))
#### Estimated changes
Modified src/measure_theory/function/ae_eq_fun.lean
- \+/\- *lemma* measure_theory.ae_eq_fun.comp_measurable_to_germ

Modified src/measure_theory/function/simple_func_dense.lean


Modified src/measure_theory/function/strongly_measurable.lean
- \+/\- *lemma* ae_measurable.ae_strongly_measurable
- \+/\- *lemma* ae_strongly_measurable_Union_iff
- \+/\- *lemma* ae_strongly_measurable_add_measure_iff
- \+/\- *lemma* ae_strongly_measurable_id
- \+/\- *lemma* ae_strongly_measurable_iff_ae_measurable
- \+/\- *lemma* ae_strongly_measurable_union_iff
- \+/\- *lemma* exists_strongly_measurable_limit_of_tendsto_ae
- \+/\- *lemma* measurable.strongly_measurable
- \+/\- *lemma* measure_theory.ae_strongly_measurable.add_measure
- \+/\- *lemma* measure_theory.ae_strongly_measurable.measurable_mk
- \+/\- *lemma* measure_theory.ae_strongly_measurable.sum_measure
- \+/\- *lemma* strongly_measurable_id

Modified src/measure_theory/group/fundamental_domain.lean


Modified src/measure_theory/integral/bochner.lean


Modified src/measure_theory/integral/integrable_on.lean


Modified src/measure_theory/integral/integral_eq_improper.lean
- \+/\- *lemma* measure_theory.ae_cover.ae_strongly_measurable



## [2022-05-23 01:49:46](https://github.com/leanprover-community/mathlib/commit/c100004)
refactor(category_theory/shift_functor): improve defeq of inverse ([#14300](https://github.com/leanprover-community/mathlib/pull/14300))
#### Estimated changes
Modified src/category_theory/shift.lean
- \+ *lemma* category_theory.shift_functor_inv



## [2022-05-23 01:49:45](https://github.com/leanprover-community/mathlib/commit/56de25e)
chore(topology/separation): golf some proofs ([#14279](https://github.com/leanprover-community/mathlib/pull/14279))
* extract `minimal_nonempty_closed_eq_singleton` out of the proof of
  `is_closed.exists_closed_singleton`;
* replace `exists_open_singleton_of_open_finset` with
  `exists_open_singleton_of_open_finite`, extract
  `minimal_nonempty_open_eq_singleton` out of its proof.
* add `exists_is_open_xor_mem`, an alias for `t0_space.t0`.
#### Estimated changes
Modified src/topology/separation.lean
- \+ *lemma* exists_is_open_xor_mem
- \+/\- *theorem* exists_open_singleton_of_fintype
- \+ *theorem* exists_open_singleton_of_open_finite
- \- *theorem* exists_open_singleton_of_open_finset
- \+ *theorem* minimal_nonempty_closed_eq_singleton
- \+ *theorem* minimal_nonempty_open_eq_singleton



## [2022-05-23 01:49:44](https://github.com/leanprover-community/mathlib/commit/01eda9a)
feat(topology/instances/ennreal): golf, add lemmas about `supr_add_supr` ([#14274](https://github.com/leanprover-community/mathlib/pull/14274))
* add `ennreal.bsupr_add'` etc that deal with
  `{ι : Sort*} {p : ι → Prop}` instead of `{ι : Type*} {s : set ι}`;
* golf some proofs by reusing more powerful generic lemmas;
* add `ennreal.supr_add_supr_le`, `ennreal.bsupr_add_bsupr_le`,
  and `ennreal.bsupr_add_bsupr_le'`.
#### Estimated changes
Modified src/topology/instances/ennreal.lean
- \+ *lemma* ennreal.add_bsupr'
- \+ *lemma* ennreal.add_bsupr
- \+/\- *lemma* ennreal.add_supr
- \+ *lemma* ennreal.bsupr_add'
- \+ *lemma* ennreal.bsupr_add_bsupr_le'
- \+ *lemma* ennreal.bsupr_add_bsupr_le
- \+ *lemma* ennreal.supr_add_supr_le



## [2022-05-23 01:49:43](https://github.com/leanprover-community/mathlib/commit/9861db0)
feat(logic/hydra): termination of a hydra game ([#14190](https://github.com/leanprover-community/mathlib/pull/14190))
+ The added file logic/hydra.lean deals with the following version of the hydra game: each head of the hydra is labelled by an element in a type `α`, and when you cut off one head with label `a`, it grows back an arbitrary but finite number of heads, all labelled by elements smaller than `a` with respect to a well-founded relation `r` on `α`. We show that no matter how (in what order) you choose cut off the heads, the game always terminates, i.e. all heads will eventually be cut off. The proof follows https://mathoverflow.net/a/229084/3332, and the notion of `fibration` and the `game_add` relation on the product of two types arise in the proof.
+ The results is used to show the well-foundedness of the intricate induction used to show that multiplication of games is well-defined on surreals, see [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Well-founded.20recursion.20for.20pgames/near/282379832).
+ One lemma `add_singleton_eq_iff` is added to data/multiset/basic.
+ `acc.trans_gen` is added, closing [a comment](https://github.com/leanprover-community/lean/pull/713/files#r867394835) at lean[#713](https://github.com/leanprover-community/mathlib/pull/713).
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *lemma* multiset.add_singleton_eq_iff

Added src/logic/hydra.lean
- \+ *lemma* acc.cut_expand
- \+ *lemma* acc.game_add
- \+ *lemma* acc.of_downward_closed
- \+ *lemma* acc.of_fibration
- \+ *lemma* relation.acc_of_singleton
- \+ *def* relation.cut_expand
- \+ *lemma* relation.cut_expand_fibration
- \+ *lemma* relation.cut_expand_iff
- \+ *def* relation.fibration
- \+ *inductive* relation.game_add
- \+ *lemma* relation.game_add_le_lex
- \+ *lemma* relation.rprod_le_trans_gen_game_add
- \+ *theorem* well_founded.cut_expand
- \+ *lemma* well_founded.game_add

Modified src/logic/relation.lean
- \+ *lemma* acc.trans_gen



## [2022-05-23 01:49:42](https://github.com/leanprover-community/mathlib/commit/8304b95)
refactor(algebra/big_operators/*): Generalize to division monoids ([#14189](https://github.com/leanprover-community/mathlib/pull/14189))
Generalize big operators lemmas to `division_comm_monoid`. Rename `comm_group.inv_monoid_hom` to `inv_monoid_hom` because it is not about`comm_group` anymore and we do not use classes as namespaces.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_div_distrib
- \+/\- *lemma* finset.prod_erase_eq_div
- \- *lemma* finset.prod_inv_distrib'
- \+/\- *lemma* finset.prod_inv_distrib
- \+/\- *lemma* finset.prod_sdiff_div_prod_sdiff
- \+/\- *lemma* finset.prod_sdiff_eq_div
- \+/\- *lemma* finset.prod_zpow
- \+/\- *lemma* finset.sum_range_sub_of_monotone
- \- *lemma* finset.sum_sub_distrib

Modified src/algebra/big_operators/finprod.lean
- \+/\- *lemma* finprod_div_distrib
- \- *lemma* finprod_div_distrib₀
- \+/\- *lemma* finprod_inv_distrib
- \- *lemma* finprod_inv_distrib₀
- \+/\- *lemma* finprod_mem_div_distrib
- \- *lemma* finprod_mem_div_distrib₀
- \+/\- *lemma* finprod_mem_inv_distrib
- \- *lemma* finprod_mem_inv_distrib₀

Modified src/algebra/big_operators/multiset.lean
- \- *lemma* multiset.coe_inv_monoid_hom
- \- *lemma* multiset.prod_map_div₀
- \+/\- *lemma* multiset.prod_map_inv'
- \+/\- *lemma* multiset.prod_map_inv
- \- *lemma* multiset.prod_map_inv₀
- \- *lemma* multiset.prod_map_zpow₀

Modified src/algebra/hom/equiv.lean
- \+/\- *def* mul_equiv.inv
- \+ *lemma* mul_equiv.inv_symm
- \- *def* mul_equiv.inv₀
- \- *lemma* mul_equiv.inv₀_symm

Modified src/algebra/hom/freiman.lean


Modified src/algebra/hom/group.lean
- \+ *lemma* coe_inv_monoid_hom
- \- *def* comm_group.inv_monoid_hom
- \+ *def* inv_monoid_hom
- \+ *lemma* inv_monoid_hom_apply

Modified src/algebra/support.lean
- \+/\- *lemma* function.mul_support_div
- \- *lemma* function.mul_support_group_div
- \+/\- *lemma* function.mul_support_inv'
- \+/\- *lemma* function.mul_support_inv
- \- *lemma* function.mul_support_inv₀
- \+/\- *lemma* function.mul_support_mul_inv

Modified src/analysis/specific_limits/basic.lean


Modified src/data/dfinsupp/basic.lean


Modified src/data/real/pi/wallis.lean


Modified src/field_theory/splitting_field.lean


Modified src/topology/algebra/continuous_monoid_hom.lean




## [2022-05-23 01:49:41](https://github.com/leanprover-community/mathlib/commit/16a5286)
feat(order/atoms): add lemmas ([#14162](https://github.com/leanprover-community/mathlib/pull/14162))
#### Estimated changes
Modified src/algebra/associated.lean


Modified src/order/atoms.lean
- \- *lemma* eq_bot_or_eq_of_le_atom
- \- *lemma* eq_top_or_eq_of_coatom_le
- \+ *lemma* is_atom.Iic_eq
- \+ *lemma* is_atom.le_iff
- \+ *lemma* is_atom.lt_iff
- \+/\- *def* is_atom
- \+/\- *lemma* is_atom_dual_iff_is_coatom
- \+ *lemma* is_coatom.Ici_eq
- \+ *lemma* is_coatom.le_iff
- \+ *lemma* is_coatom.lt_iff
- \+/\- *def* is_coatom
- \+/\- *lemma* is_coatom_dual_iff_is_atom

Modified src/order/compactly_generated.lean


Modified src/order/partition/finpartition.lean




## [2022-05-22 23:41:38](https://github.com/leanprover-community/mathlib/commit/4cdde79)
chore(set_theory/game/ordinal): minor golfing ([#14317](https://github.com/leanprover-community/mathlib/pull/14317))
We open the `pgame` namespace to save a few characters. We also very slightly golf the proof of `to_pgame_le`.
#### Estimated changes
Modified src/set_theory/game/ordinal.lean




## [2022-05-22 23:41:37](https://github.com/leanprover-community/mathlib/commit/005df45)
feat(topology/metric_space): use weaker TC assumptions ([#14316](https://github.com/leanprover-community/mathlib/pull/14316))
Assume `t0_space` instead of `separated_space` in `metric.of_t0_pseudo_metric_space` and `emetric.of_t0_pseudo_emetric_space` (both definition used to have `t2` in their names).
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+/\- *lemma* norm_eq_zero_iff'
- \+/\- *lemma* norm_le_zero_iff'
- \+/\- *lemma* norm_pos_iff'

Modified src/topology/metric_space/basic.lean
- \+ *lemma* metric.indistinguishable_iff
- \+ *def* metric.of_t0_pseudo_metric_space
- \- *def* metric.of_t2_pseudo_metric_space

Modified src/topology/metric_space/emetric_space.lean
- \+ *theorem* emetric.indistinguishable_iff
- \+ *def* emetric.of_t0_pseudo_emetric_space
- \- *def* emetric_of_t2_pseudo_emetric_space



## [2022-05-22 23:41:36](https://github.com/leanprover-community/mathlib/commit/9e9a2c9)
feat(algebra/ring/basic): add `no_zero_divisors.to_cancel_comm_monoid_with_zero` ([#14302](https://github.com/leanprover-community/mathlib/pull/14302))
This already existed as `is_domain.to_cancel_comm_monoid_with_zero` with overly strong assumptions.
#### Estimated changes
Modified src/algebra/ring/basic.lean
- \+ *def* no_zero_divisors.to_cancel_comm_monoid_with_zero



## [2022-05-22 23:41:35](https://github.com/leanprover-community/mathlib/commit/dcb3cb1)
chore(logic/equiv/set): golf definition ([#14284](https://github.com/leanprover-community/mathlib/pull/14284))
I've no idea which name is better; for now, let's at least not implement the same function twice.
#### Estimated changes
Modified src/logic/equiv/set.lean




## [2022-05-22 23:41:34](https://github.com/leanprover-community/mathlib/commit/60897e3)
refactor(set_theory/game/nim): `0 ≈ nim 0` → `nim 0 ≈ 0` ([#14270](https://github.com/leanprover-community/mathlib/pull/14270))
We invert the directions of a few simple equivalences/relabellings to a more natural order (simpler on the RHS).
#### Estimated changes
Modified src/set_theory/game/nim.lean
- \+/\- *lemma* pgame.grundy_value_star
- \+/\- *lemma* pgame.grundy_value_zero
- \+/\- *theorem* pgame.nim.nim_one_equiv
- \+/\- *theorem* pgame.nim.nim_zero_equiv
- \+/\- *def* pgame.nim.nim_zero_relabelling



## [2022-05-22 23:41:33](https://github.com/leanprover-community/mathlib/commit/5a24374)
doc(set_theory/game/basic): improve docs ([#14268](https://github.com/leanprover-community/mathlib/pull/14268))
#### Estimated changes
Modified src/set_theory/game/basic.lean




## [2022-05-22 23:41:32](https://github.com/leanprover-community/mathlib/commit/cef5898)
chore(linear_algebra): generalize conversion between matrices and bilinear forms to semirings ([#14263](https://github.com/leanprover-community/mathlib/pull/14263))
Only one lemma was moved (`dual_distrib_apply`), none were renamed, and no proofs were meaningfully changed.
Section markers were shuffled around, and some variables exchanged for variables with weaker typeclass assumptions.
A few other things have been generalized to semiring at the same time; `linear_map.trace` and `linear_map.smul_rightₗ`
#### Estimated changes
Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/bilinear_form.lean
- \+/\- *lemma* bilin_form.ext_basis
- \+/\- *lemma* bilin_form.is_pair_self_adjoint_equiv
- \+/\- *lemma* bilin_form.sum_repr_mul_repr_mul

Modified src/linear_algebra/contraction.lean


Modified src/linear_algebra/dual.lean
- \+/\- *def* submodule.dual_annihilator

Modified src/linear_algebra/matrix/basis.lean
- \+/\- *lemma* basis.to_matrix_is_unit_smul
- \+/\- *lemma* basis.to_matrix_units_smul

Modified src/linear_algebra/matrix/bilinear_form.lean
- \+/\- *lemma* bilin_form.mul_to_matrix'
- \+/\- *lemma* bilin_form.mul_to_matrix'_mul
- \+/\- *lemma* bilin_form.mul_to_matrix
- \+/\- *lemma* bilin_form.mul_to_matrix_mul
- \+/\- *def* bilin_form.to_matrix'
- \+/\- *lemma* bilin_form.to_matrix'_apply
- \+/\- *lemma* bilin_form.to_matrix'_comp
- \+/\- *lemma* bilin_form.to_matrix'_comp_left
- \+/\- *lemma* bilin_form.to_matrix'_comp_right
- \+/\- *lemma* bilin_form.to_matrix'_mul
- \+/\- *lemma* bilin_form.to_matrix'_to_bilin'
- \+/\- *lemma* bilin_form.to_matrix_apply
- \+/\- *lemma* bilin_form.to_matrix_aux_std_basis
- \+/\- *lemma* bilin_form.to_matrix_comp_left
- \+/\- *lemma* bilin_form.to_matrix_comp_right
- \+/\- *lemma* bilin_form.to_matrix_mul
- \+/\- *lemma* bilin_form.to_matrix_mul_basis_to_matrix
- \+/\- *lemma* bilin_form.to_matrix_to_bilin
- \+/\- *lemma* bilinear_form.to_matrix_aux_eq
- \+/\- *lemma* matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin
- \+/\- *def* matrix.to_bilin'
- \+/\- *lemma* matrix.to_bilin'_apply'
- \+/\- *lemma* matrix.to_bilin'_apply
- \+/\- *lemma* matrix.to_bilin'_aux_eq
- \+/\- *lemma* matrix.to_bilin'_comp
- \+/\- *lemma* matrix.to_bilin'_std_basis
- \+/\- *lemma* matrix.to_bilin'_to_matrix'
- \+/\- *lemma* matrix.to_bilin_apply
- \+/\- *lemma* matrix.to_bilin_comp
- \+/\- *lemma* matrix.to_bilin_to_matrix
- \+/\- *lemma* to_bilin'_aux_to_matrix_aux

Modified src/linear_algebra/matrix/to_lin.lean


Modified src/linear_algebra/trace.lean


Modified src/topology/algebra/module/basic.lean




## [2022-05-22 23:41:31](https://github.com/leanprover-community/mathlib/commit/e09e877)
refactor(set_theory/cardinal/cofinality): infer arguments ([#14251](https://github.com/leanprover-community/mathlib/pull/14251))
We make one of the arguments in `cof_type_le` and `lt_cof_type` implicit.
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean
- \+/\- *theorem* ordinal.cof_type_le
- \+/\- *theorem* ordinal.lt_cof_type



## [2022-05-22 23:41:30](https://github.com/leanprover-community/mathlib/commit/d946573)
chore(data/matrix/basic): add `matrix.star_mul_vec` and `matrix.star_vec_mul` ([#14248](https://github.com/leanprover-community/mathlib/pull/14248))
This also generalizes some nearby typeclasses.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.mul_vec_conj_transpose
- \+/\- *lemma* matrix.mul_vec_mul_vec
- \+ *lemma* matrix.star_mul_vec
- \+ *lemma* matrix.star_vec_mul
- \+ *lemma* matrix.vec_mul_conj_transpose
- \+/\- *lemma* matrix.vec_mul_vec_mul



## [2022-05-22 23:41:29](https://github.com/leanprover-community/mathlib/commit/684587b)
feat(set_theory/game/pgame): `add_lf_add_of_lf_of_le` ([#14150](https://github.com/leanprover-community/mathlib/pull/14150))
This generalizes the previously existing `add_lf_add` on `numeric` games.
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.add_lf_add_of_le_of_lf
- \+ *theorem* pgame.add_lf_add_of_lf_of_le

Modified src/set_theory/surreal/basic.lean
- \- *theorem* pgame.add_lf_add



## [2022-05-22 22:57:28](https://github.com/leanprover-community/mathlib/commit/b7952ee)
refactor(category_theory/shift): remove opaque_eq_to_iso ([#14262](https://github.com/leanprover-community/mathlib/pull/14262))
It seems `opaque_eq_to_iso` was only needed because we had over-eager simp lemmas. After [#14260](https://github.com/leanprover-community/mathlib/pull/14260), it is easy to remove.
#### Estimated changes
Modified src/category_theory/differential_object.lean


Modified src/category_theory/shift.lean
- \- *lemma* category_theory.map_opaque_eq_to_iso_comp_app
- \- *def* category_theory.opaque_eq_to_iso
- \- *lemma* category_theory.opaque_eq_to_iso_inv
- \- *lemma* category_theory.opaque_eq_to_iso_symm

Modified src/category_theory/triangulated/rotate.lean




## [2022-05-22 21:01:20](https://github.com/leanprover-community/mathlib/commit/178456f)
feat(set_theory/surreal/basic): definition of `≤` and `<` on numeric games ([#14169](https://github.com/leanprover-community/mathlib/pull/14169))
#### Estimated changes
Modified src/set_theory/surreal/basic.lean
- \+ *theorem* pgame.le_iff_forall_lt
- \+ *theorem* pgame.le_of_forall_lt
- \+ *theorem* pgame.lt_def
- \+ *theorem* pgame.lt_iff_forall_le
- \+ *theorem* pgame.lt_of_forall_le



## [2022-05-22 18:33:19](https://github.com/leanprover-community/mathlib/commit/fe2b5ab)
feat(set_theory/game/pgame): instances for empty moves of addition ([#14297](https://github.com/leanprover-community/mathlib/pull/14297))
#### Estimated changes
Modified src/set_theory/game/pgame.lean




## [2022-05-22 17:01:21](https://github.com/leanprover-community/mathlib/commit/1b7e918)
chore(algebra/geom_sum): rename to odd.geom_sum_pos ([#14264](https://github.com/leanprover-community/mathlib/pull/14264))
allowing dot notation :)
#### Estimated changes
Modified src/algebra/geom_sum.lean
- \- *lemma* geom_sum_pos_of_odd
- \+ *lemma* odd.geom_sum_pos



## [2022-05-22 16:14:11](https://github.com/leanprover-community/mathlib/commit/eb8994b)
feat(measure_theory): use more `[(pseudo_)metrizable_space]` ([#14232](https://github.com/leanprover-community/mathlib/pull/14232))
* Use `[metrizable_space α]` or `[pseudo_metrizable_space α]` assumptions in some lemmas, replace `tendsto_metric` with `tendsto_metrizable` in the names of these lemmas.
* Drop `measurable_of_tendsto_metric'` and `measurable_of_tendsto_metric` in favor of `measurable_of_tendsto_metrizable'` and `measurable_of_tendsto_metrizable`.
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \- *lemma* ae_measurable_of_tendsto_metric_ae'
- \- *lemma* ae_measurable_of_tendsto_metric_ae
- \+ *lemma* ae_measurable_of_tendsto_metrizable_ae'
- \+ *lemma* ae_measurable_of_tendsto_metrizable_ae
- \+/\- *lemma* ae_measurable_of_unif_approx
- \- *lemma* measurable_limit_of_tendsto_metric_ae
- \+ *lemma* measurable_limit_of_tendsto_metrizable_ae
- \- *lemma* measurable_of_tendsto_metric'
- \- *lemma* measurable_of_tendsto_metric
- \- *lemma* measurable_of_tendsto_metric_ae
- \+/\- *lemma* measurable_of_tendsto_metrizable'
- \+/\- *lemma* measurable_of_tendsto_metrizable
- \+ *lemma* measurable_of_tendsto_metrizable_ae
- \+/\- *lemma* tendsto_measure_cthickening_of_is_compact

Modified src/measure_theory/function/convergence_in_measure.lean


Modified src/measure_theory/function/strongly_measurable.lean




## [2022-05-22 14:41:20](https://github.com/leanprover-community/mathlib/commit/eae0510)
feat(category_theory/natural_isomorphism): a simp lemma cancelling inverses ([#14299](https://github.com/leanprover-community/mathlib/pull/14299))
I am not super happy to be adding lemmas like this, because it feels like better designed simp normal forms (or something else) could just avoid the need.
However my efforts to think about this keep getting stuck on the shift functor hole we're in, and this lemma is useful in the meantime to dig my way out of it. :-)
#### Estimated changes
Modified src/category_theory/natural_isomorphism.lean
- \+ *lemma* category_theory.nat_iso.inv_map_inv_app



## [2022-05-22 14:41:19](https://github.com/leanprover-community/mathlib/commit/e4a8db1)
feat(data/real/ennreal): lemmas about unions and intersections ([#14296](https://github.com/leanprover-community/mathlib/pull/14296))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.Inter_Ici_coe_nat
- \+ *lemma* ennreal.Inter_Ioi_coe_nat
- \+ *lemma* ennreal.Union_Icc_coe_nat
- \+ *lemma* ennreal.Union_Ico_coe_nat
- \+ *lemma* ennreal.Union_Iic_coe_nat
- \+ *lemma* ennreal.Union_Iio_coe_nat
- \+ *lemma* ennreal.Union_Ioc_coe_nat
- \+ *lemma* ennreal.Union_Ioo_coe_nat



## [2022-05-22 14:41:17](https://github.com/leanprover-community/mathlib/commit/a836c6d)
refactor(category_theory): remove some simp lemmas about eq_to_hom ([#14260](https://github.com/leanprover-community/mathlib/pull/14260))
The simp lemma `eq_to_hom_map : F.map (eq_to_hom p) = eq_to_hom (congr_arg F.obj p)` is rather dangerous, but after it has fired it's much harder to see the functor `F` (e.g. to use naturality of a natural transformation).
This PR removes `@[simp]` from that lemma, at the expense of having a few `local attribute [simp]`s, and adding it explicitly to simp sets.
On the upside, we also get to *remove* some `simp [-eq_to_hom_map]`s. I'm hoping also to soon be able to remove `opaque_eq_to_hom`, as it was introduced to avoid the problem this simp lemma was causing.
The PR is part of an effort to solve some problems identified on [zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/trouble.20in.20.60shift_functor.60.20land).
#### Estimated changes
Modified src/algebra/homology/additive.lean


Modified src/algebraic_geometry/AffineScheme.lean


Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/open_immersion.lean


Modified src/algebraic_geometry/presheafed_space.lean


Modified src/algebraic_geometry/presheafed_space/gluing.lean


Modified src/algebraic_geometry/presheafed_space/has_colimits.lean


Modified src/category_theory/category/Cat.lean


Modified src/category_theory/category/Cat/limit.lean


Modified src/category_theory/differential_object.lean


Modified src/category_theory/eq_to_hom.lean
- \+/\- *lemma* category_theory.eq_to_hom_map
- \+/\- *lemma* category_theory.eq_to_iso_map

Modified src/category_theory/functor/flat.lean


Modified src/category_theory/grothendieck.lean


Modified src/category_theory/limits/shapes/products.lean


Modified src/category_theory/monoidal/CommMon_.lean


Modified src/category_theory/monoidal/Mon_.lean


Modified src/category_theory/preadditive/Mat.lean


Modified src/category_theory/shift.lean


Modified src/category_theory/structured_arrow.lean


Modified src/category_theory/triangulated/rotate.lean


Modified src/category_theory/yoneda.lean


Modified src/topology/sheaves/presheaf.lean


Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean


Modified src/topology/sheaves/sheaf_condition/sites.lean




## [2022-05-22 12:23:13](https://github.com/leanprover-community/mathlib/commit/0386c3b)
refactor(order/filter/lift): reformulate `lift_infi` etc ([#14138](https://github.com/leanprover-community/mathlib/pull/14138))
* add `monotone.of_map_inf` and `monotone.of_map_sup`;
* add `filter.lift_infi_le`: this inequality doesn't need any assumptions;
* reformulate `filter.lift_infi` and `filter.lift'_infi` using `g (s ∩ t) = g s ⊓ g t` instead of `g s ⊓ g t = g (s ∩ t)`;
* rename `filter.lift_infi'` to `filter.lift_infi_of_directed`, use `g (s ∩ t) = g s ⊓ g t`;
* add `filter.lift_infi_of_map_univ` and `filter.lift'_infi_of_map_univ`.
#### Estimated changes
Modified src/order/filter/lift.lean
- \+/\- *lemma* filter.lift'_inf
- \+/\- *lemma* filter.lift'_infi
- \+ *lemma* filter.lift'_infi_of_map_univ
- \- *lemma* filter.lift_infi'
- \+/\- *lemma* filter.lift_infi
- \+ *lemma* filter.lift_infi_le
- \+ *lemma* filter.lift_infi_of_directed
- \+ *lemma* filter.lift_infi_of_map_univ

Modified src/order/filter/small_sets.lean


Modified src/order/lattice.lean
- \+ *lemma* monotone.of_map_inf
- \+ *lemma* monotone.of_map_sup

Modified src/topology/uniform_space/basic.lean




## [2022-05-22 11:09:06](https://github.com/leanprover-community/mathlib/commit/d036d3c)
feat(probability/stopping): prove measurability of the stopped value ([#14062](https://github.com/leanprover-community/mathlib/pull/14062))
#### Estimated changes
Modified src/probability/stopping.lean
- \+ *lemma* measure_theory.measurable_stopped_value
- \+/\- *lemma* measure_theory.prog_measurable.adapted_stopped_process
- \+/\- *lemma* measure_theory.prog_measurable.stopped_process
- \+/\- *lemma* measure_theory.prog_measurable.strongly_measurable_stopped_process
- \+/\- *lemma* measure_theory.prog_measurable_min_stopping_time
- \+ *lemma* measure_theory.strongly_measurable_stopped_value_of_le



## [2022-05-22 11:09:05](https://github.com/leanprover-community/mathlib/commit/49b68e8)
feat(analysis/convex/uniform): Uniformly convex spaces ([#13480](https://github.com/leanprover-community/mathlib/pull/13480))
Define uniformly convex spaces and prove the implications `inner_product_space ℝ E → uniform_convex_space E` and `uniform_convex_space E → strict_convex_space ℝ E`.
#### Estimated changes
Added src/analysis/convex/uniform.lean
- \+ *lemma* exists_forall_closed_ball_dist_add_le_two_mul_sub
- \+ *lemma* exists_forall_closed_ball_dist_add_le_two_sub
- \+ *lemma* exists_forall_sphere_dist_add_le_two_sub

Modified src/analysis/inner_product_space/basic.lean


Modified src/analysis/normed/group/basic.lean
- \+ *lemma* norm_add₃_le
- \+ *lemma* norm_sub_pos_iff



## [2022-05-22 09:27:57](https://github.com/leanprover-community/mathlib/commit/ac00603)
feat(measure_theory/measure/measure_space): add some `null_measurable_set` lemmas ([#14293](https://github.com/leanprover-community/mathlib/pull/14293))
Add `measure_bUnion₀`, `measure_sUnion₀`, and `measure_bUnion_finset₀`.
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.lintegral_Union₀
- \+ *lemma* measure_theory.lintegral_bUnion
- \+ *lemma* measure_theory.lintegral_bUnion_finset
- \+ *lemma* measure_theory.lintegral_bUnion_finset₀
- \+ *lemma* measure_theory.lintegral_bUnion₀

Modified src/measure_theory/measure/ae_disjoint.lean
- \- *lemma* disjoint.ae_disjoint

Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.measure_bUnion_finset
- \+ *lemma* measure_theory.measure_bUnion_finset₀
- \+ *lemma* measure_theory.measure_bUnion₀
- \+ *lemma* measure_theory.measure_sUnion₀



## [2022-05-22 09:27:56](https://github.com/leanprover-community/mathlib/commit/726b9ce)
feat(set_theory/ordinal/arithmetic): Lemmas about `bsup o.succ f` on a monotone function ([#14289](https://github.com/leanprover-community/mathlib/pull/14289))
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean
- \+ *theorem* ordinal.blsub_succ_of_mono
- \+ *theorem* ordinal.bsup_succ_of_mono



## [2022-05-22 09:27:55](https://github.com/leanprover-community/mathlib/commit/e99ff88)
feat(measure_theory): add `restrict_inter_add_diff` and `lintegral_inter_add_diff` ([#14280](https://github.com/leanprover-community/mathlib/pull/14280))
* add `measure_theory.measure.restrict_inter_add_diff` and `measure_theory.lintegral_inter_add_diff`;
* drop one measurability assumption in `measure_theory.lintegral_union`;
* add `measure_theory.lintegral_max` and `measure_theory.set_lintegral_max`;
* drop `measure_theory.measure.lebesgue_decomposition.max_measurable_le`: use `set_lintegral_max` instead.
#### Estimated changes
Modified src/measure_theory/decomposition/lebesgue.lean
- \- *lemma* measure_theory.measure.lebesgue_decomposition.max_measurable_le

Modified src/measure_theory/integral/lebesgue.lean
- \+ *lemma* measure_theory.lintegral_inter_add_diff
- \+ *lemma* measure_theory.lintegral_max
- \+/\- *lemma* measure_theory.lintegral_union
- \+ *lemma* measure_theory.set_lintegral_max

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.measure.restrict_inter_add_diff
- \+ *lemma* measure_theory.measure.restrict_inter_add_diff₀



## [2022-05-22 09:27:53](https://github.com/leanprover-community/mathlib/commit/2d9f791)
feat(order/filter): add lemmas about filter.has_antitone_basis ([#14131](https://github.com/leanprover-community/mathlib/pull/14131))
* add `filter.has_antitone_basis.comp_mono` and
  `filter.has_antitone_basis.comp_strict_mono`;
* add `filter.has_antitone_basis.subbasis_with_rel`;
* generalize `filter.has_basis.exists_antitone_subbasis` to `ι : Sort*`.
* add a missing docstring.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.has_antitone_basis.comp_mono
- \+ *lemma* filter.has_antitone_basis.comp_strict_mono
- \+ *lemma* filter.has_antitone_basis.subbasis_with_rel

Modified src/order/filter/bases.lean




## [2022-05-22 09:27:53](https://github.com/leanprover-community/mathlib/commit/52df6ab)
refactor(category_theory): remove all decidability instances ([#14046](https://github.com/leanprover-community/mathlib/pull/14046))
Make the category theory library thoroughly classical: mostly this is ceasing carrying around decidability instances for the indexing types of biproducts, and for the object and morphism types in `fin_category`.
It appears there was no real payoff: the category theory library is already extremely non-constructive.
As I was running into occasional problems providing decidability instances (when writing construction involving reindexing biproducts), it seems easiest to just remove this vestigial constructiveness from the category theory library.
#### Estimated changes
Modified src/algebra/category/Group/biproducts.lean
- \+/\- *def* AddCommGroup.biproduct_iso_pi
- \+/\- *lemma* AddCommGroup.biproduct_iso_pi_inv_comp_π

Modified src/algebra/category/Module/abelian.lean


Modified src/algebra/category/Module/biproducts.lean
- \+/\- *def* Module.biproduct_iso_pi
- \+/\- *lemma* Module.biproduct_iso_pi_inv_comp_π

Modified src/category_theory/closed/ideal.lean


Modified src/category_theory/fin_category.lean


Modified src/category_theory/idempotents/biproducts.lean
- \+/\- *def* category_theory.idempotents.karoubi.biproducts.bicone

Modified src/category_theory/limits/bicones.lean
- \+/\- *def* category_theory.bicone_mk

Modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean


Modified src/category_theory/limits/constructions/over/products.lean


Modified src/category_theory/limits/lattice.lean
- \+/\- *lemma* category_theory.limits.complete_lattice.finite_coproduct_eq_finset_sup
- \+/\- *lemma* category_theory.limits.complete_lattice.finite_product_eq_finset_inf

Modified src/category_theory/limits/opposites.lean


Modified src/category_theory/limits/preserves/shapes/biproducts.lean


Modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *lemma* category_theory.limits.biproduct.from_subtype_π
- \+/\- *lemma* category_theory.limits.biproduct.ι_to_subtype
- \+/\- *lemma* category_theory.limits.biproduct.ι_π

Modified src/category_theory/limits/shapes/finite_limits.lean


Modified src/category_theory/limits/shapes/finite_products.lean


Modified src/category_theory/limits/shapes/zero_morphisms.lean


Modified src/category_theory/monoidal/preadditive.lean
- \+/\- *def* category_theory.left_distributor
- \+/\- *lemma* category_theory.left_distributor_assoc
- \+/\- *lemma* category_theory.left_distributor_hom
- \+/\- *lemma* category_theory.left_distributor_inv
- \+/\- *def* category_theory.right_distributor
- \+/\- *lemma* category_theory.right_distributor_assoc
- \+/\- *lemma* category_theory.right_distributor_hom
- \+/\- *lemma* category_theory.right_distributor_inv

Modified src/category_theory/preadditive/Mat.lean


Modified src/category_theory/preadditive/additive_functor.lean


Modified src/category_theory/preadditive/biproducts.lean


Modified src/category_theory/preadditive/injective.lean


Modified src/category_theory/preadditive/projective.lean


Modified src/representation_theory/Action.lean




## [2022-05-22 08:40:44](https://github.com/leanprover-community/mathlib/commit/37647bf)
feat(measure_theory/constructions/borel_space): add `norm_cast` lemmas ([#14295](https://github.com/leanprover-community/mathlib/pull/14295))
#### Estimated changes
Modified src/measure_theory/constructions/borel_space.lean
- \+ *lemma* ae_measurable_coe_nnreal_ennreal_iff
- \+ *lemma* ae_measurable_coe_nnreal_real_iff
- \+/\- *lemma* measurable_coe_nnreal_ennreal_iff
- \+ *lemma* measurable_coe_nnreal_real_iff



## [2022-05-22 06:29:42](https://github.com/leanprover-community/mathlib/commit/9b8588a)
chore(algebra/order/ring): golf `mul_le_one` ([#14245](https://github.com/leanprover-community/mathlib/pull/14245))
golf `mul_le_one`
#### Estimated changes
Modified src/algebra/order/ring.lean




## [2022-05-22 06:29:41](https://github.com/leanprover-community/mathlib/commit/49ce967)
feat(ring_theory/valuation/basic): notation for `with_zero (multiplicative ℤ)` ([#14064](https://github.com/leanprover-community/mathlib/pull/14064))
And likewise for `with_zero (multiplicative ℕ)`
#### Estimated changes
Modified src/number_theory/function_field.lean
- \+/\- *def* function_field.infty_valuation
- \+/\- *def* function_field.infty_valuation_def
- \+/\- *def* function_field.infty_valued_Fqt

Modified src/ring_theory/dedekind_domain/adic_valuation.lean
- \+/\- *def* is_dedekind_domain.height_one_spectrum.adic_valued
- \+/\- *def* is_dedekind_domain.height_one_spectrum.int_valuation
- \+/\- *def* is_dedekind_domain.height_one_spectrum.int_valuation_def
- \+/\- *def* is_dedekind_domain.height_one_spectrum.valuation

Modified src/ring_theory/valuation/basic.lean




## [2022-05-22 04:22:45](https://github.com/leanprover-community/mathlib/commit/a8a211f)
feat(order/lattice): add `left_lt_inf` etc ([#14152](https://github.com/leanprover-community/mathlib/pull/14152))
* add `left_lt_sup`, `right_lt_sup`, `left_or_right_lt_sup`, and their `inf` counterparts;
* generalize `is_top_or_exists_gt` and `is_bot_or_exists_lt` to directed orders, replacing `forall_le_or_exists_lt_inf` and `forall_le_or_exists_lt_sup`;
* generalize `exists_lt_of_sup` and `exists_lt_of_inf` to directed orders, rename them to `exists_lt_of_directed_le` and `exists_lt_of_directed_ge`.
#### Estimated changes
Modified src/order/directed.lean
- \+ *theorem* exists_lt_of_directed_ge
- \+ *theorem* exists_lt_of_directed_le
- \+ *lemma* is_bot_or_exists_lt
- \+ *lemma* is_top_or_exists_gt

Modified src/order/lattice.lean
- \- *theorem* exists_lt_of_inf
- \- *theorem* exists_lt_of_sup
- \- *lemma* forall_le_or_exists_lt_inf
- \- *lemma* forall_le_or_exists_lt_sup
- \+ *theorem* inf_lt_left
- \+ *theorem* inf_lt_left_or_right
- \+ *theorem* inf_lt_right
- \+ *theorem* left_lt_sup
- \+ *lemma* left_or_right_lt_sup
- \+ *theorem* right_lt_sup

Modified src/order/max.lean
- \- *lemma* is_bot_or_exists_lt
- \- *lemma* is_top_or_exists_gt

Modified src/topology/algebra/order/liminf_limsup.lean




## [2022-05-22 01:40:48](https://github.com/leanprover-community/mathlib/commit/d8b6f76)
feat(set_theory/game/birthday): More basic birthdays ([#14287](https://github.com/leanprover-community/mathlib/pull/14287))
#### Estimated changes
Modified src/set_theory/game/birthday.lean
- \+ *theorem* pgame.birthday_half
- \+ *theorem* pgame.birthday_star

Modified src/set_theory/ordinal/arithmetic.lean
- \+ *theorem* ordinal.succ_one



## [2022-05-21 11:38:54](https://github.com/leanprover-community/mathlib/commit/f04684f)
chore(data/set/pointwise): Move into the `set` namespace ([#14281](https://github.com/leanprover-community/mathlib/pull/14281))
A bunch of lemmas about scalar multiplications of sets were dumped in root namespace for some reason.
The lemmas moved to `set.*` are:
* `zero_smul_set`
* `zero_smul_subset`
* `subsingleton_zero_smul_set`
* `zero_mem_smul_set`
* `zero_mem_smul_iff`
* `zero_mem_smul_set_iff`
* `smul_add_set`
* `smul_mem_smul_set_iff`
* `mem_smul_set_iff_inv_smul_mem`
* `mem_inv_smul_set_iff`
* `preimage_smul`
* `preimage_smul_inv`
* `set_smul_subset_set_smul_iff`
* `set_smul_subset_iff`
* `subset_set_smul_iff`
* `smul_mem_smul_set_iff₀`
* `mem_smul_set_iff_inv_smul_mem₀`
* `mem_inv_smul_set_iff₀`
* `preimage_smul₀`
* `preimage_smul_inv₀`
* `set_smul_subset_set_smul_iff₀`
* `set_smul_subset_iff₀`
* `subset_set_smul_iff₀`
* `smul_univ₀`
* `smul_set_univ₀`
#### Estimated changes
Modified src/algebra/algebra/spectrum.lean


Modified src/data/set/pointwise.lean
- \- *lemma* mem_inv_smul_set_iff
- \- *lemma* mem_inv_smul_set_iff₀
- \- *lemma* mem_smul_set_iff_inv_smul_mem
- \- *lemma* mem_smul_set_iff_inv_smul_mem₀
- \- *lemma* preimage_smul
- \- *lemma* preimage_smul_inv
- \- *lemma* preimage_smul_inv₀
- \- *lemma* preimage_smul₀
- \+ *lemma* set.mem_inv_smul_set_iff
- \+ *lemma* set.mem_inv_smul_set_iff₀
- \+ *lemma* set.mem_smul_set_iff_inv_smul_mem
- \+ *lemma* set.mem_smul_set_iff_inv_smul_mem₀
- \+ *lemma* set.preimage_smul
- \+ *lemma* set.preimage_smul_inv
- \+ *lemma* set.preimage_smul_inv₀
- \+ *lemma* set.preimage_smul₀
- \+ *lemma* set.set_smul_subset_iff
- \+ *lemma* set.set_smul_subset_iff₀
- \+ *lemma* set.set_smul_subset_set_smul_iff
- \+ *lemma* set.set_smul_subset_set_smul_iff₀
- \+ *lemma* set.smul_mem_smul_set_iff
- \+ *lemma* set.smul_mem_smul_set_iff₀
- \+ *lemma* set.smul_set_univ₀
- \+ *lemma* set.smul_univ₀
- \+ *lemma* set.subset_set_smul_iff
- \+ *lemma* set.subset_set_smul_iff₀
- \+ *lemma* set.subsingleton_zero_smul_set
- \+ *lemma* set.zero_mem_smul_iff
- \+ *lemma* set.zero_mem_smul_set
- \+ *lemma* set.zero_mem_smul_set_iff
- \+ *lemma* set.zero_smul_set
- \+ *lemma* set.zero_smul_subset
- \- *lemma* set_smul_subset_iff
- \- *lemma* set_smul_subset_iff₀
- \- *lemma* set_smul_subset_set_smul_iff
- \- *lemma* set_smul_subset_set_smul_iff₀
- \- *lemma* smul_mem_smul_set_iff
- \- *lemma* smul_mem_smul_set_iff₀
- \- *lemma* smul_set_univ₀
- \- *lemma* smul_univ₀
- \- *lemma* subset_set_smul_iff
- \- *lemma* subset_set_smul_iff₀
- \- *lemma* subsingleton_zero_smul_set
- \- *lemma* zero_mem_smul_iff
- \- *lemma* zero_mem_smul_set
- \- *lemma* zero_mem_smul_set_iff
- \- *lemma* zero_smul_set
- \- *lemma* zero_smul_subset

Modified src/group_theory/free_product.lean


Modified src/group_theory/subgroup/pointwise.lean


Modified src/group_theory/submonoid/pointwise.lean


Modified src/ring_theory/subring/pointwise.lean


Modified src/ring_theory/subsemiring/pointwise.lean




## [2022-05-21 08:14:04](https://github.com/leanprover-community/mathlib/commit/fc19a4e)
feat({data/finset,order/filter}/pointwise): Multiplicative action on pointwise monoids ([#14214](https://github.com/leanprover-community/mathlib/pull/14214))
`mul_action`, `distrib_mul_action`, `mul_distrib_mul_action` instances for `finset` and `filter`. Also delete `set.smul_add_set` because `smul_add` proves it.
#### Estimated changes
Modified src/data/finset/n_ary.lean
- \+/\- *lemma* finset.image₂_singleton_left

Modified src/data/finset/pointwise.lean
- \+/\- *lemma* finset.coe_smul_finset

Modified src/data/set/pointwise.lean
- \- *lemma* smul_add_set

Modified src/measure_theory/function/jacobian.lean


Modified src/order/filter/pointwise.lean




## [2022-05-21 06:32:31](https://github.com/leanprover-community/mathlib/commit/eaa771f)
chore(tactic/cancel_denoms): remove an unused have ([#14269](https://github.com/leanprover-community/mathlib/pull/14269))
#### Estimated changes
Modified src/tactic/cancel_denoms.lean




## [2022-05-21 03:17:39](https://github.com/leanprover-community/mathlib/commit/d787d49)
feat(algebra/big_operators): add `finset.prod_comm'` ([#14257](https://github.com/leanprover-community/mathlib/pull/14257))
* add a "dependent" version of `finset.prod_comm`;
* use it to prove the original lemma;
* slightly generalize `exists_eq_right_right` and `exists_eq_right_right'`;
* add two `simps` attributes.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_comm'

Modified src/logic/basic.lean


Modified src/logic/embedding.lean
- \+/\- *def* function.embedding.sectl
- \+/\- *def* function.embedding.sectr



## [2022-05-21 00:59:53](https://github.com/leanprover-community/mathlib/commit/3fc6fbb)
feat(algebra/divisibility): `is_refl` and `is_trans` instances for divisibility ([#14240](https://github.com/leanprover-community/mathlib/pull/14240))
#### Estimated changes
Modified src/algebra/divisibility.lean
- \+/\- *theorem* dvd_refl
- \+ *theorem* dvd_rfl
- \- *lemma* dvd_rfl
- \+/\- *theorem* one_dvd



## [2022-05-21 00:22:23](https://github.com/leanprover-community/mathlib/commit/0e095f0)
feat(data/polynomial/mirror): `mirror` is injective ([#14254](https://github.com/leanprover-community/mathlib/pull/14254))
This PR adds an `inj` lemma for `mirror`.
#### Estimated changes
Modified src/data/polynomial/mirror.lean
- \+ *lemma* polynomial.mirror_inj



## [2022-05-20 23:44:35](https://github.com/leanprover-community/mathlib/commit/d217e1d)
feat(set_theory/game/pgame): `sub_self_equiv` ([#14272](https://github.com/leanprover-community/mathlib/pull/14272))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.sub_self_equiv



## [2022-05-20 18:26:01](https://github.com/leanprover-community/mathlib/commit/a6b90be)
refactor(set_theory/cardinal/*): add `succ_order` instance, rename `succ` lemmas ([#14244](https://github.com/leanprover-community/mathlib/pull/14244))
We rename the lemmas on `cardinal.succ` to better match those from `succ_order`.
- `succ_le` → `succ_le_iff`
- `lt_succ` → `lt_succ_iff`
- `lt_succ_self` → `lt_succ`
We also add `succ_le_of_lt` and `le_of_lt_succ`.
#### Estimated changes
Modified src/data/W/cardinal.lean


Modified src/set_theory/cardinal/basic.lean
- \+ *theorem* cardinal.le_of_lt_succ
- \+ *theorem* cardinal.le_succ
- \+/\- *theorem* cardinal.lt_succ
- \+ *theorem* cardinal.lt_succ_iff
- \- *theorem* cardinal.lt_succ_self
- \- *theorem* cardinal.succ_le
- \+ *theorem* cardinal.succ_le_iff
- \+ *theorem* cardinal.succ_le_of_lt
- \+/\- *theorem* cardinal.succ_nonempty
- \+/\- *lemma* cardinal.succ_pos

Modified src/set_theory/cardinal/cofinality.lean


Modified src/set_theory/cardinal/continuum.lean


Modified src/set_theory/cardinal/ordinal.lean


Modified src/set_theory/ordinal/arithmetic.lean


Modified src/set_theory/ordinal/basic.lean




## [2022-05-20 17:46:23](https://github.com/leanprover-community/mathlib/commit/113f7e4)
feat(linear_algebra/trace): trace of projection maps  ([#14165](https://github.com/leanprover-community/mathlib/pull/14165))
This is proved under the `field` assumption instead of the finite free module assumptions generally used to talk about the trace because we need the submodules `p` and `f.ker` to also be free and finite.
- [x] depends on: [#13872](https://github.com/leanprover-community/mathlib/pull/13872)
#### Estimated changes
Modified src/linear_algebra/contraction.lean


Modified src/linear_algebra/trace.lean
- \+ *theorem* linear_map.is_proj.trace
- \+ *theorem* linear_map.trace_id



## [2022-05-20 16:36:21](https://github.com/leanprover-community/mathlib/commit/1983e40)
feat(data/zmod/basic): If the orbit is finite, then the minimal period is positive ([#14201](https://github.com/leanprover-community/mathlib/pull/14201))
This PR adds an instance stating that if the orbit is finite, then the minimal period is positive.
The instance is needed for an explicit computation that involves a product indexed by `zmod (minimal_period ((•) a) b)`.
#### Estimated changes
Modified src/data/zmod/basic.lean


Modified src/data/zmod/quotient.lean




## [2022-05-20 15:32:16](https://github.com/leanprover-community/mathlib/commit/846ed9f)
chore(measure_theory/integral/lebesgue): golf some proofs ([#14256](https://github.com/leanprover-community/mathlib/pull/14256))
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean




## [2022-05-20 13:34:14](https://github.com/leanprover-community/mathlib/commit/180d975)
feat(set_theory/game/pgame): Tweak `pgame.add` API ([#13611](https://github.com/leanprover-community/mathlib/pull/13611))
We modify the API for `pgame.add` as follows: 
- `left_moves_add` and `right_moves_add` are turned from type equivalences into type equalities.
- The former equivalences are prefixed with `to_` and inverted.
We also golf a few theorems and make some parameters explicit.
#### Estimated changes
Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/nim.lean


Modified src/set_theory/game/pgame.lean
- \- *def* pgame.add
- \+/\- *lemma* pgame.add_move_left_inl
- \+/\- *lemma* pgame.add_move_left_inr
- \+/\- *lemma* pgame.add_move_right_inl
- \+/\- *lemma* pgame.add_move_right_inr
- \+ *theorem* pgame.left_moves_add
- \- *def* pgame.left_moves_add
- \+ *lemma* pgame.left_moves_add_cases
- \+ *theorem* pgame.right_moves_add
- \- *def* pgame.right_moves_add
- \+ *lemma* pgame.right_moves_add_cases
- \+ *def* pgame.to_left_moves_add
- \+ *def* pgame.to_right_moves_add

Modified src/set_theory/surreal/basic.lean




## [2022-05-20 11:17:03](https://github.com/leanprover-community/mathlib/commit/1483eca)
feat(algebra/algebra/operations): add right induction principles for power membership ([#14219](https://github.com/leanprover-community/mathlib/pull/14219))
We already had the left-induction principles.
There's probably some clever trick to get these via `mul_opposite`, but I'm not sure if it's worth the effort.
#### Estimated changes
Modified src/algebra/algebra/operations.lean


Modified src/linear_algebra/clifford_algebra/grading.lean


Modified src/linear_algebra/exterior_algebra/grading.lean


Modified src/linear_algebra/tensor_algebra/grading.lean




## [2022-05-20 06:26:14](https://github.com/leanprover-community/mathlib/commit/1e011e3)
feat(linear_algebra/trace): trace of prod_map ([#13872](https://github.com/leanprover-community/mathlib/pull/13872))
In this PR I prove that the trace is additive under `prod_map`, i.e. that `trace (prod_map f g) = trace f + trace g`.
#### Estimated changes
Modified src/linear_algebra/contraction.lean
- \+ *lemma* dual_tensor_hom_prod_map_zero
- \+ *lemma* zero_prod_map_dual_tensor_hom

Modified src/linear_algebra/trace.lean
- \+ *theorem* linear_map.trace_prod_map'
- \+ *theorem* linear_map.trace_prod_map



## [2022-05-20 04:06:08](https://github.com/leanprover-community/mathlib/commit/735fbe0)
chore(scripts): update nolints.txt ([#14255](https://github.com/leanprover-community/mathlib/pull/14255))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/style-exceptions.txt




## [2022-05-20 01:48:36](https://github.com/leanprover-community/mathlib/commit/a5878bb)
feat(data/polynomial/mirror): `mirror_eq_iff` ([#14238](https://github.com/leanprover-community/mathlib/pull/14238))
This PR adds a lemma stating that `p.mirror = q ↔ p = q.mirror`.
#### Estimated changes
Modified src/data/polynomial/mirror.lean
- \+ *lemma* polynomial.mirror_eq_iff
- \+/\- *lemma* polynomial.mirror_eq_zero
- \+ *lemma* polynomial.mirror_involutive
- \+/\- *lemma* polynomial.mirror_leading_coeff
- \+/\- *lemma* polynomial.mirror_trailing_coeff



## [2022-05-20 00:16:04](https://github.com/leanprover-community/mathlib/commit/c9c9fa1)
refactor(category_theory/discrete): make discrete irreducible ([#13762](https://github.com/leanprover-community/mathlib/pull/13762))
#### Estimated changes
Modified src/algebra/category/Group/biproducts.lean
- \+ *lemma* AddCommGroup.biprod_iso_prod_inv_comp_fst
- \+ *lemma* AddCommGroup.biprod_iso_prod_inv_comp_snd
- \+/\- *def* AddCommGroup.has_limit.lift
- \- *lemma* AddCommGroup.has_limit.lift_apply
- \+/\- *def* AddCommGroup.has_limit.product_limit_cone

Modified src/algebra/category/Module/biproducts.lean
- \+/\- *def* Module.has_limit.lift
- \- *lemma* Module.has_limit.lift_apply
- \+/\- *def* Module.has_limit.product_limit_cone

Modified src/algebra/category/Module/products.lean


Modified src/algebra/category/Ring/constructions.lean


Modified src/algebraic_geometry/locally_ringed_space/has_colimits.lean


Modified src/algebraic_geometry/open_immersion.lean
- \+/\- *lemma* algebraic_geometry.SheafedSpace.is_open_immersion.image_preimage_is_empty

Modified src/algebraic_geometry/sheafed_space.lean


Modified src/algebraic_topology/fundamental_groupoid/product.lean


Modified src/category_theory/adjunction/comma.lean


Modified src/category_theory/adjunction/evaluation.lean


Modified src/category_theory/adjunction/over.lean


Modified src/category_theory/bicategory/coherence.lean
- \+ *lemma* category_theory.free_bicategory.preinclusion_map₂

Modified src/category_theory/bicategory/locally_discrete.lean
- \+ *lemma* category_theory.locally_discrete.eq_of_hom
- \+/\- *def* category_theory.locally_discrete

Modified src/category_theory/category/Cat.lean


Modified src/category_theory/category/Groupoid.lean
- \- *def* category_theory.Groupoid.pi_limit_cone
- \+ *def* category_theory.Groupoid.pi_limit_fan
- \- *abbreviation* category_theory.Groupoid.pi_limit_fan
- \+ *def* category_theory.Groupoid.pi_limit_fan_is_limit

Modified src/category_theory/discrete_category.lean
- \+/\- *lemma* category_theory.discrete.eq_of_hom
- \+ *abbreviation* category_theory.discrete.eq_to_hom'
- \+ *abbreviation* category_theory.discrete.eq_to_hom
- \+ *abbreviation* category_theory.discrete.eq_to_iso'
- \+ *abbreviation* category_theory.discrete.eq_to_iso
- \+/\- *lemma* category_theory.discrete.id_def
- \+ *lemma* category_theory.discrete.mk_as
- \+/\- *def* category_theory.discrete.nat_iso_functor
- \- *lemma* category_theory.discrete.nat_iso_hom_app
- \- *lemma* category_theory.discrete.nat_iso_inv_app
- \- *lemma* category_theory.discrete.nat_trans_app
- \+ *structure* category_theory.discrete
- \- *def* category_theory.discrete
- \+ *def* category_theory.discrete_equiv

Modified src/category_theory/elements.lean


Modified src/category_theory/fin_category.lean


Modified src/category_theory/functor/flat.lean


Modified src/category_theory/graded_object.lean


Modified src/category_theory/grothendieck.lean


Modified src/category_theory/is_connected.lean


Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/constructions/binary_products.lean


Modified src/category_theory/limits/constructions/finite_products_of_binary_products.lean


Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/constructions/over/products.lean


Modified src/category_theory/limits/final.lean


Modified src/category_theory/limits/kan_extension.lean


Modified src/category_theory/limits/lattice.lean


Modified src/category_theory/limits/preserves/shapes/biproducts.lean


Modified src/category_theory/limits/preserves/shapes/products.lean


Modified src/category_theory/limits/presheaf.lean


Modified src/category_theory/limits/punit.lean


Modified src/category_theory/limits/shapes/binary_products.lean
- \+/\- *abbreviation* category_theory.limits.binary_cofan.inl
- \+/\- *abbreviation* category_theory.limits.binary_cofan.inr
- \+/\- *abbreviation* category_theory.limits.binary_fan.fst
- \+/\- *abbreviation* category_theory.limits.binary_fan.snd
- \+/\- *def* category_theory.limits.map_pair
- \+/\- *def* category_theory.limits.map_pair_iso
- \+/\- *lemma* category_theory.limits.map_pair_left
- \+/\- *lemma* category_theory.limits.map_pair_right
- \+ *def* category_theory.limits.pair_function
- \+ *lemma* category_theory.limits.pair_function_left
- \+ *lemma* category_theory.limits.pair_function_right
- \+/\- *lemma* category_theory.limits.pair_obj_left
- \+/\- *lemma* category_theory.limits.pair_obj_right

Modified src/category_theory/limits/shapes/biproducts.lean
- \+/\- *def* category_theory.limits.bicone.to_binary_bicone
- \+/\- *def* category_theory.limits.bicone.to_binary_bicone_is_bilimit
- \+/\- *def* category_theory.limits.bicone.to_binary_bicone_is_colimit
- \+/\- *def* category_theory.limits.bicone.to_binary_bicone_is_limit
- \+ *lemma* category_theory.limits.bicone.to_cocone_X
- \+ *lemma* category_theory.limits.bicone.to_cocone_ι_app
- \+ *lemma* category_theory.limits.bicone.to_cone_X
- \+ *lemma* category_theory.limits.bicone.to_cone_π_app
- \+/\- *def* category_theory.limits.binary_bicone.to_bicone

Modified src/category_theory/limits/shapes/disjoint_coproduct.lean


Modified src/category_theory/limits/shapes/multiequalizer.lean


Modified src/category_theory/limits/shapes/products.lean
- \+ *def* category_theory.limits.fan.proj
- \+ *lemma* category_theory.limits.fan_mk_proj
- \+ *lemma* category_theory.limits.has_products_of_limit_fans
- \+ *def* category_theory.limits.mk_fan_limit

Modified src/category_theory/limits/shapes/terminal.lean


Modified src/category_theory/limits/shapes/types.lean


Modified src/category_theory/limits/shapes/zero_objects.lean


Modified src/category_theory/limits/small_complete.lean


Modified src/category_theory/monoidal/CommMon_.lean


Modified src/category_theory/monoidal/Mon_.lean


Modified src/category_theory/monoidal/braided.lean


Modified src/category_theory/monoidal/discrete.lean


Modified src/category_theory/monoidal/free/coherence.lean
- \+ *lemma* category_theory.free_monoidal_category.discrete_functor_map_eq_id
- \+ *lemma* category_theory.free_monoidal_category.discrete_functor_obj_eq_as
- \+/\- *def* category_theory.free_monoidal_category.normalize_obj
- \+/\- *lemma* category_theory.free_monoidal_category.normalize_obj_tensor
- \+/\- *lemma* category_theory.free_monoidal_category.normalize_obj_unitor

Modified src/category_theory/monoidal/of_chosen_finite_products.lean


Modified src/category_theory/opposites.lean
- \+ *def* category_theory.iso_op_equiv

Modified src/category_theory/over.lean
- \+/\- *lemma* category_theory.over.over_right
- \+/\- *lemma* category_theory.under.under_left

Modified src/category_theory/pempty.lean


Modified src/category_theory/preadditive/additive_functor.lean


Modified src/category_theory/preadditive/injective.lean


Modified src/category_theory/preadditive/projective.lean


Modified src/category_theory/punit.lean


Modified src/category_theory/shift.lean
- \+/\- *lemma* category_theory.has_shift.shift_obj_obj
- \+/\- *def* category_theory.opaque_eq_to_iso
- \+/\- *abbreviation* category_theory.shift_functor

Modified src/category_theory/simple.lean


Modified src/category_theory/sites/sheaf_of_types.lean


Modified src/category_theory/structured_arrow.lean
- \+/\- *def* category_theory.costructured_arrow.mk
- \+/\- *lemma* category_theory.costructured_arrow.mk_right
- \+/\- *def* category_theory.structured_arrow.mk
- \+/\- *lemma* category_theory.structured_arrow.mk_left

Modified src/category_theory/subterminal.lean


Modified src/order/category/omega_complete_partial_order.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/gluing.lean


Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean
- \+/\- *lemma* Top.presheaf.sheaf_condition_equalizer_products.res_π

Modified src/topology/sheaves/sheaf_condition/opens_le_cover.lean


Modified src/topology/sheaves/sheaf_condition/pairwise_intersections.lean


Modified src/topology/sheaves/sheaf_condition/sites.lean


Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean


Modified src/topology/sheaves/stalks.lean




## [2022-05-19 19:16:16](https://github.com/leanprover-community/mathlib/commit/5cf7a1c)
feat (algebra/group/prod): Showing that embed_product is injective ([#14247](https://github.com/leanprover-community/mathlib/pull/14247))
Proves that `embed_product` is injective.
#### Estimated changes
Modified src/algebra/group/prod.lean
- \+ *lemma* units.embed_product_injective



## [2022-05-19 19:16:15](https://github.com/leanprover-community/mathlib/commit/3c6f16c)
feat(algebra/group/conj): instances + misc ([#13943](https://github.com/leanprover-community/mathlib/pull/13943))
#### Estimated changes
Modified src/algebra/group/conj.lean
- \+ *lemma* is_conj_comm

Modified src/group_theory/commuting_probability.lean
- \+/\- *lemma* card_comm_eq_card_conj_classes_mul_card



## [2022-05-19 17:11:59](https://github.com/leanprover-community/mathlib/commit/c8f2a1f)
chore(*) : `zero_dvd_iff.1` → `eq_zero_of_zero_dvd` ([#14241](https://github.com/leanprover-community/mathlib/pull/14241))
We already had a name for this theorem, so we might as well use it.
#### Estimated changes
Modified src/algebra/divisibility.lean


Modified src/algebra/gcd_monoid/basic.lean


Modified src/data/nat/totient.lean


Modified src/group_theory/specific_groups/cyclic.lean




## [2022-05-19 17:11:58](https://github.com/leanprover-community/mathlib/commit/ffe7002)
feat(topology/locally_constant): Characteristic functions on clopen sets are locally constant ([#11708](https://github.com/leanprover-community/mathlib/pull/11708))
Gives an API for characteristic functions on clopen sets, `char_fn`, which are locally constant functions.
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+ *lemma* set.indicator_eq_one_iff_mem
- \+ *lemma* set.indicator_eq_zero_iff_not_mem
- \+ *lemma* set.indicator_one_inj

Modified src/topology/locally_constant/algebra.lean
- \+ *lemma* locally_constant.char_fn_eq_one
- \+ *lemma* locally_constant.char_fn_eq_zero
- \+ *lemma* locally_constant.char_fn_inj
- \+ *lemma* locally_constant.coe_char_fn

Modified src/topology/locally_constant/basic.lean
- \+ *theorem* locally_constant.mul_indicator_apply_eq_if
- \+ *theorem* locally_constant.mul_indicator_of_mem
- \+ *theorem* locally_constant.mul_indicator_of_not_mem



## [2022-05-19 16:29:55](https://github.com/leanprover-community/mathlib/commit/d403cad)
chore(linear_algebra/quadratic_form/basic): remove redundant fields ([#14246](https://github.com/leanprover-community/mathlib/pull/14246))
This renames `quadratic_form.mk_left` to `quadratic_form.mk` by removing the redundant fields in the structure, as the proof of `mk_left` didn't actually use the fact the ring was commutative as it claimed to in the docstring.
The only reason we could possibly want these is if addition were non-commutative, which seems extremely unlikely.
#### Estimated changes
Modified src/linear_algebra/quadratic_form/basic.lean
- \- *def* quadratic_form.mk_left



## [2022-05-19 14:21:27](https://github.com/leanprover-community/mathlib/commit/218d66a)
doc(tactic/lint/type_classes): Fix small typo ([#14242](https://github.com/leanprover-community/mathlib/pull/14242))
#### Estimated changes
Modified src/tactic/lint/type_classes.lean




## [2022-05-19 12:28:20](https://github.com/leanprover-community/mathlib/commit/e29d911)
feat(group_theory/quotient_group): properties of quotients of homomorphisms and equivalences ([#13046](https://github.com/leanprover-community/mathlib/pull/13046))
Add `id`, `comp` for quotients of homomorphisms and `refl`, `symm`, `trans` for quotients of equivalences.
#### Estimated changes
Modified src/group_theory/quotient_group.lean
- \+/\- *def* quotient_group.equiv_quotient_zpow_of_equiv
- \+ *lemma* quotient_group.equiv_quotient_zpow_of_equiv_refl
- \+ *lemma* quotient_group.equiv_quotient_zpow_of_equiv_symm
- \+ *lemma* quotient_group.equiv_quotient_zpow_of_equiv_trans
- \+/\- *def* quotient_group.hom_quotient_zpow_of_hom
- \+ *lemma* quotient_group.hom_quotient_zpow_of_hom_comp
- \+ *lemma* quotient_group.hom_quotient_zpow_of_hom_comp_of_right_inverse
- \+ *lemma* quotient_group.hom_quotient_zpow_of_hom_id
- \- *lemma* quotient_group.hom_quotient_zpow_of_hom_right_inverse



## [2022-05-19 10:20:40](https://github.com/leanprover-community/mathlib/commit/18624ef)
feat(order/complete_lattice): add `Sup_diff_singleton_bot` etc ([#14205](https://github.com/leanprover-community/mathlib/pull/14205))
* add `Sup_diff_singleton_bot` and `Inf_diff_singleton_top`;
* add `set.sUnion_diff_singleton_empty` and `set.sInter_diff_singleton_univ`.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* set.sInter_diff_singleton_univ
- \+ *lemma* set.sUnion_diff_singleton_empty

Modified src/order/complete_lattice.lean
- \+ *theorem* Inf_diff_singleton_top
- \+ *theorem* Sup_diff_singleton_bot



## [2022-05-19 09:41:31](https://github.com/leanprover-community/mathlib/commit/6906b6f)
feat(analysis/normed_space/pi_Lp): add missing nnnorm lemmas ([#14221](https://github.com/leanprover-community/mathlib/pull/14221))
This renames `pi_Lp.dist` to `pi_Lp.dist_eq` and `pi_Lp.edist` to `pi_Lp.edist_eq` to match `pi_Lp.norm_eq`.
The `nndist` version of these lemmas is new.
The `pi_Lp.norm_eq_of_L2` lemma was not stated at the correct generality, and has been moved to an earlier file where doing so is easier.
The `nnnorm` version of this lemma is new.
Also replaces some `∀` binders with `Π` to match the pretty-printer, and tidies some whitespace.
#### Estimated changes
Modified src/analysis/inner_product_space/pi_L2.lean
- \+ *lemma* euclidean_space.nnnorm_eq
- \- *lemma* pi_Lp.norm_eq_of_L2

Modified src/analysis/normed_space/pi_Lp.lean
- \+ *lemma* pi_Lp.dist_eq
- \+ *lemma* pi_Lp.edist_eq
- \+ *lemma* pi_Lp.nndist_eq
- \+ *lemma* pi_Lp.nnnorm_eq_of_L2
- \+ *lemma* pi_Lp.norm_eq_of_L2



## [2022-05-19 05:25:12](https://github.com/leanprover-community/mathlib/commit/ea3009f)
docs(category_theory/*): the last missing module docs ([#14237](https://github.com/leanprover-community/mathlib/pull/14237))
#### Estimated changes
Modified src/category_theory/limits/cones.lean


Modified src/category_theory/limits/creates.lean


Modified src/category_theory/limits/types.lean


Modified src/category_theory/monad/adjunction.lean


Modified src/category_theory/monad/basic.lean




## [2022-05-19 03:48:08](https://github.com/leanprover-community/mathlib/commit/923a14d)
chore(scripts): update nolints.txt ([#14239](https://github.com/leanprover-community/mathlib/pull/14239))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt


Modified scripts/style-exceptions.txt




## [2022-05-19 01:41:46](https://github.com/leanprover-community/mathlib/commit/83285b2)
refactor(set_theory/game/pgame): Rename `le_def_lf` → `le_iff_forall_lf` ([#14206](https://github.com/leanprover-community/mathlib/pull/14206))
One-sided variants of these have also been introduced.
#### Estimated changes
Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/nim.lean


Modified src/set_theory/game/pgame.lean
- \- *theorem* pgame.le_def_lf
- \+ *theorem* pgame.le_iff_forall_lf
- \+ *theorem* pgame.le_of_forall_lf
- \- *theorem* pgame.lf_def_le
- \+ *theorem* pgame.lf_iff_forall_le
- \+ *theorem* pgame.lf_of_forall_le

Modified src/set_theory/surreal/basic.lean


Modified src/set_theory/surreal/dyadic.lean




## [2022-05-19 00:34:01](https://github.com/leanprover-community/mathlib/commit/cc74bcb)
feat(topology/algebra/module/basic): add `continuous_linear_map.apply_module` ([#14223](https://github.com/leanprover-community/mathlib/pull/14223))
This matches `linear_map.apply_module`, but additionally provides `has_continuous_const_smul`.
This also adds the missing `continuous_linear_map.semiring` and `continuous_linear_map.monoid_with_zero` instances.
#### Estimated changes
Modified src/topology/algebra/module/basic.lean
- \+ *def* continuous_linear_map.to_linear_map_ring_hom



## [2022-05-18 23:17:05](https://github.com/leanprover-community/mathlib/commit/76f9f45)
feat(category_theory/limits): (co/bi)products over types with a unique term ([#14191](https://github.com/leanprover-community/mathlib/pull/14191))
#### Estimated changes
Modified src/category_theory/discrete_category.lean


Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.biproduct_unique_iso
- \+ *def* category_theory.limits.limit_bicone_of_unique

Modified src/category_theory/limits/shapes/products.lean
- \+ *def* category_theory.limits.colimit_cocone_of_unique
- \+ *def* category_theory.limits.coproduct_unique_iso
- \+ *def* category_theory.limits.limit_cone_of_unique
- \+ *def* category_theory.limits.product_unique_iso



## [2022-05-18 22:19:04](https://github.com/leanprover-community/mathlib/commit/c42cff1)
doc(deprecated/*): all deprecated files now lint ([#14233](https://github.com/leanprover-community/mathlib/pull/14233))
I am happy to remove some nolints for you.
#### Estimated changes
Modified src/deprecated/group.lean


Modified src/deprecated/subfield.lean


Modified src/deprecated/subring.lean




## [2022-05-18 22:19:03](https://github.com/leanprover-community/mathlib/commit/a5f4cf5)
fix(algebra/ring_quot): fix a diamond in the int-smul action ([#14226](https://github.com/leanprover-community/mathlib/pull/14226))
We already handle the `nsmul` diamond correctly in the lines above
#### Estimated changes
Modified src/algebra/ring_quot.lean




## [2022-05-18 20:08:39](https://github.com/leanprover-community/mathlib/commit/32700f5)
refactor(*): `insert_singleton` → `pair` ([#14210](https://github.com/leanprover-community/mathlib/pull/14210))
We rename various theorems with `insert_singleton` in the name to the more sensible and searchable `pair`. We also golf `finset.pair_comm`.
#### Estimated changes
Modified src/data/finset/basic.lean
- \- *theorem* finset.insert_singleton_comm
- \- *theorem* finset.insert_singleton_self_eq
- \+ *theorem* finset.pair_comm
- \+ *theorem* finset.pair_self_eq

Modified src/geometry/euclidean/basic.lean
- \- *lemma* euclidean_geometry.cospherical_insert_singleton
- \+ *lemma* euclidean_geometry.cospherical_pair

Modified src/geometry/euclidean/circumcenter.lean


Modified src/geometry/euclidean/monge_point.lean
- \- *lemma* affine.simplex.affine_span_insert_singleton_eq_altitude_iff
- \+ *lemma* affine.simplex.affine_span_pair_eq_altitude_iff

Modified src/group_theory/perm/support.lean


Modified src/linear_algebra/affine_space/combination.lean
- \- *lemma* finset.centroid_insert_singleton
- \- *lemma* finset.centroid_insert_singleton_fin
- \+ *lemma* finset.centroid_pair
- \+ *lemma* finset.centroid_pair_fin

Modified src/linear_algebra/affine_space/finite_dimensional.lean
- \- *lemma* collinear_insert_singleton
- \+ *lemma* collinear_pair

Modified src/number_theory/divisors.lean




## [2022-05-18 20:08:38](https://github.com/leanprover-community/mathlib/commit/5fe43a9)
feat(linear_algebra/trace): trace of tensor_products and hom_tensor_hom is an equivalence ([#13728](https://github.com/leanprover-community/mathlib/pull/13728))
#### Estimated changes
Modified src/linear_algebra/contraction.lean
- \+ *lemma* dual_tensor_hom_equiv_of_basis_symm_cancel_left
- \+ *lemma* dual_tensor_hom_equiv_of_basis_symm_cancel_right
- \+ *def* hom_tensor_hom_equiv
- \+ *lemma* hom_tensor_hom_equiv_apply
- \+ *lemma* hom_tensor_hom_equiv_to_linear_map
- \+ *lemma* ltensor_hom_equiv_hom_ltensor_apply
- \+ *lemma* ltensor_hom_equiv_hom_ltensor_to_linear_map
- \+ *lemma* map_dual_tensor_hom
- \+ *lemma* rtensor_hom_equiv_hom_rtensor_apply
- \+ *lemma* rtensor_hom_equiv_hom_rtensor_to_linear_map

Modified src/linear_algebra/tensor_product.lean
- \+ *def* tensor_product.ltensor_hom_to_hom_ltensor
- \+ *lemma* tensor_product.ltensor_hom_to_hom_ltensor_apply
- \+ *def* tensor_product.rtensor_hom_to_hom_rtensor
- \+ *lemma* tensor_product.rtensor_hom_to_hom_rtensor_apply

Modified src/linear_algebra/trace.lean
- \+ *theorem* linear_map.trace_tensor_product'
- \+ *theorem* linear_map.trace_tensor_product



## [2022-05-18 18:01:54](https://github.com/leanprover-community/mathlib/commit/259c951)
doc(src/deprecated/*): add module docstrings ([#14224](https://github.com/leanprover-community/mathlib/pull/14224))
Although we don't ever import them now, I add module docstrings for a couple of deprecated files to make the linter happier. I also attempt to unify the style in the docstrings of all the deprecated files.
#### Estimated changes
Modified src/deprecated/group.lean


Modified src/deprecated/ring.lean


Modified src/deprecated/subfield.lean


Modified src/deprecated/subgroup.lean


Modified src/deprecated/submonoid.lean


Modified src/deprecated/subring.lean




## [2022-05-18 18:01:53](https://github.com/leanprover-community/mathlib/commit/4f31117)
feat(data/set/basic): add `set.subset_range_iff_exists_image_eq` and `set.range_image` ([#14203](https://github.com/leanprover-community/mathlib/pull/14203))
* add `set.subset_range_iff_exists_image_eq` and `set.range_image`;
* use the former to golf `set.can_lift` (name fixed from `set.set.can_lift`);
* golf `set.exists_eq_singleton_iff_nonempty_subsingleton`.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.range_image
- \+ *lemma* set.subset_range_iff_exists_image_eq



## [2022-05-18 16:04:05](https://github.com/leanprover-community/mathlib/commit/470ddbd)
chore(analysis,topology): add missing ulift instances ([#14217](https://github.com/leanprover-community/mathlib/pull/14217))
#### Estimated changes
Modified src/algebra/algebra/basic.lean
- \+ *lemma* ulift.algebra_map_eq
- \+ *lemma* ulift.down_algebra_map

Modified src/analysis/normed/group/basic.lean
- \+ *lemma* ulift.nnnorm_def
- \+ *lemma* ulift.nnnorm_up
- \+ *lemma* ulift.norm_def
- \+ *lemma* ulift.norm_up

Modified src/analysis/normed/normed_field.lean


Modified src/analysis/normed_space/basic.lean


Modified src/topology/metric_space/basic.lean
- \+ *lemma* ulift.dist_eq
- \+ *lemma* ulift.dist_up_up
- \+ *lemma* ulift.nndist_eq
- \+ *lemma* ulift.nndist_up_up

Modified src/topology/metric_space/emetric_space.lean
- \+ *lemma* ulift.edist_eq
- \+ *lemma* ulift.edist_up_up



## [2022-05-18 16:04:04](https://github.com/leanprover-community/mathlib/commit/503970d)
chore(data/fintype/basic): Better `fin` lemmas ([#14200](https://github.com/leanprover-community/mathlib/pull/14200))
Turn `finset.image` into `finset.map` and `insert` into `finset.cons` in the three lemmas relating `univ : finset (fin (n + 1))` and `univ : finset (fin n)`. Golf proofs involving the related big operators lemmas.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.prod_empty
- \+ *lemma* finset.prod_of_empty

Modified src/algebra/big_operators/fin.lean
- \+ *lemma* fin.prod_cons
- \+/\- *theorem* fin.prod_univ_succ_above

Modified src/data/fin/tuple/nat_antidiagonal.lean


Modified src/data/fintype/basic.lean


Modified src/linear_algebra/linear_independent.lean




## [2022-05-18 16:04:03](https://github.com/leanprover-community/mathlib/commit/c38ab35)
feat(analysis/convex/combination): The convex hull of `s + t` ([#14160](https://github.com/leanprover-community/mathlib/pull/14160))
`convex_hull` distributes over pointwise addition of sets and commutes with pointwise scalar multiplication. Also delete `linear_map.image_convex_hull` because it duplicates `linear_map.convex_hull_image`.
#### Estimated changes
Modified src/analysis/convex/combination.lean
- \+ *lemma* convex_hull_add
- \+/\- *lemma* convex_hull_prod
- \+ *lemma* convex_hull_sub
- \+ *lemma* mk_mem_convex_hull_prod

Modified src/analysis/convex/hull.lean
- \+/\- *lemma* convex.convex_hull_eq
- \+ *lemma* convex.convex_hull_subset_iff
- \+ *lemma* convex_hull_eq_Inter
- \+ *lemma* convex_hull_neg
- \+ *lemma* convex_hull_smul
- \- *lemma* is_linear_map.image_convex_hull
- \- *lemma* linear_map.image_convex_hull
- \+ *lemma* mem_convex_hull_iff



## [2022-05-18 14:08:52](https://github.com/leanprover-community/mathlib/commit/cfedf1d)
feat(ring_theory/ideal/operations.lean): lemmas about coprime ideals ([#14176](https://github.com/leanprover-community/mathlib/pull/14176))
Generalises some lemmas from `ring_theory/coprime/lemmas.lean` to the case of non-principal ideals.
#### Estimated changes
Modified src/linear_algebra/dfinsupp.lean
- \+ *lemma* submodule.mem_supr_finset_iff_exists_sum

Added src/ring_theory/coprime/ideal.lean
- \+ *lemma* ideal.supr_infi_eq_top_iff_pairwise

Modified src/ring_theory/ideal/operations.lean
- \+ *lemma* ideal.infi_sup_eq_top
- \+ *lemma* ideal.mul_sup_eq_of_coprime_left
- \+ *lemma* ideal.mul_sup_eq_of_coprime_right
- \+ *lemma* ideal.pow_sup_eq_top
- \+ *lemma* ideal.pow_sup_pow_eq_top
- \+ *lemma* ideal.prod_sup_eq_top
- \+ *lemma* ideal.sup_infi_eq_top
- \+ *lemma* ideal.sup_mul_eq_of_coprime_left
- \+ *lemma* ideal.sup_mul_eq_of_coprime_right
- \+ *lemma* ideal.sup_pow_eq_top
- \+ *lemma* ideal.sup_prod_eq_top



## [2022-05-18 14:08:51](https://github.com/leanprover-community/mathlib/commit/2c2d515)
refactor(data/list/min_max): Generalise `list.argmin`/`list.argmax` to preorders ([#13221](https://github.com/leanprover-community/mathlib/pull/13221))
This PR generalises the contents of the `data/list/min_max` file from a `linear_order` down to a `preorder` with decidable `<`. Note that for this to work out, I have had to change the structure of the auxiliary function `argmax₂` to now mean `option.cases_on a (some b) (λ c, if f c < f b then some b else some c)`. This is because in the case of a preorder, `argmax₂` would perform the swap in the absence of the `≤` relation, which would result in a semi-random shuffle that doesn't look very `maximal`.
#### Estimated changes
Modified src/algebra/polynomial/big_operators.lean


Modified src/data/list/min_max.lean
- \+ *def* list.arg_aux
- \+ *lemma* list.arg_aux_self
- \+/\- *def* list.argmax
- \+/\- *theorem* list.argmax_eq_none
- \+/\- *theorem* list.argmax_eq_some_iff
- \+/\- *theorem* list.argmax_mem
- \+/\- *lemma* list.argmax_singleton
- \- *lemma* list.argmax_two_self
- \- *def* list.argmax₂
- \+/\- *def* list.argmin
- \+/\- *theorem* list.argmin_eq_none
- \+/\- *theorem* list.argmin_eq_some_iff
- \- *theorem* list.argmin_le_of_mem
- \+/\- *theorem* list.argmin_mem
- \+ *lemma* list.foldl_arg_aux_eq_none
- \- *lemma* list.foldl_argmax₂_eq_none
- \+ *lemma* list.foldr_max_of_ne_nil
- \+ *lemma* list.foldr_min_of_ne_nil
- \+/\- *theorem* list.index_of_argmax
- \+/\- *theorem* list.index_of_argmin
- \- *theorem* list.le_argmax_of_mem
- \+ *lemma* list.le_maximum_of_mem'
- \- *theorem* list.le_maximum_of_mem'
- \+ *lemma* list.le_maximum_of_mem
- \- *theorem* list.le_maximum_of_mem
- \+ *lemma* list.le_min_of_forall_le
- \- *lemma* list.le_min_of_le_forall
- \+ *lemma* list.le_minimum_of_mem'
- \- *theorem* list.le_minimum_of_mem'
- \+ *theorem* list.le_of_mem_argmax
- \+ *theorem* list.le_of_mem_argmin
- \+/\- *lemma* list.max_le_of_forall_le
- \- *lemma* list.max_nat_le_of_forall_le
- \- *lemma* list.maximum_eq_coe_foldr_max_of_ne_nil
- \+ *lemma* list.maximum_eq_coe_iff
- \- *theorem* list.maximum_eq_coe_iff
- \- *lemma* list.maximum_nat_eq_coe_foldr_max_of_ne_nil
- \+/\- *theorem* list.mem_argmax_iff
- \+/\- *theorem* list.mem_argmin_iff
- \- *lemma* list.minimum_eq_coe_foldr_min_of_ne_nil
- \+ *lemma* list.minimum_eq_coe_iff
- \- *theorem* list.minimum_eq_coe_iff
- \+ *lemma* list.minimum_le_of_mem
- \- *theorem* list.minimum_le_of_mem
- \+ *lemma* list.minimum_not_lt_of_mem
- \+ *theorem* list.not_lt_maximum_of_mem'
- \+ *lemma* list.not_lt_maximum_of_mem
- \+ *theorem* list.not_lt_minimum_of_mem'
- \+ *lemma* list.not_lt_of_mem_argmax
- \+ *lemma* list.not_lt_of_mem_argmin
- \+ *lemma* list.not_of_mem_foldl_arg_aux



## [2022-05-18 13:10:54](https://github.com/leanprover-community/mathlib/commit/54773fc)
feat(topology/algebra/module/multilinear): add `continuous_multilinear_map.smul_right` ([#14218](https://github.com/leanprover-community/mathlib/pull/14218))
See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Question.20about.20.60formal_multilinear_series.60 for one use case
#### Estimated changes
Modified src/topology/algebra/module/multilinear.lean
- \+ *def* continuous_multilinear_map.smul_right
- \+ *lemma* continuous_multilinear_map.smul_right_apply



## [2022-05-18 12:02:21](https://github.com/leanprover-community/mathlib/commit/9dc9c3e)
feat(logic/lemmas): Distributivity of `if then else` ([#14146](https://github.com/leanprover-community/mathlib/pull/14146))
Distributivity laws for `dite` and `ite`.
#### Estimated changes
Added src/logic/lemmas.lean
- \+ *lemma* dite_dite_distrib_left
- \+ *lemma* dite_dite_distrib_right
- \+ *lemma* dite_ite_distrib_left
- \+ *lemma* dite_ite_distrib_right
- \+ *lemma* ite_dite_distrib_left
- \+ *lemma* ite_dite_distrib_right
- \+ *lemma* ite_ite_distrib_left
- \+ *lemma* ite_ite_distrib_right



## [2022-05-18 10:31:07](https://github.com/leanprover-community/mathlib/commit/ae6a7c3)
feat(linear_algebra/multilinear/finite_dimensional): generalize to finite and free ([#14199](https://github.com/leanprover-community/mathlib/pull/14199))
This also renames some `free` and `finite` instances which had garbage names.
#### Estimated changes
Modified src/linear_algebra/free_module/basic.lean


Modified src/linear_algebra/free_module/finite/basic.lean


Modified src/linear_algebra/multilinear/finite_dimensional.lean


Modified src/ring_theory/noetherian.lean
- \- *theorem* ring.is_noetherian_of_zero_eq_one



## [2022-05-18 07:53:52](https://github.com/leanprover-community/mathlib/commit/59facea)
chore(data/multiset/basic): `∅` → `0` ([#14211](https://github.com/leanprover-community/mathlib/pull/14211))
It's preferred to use `0` instead of `∅` throughout the multiset API.
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+/\- *theorem* multiset.pair_comm



## [2022-05-18 04:57:17](https://github.com/leanprover-community/mathlib/commit/d08f734)
chore(measure_theory/function/strongly_measurable): golf some proofs ([#14209](https://github.com/leanprover-community/mathlib/pull/14209))
#### Estimated changes
Modified src/measure_theory/function/strongly_measurable.lean




## [2022-05-18 02:51:15](https://github.com/leanprover-community/mathlib/commit/50696a8)
chore(data/multiset/basic): Inline instances ([#14208](https://github.com/leanprover-community/mathlib/pull/14208))
We inline various protected theorems into the `ordered_cancel_add_comm_monoid` instance. We also declare `covariant_class` and `contravariant_class` instances, which make further theorems redundant.
#### Estimated changes
Modified src/data/multiset/basic.lean




## [2022-05-18 02:13:32](https://github.com/leanprover-community/mathlib/commit/9f6f605)
feat(data/polynomial/mirror): Central coefficient of `p * p.mirror` ([#14096](https://github.com/leanprover-community/mathlib/pull/14096))
This PR adds a lemma `(p * p.mirror).coeff (p.nat_degree + p.nat_trailing_degree) = p.sum (λ n, (^ 2))`.
I also rearranged the file by assumptions on the ring `R`.
#### Estimated changes
Modified src/data/polynomial/mirror.lean
- \+ *lemma* polynomial.coeff_mul_mirror
- \+/\- *lemma* polynomial.irreducible_of_mirror
- \+/\- *lemma* polynomial.mirror_mul_of_domain
- \+/\- *lemma* polynomial.mirror_neg
- \+/\- *lemma* polynomial.mirror_smul



## [2022-05-18 01:20:31](https://github.com/leanprover-community/mathlib/commit/f48cbb1)
feat(category_theory/limits): reindexing (co/bi)products ([#14193](https://github.com/leanprover-community/mathlib/pull/14193))
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.biproduct.reindex

Modified src/category_theory/limits/shapes/products.lean
- \+ *def* category_theory.limits.pi.reindex
- \+ *lemma* category_theory.limits.pi.reindex_hom_π
- \+ *lemma* category_theory.limits.pi.reindex_inv_π
- \+ *def* category_theory.limits.sigma.reindex
- \+ *lemma* category_theory.limits.sigma.ι_reindex_hom
- \+ *lemma* category_theory.limits.sigma.ι_reindex_inv



## [2022-05-17 23:22:58](https://github.com/leanprover-community/mathlib/commit/ca5930d)
feat(data/multiset/basic): `pair_comm` ([#14207](https://github.com/leanprover-community/mathlib/pull/14207))
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.pair_comm



## [2022-05-17 23:22:57](https://github.com/leanprover-community/mathlib/commit/6b291d7)
feat(analysis/special_functions/trigonometric/arctan): add `real.range_arctan` ([#14204](https://github.com/leanprover-community/mathlib/pull/14204))
#### Estimated changes
Modified src/analysis/special_functions/trigonometric/arctan.lean
- \+ *lemma* real.range_arctan



## [2022-05-17 23:22:56](https://github.com/leanprover-community/mathlib/commit/632fef3)
feat(analysis/normed_space/M_structure): Define L-projections, show they form a Boolean algebra ([#12173](https://github.com/leanprover-community/mathlib/pull/12173))
A continuous projection P on a normed space X is said to be an L-projection if, for all `x` in `X`,
```
∥x∥ = ∥P x∥ + ∥(1-P) x∥.
```
The range of an L-projection is said to be an L-summand of X.
A continuous projection P on a normed space X is said to be an M-projection if, for all `x` in `X`,
```
∥x∥ = max(∥P x∥,∥(1-P) x∥).
```
The range of an M-projection is said to be an M-summand of X.
The L-projections and M-projections form Boolean algebras. When X is a Banach space, the Boolean
algebra of L-projections is complete.
Let `X` be a normed space with dual `X^*`. A closed subspace `M` of `X` is said to be an M-ideal if
the topological annihilator `M^∘` is an L-summand of `X^*`.
M-ideal, M-summands and L-summands were introduced by Alfsen and Effros to
study the structure of general Banach spaces. When `A` is a JB*-triple, the M-ideals of `A` are
exactly the norm-closed ideals of `A`. When `A` is a JBW*-triple with predual `X`, the M-summands of
`A` are exactly the weak*-closed ideals, and their pre-duals can be identified with the L-summands
of `X`. In the special case when `A` is a C*-algebra, the M-ideals are exactly the norm-closed
two-sided ideals of `A`, when `A` is also a W*-algebra the M-summands are exactly the weak*-closed
two-sided ideals of `A`.
This initial PR limits itself to showing that the L-projections form a Boolean algebra. The approach followed is based on that used in `measure_theory.measurable_space`. The equivalent result for M-projections can be established by a similar argument or by a duality result (to be established). However, I thought it best to seek feedback before proceeding further.
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/ring/idempotents.lean


Added src/analysis/normed_space/M_structure.lean
- \+ *lemma* is_Lprojection.Lcomplement
- \+ *lemma* is_Lprojection.Lcomplement_iff
- \+ *lemma* is_Lprojection.coe_bot
- \+ *lemma* is_Lprojection.coe_compl
- \+ *lemma* is_Lprojection.coe_inf
- \+ *lemma* is_Lprojection.coe_one
- \+ *lemma* is_Lprojection.coe_sdiff
- \+ *lemma* is_Lprojection.coe_sup
- \+ *lemma* is_Lprojection.coe_top
- \+ *lemma* is_Lprojection.coe_zero
- \+ *lemma* is_Lprojection.commute
- \+ *lemma* is_Lprojection.compl_mul_left
- \+ *lemma* is_Lprojection.compl_orthog
- \+ *lemma* is_Lprojection.distrib_lattice_lemma
- \+ *lemma* is_Lprojection.join
- \+ *lemma* is_Lprojection.le_def
- \+ *lemma* is_Lprojection.mul
- \+ *structure* is_Lprojection
- \+ *structure* is_Mprojection



## [2022-05-17 21:17:37](https://github.com/leanprover-community/mathlib/commit/0afb90b)
refactor(algebra/parity): Generalize to division monoids ([#14187](https://github.com/leanprover-community/mathlib/pull/14187))
Generalize lemmas about `is_square`, `even` and `odd`. Improve dot notation.
#### Estimated changes
Modified src/algebra/group/opposite.lean
- \+/\- *def* mul_equiv.inv'

Modified src/algebra/parity.lean
- \+/\- *lemma* even.add_odd
- \+/\- *lemma* even.neg_one_zpow
- \+/\- *lemma* even.neg_zpow
- \+ *lemma* even.tsub
- \- *lemma* even.tsub_even
- \+/\- *lemma* even_abs
- \+ *lemma* is_square.div
- \- *lemma* is_square.div_is_square
- \+ *lemma* is_square.mul
- \- *lemma* is_square.mul_is_square
- \+/\- *def* is_square
- \+/\- *lemma* is_square_iff_exists_sq
- \+/\- *lemma* is_square_inv
- \+/\- *lemma* is_square_mul_self
- \+/\- *lemma* is_square_op_iff
- \+/\- *lemma* odd.add_odd
- \+ *lemma* odd.map
- \+ *lemma* odd.mul
- \- *lemma* odd.mul_odd
- \+/\- *lemma* odd_abs
- \+/\- *lemma* odd_neg
- \- *lemma* ring_hom.odd

Modified src/analysis/convex/specific_functions.lean




## [2022-05-17 20:04:43](https://github.com/leanprover-community/mathlib/commit/2158193)
feat(topology/instances/matrix): add topological/continuous instances ([#14202](https://github.com/leanprover-community/mathlib/pull/14202))
For completeness, `has_continuous_add` and `topological_add_group`
instances are added to matrices, as pi types already have
these. Additionally, `has_continuous_const_smul` and
`has_continuous_smul` matrix instances have been made more generic,
allowing differing index types.
#### Estimated changes
Modified src/topology/instances/matrix.lean




## [2022-05-17 18:49:25](https://github.com/leanprover-community/mathlib/commit/1f0f981)
chore(linear_algebra/multilinear/basic): move finite-dimensionality to a new file ([#14198](https://github.com/leanprover-community/mathlib/pull/14198))
`linear_algebra.matrix.to_lin` pulls in a lot of imports that appear to slow things down considerably in downstream files.
The proof is moved without modification.
#### Estimated changes
Modified src/linear_algebra/matrix/charpoly/minpoly.lean


Modified src/linear_algebra/multilinear/basic.lean


Added src/linear_algebra/multilinear/finite_dimensional.lean




## [2022-05-17 17:18:53](https://github.com/leanprover-community/mathlib/commit/ae6f59d)
feat(analysis/locally_convex/with_seminorms): pull back `with_seminorms` along a linear inducing ([#13549](https://github.com/leanprover-community/mathlib/pull/13549))
This show that, if `f : E -> F` is linear and the topology on `F` is induced by a family of seminorms `p`, then the topology induced on `E` through `f` is induced by the seminorms `(p i) ∘ f`.
- [x] depends on: [#13547](https://github.com/leanprover-community/mathlib/pull/13547)
#### Estimated changes
Modified src/analysis/locally_convex/with_seminorms.lean
- \+ *lemma* inducing.with_seminorms
- \+ *lemma* linear_map.with_seminorms_induced
- \+ *def* seminorm_family.comp
- \+ *lemma* seminorm_family.comp_apply
- \+ *lemma* seminorm_family.finset_sup_comp



## [2022-05-17 17:18:52](https://github.com/leanprover-community/mathlib/commit/ba38b47)
feat(group_theory/perm/list): Add missing `form_perm` lemmas ([#13218](https://github.com/leanprover-community/mathlib/pull/13218))
#### Estimated changes
Modified src/group_theory/perm/list.lean
- \+ *lemma* list.form_perm_mem_iff_mem
- \+ *lemma* list.mem_of_form_perm_apply_mem
- \+ *lemma* list.mem_of_form_perm_apply_ne



## [2022-05-17 15:35:00](https://github.com/leanprover-community/mathlib/commit/da201ad)
chore(set_theory/ordinal/{basic, arithmetic}): Inline instances ([#14076](https://github.com/leanprover-community/mathlib/pull/14076))
We inline various definition in the `ordinal` instances, thus avoiding protected (or unprotected!) definitions that are only used once.
#### Estimated changes
Modified src/set_theory/game/nim.lean


Modified src/set_theory/ordinal/arithmetic.lean
- \- *def* ordinal.opow
- \+ *theorem* ordinal.opow_def
- \- *def* ordinal.sub

Modified src/set_theory/ordinal/basic.lean
- \- *theorem* ordinal.le_total
- \- *def* ordinal.lt

Modified src/set_theory/ordinal/notation.lean
- \+/\- *theorem* nonote.repr_opow



## [2022-05-17 15:34:59](https://github.com/leanprover-community/mathlib/commit/600d8ea)
feat(topology/metric_space): define a pseudo metrizable space ([#14053](https://github.com/leanprover-community/mathlib/pull/14053))
* define `topological_space.pseudo_metrizable_space`;
* copy API from `topological_space.metrizable_space`;
* add `pi` instances;
* use `X`, `Y` instead of `α`, `β`.
#### Estimated changes
Modified src/topology/metric_space/basic.lean
- \+ *def* inducing.comap_pseudo_metric_space
- \+ *def* pseudo_metric_space.replace_topology
- \+ *lemma* pseudo_metric_space.replace_topology_eq

Modified src/topology/metric_space/metrizable.lean
- \+/\- *lemma* embedding.metrizable_space
- \+ *lemma* inducing.pseudo_metrizable_space



## [2022-05-17 15:34:57](https://github.com/leanprover-community/mathlib/commit/e2eea55)
feat(algebra/homology): short exact sequences ([#14009](https://github.com/leanprover-community/mathlib/pull/14009))
Migrating from LTE. (This is all Johan and Andrew's work, I think, I just tidied up some.)
Please feel free to push changes directly without consulting me. :-)
#### Estimated changes
Modified src/algebra/category/Module/adjunctions.lean


Added src/algebra/homology/short_exact/abelian.lean
- \+ *lemma* category_theory.is_iso_of_short_exact_of_is_iso_of_is_iso
- \+ *def* category_theory.left_split.splitting
- \+ *def* category_theory.splitting.mk'

Added src/algebra/homology/short_exact/preadditive.lean
- \+ *lemma* category_theory.exact_inl_snd
- \+ *lemma* category_theory.exact_inr_fst
- \+ *lemma* category_theory.exact_of_split
- \+ *lemma* category_theory.left_split.short_exact
- \+ *structure* category_theory.left_split
- \+ *lemma* category_theory.right_split.short_exact
- \+ *structure* category_theory.right_split
- \+ *structure* category_theory.short_exact
- \+ *lemma* category_theory.split.exact
- \+ *lemma* category_theory.split.left_split
- \+ *lemma* category_theory.split.map
- \+ *lemma* category_theory.split.right_split
- \+ *lemma* category_theory.split.short_exact
- \+ *structure* category_theory.split
- \+ *lemma* category_theory.splitting.comp_eq_zero
- \+ *lemma* category_theory.splitting.inl_comp_iso_eq
- \+ *lemma* category_theory.splitting.inr_iso_inv
- \+ *lemma* category_theory.splitting.iso_comp_eq_snd
- \+ *lemma* category_theory.splitting.iso_hom_fst
- \+ *def* category_theory.splitting.retraction
- \+ *lemma* category_theory.splitting.retraction_ι_eq_id_sub
- \+ *def* category_theory.splitting.section
- \+ *lemma* category_theory.splitting.section_retraction
- \+ *lemma* category_theory.splitting.section_π
- \+ *lemma* category_theory.splitting.short_exact
- \+ *lemma* category_theory.splitting.split
- \+ *lemma* category_theory.splitting.split_add
- \+ *def* category_theory.splitting.splitting_of_is_iso_zero
- \+ *lemma* category_theory.splitting.splittings_comm
- \+ *lemma* category_theory.splitting.ι_retraction
- \+ *lemma* category_theory.splitting.π_section_eq_id_sub
- \+ *structure* category_theory.splitting

Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.limits.iso_biprod_zero
- \+ *def* category_theory.limits.iso_zero_biprod

Modified src/category_theory/limits/shapes/zero_objects.lean




## [2022-05-17 13:06:20](https://github.com/leanprover-community/mathlib/commit/3d27911)
feat(data/zmod/quotient): The minimal period equals the cardinality of the orbit ([#14183](https://github.com/leanprover-community/mathlib/pull/14183))
This PR adds a lemma stating that `minimal_period ((•) a) b = card (orbit (zpowers a) b)`.
#### Estimated changes
Modified src/data/zmod/quotient.lean
- \+ *lemma* mul_action.minimal_period_eq_card
- \+/\- *lemma* mul_action.orbit_zpowers_equiv_symm_apply



## [2022-05-17 13:06:19](https://github.com/leanprover-community/mathlib/commit/3c87882)
feat(number_theory/arithmetic_function): map a multiplicative function across a product ([#14180](https://github.com/leanprover-community/mathlib/pull/14180))
#### Estimated changes
Modified src/data/nat/gcd.lean
- \+ *theorem* nat.coprime.symmetric

Modified src/number_theory/arithmetic_function.lean
- \+ *lemma* nat.arithmetic_function.is_multiplicative.map_prod



## [2022-05-17 13:06:18](https://github.com/leanprover-community/mathlib/commit/beee9ec)
feat(data/complex): real part of sum ([#14177](https://github.com/leanprover-community/mathlib/pull/14177))
#### Estimated changes
Modified src/data/complex/basic.lean
- \+ *lemma* complex.im_sum
- \+/\- *lemma* complex.of_real_prod
- \+/\- *lemma* complex.of_real_sum
- \+ *lemma* complex.re_sum



## [2022-05-17 13:06:17](https://github.com/leanprover-community/mathlib/commit/d3e3eb8)
chore(algebra/monoid_algebra): clean up some bad decidable arguments ([#14175](https://github.com/leanprover-community/mathlib/pull/14175))
Some of these statements contained classical decidable instances rather than generalized ones.
By removing `open_locale classical`, these become easy to find.
#### Estimated changes
Modified src/algebra/free_algebra.lean


Modified src/algebra/monoid_algebra/basic.lean
- \+/\- *lemma* add_monoid_algebra.mul_apply
- \+/\- *lemma* add_monoid_algebra.support_mul
- \+/\- *lemma* monoid_algebra.mul_apply
- \+/\- *lemma* monoid_algebra.support_mul

Modified src/data/polynomial/basic.lean




## [2022-05-17 13:06:16](https://github.com/leanprover-community/mathlib/commit/7db6ca9)
test({data/{finset,set},order/filter}/pointwise): Ensure priority of the `ℕ` and `ℤ` actions ([#14166](https://github.com/leanprover-community/mathlib/pull/14166))
Each of `set`, `finset`, `filter` creates (non propeq) diamonds with the fundamental `ℕ` and `ℤ` actions because of instances of the form `has_scalar α β → has_scalar α (set β)`. For example, `{2, 3}^2` could well be `{4, 9}` or `{4, 6, 9}`.
The instances involved are all too important to be discarded, so we decide to live with the diamonds but give priority to the `ℕ` and `ℤ` actions. The reasoning for the priority is that those can't easily be spelled out, while the derived actions can. For example, `s.image ((•) 2)` easily replaces `2 • s`. Incidentally, additive combinatorics uses extensively the `ℕ` action.
This PR adds both a library note and tests to ensure this stays the case. It also fixes the additive `set` and `filter` versions, which were not conforming to the test.
#### Estimated changes
Modified src/data/finset/pointwise.lean


Modified src/data/set/pointwise.lean


Modified src/order/filter/pointwise.lean


Added test/pointwise_nsmul.lean




## [2022-05-17 13:06:14](https://github.com/leanprover-community/mathlib/commit/f33b084)
feat(topology/separation): generalize a lemma ([#14154](https://github.com/leanprover-community/mathlib/pull/14154))
* generalize `nhds_eq_nhds_iff` from a `[t1_space α]` to a `[t0_space α]`;
* relate `indistinguishable` to `nhds`.
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* nhds_def'

Modified src/topology/separation.lean
- \+/\- *lemma* indistinguishable.eq
- \+/\- *lemma* indistinguishable_iff_closed
- \+/\- *lemma* indistinguishable_iff_closure
- \+ *lemma* indistinguishable_iff_nhds_eq
- \+/\- *lemma* nhds_eq_nhds_iff



## [2022-05-17 13:06:13](https://github.com/leanprover-community/mathlib/commit/65bf134)
split(algebra/hom/ring): Split off `algebra.ring.basic` ([#14144](https://github.com/leanprover-community/mathlib/pull/14144))
Move `non_unital_ring_hom` and `ring_hom` to a new file `algebra.hom.ring`.
Crediting
* Amelia for [#1305](https://github.com/leanprover-community/mathlib/pull/1305)
* Jireh for [#13430](https://github.com/leanprover-community/mathlib/pull/13430)
#### Estimated changes
Modified src/algebra/field/basic.lean


Modified src/algebra/group_power/basic.lean


Added src/algebra/hom/ring.lean
- \+ *lemma* add_monoid_hom.coe_add_monoid_hom_mk_ring_hom_of_mul_self_of_two_ne_zero
- \+ *lemma* add_monoid_hom.coe_fn_mk_ring_hom_of_mul_self_of_two_ne_zero
- \+ *def* add_monoid_hom.mk_ring_hom_of_mul_self_of_two_ne_zero
- \+ *lemma* map_bit1
- \+ *lemma* non_unital_ring_hom.cancel_left
- \+ *lemma* non_unital_ring_hom.cancel_right
- \+ *lemma* non_unital_ring_hom.coe_add_monoid_hom_id
- \+ *lemma* non_unital_ring_hom.coe_add_monoid_hom_injective
- \+ *lemma* non_unital_ring_hom.coe_add_monoid_hom_mk
- \+ *lemma* non_unital_ring_hom.coe_coe
- \+ *lemma* non_unital_ring_hom.coe_comp
- \+ *lemma* non_unital_ring_hom.coe_comp_add_monoid_hom
- \+ *lemma* non_unital_ring_hom.coe_comp_mul_hom
- \+ *lemma* non_unital_ring_hom.coe_mk
- \+ *lemma* non_unital_ring_hom.coe_mul
- \+ *lemma* non_unital_ring_hom.coe_mul_hom_id
- \+ *lemma* non_unital_ring_hom.coe_mul_hom_injective
- \+ *lemma* non_unital_ring_hom.coe_mul_hom_mk
- \+ *lemma* non_unital_ring_hom.coe_one
- \+ *lemma* non_unital_ring_hom.coe_to_add_monoid_hom
- \+ *lemma* non_unital_ring_hom.coe_to_mul_hom
- \+ *lemma* non_unital_ring_hom.coe_zero
- \+ *def* non_unital_ring_hom.comp
- \+ *lemma* non_unital_ring_hom.comp_apply
- \+ *lemma* non_unital_ring_hom.comp_assoc
- \+ *lemma* non_unital_ring_hom.comp_id
- \+ *lemma* non_unital_ring_hom.comp_zero
- \+ *lemma* non_unital_ring_hom.ext
- \+ *lemma* non_unital_ring_hom.ext_iff
- \+ *lemma* non_unital_ring_hom.id_apply
- \+ *lemma* non_unital_ring_hom.id_comp
- \+ *lemma* non_unital_ring_hom.mk_coe
- \+ *lemma* non_unital_ring_hom.mul_def
- \+ *lemma* non_unital_ring_hom.one_def
- \+ *lemma* non_unital_ring_hom.to_fun_eq_coe
- \+ *lemma* non_unital_ring_hom.zero_apply
- \+ *lemma* non_unital_ring_hom.zero_comp
- \+ *structure* non_unital_ring_hom
- \+ *lemma* ring_hom.cancel_left
- \+ *lemma* ring_hom.cancel_right
- \+ *lemma* ring_hom.codomain_trivial_iff_map_one_eq_zero
- \+ *lemma* ring_hom.codomain_trivial_iff_range_eq_singleton_zero
- \+ *lemma* ring_hom.codomain_trivial_iff_range_trivial
- \+ *lemma* ring_hom.coe_add_monoid_hom
- \+ *lemma* ring_hom.coe_add_monoid_hom_id
- \+ *lemma* ring_hom.coe_add_monoid_hom_injective
- \+ *lemma* ring_hom.coe_add_monoid_hom_mk
- \+ *lemma* ring_hom.coe_coe
- \+ *lemma* ring_hom.coe_comp
- \+ *lemma* ring_hom.coe_inj
- \+ *lemma* ring_hom.coe_mk
- \+ *lemma* ring_hom.coe_monoid_hom
- \+ *lemma* ring_hom.coe_monoid_hom_id
- \+ *lemma* ring_hom.coe_monoid_hom_injective
- \+ *lemma* ring_hom.coe_monoid_hom_mk
- \+ *lemma* ring_hom.coe_mul
- \+ *lemma* ring_hom.coe_one
- \+ *def* ring_hom.comp
- \+ *lemma* ring_hom.comp_apply
- \+ *lemma* ring_hom.comp_assoc
- \+ *lemma* ring_hom.comp_id
- \+ *lemma* ring_hom.congr_arg
- \+ *lemma* ring_hom.congr_fun
- \+ *def* ring_hom.copy
- \+ *lemma* ring_hom.domain_nontrivial
- \+ *lemma* ring_hom.ext
- \+ *lemma* ring_hom.ext_iff
- \+ *def* ring_hom.id
- \+ *lemma* ring_hom.id_apply
- \+ *lemma* ring_hom.id_comp
- \+ *lemma* ring_hom.is_unit_map
- \+ *lemma* ring_hom.map_one_ne_zero
- \+ *def* ring_hom.mk'
- \+ *lemma* ring_hom.mk_coe
- \+ *lemma* ring_hom.mul_def
- \+ *lemma* ring_hom.one_def
- \+ *lemma* ring_hom.to_add_monoid_hom_eq_coe
- \+ *lemma* ring_hom.to_fun_eq_coe
- \+ *lemma* ring_hom.to_monoid_hom_eq_coe
- \+ *lemma* ring_hom.to_monoid_with_zero_hom_eq_coe
- \+ *structure* ring_hom

Modified src/algebra/ring/basic.lean
- \- *lemma* add_monoid_hom.coe_add_monoid_hom_mk_ring_hom_of_mul_self_of_two_ne_zero
- \- *lemma* add_monoid_hom.coe_fn_mk_ring_hom_of_mul_self_of_two_ne_zero
- \- *def* add_monoid_hom.mk_ring_hom_of_mul_self_of_two_ne_zero
- \- *lemma* map_bit1
- \- *lemma* non_unital_ring_hom.cancel_left
- \- *lemma* non_unital_ring_hom.cancel_right
- \- *lemma* non_unital_ring_hom.coe_add_monoid_hom_id
- \- *theorem* non_unital_ring_hom.coe_add_monoid_hom_injective
- \- *lemma* non_unital_ring_hom.coe_add_monoid_hom_mk
- \- *lemma* non_unital_ring_hom.coe_coe
- \- *lemma* non_unital_ring_hom.coe_comp
- \- *lemma* non_unital_ring_hom.coe_comp_add_monoid_hom
- \- *lemma* non_unital_ring_hom.coe_comp_mul_hom
- \- *lemma* non_unital_ring_hom.coe_mk
- \- *lemma* non_unital_ring_hom.coe_mul
- \- *lemma* non_unital_ring_hom.coe_mul_hom_id
- \- *theorem* non_unital_ring_hom.coe_mul_hom_injective
- \- *lemma* non_unital_ring_hom.coe_mul_hom_mk
- \- *lemma* non_unital_ring_hom.coe_one
- \- *lemma* non_unital_ring_hom.coe_to_add_monoid_hom
- \- *lemma* non_unital_ring_hom.coe_to_mul_hom
- \- *lemma* non_unital_ring_hom.coe_zero
- \- *def* non_unital_ring_hom.comp
- \- *lemma* non_unital_ring_hom.comp_apply
- \- *lemma* non_unital_ring_hom.comp_assoc
- \- *lemma* non_unital_ring_hom.comp_id
- \- *lemma* non_unital_ring_hom.comp_zero
- \- *theorem* non_unital_ring_hom.ext
- \- *theorem* non_unital_ring_hom.ext_iff
- \- *lemma* non_unital_ring_hom.id_apply
- \- *lemma* non_unital_ring_hom.id_comp
- \- *lemma* non_unital_ring_hom.mk_coe
- \- *lemma* non_unital_ring_hom.mul_def
- \- *lemma* non_unital_ring_hom.one_def
- \- *lemma* non_unital_ring_hom.to_fun_eq_coe
- \- *lemma* non_unital_ring_hom.zero_apply
- \- *lemma* non_unital_ring_hom.zero_comp
- \- *structure* non_unital_ring_hom
- \- *lemma* ring_hom.cancel_left
- \- *lemma* ring_hom.cancel_right
- \- *lemma* ring_hom.codomain_trivial_iff_map_one_eq_zero
- \- *lemma* ring_hom.codomain_trivial_iff_range_eq_singleton_zero
- \- *lemma* ring_hom.codomain_trivial_iff_range_trivial
- \- *lemma* ring_hom.coe_add_monoid_hom
- \- *lemma* ring_hom.coe_add_monoid_hom_id
- \- *theorem* ring_hom.coe_add_monoid_hom_injective
- \- *lemma* ring_hom.coe_add_monoid_hom_mk
- \- *lemma* ring_hom.coe_coe
- \- *lemma* ring_hom.coe_comp
- \- *theorem* ring_hom.coe_inj
- \- *lemma* ring_hom.coe_mk
- \- *lemma* ring_hom.coe_monoid_hom
- \- *lemma* ring_hom.coe_monoid_hom_id
- \- *theorem* ring_hom.coe_monoid_hom_injective
- \- *lemma* ring_hom.coe_monoid_hom_mk
- \- *lemma* ring_hom.coe_mul
- \- *lemma* ring_hom.coe_one
- \- *def* ring_hom.comp
- \- *lemma* ring_hom.comp_apply
- \- *lemma* ring_hom.comp_assoc
- \- *lemma* ring_hom.comp_id
- \- *theorem* ring_hom.congr_arg
- \- *theorem* ring_hom.congr_fun
- \- *def* ring_hom.copy
- \- *lemma* ring_hom.domain_nontrivial
- \- *theorem* ring_hom.ext
- \- *theorem* ring_hom.ext_iff
- \- *def* ring_hom.id
- \- *lemma* ring_hom.id_apply
- \- *lemma* ring_hom.id_comp
- \- *lemma* ring_hom.is_unit_map
- \- *lemma* ring_hom.map_dvd
- \- *lemma* ring_hom.map_one_ne_zero
- \- *def* ring_hom.mk'
- \- *lemma* ring_hom.mk_coe
- \- *lemma* ring_hom.mul_def
- \- *lemma* ring_hom.one_def
- \- *lemma* ring_hom.to_add_monoid_hom_eq_coe
- \- *lemma* ring_hom.to_fun_eq_coe
- \- *lemma* ring_hom.to_monoid_hom_eq_coe
- \- *lemma* ring_hom.to_monoid_with_zero_hom_eq_coe
- \- *structure* ring_hom
- \+/\- *theorem* two_dvd_bit0

Modified src/algebra/ring/opposite.lean


Modified src/algebra/ring/pi.lean


Modified src/data/nat/cast.lean


Modified src/deprecated/group.lean




## [2022-05-17 13:06:12](https://github.com/leanprover-community/mathlib/commit/4ae5e7a)
feat(data/polynomial/laurent): laurent polynomials are a module over polynomials ([#14121](https://github.com/leanprover-community/mathlib/pull/14121))
This PR only introduces the instance `module R[X] R[T;T⁻¹]`.
I isolated it from the rest, since I want to give special attention to whether there might be any issues declaring it a global instance and whether it should be localized or even simply a def.  Edit: Eric seems happy with this instance!
#### Estimated changes
Modified src/data/polynomial/laurent.lean




## [2022-05-17 13:06:11](https://github.com/leanprover-community/mathlib/commit/46c42cc)
refactor(algebra/geom_sum): remove definition ([#14120](https://github.com/leanprover-community/mathlib/pull/14120))
There's no need to have a separate definition `geom_sum := ∑ i in range n, x ^ i`. Instead it's better to just write the lemmas about the sum itself: that way `simp` lemmas fire "in the wild", without needing to rewrite expression in terms of `geom_sum` manually.
#### Estimated changes
Modified archive/100-theorems-list/70_perfect_numbers.lean


Modified docs/100.yaml


Modified src/algebra/geom_sum.lean
- \- *def* geom_sum
- \- *theorem* geom_sum_def
- \+/\- *theorem* geom_sum_one
- \+/\- *lemma* geom_sum_pos
- \+/\- *lemma* geom_sum_succ'
- \+/\- *lemma* geom_sum_succ
- \+/\- *lemma* geom_sum_two
- \+/\- *theorem* geom_sum_zero
- \- *def* geom_sum₂
- \- *theorem* geom_sum₂_def
- \- *theorem* geom_sum₂_one
- \+/\- *theorem* geom_sum₂_with_one
- \- *theorem* geom_sum₂_zero
- \+/\- *lemma* neg_one_geom_sum
- \+/\- *lemma* one_geom_sum
- \+/\- *lemma* zero_geom_sum

Modified src/analysis/normed_space/units.lean


Modified src/analysis/special_functions/log/deriv.lean


Modified src/analysis/specific_limits/basic.lean


Modified src/analysis/specific_limits/normed.lean


Modified src/combinatorics/colex.lean


Modified src/data/complex/exponential.lean


Modified src/data/polynomial/eval.lean
- \+/\- *lemma* polynomial.eval_geom_sum

Modified src/data/real/pi/leibniz.lean


Modified src/linear_algebra/adic_completion.lean


Modified src/number_theory/bernoulli.lean


Modified src/ring_theory/integral_domain.lean


Modified src/ring_theory/polynomial/basic.lean


Modified src/ring_theory/polynomial/cyclotomic/basic.lean


Modified src/ring_theory/polynomial/cyclotomic/eval.lean


Modified src/ring_theory/polynomial/eisenstein.lean




## [2022-05-17 11:00:13](https://github.com/leanprover-community/mathlib/commit/2370d10)
chore(algebra/order/monoid): golf an instance ([#14184](https://github.com/leanprover-community/mathlib/pull/14184))
Move two instances below to reuse a proof.
#### Estimated changes
Modified src/algebra/order/monoid.lean




## [2022-05-17 03:48:46](https://github.com/leanprover-community/mathlib/commit/f1c08cd)
chore(scripts): update nolints.txt ([#14185](https://github.com/leanprover-community/mathlib/pull/14185))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-05-17 00:02:01](https://github.com/leanprover-community/mathlib/commit/737784e)
refactor(algebra/{group_power/{basic,lemmas},group_with_zero/power}): Generalize lemmas to division monoids ([#14102](https://github.com/leanprover-community/mathlib/pull/14102))
Generalize `group` and `group_with_zero` lemmas about `zpow` to `division_monoid`. Lemmas are renamed because one of the `group` or `group_with_zero` name has to go. It's just a matter of removing the suffixed `₀`.
Lemma renames
#### Estimated changes
Modified src/algebra/big_operators/multiset.lean


Modified src/algebra/field_power.lean
- \- *lemma* zpow_bit0_neg

Modified src/algebra/group/basic.lean
- \+ *lemma* bit0_neg

Modified src/algebra/group_power/basic.lean
- \- *theorem* commute.mul_zpow
- \+ *lemma* div_pow
- \+ *lemma* div_zpow
- \- *theorem* div_zpow
- \+ *lemma* inv_pow
- \- *theorem* inv_pow
- \+ *lemma* inv_pow_sub
- \- *theorem* inv_pow_sub
- \+ *lemma* inv_zpow'
- \+ *lemma* inv_zpow
- \- *theorem* inv_zpow
- \+ *lemma* mul_zpow
- \- *theorem* mul_zpow
- \+/\- *lemma* mul_zpow_neg_one
- \+ *lemma* one_div_pow
- \+ *lemma* one_div_zpow
- \+ *lemma* one_zpow
- \- *theorem* one_zpow
- \+ *lemma* pow_inv_comm
- \- *theorem* pow_inv_comm
- \+ *lemma* pow_sub
- \- *theorem* pow_sub
- \+/\- *def* zpow_group_hom
- \+ *lemma* zpow_neg
- \- *theorem* zpow_neg

Modified src/algebra/group_power/lemmas.lean
- \+ *lemma* zpow_bit0'
- \+ *lemma* zpow_bit0
- \- *theorem* zpow_bit0
- \+ *lemma* zpow_bit0_neg
- \+ *lemma* zpow_mul'
- \- *theorem* zpow_mul'
- \+ *lemma* zpow_mul
- \- *theorem* zpow_mul
- \+ *lemma* zpow_mul_comm
- \- *theorem* zpow_mul_comm

Modified src/algebra/group_with_zero/power.lean
- \- *lemma* commute.mul_zpow₀
- \- *theorem* div_pow
- \- *theorem* div_zpow₀
- \- *theorem* inv_pow₀
- \- *lemma* inv_zpow'
- \- *theorem* inv_zpow₀
- \- *lemma* mul_zpow_neg_one₀
- \- *lemma* mul_zpow₀
- \- *theorem* one_div_pow
- \- *theorem* one_div_zpow
- \- *theorem* one_zpow₀
- \- *theorem* zpow_bit0'
- \- *theorem* zpow_bit0₀
- \- *def* zpow_group_hom₀
- \- *theorem* zpow_mul₀'
- \- *theorem* zpow_mul₀
- \- *lemma* zpow_neg_one₀
- \- *theorem* zpow_neg₀

Modified src/algebra/order/archimedean.lean


Modified src/algebra/parity.lean
- \+/\- *lemma* even.neg_one_zpow
- \+/\- *lemma* odd.neg_one_zpow

Modified src/analysis/analytic/basic.lean


Modified src/analysis/asymptotics/superpolynomial_decay.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/complex/liouville.lean


Modified src/analysis/fourier.lean


Modified src/analysis/hofer.lean


Modified src/analysis/normed_space/exponential.lean


Modified src/analysis/normed_space/multilinear.lean


Modified src/analysis/p_series.lean


Modified src/analysis/special_functions/exp.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/specific_limits/floor_pow.lean


Modified src/analysis/specific_limits/normed.lean


Modified src/data/complex/exponential.lean


Modified src/data/real/ennreal.lean


Modified src/field_theory/perfect_closure.lean


Modified src/measure_theory/integral/circle_integral.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/number_theory/liouville/liouville_constant.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/number_theory/padics/padic_numbers.lean


Modified src/probability/variance.lean


Modified src/ring_theory/polynomial/dickson.lean


Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/witt_vector/defs.lean


Modified src/ring_theory/witt_vector/frobenius.lean


Modified src/topology/algebra/order/basic.lean


Modified src/topology/metric_space/pi_nat.lean




## [2022-05-16 16:38:19](https://github.com/leanprover-community/mathlib/commit/89f2760)
feat(number_theory/legendre_symbol/*): move characters on `zmod n` to new file, add API, improve a proof ([#14178](https://github.com/leanprover-community/mathlib/pull/14178))
This is another "administrative" PR with the goal to have a better file structure.
It moves the section `quad_char_mod_p` from `quadratic_char.lean` to a new file `zmod_char.lean`.
It also adds some API lemmas for `χ₈` and `χ₈'` (which will be useful when dealing with the value of quadratic characters at 2 and -2), and I have used the opportunity to shorten the proof of `χ₄_eq_neg_one_pow`.
#### Estimated changes
Modified src/number_theory/legendre_symbol/quadratic_char.lean
- \- *def* zmod.χ₄
- \- *lemma* zmod.χ₄_eq_neg_one_pow
- \- *lemma* zmod.χ₄_int_eq_if_mod_four
- \- *lemma* zmod.χ₄_nat_eq_if_mod_four
- \- *def* zmod.χ₈'
- \- *def* zmod.χ₈

Added src/number_theory/legendre_symbol/zmod_char.lean
- \+ *def* zmod.χ₄
- \+ *lemma* zmod.χ₄_eq_neg_one_pow
- \+ *lemma* zmod.χ₄_int_eq_if_mod_four
- \+ *lemma* zmod.χ₄_nat_eq_if_mod_four
- \+ *lemma* zmod.χ₄_trichotomy
- \+ *def* zmod.χ₈'
- \+ *lemma* zmod.χ₈'_eq_χ₄_mul_χ₈
- \+ *lemma* zmod.χ₈'_int_eq_if_mod_eight
- \+ *lemma* zmod.χ₈'_int_eq_χ₄_mul_χ₈
- \+ *lemma* zmod.χ₈'_nat_eq_if_mod_eight
- \+ *lemma* zmod.χ₈'_trichotomy
- \+ *def* zmod.χ₈
- \+ *lemma* zmod.χ₈_int_eq_if_mod_eight
- \+ *lemma* zmod.χ₈_nat_eq_if_mod_eight
- \+ *lemma* zmod.χ₈_trichotomy



## [2022-05-16 15:52:19](https://github.com/leanprover-community/mathlib/commit/93dca41)
chore(geometry/manifold/algebra/left_invariant_derivation): golf some proofs ([#14172](https://github.com/leanprover-community/mathlib/pull/14172))
The `simp only` had a bunch of lemmas that weren't used.
#### Estimated changes
Modified src/geometry/manifold/algebra/left_invariant_derivation.lean




## [2022-05-16 13:42:53](https://github.com/leanprover-community/mathlib/commit/4586a97)
refactor(data/pi/lex): Use `lex`, provide notation ([#14164](https://github.com/leanprover-community/mathlib/pull/14164))
Delete `pilex ι β` in favor of `lex (Π i, β i)` which we provide `Πₗ i, β i` notation for.
#### Estimated changes
Modified src/combinatorics/colex.lean


Modified src/data/list/lex.lean


Modified src/data/pi/lex.lean
- \+ *lemma* pi.lex.le_of_forall_le
- \- *def* pi.lex
- \+ *lemma* pi.of_lex_apply
- \+ *lemma* pi.to_lex_apply
- \- *lemma* pilex.le_of_forall_le
- \- *def* pilex

Modified src/data/prod/lex.lean


Modified src/data/psigma/order.lean


Modified src/data/sigma/order.lean




## [2022-05-16 13:42:52](https://github.com/leanprover-community/mathlib/commit/009669c)
feat(data/bool/basic): Kaminski's equation ([#14159](https://github.com/leanprover-community/mathlib/pull/14159))
`bool.apply_apply_apply : ∀ (f : bool → bool) (x : bool), f (f (f x)) = f x`
#### Estimated changes
Modified src/data/bool/basic.lean
- \+ *theorem* bool.apply_apply_apply



## [2022-05-16 13:42:51](https://github.com/leanprover-community/mathlib/commit/909b673)
split(data/set/semiring): Split off `data.set.pointwise` ([#14145](https://github.com/leanprover-community/mathlib/pull/14145))
Move `set_semiring` to a new file `data.set.semiring`.
Crediting Floris for [#3240](https://github.com/leanprover-community/mathlib/pull/3240)
#### Estimated changes
Modified src/algebra/algebra/operations.lean


Modified src/data/set/pointwise.lean
- \- *lemma* set.down_ssubset_down
- \- *lemma* set.down_subset_down
- \- *def* set.image_hom
- \- *lemma* set.up_le_up
- \- *lemma* set.up_lt_up

Added src/data/set/semiring.lean
- \+ *lemma* set_semiring.down_ssubset_down
- \+ *lemma* set_semiring.down_subset_down
- \+ *def* set_semiring.image_hom
- \+ *lemma* set_semiring.up_le_up
- \+ *lemma* set_semiring.up_lt_up



## [2022-05-16 13:42:49](https://github.com/leanprover-community/mathlib/commit/a9e74ab)
feat(order/filter/at_top_bot): use weaker TC assumptions, add lemmas ([#14105](https://github.com/leanprover-community/mathlib/pull/14105))
* add `filter.eventually_gt_of_tendsto_at_top`,
  `filter.eventually_ne_at_bot`,
  `filter.eventually_lt_of_tendsto_at_bot`;
* generalize `filter.eventually_ne_of_tendsto_at_top` and
  `filter.eventually_ne_of_tendsto_at_bot` from nontrivial ordered
  (semi)rings to preorders with no maximal/minimal elements.
#### Estimated changes
Modified src/analysis/asymptotics/superpolynomial_decay.lean


Modified src/analysis/normed/group/basic.lean


Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.eventually_ne_at_bot
- \- *lemma* filter.eventually_ne_of_tendsto_at_bot
- \- *lemma* filter.eventually_ne_of_tendsto_at_top
- \+ *lemma* filter.tendsto.eventually_ge_at_top
- \+ *lemma* filter.tendsto.eventually_gt_at_top
- \+ *lemma* filter.tendsto.eventually_le_at_bot
- \+ *lemma* filter.tendsto.eventually_lt_at_bot
- \+ *lemma* filter.tendsto.eventually_ne_at_bot
- \+ *lemma* filter.tendsto.eventually_ne_at_top



## [2022-05-16 11:34:45](https://github.com/leanprover-community/mathlib/commit/844a4f7)
refactor(algebra/hom/group): Generalize `map_inv` to division monoids ([#14134](https://github.com/leanprover-community/mathlib/pull/14134))
A minor change with unexpected instance synthesis breakage. A good deal of dot notation on `monoid_hom.map_inv` breaks, along with a few uses of `map_inv`. Expliciting the type fixes them all, but this is still quite concerning.
#### Estimated changes
Modified src/algebra/group/ext.lean


Modified src/algebra/hom/equiv.lean
- \- *lemma* units.coe_inv

Modified src/algebra/hom/group.lean
- \+ *lemma* map_div'
- \- *theorem* map_div'
- \+/\- *lemma* map_div
- \+ *lemma* map_inv
- \- *theorem* map_inv
- \+ *lemma* map_mul_inv
- \- *theorem* map_mul_inv
- \+/\- *theorem* map_zpow
- \+/\- *theorem* map_zsmul

Modified src/algebra/hom/units.lean
- \+ *lemma* units.coe_inv
- \+/\- *lemma* units.coe_zpow

Modified src/analysis/normed/group/hom_completion.lean


Modified src/category_theory/linear/linear_functor.lean


Modified src/category_theory/preadditive/additive_functor.lean


Modified src/category_theory/preadditive/functor_category.lean


Modified src/group_theory/free_abelian_group.lean


Modified src/group_theory/free_group.lean




## [2022-05-16 11:34:44](https://github.com/leanprover-community/mathlib/commit/90659cb)
fix(tactic/core): Make the `classical` tactic behave like `open_locale classical` ([#14122](https://github.com/leanprover-community/mathlib/pull/14122))
This renames the existing `classical` tactic to `classical!`, and adds a new `classical` tactic that is equivalent to `open_locale classical`.
Comparing the effects of these:
```lean
import tactic.interactive
import tactic.localized
-- this uses the noncomputable instance
noncomputable def foo : decidable_eq ℕ :=
λ m n, begin classical!, apply_instance, end
def bar : decidable_eq ℕ :=
λ m n, begin classical, apply_instance, end
section
open_locale classical
def baz : decidable_eq ℕ :=
λ m n, by apply_instance
end
example : baz = bar := rfl
```
In a few places `classical` was actually just being used as a `resetI`. Only a very small number of uses of `classical` actually needed the more aggressive `classical!` (there are roughtly 500 uses in total); while a number of `congr`s can be eliminated with this change.
#### Estimated changes
Modified src/analysis/inner_product_space/pi_L2.lean


Modified src/analysis/normed_space/add_torsor_bases.lean


Modified src/category_theory/category/PartialFun.lean


Modified src/combinatorics/hall/basic.lean


Modified src/combinatorics/simple_graph/degree_sum.lean


Modified src/combinatorics/simple_graph/inc_matrix.lean


Modified src/data/fintype/basic.lean


Modified src/data/set/pointwise.lean


Modified src/field_theory/finite/basic.lean


Modified src/group_theory/free_product.lean


Modified src/group_theory/order_of_element.lean


Modified src/ring_theory/discriminant.lean


Modified src/ring_theory/local_properties.lean


Modified src/ring_theory/polynomial/vieta.lean


Modified src/tactic/core.lean


Modified src/tactic/interactive.lean


Modified src/tactic/tauto.lean




## [2022-05-16 09:19:06](https://github.com/leanprover-community/mathlib/commit/df64e5e)
chore(set_theory/game/pgame): minor golf ([#14171](https://github.com/leanprover-community/mathlib/pull/14171))
#### Estimated changes
Modified src/set_theory/game/pgame.lean




## [2022-05-16 09:19:05](https://github.com/leanprover-community/mathlib/commit/f4c67ee)
chore(group_theory/specific_groups/cyclic): golf `card_order_of_eq_totient_aux₁` and `card_order_of_eq_totient_aux₂` ([#14161](https://github.com/leanprover-community/mathlib/pull/14161))
Re-writing the proofs of `card_order_of_eq_totient_aux₁` and `card_order_of_eq_totient_aux₂` to use the new `sum_totient` introduced in [#14007](https://github.com/leanprover-community/mathlib/pull/14007), and golfing them.
#### Estimated changes
Modified src/group_theory/specific_groups/cyclic.lean




## [2022-05-16 09:19:04](https://github.com/leanprover-community/mathlib/commit/a5975e7)
feat(data/int/basic): add theorem `int.div_mod_unique` ([#14158](https://github.com/leanprover-community/mathlib/pull/14158))
add the `int` version of `div_mod_unique`.
#### Estimated changes
Modified src/data/int/basic.lean




## [2022-05-16 09:19:03](https://github.com/leanprover-community/mathlib/commit/f7a7c27)
chore(ring_theory/ideal/local_ring): golf some proofs, add missing lemma ([#14157](https://github.com/leanprover-community/mathlib/pull/14157))
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* units.eq_iff_inv_mul
- \+/\- *lemma* units.inv_eq_of_mul_eq_one_right

Modified src/ring_theory/ideal/local_ring.lean




## [2022-05-16 09:19:01](https://github.com/leanprover-community/mathlib/commit/55b31e0)
feat(data/zmod/quotient): `orbit (zpowers a) b` is a cycle of order `minimal_period ((•) a) b` ([#14124](https://github.com/leanprover-community/mathlib/pull/14124))
This PR applies the orbit-stabilizer theorem to the action of a cyclic subgroup.
#### Estimated changes
Modified src/data/zmod/quotient.lean
- \+ *lemma* mul_action.orbit_zpowers_equiv_symm_apply



## [2022-05-16 09:19:00](https://github.com/leanprover-community/mathlib/commit/bc7a201)
feat(*): Pointwise monoids have distributive negations ([#14114](https://github.com/leanprover-community/mathlib/pull/14114))
More instances of `has_distrib_neg`:
* `function.injective.has_distrib_neg`, `function.surjective.has_distrib_neg`
* `add_opposite`, `mul_opposite`
* `set`, `finset`, `filter`
#### Estimated changes
Modified src/algebra/ring/basic.lean


Modified src/algebra/star/unitary.lean


Modified src/data/finset/n_ary.lean
- \+ *lemma* finset.image₂_distrib_subset_left
- \+ *lemma* finset.image₂_distrib_subset_right

Modified src/data/finset/pointwise.lean
- \+ *lemma* finset.add_mul_subset
- \+ *lemma* finset.mul_add_subset

Modified src/data/set/basic.lean
- \+ *lemma* set.image2_distrib_subset_left
- \+ *lemma* set.image2_distrib_subset_right

Modified src/data/set/pointwise.lean
- \+ *lemma* set.add_mul_subset
- \+ *lemma* set.mul_add_subset

Modified src/linear_algebra/general_linear_group.lean
- \+/\- *lemma* matrix.GL_pos.coe_neg
- \+ *lemma* matrix.GL_pos.coe_neg_GL

Modified src/linear_algebra/special_linear_group.lean
- \+/\- *lemma* matrix.special_linear_group.coe_int_neg
- \+/\- *lemma* matrix.special_linear_group.coe_neg

Modified src/order/filter/n_ary.lean
- \+ *lemma* filter.map₂_distrib_le_left
- \+ *lemma* filter.map₂_distrib_le_right

Modified src/order/filter/pointwise.lean
- \+ *lemma* filter.add_mul_subset
- \+ *lemma* filter.mul_add_subset



## [2022-05-16 09:18:59](https://github.com/leanprover-community/mathlib/commit/f0db51d)
feat(algebra/module): morphism classes for (semi)linear maps ([#13939](https://github.com/leanprover-community/mathlib/pull/13939))
This PR introduces morphism classes corresponding to `mul_action_hom`, `distrib_mul_action_hom`, `mul_semiring_action_hom` and `linear_map`.
Most of the new generic results work smoothly, only `simp` seems to have trouble applying `map_smulₛₗ`. I expect this requires another fix in the elaborator along the lines of [lean[#659](https://github.com/leanprover-community/mathlib/pull/659)](https://github.com/leanprover-community/lean/pull/659). For now we can just keep around the specialized `simp` lemmas `linear_map.map_smulₛₗ` and `linear_equiv.map_smulₛₗ`.
The other changes are either making `map_smul` protected where it conflicts, or helping the elaborator unfold some definitions that previously were helped by the specific `map_smul` lemma suggesting the type.
Thanks to @dupuisf for updating and making this branch compile!
Co-Authored-By: Frédéric Dupuis <dupuisf@iro.umontreal.ca>
#### Estimated changes
Modified src/algebra/category/Module/abelian.lean


Modified src/algebra/category/Module/basic.lean


Modified src/algebra/hom/group_action.lean
- \+/\- *theorem* distrib_mul_action_hom.ext
- \+/\- *theorem* distrib_mul_action_hom.ext_iff
- \- *lemma* distrib_mul_action_hom.map_add
- \- *lemma* distrib_mul_action_hom.map_neg
- \- *lemma* distrib_mul_action_hom.map_smul
- \- *lemma* distrib_mul_action_hom.map_sub
- \- *lemma* distrib_mul_action_hom.map_zero
- \+/\- *theorem* mul_action_hom.ext
- \+/\- *theorem* mul_action_hom.ext_iff
- \- *lemma* mul_action_hom.map_smul
- \+/\- *theorem* mul_semiring_action_hom.ext
- \+/\- *theorem* mul_semiring_action_hom.ext_iff
- \- *lemma* mul_semiring_action_hom.map_add
- \- *lemma* mul_semiring_action_hom.map_mul
- \- *lemma* mul_semiring_action_hom.map_neg
- \- *lemma* mul_semiring_action_hom.map_one
- \- *lemma* mul_semiring_action_hom.map_smul
- \- *lemma* mul_semiring_action_hom.map_sub
- \- *lemma* mul_semiring_action_hom.map_zero

Modified src/algebra/module/equiv.lean
- \- *theorem* linear_equiv.map_smulₛₗ

Modified src/algebra/module/linear_map.lean
- \- *lemma* linear_map.map_smul
- \- *lemma* linear_map.map_smul_inv
- \- *lemma* linear_map.map_smulₛₗ
- \+ *abbreviation* linear_map_class
- \+ *lemma* semilinear_map_class.map_smul_inv

Modified src/analysis/inner_product_space/dual.lean


Modified src/analysis/inner_product_space/l2_space.lean


Modified src/analysis/inner_product_space/lax_milgram.lean


Modified src/analysis/locally_convex/weak_dual.lean


Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/finite_dimension.lean


Modified src/linear_algebra/basic.lean


Modified src/linear_algebra/bilinear_map.lean


Modified src/linear_algebra/contraction.lean


Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/multilinear/basic.lean
- \- *lemma* multilinear_map.map_smul

Modified src/linear_algebra/pi_tensor_product.lean


Modified src/linear_algebra/trace.lean


Modified src/measure_theory/group/measure.lean


Modified src/measure_theory/measure/haar.lean


Modified src/measure_theory/measure/haar_lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \- *lemma* measure_theory.measure.map_smul



## [2022-05-16 08:42:11](https://github.com/leanprover-community/mathlib/commit/0d76285)
doc(set_theory/surreal/basic): update docs ([#14170](https://github.com/leanprover-community/mathlib/pull/14170))
We remove an incorrect remark about the order relations on `pgame`, and reference the branch on which the proof of surreal multiplication is being worked on.
#### Estimated changes
Modified src/set_theory/surreal/basic.lean




## [2022-05-15 19:05:27](https://github.com/leanprover-community/mathlib/commit/4cf2016)
feat(order/cover): Covering elements are unique ([#14156](https://github.com/leanprover-community/mathlib/pull/14156))
In a linear order, there's at most one element covering `a` and at most one element being covered by `a`.
#### Estimated changes
Modified src/order/cover.lean
- \+ *lemma* covby.ge_of_gt
- \+ *lemma* covby.le_of_lt
- \+ *lemma* covby.unique_left
- \+ *lemma* covby.unique_right
- \+ *lemma* wcovby.ge_of_gt
- \+ *lemma* wcovby.le_of_lt



## [2022-05-15 16:12:50](https://github.com/leanprover-community/mathlib/commit/00e80a6)
feat (group_theory/perm/cycles): Add missing `is_cycle` lemma ([#13219](https://github.com/leanprover-community/mathlib/pull/13219))
Add `is_cycle.pow_eq_pow_iff`, which extends `is_cycle.pow_eq_one_iff`.
#### Estimated changes
Modified src/group_theory/perm/cycles.lean
- \+/\- *lemma* equiv.perm.is_cycle.pow_eq_one_iff
- \+ *lemma* equiv.perm.is_cycle.pow_eq_pow_iff



## [2022-05-15 14:04:27](https://github.com/leanprover-community/mathlib/commit/c109105)
chore(logic/equiv): golf equiv.subtype_equiv ([#14125](https://github.com/leanprover-community/mathlib/pull/14125))
The naming is a bit all over the place, but I will fix this in a later PR.
#### Estimated changes
Modified src/logic/equiv/basic.lean




## [2022-05-15 14:04:26](https://github.com/leanprover-community/mathlib/commit/843240b)
feat(linear_algebra/matrix): invariant basis number for matrices ([#13845](https://github.com/leanprover-community/mathlib/pull/13845))
This PR shows that invertible matrices over a ring with invariant basis number are square.
#### Estimated changes
Modified src/linear_algebra/invariant_basis_number.lean


Added src/linear_algebra/matrix/invariant_basis_number.lean
- \+ *lemma* matrix.square_of_invertible

Modified src/linear_algebra/matrix/to_lin.lean




## [2022-05-15 14:04:26](https://github.com/leanprover-community/mathlib/commit/f9f64f3)
move(data/prod/*): A `prod` folder ([#13771](https://github.com/leanprover-community/mathlib/pull/13771))
Create folder `data.prod.` to hold `prod` files and related types. Precisely:
* `data.prod` → `data.prod.basic`
* `data.pprod` → `data.prod.pprod`
* `data.tprod` → `data.prod.tprod`
* `order.lexicographic` → `data.prod.lex`
#### Estimated changes
Modified src/algebra/order/rearrangement.lean


Modified src/combinatorics/colex.lean


Modified src/data/fin/tuple/sort.lean


Modified src/data/list/lex.lean


Modified src/data/pi/algebra.lean


Renamed src/data/prod.lean to src/data/prod/basic.lean


Renamed src/order/lexicographic.lean to src/data/prod/lex.lean


Renamed src/data/pprod.lean to src/data/prod/pprod.lean


Renamed src/data/tprod.lean to src/data/prod/tprod.lean


Modified src/data/psigma/order.lean


Modified src/data/sigma/lex.lean


Modified src/data/sigma/order.lean


Modified src/logic/embedding.lean


Modified src/logic/equiv/basic.lean


Modified src/logic/nontrivial.lean


Modified src/measure_theory/measurable_space.lean


Modified src/order/basic.lean


Modified src/order/filter/bases.lean


Modified src/tactic/core.lean


Modified src/tactic/linarith/preprocessing.lean




## [2022-05-15 11:58:06](https://github.com/leanprover-community/mathlib/commit/a74298d)
chore(order/lattice): reflow, golf ([#14151](https://github.com/leanprover-community/mathlib/pull/14151))
#### Estimated changes
Modified src/order/lattice.lean
- \+/\- *lemma* inf_le_inf_left
- \+/\- *lemma* inf_le_inf_right
- \+/\- *lemma* inf_left_comm
- \+/\- *lemma* inf_left_idem
- \+/\- *lemma* inf_left_right_swap
- \+/\- *lemma* inf_right_comm
- \+/\- *lemma* inf_right_idem
- \+/\- *theorem* le_of_inf_eq



## [2022-05-15 08:37:51](https://github.com/leanprover-community/mathlib/commit/5c954e1)
chore(order/conditionally_complete_lattice): General cleanup ([#13319](https://github.com/leanprover-community/mathlib/pull/13319))
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+/\- *theorem* cInf_eq_of_forall_ge_of_forall_gt_exists_lt
- \+/\- *theorem* cInf_le_cInf
- \+/\- *theorem* cInf_le_of_le
- \+/\- *lemma* cInf_lt_of_lt
- \+/\- *theorem* cSup_eq_of_forall_le_of_forall_lt_exists_gt
- \+/\- *theorem* cSup_eq_of_is_forall_le_of_forall_le_imp_ge
- \+/\- *theorem* cSup_inter_le
- \+/\- *theorem* cSup_le
- \+/\- *theorem* cSup_le_cSup
- \+/\- *theorem* cSup_le_iff
- \+/\- *theorem* csupr_const
- \+/\- *lemma* csupr_le
- \+/\- *lemma* exists_lt_of_cInf_lt
- \+/\- *lemma* exists_lt_of_cinfi_lt
- \+/\- *lemma* exists_lt_of_lt_cSup
- \+/\- *lemma* exists_lt_of_lt_csupr
- \+/\- *theorem* le_cInf
- \+/\- *theorem* le_cInf_iff
- \+/\- *theorem* le_cInf_inter
- \+/\- *theorem* le_cSup_of_le
- \+/\- *lemma* le_cinfi
- \+/\- *lemma* lt_cSup_of_lt
- \+/\- *lemma* with_top.coe_Inf
- \+/\- *lemma* with_top.coe_Sup



## [2022-05-15 01:31:14](https://github.com/leanprover-community/mathlib/commit/b8d8a5e)
refactor(set_theory/game/*): Fix bad notation `<` on (pre-)games ([#13963](https://github.com/leanprover-community/mathlib/pull/13963))
Our current definition for `<` on pre-games is, in the wider mathematical literature, referred to as `⧏` (less or fuzzy to). Conversely, what's usually referred to by `<` coincides with the relation we get from `preorder pgame` (which the current API avoids using at all).
We rename `<` to `⧏`, and add the basic API for both the new `<` and `⧏` relations. This allows us to define new instances on `pgame` and `game` that we couldn't before. We also take the opportunity to add some basic API on the fuzzy relation `∥`.
See the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers/near/281094687).
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \+ *theorem* game.add_lf_add_left
- \+ *theorem* game.add_lf_add_right
- \+ *def* game.fuzzy
- \- *theorem* game.le_antisymm
- \- *theorem* game.le_refl
- \- *theorem* game.le_rfl
- \- *theorem* game.le_trans
- \+ *def* game.lf
- \- *theorem* game.lt_or_eq_of_le
- \+/\- *theorem* game.not_le
- \+ *theorem* game.not_lf
- \- *theorem* game.not_lt
- \- *def* game.ordered_add_comm_group
- \- *def* game.partial_order

Modified src/set_theory/game/birthday.lean


Modified src/set_theory/game/impartial.lean
- \+/\- *lemma* pgame.impartial.first_wins_symm'
- \+/\- *lemma* pgame.impartial.first_wins_symm
- \+ *lemma* pgame.impartial.lf_zero_iff
- \- *lemma* pgame.impartial.lt_zero_iff
- \+ *lemma* pgame.impartial.nonneg
- \+ *lemma* pgame.impartial.nonpos

Modified src/set_theory/game/nim.lean


Modified src/set_theory/game/ordinal.lean
- \+ *theorem* ordinal.to_pgame_lf
- \+ *theorem* ordinal.to_pgame_lf_iff

Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.add_lf_add_left
- \+ *theorem* pgame.add_lf_add_right
- \+ *theorem* pgame.equiv.is_empty
- \+ *theorem* pgame.equiv.not_fuzzy'
- \+ *theorem* pgame.equiv.not_fuzzy
- \+/\- *theorem* pgame.equiv_rfl
- \+ *theorem* pgame.fuzzy.not_equiv'
- \+ *theorem* pgame.fuzzy.not_equiv
- \+ *theorem* pgame.fuzzy.swap
- \+ *theorem* pgame.fuzzy.swap_iff
- \+ *def* pgame.fuzzy
- \+ *theorem* pgame.fuzzy_congr
- \+ *theorem* pgame.fuzzy_congr_imp
- \+ *theorem* pgame.fuzzy_congr_left
- \+ *theorem* pgame.fuzzy_congr_right
- \+ *theorem* pgame.fuzzy_irrefl
- \+ *theorem* pgame.fuzzy_of_equiv_of_fuzzy
- \+ *theorem* pgame.fuzzy_of_fuzzy_of_equiv
- \+ *theorem* pgame.half_add_half_equiv_one
- \+/\- *theorem* pgame.le_congr
- \+ *theorem* pgame.le_congr_imp
- \+ *theorem* pgame.le_congr_left
- \+ *theorem* pgame.le_congr_right
- \+ *theorem* pgame.le_def_lf
- \- *theorem* pgame.le_def_lt
- \- *theorem* pgame.le_iff_neg_ge
- \+ *def* pgame.le_lf
- \- *def* pgame.le_lt
- \+/\- *theorem* pgame.le_of_equiv_of_le
- \+/\- *theorem* pgame.le_of_le_of_equiv
- \+ *theorem* pgame.le_or_gf
- \- *theorem* pgame.le_trans
- \- *theorem* pgame.le_trans_aux
- \+/\- *theorem* pgame.le_zero
- \- *theorem* pgame.le_zero_iff_zero_le_neg
- \+ *theorem* pgame.le_zero_lf
- \+ *def* pgame.lf
- \+ *theorem* pgame.lf_congr
- \+ *theorem* pgame.lf_congr_imp
- \+ *theorem* pgame.lf_congr_left
- \+ *theorem* pgame.lf_congr_right
- \+ *theorem* pgame.lf_def
- \+ *theorem* pgame.lf_def_le
- \+ *theorem* pgame.lf_iff_lt_or_fuzzy
- \+ *theorem* pgame.lf_iff_sub_zero_lf
- \+ *theorem* pgame.lf_irrefl
- \+ *theorem* pgame.lf_mk
- \+ *theorem* pgame.lf_mk_of_le
- \+ *theorem* pgame.lf_move_right
- \+ *theorem* pgame.lf_move_right_of_le
- \+ *theorem* pgame.lf_of_equiv_of_lf
- \+ *theorem* pgame.lf_of_fuzzy
- \+ *theorem* pgame.lf_of_le_mk
- \+ *theorem* pgame.lf_of_le_move_left
- \+ *theorem* pgame.lf_of_le_of_lf
- \+ *theorem* pgame.lf_of_lf_of_equiv
- \+ *theorem* pgame.lf_of_lf_of_le
- \+ *theorem* pgame.lf_of_lf_of_lt
- \+ *theorem* pgame.lf_of_lt
- \+ *theorem* pgame.lf_of_lt_of_lf
- \+ *theorem* pgame.lf_of_mk_le
- \+ *theorem* pgame.lf_of_move_right_le
- \+ *theorem* pgame.lf_or_equiv_of_le
- \+ *theorem* pgame.lf_or_equiv_or_gf
- \+ *theorem* pgame.lf_zero
- \+ *theorem* pgame.lf_zero_le
- \+ *theorem* pgame.lt_congr_imp
- \+ *theorem* pgame.lt_congr_left
- \+ *theorem* pgame.lt_congr_right
- \- *theorem* pgame.lt_def
- \- *theorem* pgame.lt_def_le
- \+ *theorem* pgame.lt_iff_le_and_lf
- \- *theorem* pgame.lt_iff_neg_gt
- \- *theorem* pgame.lt_mk
- \- *theorem* pgame.lt_mk_of_le
- \- *theorem* pgame.lt_move_right
- \- *theorem* pgame.lt_move_right_of_le
- \+/\- *theorem* pgame.lt_of_equiv_of_lt
- \- *theorem* pgame.lt_of_le_mk
- \- *theorem* pgame.lt_of_le_move_left
- \+ *theorem* pgame.lt_of_le_of_lf
- \- *theorem* pgame.lt_of_le_of_lt
- \+/\- *theorem* pgame.lt_of_lt_of_equiv
- \- *theorem* pgame.lt_of_lt_of_le
- \- *theorem* pgame.lt_of_mk_le
- \- *theorem* pgame.lt_of_move_right_le
- \- *theorem* pgame.lt_or_equiv_of_le
- \- *theorem* pgame.lt_or_equiv_or_gt
- \+ *theorem* pgame.lt_or_equiv_or_gt_or_fuzzy
- \+ *theorem* pgame.lt_or_fuzzy_of_lf
- \- *theorem* pgame.lt_zero
- \+ *theorem* pgame.mk_lf
- \+ *theorem* pgame.mk_lf_mk
- \+ *theorem* pgame.mk_lf_of_le
- \- *theorem* pgame.mk_lt
- \- *theorem* pgame.mk_lt_mk
- \- *theorem* pgame.mk_lt_of_le
- \+ *theorem* pgame.move_left_lf
- \+ *theorem* pgame.move_left_lf_of_le
- \- *theorem* pgame.move_left_lt
- \- *theorem* pgame.move_left_lt_of_le
- \+ *theorem* pgame.neg_le_iff
- \+ *theorem* pgame.neg_le_zero_iff
- \+ *theorem* pgame.neg_lf_iff
- \+ *theorem* pgame.neg_lf_zero_iff
- \+ *theorem* pgame.neg_lt_iff
- \+ *theorem* pgame.neg_lt_zero_iff
- \+ *theorem* pgame.not_fuzzy_of_ge
- \+ *theorem* pgame.not_fuzzy_of_le
- \- *theorem* pgame.not_le
- \+ *theorem* pgame.not_lf
- \- *theorem* pgame.not_lt
- \+ *theorem* pgame.star_fuzzy_zero
- \- *theorem* pgame.star_lt_zero
- \+/\- *theorem* pgame.zero_le
- \- *theorem* pgame.zero_le_iff_neg_le_zero
- \+ *theorem* pgame.zero_le_lf
- \+ *theorem* pgame.zero_le_neg_iff
- \+/\- *theorem* pgame.zero_le_one
- \+ *theorem* pgame.zero_lf
- \+ *theorem* pgame.zero_lf_le
- \+ *theorem* pgame.zero_lf_neg_iff
- \+ *theorem* pgame.zero_lf_one
- \- *theorem* pgame.zero_lt
- \+ *theorem* pgame.zero_lt_neg_iff
- \- *theorem* pgame.zero_lt_star

Modified src/set_theory/game/short.lean
- \+ *def* pgame.le_lf_decidable
- \- *def* pgame.le_lt_decidable

Modified src/set_theory/game/winner.lean
- \+/\- *def* pgame.first_loses
- \+/\- *def* pgame.first_wins
- \+/\- *lemma* pgame.first_wins_of_equiv_iff
- \+/\- *def* pgame.left_wins
- \+/\- *lemma* pgame.left_wins_of_equiv_iff
- \+/\- *theorem* pgame.one_left_wins
- \+/\- *def* pgame.right_wins
- \+/\- *lemma* pgame.right_wins_of_equiv_iff
- \+/\- *theorem* pgame.star_first_wins
- \+/\- *lemma* pgame.winner_cases
- \+/\- *theorem* pgame.zero_first_loses

Modified src/set_theory/surreal/basic.lean
- \+ *theorem* pgame.add_lf_add
- \- *theorem* pgame.add_lt_add
- \- *theorem* pgame.half_add_half_equiv_one
- \+ *theorem* pgame.le_of_lf
- \- *theorem* pgame.le_of_lt
- \+ *theorem* pgame.lf_asymm
- \+ *theorem* pgame.lf_iff_lt
- \- *theorem* pgame.lt_asymm
- \- *theorem* pgame.lt_iff_le_not_le
- \+ *theorem* pgame.lt_of_lf
- \- *theorem* pgame.lt_trans'
- \- *theorem* pgame.lt_trans
- \+ *theorem* pgame.not_fuzzy
- \+/\- *theorem* pgame.numeric.le_move_right
- \+ *theorem* pgame.numeric.lt_move_right
- \+/\- *theorem* pgame.numeric.move_left_le
- \+ *theorem* pgame.numeric.move_left_lt

Modified src/set_theory/surreal/dyadic.lean




## [2022-05-14 23:44:35](https://github.com/leanprover-community/mathlib/commit/1f00800)
feat(linear_algebra/projection) : projections are conjugate to prod_map id 0 ([#13802](https://github.com/leanprover-community/mathlib/pull/13802))
#### Estimated changes
Modified src/linear_algebra/projection.lean
- \+ *def* linear_map.is_proj.cod_restrict
- \+ *lemma* linear_map.is_proj.cod_restrict_apply
- \+ *lemma* linear_map.is_proj.cod_restrict_apply_cod
- \+ *lemma* linear_map.is_proj.cod_restrict_ker
- \+ *lemma* linear_map.is_proj.eq_conj_prod_map'
- \+ *lemma* linear_map.is_proj.eq_conj_prod_map
- \+ *lemma* linear_map.is_proj.is_compl
- \+ *structure* linear_map.is_proj
- \+ *lemma* linear_map.is_proj_iff_idempotent



## [2022-05-14 22:46:42](https://github.com/leanprover-community/mathlib/commit/e738612)
feat(analysis/special_functions/exp_deriv): generalize some lemmas about `complex.exp`, remove `*.cexp_real` ([#13579](https://github.com/leanprover-community/mathlib/pull/13579))
Now we can use `*.cexp` instead of some previous `*.cexp_real` lemmas.
- [x] depends on: [#13575](https://github.com/leanprover-community/mathlib/pull/13575)
#### Estimated changes
Modified src/analysis/special_functions/exp_deriv.lean
- \+/\- *lemma* complex.cont_diff_exp
- \+/\- *lemma* complex.differentiable_at_exp
- \+/\- *lemma* complex.differentiable_exp
- \+/\- *lemma* cont_diff.cexp
- \+/\- *lemma* cont_diff_at.cexp
- \+/\- *lemma* cont_diff_on.cexp
- \+/\- *lemma* cont_diff_within_at.cexp
- \+/\- *lemma* deriv_cexp
- \+/\- *lemma* deriv_within_cexp
- \+/\- *lemma* differentiable.cexp
- \+/\- *lemma* differentiable_at.cexp
- \+/\- *lemma* differentiable_on.cexp
- \+/\- *lemma* differentiable_within_at.cexp
- \- *lemma* has_deriv_at.cexp_real
- \- *lemma* has_deriv_within_at.cexp_real
- \- *lemma* has_strict_deriv_at.cexp_real

Modified src/geometry/manifold/instances/sphere.lean


Modified src/measure_theory/integral/circle_integral.lean




## [2022-05-14 17:09:34](https://github.com/leanprover-community/mathlib/commit/570db88)
feat(category_theory): missing comp_ite lemma ([#14143](https://github.com/leanprover-community/mathlib/pull/14143))
We already have `comp_dite`.
#### Estimated changes
Modified src/category_theory/category/basic.lean
- \+ *lemma* category_theory.comp_ite
- \+ *lemma* category_theory.ite_comp



## [2022-05-14 17:09:33](https://github.com/leanprover-community/mathlib/commit/ad5edeb)
feat(algebra/big_operators): prod_ite_irrel ([#14142](https://github.com/leanprover-community/mathlib/pull/14142))
A few missing lemams in `big_operators/basic.lean`.
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+/\- *lemma* finset.prod_dite_irrel
- \+ *lemma* finset.prod_erase_eq_div
- \+ *lemma* finset.prod_ite_irrel
- \+ *lemma* finset.prod_sdiff_eq_div



## [2022-05-14 17:09:32](https://github.com/leanprover-community/mathlib/commit/05997bd)
chore(set_theory/ordinal/{basic, arithmetic}): Remove redundant `function` namespace ([#14133](https://github.com/leanprover-community/mathlib/pull/14133))
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean
- \+/\- *lemma* not_injective_of_ordinal
- \+/\- *lemma* not_surjective_of_ordinal

Modified src/set_theory/ordinal/basic.lean




## [2022-05-14 17:09:31](https://github.com/leanprover-community/mathlib/commit/9d022d7)
doc(data/real/sqrt): Fix typo in described theorem ([#14126](https://github.com/leanprover-community/mathlib/pull/14126))
The previous statement was not true. e.g. sqrt 4 <= 3 does not imply 4 * 4 <= 3
#### Estimated changes
Modified src/data/real/sqrt.lean




## [2022-05-14 17:09:30](https://github.com/leanprover-community/mathlib/commit/4125b9a)
chore(category_theory/*): move some elementwise lemmas earlier ([#13998](https://github.com/leanprover-community/mathlib/pull/13998))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/algebra/category/Ring/basic.lean


Modified src/algebra/category/Semigroup/basic.lean


Modified src/algebraic_geometry/Scheme.lean


Modified src/algebraic_geometry/Spec.lean


Modified src/algebraic_geometry/properties.lean


Modified src/analysis/normed/group/SemiNormedGroup.lean


Modified src/category_theory/concrete_category/basic.lean
- \- *lemma* category_theory.coe_hom_inv_id
- \- *lemma* category_theory.coe_inv_hom_id

Modified src/category_theory/concrete_category/elementwise.lean


Added src/category_theory/elementwise.lean


Modified src/ring_theory/ideal/local_ring.lean


Modified src/topology/category/Top/basic.lean


Modified src/topology/sheaves/sheaf_condition/equalizer_products.lean


Modified src/topology/sheaves/stalks.lean




## [2022-05-14 15:50:40](https://github.com/leanprover-community/mathlib/commit/c992b04)
feat(set_theory/cardinal/cofinality): Cofinality of `nfp` and `deriv` ([#12556](https://github.com/leanprover-community/mathlib/pull/12556))
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* cardinal.deriv_bfamily_lt_ord
- \+ *theorem* cardinal.deriv_bfamily_lt_ord_lift
- \+ *theorem* cardinal.deriv_family_lt_ord
- \+ *theorem* cardinal.deriv_family_lt_ord_lift
- \+ *theorem* cardinal.deriv_lt_ord
- \+ *theorem* cardinal.nfp_bfamily_lt_ord_lift_of_is_regular
- \+ *theorem* cardinal.nfp_bfamily_lt_ord_of_is_regular
- \+ *theorem* cardinal.nfp_family_lt_ord_lift_of_is_regular
- \+ *theorem* cardinal.nfp_family_lt_ord_of_is_regular
- \+ *theorem* cardinal.nfp_lt_ord_of_is_regular
- \+ *theorem* ordinal.nfp_bfamily_lt_ord
- \+ *theorem* ordinal.nfp_bfamily_lt_ord_lift
- \+ *theorem* ordinal.nfp_family_lt_ord
- \+ *theorem* ordinal.nfp_family_lt_ord_lift
- \+ *theorem* ordinal.nfp_lt_ord



## [2022-05-14 12:48:56](https://github.com/leanprover-community/mathlib/commit/6d4c202)
feat(analysis/specific_limits/floor_pow): auxiliary results on series involving floors of powers ([#13850](https://github.com/leanprover-community/mathlib/pull/13850))
#### Estimated changes
Added src/analysis/specific_limits/floor_pow.lean
- \+ *lemma* mul_pow_le_nat_floor_pow
- \+ *lemma* sum_div_nat_floor_pow_sq_le_div_sq
- \+ *lemma* sum_div_pow_sq_le_div_sq
- \+ *lemma* tendsto_div_of_monotone_of_exists_subseq_tendsto_div
- \+ *lemma* tendsto_div_of_monotone_of_tendsto_div_floor_pow



## [2022-05-14 10:51:28](https://github.com/leanprover-community/mathlib/commit/ba9d551)
chore(algebra/invertible): minor golf ([#14141](https://github.com/leanprover-community/mathlib/pull/14141))
#### Estimated changes
Modified src/algebra/invertible.lean
- \+/\- *lemma* inv_of_inv_of
- \+/\- *lemma* inv_of_mul
- \+/\- *lemma* nonempty_invertible_iff_is_unit



## [2022-05-14 08:16:18](https://github.com/leanprover-community/mathlib/commit/79bc06b)
feat(linear_algebra/matrix/to_lin): equivalence via right multiplication ([#13870](https://github.com/leanprover-community/mathlib/pull/13870))
A very partial generalization of `linear_algebra/matrix/to_lin` to non-commutative rings.
This is far from a complete refactor of the file; it just adds enough for what I need in representation theory immediately.
I've left an extensive note explaining what should be done in a later refactor, but I don't want to have to do this all at once.
See discussion on [zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/matrices).
#### Estimated changes
Modified src/linear_algebra/matrix/to_lin.lean
- \+ *def* linear_map.to_matrix_right'
- \+/\- *def* matrix.mul_vec_lin
- \- *lemma* matrix.mul_vec_lin_apply
- \+ *def* matrix.to_linear_equiv_right'_of_inv
- \+ *abbreviation* matrix.to_linear_map_right'
- \+ *lemma* matrix.to_linear_map_right'_apply
- \+ *lemma* matrix.to_linear_map_right'_mul
- \+ *lemma* matrix.to_linear_map_right'_mul_apply
- \+ *lemma* matrix.to_linear_map_right'_one
- \+ *def* matrix.vec_mul_linear
- \+ *lemma* matrix.vec_mul_std_basis



## [2022-05-14 07:28:44](https://github.com/leanprover-community/mathlib/commit/21a71de)
chore(*): use notation instead of `set.*` ([#14139](https://github.com/leanprover-community/mathlib/pull/14139))
#### Estimated changes
Modified src/computability/language.lean


Modified src/data/real/ereal.lean
- \+/\- *def* ereal.ne_top_bot_equiv_real

Modified src/group_theory/free_product.lean


Modified src/measure_theory/measure/measure_space.lean


Modified src/topology/instances/ereal.lean
- \+/\- *lemma* ereal.continuous_on_to_real
- \+/\- *def* ereal.ne_bot_top_homeomorph_real



## [2022-05-14 05:39:32](https://github.com/leanprover-community/mathlib/commit/3824493)
refactor(group_theory/free_abelian_group): Make proofs more robust ([#14089](https://github.com/leanprover-community/mathlib/pull/14089))
Reduce the API breakage by proving `distrib (free_abelian_group α)` and `has_distrib_neg (free_abelian_group α)` earlier. Protect lemmas to avoid shadowing the root ones.
#### Estimated changes
Modified src/group_theory/free_abelian_group.lean
- \+ *lemma* free_abelian_group.lift_neg'
- \- *lemma* free_abelian_group.map_add
- \- *lemma* free_abelian_group.map_neg
- \- *lemma* free_abelian_group.map_sub
- \- *lemma* free_abelian_group.map_zero
- \+/\- *lemma* free_abelian_group.mul_def
- \+/\- *lemma* free_abelian_group.of_mul_of



## [2022-05-14 05:02:33](https://github.com/leanprover-community/mathlib/commit/9f5b328)
feat(.github/workflows): restore merge_conflicts action, running on cron ([#14137](https://github.com/leanprover-community/mathlib/pull/14137))
#### Estimated changes
Added .github/workflows/merge_conflicts.yml




## [2022-05-13 16:35:43](https://github.com/leanprover-community/mathlib/commit/b7e20ca)
feat(data/polynomial/degree/definitions): two more `nat_degree_le` lemmas ([#14098](https://github.com/leanprover-community/mathlib/pull/14098))
This PR is similar to [#14095](https://github.com/leanprover-community/mathlib/pull/14095).  It proves the `le` version of `nat_degree_X_pow` and `nat_degree_monomial`.
These lemmas are analogous to the existing `nat_degree_X_le` and `nat_degree_C_mul_X_pow_le`.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.nat_degree_X_pow_le
- \+/\- *lemma* polynomial.nat_degree_monomial
- \+ *lemma* polynomial.nat_degree_monomial_le



## [2022-05-13 15:42:07](https://github.com/leanprover-community/mathlib/commit/6b7fa7a)
feat(data/nat/totient): add `totient_div_of_dvd` and golf `sum_totient` ([#14007](https://github.com/leanprover-community/mathlib/pull/14007))
Add lemma `totient_div_of_dvd`: for `d ∣ n`, the totient of `n/d` equals the number of values `k < n` such that `gcd n k = d`.
Use this to golf `sum_totient`, now stated in terms of `divisors`.  This proof follows that of Theorem 2.2 in Apostol (1976) Introduction to Analytic Number Theory.
Adapt the proof of `nth_roots_one_eq_bUnion_primitive_roots'` to use the new `sum_totient`.
Re-prove the original statement of `sum_totient` for compatibility with uses in `group_theory/specific_groups/cyclic` — may delete this if those uses can be adapted to the new statement.
#### Estimated changes
Modified src/data/nat/totient.lean
- \+ *lemma* nat.sum_totient'
- \+/\- *lemma* nat.sum_totient
- \+ *lemma* nat.totient_div_of_dvd

Modified src/group_theory/specific_groups/cyclic.lean


Modified src/ring_theory/roots_of_unity.lean




## [2022-05-13 13:23:57](https://github.com/leanprover-community/mathlib/commit/55cd104)
feat(archive/imo/imo1975_q1): Add the formalization of IMO 1975 Q1 ([#13047](https://github.com/leanprover-community/mathlib/pull/13047))
#### Estimated changes
Added archive/imo/imo1975_q1.lean
- \+ *theorem* IMO_1975_Q1



## [2022-05-13 09:53:49](https://github.com/leanprover-community/mathlib/commit/caa1352)
feat(data/zmod/quotient): Multiplicative version of `zmultiples_quotient_stabilizer_equiv` ([#13948](https://github.com/leanprover-community/mathlib/pull/13948))
This PR adds a multiplicative version of `zmultiples_quotient_stabilizer_equiv`.
#### Estimated changes
Modified src/data/zmod/quotient.lean
- \+ *lemma* mul_action.zpowers_quotient_stabilizer_equiv_symm_apply



## [2022-05-13 09:53:48](https://github.com/leanprover-community/mathlib/commit/03da681)
feat(representation_theory): fdRep k G, the category of finite dim representations of G ([#13740](https://github.com/leanprover-community/mathlib/pull/13740))
We verify that this inherits the rigid monoidal structure from `FinVect G` when `G` is a group.
#### Estimated changes
Modified src/representation_theory/Action.lean


Added src/representation_theory/fdRep.lean
- \+ *def* fdRep.of
- \+ *abbreviation* fdRep



## [2022-05-13 07:38:22](https://github.com/leanprover-community/mathlib/commit/6a48b38)
feat(topology/uniform_space): lemmas about `s ○ s ○ ... ○ s ⊆ t` ([#14051](https://github.com/leanprover-community/mathlib/pull/14051))
#### Estimated changes
Modified src/order/filter/small_sets.lean
- \+ *lemma* filter.eventually_small_sets_subset

Modified src/topology/uniform_space/basic.lean
- \+ *lemma* eventually_uniformity_comp_subset
- \+ *lemma* eventually_uniformity_iterate_comp_subset
- \+ *lemma* left_subset_comp_rel
- \+ *lemma* right_subset_comp_rel
- \+/\- *lemma* subset_comp_self
- \+ *lemma* subset_iterate_comp_rel
- \+ *lemma* symmetric_rel.mk_mem_comm



## [2022-05-13 05:13:49](https://github.com/leanprover-community/mathlib/commit/3185c25)
feat(data/list/{count,perm},data/multiset/basic): countp and count lemmas ([#14108](https://github.com/leanprover-community/mathlib/pull/14108))
#### Estimated changes
Modified src/data/list/count.lean
- \+ *lemma* list.count_eq_zero
- \+ *lemma* list.countp_cons
- \+ *theorem* list.countp_eq_zero

Modified src/data/list/perm.lean
- \+ *theorem* list.countp_eq_countp_filter_add
- \+ *theorem* list.filter_append_perm
- \+ *theorem* list.perm.countp_congr

Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.card_eq_countp_add_countp
- \+ *theorem* multiset.count_eq_card
- \+ *theorem* multiset.count_le_card
- \+ *theorem* multiset.countp_congr
- \+ *theorem* multiset.countp_eq_card
- \+ *theorem* multiset.countp_eq_countp_filter_add
- \+ *theorem* multiset.countp_eq_zero
- \+ *lemma* multiset.countp_false
- \+ *theorem* multiset.countp_le_card
- \+ *lemma* multiset.countp_true



## [2022-05-13 05:13:48](https://github.com/leanprover-community/mathlib/commit/23a2205)
chore(data/real/ennreal): tidy some proofs ([#14101](https://github.com/leanprover-community/mathlib/pull/14101))
#### Estimated changes
Modified src/data/real/ennreal.lean




## [2022-05-13 05:13:47](https://github.com/leanprover-community/mathlib/commit/7b7af48)
feat(set_theory/ordinal/basic): Order isomorphism between `o.out.α` and `set.Iio o` ([#14074](https://github.com/leanprover-community/mathlib/pull/14074))
This strengthens the previously existing equivalence.
#### Estimated changes
Modified src/set_theory/game/nim.lean


Modified src/set_theory/game/ordinal.lean


Modified src/set_theory/ordinal/arithmetic.lean


Modified src/set_theory/ordinal/basic.lean
- \+ *def* ordinal.enum_iso
- \- *def* ordinal.typein_iso



## [2022-05-13 05:13:46](https://github.com/leanprover-community/mathlib/commit/26f4112)
feat(topology/uniform_space/separation): add `filter.has_basis.mem_separation_rel` ([#14050](https://github.com/leanprover-community/mathlib/pull/14050))
* add `filter.has_basis.mem_separation_rel`;
* add `filter.has_basis.forall_mem_mem`, use it in
  `filter.has_basis.sInter_sets`;
* replace two remaining `lift' powerset` with `small_sets`.
#### Estimated changes
Modified src/order/filter/bases.lean
- \+ *lemma* filter.has_basis.forall_mem_mem

Modified src/order/filter/small_sets.lean


Modified src/topology/uniform_space/separation.lean
- \+ *lemma* filter.has_basis.mem_separation_rel



## [2022-05-13 05:13:45](https://github.com/leanprover-community/mathlib/commit/a2e671b)
feat(number_theory/von_mangoldt): simple bounds on von mangoldt function ([#14033](https://github.com/leanprover-community/mathlib/pull/14033))
From the unit fractions project.
More interesting bounds such as the chebyshev bounds coming soon, but for now here are some easy upper and lower bounds.
#### Estimated changes
Modified src/number_theory/von_mangoldt.lean
- \+ *lemma* nat.arithmetic_function.von_mangoldt_eq_zero_iff
- \+ *lemma* nat.arithmetic_function.von_mangoldt_le_log
- \+ *lemma* nat.arithmetic_function.von_mangoldt_ne_zero_iff
- \+ *lemma* nat.arithmetic_function.von_mangoldt_pos_iff



## [2022-05-13 05:13:44](https://github.com/leanprover-community/mathlib/commit/644cae5)
feat(set_theory/cardinal/cofinality): Move fundamental sequence results to namespace ([#14020](https://github.com/leanprover-community/mathlib/pull/14020))
We put most results about fundamental sequences in the `is_fundamental_sequence` namespace. We also take the opportunity to add a simple missing theorem, `ord_cof`.
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean
- \+/\- *theorem* ordinal.is_fundamental_sequence.blsub_eq
- \- *theorem* ordinal.is_fundamental_sequence.cof_eq
- \+ *theorem* ordinal.is_fundamental_sequence.id_of_le_cof
- \- *theorem* ordinal.is_fundamental_sequence.monotone
- \+ *theorem* ordinal.is_fundamental_sequence.ord_cof
- \- *theorem* ordinal.is_fundamental_sequence.strict_mono
- \+/\- *theorem* ordinal.is_fundamental_sequence.trans
- \- *theorem* ordinal.is_fundamental_sequence_id_of_le_cof
- \- *theorem* ordinal.is_fundamental_sequence_succ
- \- *theorem* ordinal.is_fundamental_sequence_zero



## [2022-05-13 02:53:51](https://github.com/leanprover-community/mathlib/commit/c53285a)
feat(order/filter/lift): drop an unneeded assumption ([#14117](https://github.com/leanprover-community/mathlib/pull/14117))
Drop `monotone _` assumptions in `filter.comap_lift_eq` and `filter.comap_lift'_eq`.
#### Estimated changes
Modified src/order/filter/lift.lean
- \+/\- *theorem* filter.comap_lift'_eq
- \+/\- *lemma* filter.comap_lift_eq

Modified src/order/filter/small_sets.lean


Modified src/topology/uniform_space/basic.lean


Modified src/topology/uniform_space/completion.lean


Modified src/topology/uniform_space/uniform_embedding.lean




## [2022-05-13 02:53:50](https://github.com/leanprover-community/mathlib/commit/85124af)
chore(algebra/order/field): fill in TODO for inv anti lemmas ([#14112](https://github.com/leanprover-community/mathlib/pull/14112))
#### Estimated changes
Modified src/algebra/order/field.lean
- \+ *lemma* inv_pow_anti
- \+ *lemma* inv_pow_le_inv_pow_of_le
- \+ *lemma* inv_pow_lt_inv_pow_of_lt
- \+ *lemma* inv_pow_strict_anti
- \+ *lemma* inv_strict_anti_on



## [2022-05-13 02:53:49](https://github.com/leanprover-community/mathlib/commit/462b950)
chore(algebra/order/field): fill in missing lemma ([#14111](https://github.com/leanprover-community/mathlib/pull/14111))
We had `inv_le_inv` and its backward direction, this fills in the backward direction for `inv_lt_inv`.
#### Estimated changes
Modified src/algebra/order/field.lean
- \+ *lemma* inv_lt_inv_of_lt



## [2022-05-13 02:53:48](https://github.com/leanprover-community/mathlib/commit/f617862)
feat(data/polynomial/degree/lemmas): two lemmas about `nat_degree`s of sums ([#14100](https://github.com/leanprover-community/mathlib/pull/14100))
Suppose that `f, g` are polynomials.  If both `nat_degree (f + g)` and `nat_degree` of one of them are bounded by `n`, then `nat_degree` of the other is also bounded by `n`.
#### Estimated changes
Modified src/data/polynomial/degree/lemmas.lean
- \+ *lemma* polynomial.nat_degree_add_le_iff_left
- \+ *lemma* polynomial.nat_degree_add_le_iff_right



## [2022-05-13 02:53:47](https://github.com/leanprover-community/mathlib/commit/de418aa)
feat(topology/basic): add lemmas like `closure s \ interior s = frontier s` ([#14086](https://github.com/leanprover-community/mathlib/pull/14086))
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* closure_diff_frontier
- \+ *lemma* closure_diff_interior
- \+ *lemma* self_diff_frontier



## [2022-05-13 02:53:46](https://github.com/leanprover-community/mathlib/commit/15f6b52)
feat(data/set/prod): add `prod_self_{s,}subset_prod_self` ([#14084](https://github.com/leanprover-community/mathlib/pull/14084))
#### Estimated changes
Modified src/data/set/prod.lean
- \+ *lemma* set.prod_self_ssubset_prod_self
- \+ *lemma* set.prod_self_subset_prod_self



## [2022-05-13 02:53:45](https://github.com/leanprover-community/mathlib/commit/1474996)
feat(topology/basic): add `nhds_basis_closeds` ([#14083](https://github.com/leanprover-community/mathlib/pull/14083))
* add `nhds_basis_closeds`;
* golf 2 proofs;
* move `topological_space.seq_tendsto_iff` to `topology.basic`, rename
  it to `tendsto_at_top_nhds`.
#### Estimated changes
Modified src/topology/basic.lean
- \+ *lemma* nhds_basis_closeds
- \+/\- *lemma* nhds_basis_opens
- \+ *lemma* tendsto_at_top_nhds

Modified src/topology/sequences.lean
- \- *lemma* topological_space.seq_tendsto_iff



## [2022-05-13 02:53:44](https://github.com/leanprover-community/mathlib/commit/bb97a64)
feat(topology/order): add `nhds_true` and `nhds_false` ([#14082](https://github.com/leanprover-community/mathlib/pull/14082))
#### Estimated changes
Modified src/topology/order.lean
- \+ *lemma* nhds_false
- \+ *lemma* nhds_true



## [2022-05-13 02:53:43](https://github.com/leanprover-community/mathlib/commit/bd5914f)
perf(field_theory/primitive_element): declare auxiliary function `noncomputable!` ([#14071](https://github.com/leanprover-community/mathlib/pull/14071))
The declaration `roots_of_min_poly_pi_type` is computable and gets compiled by Lean. Unfortunately, compilation takes about 2-3s on my machine and times out under [#11759](https://github.com/leanprover-community/mathlib/pull/11759) (with timeouts disabled, it takes about 11s on that branch). Since the parameters are all elements of noncomputable types and its only use is a noncomputable `fintype` instance, nobody will care if we explicitly make it computable, and it saves a lot of compilation time.
See also this Zulip thread on `noncomputable!` fixing mysterious timeouts: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Timeout/near/278494746
#### Estimated changes
Modified src/field_theory/primitive_element.lean
- \- *def* field.roots_of_min_poly_pi_type



## [2022-05-13 02:53:42](https://github.com/leanprover-community/mathlib/commit/c4c279e)
feat(data/real/nnreal): add `nnreal.le_infi_add_infi` and other lemmas ([#14048](https://github.com/leanprover-community/mathlib/pull/14048))
* add `nnreal.coe_two`, `nnreal.le_infi_add_infi`, `nnreal.half_le_self`;
* generalize `le_cinfi_mul_cinfi`, `csupr_mul_csupr_le`, and their
  additive versions to allow two different index types.
#### Estimated changes
Modified src/data/real/basic.lean


Modified src/data/real/nnreal.lean
- \+ *lemma* nnreal.half_le_self
- \+ *lemma* nnreal.le_infi_add_infi

Modified src/order/conditionally_complete_lattice.lean




## [2022-05-13 01:22:31](https://github.com/leanprover-community/mathlib/commit/a945b18)
feat(linear_algebra/tensor_product): tensor_product.map is bilinear in its two arguments ([#13608](https://github.com/leanprover-community/mathlib/pull/13608))
#### Estimated changes
Modified src/linear_algebra/dual.lean
- \+ *def* tensor_product.dual_distrib
- \+ *lemma* tensor_product.dual_distrib_apply
- \+ *def* tensor_product.dual_distrib_equiv
- \+ *def* tensor_product.dual_distrib_inv_of_basis
- \+ *lemma* tensor_product.dual_distrib_inv_of_basis_apply

Modified src/linear_algebra/tensor_product.lean
- \+ *def* tensor_product.hom_tensor_hom_map
- \+ *lemma* tensor_product.hom_tensor_hom_map_apply
- \+ *lemma* tensor_product.map_add_left
- \+ *lemma* tensor_product.map_add_right
- \+ *def* tensor_product.map_bilinear
- \+ *lemma* tensor_product.map_bilinear_apply
- \+ *lemma* tensor_product.map_smul_left
- \+ *lemma* tensor_product.map_smul_right
- \+ *lemma* tensor_product.smul_tmul_smul

Modified src/ring_theory/tensor_product.lean
- \+ *def* module.End_tensor_End_alg_hom
- \+ *lemma* module.End_tensor_End_alg_hom_apply



## [2022-05-12 20:54:24](https://github.com/leanprover-community/mathlib/commit/17102ae)
feat(algebra/big_operators/basic): add `sum_erase_lt_of_pos` ([#14066](https://github.com/leanprover-community/mathlib/pull/14066))
`sum_erase_lt_of_pos (hd : d ∈ s) (hdf : 0 < f d) : ∑ (m : ℕ) in s.erase d, f m < ∑ (m : ℕ) in s, f m`
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.sum_erase_lt_of_pos



## [2022-05-12 20:54:23](https://github.com/leanprover-community/mathlib/commit/86d58ae)
feat(data/nat/factorization): three lemmas on the components of factorizations ([#14031](https://github.com/leanprover-community/mathlib/pull/14031))
`pow_factorization_le : p ^ (n.factorization) p ≤ n`
`div_pow_factorization_ne_zero : n / p ^ (n.factorization) p ≠ 0`
`not_dvd_div_pow_factorization : ¬p ∣ n / p ^ (n.factorization) p`
Prompted by [this question](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/prime.20factorisation) in Zulip
#### Estimated changes
Modified src/data/nat/factorization.lean
- \+ *lemma* nat.div_pow_factorization_ne_zero
- \+ *lemma* nat.not_dvd_div_pow_factorization
- \+ *lemma* nat.pow_factorization_le



## [2022-05-12 20:54:22](https://github.com/leanprover-community/mathlib/commit/3c1ced3)
feat(data/nat/basic): four lemmas on nat and int division ([#13991](https://github.com/leanprover-community/mathlib/pull/13991))
`lt_div_iff_mul_lt (hnd : d ∣ n) : a < n / d ↔ d * a < n`
`div_left_inj (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b` (for `ℕ` and `ℤ`)
`div_lt_div_of_lt_of_dvd (hdb : d ∣ b) (h : a < b) : a / d < b / d`
#### Estimated changes
Modified src/data/int/basic.lean


Modified src/data/nat/basic.lean
- \+ *lemma* nat.div_lt_div_of_lt_of_dvd



## [2022-05-12 19:34:26](https://github.com/leanprover-community/mathlib/commit/4b3988a)
feat(data/sym/sym2): simp lemma for quotient.eq ([#14113](https://github.com/leanprover-community/mathlib/pull/14113))
#### Estimated changes
Modified src/data/sym/sym2.lean
- \+ *lemma* sym2.rel_iff



## [2022-05-12 19:34:25](https://github.com/leanprover-community/mathlib/commit/3d03098)
doc(data/matrix/basic): Clarify docstring ([#14109](https://github.com/leanprover-community/mathlib/pull/14109))
#### Estimated changes
Modified src/data/matrix/basic.lean




## [2022-05-12 18:30:47](https://github.com/leanprover-community/mathlib/commit/27e7f7a)
feat(number_theory/divisors): add `filter_dvd_eq_proper_divisors` ([#14049](https://github.com/leanprover-community/mathlib/pull/14049))
Adds `filter_dvd_eq_proper_divisors` and golfs `filter_dvd_eq_divisors` and a few other lemmas
#### Estimated changes
Modified src/number_theory/divisors.lean
- \+/\- *lemma* nat.filter_dvd_eq_divisors
- \+ *lemma* nat.filter_dvd_eq_proper_divisors
- \+/\- *lemma* nat.mem_divisors



## [2022-05-12 17:54:58](https://github.com/leanprover-community/mathlib/commit/3b18573)
doc(tactic/rewrite_search/explain): Fix documentation-breaking docstring ([#14107](https://github.com/leanprover-community/mathlib/pull/14107))
This currently renders as
![image](https://user-images.githubusercontent.com/425260/168125021-06ef8851-55a6-4629-b437-7c38a1df7b05.png)
#### Estimated changes
Modified src/tactic/rewrite_search/explain.lean




## [2022-05-12 16:23:39](https://github.com/leanprover-community/mathlib/commit/0e834df)
chore(data/nat/multiplicity): simplify proof ([#14103](https://github.com/leanprover-community/mathlib/pull/14103))
#### Estimated changes
Modified src/data/nat/multiplicity.lean
- \+/\- *lemma* nat.prime.multiplicity_le_multiplicity_choose_add



## [2022-05-12 16:23:38](https://github.com/leanprover-community/mathlib/commit/0509c9c)
fix(analysis/special_functions/pow): fix norm_num extension ([#14099](https://github.com/leanprover-community/mathlib/pull/14099))
As [reported on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/kernel.20slow.20to.20accept.20refl.20proof/near/282043840).
#### Estimated changes
Modified src/analysis/special_functions/pow.lean
- \+/\- *theorem* norm_num.rpow_pos

Modified test/norm_num_ext.lean




## [2022-05-12 16:23:37](https://github.com/leanprover-community/mathlib/commit/c8edd60)
chore(data/polynomial/ring_division): golf a few proofs ([#14097](https://github.com/leanprover-community/mathlib/pull/14097))
* add `polynomial.finite_set_of_is_root`;
* use it to golf a few proofs.
#### Estimated changes
Modified src/analysis/special_functions/polynomials.lean
- \+/\- *lemma* polynomial.eventually_no_roots

Modified src/data/polynomial/ring_division.lean
- \+/\- *lemma* polynomial.eq_of_infinite_eval_eq
- \+/\- *lemma* polynomial.eq_zero_of_infinite_is_root
- \+ *lemma* polynomial.finite_set_of_is_root



## [2022-05-12 16:23:36](https://github.com/leanprover-community/mathlib/commit/6cf6e8c)
chore(order/filter/basic): golf a few proofs ([#14078](https://github.com/leanprover-community/mathlib/pull/14078))
* golf the proof of `mem_generate_iff` by using `sInter_mem`;
* use `set.inj_on` in the statement of `filter.eq_of_map_eq_map_inj'`;
* golf the proofs of `filter.map_inj` and `filter.comap_ne_bot_iff`.
#### Estimated changes
Modified src/order/filter/basic.lean




## [2022-05-12 14:24:07](https://github.com/leanprover-community/mathlib/commit/9b41e4e)
feat(data/polynomial/laurent): add truncation from Laurent polynomials to polynomials ([#14085](https://github.com/leanprover-community/mathlib/pull/14085))
We introduce the truncation of a Laurent polynomial `f`.  It returns a polynomial whose support is exactly the non-negative support of `f`.  We use it to prove injectivity of the inclusion of polynomials in Laurent polynomials.
I also plan to use the results in this PR to prove that any Laurent polynomials is obtain from a polynomial by dividing by a power of the variable.
#### Estimated changes
Modified src/data/polynomial/laurent.lean
- \+ *lemma* laurent_polynomial.left_inverse_trunc_to_laurent
- \+ *def* laurent_polynomial.trunc
- \+ *lemma* laurent_polynomial.trunc_C_mul_T
- \+ *lemma* polynomial.to_laurent_inj
- \+ *lemma* polynomial.to_laurent_injective
- \+ *lemma* polynomial.trunc_to_laurent



## [2022-05-12 14:24:06](https://github.com/leanprover-community/mathlib/commit/fa4c036)
chore(order/complete_lattice,data/set/lattice): move `Sup_sUnion` ([#14077](https://github.com/leanprover-community/mathlib/pull/14077))
* move `Sup_sUnion` and `Inf_sUnion` to `data.set.lattice`;
* golf a few proofs.
#### Estimated changes
Modified src/data/set/lattice.lean
- \+ *lemma* Inf_sUnion
- \+ *lemma* Sup_sUnion

Modified src/order/complete_lattice.lean
- \- *lemma* Inf_sUnion
- \- *lemma* Sup_sUnion



## [2022-05-12 12:10:19](https://github.com/leanprover-community/mathlib/commit/bada932)
feat(data/multiset/basic): `erase_singleton` ([#14094](https://github.com/leanprover-community/mathlib/pull/14094))
Add `multiset.erase_singleton` which is analogous to the existing [finset.erase_singleton](https://leanprover-community.github.io/mathlib_docs/data/finset/basic.html#finset.erase_singleton).
#### Estimated changes
Modified src/data/multiset/basic.lean
- \+ *theorem* multiset.erase_singleton



## [2022-05-12 12:10:18](https://github.com/leanprover-community/mathlib/commit/55671be)
chore(set_theory/zfc): use `derive` for some instances ([#14079](https://github.com/leanprover-community/mathlib/pull/14079))
Also use `has_compl` instead of `has_neg`.
#### Estimated changes
Modified src/set_theory/zfc.lean




## [2022-05-12 12:10:17](https://github.com/leanprover-community/mathlib/commit/d9e623c)
feat(algebra/*): Division monoid instances for `with_zero` and `mul_opposite` ([#14073](https://github.com/leanprover-community/mathlib/pull/14073))
A few missing instances of `division_monoid` and friends.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \+ *lemma* inv_comp_inv

Modified src/algebra/group/opposite.lean


Modified src/algebra/group/with_one.lean
- \+/\- *lemma* with_zero.coe_inv
- \+/\- *lemma* with_zero.inv_zero



## [2022-05-12 12:10:16](https://github.com/leanprover-community/mathlib/commit/c57cfc6)
feat({data/{finset,set},order/filter}/pointwise): Pointwise monoids are division monoids ([#13900](https://github.com/leanprover-community/mathlib/pull/13900))
`α` is a `division_monoid` implies that `set α`, `finset α`, `filter α` are too. The core result needed for this is that `s` is a unit in `set α`/`finset α`/`filter α` if and only if it is equal to `{u}`/`{u}`/`pure u` for some unit `u : α`.
#### Estimated changes
Modified src/data/finset/pointwise.lean
- \+ *lemma* finset.coe_singleton_monoid_hom
- \+ *lemma* finset.coe_singleton_mul_hom
- \+ *lemma* finset.coe_singleton_one_hom
- \- *lemma* finset.coe_zpow'
- \+/\- *lemma* finset.coe_zpow
- \+ *lemma* finset.is_unit_coe
- \+ *lemma* finset.is_unit_iff
- \+ *lemma* finset.is_unit_iff_singleton
- \+ *lemma* finset.is_unit_singleton
- \+ *def* finset.singleton_monoid_hom
- \+ *lemma* finset.singleton_monoid_hom_apply
- \+ *def* finset.singleton_mul_hom
- \+ *lemma* finset.singleton_mul_hom_apply
- \+ *def* finset.singleton_one_hom
- \+ *lemma* finset.singleton_one_hom_apply

Modified src/data/set/pointwise.lean
- \+ *lemma* set.coe_singleton_monoid_hom
- \+ *lemma* set.coe_singleton_mul_hom
- \+ *lemma* set.coe_singleton_one_hom
- \+ *lemma* set.is_unit_iff
- \+ *lemma* set.is_unit_iff_singleton
- \+ *lemma* set.is_unit_singleton
- \+ *def* set.singleton_monoid_hom
- \+ *lemma* set.singleton_monoid_hom_apply
- \+/\- *def* set.singleton_mul_hom
- \+ *lemma* set.singleton_mul_hom_apply
- \+ *def* set.singleton_one_hom

Modified src/order/filter/pointwise.lean
- \+ *lemma* filter.coe_pure_monoid_hom
- \+ *lemma* filter.coe_pure_mul_hom
- \+ *lemma* filter.coe_pure_one_hom
- \+ *lemma* filter.is_unit_iff
- \+ *lemma* filter.is_unit_iff_singleton
- \+ *lemma* filter.is_unit_pure
- \+ *def* filter.pure_monoid_hom
- \+ *lemma* filter.pure_monoid_hom_apply
- \+ *def* filter.pure_mul_hom
- \+ *lemma* filter.pure_mul_hom_apply
- \+ *def* filter.pure_one_hom
- \+ *lemma* filter.pure_one_hom_apply

Modified src/order/filter/ultrafilter.lean
- \+/\- *lemma* filter.mem_iff_ultrafilter

Modified src/topology/algebra/group.lean




## [2022-05-12 10:27:03](https://github.com/leanprover-community/mathlib/commit/c2e87de)
feat(data/polynomial/degree/definitions): if `r ≠ 0`, then `(monomial i r).nat_degree = i` ([#14095](https://github.com/leanprover-community/mathlib/pull/14095))
Add a lemma analogous to `nat_degree_C_mul_X_pow` and `nat_degree_C_mul_X`.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean
- \+ *lemma* polynomial.nat_degree_monomial_eq



## [2022-05-12 10:27:02](https://github.com/leanprover-community/mathlib/commit/5927330)
refactor(combinatorics/simple_graph/basic): relax `edge_finset` typeclasses ([#14091](https://github.com/leanprover-community/mathlib/pull/14091))
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \+/\- *def* simple_graph.edge_finset
- \+ *lemma* simple_graph.edge_finset_card
- \+/\- *lemma* simple_graph.edge_set_univ_card
- \+/\- *lemma* simple_graph.mem_edge_finset



## [2022-05-12 10:27:01](https://github.com/leanprover-community/mathlib/commit/41afd8c)
feat(analysis/special_functions/pow): asymptotics for real powers and log ([#14088](https://github.com/leanprover-community/mathlib/pull/14088))
From the unit fractions project.
#### Estimated changes
Modified src/analysis/special_functions/log/basic.lean
- \+ *lemma* real.is_o_log_id_at_top
- \+/\- *lemma* real.is_o_pow_log_id_at_top

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* asymptotics.is_O.rpow
- \+ *lemma* asymptotics.is_O_with.rpow
- \+ *lemma* asymptotics.is_o.rpow
- \+ *lemma* is_o_log_rpow_at_top
- \+ *lemma* is_o_log_rpow_rpow_at_top



## [2022-05-12 08:45:52](https://github.com/leanprover-community/mathlib/commit/1c8ce7e)
feat(data/complex): real exponential bounds ([#14087](https://github.com/leanprover-community/mathlib/pull/14087))
Bounds on the real exponential function near 1, derived from the complex versions.
#### Estimated changes
Modified src/data/complex/exponential.lean
- \+/\- *lemma* complex.abs_exp
- \+ *lemma* real.abs_exp_sub_one_le
- \+ *lemma* real.abs_exp_sub_one_sub_id_le



## [2022-05-12 08:45:51](https://github.com/leanprover-community/mathlib/commit/b6d1028)
chore(topology/sequences): golf a few proofs ([#14081](https://github.com/leanprover-community/mathlib/pull/14081))
#### Estimated changes
Modified src/topology/sequences.lean
- \+/\- *lemma* seq_compact.lebesgue_number_lemma_of_metric
- \+/\- *lemma* tendsto_subseq_of_bounded
- \+/\- *lemma* tendsto_subseq_of_frequently_bounded



## [2022-05-12 08:45:50](https://github.com/leanprover-community/mathlib/commit/7c4c90f)
feat(category_theory/noetherian): nonzero artinian objects have simple subobjects ([#13972](https://github.com/leanprover-community/mathlib/pull/13972))
# Artinian and noetherian categories
An artinian category is a category in which objects do not
have infinite decreasing sequences of subobjects.
A noetherian category is a category in which objects do not
have infinite increasing sequences of subobjects.
We show that any nonzero artinian object has a simple subobject.
## Future work
The Jordan-Hölder theorem, following https://stacks.math.columbia.edu/tag/0FCK.
#### Estimated changes
Added src/category_theory/noetherian.lean
- \+ *lemma* category_theory.exists_simple_subobject

Modified src/category_theory/simple.lean
- \+ *lemma* category_theory.subobject_simple_iff_is_atom

Modified src/category_theory/subobject/lattice.lean
- \+ *lemma* category_theory.subobject.nontrivial_of_not_is_zero
- \+ *def* category_theory.subobject.subobject_order_iso



## [2022-05-12 08:45:49](https://github.com/leanprover-community/mathlib/commit/fd98cf1)
chore(ring_theory/unique_factorization_domain): golf ([#13820](https://github.com/leanprover-community/mathlib/pull/13820))
+ Shorten the proof of `exists_irreducible_factor` using `well_founded.has_min` instead of `well_founded.fix`.
+ Remove use of `simp` in `induction_on_irreducible`; now a pure term-mode proof except for the classical instance.
+ Change the proof of `not_unit_iff_exists_factors_eq` (just added in [[#13682](https://github.com/leanprover-community/mathlib/pull/13682)](https://github.com/leanprover-community/mathlib/pull/13682)) to use induction. The new proof doesn't require the `multiset.prod_erase` introduced in [[#13682](https://github.com/leanprover-community/mathlib/pull/13682)](https://github.com/leanprover-community/mathlib/pull/13682), but is about as complex as the old one, so I might change it back if reviewers prefer.
#### Estimated changes
Modified src/ring_theory/unique_factorization_domain.lean




## [2022-05-12 08:45:48](https://github.com/leanprover-community/mathlib/commit/0c26348)
feat(data/finsupp/basic): `finsupp.comap_domain` is an `add_monoid_hom` ([#13783](https://github.com/leanprover-community/mathlib/pull/13783))
This is the version of `map_domain.add_monoid_hom` for `comap_domain`.
I plan to use it for the inclusion of polynomials in Laurent polynomials ([#13415](https://github.com/leanprover-community/mathlib/pull/13415)).
I also fixed a typo in a doc-string.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *def* finsupp.comap_domain.add_monoid_hom
- \+ *lemma* finsupp.comap_domain_add
- \+ *lemma* finsupp.comap_domain_add_of_injective
- \+ *lemma* finsupp.comap_domain_single
- \+ *lemma* finsupp.comap_domain_smul
- \+ *lemma* finsupp.comap_domain_smul_of_injective
- \+ *lemma* finsupp.comap_domain_zero
- \+/\- *lemma* finsupp.map_domain_comap_domain



## [2022-05-12 07:44:21](https://github.com/leanprover-community/mathlib/commit/a966557)
chore(analysis/special_functions/pow): golf a proof ([#14093](https://github.com/leanprover-community/mathlib/pull/14093))
* move `real.abs_rpow_of_nonneg` up;
* use it to golf a line in `real.abs_rpow_le_abs_rpow`.
#### Estimated changes
Modified src/analysis/special_functions/pow.lean




## [2022-05-12 00:05:58](https://github.com/leanprover-community/mathlib/commit/4977fd9)
feat(ring_theory/finiteness): tensor product of two finite modules is finite ([#13733](https://github.com/leanprover-community/mathlib/pull/13733))
Removes [finite_dimensional_tensor_product](https://leanprover-community.github.io/mathlib_docs/linear_algebra/tensor_product_basis.html#finite_dimensional_tensor_product) since it's now proved by `infer_instance`.
#### Estimated changes
Modified src/algebra/category/FinVect.lean


Modified src/linear_algebra/tensor_product.lean
- \+ *lemma* tensor_product.map₂_mk_top_top_eq_top

Modified src/linear_algebra/tensor_product_basis.lean


Modified src/ring_theory/finiteness.lean




## [2022-05-11 20:41:58](https://github.com/leanprover-community/mathlib/commit/d4884c0)
feat(analysis/asymptotics): use weaker TC assumptions ([#14080](https://github.com/leanprover-community/mathlib/pull/14080))
Merge `is_o.trans` with `is_o.trans'`: both lemmas previously took one `semi_normed_group` argument on the primed type (corresponding to the primed function), but now only assume `has_norm` on all three types.
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \- *theorem* asymptotics.is_o.trans'
- \+/\- *theorem* asymptotics.is_o.trans



## [2022-05-11 18:53:31](https://github.com/leanprover-community/mathlib/commit/0302cfd)
chore(measure_theory/function/conditional_expectation): change the definition of condexp and its notation ([#14010](https://github.com/leanprover-community/mathlib/pull/14010))
Before this PR, the conditional expectation `condexp` was defined using an argument `(hm : m ≤ m0)`.
This changes the definition to take only `m`, and assigns the default value 0 if we don't have `m ≤ m0`.
The notation for `condexp m μ f` is simplified to `μ[f|m]`.
The change makes the proofs of the condexp API longer, but no change is needed to lemmas outside of that file. See the file `martingale.lean`: the notation is now simpler, but otherwise little else changes besides removing the now unused argument `[sigma_finite_filtration μ ℱ]` from many lemmas.
Also add an instance `is_finite_measure.sigma_finite_filtration`: we had a lemma with both `is_finite_measure` and `sigma_finite_filtration` arguments, but the first one implies the other.
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+/\- *def* measure_theory.condexp
- \+/\- *lemma* measure_theory.condexp_ae_eq_condexp_L1
- \+/\- *lemma* measure_theory.condexp_ae_eq_condexp_L1_clm
- \+/\- *lemma* measure_theory.condexp_condexp_of_le
- \+/\- *lemma* measure_theory.condexp_const
- \+/\- *lemma* measure_theory.condexp_neg
- \+ *lemma* measure_theory.condexp_of_not_le
- \+ *lemma* measure_theory.condexp_of_not_sigma_finite
- \+ *lemma* measure_theory.condexp_of_sigma_finite
- \+/\- *lemma* measure_theory.condexp_of_strongly_measurable
- \+/\- *lemma* measure_theory.condexp_smul
- \+/\- *lemma* measure_theory.condexp_undef
- \+/\- *lemma* measure_theory.condexp_zero
- \+/\- *lemma* measure_theory.integrable_condexp
- \+/\- *lemma* measure_theory.integral_condexp
- \+/\- *lemma* measure_theory.rn_deriv_ae_eq_condexp
- \+/\- *lemma* measure_theory.set_integral_condexp
- \+/\- *lemma* measure_theory.strongly_measurable_condexp

Modified src/probability/martingale.lean
- \+/\- *lemma* measure_theory.martingale.set_integral_eq
- \+/\- *def* measure_theory.martingale
- \+/\- *lemma* measure_theory.martingale_zero
- \+/\- *lemma* measure_theory.submartingale.expected_stopped_value_mono
- \+/\- *lemma* measure_theory.submartingale.set_integral_le
- \+/\- *def* measure_theory.submartingale
- \+/\- *lemma* measure_theory.supermartingale.set_integral_le
- \+/\- *def* measure_theory.supermartingale

Modified src/probability/notation.lean


Modified src/probability/stopping.lean




## [2022-05-11 15:02:00](https://github.com/leanprover-community/mathlib/commit/7a3ae97)
feat(data/polynomial/laurent): add inductions for Laurent polynomials ([#14005](https://github.com/leanprover-community/mathlib/pull/14005))
This PR introduces two induction principles for Laurent polynomials and uses them to show that `T` commutes with everything.
#### Estimated changes
Modified src/data/polynomial/laurent.lean
- \+ *lemma* laurent_polynomial.T_mul
- \+ *lemma* laurent_polynomial.commute_T



## [2022-05-11 14:23:17](https://github.com/leanprover-community/mathlib/commit/483affa)
feat(measure_theory/integral/interval_integral): add lemma `interval_integrable.sum` ([#14069](https://github.com/leanprover-community/mathlib/pull/14069))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integrable.sum



## [2022-05-11 08:00:03](https://github.com/leanprover-community/mathlib/commit/83bc3b9)
chore(algebra/module/submodule*): replace underscores in file names with a folder ([#14063](https://github.com/leanprover-community/mathlib/pull/14063))
#### Estimated changes
Modified src/algebra/algebra/operations.lean


Modified src/algebra/module/default.lean


Renamed src/algebra/module/submodule.lean to src/algebra/module/submodule/basic.lean


Renamed src/algebra/module/submodule_bilinear.lean to src/algebra/module/submodule/bilinear.lean


Renamed src/algebra/module/submodule_lattice.lean to src/algebra/module/submodule/lattice.lean


Renamed src/algebra/module/submodule_pointwise.lean to src/algebra/module/submodule/pointwise.lean


Modified src/linear_algebra/basic.lean


Modified src/topology/algebra/nonarchimedean/bases.lean


Modified test/import_order_timeout.lean




## [2022-05-11 08:00:02](https://github.com/leanprover-community/mathlib/commit/ba60237)
chore(field_theory/adjoin): clarify and speed up proof ([#14041](https://github.com/leanprover-community/mathlib/pull/14041))
This PR turns a couple of refls into `simp` lemmas. Apart from being clearer now, this also speeds up the proof significantly in [#11759](https://github.com/leanprover-community/mathlib/pull/11759) (where the elaborator chooses the wrong subexpression to unfold first).
Elaboration time changed stayed about the same at about 300-350ms on master, and went from timeout to about 300ms on [#11759](https://github.com/leanprover-community/mathlib/pull/11759).
#### Estimated changes
Modified src/field_theory/adjoin.lean
- \+ *lemma* intermediate_field.bot_equiv_symm
- \+ *lemma* intermediate_field.coe_algebra_map_over_bot



## [2022-05-11 08:00:01](https://github.com/leanprover-community/mathlib/commit/b75113a)
chore(set_theory/game/ordinal): Remove redundant namespaces ([#14039](https://github.com/leanprover-community/mathlib/pull/14039))
#### Estimated changes
Modified src/set_theory/game/birthday.lean




## [2022-05-11 06:01:29](https://github.com/leanprover-community/mathlib/commit/4231b68)
feat(data/list): add a few lemmas ([#14047](https://github.com/leanprover-community/mathlib/pull/14047))
* add `list.reverse_surjective` and `list.reverse_bijective`;
* add `list.chain_iff_forall₂`,
  `list.chain_append_singleton_iff_forall₂`, and `list.all₂_zip_with`.
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *theorem* list.reverse_bijective
- \+/\- *theorem* list.reverse_injective
- \+/\- *theorem* list.reverse_involutive
- \+ *theorem* list.reverse_surjective

Modified src/data/list/chain.lean
- \+ *theorem* list.chain_append_singleton_iff_forall₂
- \+ *theorem* list.chain_iff_forall₂

Modified src/data/list/zip.lean
- \+ *theorem* list.all₂_zip_with



## [2022-05-10 19:04:38](https://github.com/leanprover-community/mathlib/commit/df9683c)
feat(topology/algebra/infinite_sum): lemmas about `mul_opposite` ([#13674](https://github.com/leanprover-community/mathlib/pull/13674))
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean
- \+ *lemma* exp_op
- \+ *lemma* exp_unop

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.op
- \+ *lemma* has_sum.unop
- \+ *lemma* has_sum_op
- \+ *lemma* has_sum_unop
- \+ *lemma* summable.op
- \+ *lemma* summable.unop
- \+ *lemma* summable_op
- \+ *lemma* summable_unop
- \+ *lemma* tsum_op
- \+ *lemma* tsum_unop



## [2022-05-10 17:00:25](https://github.com/leanprover-community/mathlib/commit/3ea573e)
refactor(algebra/{group,group_with_zero/basic): Delete lemmas generalized to division monoids ([#14042](https://github.com/leanprover-community/mathlib/pull/14042))
Delete the `group` and `group_with_zero` lemmas which have been made one-liners in [#14000](https://github.com/leanprover-community/mathlib/pull/14000).
Lemmas are renamed because
* one of the `group` or `group_with_zero` name has to go
* the new API should have a consistent naming convention
Lemma renames
#### Estimated changes
Modified archive/100-theorems-list/9_area_of_a_circle.lean


Modified archive/imo/imo2006_q3.lean


Modified src/algebra/add_torsor.lean


Modified src/algebra/big_operators/multiset.lean


Modified src/algebra/field/basic.lean


Modified src/algebra/geom_sum.lean


Modified src/algebra/group/basic.lean
- \+/\- *lemma* div_div
- \- *theorem* div_div_assoc_swap
- \+/\- *lemma* div_div_div_comm
- \+ *lemma* div_div_div_eq
- \+ *lemma* div_div_eq_mul_div
- \- *lemma* div_eq_inv_mul'
- \+ *lemma* div_eq_inv_mul
- \+/\- *lemma* div_inv_eq_mul
- \+/\- *lemma* div_mul
- \+ *lemma* div_mul_comm
- \+/\- *lemma* div_mul_div_comm
- \+/\- *lemma* div_mul_eq_div_div
- \+/\- *lemma* div_mul_eq_div_div_swap
- \+ *lemma* div_mul_eq_div_mul_one_div
- \- *lemma* div_mul_eq_mul_div'
- \+ *lemma* div_mul_eq_mul_div
- \+/\- *lemma* div_ne_one_of_ne
- \- *lemma* div_one'
- \+ *lemma* div_one
- \- *lemma* div_right_comm'
- \+ *lemma* div_right_comm
- \- *lemma* division_comm_monoid.div_div
- \- *lemma* division_comm_monoid.div_div_div_comm
- \- *lemma* division_comm_monoid.div_div_div_eq
- \- *lemma* division_comm_monoid.div_eq_inv_mul
- \- *lemma* division_comm_monoid.div_mul
- \- *lemma* division_comm_monoid.div_mul_comm
- \- *lemma* division_comm_monoid.div_mul_div_comm
- \- *lemma* division_comm_monoid.div_mul_eq_div_div
- \- *lemma* division_comm_monoid.div_mul_eq_div_mul_one_div
- \- *lemma* division_comm_monoid.div_mul_eq_mul_div
- \- *lemma* division_comm_monoid.div_right_comm
- \- *lemma* division_comm_monoid.inv_div_inv
- \- *lemma* division_comm_monoid.inv_inv_div_inv
- \- *lemma* division_comm_monoid.inv_mul'
- \- *lemma* division_comm_monoid.inv_mul_eq_div
- \- *lemma* division_comm_monoid.mul_comm_div
- \- *lemma* division_comm_monoid.mul_div_left_comm
- \- *lemma* division_comm_monoid.mul_div_mul_comm
- \- *lemma* division_comm_monoid.mul_div_right_comm
- \- *lemma* division_comm_monoid.mul_inv
- \- *lemma* division_comm_monoid.one_div_mul_one_div
- \- *lemma* division_monoid.div_div_eq_mul_div
- \- *lemma* division_monoid.div_inv_eq_mul
- \- *lemma* division_monoid.div_mul_eq_div_div_swap
- \- *lemma* division_monoid.div_ne_one_of_ne
- \- *lemma* division_monoid.div_one
- \- *lemma* division_monoid.eq_inv_of_mul_eq_one_left
- \- *lemma* division_monoid.eq_inv_of_mul_eq_one_right
- \- *lemma* division_monoid.eq_of_div_eq_one
- \- *lemma* division_monoid.eq_of_one_div_eq_one_div
- \- *lemma* division_monoid.eq_one_div_of_mul_eq_one_left
- \- *lemma* division_monoid.eq_one_div_of_mul_eq_one_right
- \- *lemma* division_monoid.inv_div
- \- *lemma* division_monoid.inv_div_left
- \- *lemma* division_monoid.inv_eq_of_mul_eq_one_left
- \- *lemma* division_monoid.inv_eq_one
- \- *lemma* division_monoid.inv_ne_one
- \- *lemma* division_monoid.inv_one
- \- *lemma* division_monoid.one_div_div
- \- *lemma* division_monoid.one_div_mul_one_div_rev
- \- *lemma* division_monoid.one_div_one
- \- *lemma* division_monoid.one_div_one_div
- \- *lemma* division_monoid.one_eq_inv
- \- *lemma* eq_inv_of_mul_eq_one
- \+ *lemma* eq_inv_of_mul_eq_one_left
- \+ *lemma* eq_inv_of_mul_eq_one_right
- \- *lemma* eq_of_div_eq_one'
- \+ *lemma* eq_of_div_eq_one
- \+ *lemma* eq_of_one_div_eq_one_div
- \+ *lemma* eq_one_div_of_mul_eq_one_left
- \+ *lemma* eq_one_div_of_mul_eq_one_right
- \+/\- *lemma* inv_div'
- \+ *lemma* inv_div
- \+/\- *lemma* inv_div_inv
- \+ *lemma* inv_div_left
- \+ *lemma* inv_eq_of_mul_eq_one_left
- \+ *lemma* inv_eq_one
- \- *theorem* inv_eq_one
- \+/\- *lemma* inv_inv_div_inv
- \+ *lemma* inv_mul'
- \- *theorem* inv_mul'
- \+/\- *lemma* inv_mul_eq_div
- \+ *lemma* inv_ne_one
- \- *theorem* inv_ne_one
- \+ *lemma* inv_one
- \+ *lemma* mul_comm_div
- \+/\- *lemma* mul_div
- \+/\- *lemma* mul_div_cancel'''
- \- *lemma* mul_div_comm'
- \+/\- *lemma* mul_div_left_comm
- \+ *lemma* mul_div_mul_comm
- \+ *lemma* mul_div_right_comm
- \+/\- *lemma* mul_inv
- \+ *lemma* one_div_div
- \+ *lemma* one_div_mul_one_div
- \+ *lemma* one_div_mul_one_div_rev
- \+ *lemma* one_div_one
- \+ *lemma* one_div_one_div
- \+ *lemma* one_eq_inv
- \- *theorem* one_eq_inv
- \- *lemma* one_inv

Modified src/algebra/group/defs.lean
- \- *lemma* inv_eq_of_mul_eq_one

Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group/units.lean
- \- *lemma* units.inv_eq_of_mul_eq_one
- \+ *lemma* units.inv_eq_of_mul_eq_one_right

Modified src/algebra/group_power/basic.lean


Modified src/algebra/group_with_zero/basic.lean
- \- *lemma* div_div_div_comm₀
- \- *lemma* div_div_div_div_eq
- \- *lemma* div_div_eq_div_mul
- \- *lemma* div_div_eq_mul_div
- \- *lemma* div_eq_inv_mul
- \- *lemma* div_mul_comm'
- \- *lemma* div_mul_div_comm₀
- \- *lemma* div_mul_eq_div_mul_one_div
- \- *lemma* div_mul_eq_mul_div
- \- *lemma* div_mul_eq_mul_div_comm
- \- *lemma* div_one
- \- *lemma* div_right_comm
- \- *lemma* eq_inv_of_mul_left_eq_one
- \- *lemma* eq_inv_of_mul_right_eq_one
- \- *lemma* eq_of_div_eq_one
- \- *lemma* eq_of_one_div_eq_one_div
- \- *lemma* eq_one_div_of_mul_eq_one
- \- *lemma* eq_one_div_of_mul_eq_one_left
- \- *lemma* inv_div
- \- *lemma* inv_div_left
- \- *lemma* inv_eq_one₀
- \- *lemma* inv_one
- \- *lemma* mul_comm_div'
- \- *lemma* mul_div_comm
- \- *lemma* mul_div_right_comm
- \+/\- *lemma* mul_eq_mul_of_div_eq_div
- \- *lemma* mul_inv_rev₀
- \- *lemma* mul_inv₀
- \- *lemma* one_div_div
- \- *lemma* one_div_mul_one_div
- \- *lemma* one_div_mul_one_div_rev
- \- *lemma* one_div_one
- \- *lemma* one_div_one_div

Modified src/algebra/group_with_zero/power.lean


Modified src/algebra/hom/equiv.lean


Modified src/algebra/hom/group.lean


Modified src/algebra/module/basic.lean


Modified src/algebra/module/linear_map.lean


Modified src/algebra/order/field.lean


Modified src/algebra/order/lattice_group.lean
- \+/\- *lemma* lattice_ordered_comm_group.neg_one

Modified src/algebra/ring/basic.lean


Modified src/algebra/smul_with_zero.lean


Modified src/algebra/star/chsh.lean
- \+/\- *lemma* tsirelson_inequality.sqrt_two_inv_mul_self

Modified src/algebra/star/module.lean


Modified src/algebra/star/unitary.lean


Modified src/algebra/support.lean


Modified src/algebraic_topology/fundamental_groupoid/basic.lean


Modified src/analysis/ODE/picard_lindelof.lean


Modified src/analysis/asymptotics/asymptotic_equivalent.lean


Modified src/analysis/asymptotics/asymptotics.lean


Modified src/analysis/box_integral/box/subbox_induction.lean


Modified src/analysis/box_integral/partition/subbox_induction.lean


Modified src/analysis/calculus/deriv.lean


Modified src/analysis/calculus/fderiv.lean


Modified src/analysis/calculus/fderiv_measurable.lean


Modified src/analysis/complex/circle.lean


Modified src/analysis/complex/liouville.lean


Modified src/analysis/complex/polynomial.lean


Modified src/analysis/convex/gauge.lean


Modified src/analysis/convex/strict_convex_space.lean


Modified src/analysis/inner_product_space/basic.lean


Modified src/analysis/inner_product_space/projection.lean


Modified src/analysis/inner_product_space/rayleigh.lean


Modified src/analysis/mean_inequalities.lean


Modified src/analysis/normed_space/banach_steinhaus.lean


Modified src/analysis/normed_space/basic.lean


Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/pointwise.lean


Modified src/analysis/seminorm.lean


Modified src/analysis/special_functions/arsinh.lean


Modified src/analysis/special_functions/exp.lean


Modified src/analysis/special_functions/polynomials.lean


Modified src/analysis/special_functions/pow.lean


Modified src/analysis/special_functions/pow_deriv.lean


Modified src/analysis/special_functions/trigonometric/arctan.lean


Modified src/analysis/special_functions/trigonometric/complex.lean


Modified src/analysis/specific_limits/basic.lean


Modified src/analysis/specific_limits/normed.lean


Modified src/data/complex/exponential.lean


Modified src/data/list/big_operators.lean


Modified src/data/nat/modeq.lean


Modified src/data/nat/totient.lean


Modified src/data/polynomial/field_division.lean


Modified src/data/rat/cast.lean


Modified src/data/rat/order.lean


Modified src/data/real/cau_seq.lean


Modified src/data/real/cau_seq_completion.lean


Modified src/data/real/ennreal.lean
- \- *lemma* ennreal.eq_inv_of_mul_eq_one
- \+ *lemma* ennreal.eq_inv_of_mul_eq_one_left

Modified src/data/real/hyperreal.lean


Modified src/data/real/nnreal.lean


Modified src/data/real/pi/bounds.lean


Modified src/data/real/pi/wallis.lean


Modified src/data/set/pointwise.lean


Modified src/deprecated/group.lean
- \- *lemma* is_add_group_hom.map_sub
- \+ *lemma* is_group_hom.map_div

Modified src/deprecated/subfield.lean


Modified src/deprecated/subgroup.lean


Modified src/dynamics/circle/rotation_number/translation_number.lean


Modified src/field_theory/adjoin.lean


Modified src/field_theory/minpoly.lean


Modified src/field_theory/ratfunc.lean


Modified src/field_theory/subfield.lean


Modified src/geometry/euclidean/basic.lean


Modified src/geometry/euclidean/oriented_angle.lean


Modified src/geometry/euclidean/triangle.lean


Modified src/group_theory/complement.lean


Modified src/group_theory/group_action/conj_act.lean


Modified src/group_theory/group_action/defs.lean


Modified src/group_theory/group_action/group.lean


Modified src/group_theory/nielsen_schreier.lean


Modified src/group_theory/order_of_element.lean


Modified src/group_theory/perm/cycle_type.lean


Modified src/group_theory/quotient_group.lean


Modified src/group_theory/schreier.lean


Modified src/group_theory/schur_zassenhaus.lean


Modified src/group_theory/subgroup/basic.lean


Modified src/group_theory/submonoid/inverses.lean


Modified src/group_theory/submonoid/pointwise.lean


Modified src/group_theory/transfer.lean


Modified src/linear_algebra/affine_space/ordered.lean


Modified src/linear_algebra/affine_space/slope.lean


Modified src/linear_algebra/alternating.lean
- \+/\- *lemma* alternating_map.map_swap

Modified src/linear_algebra/finite_dimensional.lean


Modified src/linear_algebra/multilinear/basic.lean


Modified src/linear_algebra/quadratic_form/real.lean


Modified src/measure_theory/decomposition/lebesgue.lean


Modified src/measure_theory/function/uniform_integrable.lean


Modified src/measure_theory/integral/circle_integral.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/integral/mean_inequalities.lean


Modified src/measure_theory/measure/haar.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/bernoulli_polynomials.lean


Modified src/number_theory/class_number/admissible_abs.lean


Modified src/number_theory/liouville/liouville_constant.lean


Modified src/number_theory/liouville/liouville_with.lean


Modified src/number_theory/padics/hensel.lean


Modified src/number_theory/pythagorean_triples.lean


Modified src/number_theory/zsqrtd/basic.lean


Modified src/probability/cond_count.lean


Modified src/representation_theory/basic.lean


Modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* fractional_ideal.inv_one
- \- *lemma* fractional_ideal.one_inv

Modified src/ring_theory/derivation.lean


Modified src/ring_theory/fractional_ideal.lean
- \- *theorem* fractional_ideal.eq_one_div_of_mul_eq_one
- \+ *theorem* fractional_ideal.eq_one_div_of_mul_eq_one_right

Modified src/ring_theory/polynomial/eisenstein.lean


Modified src/ring_theory/power_series/basic.lean
- \+ *lemma* mv_power_series.inv_one
- \- *lemma* mv_power_series.one_inv
- \+ *lemma* power_series.inv_one
- \- *lemma* power_series.one_inv

Modified src/ring_theory/roots_of_unity.lean


Modified src/ring_theory/valuation/valuation_ring.lean


Modified src/tactic/abel.lean
- \+/\- *lemma* tactic.abel.unfold_sub

Modified src/tactic/cancel_denoms.lean


Modified src/topology/algebra/group.lean


Modified src/topology/algebra/order/basic.lean


Modified src/topology/algebra/uniform_group.lean


Modified src/topology/algebra/valued_field.lean


Modified src/topology/path_connected.lean


Modified test/integration.lean




## [2022-05-10 11:03:33](https://github.com/leanprover-community/mathlib/commit/e689611)
chore({data/{finset,set},order/filter}/pointwise): Reorganize files ([#14021](https://github.com/leanprover-community/mathlib/pull/14021))
Order the three files more similarly. The idea is to order things as:
* Arithmetic notation typeclasses, and lemmas that don't depend on algebraic structure for them:
  * `0` and `1`
  * `-` and `⁻¹`
  * `+` and `*`
  * `-` and `/`
* monoid-like instances, interleaved with the corresponding lemmas (some of them are used for the instances themselves, and more will be in the future)
* `•`
* `-ᵥ`
* scalar instances
#### Estimated changes
Modified src/data/finset/pointwise.lean
- \+/\- *lemma* finset.coe_pow
- \+/\- *lemma* finset.image_mul_right'
- \+/\- *lemma* finset.image_mul_right
- \+/\- *lemma* finset.preimage_mul_left_one'
- \+/\- *lemma* finset.preimage_mul_left_one
- \+/\- *lemma* finset.preimage_mul_right_one'
- \+/\- *lemma* finset.preimage_mul_right_one

Modified src/data/set/pointwise.lean
- \+/\- *lemma* set.Inter_inv
- \+/\- *lemma* set.Union_inv
- \+/\- *lemma* set.compl_inv
- \+/\- *lemma* set.empty_pow
- \+/\- *def* set.fintype_mul
- \+/\- *lemma* set.image_mul_left'
- \+/\- *lemma* set.image_mul_left
- \+/\- *lemma* set.image_mul_right'
- \+/\- *lemma* set.image_mul_right
- \+/\- *lemma* set.inter_inv
- \+/\- *lemma* set.inv_preimage
- \+/\- *lemma* set.mem_inv
- \+/\- *lemma* set.mul_univ
- \+/\- *lemma* set.pow_mem_pow
- \+/\- *lemma* set.pow_subset_pow
- \+/\- *lemma* set.preimage_mul_left_one'
- \+/\- *lemma* set.preimage_mul_left_one
- \+/\- *lemma* set.preimage_mul_left_singleton
- \+/\- *lemma* set.preimage_mul_right_one'
- \+/\- *lemma* set.preimage_mul_right_one
- \+/\- *lemma* set.preimage_mul_right_singleton
- \- *def* set.singleton_hom
- \+/\- *lemma* set.subset_mul_left
- \+/\- *lemma* set.subset_mul_right
- \+/\- *lemma* set.union_inv
- \+/\- *lemma* set.univ_mul
- \+/\- *lemma* set.univ_mul_univ

Modified src/order/filter/pointwise.lean
- \+/\- *lemma* filter.comap_mul_comap_le
- \+/\- *lemma* filter.map_inv'
- \+ *lemma* filter.pow_mem_pow
- \+/\- *lemma* filter.tendsto.div_div
- \+/\- *lemma* filter.tendsto.inv_inv



## [2022-05-10 11:03:32](https://github.com/leanprover-community/mathlib/commit/45d2b52)
chore(analysis/normed_space/basic): reorder the `restrict_scalars` definitions ([#13995](https://github.com/leanprover-community/mathlib/pull/13995))
This also update the docstrings to make `normed_space.restrict_scalars` even scarier.
The instances here themselves haven't actually changed.
#### Estimated changes
Modified src/analysis/normed_space/basic.lean




## [2022-05-10 11:03:31](https://github.com/leanprover-community/mathlib/commit/91489ac)
feat(algebra/module/submodule_bilinear): add `submodule.map₂`, generalizing `submodule.has_mul` ([#13709](https://github.com/leanprover-community/mathlib/pull/13709))
The motivation here is to be able to talk about combinations of submodules under other bilinear maps, such as the tensor product. This unifies the definitions of and lemmas about `submodule.has_mul` and `submodule.has_scalar'`.
The lemmas about `submodule.map₂` are copied verbatim from those for `mul`, and then adjusted slightly replacing `mul_zero` with `linear_map.map_zero` etc. I've then replaced the lemmas about `smul` with the `map₂` proofs where possible.
The lemmas about finiteness weren't possible to copy this way, as the proofs about `finset` multiplication are not generalized in a similar way. Someone else can copy these in a future PR.
This also adds `set.image2_eq_Union` to match `set.image_eq_Union`, and removes `submodule.union_eq_smul_set` which is neither about submodules nor about `union`, and instead is really just a copy of `set.image_eq_Union`
#### Estimated changes
Modified src/algebra/algebra/operations.lean
- \+/\- *theorem* submodule.bot_mul
- \+/\- *theorem* submodule.mul_bot
- \+/\- *theorem* submodule.mul_le
- \+/\- *theorem* submodule.mul_le_mul
- \+/\- *theorem* submodule.mul_le_mul_left
- \+/\- *theorem* submodule.mul_le_mul_right
- \+/\- *theorem* submodule.mul_mem_mul
- \+/\- *theorem* submodule.mul_sup
- \+/\- *theorem* submodule.span_mul_span
- \+/\- *theorem* submodule.sup_mul

Added src/algebra/module/submodule_bilinear.lean
- \+ *theorem* submodule.apply_mem_map₂
- \+ *lemma* submodule.image2_subset_map₂
- \+ *def* submodule.map₂
- \+ *theorem* submodule.map₂_bot_left
- \+ *theorem* submodule.map₂_bot_right
- \+ *lemma* submodule.map₂_eq_span_image2
- \+ *theorem* submodule.map₂_le
- \+ *theorem* submodule.map₂_le_map₂
- \+ *theorem* submodule.map₂_le_map₂_left
- \+ *theorem* submodule.map₂_le_map₂_right
- \+ *theorem* submodule.map₂_span_span
- \+ *theorem* submodule.map₂_sup_left
- \+ *theorem* submodule.map₂_sup_right
- \+ *lemma* submodule.map₂_supr_left
- \+ *lemma* submodule.map₂_supr_right

Modified src/data/set/lattice.lean
- \+ *lemma* set.image2_eq_Union

Modified src/ring_theory/henselian.lean


Modified src/ring_theory/ideal/operations.lean
- \+/\- *theorem* submodule.bot_smul
- \+/\- *theorem* submodule.smul_bot
- \+/\- *theorem* submodule.smul_le
- \+/\- *theorem* submodule.smul_mem_smul
- \+/\- *theorem* submodule.smul_mono
- \+/\- *theorem* submodule.smul_mono_left
- \+/\- *theorem* submodule.smul_mono_right
- \+/\- *theorem* submodule.smul_sup
- \+/\- *lemma* submodule.span_smul_eq
- \+/\- *theorem* submodule.sup_smul
- \- *lemma* submodule.union_eq_smul_set

Modified src/ring_theory/noetherian.lean
- \+ *theorem* submodule.fg.map₂
- \+/\- *theorem* submodule.fg.mul



## [2022-05-10 08:56:43](https://github.com/leanprover-community/mathlib/commit/34f29db)
feat(topology/algebra/group): Division is an open map ([#14028](https://github.com/leanprover-community/mathlib/pull/14028))
A few missing lemmas about division in topological groups.
#### Estimated changes
Modified src/topology/algebra/group.lean
- \+/\- *lemma* inv_closure
- \+/\- *lemma* is_closed.inv
- \+ *lemma* is_closed_map_div_left
- \+ *lemma* is_closed_map_inv
- \+/\- *lemma* is_compact.inv
- \+ *lemma* is_open.closure_div
- \+/\- *lemma* is_open.closure_mul
- \+ *lemma* is_open.div_closure
- \+ *lemma* is_open.div_left
- \+ *lemma* is_open.div_right
- \+/\- *lemma* is_open.inv
- \+/\- *lemma* is_open.mul_closure
- \+/\- *lemma* is_open.mul_left
- \+/\- *lemma* is_open.mul_right
- \+ *lemma* is_open_map_div_left
- \+ *lemma* is_open_map_inv
- \+/\- *lemma* nhds_translation_div
- \+ *lemma* subset_interior_div
- \+ *lemma* subset_interior_div_left
- \+ *lemma* subset_interior_div_right
- \+/\- *lemma* subset_interior_mul
- \+/\- *lemma* subset_interior_mul_left
- \+/\- *lemma* subset_interior_mul_right



## [2022-05-10 08:56:42](https://github.com/leanprover-community/mathlib/commit/c892622)
move(order/synonym): Group `order_dual` and `lex` ([#13769](https://github.com/leanprover-community/mathlib/pull/13769))
Move `to_dual`, `of_dual`, `to_lex`, `of_lex` to a new file `order.synonym`. This does not change the import tree, because `order.lexicographic` had slightly higher imports than `order.order_dual`, but those weren't used for `lex` itself.
#### Estimated changes
Modified src/algebra/group/type_tags.lean


Modified src/algebra/order/group.lean


Modified src/algebra/order/rearrangement.lean


Modified src/analysis/convex/function.lean


Modified src/data/finset/lattice.lean


Modified src/data/psigma/order.lean


Modified src/data/sigma/order.lean


Modified src/data/sum/order.lean


Modified src/group_theory/group_action/fixing_subgroup.lean


Modified src/order/compare.lean


Modified src/order/galois_connection.lean


Modified src/order/lexicographic.lean
- \- *def* lex
- \- *def* of_lex
- \- *lemma* of_lex_inj
- \- *lemma* of_lex_symm_eq
- \- *lemma* of_lex_to_lex
- \- *def* to_lex
- \- *lemma* to_lex_inj
- \- *lemma* to_lex_of_lex
- \- *lemma* to_lex_symm_eq

Modified src/order/max.lean


Deleted src/order/order_dual.lean
- \- *lemma* order_dual.le_to_dual
- \- *lemma* order_dual.lt_to_dual
- \- *def* order_dual.of_dual
- \- *lemma* order_dual.of_dual_inj
- \- *lemma* order_dual.of_dual_le_of_dual
- \- *lemma* order_dual.of_dual_lt_of_dual
- \- *lemma* order_dual.of_dual_symm_eq
- \- *lemma* order_dual.of_dual_to_dual
- \- *def* order_dual.to_dual
- \- *lemma* order_dual.to_dual_inj
- \- *lemma* order_dual.to_dual_le
- \- *lemma* order_dual.to_dual_le_to_dual
- \- *lemma* order_dual.to_dual_lt
- \- *lemma* order_dual.to_dual_lt_to_dual
- \- *lemma* order_dual.to_dual_of_dual
- \- *lemma* order_dual.to_dual_symm_eq

Added src/order/synonym.lean
- \+ *def* lex
- \+ *def* of_lex
- \+ *lemma* of_lex_inj
- \+ *lemma* of_lex_symm_eq
- \+ *lemma* of_lex_to_lex
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
- \+ *def* to_lex
- \+ *lemma* to_lex_inj
- \+ *lemma* to_lex_of_lex
- \+ *lemma* to_lex_symm_eq



## [2022-05-10 08:02:09](https://github.com/leanprover-community/mathlib/commit/37c691f)
feat(analysis/convex/*): Convexity and subtraction ([#14015](https://github.com/leanprover-community/mathlib/pull/14015))
Now that we have a fair bit more pointwise operations on `set`, a few results can be (re)written using them. For example, existing lemmas about `add` and `neg` can be combined to give lemmas about `sub`.
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.affine_image
- \- *lemma* convex.neg_preimage
- \+/\- *lemma* convex.sub
- \+/\- *lemma* convex.translate
- \+ *lemma* convex.vadd

Modified src/analysis/convex/function.lean
- \+ *lemma* concave_on.add_strict_concave_on
- \+ *lemma* concave_on.sub
- \+ *lemma* concave_on.sub_strict_convex_on
- \+ *lemma* convex_on.add_strict_convex_on
- \+ *lemma* convex_on.sub
- \+ *lemma* convex_on.sub_strict_concave_on
- \+ *lemma* strict_concave_on.add_concave_on
- \+ *lemma* strict_concave_on.sub
- \+ *lemma* strict_concave_on.sub_convex_on
- \+ *lemma* strict_convex_on.add_convex_on
- \+ *lemma* strict_convex_on.sub
- \+ *lemma* strict_convex_on.sub_concave_on

Modified src/analysis/convex/star.lean
- \+/\- *lemma* star_convex.neg
- \- *lemma* star_convex.neg_preimage
- \+ *lemma* star_convex.sub'
- \+/\- *lemma* star_convex.sub

Modified src/analysis/convex/strict.lean
- \+/\- *lemma* strict_convex.neg
- \- *lemma* strict_convex.neg_preimage
- \+ *lemma* strict_convex.sub



## [2022-05-10 05:20:28](https://github.com/leanprover-community/mathlib/commit/5650366)
chore(.github/workflows): disable merge conflicts bot for now ([#14057](https://github.com/leanprover-community/mathlib/pull/14057))
#### Estimated changes
Deleted .github/workflows/merge_conflicts.yml




## [2022-05-10 05:20:27](https://github.com/leanprover-community/mathlib/commit/153b20f)
chore(scripts): update nolints.txt ([#14056](https://github.com/leanprover-community/mathlib/pull/14056))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-05-10 05:20:26](https://github.com/leanprover-community/mathlib/commit/b17070d)
fix(data/real/ennreal): style and golfing ([#14055](https://github.com/leanprover-community/mathlib/pull/14055))
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+/\- *lemma* ennreal.coe_inv_two
- \+/\- *lemma* ennreal.inv_one
- \+/\- *lemma* ennreal.mul_left_mono
- \+/\- *lemma* ennreal.mul_right_mono



## [2022-05-10 05:20:26](https://github.com/leanprover-community/mathlib/commit/87069e9)
chore(ring_theory/hahn_series): golf a proof ([#14054](https://github.com/leanprover-community/mathlib/pull/14054))
#### Estimated changes
Modified src/ring_theory/hahn_series.lean




## [2022-05-10 03:35:32](https://github.com/leanprover-community/mathlib/commit/c5e0299)
feat(group_theory/subsemigroup/{center, centralizer}): define center and centralizer as subsemigroups ([#13627](https://github.com/leanprover-community/mathlib/pull/13627))
This defines the center and centralizers for semigroups. This is necessary so that we can do the same for non-unital semirings. 
- [x] depends on: [#12112](https://github.com/leanprover-community/mathlib/pull/12112) 
- [x] depends on: [#13903](https://github.com/leanprover-community/mathlib/pull/13903)
#### Estimated changes
Modified src/group_theory/submonoid/center.lean
- \+ *lemma* add_submonoid.center_to_add_subsemigroup
- \+ *lemma* submonoid.center_to_subsemigroup

Modified src/group_theory/submonoid/centralizer.lean
- \+ *lemma* add_submonoid.centralizer_to_add_subsemigroup
- \+ *lemma* submonoid.centralizer_to_subsemigroup

Modified src/group_theory/subsemigroup/center.lean
- \+ *def* subsemigroup.center
- \+ *lemma* subsemigroup.center_eq_top
- \+ *lemma* subsemigroup.coe_center
- \+ *lemma* subsemigroup.mem_center_iff

Modified src/group_theory/subsemigroup/centralizer.lean
- \+ *def* subsemigroup.centralizer
- \+ *lemma* subsemigroup.centralizer_le
- \+ *lemma* subsemigroup.centralizer_univ
- \+ *lemma* subsemigroup.coe_centralizer
- \+ *lemma* subsemigroup.mem_centralizer_iff



## [2022-05-09 20:46:25](https://github.com/leanprover-community/mathlib/commit/260d5ce)
feat(model_theory/semantics): Realizing restricted terms and formulas ([#14014](https://github.com/leanprover-community/mathlib/pull/14014))
Shows that realizing a restricted term or formula gives the same value as the unrestricted version.
#### Estimated changes
Modified src/data/set/basic.lean
- \+ *lemma* set.inclusion_comp_inclusion

Modified src/model_theory/semantics.lean
- \+ *lemma* first_order.language.bounded_formula.realize_restrict_free_var
- \+ *lemma* first_order.language.term.realize_restrict_var
- \+ *lemma* first_order.language.term.realize_restrict_var_left



## [2022-05-09 16:57:31](https://github.com/leanprover-community/mathlib/commit/98f2779)
refactor(number_theory/legendre_symbol/*): move section `general` from `quadratic_char.lean` into new file `auxiliary.lean` ([#14027](https://github.com/leanprover-community/mathlib/pull/14027))
This is a purely administrative step (in preparation of adding more files that may need some of the auxiliary results).
We move the collection of auxiliary results that constitute `section general` of `quadratic_char.lean` to a new file `auxiliary.lean` (and change the `import`s of `quadratic_char.lean` accordingly).
This new file is meant as a temporary place for these auxiliary results; when the refactor of `quadratic_reciprocity` is finished, they will be moved to appropriate files in mathlib.
#### Estimated changes
Added src/number_theory/legendre_symbol/auxiliary.lean
- \+ *lemma* finite_field.even_card_iff_char_two
- \+ *lemma* finite_field.even_card_of_char_two
- \+ *lemma* finite_field.exists_nonsquare
- \+ *lemma* finite_field.is_square_iff
- \+ *lemma* finite_field.is_square_of_char_two
- \+ *lemma* finite_field.neg_ne_self_of_char_ne_two
- \+ *lemma* finite_field.neg_one_ne_one_of_char_ne_two
- \+ *lemma* finite_field.odd_card_of_char_ne_two
- \+ *lemma* finite_field.pow_dichotomy
- \+ *lemma* finite_field.unit_is_square_iff
- \+ *lemma* is_square_of_char_two'
- \+ *lemma* nat.odd_mod_four_iff

Modified src/number_theory/legendre_symbol/quadratic_char.lean
- \- *lemma* finite_field.even_card_iff_char_two
- \- *lemma* finite_field.even_card_of_char_two
- \- *lemma* finite_field.exists_nonsquare
- \- *lemma* finite_field.is_square_iff
- \- *lemma* finite_field.is_square_of_char_two
- \- *lemma* finite_field.neg_ne_self_of_char_ne_two
- \- *lemma* finite_field.neg_one_ne_one_of_char_ne_two
- \- *lemma* finite_field.odd_card_of_char_ne_two
- \- *lemma* finite_field.pow_dichotomy
- \- *lemma* finite_field.unit_is_square_iff
- \- *lemma* is_square_of_char_two'
- \- *lemma* nat.odd_mod_four_iff



## [2022-05-09 14:40:50](https://github.com/leanprover-community/mathlib/commit/31af0e8)
feat(model_theory/satisfiability): Definition of categorical theories ([#14038](https://github.com/leanprover-community/mathlib/pull/14038))
Defines that a first-order theory is `κ`-categorical when all models of cardinality `κ` are isomorphic.
Shows that all theories in the empty language are `κ`-categorical for all cardinals `κ`.
#### Estimated changes
Modified src/model_theory/satisfiability.lean
- \+ *def* cardinal.categorical
- \+ *theorem* cardinal.empty_Theory_categorical



## [2022-05-09 14:40:49](https://github.com/leanprover-community/mathlib/commit/5d8b432)
feat(model_theory/language_map): Cardinality of languages with constants ([#13981](https://github.com/leanprover-community/mathlib/pull/13981))
`first_order.language.card_with_constants` shows that the cardinality of `L[[A]]` is `L.card + # A`.
#### Estimated changes
Modified src/logic/equiv/basic.lean
- \+ *def* equiv.sigma_nat_succ

Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.card_mk₂
- \+ *lemma* first_order.language.constants_mk₂
- \+ *lemma* first_order.sequence₂.lift_mk
- \+ *lemma* first_order.sequence₂.sum_card
- \+/\- *def* first_order.sequence₂

Modified src/model_theory/bundled.lean


Modified src/model_theory/language_map.lean
- \+ *lemma* first_order.language.card_constants_on
- \+ *lemma* first_order.language.card_with_constants
- \+/\- *def* first_order.language.constants_on
- \+/\- *lemma* first_order.language.constants_on_constants
- \- *def* first_order.language.constants_on_functions

Modified src/model_theory/substructures.lean


Modified src/set_theory/cardinal/basic.lean
- \+ *theorem* cardinal.sum_nat_eq_add_sum_succ



## [2022-05-09 14:40:47](https://github.com/leanprover-community/mathlib/commit/4eb76a7)
refactor(set_theory/ordinal/arithmetic): Rename theorems to match `nat.log` API ([#12733](https://github.com/leanprover-community/mathlib/pull/12733))
We match the API for `ordinal.log` with that of `nat.log`.
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean
- \- *theorem* ordinal.le_log
- \+/\- *def* ordinal.log
- \- *theorem* ordinal.log_le_log
- \- *theorem* ordinal.log_lt
- \+ *theorem* ordinal.log_mono_right
- \- *theorem* ordinal.log_not_one_lt
- \+ *theorem* ordinal.log_of_left_le_one
- \+ *theorem* ordinal.log_of_not_one_lt_left
- \- *theorem* ordinal.log_one
- \+ *theorem* ordinal.log_one_left
- \+ *theorem* ordinal.log_one_right
- \- *theorem* ordinal.log_zero
- \+ *lemma* ordinal.log_zero_left
- \+ *theorem* ordinal.log_zero_right
- \+ *theorem* ordinal.lt_opow_iff_log_lt
- \- *theorem* ordinal.lt_opow_succ_log
- \+ *theorem* ordinal.lt_opow_succ_log_self
- \+/\- *theorem* ordinal.mod_opow_log_lt_self
- \+ *theorem* ordinal.opow_le_iff_le_log
- \- *theorem* ordinal.opow_log_le
- \+ *theorem* ordinal.opow_log_le_self
- \+/\- *lemma* ordinal.opow_mul_add_pos
- \+ *theorem* ordinal.zero_le_one

Modified src/set_theory/ordinal/principal.lean




## [2022-05-09 12:58:30](https://github.com/leanprover-community/mathlib/commit/00cec55)
feat(linear_algebra/affine_space/independent): add characterisation of affine independence for modules ([#14043](https://github.com/leanprover-community/mathlib/pull/14043))
#### Estimated changes
Modified src/linear_algebra/affine_space/combination.lean
- \+ *lemma* finset.weighted_vsub_eq_linear_combination

Modified src/linear_algebra/affine_space/independent.lean
- \+ *lemma* affine_independent_iff



## [2022-05-09 12:58:29](https://github.com/leanprover-community/mathlib/commit/1fef515)
chore(analysis/normed_space/basic): add short-circuit instance to obtain module structure over reals ([#14013](https://github.com/leanprover-community/mathlib/pull/14013))
#### Estimated changes
Modified src/algebra/module/pi.lean




## [2022-05-09 12:58:28](https://github.com/leanprover-community/mathlib/commit/4da939b)
feat(probability_theory/cond_count): use the counting measure to describe probability in the elementary sense ([#13484](https://github.com/leanprover-community/mathlib/pull/13484))
#### Estimated changes
Added src/probability/cond_count.lean
- \+ *def* probability_theory.cond_count
- \+ *lemma* probability_theory.cond_count_add_compl_eq
- \+ *lemma* probability_theory.cond_count_compl
- \+ *lemma* probability_theory.cond_count_disjoint_union
- \+ *lemma* probability_theory.cond_count_empty
- \+ *lemma* probability_theory.cond_count_empty_meas
- \+ *lemma* probability_theory.cond_count_eq_one_of
- \+ *lemma* probability_theory.cond_count_eq_zero_iff
- \+ *lemma* probability_theory.cond_count_inter'
- \+ *lemma* probability_theory.cond_count_inter
- \+ *lemma* probability_theory.cond_count_inter_self
- \+ *lemma* probability_theory.cond_count_is_probability_measure
- \+ *lemma* probability_theory.cond_count_self
- \+ *lemma* probability_theory.cond_count_singleton
- \+ *lemma* probability_theory.cond_count_union
- \+ *lemma* probability_theory.cond_count_univ
- \+ *lemma* probability_theory.finite_of_cond_count_ne_zero
- \+ *lemma* probability_theory.pred_true_of_cond_count_eq_one

Modified src/probability/conditional.lean
- \+ *lemma* probability_theory.cond_add_cond_compl_eq
- \+/\- *lemma* probability_theory.cond_apply
- \+ *lemma* probability_theory.cond_cond_eq_cond_inter'
- \+/\- *lemma* probability_theory.cond_cond_eq_cond_inter
- \+ *lemma* probability_theory.cond_empty
- \+/\- *theorem* probability_theory.cond_eq_inv_mul_cond_mul
- \+ *lemma* probability_theory.cond_inter_self
- \+ *lemma* probability_theory.cond_mul_eq_inter'
- \+/\- *lemma* probability_theory.cond_mul_eq_inter
- \+/\- *lemma* probability_theory.cond_pos_of_inter_ne_zero



## [2022-05-09 12:18:53](https://github.com/leanprover-community/mathlib/commit/5397ac0)
chore(ring_theory/hahn_series): remove redundant instances ([#14045](https://github.com/leanprover-community/mathlib/pull/14045))
Both of these instances can be proved `by apply_instance`
#### Estimated changes
Modified src/ring_theory/hahn_series.lean




## [2022-05-09 11:26:03](https://github.com/leanprover-community/mathlib/commit/c43486e)
feat(category_theory/limits): allow (co)limits over lower universes in algebraic categories ([#13990](https://github.com/leanprover-community/mathlib/pull/13990))
I'm concerned about the new universe annotations required in places. It was not so impossible to add them when proofs broke, but the proofs might have been hard to construct in the first place ....
#### Estimated changes
Modified src/algebra/category/Algebra/limits.lean
- \+/\- *def* Algebra.has_limits.limit_cone
- \+/\- *def* Algebra.has_limits.limit_cone_is_limit
- \+/\- *def* Algebra.limit_π_alg_hom
- \+/\- *def* Algebra.sections_subalgebra

Modified src/algebra/category/FinVect/limits.lean


Modified src/algebra/category/Group/filtered_colimits.lean
- \+/\- *abbreviation* CommGroup.filtered_colimits.G
- \+/\- *abbreviation* Group.filtered_colimits.G

Modified src/algebra/category/Group/limits.lean
- \+/\- *def* AddCommGroup.kernel_iso_ker
- \+/\- *def* CommGroup.forget₂_CommMon_preserves_limits_aux
- \+/\- *def* CommGroup.limit_cone
- \+/\- *def* CommGroup.limit_cone_is_limit
- \+/\- *def* Group.limit_cone
- \+/\- *def* Group.limit_cone_is_limit

Modified src/algebra/category/Module/basic.lean
- \+/\- *lemma* Module.coe_of

Modified src/algebra/category/Module/filtered_colimits.lean


Modified src/algebra/category/Module/limits.lean
- \+/\- *def* Module.forget₂_AddCommGroup_preserves_limits_aux
- \+/\- *def* Module.has_limits.limit_cone
- \+/\- *def* Module.has_limits.limit_cone_is_limit
- \+/\- *def* Module.sections_submodule

Modified src/algebra/category/Module/products.lean


Modified src/algebra/category/Mon/filtered_colimits.lean
- \+/\- *abbreviation* CommMon.filtered_colimits.M
- \+/\- *abbreviation* Mon.filtered_colimits.M

Modified src/algebra/category/Mon/limits.lean
- \+/\- *def* CommMon.limit_cone
- \+/\- *def* CommMon.limit_cone_is_limit
- \+/\- *def* Mon.has_limits.limit_cone
- \+/\- *def* Mon.has_limits.limit_cone_is_limit
- \+/\- *def* Mon.limit_π_monoid_hom
- \+/\- *def* Mon.sections_submonoid

Modified src/algebra/category/Ring/filtered_colimits.lean
- \+/\- *abbreviation* SemiRing.filtered_colimits.R

Modified src/algebra/category/Ring/limits.lean
- \+/\- *def* CommRing.forget₂_CommSemiRing_preserves_limits_aux
- \+/\- *def* CommRing.limit_cone
- \+/\- *def* CommRing.limit_cone_is_limit
- \+/\- *def* CommSemiRing.limit_cone
- \+/\- *def* CommSemiRing.limit_cone_is_limit
- \+/\- *def* Ring.forget₂_AddCommGroup_preserves_limits_aux
- \+/\- *def* Ring.limit_cone
- \+/\- *def* Ring.limit_cone_is_limit
- \+/\- *def* Ring.sections_subring
- \+/\- *def* SemiRing.forget₂_AddCommMon_preserves_limits_aux
- \+/\- *def* SemiRing.forget₂_Mon_preserves_limits_aux
- \+/\- *def* SemiRing.has_limits.limit_cone
- \+/\- *def* SemiRing.has_limits.limit_cone_is_limit
- \+/\- *def* SemiRing.limit_π_ring_hom
- \+/\- *def* SemiRing.sections_subsemiring

Modified src/algebraic_geometry/locally_ringed_space/has_colimits.lean


Modified src/algebraic_geometry/open_immersion.lean


Modified src/algebraic_topology/fundamental_groupoid/product.lean


Modified src/category_theory/category/Cat/limit.lean


Modified src/category_theory/limits/concrete_category.lean


Modified src/category_theory/limits/filtered_colimit_commutes_finite_limit.lean


Modified src/category_theory/limits/final.lean


Modified src/category_theory/limits/preserves/filtered.lean


Modified src/category_theory/limits/types.lean
- \+ *lemma* category_theory.limits.types.colimit.w_apply'
- \+/\- *lemma* category_theory.limits.types.colimit.w_apply
- \+ *lemma* category_theory.limits.types.colimit.ι_desc_apply'
- \+/\- *lemma* category_theory.limits.types.colimit.ι_desc_apply
- \+ *lemma* category_theory.limits.types.colimit.ι_map_apply'
- \+/\- *lemma* category_theory.limits.types.colimit.ι_map_apply
- \+/\- *def* category_theory.limits.types.colimit_cocone
- \+/\- *def* category_theory.limits.types.colimit_cocone_is_colimit
- \+/\- *lemma* category_theory.limits.types.colimit_eq
- \+/\- *def* category_theory.limits.types.colimit_equiv_quot
- \+/\- *lemma* category_theory.limits.types.colimit_equiv_quot_apply
- \+/\- *lemma* category_theory.limits.types.colimit_equiv_quot_symm_apply
- \+/\- *def* category_theory.limits.types.is_limit_equiv_sections
- \+/\- *lemma* category_theory.limits.types.jointly_surjective'
- \+/\- *lemma* category_theory.limits.types.jointly_surjective
- \+ *lemma* category_theory.limits.types.limit.lift_π_apply'
- \+/\- *lemma* category_theory.limits.types.limit.lift_π_apply
- \+ *lemma* category_theory.limits.types.limit.map_π_apply'
- \+/\- *lemma* category_theory.limits.types.limit.map_π_apply
- \+/\- *def* category_theory.limits.types.limit.mk
- \+ *lemma* category_theory.limits.types.limit.w_apply'
- \+/\- *lemma* category_theory.limits.types.limit.w_apply
- \+ *lemma* category_theory.limits.types.limit.π_mk'
- \+/\- *lemma* category_theory.limits.types.limit.π_mk
- \+/\- *def* category_theory.limits.types.limit_cone
- \+/\- *def* category_theory.limits.types.limit_cone_is_limit
- \+/\- *def* category_theory.limits.types.limit_equiv_sections
- \+/\- *lemma* category_theory.limits.types.limit_equiv_sections_apply
- \+ *lemma* category_theory.limits.types.limit_equiv_sections_symm_apply'
- \+/\- *lemma* category_theory.limits.types.limit_equiv_sections_symm_apply
- \+ *lemma* category_theory.limits.types.limit_ext'
- \+/\- *lemma* category_theory.limits.types.limit_ext
- \+ *lemma* category_theory.limits.types.limit_ext_iff'
- \+/\- *lemma* category_theory.limits.types.limit_ext_iff
- \+/\- *def* category_theory.limits.types.quot.rel
- \+/\- *def* category_theory.limits.types.quot

Modified src/category_theory/sites/sheaf_of_types.lean


Modified src/topology/category/CompHaus/default.lean
- \+/\- *def* CompHaus.limit_cone
- \+/\- *def* CompHaus.limit_cone_is_limit

Modified src/topology/category/Profinite/cofiltered_limit.lean


Modified src/topology/category/Profinite/default.lean


Modified src/topology/category/Top/limits.lean
- \+/\- *lemma* Top.coinduced_of_is_colimit
- \+/\- *def* Top.colimit_cocone
- \+/\- *def* Top.colimit_cocone_is_colimit
- \+/\- *lemma* Top.colimit_is_open_iff
- \+/\- *lemma* Top.colimit_topology
- \+/\- *lemma* Top.induced_of_is_limit
- \+/\- *def* Top.limit_cone
- \+/\- *def* Top.limit_cone_infi
- \+/\- *def* Top.limit_cone_infi_is_limit
- \+/\- *def* Top.limit_cone_is_limit
- \+/\- *lemma* Top.limit_topology
- \+/\- *def* Top.pi_fan
- \+/\- *def* Top.pi_fan_is_limit
- \+/\- *def* Top.pi_iso_pi
- \+/\- *lemma* Top.pi_iso_pi_hom_apply
- \+/\- *lemma* Top.pi_iso_pi_inv_π
- \+/\- *lemma* Top.pi_iso_pi_inv_π_apply
- \+/\- *abbreviation* Top.pi_π
- \+/\- *def* Top.sigma_cofan
- \+/\- *def* Top.sigma_cofan_is_colimit
- \+/\- *def* Top.sigma_iso_sigma
- \+/\- *lemma* Top.sigma_iso_sigma_hom_ι
- \+/\- *lemma* Top.sigma_iso_sigma_hom_ι_apply
- \+/\- *lemma* Top.sigma_iso_sigma_inv_apply
- \+/\- *abbreviation* Top.sigma_ι

Modified src/topology/gluing.lean


Modified src/topology/sheaves/local_predicate.lean


Modified src/topology/sheaves/sheaf_condition/unique_gluing.lean


Modified src/topology/sheaves/stalks.lean




## [2022-05-09 11:25:59](https://github.com/leanprover-community/mathlib/commit/ad244dd)
feat(ring_theory/dedekind_domain/adic_valuation): extend valuation ([#13462](https://github.com/leanprover-community/mathlib/pull/13462))
We extend the `v`-adic valuation on a Dedekind domain `R` to its field of fractions `K` and prove some basic properties. We define the completion of `K` with respect to this valuation, as well as its ring of integers, and provide some topological instances.
#### Estimated changes
Modified src/ring_theory/dedekind_domain/adic_valuation.lean
- \+ *def* is_dedekind_domain.height_one_spectrum.adic_completion
- \+ *def* is_dedekind_domain.height_one_spectrum.adic_completion_integers
- \+ *def* is_dedekind_domain.height_one_spectrum.adic_valued
- \+ *lemma* is_dedekind_domain.height_one_spectrum.adic_valued_apply
- \+ *def* is_dedekind_domain.height_one_spectrum.valuation
- \+ *lemma* is_dedekind_domain.height_one_spectrum.valuation_def
- \+ *lemma* is_dedekind_domain.height_one_spectrum.valuation_exists_uniformizer
- \+ *lemma* is_dedekind_domain.height_one_spectrum.valuation_le_one
- \+ *lemma* is_dedekind_domain.height_one_spectrum.valuation_lt_one_iff_dvd
- \+ *lemma* is_dedekind_domain.height_one_spectrum.valuation_of_algebra_map
- \+ *lemma* is_dedekind_domain.height_one_spectrum.valuation_of_mk'
- \+ *lemma* is_dedekind_domain.height_one_spectrum.valuation_uniformizer_ne_zero
- \+ *lemma* is_dedekind_domain.height_one_spectrum.valued_adic_completion_def



## [2022-05-09 09:20:59](https://github.com/leanprover-community/mathlib/commit/fc64096)
feat(topology/algebra/infinite_sum): summable on subtype iff ([#14032](https://github.com/leanprover-community/mathlib/pull/14032))
A summable version of the `has_sum` lemma previously (the `tsum` version is already present)
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* summable_subtype_iff_indicator



## [2022-05-09 09:20:58](https://github.com/leanprover-community/mathlib/commit/d55a654)
feat(order/*): Order constructions under `to_dual`/`of_dual` ([#13788](https://github.com/leanprover-community/mathlib/pull/13788))
A few missing lemmas about `of_dual` and `to_dual`.
#### Estimated changes
Modified src/data/finset/lattice.lean
- \+ *lemma* finset.map_of_dual_max
- \+ *lemma* finset.map_of_dual_min
- \+ *lemma* finset.map_to_dual_max
- \+ *lemma* finset.map_to_dual_min
- \- *lemma* finset.max'_eq_of_dual_min'
- \- *lemma* finset.min'_eq_of_dual_max'
- \+ *lemma* finset.of_dual_inf'
- \+ *lemma* finset.of_dual_inf
- \+ *lemma* finset.of_dual_max'
- \- *lemma* finset.of_dual_max_eq_min_of_dual
- \+ *lemma* finset.of_dual_min'
- \- *lemma* finset.of_dual_min_eq_max_of_dual
- \+ *lemma* finset.of_dual_sup'
- \+ *lemma* finset.of_dual_sup
- \+ *lemma* finset.to_dual_inf'
- \+ *lemma* finset.to_dual_inf
- \+ *lemma* finset.to_dual_max'
- \+ *lemma* finset.to_dual_min'
- \+ *lemma* finset.to_dual_sup'
- \+ *lemma* finset.to_dual_sup

Modified src/order/boolean_algebra.lean
- \+ *lemma* of_dual_compl
- \+ *lemma* to_dual_compl

Modified src/order/bounded_order.lean
- \+ *lemma* of_dual_bot
- \+ *lemma* of_dual_top
- \+ *lemma* to_dual_bot
- \+ *lemma* to_dual_top

Modified src/order/lattice.lean
- \+ *lemma* of_dual_inf
- \+ *lemma* of_dual_max
- \+ *lemma* of_dual_min
- \+ *lemma* of_dual_sup
- \+ *lemma* to_dual_inf
- \+ *lemma* to_dual_max
- \+ *lemma* to_dual_min
- \+ *lemma* to_dual_sup



## [2022-05-09 09:20:56](https://github.com/leanprover-community/mathlib/commit/1d9d573)
feat(algebra/order/monoid_lemmas_zero_lt): add some lemmas assuming `has_mul` `has_zero` `preorder` ([#13296](https://github.com/leanprover-community/mathlib/pull/13296))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* zero_lt.le_mul_of_le_mul_left
- \+ *lemma* zero_lt.le_mul_of_le_mul_right
- \+ *lemma* zero_lt.lt_mul_of_lt_mul_left
- \+ *lemma* zero_lt.lt_mul_of_lt_mul_right
- \+ *lemma* zero_lt.mul_le_mul_of_le_of_le'
- \+ *lemma* zero_lt.mul_le_mul_of_le_of_le
- \+ *lemma* zero_lt.mul_le_of_mul_le_left
- \+ *lemma* zero_lt.mul_le_of_mul_le_right
- \+ *lemma* zero_lt.mul_lt_mul_of_le_of_lt'
- \+ *lemma* zero_lt.mul_lt_mul_of_le_of_lt
- \+ *lemma* zero_lt.mul_lt_mul_of_lt_of_le'
- \+ *lemma* zero_lt.mul_lt_mul_of_lt_of_le
- \+ *lemma* zero_lt.mul_lt_mul_of_lt_of_lt'
- \+ *lemma* zero_lt.mul_lt_mul_of_lt_of_lt
- \+ *lemma* zero_lt.mul_lt_of_mul_lt_left
- \+ *lemma* zero_lt.mul_lt_of_mul_lt_right



## [2022-05-09 08:31:21](https://github.com/leanprover-community/mathlib/commit/b38aee4)
feat(analysis/special_functions): differentiability of Gamma function ([#13000](https://github.com/leanprover-community/mathlib/pull/13000))
Third instalment of my Gamma-function project (following [#12917](https://github.com/leanprover-community/mathlib/pull/12917) and [#13156](https://github.com/leanprover-community/mathlib/pull/13156)). This PR adds the proof that the Gamma function is complex-analytic, away from the poles at non-positive integers.
#### Estimated changes
Modified src/analysis/special_functions/gamma.lean
- \+ *theorem* complex.differentiable_at_Gamma
- \+ *lemma* complex.differentiable_at_Gamma_aux
- \+ *theorem* complex.has_deriv_at_Gamma_integral
- \+ *lemma* dGamma_integral_abs_convergent
- \+ *def* dGamma_integrand
- \+ *lemma* dGamma_integrand_is_O_at_top
- \+ *def* dGamma_integrand_real
- \+ *lemma* loc_unif_bound_dGamma_integrand
- \+/\- *lemma* real.Gamma_integrand_is_O

Modified src/analysis/special_functions/log/basic.lean
- \+ *lemma* real.abs_log_mul_self_lt

Modified src/analysis/special_functions/pow.lean
- \+ *lemma* real.abs_log_mul_self_rpow_lt



## [2022-05-09 06:03:23](https://github.com/leanprover-community/mathlib/commit/bf8db9b)
feat(analysis/normed_space/matrix_exponential): lemmas about the matrix exponential ([#13520](https://github.com/leanprover-community/mathlib/pull/13520))
This checks off "Matrix Exponential" from the undergrad TODO list, by providing the majority of the "obvious" statements about matrices over a real normed algebra. Combining this PR with what is already in mathlib, we have:
* `exp 0 = 1`
* `exp (A + B) = exp A * exp B` when `A` and `B` commute
* `exp (n • A) = exp A ^ n`
* `exp (z • A) = exp A ^ z`
* `exp (-A) = (exp A)⁻¹`
* `exp (U * D * ↑(U⁻¹)) = U * exp D * ↑(U⁻¹)`
* `exp Aᵀ = (exp A)ᵀ`
* `exp Aᴴ = (exp A)ᴴ`
* `A * exp B = exp B * A`  if `A * B = B * A`
* `exp (diagonal v) = diagonal (exp v)`
* `exp (block_diagonal v) = block_diagonal (exp v)`
* `exp (block_diagonal' v) = block_diagonal' (exp v)`
Still missing are:
* `det (exp A) = exp (trace A)`
* `exp A` can be written a weighted sum of powers of `A : matrix n n R` less than `fintype.card n` (an extension of [`matrix.pow_eq_aeval_mod_charpoly`](https://leanprover-community.github.io/mathlib_docs/linear_algebra/matrix/charpoly/coeff.html#matrix.pow_eq_aeval_mod_charpoly))
The proofs in this PR may seem small, but they had a substantial dependency chain: https://github.com/leanprover-community/mathlib/projects/16.
It turns out that there's always more missing glue than you think there is.
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/analysis/normed_space/exponential.lean


Added src/analysis/normed_space/matrix_exponential.lean
- \+ *lemma* matrix.exp_add_of_commute
- \+ *lemma* matrix.exp_block_diagonal'
- \+ *lemma* matrix.exp_block_diagonal
- \+ *lemma* matrix.exp_conj'
- \+ *lemma* matrix.exp_conj
- \+ *lemma* matrix.exp_conj_transpose
- \+ *lemma* matrix.exp_diagonal
- \+ *lemma* matrix.exp_neg
- \+ *lemma* matrix.exp_nsmul
- \+ *lemma* matrix.exp_sum_of_commute
- \+ *lemma* matrix.exp_transpose
- \+ *lemma* matrix.exp_units_conj'
- \+ *lemma* matrix.exp_units_conj
- \+ *lemma* matrix.exp_zsmul
- \+ *lemma* matrix.is_unit_exp



## [2022-05-09 02:37:50](https://github.com/leanprover-community/mathlib/commit/77c86ba)
rename(imo/imo1972_b2 → imo/imo1972_q5): Fix file name ([#14037](https://github.com/leanprover-community/mathlib/pull/14037))
#### Estimated changes
Renamed archive/imo/imo1972_b2.lean to archive/imo/imo1972_q5.lean




## [2022-05-09 02:37:49](https://github.com/leanprover-community/mathlib/commit/8412f1f)
feat(representation_theory/invariants): invariants of `lin_hom` are representation morphisms ([#14012](https://github.com/leanprover-community/mathlib/pull/14012))
#### Estimated changes
Modified src/representation_theory/invariants.lean
- \+ *def* representation.lin_hom.invariants_equiv_Rep_hom
- \+ *lemma* representation.lin_hom.mem_invariants_iff_comm



## [2022-05-09 02:37:47](https://github.com/leanprover-community/mathlib/commit/594ceda)
feat(analysis/normed_space/exponential): Generalize `field` lemmas to `division_ring` ([#13997](https://github.com/leanprover-community/mathlib/pull/13997))
This generalizes the lemmas about `exp 𝕂 𝕂` to lemmas about `exp 𝕂 𝔸` where `𝔸` is a `division_ring`.
This moves the lemmas down to the appropriate division_ring sections, and replaces the word `field` with `div` in their names, since `division_ring` is a mouthful, and really the name reflects the use of `/` in the definition.
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean
- \+/\- *lemma* exp_continuous
- \+ *lemma* exp_eq_tsum_div
- \- *lemma* exp_eq_tsum_field
- \+ *lemma* exp_series_apply_eq_div'
- \+ *lemma* exp_series_apply_eq_div
- \- *lemma* exp_series_apply_eq_field'
- \- *lemma* exp_series_apply_eq_field
- \+ *lemma* exp_series_div_has_sum_exp
- \+ *lemma* exp_series_div_has_sum_exp_of_mem_ball
- \+ *lemma* exp_series_div_summable
- \+ *lemma* exp_series_div_summable_of_mem_ball
- \- *lemma* exp_series_field_has_sum_exp
- \- *lemma* exp_series_field_has_sum_exp_of_mem_ball
- \- *lemma* exp_series_field_summable
- \- *lemma* exp_series_field_summable_of_mem_ball
- \+ *lemma* exp_series_sum_eq_div
- \- *lemma* exp_series_sum_eq_field
- \+ *lemma* norm_exp_series_div_summable
- \+ *lemma* norm_exp_series_div_summable_of_mem_ball
- \- *lemma* norm_exp_series_field_summable
- \- *lemma* norm_exp_series_field_summable_of_mem_ball

Modified src/analysis/special_functions/exponential.lean


Modified src/analysis/specific_limits/normed.lean


Modified src/combinatorics/derangements/exponential.lean




## [2022-05-09 02:37:47](https://github.com/leanprover-community/mathlib/commit/afec1d7)
fix(tactics/alias): Make docstring calculation available to to_additive ([#13968](https://github.com/leanprover-community/mathlib/pull/13968))
PR [#13944](https://github.com/leanprover-community/mathlib/pull/13944) fixed the docstrings for iff-style aliases, but because of
code duplication I added in [#13330](https://github.com/leanprover-community/mathlib/pull/13330) this did not apply to aliases
introduced by `to_additive`. This fixes that.
#### Estimated changes
Modified src/algebra/group/to_additive.lean


Modified src/tactic/alias.lean




## [2022-05-09 02:37:45](https://github.com/leanprover-community/mathlib/commit/34b61e3)
chore(algebra/regular/*): generalisation linter ([#13955](https://github.com/leanprover-community/mathlib/pull/13955))
#### Estimated changes
Modified src/algebra/regular/basic.lean


Modified src/algebra/regular/smul.lean
- \+/\- *lemma* is_smul_regular.mul
- \+/\- *lemma* is_smul_regular.mul_and_mul_iff
- \+/\- *lemma* is_smul_regular.mul_iff_right
- \+/\- *lemma* is_smul_regular.of_mul



## [2022-05-09 02:37:44](https://github.com/leanprover-community/mathlib/commit/5253153)
feat(algebra/category/Module/basic): `iso.hom_congr`agrees with `linear_equiv.arrow_congr` ([#13954](https://github.com/leanprover-community/mathlib/pull/13954))
#### Estimated changes
Modified src/algebra/category/Module/basic.lean
- \+ *lemma* Module.iso.conj_eq_conj
- \+ *lemma* Module.iso.hom_congr_eq_arrow_congr



## [2022-05-09 02:37:43](https://github.com/leanprover-community/mathlib/commit/4f386e6)
feat(set_theory/pgame/birthday): Birthdays of ordinals ([#13714](https://github.com/leanprover-community/mathlib/pull/13714))
#### Estimated changes
Modified src/set_theory/game/birthday.lean
- \+ *theorem* pgame.le_birthday
- \+ *theorem* pgame.neg_birthday
- \+ *theorem* pgame.neg_birthday_le
- \+ *theorem* pgame.to_pgame_birthday

Modified src/set_theory/game/ordinal.lean




## [2022-05-09 02:37:42](https://github.com/leanprover-community/mathlib/commit/1e8f381)
feat(algebraic_topology/dold_kan): defining some null homotopic maps ([#13085](https://github.com/leanprover-community/mathlib/pull/13085))
#### Estimated changes
Modified docs/references.bib


Modified src/algebra/homology/complex_shape.lean
- \+ *lemma* complex_shape.down'_mk
- \+ *lemma* complex_shape.down_mk

Added src/algebraic_topology/dold_kan/homotopies.lean
- \+ *def* algebraic_topology.dold_kan.Hσ
- \+ *lemma* algebraic_topology.dold_kan.Hσ_eq_zero
- \+ *abbreviation* algebraic_topology.dold_kan.c
- \+ *lemma* algebraic_topology.dold_kan.c_mk
- \+ *lemma* algebraic_topology.dold_kan.cs_down_0_not_rel_left
- \+ *def* algebraic_topology.dold_kan.homotopy_Hσ_to_zero
- \+ *def* algebraic_topology.dold_kan.hσ'
- \+ *lemma* algebraic_topology.dold_kan.hσ'_eq
- \+ *lemma* algebraic_topology.dold_kan.hσ'_eq_zero
- \+ *lemma* algebraic_topology.dold_kan.hσ'_naturality
- \+ *def* algebraic_topology.dold_kan.hσ
- \+ *lemma* algebraic_topology.dold_kan.map_Hσ
- \+ *lemma* algebraic_topology.dold_kan.map_hσ'
- \+ *def* algebraic_topology.dold_kan.nat_trans_Hσ

Added src/algebraic_topology/dold_kan/notations.lean




## [2022-05-09 00:34:40](https://github.com/leanprover-community/mathlib/commit/bf6e13b)
refactor(algebra/{group,group_with_zero/basic): Generalize lemmas to division monoids ([#14000](https://github.com/leanprover-community/mathlib/pull/14000))
Generalize `group` and `group_with_zero` lemmas to `division_monoid`. We do not actually delete the original lemmas but make them one-liners from the new ones. The next PR will then delete the old lemmas and perform the renames in all files.
Lemmas are renamed because
* one of the `group` or `group_with_zero` name has to go
* the new API should have a consistent naming convention
Pre-emptive lemma renames
#### Estimated changes
Modified src/algebra/continued_fractions/computation/terminates_iff_rat.lean


Modified src/algebra/group/basic.lean
- \+/\- *lemma* div_div
- \+/\- *theorem* div_div_assoc_swap
- \+/\- *lemma* div_div_div_comm
- \+/\- *lemma* div_eq_div_mul_div
- \+/\- *lemma* div_eq_inv_mul'
- \+ *lemma* div_eq_mul_one_div
- \+/\- *lemma* div_inv_eq_mul
- \+/\- *lemma* div_mul
- \+/\- *lemma* div_ne_one_of_ne
- \+/\- *lemma* div_one'
- \+ *lemma* division_comm_monoid.div_div
- \+ *lemma* division_comm_monoid.div_div_div_comm
- \+ *lemma* division_comm_monoid.div_div_div_eq
- \+ *lemma* division_comm_monoid.div_eq_inv_mul
- \+ *lemma* division_comm_monoid.div_mul
- \+ *lemma* division_comm_monoid.div_mul_comm
- \+ *lemma* division_comm_monoid.div_mul_div_comm
- \+ *lemma* division_comm_monoid.div_mul_eq_div_div
- \+ *lemma* division_comm_monoid.div_mul_eq_div_mul_one_div
- \+ *lemma* division_comm_monoid.div_mul_eq_mul_div
- \+ *lemma* division_comm_monoid.div_right_comm
- \+ *lemma* division_comm_monoid.inv_div_inv
- \+ *lemma* division_comm_monoid.inv_inv_div_inv
- \+ *lemma* division_comm_monoid.inv_mul'
- \+ *lemma* division_comm_monoid.inv_mul_eq_div
- \+ *lemma* division_comm_monoid.mul_comm_div
- \+ *lemma* division_comm_monoid.mul_div_left_comm
- \+ *lemma* division_comm_monoid.mul_div_mul_comm
- \+ *lemma* division_comm_monoid.mul_div_right_comm
- \+ *lemma* division_comm_monoid.mul_inv
- \+ *lemma* division_comm_monoid.one_div_mul_one_div
- \+ *lemma* division_monoid.div_div_eq_mul_div
- \+ *lemma* division_monoid.div_inv_eq_mul
- \+ *lemma* division_monoid.div_mul_eq_div_div_swap
- \+ *lemma* division_monoid.div_ne_one_of_ne
- \+ *lemma* division_monoid.div_one
- \+ *lemma* division_monoid.eq_inv_of_mul_eq_one_left
- \+ *lemma* division_monoid.eq_inv_of_mul_eq_one_right
- \+ *lemma* division_monoid.eq_of_div_eq_one
- \+ *lemma* division_monoid.eq_of_one_div_eq_one_div
- \+ *lemma* division_monoid.eq_one_div_of_mul_eq_one_left
- \+ *lemma* division_monoid.eq_one_div_of_mul_eq_one_right
- \+ *lemma* division_monoid.inv_div
- \+ *lemma* division_monoid.inv_div_left
- \+ *lemma* division_monoid.inv_eq_of_mul_eq_one_left
- \+ *lemma* division_monoid.inv_eq_one
- \+ *lemma* division_monoid.inv_ne_one
- \+ *lemma* division_monoid.inv_one
- \+ *lemma* division_monoid.one_div_div
- \+ *lemma* division_monoid.one_div_mul_one_div_rev
- \+ *lemma* division_monoid.one_div_one
- \+ *lemma* division_monoid.one_div_one_div
- \+ *lemma* division_monoid.one_eq_inv
- \+/\- *lemma* eq_inv_of_mul_eq_one
- \+/\- *lemma* eq_of_div_eq_one'
- \+/\- *lemma* inv_div'
- \+/\- *lemma* inv_div_inv
- \+/\- *theorem* inv_eq_one
- \+/\- *lemma* inv_inv_div_inv
- \+/\- *theorem* inv_mul'
- \+/\- *lemma* inv_mul_eq_div
- \+/\- *theorem* inv_ne_one
- \+ *lemma* left_inverse_inv
- \- *theorem* left_inverse_inv
- \+/\- *lemma* mul_inv
- \+/\- *theorem* one_eq_inv
- \+/\- *lemma* one_inv
- \+ *lemma* right_inverse_inv

Modified src/algebra/group/defs.lean
- \+ *lemma* inv_eq_of_mul_eq_one_right

Modified src/algebra/group_with_zero/basic.lean
- \+/\- *lemma* div_eq_inv_mul
- \- *lemma* div_eq_mul_one_div
- \+/\- *lemma* div_one
- \+/\- *lemma* eq_inv_of_mul_left_eq_one
- \+/\- *lemma* eq_inv_of_mul_right_eq_one
- \+/\- *lemma* eq_of_div_eq_one
- \+/\- *lemma* eq_of_one_div_eq_one_div
- \+/\- *lemma* eq_one_div_of_mul_eq_one
- \+/\- *lemma* eq_one_div_of_mul_eq_one_left
- \+/\- *lemma* inv_div
- \+/\- *lemma* inv_div_left
- \+/\- *lemma* inv_eq_one₀
- \+/\- *lemma* inv_one
- \+/\- *lemma* mul_comm_div'
- \+/\- *lemma* mul_inv_rev₀
- \+/\- *lemma* mul_inv₀
- \+/\- *lemma* one_div_div
- \+/\- *lemma* one_div_one
- \+/\- *lemma* one_div_one_div

Modified src/analysis/special_functions/trigonometric/complex.lean




## [2022-05-08 19:06:53](https://github.com/leanprover-community/mathlib/commit/449ba97)
refactor(data/nat/log): Golf + improved theorem names ([#14019](https://github.com/leanprover-community/mathlib/pull/14019))
Other than golfing and moving a few things around, our main changes are:
- rename `log_le_log_of_le` to `log_mono_right`, analogous renames elsewhere.
- add `lt_pow_iff_log_lt` and a `clog` analog.
#### Estimated changes
Modified src/data/nat/choose/central.lean


Modified src/data/nat/digits.lean


Modified src/data/nat/log.lean
- \+ *lemma* nat.clog_anti_left
- \- *lemma* nat.clog_le_clog_of_le
- \- *lemma* nat.clog_le_clog_of_left_ge
- \+ *lemma* nat.clog_mono_right
- \+/\- *lemma* nat.le_pow_iff_clog_le
- \+ *lemma* nat.log_anti_left
- \- *lemma* nat.log_eq_zero
- \- *lemma* nat.log_le_log_of_le
- \- *lemma* nat.log_le_log_of_left_ge
- \+ *lemma* nat.log_mono_right
- \+/\- *lemma* nat.log_monotone
- \+/\- *lemma* nat.log_of_left_le_one
- \+/\- *lemma* nat.log_of_lt
- \+/\- *lemma* nat.log_one_left
- \+/\- *lemma* nat.log_zero_left
- \+ *lemma* nat.lt_pow_iff_log_lt
- \+/\- *lemma* nat.pow_le_iff_le_log
- \+ *lemma* nat.pow_lt_iff_lt_clog

Modified src/data/nat/multiplicity.lean




## [2022-05-08 18:01:58](https://github.com/leanprover-community/mathlib/commit/163ef61)
feat(topology/algebra/infinite_sum): add `tsum_star` ([#13999](https://github.com/leanprover-community/mathlib/pull/13999))
These lemmas names are copied from `tsum_neg` and friends.
As a result, `star_exp` can be golfed and generalized.
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean
- \+/\- *lemma* star_exp

Modified src/analysis/normed_space/star/exponential.lean


Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* has_sum.star
- \+ *lemma* summable.of_star
- \+ *lemma* summable.star
- \+ *lemma* summable_star_iff'
- \+ *lemma* summable_star_iff
- \+ *lemma* tsum_star



## [2022-05-08 18:01:58](https://github.com/leanprover-community/mathlib/commit/dd16a83)
fix(topology/algebra/module/weak_dual): fix namespace issue, add a few extra lemmas ([#13407](https://github.com/leanprover-community/mathlib/pull/13407))
This PR fixes a namespace issue in `weak_dual`, to ensure lemmas with names like `eval_continuous` are appropriately namespaced. Also, lemmas about continuity of the evaluation map have been copied from `weak_bilin` to `weak_dual`.
#### Estimated changes
Modified src/analysis/locally_convex/polar.lean


Modified src/analysis/normed_space/weak_dual.lean


Modified src/measure_theory/measure/finite_measure_weak_convergence.lean


Modified src/topology/algebra/module/weak_dual.lean
- \- *lemma* bilin_embedding
- \- *lemma* coe_fn_continuous
- \- *lemma* continuous_of_continuous_eval
- \- *lemma* eval_continuous
- \- *theorem* tendsto_iff_forall_eval_tendsto
- \+ *lemma* weak_bilin.coe_fn_continuous
- \+ *lemma* weak_bilin.continuous_of_continuous_eval
- \+ *lemma* weak_bilin.embedding
- \+ *lemma* weak_bilin.eval_continuous
- \+ *theorem* weak_bilin.tendsto_iff_forall_eval_tendsto
- \+ *lemma* weak_dual.coe_fn_continuous
- \+ *lemma* weak_dual.continuous_of_continuous_eval
- \+ *lemma* weak_dual.eval_continuous



## [2022-05-08 16:31:29](https://github.com/leanprover-community/mathlib/commit/69c07a4)
feat(linear_algebra/linear_pmap): `mk_span_singleton` of the same point ([#14029](https://github.com/leanprover-community/mathlib/pull/14029))
One more lemma about `mk_span_singleton'` and slightly better lemma names.
#### Estimated changes
Modified src/linear_algebra/dual.lean


Modified src/linear_algebra/linear_pmap.lean
- \+ *lemma* linear_pmap.mk_span_singleton'_apply
- \+ *lemma* linear_pmap.mk_span_singleton'_apply_self
- \- *lemma* linear_pmap.mk_span_singleton_apply'
- \+/\- *lemma* linear_pmap.mk_span_singleton_apply



## [2022-05-08 16:31:28](https://github.com/leanprover-community/mathlib/commit/6a5d17e)
feat(measure_theory/integral): a few more integral lemmas ([#14025](https://github.com/leanprover-community/mathlib/pull/14025))
#### Estimated changes
Modified src/measure_theory/integral/interval_integral.lean
- \+ *lemma* interval_integrable.trans_iterate_Ico
- \+ *lemma* interval_integral.sum_integral_adjacent_intervals_Ico

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.of_real_set_integral_one
- \+ *lemma* measure_theory.of_real_set_integral_one_of_measure_ne_top



## [2022-05-08 15:55:36](https://github.com/leanprover-community/mathlib/commit/e330694)
feat(analysis/p_series): explicit bounds on sums of the form 1/j^2 ([#13851](https://github.com/leanprover-community/mathlib/pull/13851))
#### Estimated changes
Modified src/analysis/p_series.lean
- \+ *lemma* sum_Ioc_inv_sq_le_sub
- \+ *lemma* sum_Ioo_inv_sq_le



## [2022-05-08 14:02:33](https://github.com/leanprover-community/mathlib/commit/79ffb55)
chore(algebra/category/CommRing=>Ring): rename ([#14022](https://github.com/leanprover-community/mathlib/pull/14022))
This folder was originally named `algebra/category/CommRing/` because it only handled the commutative case. That's largely no longer the case, so we should rename the folder.
#### Estimated changes
Modified src/algebra/category/Algebra/basic.lean


Modified src/algebra/category/Algebra/limits.lean


Modified src/algebra/category/BoolRing.lean


Deleted src/algebra/category/CommRing/default.lean


Renamed src/algebra/category/CommRing/adjunctions.lean to src/algebra/category/Ring/adjunctions.lean


Renamed src/algebra/category/CommRing/basic.lean to src/algebra/category/Ring/basic.lean


Renamed src/algebra/category/CommRing/colimits.lean to src/algebra/category/Ring/colimits.lean


Renamed src/algebra/category/CommRing/constructions.lean to src/algebra/category/Ring/constructions.lean


Added src/algebra/category/Ring/default.lean


Renamed src/algebra/category/CommRing/filtered_colimits.lean to src/algebra/category/Ring/filtered_colimits.lean


Renamed src/algebra/category/CommRing/instances.lean to src/algebra/category/Ring/instances.lean


Renamed src/algebra/category/CommRing/limits.lean to src/algebra/category/Ring/limits.lean


Modified src/algebraic_geometry/locally_ringed_space/has_colimits.lean


Modified src/algebraic_geometry/open_immersion.lean


Modified src/algebraic_geometry/properties.lean


Modified src/algebraic_geometry/ringed_space.lean


Modified src/algebraic_geometry/structure_sheaf.lean


Modified src/ring_theory/ideal/local_ring.lean


Modified src/topology/category/TopCommRing.lean


Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/stalks.lean




## [2022-05-08 12:55:28](https://github.com/leanprover-community/mathlib/commit/3478a2a)
feat(probability/ident_distrib): identically distributed random variables ([#14024](https://github.com/leanprover-community/mathlib/pull/14024))
#### Estimated changes
Added src/probability/ident_distrib.lean
- \+ *lemma* probability_theory.ident_distrib.ae_mem_snd
- \+ *lemma* probability_theory.ident_distrib.ae_snd
- \+ *lemma* probability_theory.ident_distrib.ae_strongly_measurable_fst
- \+ *lemma* probability_theory.ident_distrib.ae_strongly_measurable_iff
- \+ *lemma* probability_theory.ident_distrib.ae_strongly_measurable_snd
- \+ *lemma* probability_theory.ident_distrib.const_div
- \+ *lemma* probability_theory.ident_distrib.const_mul
- \+ *lemma* probability_theory.ident_distrib.div_const
- \+ *lemma* probability_theory.ident_distrib.ess_sup_eq
- \+ *lemma* probability_theory.ident_distrib.integrable_iff
- \+ *lemma* probability_theory.ident_distrib.integrable_snd
- \+ *lemma* probability_theory.ident_distrib.integral_eq
- \+ *lemma* probability_theory.ident_distrib.lintegral_eq
- \+ *lemma* probability_theory.ident_distrib.measure_mem_eq
- \+ *lemma* probability_theory.ident_distrib.mem_ℒp_iff
- \+ *lemma* probability_theory.ident_distrib.mem_ℒp_snd
- \+ *lemma* probability_theory.ident_distrib.mul_const
- \+ *lemma* probability_theory.ident_distrib.snorm_eq
- \+ *lemma* probability_theory.ident_distrib.variance_eq
- \+ *structure* probability_theory.ident_distrib



## [2022-05-08 06:24:13](https://github.com/leanprover-community/mathlib/commit/0c64b3d)
feat(algebra/category/Module): biproducts ([#13908](https://github.com/leanprover-community/mathlib/pull/13908))
Following the same pattern for `AddCommGroup`, create the instance for biproducts in` Module R`, and check they are isomorphic to the usual construction.
#### Estimated changes
Modified src/algebra/category/Group/biproducts.lean
- \+ *lemma* AddCommGroup.binary_product_limit_cone_cone_π_app_left
- \+ *lemma* AddCommGroup.binary_product_limit_cone_cone_π_app_right
- \+/\- *def* AddCommGroup.biproduct_iso_pi
- \+ *lemma* AddCommGroup.biproduct_iso_pi_inv_comp_π
- \+/\- *def* AddCommGroup.has_limit.product_limit_cone

Added src/algebra/category/Module/biproducts.lean
- \+ *def* Module.binary_product_limit_cone
- \+ *lemma* Module.binary_product_limit_cone_cone_π_app_left
- \+ *lemma* Module.binary_product_limit_cone_cone_π_app_right
- \+ *def* Module.biprod_iso_prod
- \+ *lemma* Module.biprod_iso_prod_inv_comp_fst
- \+ *lemma* Module.biprod_iso_prod_inv_comp_snd
- \+ *def* Module.biproduct_iso_pi
- \+ *lemma* Module.biproduct_iso_pi_inv_comp_π
- \+ *def* Module.has_limit.lift
- \+ *lemma* Module.has_limit.lift_apply
- \+ *def* Module.has_limit.product_limit_cone



## [2022-05-08 04:50:21](https://github.com/leanprover-community/mathlib/commit/ce0dc83)
feat(set_theory/ordinal/basic): Supremum indexed over an empty / unique type ([#13735](https://github.com/leanprover-community/mathlib/pull/13735))
This PR contains the following changes:
- The lemmas `sup_unique`, `bsup_one`, `lsub_unique`, `blsub_one`.
- `congr` lemmas for `bsup` and `blsub`
- Arguments like `o = 0` are removed as the `congr` lemmas now handle this.
- `a + 1` is changed to `a.succ` in some lemmas (for better rewriting).
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean


Modified src/set_theory/game/birthday.lean


Modified src/set_theory/ordinal/arithmetic.lean
- \+ *lemma* ordinal.blsub_congr
- \+/\- *theorem* ordinal.blsub_const
- \+ *theorem* ordinal.blsub_one
- \+/\- *lemma* ordinal.blsub_zero
- \+ *lemma* ordinal.bsup_congr
- \+ *theorem* ordinal.bsup_one
- \+/\- *theorem* ordinal.bsup_zero
- \+/\- *theorem* ordinal.lsub_const
- \+/\- *lemma* ordinal.lsub_empty
- \+ *theorem* ordinal.lsub_unique
- \+/\- *theorem* ordinal.sup_const
- \+/\- *theorem* ordinal.sup_empty
- \+ *theorem* ordinal.sup_unique



## [2022-05-07 22:21:48](https://github.com/leanprover-community/mathlib/commit/3a0eb4b)
chore(logic/relation): Dot notation on `well_founded.trans_gen` ([#14016](https://github.com/leanprover-community/mathlib/pull/14016))
#### Estimated changes
Modified src/logic/relation.lean
- \- *lemma* relation.well_founded.trans_gen
- \+ *lemma* well_founded.trans_gen

Modified src/set_theory/game/pgame.lean
- \+/\- *theorem* pgame.wf_subsequent



## [2022-05-07 22:21:47](https://github.com/leanprover-community/mathlib/commit/e190225)
feat(data/rat/meta_defs, meta/expr): rat.to_pexpr and int.to_pexpr ([#14002](https://github.com/leanprover-community/mathlib/pull/14002))
#### Estimated changes
Modified src/data/rat/meta_defs.lean


Modified src/meta/expr.lean




## [2022-05-07 20:15:08](https://github.com/leanprover-community/mathlib/commit/e0dd300)
feat(algebra/{invertible + group_power/lemmas}): taking `inv_of` (⅟_) is injective ([#14011](https://github.com/leanprover-community/mathlib/pull/14011))
Besides the lemma stated in the description, I also made explicit an argument that was implicit in a different lemma and swapped the arguments of `invertible_unique` in order to get the typeclass assumptions before some non-typeclass assumptions.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/inv_of_inj)
#### Estimated changes
Modified src/algebra/group_power/lemmas.lean


Modified src/algebra/invertible.lean
- \+ *lemma* inv_of_inj
- \+/\- *lemma* inv_of_inv_of
- \+/\- *lemma* invertible_unique



## [2022-05-07 15:50:10](https://github.com/leanprover-community/mathlib/commit/0e494af)
chore(order/*): Less `order_dual` abuse ([#14008](https://github.com/leanprover-community/mathlib/pull/14008))
Sanitize uses of `order_dual` by inserting the required `of_dual` and `to_dual` instead of type-ascripting. Also remove some uses which were not necessary. Those dated from the time where we did not have antitone functions.
#### Estimated changes
Modified archive/100-theorems-list/82_cubing_a_cube.lean
- \+/\- *def* decreasing_sequence
- \+ *lemma* strict_anti_sequence_of_cubes
- \- *lemma* strict_mono_sequence_of_cubes

Modified src/algebra/order/field.lean
- \+ *lemma* one_div_pow_anti
- \- *lemma* one_div_pow_mono
- \+ *lemma* one_div_pow_strict_anti
- \- *lemma* one_div_pow_strict_mono

Modified src/analysis/convex/quasiconvex.lean
- \+/\- *lemma* quasiconcave_on.dual
- \+/\- *lemma* quasiconvex_on.dual
- \+/\- *lemma* quasilinear_on.dual

Modified src/data/finset/lattice.lean
- \+ *lemma* finset.le_inf'_iff

Modified src/number_theory/liouville/liouville_constant.lean


Modified src/order/compare.lean
- \+ *lemma* of_dual_compares_of_dual
- \- *lemma* order_dual.dual_compares
- \+ *lemma* to_dual_compares_to_dual

Modified src/order/galois_connection.lean
- \+/\- *def* galois_coinsertion.dual
- \+/\- *def* galois_coinsertion.of_dual
- \+/\- *structure* galois_coinsertion
- \+/\- *def* galois_insertion.dual
- \+/\- *def* galois_insertion.of_dual

Modified src/order/monotone.lean


Modified src/order/ord_continuous.lean




## [2022-05-07 15:50:09](https://github.com/leanprover-community/mathlib/commit/5166765)
chore(order/filter/pointwise): Better definitional unfolding ([#13941](https://github.com/leanprover-community/mathlib/pull/13941))
Tweak pointwise operation definitions to make them easier to work with:
* `1` is now `pure 1` instead of `principal 1`. This changes defeq.
* Binary operations unfold to the set operation instead exposing a bare `set.image2` (`obtain ⟨t₁, t₂, h₁, h₂, h⟩ : s ∈ f * g` now gives `h : t₁ * t₂ ⊆ s` instead of `h : set.image2 (*) t₁ t₂ ⊆ s`. This does not change defeq.
#### Estimated changes
Modified src/order/filter/pointwise.lean
- \+/\- *lemma* filter.eventually_one
- \+/\- *lemma* filter.le_one_iff
- \+/\- *lemma* filter.mem_one
- \+/\- *lemma* filter.one_mem_one
- \+ *lemma* filter.one_ne_bot
- \+/\- *lemma* filter.principal_one
- \+/\- *lemma* filter.pure_one



## [2022-05-07 11:59:00](https://github.com/leanprover-community/mathlib/commit/cf65daf)
feat(probability/variance): define the variance of a random variable, prove its basic properties ([#13912](https://github.com/leanprover-community/mathlib/pull/13912))
#### Estimated changes
Modified docs/undergrad.yaml


Modified src/probability/integration.lean
- \+/\- *lemma* probability_theory.indep_fun.integrable_mul
- \+ *theorem* probability_theory.indep_fun.integral_mul_of_integrable'

Added src/probability/variance.lean
- \+ *theorem* probability_theory.indep_fun.variance_add
- \+ *theorem* probability_theory.indep_fun.variance_sum
- \+ *theorem* probability_theory.meas_ge_le_variance_div_sq
- \+ *def* probability_theory.variance
- \+ *lemma* probability_theory.variance_def'
- \+ *lemma* probability_theory.variance_le_expectation_sq
- \+ *lemma* probability_theory.variance_mul
- \+ *lemma* probability_theory.variance_nonneg
- \+ *lemma* probability_theory.variance_smul'
- \+ *lemma* probability_theory.variance_smul
- \+ *lemma* probability_theory.variance_zero



## [2022-05-07 09:57:54](https://github.com/leanprover-community/mathlib/commit/c247622)
feat(group_theory/group_action/units): simp lemma for scalar action of `is_unit.unit h` ([#14006](https://github.com/leanprover-community/mathlib/pull/14006))
#### Estimated changes
Modified src/algebra/group_with_zero/basic.lean
- \+ *lemma* units.smul_mk0

Modified src/group_theory/group_action/units.lean
- \+ *lemma* units.smul_is_unit

Modified src/ring_theory/witt_vector/isocrystal.lean




## [2022-05-07 09:57:53](https://github.com/leanprover-community/mathlib/commit/9134a8e)
feat(combinatorics/simple_graph/hasse): Hasse diagram and path graph ([#13959](https://github.com/leanprover-community/mathlib/pull/13959))
Define the Hasse diagram of an order and the path graph on `n` vertices as the Hasse diagram of `fin n`.
#### Estimated changes
Modified src/combinatorics/simple_graph/basic.lean
- \- *lemma* simple_graph.irrefl

Modified src/combinatorics/simple_graph/connectivity.lean


Added src/combinatorics/simple_graph/hasse.lean
- \+ *def* simple_graph.hasse
- \+ *lemma* simple_graph.hasse_adj
- \+ *def* simple_graph.hasse_dual_iso
- \+ *lemma* simple_graph.hasse_dual_iso_apply
- \+ *lemma* simple_graph.hasse_dual_iso_symm_apply
- \+ *lemma* simple_graph.hasse_preconnected_of_pred
- \+ *lemma* simple_graph.hasse_preconnected_of_succ
- \+ *def* simple_graph.path_graph
- \+ *lemma* simple_graph.path_graph_connected
- \+ *lemma* simple_graph.path_graph_preconnected



## [2022-05-07 09:57:51](https://github.com/leanprover-community/mathlib/commit/b2aa27e)
feat(analysis/calculus/deriv): generalize some lemmas ([#13575](https://github.com/leanprover-community/mathlib/pull/13575))
The types of scalar and codomain can be different now.
For example, these lemmas can be used for `f : ℝ → ℂ` `f' : ℝ →L[ℝ] ℂ` now.
#### Estimated changes
Modified src/analysis/calculus/deriv.lean
- \+/\- *theorem* has_deriv_at.comp_has_fderiv_at
- \+/\- *theorem* has_deriv_at.comp_has_fderiv_within_at
- \+/\- *theorem* has_deriv_at_filter.comp_has_fderiv_at_filter
- \+/\- *theorem* has_deriv_within_at.comp_has_fderiv_within_at
- \+/\- *theorem* has_strict_deriv_at.comp_has_strict_fderiv_at



## [2022-05-07 08:20:10](https://github.com/leanprover-community/mathlib/commit/f8bc097)
feat(algebra/module/linear_map): `Rᵐᵒᵖ` is isomorphic to `module.End R R` ([#13931](https://github.com/leanprover-community/mathlib/pull/13931))
This PR adds the canonical (semi)ring isomorphism from `Rᵐᵒᵖ` to
`module.End R R` for a (semi)ring `R`, given by the right multiplication.
#### Estimated changes
Modified src/algebra/module/linear_map.lean
- \+ *theorem* linear_map.ext_ring_op
- \+ *def* module.module_End_self
- \+ *def* module.module_End_self_op



## [2022-05-07 07:07:16](https://github.com/leanprover-community/mathlib/commit/559f58b)
feat(order/filter): add a few lemmas ([#13985](https://github.com/leanprover-community/mathlib/pull/13985))
* weaken assumptions of `filter.has_antitone_basis.tendsto` from `[semilattice_sup ι] [nonempty ι]` to `[preorder ι]`;
* add `filter.has_antitone_basis.tendsto`, `filter.has_antitone_basis.mem`, `filter.has_antitone_basis.tendsto_small_sets`.
#### Estimated changes
Modified src/order/filter/at_top_bot.lean
- \+ *lemma* filter.has_antitone_basis.eventually_subset
- \- *lemma* filter.has_antitone_basis.tendsto

Modified src/order/filter/bases.lean


Modified src/order/filter/small_sets.lean
- \+ *lemma* filter.has_antitone_basis.tendsto_small_sets



## [2022-05-07 04:45:56](https://github.com/leanprover-community/mathlib/commit/ca1375a)
refactor(algebra/order/monoid_lemmas): reorder the file ([#13492](https://github.com/leanprover-community/mathlib/pull/13492))
Just like in `algebra/order/monoid_lemmas_zero_lt`, sort by algebraic assumptions and order assumptions first, then put similar lemmas together.
It would be simpler to find duplicates, missing lemmas, and inconsistencies. (There are so many!)
#### Estimated changes
Modified src/algebra/order/monoid_lemmas.lean
- \+/\- *def* contravariant.to_left_cancel_semigroup
- \+/\- *def* contravariant.to_right_cancel_semigroup
- \+/\- *lemma* exists_square_le
- \+/\- *lemma* le_mul_of_le_mul_left
- \+/\- *lemma* le_mul_of_le_mul_right
- \+/\- *lemma* le_mul_of_le_of_one_le
- \+/\- *lemma* le_mul_of_one_le_left'
- \+/\- *lemma* le_mul_of_one_le_right'
- \+/\- *lemma* le_of_le_mul_of_le_one_left
- \+/\- *lemma* le_of_le_mul_of_le_one_right
- \+/\- *lemma* le_of_mul_le_of_one_le_left
- \+/\- *lemma* le_of_mul_le_of_one_le_right
- \+/\- *lemma* lt_mul_of_lt_mul_left
- \+/\- *lemma* lt_mul_of_lt_mul_right
- \+/\- *lemma* lt_mul_of_lt_of_one_le'
- \+/\- *lemma* lt_mul_of_lt_of_one_lt'
- \+/\- *lemma* lt_mul_of_one_le_of_lt
- \+/\- *lemma* lt_mul_of_one_lt_of_lt
- \+/\- *lemma* lt_of_lt_mul_of_le_one_left
- \+/\- *lemma* lt_of_lt_mul_of_le_one_right
- \+/\- *lemma* lt_of_mul_lt_of_one_le_left
- \+/\- *lemma* lt_of_mul_lt_of_one_le_right
- \+/\- *lemma* mul_eq_mul_iff_eq_and_eq
- \+/\- *lemma* mul_eq_one_iff'
- \+/\- *lemma* mul_le_mul'
- \+/\- *lemma* mul_le_mul_left'
- \+/\- *lemma* mul_le_mul_three
- \+/\- *lemma* mul_le_of_le_one_left'
- \+/\- *lemma* mul_le_of_le_one_right'
- \+/\- *lemma* mul_le_of_mul_le_left
- \+/\- *lemma* mul_le_of_mul_le_right
- \+/\- *lemma* mul_left_cancel''
- \+/\- *lemma* mul_lt_mul'''
- \+/\- *lemma* mul_lt_mul_left'
- \+/\- *lemma* mul_lt_mul_of_le_of_lt
- \+/\- *lemma* mul_lt_mul_of_lt_of_le
- \+/\- *lemma* mul_lt_mul_of_lt_of_lt
- \+/\- *lemma* mul_lt_of_le_of_lt_one
- \+/\- *lemma* mul_lt_of_mul_lt_left
- \+/\- *lemma* mul_lt_of_mul_lt_right
- \+/\- *lemma* mul_right_cancel''
- \+/\- *lemma* one_le_mul_right
- \+/\- *lemma* one_lt_mul'
- \+/\- *lemma* one_lt_mul_of_le_of_lt'
- \+/\- *lemma* one_lt_mul_of_lt_of_le'



## [2022-05-07 04:10:25](https://github.com/leanprover-community/mathlib/commit/5789c63)
chore(scripts): update nolints.txt ([#14004](https://github.com/leanprover-community/mathlib/pull/14004))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-05-07 00:43:46](https://github.com/leanprover-community/mathlib/commit/275dabf)
feat(order/atoms): is_atomic_of_order_bot_lt_well_founded ([#13967](https://github.com/leanprover-community/mathlib/pull/13967))
#### Estimated changes
Modified src/order/atoms.lean
- \+ *lemma* is_atomic_of_order_bot_well_founded_lt
- \+ *lemma* is_coatomic_of_order_top_gt_well_founded



## [2022-05-06 20:39:04](https://github.com/leanprover-community/mathlib/commit/dcd452d)
feat(analysis/locally_convex/with_seminorms): characterization of the topology induced by seminorms in terms of `𝓝 0` ([#13547](https://github.com/leanprover-community/mathlib/pull/13547))
This shows that a topology is induced by the family of seminorms `p` iff `𝓝 0 = ⨅ i, (𝓝 0).comap (p i)`, which allows to use the extensive filter and topology library (see e.g. [#13549](https://github.com/leanprover-community/mathlib/pull/13549)).
#### Estimated changes
Modified src/analysis/locally_convex/with_seminorms.lean
- \+ *lemma* seminorm_family.filter_eq_infi
- \+ *lemma* seminorm_family.with_seminorms_iff_nhds_eq_infi

Modified src/analysis/seminorm.lean
- \+ *lemma* seminorm.ball_zero_eq_preimage_ball



## [2022-05-06 19:31:54](https://github.com/leanprover-community/mathlib/commit/10721ba)
feat(topology/algebra/module/basic): basic topological properties of quotient modules ([#13433](https://github.com/leanprover-community/mathlib/pull/13433))
More precisely, we prove that : 
* if `M` is a topological module and `S` is a submodule of `M`, then `M ⧸ S` is a topological module
* furthermore, if `S` is closed, then `M ⧸ S` is regular (hence T2) 
- [x] depends on: [#13278](https://github.com/leanprover-community/mathlib/pull/13278) 
- [x] depends on: [#13401](https://github.com/leanprover-community/mathlib/pull/13401)
#### Estimated changes
Modified src/topology/algebra/module/basic.lean
- \+ *lemma* submodule.is_open_map_mkq



## [2022-05-06 18:45:20](https://github.com/leanprover-community/mathlib/commit/8f116f4)
feat(ring_theory/localization): generalize lemmas from `comm_ring` to `comm_semiring` ([#13994](https://github.com/leanprover-community/mathlib/pull/13994))
This PR does not add new stuffs, but removes several subtractions from the proofs.
#### Estimated changes
Modified src/ring_theory/localization/at_prime.lean
- \+ *lemma* is_localization.at_prime.nontrivial
- \+/\- *lemma* localization.local_ring_hom_comp

Modified src/ring_theory/localization/away.lean
- \+/\- *abbreviation* is_localization.away

Modified src/ring_theory/localization/ideal.lean




## [2022-05-06 18:45:19](https://github.com/leanprover-community/mathlib/commit/27e105d)
chore(analysis/normed_space/exponential): Make the `𝔸` argument implicit ([#13986](https://github.com/leanprover-community/mathlib/pull/13986))
`exp 𝕂 𝔸` is now just `exp 𝕂`.
This also renames two lemmas that refer to this argument in their name to no longer do so.
In a few places we have to add type annotations where they weren't needed before, but nowhere do we need to resort to `@`.
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean
- \+/\- *lemma* commute.exp
- \+/\- *lemma* commute.exp_left
- \+/\- *lemma* commute.exp_right
- \+/\- *lemma* exp_add
- \+/\- *lemma* exp_eq_exp
- \+/\- *lemma* exp_eq_tsum
- \+/\- *lemma* exp_neg
- \+/\- *lemma* exp_series_field_has_sum_exp
- \+/\- *lemma* exp_series_has_sum_exp'
- \+/\- *lemma* exp_series_has_sum_exp
- \+/\- *lemma* exp_zero
- \+/\- *lemma* exp_zsmul
- \+/\- *lemma* exp_ℝ_ℂ_eq_exp_ℂ_ℂ
- \+/\- *lemma* inv_of_exp
- \+/\- *lemma* is_unit_exp
- \+/\- *lemma* map_exp
- \+/\- *lemma* prod.fst_exp
- \+/\- *lemma* prod.snd_exp
- \+/\- *lemma* ring.inverse_exp

Modified src/analysis/normed_space/spectrum.lean


Modified src/analysis/normed_space/star/exponential.lean


Modified src/analysis/normed_space/star/spectrum.lean


Modified src/analysis/special_functions/exponential.lean
- \+ *lemma* complex.exp_eq_exp_ℂ
- \- *lemma* complex.exp_eq_exp_ℂ_ℂ
- \+/\- *lemma* has_deriv_at_exp
- \+/\- *lemma* has_strict_deriv_at_exp
- \+/\- *lemma* has_strict_deriv_at_exp_zero
- \+ *lemma* real.exp_eq_exp_ℝ
- \- *lemma* real.exp_eq_exp_ℝ_ℝ

Modified src/combinatorics/derangements/exponential.lean




## [2022-05-06 18:45:18](https://github.com/leanprover-community/mathlib/commit/eea16dc)
feat(number_theory/legendre_symbol/*): add results on value at -1 ([#13978](https://github.com/leanprover-community/mathlib/pull/13978))
This PR adds code expressing the value of the quadratic character at -1 of a finite field of odd characteristic as χ₄ applied to the cardinality of the field. This is then also done for the Legendre symbol.
Additional changes:
* two helper lemmas `odd_mod_four` and `finite_field.even_card_of_char_two` that are needed
* some API lemmas for χ₄
* write `euler_criterion` and `exists_sq_eq_neg_one_iff` in terms of `is_square`; simplify the proof of the latter using the general result for quadratic characters
#### Estimated changes
Modified archive/imo/imo2008_q3.lean


Modified src/number_theory/legendre_symbol/quadratic_char.lean
- \+ *lemma* char.is_square_neg_one_iff
- \+ *lemma* char.quadratic_char_neg_one
- \+ *lemma* finite_field.even_card_iff_char_two
- \+ *lemma* finite_field.even_card_of_char_two
- \+ *lemma* nat.odd_mod_four_iff
- \+ *lemma* zmod.χ₄_eq_neg_one_pow
- \+ *lemma* zmod.χ₄_int_eq_if_mod_four
- \+ *lemma* zmod.χ₄_nat_eq_if_mod_four

Modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean
- \+/\- *lemma* zmod.exists_sq_eq_neg_one_iff
- \+ *lemma* zmod.legendre_sym_neg_one

Modified src/number_theory/zsqrtd/gaussian_int.lean




## [2022-05-06 18:45:17](https://github.com/leanprover-community/mathlib/commit/dfe1897)
feat(data/polynomial/laurent): laurent polynomials -- defs and some API ([#13784](https://github.com/leanprover-community/mathlib/pull/13784))
I broke off the initial part of [#13415](https://github.com/leanprover-community/mathlib/pull/13415) into this initial segment, leaving the rest of the PR as depending on this one.
#### Estimated changes
Added src/data/polynomial/laurent.lean
- \+ *def* laurent_polynomial.C
- \+ *lemma* laurent_polynomial.C_eq_algebra_map
- \+ *def* laurent_polynomial.T
- \+ *lemma* laurent_polynomial.T_add
- \+ *lemma* laurent_polynomial.T_pow
- \+ *lemma* laurent_polynomial.T_zero
- \+ *lemma* laurent_polynomial.algebra_map_apply
- \+ *lemma* laurent_polynomial.inv_of_T
- \+ *lemma* laurent_polynomial.is_unit_T
- \+ *lemma* laurent_polynomial.mul_T_assoc
- \+ *lemma* laurent_polynomial.single_eq_C
- \+ *lemma* laurent_polynomial.single_eq_C_mul_T
- \+ *lemma* laurent_polynomial.single_zero_one_eq_one
- \+ *abbreviation* laurent_polynomial
- \+ *def* polynomial.to_laurent
- \+ *lemma* polynomial.to_laurent_C
- \+ *lemma* polynomial.to_laurent_C_mul_T
- \+ *lemma* polynomial.to_laurent_C_mul_X_pow
- \+ *lemma* polynomial.to_laurent_C_mul_eq
- \+ *lemma* polynomial.to_laurent_X
- \+ *lemma* polynomial.to_laurent_X_pow
- \+ *def* polynomial.to_laurent_alg
- \+ *lemma* polynomial.to_laurent_alg_apply
- \+ *lemma* polynomial.to_laurent_apply
- \+ *lemma* polynomial.to_laurent_one



## [2022-05-06 16:39:40](https://github.com/leanprover-community/mathlib/commit/58d83ed)
feat(tactic/lint/misc): adding a linter that flags iffs with explicit variables on both sides ([#11606](https://github.com/leanprover-community/mathlib/pull/11606))
#### Estimated changes
Modified src/tactic/lint/default.lean


Modified src/tactic/lint/misc.lean




## [2022-05-06 15:42:43](https://github.com/leanprover-community/mathlib/commit/863a167)
docs(ring_theory/localization/ideal): fix an unused name ([#13992](https://github.com/leanprover-community/mathlib/pull/13992))
#### Estimated changes
Modified src/ring_theory/localization/ideal.lean




## [2022-05-06 15:42:42](https://github.com/leanprover-community/mathlib/commit/db5c2a6)
chore(data/zmod/basic.lean): change order of arguments of `zmod.nat_cast_mod` for consistency ([#13988](https://github.com/leanprover-community/mathlib/pull/13988))
As discussed [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60zmod.2Enat_cast_mod.60.20vs.20.60zmod.2Eint_cast_mod.60), this changes the order of arguments in `zmod.nat_cast_mod` to be compatible with `zmod.int_cast_mod`.
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+/\- *lemma* zmod.nat_cast_mod

Modified src/number_theory/padics/ring_homs.lean


Modified src/number_theory/zsqrtd/gaussian_int.lean




## [2022-05-06 15:42:40](https://github.com/leanprover-community/mathlib/commit/40bedd6)
refactor(set_theory/game/pgame): Remove `pgame.omega` ([#13960](https://github.com/leanprover-community/mathlib/pull/13960))
This barely had any API to begin with. Thanks to `ordinal.to_pgame`, it is now entirely redundant.
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \- *def* pgame.omega

Modified src/set_theory/game/winner.lean
- \- *theorem* pgame.omega_left_wins

Modified src/set_theory/surreal/basic.lean
- \- *theorem* pgame.numeric_omega



## [2022-05-06 15:42:39](https://github.com/leanprover-community/mathlib/commit/c9f5cee)
feat(set_theory/game/pgame): Add remark on relabelings ([#13732](https://github.com/leanprover-community/mathlib/pull/13732))
#### Estimated changes
Modified src/set_theory/game/pgame.lean




## [2022-05-06 14:58:58](https://github.com/leanprover-community/mathlib/commit/ba627bc)
feat(measure_theory/function/conditional_expectation): induction over Lp functions which are strongly measurable wrt a sub-sigma-algebra ([#13129](https://github.com/leanprover-community/mathlib/pull/13129))
#### Estimated changes
Modified src/measure_theory/function/conditional_expectation.lean
- \+ *lemma* measure_theory.Lp.induction_strongly_measurable
- \+ *lemma* measure_theory.Lp.induction_strongly_measurable_aux
- \+/\- *lemma* measure_theory.Lp_meas_to_Lp_trim_lie_symm_indicator
- \+ *lemma* measure_theory.Lp_meas_to_Lp_trim_lie_symm_to_Lp
- \+ *lemma* measure_theory.mem_ℒp.induction_strongly_measurable

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* measure_theory.mem_ℒp.to_Lp_congr

Modified src/order/filter/indicator_function.lean
- \+ *lemma* filter.eventually_eq.support



## [2022-05-06 12:51:04](https://github.com/leanprover-community/mathlib/commit/fe0c4cd)
docs(data/polynomial/algebra_map): fix a typo in a doc-string ([#13989](https://github.com/leanprover-community/mathlib/pull/13989))
The doc-string talks about `comm_ring`, while the lemma uses `comm_semiring`.  I aligned the two to the weaker one!
#### Estimated changes
Modified src/data/polynomial/algebra_map.lean




## [2022-05-06 12:51:03](https://github.com/leanprover-community/mathlib/commit/f6c030f)
feat(linear_algebra/matrix/nonsingular_inverse): inverse of a diagonal matrix is diagonal ([#13827](https://github.com/leanprover-community/mathlib/pull/13827))
The main results are `is_unit (diagonal v) ↔ is_unit v` and `(diagonal v)⁻¹ = diagonal (ring.inverse v)`.
This also generalizes `invertible.map` to `monoid_hom_class`.
#### Estimated changes
Modified src/algebra/invertible.lean
- \+/\- *def* invertible.map

Modified src/data/mv_polynomial/invertible.lean


Modified src/linear_algebra/matrix/nonsingular_inverse.lean
- \+ *def* matrix.diagonal_invertible
- \+ *def* matrix.diagonal_invertible_equiv_invertible
- \+ *lemma* matrix.inv_diagonal
- \+ *lemma* matrix.inv_of_diagonal_eq
- \+ *def* matrix.invertible_of_diagonal_invertible
- \+ *lemma* matrix.is_unit_diagonal

Modified src/ring_theory/algebra_tower.lean




## [2022-05-06 12:03:00](https://github.com/leanprover-community/mathlib/commit/e4d3d33)
feat(probability/stopping): add properties of the measurable space generated by a stopping time ([#13909](https://github.com/leanprover-community/mathlib/pull/13909))
- add lemmas stating that various sets are measurable with respect to that space
- describe the sigma algebra generated by the minimum of two stopping times
- use the results to generalize `is_stopping_time.measurable_set_eq_const` from nat to first countable linear orders and rename it to `is_stopping_time.measurable_space_eq'` to have a name similar to `is_stopping_time.measurable_set_eq`.
#### Estimated changes
Modified src/probability/martingale.lean


Modified src/probability/stopping.lean
- \- *lemma* measure_theory.adapted.measurable_stopped_process_of_nat
- \+ *lemma* measure_theory.adapted.strongly_measurable_stopped_process_of_nat
- \+ *lemma* measure_theory.is_stopping_time.le_measurable_space_of_const_le
- \- *lemma* measure_theory.is_stopping_time.measurable
- \- *lemma* measure_theory.is_stopping_time.measurable_set
- \- *lemma* measure_theory.is_stopping_time.measurable_set_eq_const
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_inter_eq_iff
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_inter_le
- \- *lemma* measure_theory.is_stopping_time.measurable_set_le
- \+ *lemma* measure_theory.is_stopping_time.measurable_set_min_iff
- \+ *lemma* measure_theory.is_stopping_time.measurable_space_const
- \+/\- *lemma* measure_theory.is_stopping_time.measurable_space_le
- \+ *lemma* measure_theory.is_stopping_time.measurable_space_le_of_le_const
- \+ *lemma* measure_theory.is_stopping_time.measurable_space_min
- \+/\- *lemma* measure_theory.is_stopping_time_const
- \- *lemma* measure_theory.prog_measurable.measurable_stopped_process
- \+ *lemma* measure_theory.prog_measurable.strongly_measurable_stopped_process



## [2022-05-06 10:42:54](https://github.com/leanprover-community/mathlib/commit/f033937)
feat(topology/algebra/monoid): add missing `has_continuous_const_smul` instances ([#13987](https://github.com/leanprover-community/mathlib/pull/13987))
This makes an argument to `exp` redundant.
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean


Modified src/topology/algebra/monoid.lean


Modified src/topology/continuous_function/locally_constant.lean




## [2022-05-06 10:42:53](https://github.com/leanprover-community/mathlib/commit/97c4d4e)
feat(analysis/asymptotics/asymptotics): add `is_O.exists_mem_basis` ([#13973](https://github.com/leanprover-community/mathlib/pull/13973))
#### Estimated changes
Modified src/analysis/asymptotics/asymptotics.lean
- \+ *lemma* asymptotics.is_O.exists_mem_basis



## [2022-05-06 10:07:19](https://github.com/leanprover-community/mathlib/commit/d989305)
feat(algebra/order/monoid_lemmas_zero_lt): add some lemmas assuming `mul_zero_class` `partial_order` / `linear_order` ([#13377](https://github.com/leanprover-community/mathlib/pull/13377))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* zero_lt.left.mul_nonneg
- \+ *lemma* zero_lt.left.neg_of_mul_neg_left
- \+ *lemma* zero_lt.left.neg_of_mul_neg_right
- \+ *lemma* zero_lt.mul_le_mul_left''
- \+ *lemma* zero_lt.mul_le_mul_right''
- \+ *lemma* zero_lt.mul_nonpos_of_nonneg_of_nonpos
- \+ *lemma* zero_lt.mul_nonpos_of_nonpos_of_nonneg
- \+ *lemma* zero_lt.neg_iff_neg_of_mul_pos
- \+ *lemma* zero_lt.neg_of_mul_pos_left
- \+ *lemma* zero_lt.neg_of_mul_pos_right
- \+ *lemma* zero_lt.pos_and_pos_or_neg_and_neg_of_mul_pos
- \+ *lemma* zero_lt.pos_iff_pos_of_mul_pos
- \+ *lemma* zero_lt.pos_of_mul_pos_left
- \+ *lemma* zero_lt.pos_of_mul_pos_right
- \+ *lemma* zero_lt.right.mul_nonneg
- \+ *lemma* zero_lt.right.neg_of_mul_neg_left
- \+ *lemma* zero_lt.right.neg_of_mul_neg_right



## [2022-05-06 10:07:18](https://github.com/leanprover-community/mathlib/commit/1675b78)
feat(algebra/order/monoid_lemmas_zero_lt): add some lemmas assuming `mul_zero_one_class` `partial_order` ([#13375](https://github.com/leanprover-community/mathlib/pull/13375))
#### Estimated changes
Modified src/algebra/order/monoid_lemmas_zero_lt.lean
- \+ *lemma* zero_lt.le_of_le_mul_of_le_one_left'
- \+ *lemma* zero_lt.le_of_le_mul_of_le_one_right'
- \+ *lemma* zero_lt.le_of_mul_le_of_one_le_left'
- \+ *lemma* zero_lt.le_of_mul_le_of_one_le_right'



## [2022-05-06 09:15:39](https://github.com/leanprover-community/mathlib/commit/95413e2)
feat(measure_theory/group/*): various lemmas about invariant measures ([#13539](https://github.com/leanprover-community/mathlib/pull/13539))
* Make the `measurable_equiv` argument to `measure_preserving.symm` explicit. This argument is cannot always be deduced from the other explicit arguments (which can be seen form the changes in `src/measure_theory/constructions/pi.lean`).
* From the sphere eversion project
* Required for convolutions
#### Estimated changes
Modified src/analysis/complex/cauchy_integral.lean


Modified src/dynamics/ergodic/measure_preserving.lean
- \+/\- *lemma* measure_theory.measure_preserving.symm

Modified src/measure_theory/constructions/pi.lean


Modified src/measure_theory/constructions/prod.lean
- \+ *lemma* measure_theory.ae_strongly_measurable.fst
- \+ *lemma* measure_theory.ae_strongly_measurable.snd
- \+ *lemma* measure_theory.quasi_measure_preserving.prod_of_left
- \+ *lemma* measure_theory.quasi_measure_preserving.prod_of_right

Modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* continuous_linear_map.ae_strongly_measurable_comp₂
- \- *lemma* measure_theory.ae_strongly_measurable.ae_strongly_measurable_comp₂
- \+ *lemma* measure_theory.ae_strongly_measurable.comp_measurable'

Modified src/measure_theory/group/arithmetic.lean
- \+ *lemma* measurable_div_const'

Modified src/measure_theory/group/fundamental_domain.lean


Modified src/measure_theory/group/integration.lean
- \+ *lemma* measure_theory.integrable_comp_div_left
- \+ *lemma* measure_theory.integral_div_right_eq_self
- \+ *lemma* measure_theory.integral_smul_eq_self
- \+ *lemma* measure_theory.lintegral_div_right_eq_self

Modified src/measure_theory/group/measurable_equiv.lean
- \+ *def* measurable_equiv.div_left
- \+ *def* measurable_equiv.div_right

Modified src/measure_theory/group/measure.lean
- \+/\- *lemma* measure_theory.forall_measure_preimage_mul_iff
- \+/\- *lemma* measure_theory.forall_measure_preimage_mul_right_iff
- \+ *lemma* measure_theory.map_div_right_ae
- \+ *lemma* measure_theory.map_mul_left_ae
- \+ *lemma* measure_theory.map_mul_right_ae
- \+ *lemma* measure_theory.measure.map_div_left_ae
- \+ *lemma* measure_theory.measure_preserving_mul_left
- \+ *lemma* measure_theory.measure_preserving_mul_right

Modified src/measure_theory/group/prod.lean
- \+ *lemma* measure_theory.absolutely_continuous_map_div_left
- \+ *lemma* measure_theory.absolutely_continuous_map_inv
- \+ *lemma* measure_theory.absolutely_continuous_map_mul_right
- \+/\- *lemma* measure_theory.absolutely_continuous_of_is_mul_left_invariant
- \+/\- *lemma* measure_theory.ae_measure_preimage_mul_right_lt_top
- \+/\- *lemma* measure_theory.ae_measure_preimage_mul_right_lt_top_of_ne_zero
- \+/\- *lemma* measure_theory.lintegral_lintegral_mul_inv
- \+ *lemma* measure_theory.map_div_left_absolutely_continuous
- \+ *lemma* measure_theory.map_inv_absolutely_continuous
- \+ *lemma* measure_theory.map_mul_right_absolutely_continuous
- \+/\- *lemma* measure_theory.map_prod_inv_mul_eq_swap
- \+/\- *lemma* measure_theory.map_prod_mul_inv_eq
- \+/\- *lemma* measure_theory.measurable_measure_mul_right
- \+/\- *lemma* measure_theory.measure_eq_div_smul
- \+/\- *lemma* measure_theory.measure_inv_null
- \+/\- *lemma* measure_theory.measure_lintegral_div_measure
- \+/\- *lemma* measure_theory.measure_mul_lintegral_eq
- \+/\- *lemma* measure_theory.measure_mul_measure_eq
- \+/\- *lemma* measure_theory.measure_mul_right_ne_zero
- \+/\- *lemma* measure_theory.measure_mul_right_null
- \+ *lemma* measure_theory.quasi_measure_preserving_div
- \+ *lemma* measure_theory.quasi_measure_preserving_div_left
- \+/\- *lemma* measure_theory.quasi_measure_preserving_inv
- \+ *lemma* measure_theory.quasi_measure_preserving_mul_right

Modified src/measure_theory/integral/divergence_theorem.lean


Modified src/measure_theory/integral/torus_integral.lean


Modified src/measure_theory/measure/complex_lebesgue.lean


Modified src/measure_theory/measure/lebesgue.lean


Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measurable_equiv.map_ae



## [2022-05-06 06:39:57](https://github.com/leanprover-community/mathlib/commit/ebac9f0)
feat(analysis/special_functions/trigonometric): add a lemma ([#13975](https://github.com/leanprover-community/mathlib/pull/13975))
Add a lemma needed for [#13178](https://github.com/leanprover-community/mathlib/pull/13178)
#### Estimated changes
Modified src/algebra/order/group.lean
- \+ *lemma* apply_abs_le_mul_of_one_le'
- \+ *lemma* apply_abs_le_mul_of_one_le

Modified src/analysis/special_functions/trigonometric/basic.lean
- \+ *lemma* complex.abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le



## [2022-05-06 06:03:17](https://github.com/leanprover-community/mathlib/commit/faf1690)
feat(model_theory/*): Any theory with infinite models has arbitrarily large models ([#13980](https://github.com/leanprover-community/mathlib/pull/13980))
Defines the theory `distinct_constants_theory`, indicating that a set of constants are distinct.
Uses that theory to show that any theory with an infinite model has models of arbitrarily large cardinality.
#### Estimated changes
Modified src/model_theory/bundled.lean
- \+ *lemma* first_order.language.Theory.Model.carrier_eq_coe
- \+/\- *def* first_order.language.Theory.Model.reduct

Modified src/model_theory/language_map.lean


Modified src/model_theory/satisfiability.lean
- \+ *lemma* first_order.language.Theory.exists_large_model_of_infinite_model
- \+ *theorem* first_order.language.Theory.is_satisfiable_union_distinct_constants_theory_of_card_le
- \+ *theorem* first_order.language.Theory.is_satisfiable_union_distinct_constants_theory_of_infinite

Modified src/model_theory/semantics.lean
- \+/\- *lemma* first_order.language.Theory.model.mono
- \+ *lemma* first_order.language.Theory.model.union
- \+/\- *theorem* first_order.language.Theory.model_iff_subset_complete_theory
- \+/\- *lemma* first_order.language.Theory.model_singleton_iff
- \+ *lemma* first_order.language.Theory.model_union_iff
- \+ *lemma* first_order.language.card_le_of_model_distinct_constants_theory
- \+ *lemma* first_order.language.model_distinct_constants_theory

Modified src/model_theory/syntax.lean
- \+ *lemma* first_order.language.directed_distinct_constants_theory
- \+ *def* first_order.language.distinct_constants_theory
- \+ *lemma* first_order.language.distinct_constants_theory_eq_Union
- \+ *lemma* first_order.language.monotone_distinct_constants_theory



## [2022-05-06 01:59:37](https://github.com/leanprover-community/mathlib/commit/f0eded9)
chore(algebra/ring/idempotents): golf iff_eq_zero_or_one ([#13977](https://github.com/leanprover-community/mathlib/pull/13977))
#### Estimated changes
Modified src/algebra/ring/idempotents.lean




## [2022-05-05 23:51:54](https://github.com/leanprover-community/mathlib/commit/151933d)
feat(algebra/group/defs): Division monoids ([#13860](https://github.com/leanprover-community/mathlib/pull/13860))
Introduce what I call division monoids. Those are monoids `α` with a pseudo-inverse `⁻¹ : α → α ` and a pseudo-division `/ : α → α → α` respecting:
* `a / b = a * b⁻¹`
* `a⁻¹⁻¹ = a`
* `(a * b)⁻¹ = b⁻¹ * a⁻¹`
* `a * b = 1 → a⁻¹ = b`
This made-up algebraic structure has two uses:
* Deduplicate lemmas between `group` and `group_with_zero`. Almost all lemmas which are literally duplicated (same conclusion, same assumptions except for `group` vs `group_with_zero`) generalize to division monoids.
* Give access to lemmas for pointwise operations: `set α`, `finset α`, `filter α`, `submonoid α`, `subgroup α`, etc... all are division monoids when `α` is. In some sense, they are very close to being groups, the only obstruction being that `s / s ≠ 1` in general. Hence any identity which is true in a group/group with zero is also true in those pointwise monoids, if no cancellation is involved.
#### Estimated changes
Modified src/algebra/group/basic.lean
- \- *lemma* inv_mul_cancel_right
- \- *lemma* mul_inv_cancel_left
- \- *lemma* mul_inv_rev

Modified src/algebra/group/defs.lean
- \+/\- *lemma* div_eq_mul_inv
- \+/\- *lemma* inv_eq_of_mul_eq_one
- \+/\- *lemma* inv_inv
- \+/\- *lemma* inv_mul_cancel_left
- \+ *lemma* inv_mul_cancel_right
- \+ *lemma* mul_inv_cancel_left
- \+/\- *lemma* mul_inv_cancel_right
- \+ *lemma* mul_inv_rev

Modified src/algebra/group/inj_surj.lean


Modified src/algebra/group/pi.lean


Modified src/algebra/group/prod.lean


Modified src/algebra/group/type_tags.lean


Modified src/algebra/group_with_zero/basic.lean


Modified src/analysis/complex/liouville.lean


Modified src/measure_theory/integral/circle_integral.lean


Modified src/number_theory/bernoulli.lean




## [2022-05-05 22:29:30](https://github.com/leanprover-community/mathlib/commit/c62dfe6)
feat(model_theory/skolem): Downward Löwenheim–Skolem ([#13723](https://github.com/leanprover-community/mathlib/pull/13723))
Proves the Downward Löwenheim–Skolem theorem:  If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of cardinality `κ`.
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.card_functions_sum
- \+ *lemma* first_order.language.card_relations_sum
- \+ *lemma* first_order.language.card_sum

Modified src/model_theory/skolem.lean
- \+ *theorem* first_order.language.card_functions_sum_skolem₁
- \+ *theorem* first_order.language.card_functions_sum_skolem₁_le
- \+ *theorem* first_order.language.exists_elementary_substructure_card_eq
- \+/\- *def* first_order.language.skolem₁
- \+/\- *lemma* first_order.language.substructure.coe_sort_elementary_skolem₁_reduct
- \+/\- *lemma* first_order.language.substructure.skolem₁_reduct_is_elementary

Modified src/model_theory/syntax.lean




## [2022-05-05 20:53:20](https://github.com/leanprover-community/mathlib/commit/91cc3f0)
feat(linear_algebra/basic): ker of a linear map equals ker of the corresponding group hom ([#13858](https://github.com/leanprover-community/mathlib/pull/13858))
#### Estimated changes
Modified src/linear_algebra/basic.lean
- \+ *lemma* linear_map.ker_to_add_subgroup
- \+ *lemma* linear_map.ker_to_add_submonoid
- \+ *lemma* linear_map.range_to_add_subgroup
- \+ *lemma* linear_map.range_to_add_submonoid



## [2022-05-05 19:41:55](https://github.com/leanprover-community/mathlib/commit/c12536a)
fix(gitpod): correct command name ([#13976](https://github.com/leanprover-community/mathlib/pull/13976))
`leanpkg config` doesn't exist, it's `leanpkg configure`.
@b-mehta tricked me in https://github.com/leanprover-community/mathlib/pull/13949#issuecomment-1117589670
#### Estimated changes
Modified .gitpod.yml




## [2022-05-05 17:30:45](https://github.com/leanprover-community/mathlib/commit/73e5dad)
feat(analysis/special_functions/exp): add limits of `exp z` as `re z → ±∞` ([#13974](https://github.com/leanprover-community/mathlib/pull/13974))
#### Estimated changes
Modified src/analysis/special_functions/exp.lean
- \+ *lemma* complex.tendsto_exp_comap_re_at_bot
- \+ *lemma* complex.tendsto_exp_comap_re_at_bot_nhds_within
- \+ *lemma* complex.tendsto_exp_comap_re_at_top



## [2022-05-05 16:19:12](https://github.com/leanprover-community/mathlib/commit/54af9e9)
fix(topology/algebra/infinite_sum): `tsum_neg` doesn't need `summable` ([#13950](https://github.com/leanprover-community/mathlib/pull/13950))
Both sides are 0 in the not-summable case.
#### Estimated changes
Modified src/topology/algebra/infinite_sum.lean
- \+/\- *lemma* tsum_neg



## [2022-05-05 14:55:41](https://github.com/leanprover-community/mathlib/commit/ec44f45)
feat(data/matrix/basic): even more lemmas about `conj_transpose` and `smul` ([#13970](https://github.com/leanprover-community/mathlib/pull/13970))
It turns out none of the lemmas in the previous [#13938](https://github.com/leanprover-community/mathlib/pull/13938) were the ones I needed.
#### Estimated changes
Modified src/algebra/star/module.lean
- \+ *lemma* star_int_cast_smul
- \+ *lemma* star_inv_int_cast_smul
- \+ *lemma* star_inv_nat_cast_smul
- \+ *lemma* star_nat_cast_smul
- \+ *lemma* star_rat_cast_smul

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.conj_transpose_int_cast_smul
- \+ *lemma* matrix.conj_transpose_inv_int_cast_smul
- \+ *lemma* matrix.conj_transpose_inv_nat_cast_smul
- \+ *lemma* matrix.conj_transpose_nat_cast_smul
- \+ *lemma* matrix.conj_transpose_rat_cast_smul



## [2022-05-05 13:11:01](https://github.com/leanprover-community/mathlib/commit/420fabf)
chore(analysis/normed_space/exponential): replace `1/x` with `x⁻¹` ([#13971](https://github.com/leanprover-community/mathlib/pull/13971))
Note that `one_div` makes `⁻¹` the simp-normal form.
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean
- \+/\- *lemma* exp_eq_tsum
- \+/\- *lemma* exp_series_apply_eq
- \+/\- *lemma* exp_series_has_sum_exp'
- \+/\- *lemma* exp_series_sum_eq
- \+/\- *lemma* exp_series_summable'
- \+/\- *lemma* norm_exp_series_summable'

Modified src/analysis/normed_space/spectrum.lean


Modified src/analysis/special_functions/exponential.lean




## [2022-05-05 13:11:00](https://github.com/leanprover-community/mathlib/commit/03f5ac9)
feat(category_theory/simple): simple_iff_subobject_is_simple_order ([#13969](https://github.com/leanprover-community/mathlib/pull/13969))
#### Estimated changes
Modified src/algebra/category/Module/simple.lean
- \+ *lemma* simple_iff_is_simple_module

Modified src/category_theory/limits/shapes/zero_morphisms.lean
- \+ *def* category_theory.limits.iso_zero_of_epi_eq_zero
- \+ *def* category_theory.limits.iso_zero_of_mono_eq_zero

Modified src/category_theory/simple.lean
- \+ *lemma* category_theory.simple_iff_subobject_is_simple_order
- \+ *lemma* category_theory.simple_of_is_simple_order_subobject

Modified src/category_theory/subobject/factor_thru.lean
- \+ *lemma* category_theory.subobject.factor_thru_mk_self
- \+ *lemma* category_theory.subobject.mk_factors_self

Modified src/category_theory/subobject/lattice.lean
- \+ *lemma* category_theory.subobject.mk_eq_bot_iff_zero



## [2022-05-05 13:10:59](https://github.com/leanprover-community/mathlib/commit/929c901)
refactor(ring_theory/*): Remove unnecessary commutativity assumptions ([#13966](https://github.com/leanprover-community/mathlib/pull/13966))
This replaces `[comm_ring R]` or `[comm_semiring R]` with `[ring R]` or `[semiring R]`, without changing any proofs.
#### Estimated changes
Modified src/ring_theory/artinian.lean
- \+/\- *theorem* is_artinian_ring_of_ring_equiv
- \+/\- *theorem* is_artinian_ring_of_surjective

Modified src/ring_theory/finiteness.lean


Modified src/ring_theory/ideal/basic.lean
- \+/\- *lemma* ideal.maximal_of_no_maximal

Modified src/ring_theory/noetherian.lean
- \+/\- *lemma* is_noetherian_ring_iff_ideal_fg
- \+/\- *theorem* is_noetherian_ring_of_ring_equiv
- \+/\- *theorem* is_noetherian_ring_of_surjective
- \+/\- *lemma* submodule.fg_restrict_scalars



## [2022-05-05 13:10:58](https://github.com/leanprover-community/mathlib/commit/8e0ab16)
feat(polynomial/cyclotomic/basic): ɸ_pⁱ irreducible → ɸ_pʲ irreducible for j ≤ i ([#13952](https://github.com/leanprover-community/mathlib/pull/13952))
#### Estimated changes
Modified src/number_theory/cyclotomic/discriminant.lean


Modified src/number_theory/cyclotomic/primitive_roots.lean


Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+/\- *lemma* polynomial.cyclotomic_irreducible_of_irreducible_pow
- \+ *lemma* polynomial.cyclotomic_irreducible_pow_of_irreducible_pow



## [2022-05-05 11:55:59](https://github.com/leanprover-community/mathlib/commit/057e028)
feat(linear_algebra/finite_dimensional): surjective_of_nonzero_of_finrank_eq_one ([#13961](https://github.com/leanprover-community/mathlib/pull/13961))
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* surjective_of_nonzero_of_finrank_eq_one



## [2022-05-05 11:55:58](https://github.com/leanprover-community/mathlib/commit/da06587)
feat(linear_algebra): A-linear maps between finite dimensional vector spaces over k are finite dimensional ([#13934](https://github.com/leanprover-community/mathlib/pull/13934))
#### Estimated changes
Added src/algebra/module/algebra.lean
- \+ *def* linear_map.restrict_scalars_linear_map

Modified src/linear_algebra/matrix/to_lin.lean




## [2022-05-05 09:52:28](https://github.com/leanprover-community/mathlib/commit/4dfbcac)
feat({data/{finset,set},order/filter}/pointwise): More basic API ([#13899](https://github.com/leanprover-community/mathlib/pull/13899))
More basic lemmas about pointwise operations on `set`/`finset`/`filter`. Also make the three APIs more consistent with each other.
#### Estimated changes
Modified src/data/finset/basic.lean
- \+ *lemma* finset.image_inter_subset

Modified src/data/finset/pointwise.lean
- \+ *lemma* finset.div_eq_empty
- \+ *lemma* finset.div_inter_subset
- \+ *lemma* finset.div_nonempty
- \- *lemma* finset.div_nonempty_iff
- \+ *lemma* finset.div_subset_div_left
- \+ *lemma* finset.div_subset_div_right
- \+ *lemma* finset.div_subset_iff
- \+ *lemma* finset.div_union
- \+ *lemma* finset.inter_div_subset
- \+ *lemma* finset.inter_mul_subset
- \+ *lemma* finset.inter_smul_subset
- \+ *lemma* finset.inter_vsub_subset
- \+ *lemma* finset.mul_eq_empty
- \+ *lemma* finset.mul_inter_subset
- \+ *lemma* finset.mul_nonempty
- \- *lemma* finset.mul_nonempty_iff
- \+ *lemma* finset.mul_subset_iff
- \+ *lemma* finset.mul_subset_mul_left
- \+ *lemma* finset.mul_subset_mul_right
- \+ *lemma* finset.mul_union
- \+ *lemma* finset.nonempty.of_div_left
- \+ *lemma* finset.nonempty.of_div_right
- \+ *lemma* finset.nonempty.of_mul_left
- \+ *lemma* finset.nonempty.of_mul_right
- \+ *lemma* finset.nonempty.of_smul_left
- \+ *lemma* finset.nonempty.of_smul_right
- \+ *lemma* finset.nonempty.of_vsub_left
- \+ *lemma* finset.nonempty.of_vsub_right
- \+/\- *lemma* finset.singleton_div_singleton
- \+/\- *lemma* finset.singleton_mul_singleton
- \+/\- *lemma* finset.singleton_smul
- \+/\- *lemma* finset.singleton_smul_singleton
- \+/\- *lemma* finset.singleton_vsub_singleton
- \+ *lemma* finset.smul_eq_empty
- \+ *lemma* finset.smul_finset_eq_empty
- \+ *lemma* finset.smul_finset_inter_subset
- \+ *lemma* finset.smul_finset_nonempty
- \- *lemma* finset.smul_finset_nonempty_iff
- \+ *lemma* finset.smul_finset_union
- \+ *lemma* finset.smul_inter_subset
- \+/\- *lemma* finset.smul_nonempty_iff
- \+/\- *lemma* finset.smul_singleton
- \+ *lemma* finset.smul_subset_iff
- \+ *lemma* finset.smul_subset_smul_left
- \+ *lemma* finset.smul_subset_smul_right
- \+ *lemma* finset.smul_union
- \+/\- *lemma* finset.subset_vsub
- \+ *lemma* finset.union_div
- \+ *lemma* finset.union_mul
- \+ *lemma* finset.union_smul
- \+ *lemma* finset.union_vsub
- \+ *lemma* finset.vsub_eq_empty
- \+ *lemma* finset.vsub_inter_subset
- \+ *lemma* finset.vsub_nonempty
- \- *lemma* finset.vsub_nonempty_iff
- \+ *lemma* finset.vsub_subset_iff
- \+ *lemma* finset.vsub_subset_vsub_left
- \+ *lemma* finset.vsub_subset_vsub_right
- \+ *lemma* finset.vsub_union

Modified src/data/set/basic.lean
- \+ *lemma* set.nonempty.of_image2_left
- \+ *lemma* set.nonempty.of_image2_right
- \+ *lemma* set.nonempty.subset_singleton_iff

Modified src/data/set/pointwise.lean
- \+/\- *lemma* set.Union_div
- \+/\- *lemma* set.Union_div_left_image
- \+/\- *lemma* set.Union_div_right_image
- \+/\- *lemma* set.Union_mul
- \+/\- *lemma* set.Union_mul_left_image
- \+/\- *lemma* set.Union_mul_right_image
- \+/\- *lemma* set.Union_smul
- \+/\- *lemma* set.Union_smul_left_image
- \+/\- *lemma* set.Union_smul_right_image
- \+/\- *lemma* set.div_Union
- \+ *lemma* set.div_eq_empty
- \+/\- *lemma* set.div_inter_subset
- \+/\- *lemma* set.div_mem_div
- \+ *lemma* set.div_nonempty
- \+/\- *lemma* set.div_subset_div
- \+/\- *lemma* set.div_subset_div_left
- \+/\- *lemma* set.div_subset_div_right
- \+ *lemma* set.div_subset_iff
- \+/\- *lemma* set.image_one
- \+/\- *lemma* set.inter_div_subset
- \+/\- *lemma* set.inter_mul_subset
- \+/\- *lemma* set.inter_smul_subset
- \+/\- *lemma* set.mem_one
- \- *lemma* set.mem_smul_of_mem
- \+/\- *lemma* set.mul_Union
- \+ *lemma* set.mul_eq_empty
- \+/\- *lemma* set.mul_inter_subset
- \+/\- *lemma* set.mul_mem_mul
- \+ *lemma* set.mul_nonempty
- \+ *lemma* set.mul_subset_iff
- \+/\- *lemma* set.mul_subset_mul
- \+/\- *lemma* set.mul_subset_mul_left
- \+/\- *lemma* set.mul_subset_mul_right
- \+ *lemma* set.nonempty.div
- \+ *lemma* set.nonempty.of_div_left
- \+ *lemma* set.nonempty.of_div_right
- \+ *lemma* set.nonempty.of_mul_left
- \+ *lemma* set.nonempty.of_mul_right
- \+ *lemma* set.nonempty.of_smul_left
- \+ *lemma* set.nonempty.of_smul_right
- \+ *lemma* set.nonempty.of_vsub_left
- \+ *lemma* set.nonempty.of_vsub_right
- \+ *lemma* set.nonempty.subset_one_iff
- \+/\- *lemma* set.one_mem_one
- \+/\- *lemma* set.one_nonempty
- \+/\- *lemma* set.one_subset
- \+/\- *lemma* set.singleton_div_singleton
- \+/\- *lemma* set.singleton_mul_singleton
- \+/\- *lemma* set.singleton_one
- \+/\- *lemma* set.singleton_smul_singleton
- \+/\- *lemma* set.smul_Union
- \+ *lemma* set.smul_eq_empty
- \+/\- *lemma* set.smul_inter_subset
- \+/\- *lemma* set.smul_mem_smul
- \+/\- *lemma* set.smul_mem_smul_set
- \+ *lemma* set.smul_nonempty
- \+ *lemma* set.smul_set_eq_empty
- \+ *lemma* set.smul_set_nonempty
- \+/\- *lemma* set.smul_subset_smul
- \+/\- *lemma* set.smul_subset_smul_left
- \+/\- *lemma* set.smul_subset_smul_right
- \+ *lemma* set.subset_one_iff_eq
- \+ *lemma* set.vsub_eq_empty
- \+ *lemma* set.vsub_nonempty
- \+/\- *lemma* set.vsub_subset_iff
- \+/\- *lemma* set.vsub_subset_vsub
- \+/\- *lemma* set.vsub_subset_vsub_left
- \+/\- *lemma* set.vsub_subset_vsub_right

Modified src/order/filter/n_ary.lean
- \+ *lemma* filter.ne_bot.of_map₂_left
- \+ *lemma* filter.ne_bot.of_map₂_right

Modified src/order/filter/pointwise.lean
- \+ *lemma* filter.div_pure
- \+ *lemma* filter.inv_eq_bot_iff
- \+ *lemma* filter.inv_pure
- \+ *lemma* filter.mul_pure
- \+ *lemma* filter.ne_bot.of_div_left
- \+ *lemma* filter.ne_bot.of_div_right
- \+ *lemma* filter.ne_bot.of_mul_left
- \+ *lemma* filter.ne_bot.of_mul_right
- \+ *lemma* filter.ne_bot.of_smul_left
- \+ *lemma* filter.ne_bot.of_smul_right
- \+ *lemma* filter.ne_bot.of_vsub_left
- \+ *lemma* filter.ne_bot.of_vsub_right
- \+ *lemma* filter.pure_div
- \+ *lemma* filter.pure_div_pure
- \+ *lemma* filter.pure_mul
- \+ *lemma* filter.pure_mul_pure
- \+ *lemma* filter.pure_smul
- \+ *lemma* filter.pure_smul_pure
- \+ *lemma* filter.pure_vsub
- \+ *lemma* filter.pure_vsub_pure
- \+ *lemma* filter.smul_pure
- \+ *lemma* filter.vsub_pure

Modified src/topology/algebra/filter_basis.lean




## [2022-05-05 07:41:38](https://github.com/leanprover-community/mathlib/commit/f820671)
ci(gitpod): do not rerun get-cache if a workspace is reloaded ([#13949](https://github.com/leanprover-community/mathlib/pull/13949))
Instead, only run it at workspace start. This prevents it clobbering local builds created with `lean --make src` or similar.
I have no idea why the `. /home/gitpod/.profile` line is there, so I've left it to run in the same phase as before.
#### Estimated changes
Modified .gitpod.yml




## [2022-05-05 07:41:37](https://github.com/leanprover-community/mathlib/commit/6970129)
chore(algebra/group/units): add a lemma about is_unit on a coerced unit ([#13947](https://github.com/leanprover-community/mathlib/pull/13947))
#### Estimated changes
Modified src/algebra/group/units.lean
- \+ *lemma* is_unit.unit_of_coe_units



## [2022-05-05 07:41:36](https://github.com/leanprover-community/mathlib/commit/bd944fe)
chore(linear_algebra/free_module): fix name in doc ([#13942](https://github.com/leanprover-community/mathlib/pull/13942))
#### Estimated changes
Modified src/linear_algebra/free_module/basic.lean




## [2022-05-05 07:41:35](https://github.com/leanprover-community/mathlib/commit/4f7603c)
chore(data/matrix/basic): add more lemmas about `conj_transpose` and `smul` ([#13938](https://github.com/leanprover-community/mathlib/pull/13938))
Unfortunately the `star_module` typeclass is of no help here; see [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Is.20star_module.20sensible.20for.20non-commutative.20rings.3F/near/257272767) for some discussion.
In the meantime, this adds the lemmas for the most frequent special cases.
#### Estimated changes
Modified src/algebra/star/basic.lean
- \+/\- *lemma* star_nsmul
- \+/\- *lemma* star_zsmul

Modified src/algebra/star/module.lean
- \+ *lemma* star_rat_smul

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.conj_transpose_nsmul
- \+ *lemma* matrix.conj_transpose_rat_smul
- \+/\- *lemma* matrix.conj_transpose_smul
- \+ *lemma* matrix.conj_transpose_smul_non_comm
- \+ *lemma* matrix.conj_transpose_smul_self
- \+ *lemma* matrix.conj_transpose_zsmul



## [2022-05-05 07:41:33](https://github.com/leanprover-community/mathlib/commit/7eacca3)
feat(analysis/normed/normed_field): limit of `∥a * x∥` as `∥x∥ → ∞` ([#13819](https://github.com/leanprover-community/mathlib/pull/13819))
These lemmas should use `bornology.cobounded` but we don't have an instance `pseudo_metric_space α -> bornology α` yet.
#### Estimated changes
Modified src/analysis/normed/group/basic.lean
- \+ *lemma* filter.tendsto_neg_cobounded

Modified src/analysis/normed/normed_field.lean
- \+ *lemma* filter.tendsto_mul_left_cobounded
- \+ *lemma* filter.tendsto_mul_right_cobounded



## [2022-05-05 05:36:23](https://github.com/leanprover-community/mathlib/commit/03fbe7d)
Update CODE_OF_CONDUCT.md ([#13965](https://github.com/leanprover-community/mathlib/pull/13965))
deleted one character (duplicate space)
#### Estimated changes
Modified CODE_OF_CONDUCT.md




## [2022-05-05 05:36:22](https://github.com/leanprover-community/mathlib/commit/63875ea)
chore(scripts): update nolints.txt ([#13964](https://github.com/leanprover-community/mathlib/pull/13964))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-05-05 05:36:21](https://github.com/leanprover-community/mathlib/commit/116435d)
feat(tactic/alias): fix alias docstrings for implications from iffs ([#13944](https://github.com/leanprover-community/mathlib/pull/13944))
Now they say for instance:
```lean
le_inv_mul_of_mul_le : ∀ {α : Type u} [_inst_1 : group α] [_inst_2 : has_le α] [_inst_3 : covariant_class α α has_mul.mul has_le.le] {a b c : α}, a * b ≤ c → b ≤ a⁻¹ * c
**Alias** of the reverse direction of `le_inv_mul_iff_mul_le`.
```
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60alias.60.20issue.20in.20algebra.2Eorder.2Egroup/near/281158569
#### Estimated changes
Modified src/tactic/alias.lean




## [2022-05-05 05:36:20](https://github.com/leanprover-community/mathlib/commit/524793d)
feat(representation_theory): Action V G is rigid whenever V is ([#13738](https://github.com/leanprover-community/mathlib/pull/13738))
#### Estimated changes
Modified src/algebra/category/Group/basic.lean


Modified src/algebra/category/Mon/basic.lean


Modified src/representation_theory/Action.lean
- \+ *def* Action.functor_category_monoidal_equivalence



## [2022-05-05 05:36:19](https://github.com/leanprover-community/mathlib/commit/b1da074)
feat(data/sum/basic): Shortcuts for the ternary sum of types ([#13678](https://github.com/leanprover-community/mathlib/pull/13678))
Define `sum3.in₀`, `sum3.in₁`, `sum3.in₂`, shortcut patterns for pattern-matching on a ternary sum of types.
#### Estimated changes
Modified src/data/sum/basic.lean
- \+ *def* sum3.in₀
- \+ *def* sum3.in₁
- \+ *def* sum3.in₂



## [2022-05-05 03:36:27](https://github.com/leanprover-community/mathlib/commit/0c9b726)
feat(algebra/group/{pi, opposite}): add missing pi and opposite defs for `mul_hom` ([#13956](https://github.com/leanprover-community/mathlib/pull/13956))
The declaration names and the contents of these definitions are all copied from the corresponding ones for `monoid_hom`.
#### Estimated changes
Modified src/algebra/group/opposite.lean
- \+ *def* add_hom.mul_op
- \+ *def* add_hom.mul_unop
- \+ *def* mul_hom.from_opposite
- \+ *def* mul_hom.op
- \+ *def* mul_hom.to_opposite
- \+ *def* mul_hom.unop

Modified src/algebra/group/pi.lean
- \+ *def* mul_hom.coe_fn
- \+ *def* pi.const_mul_hom
- \+ *def* pi.eval_mul_hom



## [2022-05-05 02:21:58](https://github.com/leanprover-community/mathlib/commit/5078119)
feat(data/matrix/block): add `matrix.block_diag` and `matrix.block_diag'` ([#13918](https://github.com/leanprover-community/mathlib/pull/13918))
`matrix.block_diag` is to `matrix.block_diagonal` as `matrix.diag` is to `matrix.diagonal`.
As well as the basic arithmetic lemmas and bundling, this also adds continuity lemmas.
These definitions are primarily an auxiliary construction to prove `matrix.tsum_block_diagonal`, and `matrix.tsum_block_diagonal'`, which are really the main goal of this PR.
#### Estimated changes
Modified src/data/matrix/block.lean
- \+ *def* matrix.block_diag'
- \+ *lemma* matrix.block_diag'_add
- \+ *def* matrix.block_diag'_add_monoid_hom
- \+ *lemma* matrix.block_diag'_block_diagonal'
- \+ *lemma* matrix.block_diag'_conj_transpose
- \+ *lemma* matrix.block_diag'_diagonal
- \+ *lemma* matrix.block_diag'_map
- \+ *lemma* matrix.block_diag'_neg
- \+ *lemma* matrix.block_diag'_one
- \+ *lemma* matrix.block_diag'_smul
- \+ *lemma* matrix.block_diag'_sub
- \+ *lemma* matrix.block_diag'_transpose
- \+ *lemma* matrix.block_diag'_zero
- \+ *def* matrix.block_diag
- \+ *lemma* matrix.block_diag_add
- \+ *def* matrix.block_diag_add_monoid_hom
- \+ *lemma* matrix.block_diag_block_diagonal
- \+ *lemma* matrix.block_diag_conj_transpose
- \+ *lemma* matrix.block_diag_diagonal
- \+ *lemma* matrix.block_diag_map
- \+ *lemma* matrix.block_diag_neg
- \+ *lemma* matrix.block_diag_one
- \+ *lemma* matrix.block_diag_smul
- \+ *lemma* matrix.block_diag_sub
- \+ *lemma* matrix.block_diag_transpose
- \+ *lemma* matrix.block_diag_zero

Modified src/topology/instances/matrix.lean
- \+ *lemma* continuous.matrix_block_diag'
- \+ *lemma* continuous.matrix_block_diag
- \+ *lemma* has_sum.matrix_block_diag'
- \+ *lemma* has_sum.matrix_block_diag
- \+ *lemma* matrix.block_diagonal'_tsum
- \+ *lemma* matrix.block_diagonal_tsum
- \+ *lemma* summable.matrix_block_diag'
- \+ *lemma* summable.matrix_block_diag
- \+/\- *lemma* summable.matrix_block_diagonal'
- \+ *lemma* summable_matrix_block_diagonal'
- \+ *lemma* summable_matrix_block_diagonal



## [2022-05-05 02:21:58](https://github.com/leanprover-community/mathlib/commit/50fd3d6)
feat(analysis/special_functions/log/monotone): add lemmas ([#13848](https://github.com/leanprover-community/mathlib/pull/13848))
Adds a few lemmas regarding tonality of `log x / x ^ a`, and puts them in a new file, along with previous results.
#### Estimated changes
Modified src/analysis/special_functions/arsinh.lean


Modified src/analysis/special_functions/complex/log.lean


Renamed src/analysis/special_functions/logb.lean to src/analysis/special_functions/log/base.lean


Renamed src/analysis/special_functions/log.lean to src/analysis/special_functions/log/basic.lean
- \- *lemma* real.log_div_self_antitone_on

Renamed src/analysis/special_functions/log_deriv.lean to src/analysis/special_functions/log/deriv.lean


Added src/analysis/special_functions/log/monotone.lean
- \+ *lemma* real.log_div_self_antitone_on
- \+ *lemma* real.log_div_self_rpow_antitone_on
- \+ *lemma* real.log_div_sqrt_antitone_on
- \+ *lemma* real.log_mul_self_monotone_on

Modified src/analysis/special_functions/pow_deriv.lean


Modified src/data/complex/exponential_bounds.lean


Modified src/number_theory/von_mangoldt.lean


Modified test/differentiable.lean




## [2022-05-05 00:25:32](https://github.com/leanprover-community/mathlib/commit/1e18935)
docs(algebra/ring/opposite): fix docstring for `ring_hom.from_opposite` ([#13957](https://github.com/leanprover-community/mathlib/pull/13957))
#### Estimated changes
Modified src/algebra/ring/opposite.lean




## [2022-05-05 00:25:31](https://github.com/leanprover-community/mathlib/commit/3650936)
feat(representation_theory/Action): lemma about isomorphisms in `Action G V` ([#13951](https://github.com/leanprover-community/mathlib/pull/13951))
#### Estimated changes
Modified src/representation_theory/Action.lean
- \+ *lemma* Action.iso.conj_ρ



## [2022-05-05 00:25:30](https://github.com/leanprover-community/mathlib/commit/9b245e2)
feat(analysis/convex/integral): drop an assumption, add a version ([#13920](https://github.com/leanprover-community/mathlib/pull/13920))
* add `convex.set_average_mem_closure`;
* drop `is_closed s` assumption in `convex.average_mem_interior_of_set`;
* add `ae_eq_const_or_norm_average_lt_of_norm_le_const`, a version of `ae_eq_const_or_norm_integral_lt_of_norm_le_const` for average.
#### Estimated changes
Modified src/analysis/convex/integral.lean
- \+ *lemma* ae_eq_const_or_norm_average_lt_of_norm_le_const
- \+ *lemma* convex.set_average_mem_closure



## [2022-05-04 22:19:39](https://github.com/leanprover-community/mathlib/commit/f8c303e)
refactor(order/filter/pointwise): Localize instances ([#13898](https://github.com/leanprover-community/mathlib/pull/13898))
Localize pointwise `filter` instances into the `pointwise` locale, as is done for `set` and `finset`.
#### Estimated changes
Modified src/order/filter/pointwise.lean
- \+ *def* filter.has_involutive_inv



## [2022-05-04 22:19:38](https://github.com/leanprover-community/mathlib/commit/627f81b)
feat(group_theory/order_of_element): The index-th power lands in the subgroup ([#13890](https://github.com/leanprover-community/mathlib/pull/13890))
The PR adds a lemma stating `g ^ index H ∈ H`. I had to restate `G` to avoid the fintype assumption on `G`.
#### Estimated changes
Modified src/group_theory/order_of_element.lean
- \+ *lemma* subgroup.pow_index_mem



## [2022-05-04 22:19:37](https://github.com/leanprover-community/mathlib/commit/5696275)
feat(data/list/big_operators): add `list.sublist.prod_le_prod'` etc ([#13879](https://github.com/leanprover-community/mathlib/pull/13879))
* add `list.forall₂.prod_le_prod'`, `list.sublist.prod_le_prod'`, and `list.sublist_forall₂.prod_le_prod'`;
* add their additive versions;
* upgrade `list.forall₂_same` to an `iff`.
#### Estimated changes
Modified src/data/list/big_operators.lean
- \+ *lemma* list.forall₂.prod_le_prod'
- \+ *lemma* list.sublist.prod_le_prod'
- \+ *lemma* list.sublist_forall₂.prod_le_prod'

Modified src/data/list/forall2.lean
- \+/\- *lemma* list.forall₂_eq_eq_eq
- \+/\- *lemma* list.forall₂_same

Modified src/data/multiset/powerset.lean


Modified src/order/well_founded_set.lean




## [2022-05-04 20:04:22](https://github.com/leanprover-community/mathlib/commit/9503f73)
feat(linear_algebra/dual): dual of a finite free module is finite free ([#13896](https://github.com/leanprover-community/mathlib/pull/13896))
#### Estimated changes
Modified src/linear_algebra/dual.lean




## [2022-05-04 20:04:21](https://github.com/leanprover-community/mathlib/commit/eb1a566)
refactor(set_theory/game/ordinal): Improve API ([#13878](https://github.com/leanprover-community/mathlib/pull/13878))
We change our former equivalence `o.out.α ≃ o.to_pgame.left_moves` to an equivalence `{o' // o' < o} ≃ o.to_pgame.left_moves`. This makes two proofs much simpler. 
We also add a simple missing lemma, `to_pgame_equiv_iff`.
#### Estimated changes
Modified src/set_theory/game/ordinal.lean
- \- *def* ordinal.to_left_moves_to_pgame
- \+ *theorem* ordinal.to_left_moves_to_pgame_symm_lt
- \+ *theorem* ordinal.to_pgame_equiv_iff
- \+ *theorem* ordinal.to_pgame_move_left'
- \+/\- *theorem* ordinal.to_pgame_move_left



## [2022-05-04 20:04:20](https://github.com/leanprover-community/mathlib/commit/28568bd)
feat(set_theory/game/nim): Add basic API ([#13857](https://github.com/leanprover-community/mathlib/pull/13857))
#### Estimated changes
Modified src/set_theory/game/nim.lean
- \+/\- *lemma* pgame.nim.exists_move_left_eq
- \+/\- *lemma* pgame.nim.exists_ordinal_move_left_eq
- \+ *lemma* pgame.nim.left_moves_nim
- \+ *lemma* pgame.nim.move_left_nim'
- \+ *lemma* pgame.nim.move_left_nim
- \+ *lemma* pgame.nim.move_left_nim_heq
- \+ *lemma* pgame.nim.move_right_nim'
- \+ *lemma* pgame.nim.move_right_nim
- \+ *lemma* pgame.nim.move_right_nim_heq
- \+ *lemma* pgame.nim.neg_nim
- \+ *lemma* pgame.nim.right_moves_nim
- \+ *theorem* pgame.nim.to_left_moves_nim_symm_lt
- \+ *theorem* pgame.nim.to_right_moves_nim_symm_lt



## [2022-05-04 20:04:19](https://github.com/leanprover-community/mathlib/commit/a80e568)
feat(logic/equiv/set): equivalences between all preimages gives an equivalence of domains ([#13853](https://github.com/leanprover-community/mathlib/pull/13853))
#### Estimated changes
Modified src/data/fintype/card.lean


Modified src/group_theory/coset.lean


Modified src/group_theory/group_action/basic.lean


Modified src/group_theory/p_group.lean


Modified src/logic/equiv/basic.lean
- \+ *def* equiv.of_fiber_equiv
- \+ *lemma* equiv.of_fiber_equiv_map
- \+ *def* equiv.sigma_fiber_equiv
- \- *def* equiv.sigma_preimage_equiv
- \+ *def* equiv.sigma_subtype_fiber_equiv
- \+ *def* equiv.sigma_subtype_fiber_equiv_subtype
- \- *def* equiv.sigma_subtype_preimage_equiv
- \- *def* equiv.sigma_subtype_preimage_equiv_subtype

Modified src/logic/equiv/set.lean
- \+ *def* equiv.of_preimage_equiv
- \+ *lemma* equiv.of_preimage_equiv_map
- \+ *def* equiv.sigma_preimage_equiv

Modified src/logic/small.lean


Modified src/set_theory/cardinal/basic.lean




## [2022-05-04 20:04:18](https://github.com/leanprover-community/mathlib/commit/edf6cef)
feat(set_theory/game/nim): `nim 0` is a relabelling of `0` and `nim 1` is a relabelling of `star` ([#13846](https://github.com/leanprover-community/mathlib/pull/13846))
#### Estimated changes
Modified src/set_theory/game/nim.lean
- \+ *lemma* pgame.grundy_value_star
- \+/\- *lemma* pgame.grundy_value_zero
- \+ *theorem* pgame.nim.nim_one_equiv
- \+ *theorem* pgame.nim.nim_zero_equiv
- \+ *def* pgame.nim.nim_zero_relabelling

Modified src/set_theory/ordinal/arithmetic.lean
- \+ *theorem* ordinal.one_out_eq
- \+ *theorem* ordinal.typein_one_out
- \+/\- *theorem* ordinal.zero_lt_one



## [2022-05-04 20:04:17](https://github.com/leanprover-community/mathlib/commit/fd8474f)
feat(algebra/ring/idempotents): Introduce idempotents ([#13830](https://github.com/leanprover-community/mathlib/pull/13830))
#### Estimated changes
Added src/algebra/ring/idempotents.lean
- \+ *lemma* is_idempotent_elem.coe_compl
- \+ *lemma* is_idempotent_elem.coe_one
- \+ *lemma* is_idempotent_elem.coe_zero
- \+ *lemma* is_idempotent_elem.compl_compl
- \+ *lemma* is_idempotent_elem.eq
- \+ *lemma* is_idempotent_elem.iff_eq_one
- \+ *lemma* is_idempotent_elem.iff_eq_zero_or_one
- \+ *lemma* is_idempotent_elem.mul_of_commute
- \+ *lemma* is_idempotent_elem.of_is_idempotent
- \+ *lemma* is_idempotent_elem.one
- \+ *lemma* is_idempotent_elem.one_compl
- \+ *lemma* is_idempotent_elem.one_sub
- \+ *lemma* is_idempotent_elem.one_sub_iff
- \+ *lemma* is_idempotent_elem.pow
- \+ *lemma* is_idempotent_elem.pow_succ_eq
- \+ *lemma* is_idempotent_elem.zero
- \+ *lemma* is_idempotent_elem.zero_compl
- \+ *def* is_idempotent_elem



## [2022-05-04 20:04:15](https://github.com/leanprover-community/mathlib/commit/91c0ef8)
feat(analysis/normed_space/weak_dual): add the rest of Banach-Alaoglu theorem ([#9862](https://github.com/leanprover-community/mathlib/pull/9862))
The second of two parts to add the Banach-Alaoglu theorem about the compactness of the closed unit ball (and more generally polar sets of neighborhoods of the origin) of the dual of a normed space in the weak-star topology.
This second half is about the embedding of the weak dual of a normed space into a (big) product of the ground fields, and the required compactness statements from Tychonoff's theorem. In particular it contains the actual Banach-Alaoglu theorem.
Co-Authored-By: Yury Kudryashov <urkud@urkud.name>
#### Estimated changes
Modified src/analysis/normed_space/dual.lean


Modified src/analysis/normed_space/operator_norm.lean
- \+ *lemma* continuous_linear_map.is_closed_image_coe_closed_ball
- \+ *lemma* continuous_linear_map.is_closed_image_coe_of_bounded_of_weak_closed
- \+ *lemma* continuous_linear_map.is_compact_closure_image_coe_of_bounded
- \+ *lemma* continuous_linear_map.is_compact_image_coe_closed_ball
- \+ *lemma* continuous_linear_map.is_compact_image_coe_of_bounded_of_closed_image
- \+ *lemma* continuous_linear_map.is_compact_image_coe_of_bounded_of_weak_closed
- \+ *lemma* continuous_linear_map.is_weak_closed_closed_ball

Modified src/analysis/normed_space/weak_dual.lean
- \+ *lemma* normed_space.dual.coe_to_weak_dual
- \+ *lemma* normed_space.dual.is_closed_image_polar_of_mem_nhds
- \+/\- *def* normed_space.dual.to_weak_dual
- \+/\- *theorem* normed_space.dual.to_weak_dual_continuous
- \- *lemma* weak_dual.coe_to_fun_eq_normed_coe_to_fun
- \+ *lemma* weak_dual.coe_to_normed_dual
- \+ *lemma* weak_dual.is_closed_closed_ball
- \+ *lemma* weak_dual.is_closed_image_coe_of_bounded_of_closed
- \+ *lemma* weak_dual.is_closed_image_polar_of_mem_nhds
- \+ *lemma* weak_dual.is_closed_polar
- \+ *theorem* weak_dual.is_compact_closed_ball
- \+ *lemma* weak_dual.is_compact_of_bounded_of_closed
- \+ *theorem* weak_dual.is_compact_polar
- \+ *def* weak_dual.polar
- \+ *lemma* weak_dual.polar_def
- \- *lemma* weak_dual.to_normed_dual.preimage_closed_unit_ball
- \+/\- *def* weak_dual.to_normed_dual
- \+/\- *lemma* weak_dual.to_normed_dual_eq_iff

Modified src/topology/algebra/module/weak_dual.lean


Modified src/topology/maps.lean
- \+ *lemma* inducing.is_closed_iff'

Modified src/topology/order.lean
- \+ *lemma* is_closed_induced_iff'



## [2022-05-04 17:58:32](https://github.com/leanprover-community/mathlib/commit/90d6f27)
ci(workflows/dependent-issues): run once every 15 mins, instead of on every merged PR ([#13940](https://github.com/leanprover-community/mathlib/pull/13940))
#### Estimated changes
Modified .github/workflows/dependent-issues.yml




## [2022-05-04 17:58:30](https://github.com/leanprover-community/mathlib/commit/aabcd89)
chore(analysis/analytic_composition): weaken some typeclass arguments ([#13924](https://github.com/leanprover-community/mathlib/pull/13924))
There's no need to do a long computation to show the multilinear_map is bounded, when continuity follows directly from the definition.
This deletes `comp_along_composition_aux`, and moves the lemmas about the norm of `comp_along_composition` further down the file so as to get the lemmas with weaker typeclass requirements out of the way first.
The norm proofs are essentially unchanged.
#### Estimated changes
Modified src/analysis/analytic/composition.lean
- \- *def* continuous_multilinear_map.comp_along_composition_aux
- \- *lemma* continuous_multilinear_map.comp_along_composition_aux_bound
- \+ *lemma* formal_multilinear_series.comp_along_composition_bound

Modified src/analysis/normed_space/indicator_function.lean




## [2022-05-04 17:58:29](https://github.com/leanprover-community/mathlib/commit/209bb5d)
feat(set_theory/game/{pgame, basic}): Add more order lemmas ([#13807](https://github.com/leanprover-community/mathlib/pull/13807))
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \+ *theorem* game.lt_or_eq_of_le

Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.lt_or_equiv_of_le
- \+ *theorem* pgame.lt_or_equiv_or_gt



## [2022-05-04 17:58:28](https://github.com/leanprover-community/mathlib/commit/3152982)
feat(representation/Rep): linear structures ([#13782](https://github.com/leanprover-community/mathlib/pull/13782))
Make `Rep k G` a `k`-linear (and `k`-linear monoidal) category.
#### Estimated changes
Modified src/algebra/category/Module/monoidal.lean


Modified src/category_theory/linear/default.lean


Added src/category_theory/linear/functor_category.lean
- \+ *def* category_theory.nat_trans.app_linear_map
- \+ *lemma* category_theory.nat_trans.app_smul

Added src/category_theory/monoidal/linear.lean


Modified src/category_theory/monoidal/transport.lean


Modified src/category_theory/preadditive/functor_category.lean


Modified src/representation_theory/Action.lean
- \+ *lemma* Action.add_hom
- \+ *lemma* Action.associator_hom_hom
- \+ *lemma* Action.associator_inv_hom
- \+/\- *def* Action.forget_braided
- \+ *lemma* Action.left_unitor_hom_hom
- \+ *lemma* Action.left_unitor_inv_hom
- \+ *lemma* Action.neg_hom
- \+ *lemma* Action.right_unitor_hom_hom
- \+ *lemma* Action.right_unitor_inv_hom
- \+ *lemma* Action.smul_hom
- \+ *lemma* Action.tensor_V
- \+ *lemma* Action.tensor_hom
- \+ *lemma* Action.tensor_rho
- \+ *lemma* Action.zero_hom

Modified src/representation_theory/Rep.lean




## [2022-05-04 17:58:27](https://github.com/leanprover-community/mathlib/commit/0009ffb)
refactor(linear_algebra/charpoly): split file to reduce imports ([#13778](https://github.com/leanprover-community/mathlib/pull/13778))
While working on representation theory I was annoyed to find that essentially all of field theory was being transitively imported (causing lots of unnecessary recompilation). This improves the situation slightly.
#### Estimated changes
Modified archive/100-theorems-list/83_friendship_graphs.lean


Modified src/linear_algebra/charpoly/basic.lean


Modified src/linear_algebra/matrix/charpoly/coeff.lean
- \- *lemma* charpoly_left_mul_matrix
- \- *lemma* finite_field.matrix.charpoly_pow_card
- \- *lemma* finite_field.trace_pow_card
- \- *theorem* matrix.is_integral
- \- *theorem* matrix.minpoly_dvd_charpoly
- \- *lemma* zmod.charpoly_pow_card
- \- *lemma* zmod.trace_pow_card

Added src/linear_algebra/matrix/charpoly/finite_field.lean
- \+ *lemma* finite_field.matrix.charpoly_pow_card
- \+ *lemma* finite_field.trace_pow_card
- \+ *lemma* zmod.charpoly_pow_card
- \+ *lemma* zmod.trace_pow_card

Added src/linear_algebra/matrix/charpoly/minpoly.lean
- \+ *lemma* charpoly_left_mul_matrix
- \+ *theorem* matrix.is_integral
- \+ *theorem* matrix.minpoly_dvd_charpoly

Modified src/ring_theory/norm.lean


Modified src/ring_theory/trace.lean




## [2022-05-04 17:58:26](https://github.com/leanprover-community/mathlib/commit/dd4590a)
refactor(algebra/restrict_scalars): remove global instance on module_orig ([#13759](https://github.com/leanprover-community/mathlib/pull/13759))
The global instance was conceptually wrong, unnecessary (after avoiding a hack in algebra/lie/base_change.lean), and wreaking havoc in [#13713](https://github.com/leanprover-community/mathlib/pull/13713).
#### Estimated changes
Modified src/algebra/algebra/restrict_scalars.lean
- \+ *def* restrict_scalars.add_equiv
- \+ *lemma* restrict_scalars.add_equiv_map_smul
- \- *def* restrict_scalars.alg_equiv
- \- *def* restrict_scalars.linear_equiv
- \- *lemma* restrict_scalars.linear_equiv_map_smul
- \+ *def* restrict_scalars.lsmul
- \+ *def* restrict_scalars.module_orig
- \+ *def* restrict_scalars.ring_equiv
- \+ *lemma* restrict_scalars.ring_equiv_algebra_map
- \+ *lemma* restrict_scalars.ring_equiv_map_smul

Modified src/algebra/lie/base_change.lean


Modified src/analysis/normed_space/basic.lean
- \+ *def* module.restrict_scalars.normed_space_orig

Modified src/analysis/normed_space/extend.lean


Modified src/ring_theory/algebra_tower.lean
- \- *theorem* algebra.adjoin_algebra_map'



## [2022-05-04 17:58:24](https://github.com/leanprover-community/mathlib/commit/abcd601)
fix(src/tactic/alias): Teach `get_alias_target` about `alias f ↔ a b` ([#13742](https://github.com/leanprover-community/mathlib/pull/13742))
the `get_alias_target` function in `alias.lean` is used by the
`to_additive` command to add the “Alias of …” docstring when creating an
additive version of an existing alias (this was [#13330](https://github.com/leanprover-community/mathlib/pull/13330)).
But `get_alias_target` did not work for `alias f ↔ a b`. This fixes it
by extending the `alias_attr` map to not just store whether a defintion
is an alias, but also what it is an alias of. Much more principled than
trying to reconstruct the alias target from the RHS of the alias
definition.
Note that `alias` currently says “Alias of `foo_iff`” even though it’s
really an alias of `foo_iff.mp`. This is an existing bug, not fixed in
this PR – the effect is just that this “bug” will uniformly apply to
additive lemmas as well.
Hopefully will get rid of plenty of nolint.txt entries, and create
better docs.
Also improve the test file for the linter significantly.
#### Estimated changes
Modified src/algebra/parity.lean


Modified src/tactic/alias.lean


Modified test/lint_to_additive_doc.lean
- \+ *def* a_one_iff_b_one
- \- *def* no_to_additive
- \+ *def* without_to_additive



## [2022-05-04 15:53:31](https://github.com/leanprover-community/mathlib/commit/0038a04)
feat(data/int/cast): int cast division lemmas ([#13929](https://github.com/leanprover-community/mathlib/pull/13929))
Adds lemmas for passing int cast through division, and renames the nat versions from `nat.cast_dvd` to `nat.cast_div`. 
Also some golf.
#### Estimated changes
Modified src/algebra/char_zero.lean
- \+ *theorem* nat.cast_div_char_zero
- \- *theorem* nat.cast_dvd_char_zero

Modified src/data/int/cast.lean
- \+ *theorem* int.cast_div

Modified src/data/int/char_zero.lean
- \+ *theorem* int.cast_div_char_zero

Modified src/data/nat/cast.lean
- \+ *theorem* nat.cast_div
- \- *theorem* nat.cast_dvd

Modified src/data/nat/totient.lean


Modified src/number_theory/bernoulli.lean


Modified src/number_theory/von_mangoldt.lean


Modified src/ring_theory/discriminant.lean


Modified src/ring_theory/power_series/well_known.lean




## [2022-05-04 15:53:30](https://github.com/leanprover-community/mathlib/commit/4602370)
feat(set_theory/game/birthday): More basic lemmas on birthdays ([#13729](https://github.com/leanprover-community/mathlib/pull/13729))
#### Estimated changes
Modified src/set_theory/game/birthday.lean
- \+ *theorem* pgame.birthday_add_zero
- \+ *theorem* pgame.birthday_one
- \+ *theorem* pgame.birthday_zero_add

Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.nat_one



## [2022-05-04 15:53:29](https://github.com/leanprover-community/mathlib/commit/60ad844)
feat(group_theory/complement): API lemmas relating `range_mem_transversals` and `to_equiv` ([#13694](https://github.com/leanprover-community/mathlib/pull/13694))
This PR adds an API lemma relating `range_mem_left_transversals` (the main way of constructing left transversals) and `mem_left_transversals.to_equiv` (one of the main constructions from left transversals), and a similar lemma relating the right versions.
#### Estimated changes
Modified src/group_theory/complement.lean
- \+ *lemma* subgroup.mem_left_transversals.to_equiv_apply
- \+ *lemma* subgroup.mem_right_transversals.to_equiv_apply



## [2022-05-04 15:53:28](https://github.com/leanprover-community/mathlib/commit/923ae0b)
feat(group_theory/free_group): is_free_group via `free_group X ≃* G` ([#13633](https://github.com/leanprover-community/mathlib/pull/13633))
The previous definition of the `is_free_group` class was defined via the universal
property of free groups, which is intellectually pleasing, but
technically annoying, due to the universe problems of quantifying over
“all other groups” in the definition. To work around them, many
definitions had to be duplicated.
This changes the definition of `is_free_group` to contain an isomorphism
between the `free_group` over the generator and `G`. It also moves this
class into `free_group.lean`, so that it can be found more easily.
Relevant Zulip thread:
<https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/universe.20levels.20for.20is_free_group>
A previous attempt at reforming `is_free_group` to unbundle the set
of generators (`is_freely_generated_by G X`) is on branch
`joachim/is_freely_generated_by`, but it wasn't very elegant to use in some places.
#### Estimated changes
Modified src/group_theory/free_product.lean


Modified src/group_theory/is_free_group.lean
- \- *lemma* is_free_group.ext_hom'
- \+/\- *lemma* is_free_group.ext_hom
- \- *def* is_free_group.lift'
- \- *lemma* is_free_group.lift'_of
- \+/\- *def* is_free_group.lift
- \- *lemma* is_free_group.lift_eq_free_group_lift
- \+/\- *lemma* is_free_group.lift_of
- \+ *lemma* is_free_group.lift_symm_apply
- \+ *def* is_free_group.of
- \+/\- *lemma* is_free_group.of_eq_free_group_of
- \+ *def* is_free_group.of_lift
- \+/\- *def* is_free_group.of_mul_equiv
- \+ *def* is_free_group.of_unique_lift
- \+/\- *def* is_free_group.to_free_group
- \+/\- *lemma* is_free_group.unique_lift

Modified src/group_theory/nielsen_schreier.lean
- \+/\- *def* is_free_groupoid.spanning_tree.End_is_free



## [2022-05-04 15:53:27](https://github.com/leanprover-community/mathlib/commit/552a470)
feat(number_theory/cyclotomic/rat): the ring of integers of cyclotomic fields. ([#13585](https://github.com/leanprover-community/mathlib/pull/13585))
We compute the ring of integers of a `p ^ n`-th cyclotomic extension of `ℚ`.
From flt-regular
#### Estimated changes
Modified src/number_theory/cyclotomic/basic.lean
- \+ *lemma* is_cyclotomic_extension.singleton_one

Modified src/number_theory/cyclotomic/discriminant.lean
- \+ *lemma* is_cyclotomic_extension.discr_prime_pow
- \+ *lemma* is_cyclotomic_extension.discr_prime_pow_eq_unit_mul_pow
- \+ *lemma* is_cyclotomic_extension.discr_prime_pow_ne_two'

Added src/number_theory/cyclotomic/rat.lean
- \+ *lemma* is_cyclotomic_extension.rat.cyclotomic_ring_is_integral_closure_of_prime
- \+ *lemma* is_cyclotomic_extension.rat.cyclotomic_ring_is_integral_closure_of_prime_pow
- \+ *lemma* is_cyclotomic_extension.rat.discr_odd_prime'
- \+ *lemma* is_cyclotomic_extension.rat.discr_prime_pow'
- \+ *lemma* is_cyclotomic_extension.rat.discr_prime_pow_eq_unit_mul_pow'
- \+ *lemma* is_cyclotomic_extension.rat.discr_prime_pow_ne_two'
- \+ *lemma* is_cyclotomic_extension.rat.is_integral_closure_adjoing_singleton_of_prime
- \+ *lemma* is_cyclotomic_extension.rat.is_integral_closure_adjoing_singleton_of_prime_pow

Modified src/ring_theory/polynomial/cyclotomic/basic.lean
- \+ *lemma* polynomial.cyclotomic_irreducible_of_irreducible_pow



## [2022-05-04 15:53:26](https://github.com/leanprover-community/mathlib/commit/e716139)
feat(algebra/homology/Module): API for complexes of modules ([#12622](https://github.com/leanprover-community/mathlib/pull/12622))
API for homological complexes in `Module R`.
#### Estimated changes
Modified src/algebra/category/Module/kernels.lean
- \+ *lemma* Module.cokernel_π_ext

Modified src/algebra/category/Module/subobject.lean
- \+ *lemma* Module.cokernel_π_image_subobject_ext
- \+ *lemma* Module.to_kernel_subobject_arrow

Added src/algebra/homology/Module.lean
- \+ *lemma* Module.cycles_ext
- \+ *lemma* Module.cycles_map_to_cycles
- \+ *lemma* Module.homology_ext'
- \+ *lemma* Module.homology_ext
- \+ *abbreviation* Module.to_cycles
- \+ *abbreviation* Module.to_homology

Modified src/algebra/homology/homology.lean
- \+/\- *lemma* cycles_map_arrow
- \- *lemma* homological_complex.boundaries_to_cycles_arrow
- \+ *abbreviation* homological_complex.cycles
- \- *def* homological_complex.cycles
- \- *lemma* homological_complex.cycles_arrow_d_from

Modified src/category_theory/limits/concrete_category.lean
- \+ *lemma* category_theory.limits.cokernel_funext



## [2022-05-04 15:53:24](https://github.com/leanprover-community/mathlib/commit/a7c5097)
feat(set_theory/cardinal/cofinality): Cofinality of normal functions ([#12384](https://github.com/leanprover-community/mathlib/pull/12384))
If `f` is normal and `a` is limit, then `cof (f a) = cof a`. We use this to golf `cof_add` from 24 lines down to 6.
#### Estimated changes
Modified src/set_theory/cardinal/cofinality.lean
- \+ *theorem* ordinal.aleph'_cof
- \+ *theorem* ordinal.aleph_cof
- \+ *theorem* ordinal.cof_ne_zero
- \+ *theorem* ordinal.is_normal.cof_eq
- \+ *theorem* ordinal.is_normal.cof_le



## [2022-05-04 15:53:23](https://github.com/leanprover-community/mathlib/commit/d565adb)
feat(analysis/convex/topology): Separating by convex sets ([#11458](https://github.com/leanprover-community/mathlib/pull/11458))
When `s` is compact, `t` is closed and both are convex, we can find disjoint open convex sets containing `s` and `t`.
#### Estimated changes
Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex.neg
- \+/\- *lemma* convex_Inter
- \+ *lemma* convex_Inter₂

Modified src/analysis/convex/topology.lean
- \+ *lemma* convex.cthickening
- \+ *lemma* convex.thickening
- \+/\- *lemma* convex_on_dist
- \+/\- *lemma* convex_on_norm
- \+ *lemma* disjoint.exists_open_convexes

Modified src/topology/metric_space/hausdorff_distance.lean
- \+ *lemma* disjoint.exists_cthickenings
- \+ *lemma* disjoint.exists_thickenings
- \+ *lemma* emetric.exists_pos_forall_le_edist



## [2022-05-04 14:57:36](https://github.com/leanprover-community/mathlib/commit/32320a1)
feat(measure_theory/integral/lebesgue): speed up a proof ([#13946](https://github.com/leanprover-community/mathlib/pull/13946))
#### Estimated changes
Modified src/measure_theory/integral/lebesgue.lean




## [2022-05-04 11:10:47](https://github.com/leanprover-community/mathlib/commit/ceca8d7)
fix(ring_theory/polynomial/basic): fix unexpected change of an implicit parameter ([#13935](https://github.com/leanprover-community/mathlib/pull/13935))
Fix unexpected change of an implicit parameter in the previous PR([#13800](https://github.com/leanprover-community/mathlib/pull/13800)).
Fix docstring.
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean
- \+/\- *def* polynomial.degree_lt_equiv



## [2022-05-04 11:10:46](https://github.com/leanprover-community/mathlib/commit/53c79d5)
feat(linear_algebra/span): add `finite_span_is_compact_element` ([#13901](https://github.com/leanprover-community/mathlib/pull/13901))
This PR adds `finite_span_is_compact_element`, which extends `singleton_span_is_compact_element` to the spans of finite subsets.
This will be useful e.g. when proving the existence of a maximal submodule of a finitely generated module.
#### Estimated changes
Modified src/linear_algebra/span.lean
- \+ *lemma* submodule.finite_span_is_compact_element
- \+ *lemma* submodule.finset_span_is_compact_element



## [2022-05-04 11:10:45](https://github.com/leanprover-community/mathlib/commit/a057441)
feat(order/basic): Notation for `order_dual` ([#13798](https://github.com/leanprover-community/mathlib/pull/13798))
Define `αᵒᵈ` as notation for `order_dual α` and replace current uses.
[Zulip poll](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Notation.20for.20order_dual/near/280629129)
#### Estimated changes
Modified src/algebra/big_operators/multiset.lean


Modified src/algebra/big_operators/order.lean


Modified src/algebra/bounds.lean


Modified src/algebra/group_power/order.lean
- \+ *lemma* pow_le_one'
- \- *theorem* pow_le_one'
- \+ *lemma* pow_lt_one'
- \- *theorem* pow_lt_one'

Modified src/algebra/indicator_function.lean


Modified src/algebra/order/archimedean.lean


Modified src/algebra/order/field.lean


Modified src/algebra/order/group.lean
- \+/\- *def* order_iso.inv

Modified src/algebra/order/module.lean
- \+/\- *def* order_iso.smul_left_dual

Modified src/algebra/order/monoid.lean


Modified src/algebra/order/ring.lean


Modified src/algebra/order/smul.lean
- \+/\- *lemma* order_dual.of_dual_smul

Modified src/algebra/order/with_zero.lean


Modified src/algebra/support.lean


Modified src/algebraic_geometry/prime_spectrum/basic.lean
- \+/\- *lemma* prime_spectrum.gc
- \+/\- *lemma* prime_spectrum.gc_set

Modified src/algebraic_geometry/projective_spectrum/topology.lean


Modified src/analysis/box_integral/partition/filter.lean
- \+/\- *def* box_integral.integration_params.equiv_prod
- \+/\- *def* box_integral.integration_params.iso_prod

Modified src/analysis/convex/basic.lean
- \+/\- *lemma* convex_Ici
- \+/\- *lemma* convex_Ioi

Modified src/analysis/convex/extrema.lean


Modified src/analysis/convex/function.lean


Modified src/analysis/convex/jensen.lean


Modified src/analysis/convex/quasiconvex.lean


Modified src/analysis/convex/strict.lean
- \+/\- *lemma* strict_convex_Ici

Modified src/analysis/inner_product_space/basic.lean


Modified src/analysis/normed_space/lattice_ordered_group.lean


Modified src/combinatorics/pigeonhole.lean


Modified src/data/fin/basic.lean
- \+/\- *def* order_iso.fin_equiv

Modified src/data/fin/tuple/basic.lean


Modified src/data/finset/lattice.lean
- \+/\- *lemma* finset.inf'_const
- \+/\- *lemma* finset.inf'_le
- \+/\- *lemma* finset.inf'_le_iff
- \+/\- *lemma* finset.inf'_lt_iff
- \+/\- *lemma* finset.inf_eq_infi
- \+/\- *lemma* finset.inf_id_eq_Inf
- \+/\- *lemma* finset.inf_top
- \+/\- *lemma* finset.infi_option_to_finset
- \+/\- *lemma* finset.le_inf'
- \+/\- *lemma* finset.lt_inf'_iff
- \+/\- *lemma* finset.lt_min'_iff
- \+/\- *theorem* finset.mem_of_min
- \+/\- *lemma* finset.min'_eq_inf'
- \+/\- *lemma* infi_eq_infi_finset

Modified src/data/finset/locally_finite.lean


Modified src/data/finset/pi_induction.lean


Modified src/data/finset/sigma.lean


Modified src/data/fintype/basic.lean
- \+/\- *lemma* fintype.card_order_dual

Modified src/data/list/big_operators.lean


Modified src/data/list/min_max.lean
- \+/\- *def* list.argmin
- \+/\- *lemma* list.le_min_of_le_forall
- \+/\- *lemma* list.minimum_eq_coe_foldr_min_of_ne_nil

Modified src/data/nat/lattice.lean


Modified src/data/nat/pairing.lean


Modified src/data/ordmap/ordset.lean
- \+/\- *theorem* ordnode.bounded.dual_iff
- \+/\- *theorem* ordnode.valid'.dual
- \+/\- *theorem* ordnode.valid'.dual_iff
- \+/\- *theorem* ordnode.valid.dual
- \+/\- *theorem* ordnode.valid.dual_iff

Modified src/data/real/ennreal.lean
- \+/\- *def* order_iso.inv_ennreal

Modified src/data/real/ereal.lean
- \+/\- *def* ereal.neg_order_iso

Modified src/data/set/finite.lean


Modified src/data/set/function.lean


Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.Iic_subset_Iic

Modified src/data/set/intervals/infinite.lean
- \+/\- *lemma* set.Ioi.infinite

Modified src/data/set/intervals/pi.lean


Modified src/data/set/intervals/with_bot_top.lean
- \+/\- *lemma* with_bot.range_coe

Modified src/data/sum/order.lean
- \+/\- *def* order_iso.sum_dual_distrib
- \+/\- *def* order_iso.sum_lex_dual_antidistrib

Modified src/field_theory/galois.lean


Modified src/linear_algebra/affine_space/ordered.lean


Modified src/linear_algebra/basic.lean
- \+/\- *def* linear_map.iterate_range

Modified src/linear_algebra/prod.lean
- \+/\- *def* linear_map.tunnel

Modified src/measure_theory/constructions/borel_space.lean


Modified src/measure_theory/function/ess_sup.lean


Modified src/measure_theory/function/locally_integrable.lean


Modified src/measure_theory/integral/interval_integral.lean


Modified src/measure_theory/lattice.lean


Modified src/measure_theory/measurable_space_def.lean


Modified src/measure_theory/measure/measure_space.lean
- \+/\- *lemma* measure_theory.Ioi_ae_eq_Ici'

Modified src/measure_theory/pi_system.lean


Modified src/order/antisymmetrization.lean


Modified src/order/atoms.lean
- \+ *lemma* is_atomic_dual_iff_is_coatomic
- \- *theorem* is_atomic_dual_iff_is_coatomic
- \+/\- *theorem* is_atomistic_dual_iff_is_coatomistic
- \+ *lemma* is_coatomic_dual_iff_is_atomic
- \- *theorem* is_coatomic_dual_iff_is_atomic
- \+/\- *theorem* is_coatomistic_dual_iff_is_atomistic

Modified src/order/basic.lean


Modified src/order/boolean_algebra.lean


Modified src/order/bounded.lean


Modified src/order/bounded_order.lean


Modified src/order/bounds.lean
- \+/\- *lemma* exists_glb_Ioi
- \+/\- *lemma* is_glb_Ioi
- \+/\- *lemma* is_least_singleton
- \+/\- *lemma* is_lub_empty
- \+/\- *lemma* le_glb_Ioi
- \+/\- *lemma* lower_bounds_empty
- \+/\- *lemma* not_bdd_below_iff'
- \+/\- *lemma* order_iso.lower_bounds_image

Modified src/order/category/BoolAlg.lean


Modified src/order/category/BoundedDistribLattice.lean


Modified src/order/category/BoundedLattice.lean


Modified src/order/category/BoundedOrder.lean


Modified src/order/category/CompleteLattice.lean


Modified src/order/category/DistribLattice.lean


Modified src/order/category/FinBoolAlg.lean


Modified src/order/category/FinPartialOrder.lean


Modified src/order/category/Lattice.lean
- \+/\- *def* Lattice.dual

Modified src/order/category/LinearOrder.lean


Modified src/order/category/NonemptyFinLinOrd.lean


Modified src/order/category/PartialOrder.lean


Modified src/order/category/Preorder.lean


Modified src/order/category/Semilattice.lean


Modified src/order/circular.lean


Modified src/order/compare.lean


Modified src/order/complete_boolean_algebra.lean
- \+ *lemma* Inf_sup_eq
- \- *theorem* Inf_sup_eq
- \+ *lemma* infi_sup_eq
- \- *theorem* infi_sup_eq
- \+ *lemma* sup_Inf_eq
- \- *theorem* sup_Inf_eq
- \+ *lemma* sup_infi_eq
- \- *theorem* sup_infi_eq

Modified src/order/complete_lattice.lean
- \+/\- *lemma* Inf_eq_bot
- \+/\- *lemma* Inf_eq_infi'
- \+/\- *lemma* Inf_eq_infi
- \+/\- *lemma* Inf_image'
- \+/\- *lemma* Inf_sUnion
- \+ *lemma* Sup_eq_bot
- \- *theorem* Sup_eq_bot
- \+/\- *theorem* Sup_image
- \+/\- *lemma* inf_eq_infi
- \+/\- *lemma* infi_bool_eq
- \+/\- *lemma* infi_comm
- \+/\- *theorem* infi_of_empty
- \+/\- *lemma* infi_top
- \+/\- *theorem* le_Inf_inter
- \+/\- *lemma* supr_and
- \+/\- *lemma* supr_bot
- \+/\- *theorem* supr_const

Modified src/order/concept.lean
- \+/\- *def* concept.swap_equiv

Modified src/order/conditionally_complete_lattice.lean
- \+/\- *theorem* cinfi_const
- \+/\- *lemma* cinfi_set

Modified src/order/cover.lean
- \+/\- *lemma* of_dual_covby_of_dual_iff
- \+/\- *lemma* of_dual_wcovby_of_dual_iff

Modified src/order/directed.lean


Modified src/order/filter/at_top_bot.lean
- \+/\- *lemma* filter.at_bot_Iio_eq
- \+/\- *lemma* filter.at_bot_basis'
- \+/\- *lemma* filter.at_bot_basis

Modified src/order/filter/basic.lean


Modified src/order/filter/cofinite.lean


Modified src/order/filter/extr.lean
- \+/\- *lemma* is_min_on.infi_eq

Modified src/order/fixed_points.lean
- \+/\- *lemma* order_hom.gfp_gfp

Modified src/order/grade.lean
- \+/\- *lemma* grade_of_dual

Modified src/order/hom/basic.lean
- \+/\- *def* order_hom.dual_iso
- \+/\- *lemma* order_hom.symm_dual_comp
- \+/\- *def* order_iso.compl
- \+/\- *def* order_iso.dual_dual
- \+/\- *lemma* order_iso.dual_dual_symm_apply

Modified src/order/hom/bounded.lean
- \+/\- *lemma* bot_hom.symm_dual_comp
- \+/\- *lemma* bounded_order_hom.symm_dual_comp
- \+/\- *lemma* top_hom.symm_dual_comp

Modified src/order/hom/complete_lattice.lean
- \+/\- *lemma* Inf_hom.symm_dual_comp
- \+/\- *lemma* Sup_hom.symm_dual_comp
- \+/\- *lemma* complete_lattice_hom.symm_dual_comp

Modified src/order/hom/lattice.lean
- \+/\- *lemma* bounded_lattice_hom.symm_dual_comp
- \+/\- *lemma* inf_hom.symm_dual_comp
- \+/\- *lemma* inf_top_hom.symm_dual_comp
- \+/\- *lemma* lattice_hom.symm_dual_comp
- \+/\- *def* sup_bot_hom.dual
- \+/\- *lemma* sup_bot_hom.symm_dual_comp
- \+/\- *lemma* sup_hom.symm_dual_comp

Modified src/order/iterate.lean


Modified src/order/lattice.lean
- \+ *lemma* inf_assoc
- \- *theorem* inf_assoc
- \+ *lemma* inf_comm
- \- *theorem* inf_comm
- \+ *lemma* inf_idem
- \- *theorem* inf_idem
- \+/\- *lemma* inf_ind
- \+/\- *lemma* inf_le_iff
- \+/\- *lemma* inf_lt_iff
- \+/\- *theorem* le_inf_iff
- \+/\- *lemma* lt_inf_iff

Modified src/order/liminf_limsup.lean


Modified src/order/locally_finite.lean


Modified src/order/max.lean
- \+/\- *lemma* is_bot_of_dual_iff
- \+/\- *lemma* is_bot_or_exists_lt
- \+/\- *lemma* is_max_of_dual_iff
- \+/\- *lemma* is_min_of_dual_iff
- \+/\- *lemma* is_top_of_dual_iff

Modified src/order/min_max.lean
- \+/\- *lemma* max_cases
- \+/\- *lemma* max_eq_iff
- \+/\- *lemma* max_lt_max_left_iff
- \+/\- *lemma* max_lt_max_right_iff
- \+/\- *lemma* min_lt_min

Modified src/order/modular_lattice.lean


Modified src/order/monotone.lean
- \+/\- *lemma* antitone_nat_of_succ_le
- \+/\- *lemma* strict_anti_nat_of_succ_lt
- \+/\- *lemma* strict_mono_nat_of_lt_succ

Modified src/order/order_dual.lean
- \+/\- *lemma* order_dual.le_to_dual
- \+/\- *lemma* order_dual.lt_to_dual
- \+/\- *def* order_dual.of_dual
- \+/\- *lemma* order_dual.of_dual_inj
- \+/\- *lemma* order_dual.of_dual_le_of_dual
- \+/\- *lemma* order_dual.of_dual_lt_of_dual
- \+/\- *def* order_dual.to_dual
- \+/\- *lemma* order_dual.to_dual_inj
- \+/\- *lemma* order_dual.to_dual_le
- \+/\- *lemma* order_dual.to_dual_le_to_dual
- \+/\- *lemma* order_dual.to_dual_lt
- \+/\- *lemma* order_dual.to_dual_lt_to_dual
- \+/\- *lemma* order_dual.to_dual_of_dual

Modified src/order/pfilter.lean


Modified src/order/rel_classes.lean


Modified src/order/rel_iso.lean


Modified src/order/succ_pred/basic.lean
- \+/\- *lemma* order.le_pred_iff_eq_bot
- \+/\- *lemma* order.pred_lt_iff_ne_bot

Modified src/order/succ_pred/relation.lean


Modified src/order/upper_lower.lean
- \+/\- *lemma* is_lower_set_preimage_to_dual_iff
- \+/\- *lemma* is_upper_set_preimage_to_dual_iff
- \+/\- *def* upper_set.Ici_Sup_hom
- \+/\- *def* upper_set.Ici_sup_hom

Modified src/order/well_founded.lean


Modified src/order/well_founded_set.lean
- \+/\- *theorem* set.is_wf_iff_no_descending_seq

Modified src/order/zorn.lean


Modified src/ring_theory/artinian.lean
- \+/\- *theorem* is_artinian.monotone_stabilizes

Modified src/ring_theory/nullstellensatz.lean


Modified src/ring_theory/valuation/basic.lean
- \+/\- *def* add_valuation.valuation
- \+/\- *def* add_valuation

Modified src/ring_theory/valuation/valuation_subring.lean
- \+/\- *def* valuation_subring.prime_spectrum_order_equiv

Modified src/topology/algebra/order/basic.lean
- \+/\- *lemma* closure_Iio'
- \+/\- *lemma* disjoint_nhds_at_bot
- \+/\- *lemma* frontier_Ici_subset
- \+/\- *lemma* inf_nhds_at_bot

Modified src/topology/algebra/order/compact.lean
- \+/\- *lemma* is_compact.Sup_mem

Modified src/topology/algebra/order/extend_from.lean


Modified src/topology/algebra/order/intermediate_value.lean


Modified src/topology/algebra/order/left_right.lean


Modified src/topology/algebra/order/liminf_limsup.lean
- \+/\- *theorem* Liminf_nhds
- \+/\- *lemma* is_bounded_ge_nhds

Modified src/topology/algebra/order/monotone_continuity.lean


Modified src/topology/algebra/order/monotone_convergence.lean
- \+/\- *lemma* tendsto_at_bot_csupr
- \+/\- *lemma* tendsto_at_bot_is_lub
- \+/\- *lemma* tendsto_at_top_cinfi
- \+/\- *lemma* tendsto_at_top_is_glb

Modified src/topology/continuous_function/ordered.lean


Modified src/topology/local_extr.lean


Modified src/topology/order.lean


Modified src/topology/order/lattice.lean


Modified src/topology/semicontinuous.lean




## [2022-05-04 11:10:44](https://github.com/leanprover-community/mathlib/commit/402e564)
feat(linear_algebra/prod): linear version of prod_map ([#13751](https://github.com/leanprover-community/mathlib/pull/13751))
#### Estimated changes
Modified src/linear_algebra/prod.lean
- \+ *lemma* linear_map.prod_map_add
- \+ *def* linear_map.prod_map_alg_hom
- \+ *def* linear_map.prod_map_linear
- \- *def* linear_map.prod_map_monoid_hom
- \+ *def* linear_map.prod_map_ring_hom
- \+ *lemma* linear_map.prod_map_smul
- \+ *lemma* linear_map.prod_map_zero



## [2022-05-04 11:10:43](https://github.com/leanprover-community/mathlib/commit/e1f00bc)
feat(order/well_founded): Well founded relations are asymmetric and irreflexive ([#13692](https://github.com/leanprover-community/mathlib/pull/13692))
#### Estimated changes
Modified src/order/well_founded.lean
- \+ *theorem* well_founded.not_gt_of_lt



## [2022-05-04 11:10:42](https://github.com/leanprover-community/mathlib/commit/6c7b880)
feat(algebra/module/torsion): torsion ideal, decomposition lemma ([#13414](https://github.com/leanprover-community/mathlib/pull/13414))
Defines the torsion ideal of an element in a module, and also shows a decomposition lemma for torsion modules.
#### Estimated changes
Modified src/algebra/module/torsion.lean
- \+ *lemma* ideal.quotient.torsion_by_eq_span_singleton
- \+ *lemma* mem_torsion_of_iff
- \+ *def* module.is_torsion_by_set.has_scalar
- \+ *lemma* module.is_torsion_by_set.mk_smul
- \+ *def* module.is_torsion_by_set.module
- \+ *def* module.is_torsion_by_set
- \+ *lemma* quot_torsion_of_equiv_span_singleton_apply_mk
- \+ *lemma* submodule.is_torsion'_powers_iff
- \+ *lemma* submodule.is_torsion_by_set_iff_is_torsion_by_span
- \+ *lemma* submodule.is_torsion_by_set_iff_torsion_by_set_eq_top
- \+ *lemma* submodule.is_torsion_by_singleton_iff
- \+ *lemma* submodule.is_torsion_by_span_singleton_iff
- \+ *lemma* submodule.mem_torsion_by_set_iff
- \+ *lemma* submodule.supr_torsion_by_eq_torsion_by_prod
- \+/\- *lemma* submodule.torsion_by.mk_smul
- \+ *lemma* submodule.torsion_by_independent
- \+ *lemma* submodule.torsion_by_le_torsion_by_of_dvd
- \+ *lemma* submodule.torsion_by_one
- \+ *lemma* submodule.torsion_by_set.mk_smul
- \+ *def* submodule.torsion_by_set
- \+ *lemma* submodule.torsion_by_set_eq_torsion_by_span
- \+ *lemma* submodule.torsion_by_set_is_torsion_by_set
- \+ *lemma* submodule.torsion_by_set_le_torsion_by_set_of_subset
- \+ *lemma* submodule.torsion_by_set_torsion_by_set_eq_top
- \+ *lemma* submodule.torsion_by_singleton_eq
- \+ *lemma* submodule.torsion_by_span_singleton_eq
- \+ *lemma* submodule.torsion_by_univ
- \+ *lemma* submodule.torsion_is_internal
- \+ *def* torsion_of

Modified src/ring_theory/coprime/lemmas.lean
- \+/\- *lemma* exists_sum_eq_one_iff_pairwise_coprime'
- \+/\- *lemma* exists_sum_eq_one_iff_pairwise_coprime
- \+/\- *lemma* pairwise_coprime_iff_coprime_prod



## [2022-05-04 11:10:40](https://github.com/leanprover-community/mathlib/commit/e24f7f7)
move(set_theory/ordinal/{arithmetic → fixed_points}): Move `nfp` ([#13315](https://github.com/leanprover-community/mathlib/pull/13315))
That way, it belong with the other functions about fixed points.
#### Estimated changes
Modified src/set_theory/ordinal/arithmetic.lean
- \- *theorem* ordinal.add_eq_right_iff_mul_omega_le
- \- *theorem* ordinal.add_le_right_iff_mul_omega_le
- \- *def* ordinal.deriv
- \- *theorem* ordinal.deriv_add_eq_mul_omega_add
- \- *theorem* ordinal.deriv_eq_enum_fp
- \- *theorem* ordinal.deriv_eq_id_of_nfp_eq_id
- \- *theorem* ordinal.deriv_is_normal
- \- *theorem* ordinal.deriv_limit
- \- *theorem* ordinal.deriv_mul_eq_opow_omega_mul
- \- *theorem* ordinal.deriv_mul_zero
- \- *theorem* ordinal.deriv_succ
- \- *theorem* ordinal.deriv_zero
- \- *theorem* ordinal.eq_zero_or_opow_omega_le_of_mul_eq_right
- \- *theorem* ordinal.is_normal.apply_eq_self_iff_deriv
- \- *theorem* ordinal.is_normal.deriv_fp
- \- *theorem* ordinal.is_normal.le_iff_deriv
- \- *theorem* ordinal.is_normal.le_nfp
- \- *theorem* ordinal.is_normal.nfp_fp
- \- *theorem* ordinal.is_normal.nfp_le_fp
- \- *theorem* ordinal.is_normal.nfp_unbounded
- \- *theorem* ordinal.iterate_le_nfp
- \- *theorem* ordinal.le_nfp_self
- \- *theorem* ordinal.lt_nfp
- \- *theorem* ordinal.mul_eq_right_iff_opow_omega_dvd
- \- *theorem* ordinal.mul_le_right_iff_opow_omega_dvd
- \- *def* ordinal.nfp
- \- *theorem* ordinal.nfp_add_eq_mul_omega
- \- *theorem* ordinal.nfp_add_zero
- \- *theorem* ordinal.nfp_eq_self
- \- *theorem* ordinal.nfp_le
- \- *theorem* ordinal.nfp_le_iff
- \- *theorem* ordinal.nfp_mul_eq_opow_omega
- \- *theorem* ordinal.nfp_mul_one
- \- *theorem* ordinal.nfp_mul_opow_omega_add
- \- *theorem* ordinal.nfp_mul_zero
- \- *theorem* ordinal.nfp_zero_mul

Modified src/set_theory/ordinal/fixed_point.lean
- \+ *theorem* ordinal.add_eq_right_iff_mul_omega_le
- \+ *theorem* ordinal.add_le_right_iff_mul_omega_le
- \+ *theorem* ordinal.apply_le_nfp_bfamily
- \+ *def* ordinal.deriv
- \+ *theorem* ordinal.deriv_add_eq_mul_omega_add
- \+ *theorem* ordinal.deriv_eq_deriv_family
- \+ *theorem* ordinal.deriv_eq_enum_ord
- \+ *theorem* ordinal.deriv_eq_id_of_nfp_eq_id
- \+ *theorem* ordinal.deriv_id_of_nfp_id
- \+ *theorem* ordinal.deriv_is_normal
- \+ *theorem* ordinal.deriv_limit
- \+ *theorem* ordinal.deriv_mul_eq_opow_omega_mul
- \+ *theorem* ordinal.deriv_mul_zero
- \+ *theorem* ordinal.deriv_succ
- \+ *theorem* ordinal.deriv_zero
- \+ *theorem* ordinal.eq_zero_or_opow_omega_le_of_mul_eq_right
- \+ *theorem* ordinal.fp_unbounded
- \+ *theorem* ordinal.is_normal.apply_le_nfp
- \+ *theorem* ordinal.is_normal.apply_lt_nfp
- \+ *theorem* ordinal.is_normal.deriv_fp
- \+ *theorem* ordinal.is_normal.fp_iff_deriv
- \+ *theorem* ordinal.is_normal.le_iff_deriv
- \+ *theorem* ordinal.is_normal.nfp_fp
- \+ *theorem* ordinal.is_normal.nfp_le_apply
- \+ *theorem* ordinal.iterate_le_nfp
- \+ *theorem* ordinal.le_nfp
- \+/\- *theorem* ordinal.le_nfp_bfamily
- \+ *theorem* ordinal.le_nfp_family
- \+ *theorem* ordinal.lt_nfp
- \+ *theorem* ordinal.mul_eq_right_iff_opow_omega_dvd
- \+ *theorem* ordinal.mul_le_right_iff_opow_omega_dvd
- \+ *def* ordinal.nfp
- \+ *theorem* ordinal.nfp_add_eq_mul_omega
- \+ *theorem* ordinal.nfp_add_zero
- \+ *theorem* ordinal.nfp_eq_nfp_family
- \+ *theorem* ordinal.nfp_eq_self
- \+ *theorem* ordinal.nfp_id
- \+ *theorem* ordinal.nfp_le
- \+ *theorem* ordinal.nfp_le_fp
- \+ *theorem* ordinal.nfp_le_iff
- \+ *theorem* ordinal.nfp_monotone
- \+ *theorem* ordinal.nfp_mul_eq_opow_omega
- \+ *theorem* ordinal.nfp_mul_one
- \+ *theorem* ordinal.nfp_mul_opow_omega_add
- \+ *theorem* ordinal.nfp_mul_zero
- \+ *theorem* ordinal.nfp_zero_mul
- \- *theorem* ordinal.self_le_nfp_bfamily
- \- *theorem* ordinal.self_le_nfp_family
- \+ *theorem* ordinal.sup_iterate_eq_nfp

Modified src/set_theory/ordinal/principal.lean




## [2022-05-04 07:51:01](https://github.com/leanprover-community/mathlib/commit/1a86249)
feat(measure_theory/function/l1_space): add `integrable_smul_measure` ([#13922](https://github.com/leanprover-community/mathlib/pull/13922))
* add `integrable_smul_measure`, an `iff` version of
  `integrable.smul_measure`;
* add `integrable_average`, an `iff` version of `integrable.to_average`.
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable_average
- \+ *lemma* measure_theory.integrable_smul_measure



## [2022-05-04 07:51:00](https://github.com/leanprover-community/mathlib/commit/af4c6c8)
chore(ring_theory/polynomial/basic): golf polynomial_not_is_field ([#13919](https://github.com/leanprover-community/mathlib/pull/13919))
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean




## [2022-05-04 07:50:59](https://github.com/leanprover-community/mathlib/commit/d0efe25)
feat(data/finset/prod): diag of union ([#13916](https://github.com/leanprover-community/mathlib/pull/13916))
Lemmas about diag and off diag in relation to simple finset constructions.
#### Estimated changes
Modified src/data/finset/prod.lean
- \+ *lemma* finset.diag_insert
- \+ *lemma* finset.diag_singleton
- \+ *lemma* finset.diag_union
- \+ *lemma* finset.off_diag_insert
- \+ *lemma* finset.off_diag_singleton
- \+ *lemma* finset.off_diag_union
- \+ *lemma* finset.product_sdiff_diag
- \+ *lemma* finset.product_sdiff_off_diag



## [2022-05-04 07:50:58](https://github.com/leanprover-community/mathlib/commit/098ab17)
feat(category_theory/simple): nonzero morphisms to/from a simple are epi/mono ([#13905](https://github.com/leanprover-community/mathlib/pull/13905))
#### Estimated changes
Modified src/category_theory/preadditive/schur.lean
- \+ *lemma* category_theory.mono_of_nonzero_from_simple

Modified src/category_theory/simple.lean
- \+ *lemma* category_theory.epi_of_nonzero_to_simple



## [2022-05-04 07:50:57](https://github.com/leanprover-community/mathlib/commit/455393d)
refactor(group_theory/{submonoid, subsemigroup}/{center, centralizer}): move set.center and set.centralizer into subsemigroup ([#13903](https://github.com/leanprover-community/mathlib/pull/13903))
This moves `set.center` and `set.centralizer` (the center and centralizers for a magma) into `group_theory/subsemigroup/{center, centralizer}` so that we can define the center and centralizers for semigroups in [#13627](https://github.com/leanprover-community/mathlib/pull/13627).
#### Estimated changes
Modified src/group_theory/submonoid/center.lean
- \- *lemma* set.add_mem_center
- \- *def* set.center
- \- *lemma* set.center_eq_univ
- \- *lemma* set.center_units_eq
- \- *lemma* set.center_units_subset
- \- *lemma* set.div_mem_center
- \- *lemma* set.div_mem_center₀
- \- *lemma* set.inv_mem_center
- \- *lemma* set.inv_mem_center₀
- \- *lemma* set.mem_center_iff
- \- *lemma* set.mul_mem_center
- \- *lemma* set.neg_mem_center
- \- *lemma* set.one_mem_center
- \- *lemma* set.subset_center_units
- \- *lemma* set.zero_mem_center

Modified src/group_theory/submonoid/centralizer.lean
- \- *lemma* set.add_mem_centralizer
- \- *def* set.centralizer
- \- *lemma* set.centralizer_eq_univ
- \- *lemma* set.centralizer_subset
- \- *lemma* set.centralizer_univ
- \- *lemma* set.div_mem_centralizer
- \- *lemma* set.div_mem_centralizer₀
- \- *lemma* set.inv_mem_centralizer
- \- *lemma* set.inv_mem_centralizer₀
- \- *lemma* set.mem_centralizer_iff
- \- *lemma* set.mul_mem_centralizer
- \- *lemma* set.neg_mem_centralizer
- \- *lemma* set.one_mem_centralizer
- \- *lemma* set.zero_mem_centralizer

Added src/group_theory/subsemigroup/center.lean
- \+ *lemma* set.add_mem_center
- \+ *def* set.center
- \+ *lemma* set.center_eq_univ
- \+ *lemma* set.center_units_eq
- \+ *lemma* set.center_units_subset
- \+ *lemma* set.div_mem_center
- \+ *lemma* set.div_mem_center₀
- \+ *lemma* set.inv_mem_center
- \+ *lemma* set.inv_mem_center₀
- \+ *lemma* set.mem_center_iff
- \+ *lemma* set.mul_mem_center
- \+ *lemma* set.neg_mem_center
- \+ *lemma* set.one_mem_center
- \+ *lemma* set.subset_center_units
- \+ *lemma* set.zero_mem_center

Added src/group_theory/subsemigroup/centralizer.lean
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



## [2022-05-04 07:50:55](https://github.com/leanprover-community/mathlib/commit/e6b8499)
feat(ring_theory/valuation/valuation_subring): Adds some equivalent conditions for equivalence of valuations ([#13895](https://github.com/leanprover-community/mathlib/pull/13895))
#### Estimated changes
Modified src/ring_theory/valuation/basic.lean
- \+ *lemma* valuation.is_equiv_iff_val_eq_one
- \+ *lemma* valuation.is_equiv_iff_val_le_one
- \+ *lemma* valuation.map_add_eq_of_lt_left
- \+ *lemma* valuation.map_add_eq_of_lt_right

Modified src/ring_theory/valuation/valuation_subring.lean
- \+ *lemma* valuation.is_equiv_iff_valuation_subring
- \+ *lemma* valuation.is_equiv_valuation_valuation_subring
- \+ *lemma* valuation.mem_valuation_subring_iff
- \+ *def* valuation.valuation_subring
- \+ *lemma* valuation_subring.valuation_subring_valuation



## [2022-05-04 07:50:54](https://github.com/leanprover-community/mathlib/commit/6d37006)
feat(data/list/basic): add `list.cons_diff` ([#13892](https://github.com/leanprover-community/mathlib/pull/13892))
#### Estimated changes
Modified src/data/list/basic.lean
- \+ *lemma* list.cons_diff
- \+ *lemma* list.cons_diff_of_mem
- \+ *lemma* list.cons_diff_of_not_mem



## [2022-05-04 07:50:53](https://github.com/leanprover-community/mathlib/commit/269bc85)
feat(analysis/matrix): add `frobenius_norm_conj_transpose` ([#13883](https://github.com/leanprover-community/mathlib/pull/13883))
This also moves the existing lemmas about the elementwise norm to the same file.
#### Estimated changes
Modified src/analysis/matrix.lean
- \+ *lemma* matrix.frobenius_nnnorm_conj_transpose
- \+ *lemma* matrix.frobenius_norm_conj_transpose
- \+ *lemma* matrix.nnnorm_conj_transpose
- \+ *lemma* matrix.norm_conj_transpose

Modified src/analysis/normed_space/star/matrix.lean
- \- *lemma* matrix.nnnorm_conj_transpose
- \- *lemma* matrix.norm_conj_transpose



## [2022-05-04 07:50:52](https://github.com/leanprover-community/mathlib/commit/d537897)
feat(category_theory/simple): simple objects are indecomposable ([#13882](https://github.com/leanprover-community/mathlib/pull/13882))
Remarkably tedious.
#### Estimated changes
Modified src/category_theory/limits/shapes/biproducts.lean
- \+ *def* category_theory.indecomposable
- \+ *lemma* category_theory.limits.biprod.is_iso_inl_iff_id_eq_fst_comp_inl

Modified src/category_theory/limits/shapes/zero_morphisms.lean
- \+ *lemma* category_theory.limits.is_zero.eq_zero_of_src
- \+ *lemma* category_theory.limits.is_zero.eq_zero_of_tgt
- \+ *lemma* category_theory.limits.is_zero.iff_id_eq_zero
- \+ *lemma* category_theory.limits.is_zero.iff_split_epi_eq_zero
- \+ *lemma* category_theory.limits.is_zero.iff_split_mono_eq_zero
- \+ *lemma* category_theory.limits.is_zero.of_epi
- \+ *lemma* category_theory.limits.is_zero.of_epi_eq_zero
- \+ *lemma* category_theory.limits.is_zero.of_epi_zero
- \+ *lemma* category_theory.limits.is_zero.of_mono
- \+ *lemma* category_theory.limits.is_zero.of_mono_eq_zero
- \+ *lemma* category_theory.limits.is_zero.of_mono_zero

Modified src/category_theory/simple.lean
- \+ *lemma* category_theory.biprod.is_iso_inl_iff_is_zero
- \+ *lemma* category_theory.indecomposable_of_simple
- \+ *lemma* category_theory.simple.not_is_zero
- \+ *lemma* category_theory.simple.of_iso



## [2022-05-04 07:50:51](https://github.com/leanprover-community/mathlib/commit/1afdaf9)
feat(linear_algebra/trace): more general versions of `trace_mul_comm` and `trace_conj` ([#13874](https://github.com/leanprover-community/mathlib/pull/13874))
#### Estimated changes
Modified src/linear_algebra/bilinear_map.lean
- \+ *theorem* linear_map.lcomp_apply'
- \+ *theorem* linear_map.llcomp_apply'

Modified src/linear_algebra/contraction.lean
- \+ *lemma* comp_dual_tensor_hom

Modified src/linear_algebra/trace.lean
- \+ *theorem* linear_map.trace_comp_comm'
- \+ *theorem* linear_map.trace_comp_comm
- \+/\- *theorem* linear_map.trace_conj'
- \+ *theorem* linear_map.trace_eq_contract_apply



## [2022-05-04 07:50:50](https://github.com/leanprover-community/mathlib/commit/517aa8b)
feat(topology/algebra/star): continuity of `star` ([#13855](https://github.com/leanprover-community/mathlib/pull/13855))
This adds the obvious instances for `pi`, `prod`, `units`, `mul_opposite`, `real`, `complex`, `is_R_or_C`, and `matrix`.
We already had a `continuous_star` lemma, but it had stronger typeclass assumptions.
This resolves multiple TODO comments.
#### Estimated changes
Modified src/analysis/complex/basic.lean
- \+/\- *lemma* complex.continuous_conj

Modified src/analysis/normed_space/star/basic.lean
- \- *lemma* continuous.star
- \- *lemma* continuous_at.star
- \- *lemma* continuous_at_star
- \- *lemma* continuous_on.star
- \- *lemma* continuous_on_star
- \- *lemma* continuous_star
- \- *lemma* continuous_within_at.star
- \- *lemma* continuous_within_at_star
- \- *lemma* filter.tendsto.star
- \- *lemma* tendsto_star

Modified src/data/complex/is_R_or_C.lean
- \+/\- *lemma* is_R_or_C.continuous_conj

Added src/topology/algebra/star.lean
- \+ *lemma* continuous.star
- \+ *lemma* continuous_at.star
- \+ *lemma* continuous_at_star
- \+ *lemma* continuous_on.star
- \+ *lemma* continuous_on_star
- \+ *lemma* continuous_within_at.star
- \+ *lemma* continuous_within_at_star
- \+ *lemma* filter.tendsto.star
- \+ *lemma* tendsto_star

Modified src/topology/continuous_function/zero_at_infty.lean


Modified src/topology/instances/matrix.lean
- \+ *lemma* continuous.matrix_conj_transpose
- \+ *lemma* has_sum.matrix_conj_transpose
- \+ *lemma* matrix.conj_transpose_tsum
- \+ *lemma* summable.matrix_conj_transpose
- \+ *lemma* summable_matrix_conj_transpose

Modified src/topology/instances/real.lean




## [2022-05-04 07:50:49](https://github.com/leanprover-community/mathlib/commit/35c8980)
feat(analysis/asymptotics/specific_asymptotics): Cesaro averaging preserves convergence ([#13825](https://github.com/leanprover-community/mathlib/pull/13825))
#### Estimated changes
Modified src/analysis/asymptotics/specific_asymptotics.lean
- \+ *lemma* asymptotics.is_o.sum_range
- \+ *lemma* asymptotics.is_o_sum_range_of_tendsto_zero
- \+ *lemma* filter.tendsto.cesaro
- \+ *lemma* filter.tendsto.cesaro_smul



## [2022-05-04 07:50:48](https://github.com/leanprover-community/mathlib/commit/6e00330)
feat(algebra/squarefree): relate squarefree on naturals to factorization ([#13816](https://github.com/leanprover-community/mathlib/pull/13816))
Also moves `nat.two_le_iff` higher up the hierarchy since it's an elementary lemma and give it a more appropriate type.
The lemma `squarefree_iff_prime_sq_not_dvd` has been deleted because it's a duplicate of a lemma which is already earlier in the same file.
#### Estimated changes
Modified src/algebra/squarefree.lean
- \+ *lemma* nat.squarefree.ext_iff
- \+ *lemma* nat.squarefree.factorization_le_one
- \+ *lemma* nat.squarefree_and_prime_pow_iff_prime
- \+ *lemma* nat.squarefree_iff_factorization_le_one
- \- *lemma* nat.squarefree_iff_prime_sq_not_dvd
- \+ *lemma* nat.squarefree_of_factorization_le_one
- \+ *lemma* nat.squarefree_pow_iff

Modified src/data/nat/basic.lean
- \+ *lemma* nat.two_le_iff

Modified src/data/nat/factorization.lean
- \+ *lemma* nat.dvd_of_factorization_pos
- \+ *lemma* nat.prime.dvd_iff_one_le_factorization

Modified src/data/nat/prime.lean
- \- *lemma* nat.two_le_iff



## [2022-05-04 07:50:47](https://github.com/leanprover-community/mathlib/commit/ba4bf54)
feat(set_theory/game/pgame): Add more congr lemmas ([#13808](https://github.com/leanprover-community/mathlib/pull/13808))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.add_congr_left
- \+ *theorem* pgame.add_congr_right
- \+/\- *theorem* pgame.equiv_refl
- \+ *theorem* pgame.equiv_rfl
- \+ *theorem* pgame.sub_congr_left
- \+ *theorem* pgame.sub_congr_right



## [2022-05-04 07:50:46](https://github.com/leanprover-community/mathlib/commit/85657f1)
feat(algebra/category/FinVect): has finite limits ([#13793](https://github.com/leanprover-community/mathlib/pull/13793))
#### Estimated changes
Modified src/algebra/category/FinVect.lean
- \+ *def* FinVect.of

Added src/algebra/category/FinVect/limits.lean
- \+ *def* FinVect.forget₂_creates_limit

Added src/algebra/category/Module/products.lean
- \+ *lemma* Module.pi_iso_pi_hom_ker_subtype
- \+ *lemma* Module.pi_iso_pi_inv_kernel_ι
- \+ *def* Module.product_cone
- \+ *def* Module.product_cone_is_limit

Modified src/category_theory/concrete_category/basic.lean


Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean
- \+ *def* category_theory.limits.colimit_cocone_of_coequalizer_and_coproduct
- \+ *def* category_theory.limits.colimit_quotient_coproduct
- \+ *def* category_theory.limits.limit_cone_of_equalizer_and_product
- \+ *def* category_theory.limits.limit_subobject_product

Modified src/linear_algebra/finite_dimensional.lean




## [2022-05-04 07:50:45](https://github.com/leanprover-community/mathlib/commit/e3d38ed)
feat(algebra/hom/non_unital_alg): some constructions for `prod` ([#13785](https://github.com/leanprover-community/mathlib/pull/13785))
#### Estimated changes
Modified src/algebra/hom/non_unital_alg.lean
- \+ *theorem* non_unital_alg_hom.coe_inl
- \+ *theorem* non_unital_alg_hom.coe_inr
- \+ *lemma* non_unital_alg_hom.coe_prod
- \+ *def* non_unital_alg_hom.fst
- \+ *theorem* non_unital_alg_hom.fst_prod
- \+ *def* non_unital_alg_hom.inl
- \+ *theorem* non_unital_alg_hom.inl_apply
- \+ *def* non_unital_alg_hom.inr
- \+ *theorem* non_unital_alg_hom.inr_apply
- \+ *def* non_unital_alg_hom.prod
- \+ *def* non_unital_alg_hom.prod_equiv
- \+ *theorem* non_unital_alg_hom.prod_fst_snd
- \+ *def* non_unital_alg_hom.snd
- \+ *theorem* non_unital_alg_hom.snd_prod



## [2022-05-04 07:50:44](https://github.com/leanprover-community/mathlib/commit/9015d2a)
refactor(set_theory/game/pgame): Redefine `subsequent` ([#13752](https://github.com/leanprover-community/mathlib/pull/13752))
We redefine `subsequent` as `trans_gen is_option`. This gives a much nicer induction principle than the previous one, and allows us to immediately prove well-foundedness.
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \- *lemma* pgame.subsequent.left_move
- \+ *lemma* pgame.subsequent.mk_left
- \+ *lemma* pgame.subsequent.mk_right
- \+ *lemma* pgame.subsequent.move_left
- \+ *lemma* pgame.subsequent.move_right
- \- *lemma* pgame.subsequent.right_move
- \+ *theorem* pgame.subsequent.trans
- \+ *def* pgame.subsequent
- \- *inductive* pgame.subsequent
- \+/\- *theorem* pgame.wf_subsequent



## [2022-05-04 07:50:43](https://github.com/leanprover-community/mathlib/commit/b337b92)
feat(model_theory/satisfiability): A union of a directed family of satisfiable theories is satisfiable ([#13750](https://github.com/leanprover-community/mathlib/pull/13750))
Proves `first_order.language.Theory.is_satisfiable_directed_union_iff` - the union of a directed family of theories is satisfiable if and only if all of the theories in the family are satisfiable.
#### Estimated changes
Modified src/model_theory/satisfiability.lean
- \+ *theorem* first_order.language.Theory.is_satisfiable_directed_union_iff



## [2022-05-04 07:50:40](https://github.com/leanprover-community/mathlib/commit/51d8167)
feat(model_theory/elementary_maps): The elementary diagram of a structure ([#13724](https://github.com/leanprover-community/mathlib/pull/13724))
Defines the elementary diagram of a structure - the theory consisting of all sentences with parameters it satisfies.
Defines the canonical elementary embedding of a structure into any model of its elementary diagram.
#### Estimated changes
Modified src/model_theory/elementary_maps.lean
- \+ *abbreviation* first_order.language.elementary_diagram
- \+ *def* first_order.language.elementary_embedding.of_models_elementary_diagram

Modified src/model_theory/language_map.lean




## [2022-05-04 07:50:39](https://github.com/leanprover-community/mathlib/commit/319d502)
refactor(linear_algebra/*): more generalisations ([#13668](https://github.com/leanprover-community/mathlib/pull/13668))
Many further generalisations from `field` to `division_ring` in the linear algebra library.
This PR changes some proofs; it's not just relaxing hypotheses.
#### Estimated changes
Modified src/data/finsupp/basic.lean
- \+ *def* equiv.finsupp_unique
- \+/\- *lemma* finsupp.unique_ext_iff

Modified src/linear_algebra/affine_space/basis.lean


Modified src/linear_algebra/affine_space/finite_dimensional.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+/\- *lemma* finite_dimensional.finrank_map_subtype_eq



## [2022-05-04 07:50:38](https://github.com/leanprover-community/mathlib/commit/36c5faa)
feat(set_theory/game/pgame): Tweak `pgame.mul` API ([#13651](https://github.com/leanprover-community/mathlib/pull/13651))
We modify the API for `pgame.mul` in two ways:
- `left_moves_mul` and `right_moves_mul` are turned from type equivalences into type equalities.
- The former equivalences are prefixed with `to_` and inverted.
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \+ *theorem* pgame.left_moves_mul
- \- *def* pgame.left_moves_mul
- \+ *theorem* pgame.right_moves_mul
- \- *def* pgame.right_moves_mul
- \+ *def* pgame.to_left_moves_mul
- \+ *def* pgame.to_right_moves_mul



## [2022-05-04 07:50:37](https://github.com/leanprover-community/mathlib/commit/bd23639)
feat(topology/bornology): add more instances ([#13621](https://github.com/leanprover-community/mathlib/pull/13621))
#### Estimated changes
Added src/topology/bornology/constructions.lean
- \+ *lemma* bornology.cobounded_pi
- \+ *lemma* bornology.cobounded_prod
- \+ *lemma* bornology.forall_is_bounded_image_eval_iff
- \+ *def* bornology.induced
- \+ *lemma* bornology.is_bounded.fst_of_prod
- \+ *lemma* bornology.is_bounded.pi
- \+ *lemma* bornology.is_bounded.prod
- \+ *lemma* bornology.is_bounded.snd_of_prod
- \+ *lemma* bornology.is_bounded_image_fst_and_snd
- \+ *lemma* bornology.is_bounded_image_subtype_coe
- \+ *lemma* bornology.is_bounded_induced
- \+ *lemma* bornology.is_bounded_pi
- \+ *lemma* bornology.is_bounded_pi_of_nonempty
- \+ *lemma* bornology.is_bounded_prod
- \+ *lemma* bornology.is_bounded_prod_of_nonempty
- \+ *lemma* bornology.is_bounded_prod_self
- \+ *lemma* bounded_space_coe_set_iff
- \+ *lemma* bounded_space_induced_iff
- \+ *lemma* bounded_space_subtype_iff



## [2022-05-04 07:50:35](https://github.com/leanprover-community/mathlib/commit/2402b4d)
feat(set_theory/game/pgame): Tweak `pgame.neg` API ([#13617](https://github.com/leanprover-community/mathlib/pull/13617))
We modify the API for `pgame.neg` in various ways: 
- `left_moves_neg` and `right_moves_neg` are turned from type equivalences into type equalities.
- The former equivalences are prefixed with `to_` and inverted.
We also golf a few theorems.
#### Estimated changes
Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.left_moves_neg
- \- *def* pgame.left_moves_neg
- \- *lemma* pgame.move_left_left_moves_neg_symm
- \+ *lemma* pgame.move_left_neg'
- \+ *lemma* pgame.move_left_neg
- \+ *lemma* pgame.move_left_neg_symm'
- \+ *lemma* pgame.move_left_neg_symm
- \- *lemma* pgame.move_left_right_moves_neg
- \- *lemma* pgame.move_right_left_moves_neg
- \+ *lemma* pgame.move_right_neg'
- \+ *lemma* pgame.move_right_neg
- \+ *lemma* pgame.move_right_neg_symm'
- \+ *lemma* pgame.move_right_neg_symm
- \- *lemma* pgame.move_right_right_moves_neg_symm
- \+ *theorem* pgame.right_moves_neg
- \- *def* pgame.right_moves_neg
- \+ *def* pgame.to_left_moves_neg
- \+ *def* pgame.to_right_moves_neg



## [2022-05-04 06:42:38](https://github.com/leanprover-community/mathlib/commit/58de2a0)
chore(analysis): use nnnorm notation everywhere ([#13930](https://github.com/leanprover-community/mathlib/pull/13930))
This was done with a series of ad-hoc regular expressions, then cleaned up by hand.
#### Estimated changes
Modified src/analysis/analytic/composition.lean


Modified src/analysis/analytic/radius_liminf.lean
- \+/\- *lemma* formal_multilinear_series.radius_eq_liminf

Modified src/analysis/calculus/inverse.lean


Modified src/analysis/normed/group/hom.lean
- \+/\- *def* add_monoid_hom.mk_normed_group_hom'

Modified src/analysis/normed_space/banach.lean


Modified src/analysis/normed_space/enorm.lean
- \+/\- *lemma* enorm.map_smul

Modified src/analysis/normed_space/finite_dimension.lean


Modified src/analysis/normed_space/indicator_function.lean


Modified src/analysis/normed_space/linear_isometry.lean
- \+/\- *lemma* linear_isometry.nnnorm_map
- \+/\- *lemma* linear_isometry_equiv.nnnorm_map

Modified src/analysis/normed_space/multilinear.lean
- \+/\- *theorem* continuous_multilinear_map.le_of_op_nnnorm_le
- \+/\- *theorem* continuous_multilinear_map.le_op_nnnorm

Modified src/analysis/normed_space/operator_norm.lean


Modified src/measure_theory/constructions/borel_space.lean
- \+/\- *lemma* measurable.nnnorm
- \+/\- *lemma* measurable_ennnorm

Modified src/measure_theory/constructions/prod.lean


Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/function/l1_space.lean
- \+/\- *lemma* measure_theory.lintegral_nnnorm_zero

Modified src/measure_theory/function/l2_space.lean


Modified src/measure_theory/function/lp_space.lean


Modified src/measure_theory/function/simple_func_dense_lp.lean


Modified src/measure_theory/function/strongly_measurable.lean


Modified src/measure_theory/integral/set_to_l1.lean




## [2022-05-04 06:42:36](https://github.com/leanprover-community/mathlib/commit/6f3426c)
chore(number_theory/legendre_symbol/quadratic_char): golf some proofs ([#13926](https://github.com/leanprover-community/mathlib/pull/13926))
#### Estimated changes
Modified src/number_theory/legendre_symbol/quadratic_char.lean




## [2022-05-04 06:42:35](https://github.com/leanprover-community/mathlib/commit/171825a)
chore(algebra/order/floor): missing simp lemmas on floor of nat and int ([#13904](https://github.com/leanprover-community/mathlib/pull/13904))
#### Estimated changes
Modified src/algebra/order/floor.lean
- \+ *lemma* int.ceil_int
- \+ *lemma* int.floor_int
- \+ *lemma* int.fract_int
- \+ *lemma* nat.ceil_int
- \+ *lemma* nat.ceil_nat
- \+ *lemma* nat.floor_int
- \+ *lemma* nat.floor_nat



## [2022-05-04 05:51:33](https://github.com/leanprover-community/mathlib/commit/4d0b630)
feat(category_theory/bicategory/coherence_tactic): coherence tactic for bicategories ([#13417](https://github.com/leanprover-community/mathlib/pull/13417))
This PR extends the coherence tactic for monoidal categories [#13125](https://github.com/leanprover-community/mathlib/pull/13125) to bicategories. The setup is the same as for monoidal case except for the following : we normalize 2-morphisms before running the coherence tactic. This normalization is achieved by the set of simp lemmas in `whisker_simps` defined in `coherence_tactic.lean`.
As a test of the tactic in the real world, I have proved several properties of adjunction in bicategories in [#13418](https://github.com/leanprover-community/mathlib/pull/13418). Unfortunately some proofs cause timeout, so it seems that we need to speed up the coherence tactic in the future.
#### Estimated changes
Added src/category_theory/bicategory/coherence_tactic.lean
- \+ *def* category_theory.bicategory.bicategorical_comp
- \+ *lemma* category_theory.bicategory.bicategorical_comp_refl
- \+ *def* category_theory.bicategory.bicategorical_iso
- \+ *def* category_theory.bicategory.bicategorical_iso_comp
- \+ *lemma* tactic.bicategory.coherence.assoc_lift_hom₂

Modified src/category_theory/monoidal/coherence.lean


Modified src/category_theory/monoidal/internal/types.lean


Modified test/coherence.lean




## [2022-05-04 05:16:36](https://github.com/leanprover-community/mathlib/commit/c1f329d)
feat(data/zmod/quotient): The quotient `<a>/stab(b)` is cyclic of order `minimal_period ((+ᵥ) a) b` ([#13722](https://github.com/leanprover-community/mathlib/pull/13722))
This PR adds an isomorphism stating that the quotient `<a>/stab(b)` is cyclic of order `minimal_period ((+ᵥ) a) b`.
There is also a multiplicative version, but it is easily proved from the additive version, so I'll PR the multiplicative version afterwards.
#### Estimated changes
Modified src/data/zmod/quotient.lean
- \+ *lemma* add_action.zmultiples_quotient_stabilizer_equiv_symm_apply



## [2022-05-04 04:20:31](https://github.com/leanprover-community/mathlib/commit/a2a873f)
chore(scripts): update nolints.txt ([#13932](https://github.com/leanprover-community/mathlib/pull/13932))
I am happy to remove some nolints for you!
#### Estimated changes
Modified scripts/nolints.txt




## [2022-05-04 01:08:00](https://github.com/leanprover-community/mathlib/commit/dd58438)
feat(set_theory/game/short): Birthday of short games ([#13875](https://github.com/leanprover-community/mathlib/pull/13875))
We prove that a short game has a finite birthday. We also clean up the file somewhat.
#### Estimated changes
Modified src/set_theory/game/short.lean
- \+ *def* pgame.short.of_is_empty
- \+ *theorem* pgame.short_birthday
- \- *def* pgame.short_of_equiv_empty



## [2022-05-04 00:13:27](https://github.com/leanprover-community/mathlib/commit/fc3de19)
feat(ring_theory/ideal/local_ring): generalize lemmas to semirings ([#13471](https://github.com/leanprover-community/mathlib/pull/13471))
What is essentially new is the proof of `local_ring.of_surjective` and `local_ring.is_unit_or_is_unit_of_is_unit_add`.
- I changed the definition of local ring to `local_ring.of_is_unit_or_is_unit_of_add_one`, which is reminiscent of the definition before the recent change in [#13341](https://github.com/leanprover-community/mathlib/pull/13341). The equivalence of the previous definition is essentially given by `local_ring.is_unit_or_is_unit_of_is_unit_add`. The choice of the definition is insignificant here because they are all equivalent, but I think the choice here is better for the default constructor because this condition is "weaker" than e.g. `local_ring.of_non_units_add` in some sense.
- The proof of `local_ring.of_surjective` needs `[is_local_ring_hom f]`, which was not necessary for commutative rings in the previous proof. So the new version here is not a genuine generalization of the previous version. The previous version was  renamed to `local_ring.of_surjective'`.
#### Estimated changes
Modified src/logic/equiv/transfer_instance.lean


Modified src/number_theory/padics/padic_integers.lean


Modified src/ring_theory/ideal/local_ring.lean
- \+ *lemma* local_ring.is_unit_or_is_unit_of_is_unit_add
- \+ *lemma* local_ring.nonunits_add
- \+ *lemma* local_ring.of_is_unit_or_is_unit_of_is_unit_add
- \+ *lemma* local_ring.of_nonunits_add
- \+ *lemma* local_ring.of_surjective'
- \+/\- *lemma* local_ring.of_surjective

Modified src/ring_theory/localization/at_prime.lean




## [2022-05-03 23:37:38](https://github.com/leanprover-community/mathlib/commit/6c0580a)
fix(.docker/*): update elan URL ([#13928](https://github.com/leanprover-community/mathlib/pull/13928))
These are hopefully the last occurrences of the URL that was breaking things earlier today. cf. [#13906](https://github.com/leanprover-community/mathlib/pull/13906)
#### Estimated changes
Modified .docker/debian/lean/Dockerfile


Modified .docker/gitpod/mathlib/Dockerfile




## [2022-05-03 22:34:05](https://github.com/leanprover-community/mathlib/commit/fd65159)
feat(topology/metric_space/basic): golf, avoid unfold ([#13923](https://github.com/leanprover-community/mathlib/pull/13923))
* Don't use `unfold` in `nnreal.pseudo_metric_space`.
* Golf some proofs.
#### Estimated changes
Modified src/topology/metric_space/basic.lean




## [2022-05-03 21:57:27](https://github.com/leanprover-community/mathlib/commit/de07131)
feat(measure_theory/integral/torus_integral): torus integral and its properties ([#12892](https://github.com/leanprover-community/mathlib/pull/12892))
Define a generalized torus map and prove some basic properties.
Define the torus integral and the integrability of functions on a generalized torus, and prove lemmas about them.
#### Estimated changes
Modified src/measure_theory/integral/circle_integral.lean
- \+ *lemma* circle_integral_def_Icc
- \+ *lemma* circle_map_zero

Added src/measure_theory/integral/torus_integral.lean
- \+ *lemma* norm_torus_integral_le_of_norm_le_const
- \+ *lemma* torus_integrable.function_integrable
- \+ *lemma* torus_integrable.torus_integrable_const
- \+ *lemma* torus_integrable.torus_integrable_zero_radius
- \+ *def* torus_integrable
- \+ *def* torus_integral
- \+ *lemma* torus_integral_add
- \+ *lemma* torus_integral_const_mul
- \+ *lemma* torus_integral_dim0
- \+ *lemma* torus_integral_dim1
- \+ *lemma* torus_integral_neg
- \+ *lemma* torus_integral_radius_zero
- \+ *lemma* torus_integral_smul
- \+ *lemma* torus_integral_sub
- \+ *lemma* torus_integral_succ
- \+ *lemma* torus_integral_succ_above
- \+ *def* torus_map
- \+ *lemma* torus_map_eq_center_iff
- \+ *lemma* torus_map_sub_center
- \+ *lemma* torus_map_zero_radius



## [2022-05-03 20:33:18](https://github.com/leanprover-community/mathlib/commit/9c0dfcd)
doc(order/countable_dense_linear_order): Fix minor mistake ([#13921](https://github.com/leanprover-community/mathlib/pull/13921))
I wrongfully removed some instances of the word "linear" in [#12928](https://github.com/leanprover-community/mathlib/pull/12928). This is in fact used as a hypothesis.
#### Estimated changes
Modified src/order/countable_dense_linear_order.lean




## [2022-05-03 19:18:51](https://github.com/leanprover-community/mathlib/commit/5cfb8db)
refactor(ring_theory/jacobson_ideal): generalize lemmas to non-commutative rings ([#13865](https://github.com/leanprover-community/mathlib/pull/13865))
The main change here is that the order of multiplication has been adjusted slightly in `mem_jacobson_iff`and `exists_mul_sub_mem_of_sub_one_mem_jacobson`. In the commutative case this doesn't matter anyway.
All the other changes are just moving lemmas between sections, the statements of no lemmas other than those two have been changed. No lemmas have been added or removed.
The lemmas about `is_unit` and quotients don't generalize as easily, so I've not attempted to touch those; that would require some mathematical insight, which is out of scope for this PR!
#### Estimated changes
Modified src/ring_theory/jacobson_ideal.lean
- \+/\- *theorem* ideal.is_primary_of_is_maximal_radical
- \+/\- *theorem* ideal.mem_jacobson_iff

Modified src/ring_theory/nakayama.lean




## [2022-05-03 18:19:54](https://github.com/leanprover-community/mathlib/commit/16157f2)
chore(topology/continuous_function/bounded): generalize from `normed_*` to `semi_normed_*` ([#13915](https://github.com/leanprover-community/mathlib/pull/13915))
Every single lemma in this file generalized, apart from the ones that transferred a `normed_*` instance which obviously need the stronger assumption.
`dist_zero_of_empty` was the only lemma that actually needed reproving from scratch, all the other affected proofs are just split between two instances.
#### Estimated changes
Modified src/topology/continuous_function/bounded.lean
- \+/\- *theorem* bounded_continuous_function.arzela_ascoli
- \+/\- *lemma* bounded_continuous_function.equicontinuous_of_continuity_modulus
- \+/\- *def* bounded_continuous_function.of_normed_group
- \+/\- *structure* bounded_continuous_function



## [2022-05-03 18:19:53](https://github.com/leanprover-community/mathlib/commit/bd1d935)
feat(number_theory/legendre_symbol/): add some lemmas ([#13831](https://github.com/leanprover-community/mathlib/pull/13831))
This adds essentially two lemmas on quadratic characters:
* `quadratic_char_neg_one_iff_not_is_square`, which says that the quadratic character takes the value `-1` exactly on non-squares, and
* `quadratic_char_number_of_sqrts`. which says that the number of square roots of `a : F` is `quadratic_char F a + 1`.
It also adds the corresponding statements, `legendre_sym_eq_neg_one_iff` and `legendre_sym_number_of_sqrts`, for the Legendre symbol.
#### Estimated changes
Modified src/number_theory/legendre_symbol/quadratic_char.lean
- \+ *lemma* char.quadratic_char_card_sqrts
- \+ *lemma* char.quadratic_char_eq_neg_one_iff_not_one
- \+ *lemma* char.quadratic_char_neg_one_iff_not_is_square
- \+ *lemma* finite_field.neg_ne_self_of_char_ne_two

Modified src/number_theory/legendre_symbol/quadratic_reciprocity.lean
- \+ *lemma* zmod.legendre_sym_card_sqrts
- \+ *lemma* zmod.legendre_sym_eq_neg_one_iff
- \+ *lemma* zmod.legendre_sym_eq_neg_one_iff_not_one



## [2022-05-03 16:29:01](https://github.com/leanprover-community/mathlib/commit/7d28753)
chore(normed_space/weak_dual): generalize `normed_group` to `semi_normed_group` ([#13914](https://github.com/leanprover-community/mathlib/pull/13914))
This almost halves the time this file takes to build, and is more general too.
#### Estimated changes
Modified src/analysis/normed_space/weak_dual.lean




## [2022-05-03 16:29:00](https://github.com/leanprover-community/mathlib/commit/8688753)
feat(set_theory/game/basic): Inline instances ([#13813](https://github.com/leanprover-community/mathlib/pull/13813))
We also add a few missing instances.
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \- *def* game.add
- \- *theorem* game.add_assoc
- \- *theorem* game.add_comm
- \- *theorem* game.add_left_neg
- \- *theorem* game.add_zero
- \- *def* game.game_partial_order
- \- *def* game.le
- \- *def* game.lt
- \- *def* game.neg
- \+/\- *theorem* game.not_le
- \+ *theorem* game.not_lt
- \+ *def* game.ordered_add_comm_group
- \- *def* game.ordered_add_comm_group_game
- \+ *def* game.partial_order
- \- *theorem* game.zero_add
- \- *def* pgame.mul



## [2022-05-03 16:28:59](https://github.com/leanprover-community/mathlib/commit/5c433d0)
feat(algebra/big_operators/basic): `prod_list_count` and `prod_list_count_of_subset` ([#13370](https://github.com/leanprover-community/mathlib/pull/13370))
Add 
`prod_list_count (l : list α) : l.prod = ∏ x in l.to_finset, (x ^ (l.count x))`
and
`prod_list_count_of_subset (l : list α) (s : finset α) (hs : l.to_finset ⊆ s) : l.prod = ∏ x in s, x ^ (l.count x)`
as counterparts of `prod_multiset_count` and `prod_multiset_count_of_subset` (whose proofs are then golfed using the new lemmas).
#### Estimated changes
Modified src/algebra/big_operators/basic.lean
- \+ *lemma* finset.prod_list_count
- \+ *lemma* finset.prod_list_count_of_subset
- \+ *lemma* finset.prod_list_map_count



## [2022-05-03 14:29:31](https://github.com/leanprover-community/mathlib/commit/40b5952)
doc(analysis/matrix): fix broken LaTeX ([#13910](https://github.com/leanprover-community/mathlib/pull/13910))
#### Estimated changes
Modified src/analysis/matrix.lean




## [2022-05-03 14:29:30](https://github.com/leanprover-community/mathlib/commit/1c4d2b7)
feat(linear_algebra/matrix/trace): add `trace_conj_transpose` ([#13888](https://github.com/leanprover-community/mathlib/pull/13888))
#### Estimated changes
Modified src/linear_algebra/matrix/trace.lean
- \+ *lemma* matrix.trace_conj_transpose



## [2022-05-03 14:29:29](https://github.com/leanprover-community/mathlib/commit/0f8d7a9)
feat(order/omega_complete_partial_order): make `continuous_hom.prod.apply` continuous ([#13833](https://github.com/leanprover-community/mathlib/pull/13833))
Previous it was defined as `apply : (α →𝒄 β) × α →o β` and the comment
said that it would make sense to define it as a continuous function, but
we need an instance for `α →𝒄 β` first. But then let’s just define that
instance first, and then define `apply : (α →𝒄 β) × α →𝒄 β` as you would
expect.
Also rephrases `lemma ωSup_ωSup` differently now that `apply` is
continuous.
#### Estimated changes
Modified src/order/omega_complete_partial_order.lean
- \+/\- *def* omega_complete_partial_order.continuous_hom.prod.apply
- \+ *lemma* omega_complete_partial_order.continuous_hom.ωSup_apply_ωSup
- \- *lemma* omega_complete_partial_order.continuous_hom.ωSup_ωSup
- \+ *lemma* prod.ωSup_zip



## [2022-05-03 14:29:28](https://github.com/leanprover-community/mathlib/commit/475a533)
feat(topology/algebra/module/basic): A continuous linear functional is open ([#13829](https://github.com/leanprover-community/mathlib/pull/13829))
#### Estimated changes
Modified src/topology/algebra/module/basic.lean
- \+ *lemma* continuous_linear_map.exists_ne_zero



## [2022-05-03 14:29:27](https://github.com/leanprover-community/mathlib/commit/4cea0a8)
move(data/pi/*): Group `pi` files ([#13826](https://github.com/leanprover-community/mathlib/pull/13826))
Move `data.pi` to `data.pi.algebra` and `order.pilex` to `data.pi.lex`.
#### Estimated changes
Modified src/algebra/group/pi.lean


Modified src/algebra/hom/equiv.lean


Modified src/algebra/ring/basic.lean


Modified src/data/fin/tuple/basic.lean


Renamed src/data/pi.lean to src/data/pi/algebra.lean


Renamed src/order/pilex.lean to src/data/pi/lex.lean




## [2022-05-03 14:29:25](https://github.com/leanprover-community/mathlib/commit/8a5b4a7)
feat(analysis/special_functions/complex/arg): lemmas about `arg z` and `±(π / 2)` ([#13821](https://github.com/leanprover-community/mathlib/pull/13821))
#### Estimated changes
Modified src/analysis/special_functions/complex/arg.lean
- \+ *lemma* complex.abs_arg_le_pi_div_two_iff
- \+ *lemma* complex.arg_le_pi_div_two_iff
- \+ *lemma* complex.neg_pi_div_two_le_arg_iff



## [2022-05-03 14:29:24](https://github.com/leanprover-community/mathlib/commit/2f38ccb)
chore(data/matrix/basic): add lemmas about powers of matrices ([#13815](https://github.com/leanprover-community/mathlib/pull/13815))
Shows that:
* natural powers commute with `transpose`, `conj_transpose`, `diagonal`, `block_diagonal`, and `block_diagonal'`.
* integer powers commute with `transpose`, and `conj_transpose`.
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+/\- *lemma* matrix.conj_transpose_list_prod
- \+ *lemma* matrix.conj_transpose_pow
- \+/\- *def* matrix.conj_transpose_ring_equiv
- \+ *lemma* matrix.diagonal_pow
- \+ *lemma* matrix.map_injective
- \+ *lemma* matrix.transpose_pow

Modified src/data/matrix/block.lean
- \+ *lemma* matrix.block_diagonal'_pow
- \+ *lemma* matrix.block_diagonal_pow

Modified src/linear_algebra/matrix/zpow.lean
- \+ *theorem* matrix.conj_transpose_zpow
- \+ *theorem* matrix.transpose_zpow



## [2022-05-03 14:29:24](https://github.com/leanprover-community/mathlib/commit/36b5341)
feat(ring_theory/polynomial/basic): reduce assumptions, golf ([#13800](https://github.com/leanprover-community/mathlib/pull/13800))
There is some reorder, so the diff is a bit large. Sorry for that.
#### Estimated changes
Modified src/ring_theory/polynomial/basic.lean
- \+/\- *theorem* ideal.is_fg_degree_le
- \+/\- *def* polynomial.degree_lt_equiv
- \+/\- *theorem* polynomial.map_restriction
- \+/\- *lemma* polynomial.monic.geom_sum'
- \+/\- *lemma* polynomial.monic.geom_sum
- \+/\- *lemma* polynomial.monic_geom_sum_X



## [2022-05-03 14:29:22](https://github.com/leanprover-community/mathlib/commit/6d2788c)
feat(analysis/calculus/cont_diff): cont_diff_succ_iff_fderiv_apply ([#13797](https://github.com/leanprover-community/mathlib/pull/13797))
* Prove that a map is `C^(n+1)` iff it is differentiable and all its directional derivatives in all points are `C^n`. 
* Also some supporting lemmas about `continuous_linear_equiv`.
* We only manage to prove this when the domain is finite dimensional.
* Prove one direction of `cont_diff_on_succ_iff_fderiv_within` with fewer assumptions
* From the sphere eversion project
Co-authored by: Patrick Massot [patrick.massot@u-psud.fr](mailto:patrick.massot@u-psud.fr)
Co-authored by: Oliver Nash [github@olivernash.org](mailto:github@olivernash.org)
#### Estimated changes
Modified src/algebra/module/equiv.lean
- \+/\- *lemma* linear_equiv.symm_trans_apply
- \+ *lemma* linear_equiv.trans_symm

Modified src/analysis/calculus/cont_diff.lean
- \+ *lemma* cont_diff_clm_apply
- \+ *lemma* cont_diff_on_clm_apply
- \+ *lemma* cont_diff_on_succ_iff_fderiv_apply
- \+ *lemma* cont_diff_on_succ_of_fderiv_apply
- \+ *lemma* cont_diff_on_succ_of_fderiv_within
- \+ *lemma* cont_diff_succ_iff_fderiv_apply

Modified src/analysis/normed_space/finite_dimension.lean
- \+ *lemma* continuous_clm_apply
- \+ *def* continuous_linear_equiv.pi_ring
- \+ *lemma* continuous_on_clm_apply

Modified src/analysis/normed_space/operator_norm.lean
- \+ *def* continuous_linear_equiv.arrow_congr
- \+ *def* continuous_linear_equiv.arrow_congrSL

Modified src/topology/algebra/module/basic.lean




## [2022-05-03 14:29:21](https://github.com/leanprover-community/mathlib/commit/234b3df)
feat(analysis/normed_space): lemmas about continuous bilinear maps ([#13522](https://github.com/leanprover-community/mathlib/pull/13522))
* Define `continuous_linear_map.map_sub₂` and friends, similar to the lemmas for `linear_map`. 
* Rename `continuous_linear_map.map_add₂` to `continuous_linear_map.map_add_add`
* Two comments refer to `continuous.comp₂`, which will be added in [#13423](https://github.com/leanprover-community/mathlib/pull/13423) (but there is otherwise no dependency on this PR).
* Define `precompR` and `precompL`, which will be used to compute the derivative of a convolution.
* From the sphere eversion project
* Required for convolutions
#### Estimated changes
Modified src/analysis/analytic/linear.lean


Modified src/analysis/normed_space/bounded_linear_maps.lean
- \+ *lemma* continuous_linear_map.continuous₂
- \+ *lemma* continuous_linear_map.map_add₂
- \+ *lemma* continuous_linear_map.map_neg₂
- \+ *lemma* continuous_linear_map.map_smul₂
- \+ *lemma* continuous_linear_map.map_smulₛₗ₂
- \+ *lemma* continuous_linear_map.map_sub₂
- \+ *lemma* continuous_linear_map.map_zero₂

Modified src/analysis/normed_space/operator_norm.lean
- \+ *theorem* continuous_linear_map.dist_le_op_norm
- \+ *lemma* continuous_linear_map.map_add_add
- \- *lemma* continuous_linear_map.map_add₂
- \+ *theorem* continuous_linear_map.nndist_le_op_nnnorm
- \+ *def* continuous_linear_map.precompL
- \+ *def* continuous_linear_map.precompR

Modified src/measure_theory/function/strongly_measurable.lean
- \+ *lemma* measure_theory.ae_strongly_measurable.ae_strongly_measurable_comp₂



## [2022-05-03 12:18:57](https://github.com/leanprover-community/mathlib/commit/3b971a7)
feat(data/zmod/basic): Add `zmod.cast_sub_one` ([#13889](https://github.com/leanprover-community/mathlib/pull/13889))
This PR adds `zmod.cast_sub_one`, an analog of `fin.coe_sub_one`. Unfortunately, the proof is a bit long. But maybe it can be golfed?
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.cast_sub_one



## [2022-05-03 12:18:56](https://github.com/leanprover-community/mathlib/commit/78c86e1)
chore(data/nat/totient): golf three lemmas ([#13886](https://github.com/leanprover-community/mathlib/pull/13886))
Golf the proofs of `totient_le`, `totient_lt`, and `totient_pos`
#### Estimated changes
Modified src/data/nat/totient.lean




## [2022-05-03 12:18:55](https://github.com/leanprover-community/mathlib/commit/9f818ce)
feat(set_theory/ordinal_basic): `o.out.α` is equivalent to the ordinals below `o` ([#13876](https://github.com/leanprover-community/mathlib/pull/13876))
#### Estimated changes
Modified src/set_theory/ordinal/basic.lean




## [2022-05-03 12:18:54](https://github.com/leanprover-community/mathlib/commit/82b9c42)
feat(set_theory/game/nim): Mark many lemmas as `simp` ([#13844](https://github.com/leanprover-community/mathlib/pull/13844))
#### Estimated changes
Modified src/set_theory/game/nim.lean
- \- *lemma* pgame.equiv_iff_grundy_value_eq
- \+/\- *theorem* pgame.equiv_nim_grundy_value
- \- *lemma* pgame.equiv_nim_iff_grundy_value_eq
- \- *lemma* pgame.equiv_zero_iff_grundy_value
- \+/\- *lemma* pgame.grundy_value_def
- \+ *lemma* pgame.grundy_value_eq_iff_equiv
- \+ *lemma* pgame.grundy_value_eq_iff_equiv_nim
- \+ *lemma* pgame.grundy_value_iff_equiv_zero
- \+/\- *lemma* pgame.grundy_value_nim_add_nim
- \+/\- *lemma* pgame.grundy_value_zero
- \+/\- *lemma* pgame.nim.equiv_iff_eq
- \+/\- *lemma* pgame.nim.sum_first_loses_iff_eq
- \+/\- *lemma* pgame.nim.sum_first_wins_iff_neq
- \+/\- *lemma* pgame.nim.zero_first_loses



## [2022-05-03 12:18:53](https://github.com/leanprover-community/mathlib/commit/e104992)
chore(order/*): Replace total partial orders by linear orders ([#13839](https://github.com/leanprover-community/mathlib/pull/13839))
`partial_order α` + `is_total α (≤)` has no more theorems than `linear_order α`  but is nonetheless used in some places. This replaces those uses by `linear_order α` or `complete_linear_order α`. Also make implicit one argument of `finset.lt_inf'_iff` and friends.
#### Estimated changes
Modified src/analysis/locally_convex/weak_dual.lean


Modified src/data/finset/lattice.lean
- \+/\- *lemma* finset.comp_inf_eq_inf_comp_of_is_total
- \+/\- *lemma* finset.comp_sup_eq_sup_comp_of_is_total
- \+/\- *lemma* finset.exists_mem_eq_inf'
- \+/\- *lemma* finset.exists_mem_eq_inf
- \+/\- *lemma* finset.exists_mem_eq_sup'
- \+/\- *lemma* finset.exists_mem_eq_sup
- \+/\- *lemma* finset.inf'_le_iff
- \+/\- *lemma* finset.inf'_lt_iff
- \- *lemma* finset.inf_le_iff
- \- *lemma* finset.inf_lt_iff
- \- *lemma* finset.le_inf'_iff
- \+/\- *lemma* finset.le_sup'_iff
- \- *lemma* finset.le_sup_iff
- \+/\- *lemma* finset.lt_inf'_iff
- \- *lemma* finset.lt_inf_iff
- \+/\- *lemma* finset.lt_sup'_iff
- \- *lemma* finset.lt_sup_iff
- \+/\- *lemma* finset.sup'_lt_iff
- \- *lemma* finset.sup_lt_iff

Modified src/data/real/nnreal.lean


Modified src/data/set/intervals/basic.lean
- \+/\- *lemma* set.Icc_bot_top
- \+/\- *lemma* set.Ici_top
- \+/\- *lemma* set.Iic_bot
- \+/\- *lemma* set.Iio_inter_Iio
- \+/\- *lemma* set.Ioc_inter_Ioi
- \+/\- *lemma* set.Ioi_inter_Ioi

Modified src/order/complete_lattice.lean


Modified src/order/lattice.lean
- \+/\- *lemma* antitone.map_inf
- \+/\- *lemma* antitone.map_sup
- \+ *lemma* inf_eq_min
- \- *theorem* inf_eq_min
- \+/\- *lemma* inf_ind
- \+/\- *lemma* inf_le_iff
- \+ *lemma* inf_lt_iff
- \+/\- *lemma* le_sup_iff
- \+/\- *lemma* lt_inf_iff
- \+/\- *lemma* lt_sup_iff
- \+/\- *lemma* monotone.map_inf
- \+/\- *lemma* monotone.map_sup
- \+ *lemma* sup_eq_max
- \- *theorem* sup_eq_max
- \+/\- *lemma* sup_ind
- \+/\- *lemma* sup_lt_iff

Modified src/order/min_max.lean
- \+/\- *lemma* le_max_iff
- \+/\- *lemma* lt_max_iff
- \+/\- *lemma* lt_min_iff
- \+/\- *lemma* max_lt_iff
- \+ *lemma* max_lt_max_left_iff
- \+ *lemma* max_lt_max_right_iff
- \+/\- *lemma* min_le_iff
- \+/\- *lemma* min_lt_iff
- \+ *lemma* min_lt_min_left_iff
- \+ *lemma* min_lt_min_right_iff

Modified src/order/omega_complete_partial_order.lean
- \+/\- *lemma* complete_lattice.inf_continuous'
- \+/\- *lemma* complete_lattice.inf_continuous

Modified src/topology/algebra/order/basic.lean
- \+/\- *lemma* nhds_bot_basis
- \+/\- *lemma* nhds_bot_basis_Iic
- \+/\- *lemma* nhds_top_basis
- \+/\- *lemma* nhds_top_basis_Ici



## [2022-05-03 12:18:52](https://github.com/leanprover-community/mathlib/commit/f6cb9be)
fix(data/complex/basic): make complex addition computable again ([#13837](https://github.com/leanprover-community/mathlib/pull/13837))
This was fixed once before in [#8166](https://github.com/leanprover-community/mathlib/pull/8166) (5f2358c43b769b334f3986a96565e606fe5bccec), but a new noncomputable shortcut appears if your file has more imports.
#### Estimated changes
Modified src/data/complex/basic.lean




## [2022-05-03 12:18:51](https://github.com/leanprover-community/mathlib/commit/b07c0f7)
feat(set_theory/game/basic): Add `le_rfl` on games ([#13814](https://github.com/leanprover-community/mathlib/pull/13814))
#### Estimated changes
Modified src/set_theory/game/basic.lean
- \+/\- *theorem* game.le_refl
- \+ *theorem* game.le_rfl



## [2022-05-03 12:18:50](https://github.com/leanprover-community/mathlib/commit/72816f9)
feat(data/real/nnreal): add `nnreal.forall` and `nnreal.exists` ([#13774](https://github.com/leanprover-community/mathlib/pull/13774))
#### Estimated changes
Modified src/data/real/nnreal.lean




## [2022-05-03 12:18:49](https://github.com/leanprover-community/mathlib/commit/7931ba4)
feat(order/conditionally_complete_lattice): Simp theorems ([#13756](https://github.com/leanprover-community/mathlib/pull/13756))
We remove `supr_unit` and `infi_unit` since, thanks to [#13741](https://github.com/leanprover-community/mathlib/pull/13741), they can be proven by `simp`.
#### Estimated changes
Modified src/order/conditionally_complete_lattice.lean
- \+/\- *theorem* infi_unique
- \- *theorem* infi_unit
- \+/\- *theorem* supr_unique
- \- *theorem* supr_unit



## [2022-05-03 11:43:28](https://github.com/leanprover-community/mathlib/commit/65cad41)
chore(.github/workflows): use separate secret token for dependent issues ([#13902](https://github.com/leanprover-community/mathlib/pull/13902))
#### Estimated changes
Modified .github/workflows/dependent-issues.yml




## [2022-05-03 11:03:24](https://github.com/leanprover-community/mathlib/commit/1c39267)
ci(elan): update dead repository URLs ([#13906](https://github.com/leanprover-community/mathlib/pull/13906))
`Kha/elan` is redirected by github to `leanprover/elan`, but seemingly with a cache that is delayed.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/install.20elan.20fails.20in.20CI/near/280981154)
#### Estimated changes
Modified .github/workflows/bors.yml


Modified .github/workflows/build.yml


Modified .github/workflows/build.yml.in


Modified .github/workflows/build_fork.yml




## [2022-05-02 21:37:01](https://github.com/leanprover-community/mathlib/commit/ca1551c)
feat(data/finset/n_ary): Binary image of finsets ([#13718](https://github.com/leanprover-community/mathlib/pull/13718))
Define `finset.image₂`, the binary map of finsets. Golf `data.finset.pointwise` using it.
#### Estimated changes
Added src/data/finset/n_ary.lean
- \+ *lemma* finset.card_image₂
- \+ *lemma* finset.card_image₂_le
- \+ *lemma* finset.coe_image₂
- \+ *lemma* finset.forall_image₂_iff
- \+ *lemma* finset.image_image₂
- \+ *lemma* finset.image_image₂_antidistrib
- \+ *lemma* finset.image_image₂_antidistrib_left
- \+ *lemma* finset.image_image₂_antidistrib_right
- \+ *lemma* finset.image_image₂_distrib
- \+ *lemma* finset.image_image₂_distrib_left
- \+ *lemma* finset.image_image₂_distrib_right
- \+ *lemma* finset.image_image₂_right_anticomm
- \+ *lemma* finset.image_image₂_right_comm
- \+ *lemma* finset.image_subset_image₂_left
- \+ *lemma* finset.image_subset_image₂_right
- \+ *def* finset.image₂
- \+ *lemma* finset.image₂_assoc
- \+ *lemma* finset.image₂_comm
- \+ *lemma* finset.image₂_congr'
- \+ *lemma* finset.image₂_congr
- \+ *lemma* finset.image₂_empty_left
- \+ *lemma* finset.image₂_empty_right
- \+ *lemma* finset.image₂_eq_empty_iff
- \+ *lemma* finset.image₂_image_left
- \+ *lemma* finset.image₂_image_left_anticomm
- \+ *lemma* finset.image₂_image_left_comm
- \+ *lemma* finset.image₂_image_right
- \+ *lemma* finset.image₂_inter_subset_left
- \+ *lemma* finset.image₂_inter_subset_right
- \+ *lemma* finset.image₂_left
- \+ *lemma* finset.image₂_left_comm
- \+ *lemma* finset.image₂_nonempty_iff
- \+ *lemma* finset.image₂_right
- \+ *lemma* finset.image₂_right_comm
- \+ *lemma* finset.image₂_singleton
- \+ *lemma* finset.image₂_singleton_left
- \+ *lemma* finset.image₂_singleton_right
- \+ *lemma* finset.image₂_subset
- \+ *lemma* finset.image₂_subset_iff
- \+ *lemma* finset.image₂_subset_left
- \+ *lemma* finset.image₂_subset_right
- \+ *lemma* finset.image₂_swap
- \+ *lemma* finset.image₂_union_left
- \+ *lemma* finset.image₂_union_right
- \+ *lemma* finset.mem_image₂
- \+ *lemma* finset.mem_image₂_iff
- \+ *lemma* finset.mem_image₂_of_mem
- \+ *lemma* finset.nonempty.image₂
- \+ *lemma* finset.nonempty.of_image₂_left
- \+ *lemma* finset.nonempty.of_image₂_right
- \+ *lemma* finset.subset_image₂

Modified src/data/finset/pointwise.lean
- \+/\- *lemma* finset.coe_div
- \+/\- *lemma* finset.coe_mul
- \+/\- *lemma* finset.coe_vsub
- \+/\- *lemma* finset.div_card_le
- \+/\- *lemma* finset.div_empty
- \+/\- *lemma* finset.div_mem_div
- \+/\- *lemma* finset.div_singleton
- \+/\- *lemma* finset.div_subset_div
- \+/\- *lemma* finset.empty_div
- \+/\- *lemma* finset.empty_mul
- \+/\- *lemma* finset.empty_smul
- \+/\- *lemma* finset.empty_vsub
- \+/\- *lemma* finset.image_vsub_product
- \+/\- *lemma* finset.mem_div
- \+/\- *lemma* finset.mem_mul
- \+/\- *lemma* finset.mem_smul
- \+/\- *lemma* finset.mem_vsub
- \+/\- *lemma* finset.mul_card_le
- \+/\- *lemma* finset.mul_empty
- \+/\- *lemma* finset.mul_mem_mul
- \+/\- *lemma* finset.mul_singleton
- \+/\- *lemma* finset.mul_subset_mul
- \+ *lemma* finset.nonempty.div
- \+ *lemma* finset.nonempty.mul
- \+/\- *lemma* finset.nonempty.smul
- \+/\- *lemma* finset.nonempty.vsub
- \+/\- *lemma* finset.singleton_div
- \+/\- *lemma* finset.singleton_div_singleton
- \+/\- *lemma* finset.singleton_mul
- \+/\- *lemma* finset.singleton_mul_singleton
- \+/\- *lemma* finset.singleton_smul
- \+/\- *lemma* finset.singleton_vsub_singleton
- \+/\- *lemma* finset.smul_card_le
- \+/\- *lemma* finset.smul_empty
- \+/\- *lemma* finset.smul_finset_mem_smul_finset
- \+/\- *lemma* finset.smul_mem_smul
- \+/\- *lemma* finset.smul_nonempty_iff
- \+/\- *lemma* finset.smul_singleton
- \+/\- *lemma* finset.smul_subset_smul
- \+/\- *lemma* finset.subset_div
- \+/\- *lemma* finset.subset_mul
- \+/\- *lemma* finset.subset_smul
- \+/\- *lemma* finset.subset_vsub
- \+/\- *lemma* finset.vsub_card_le
- \+/\- *lemma* finset.vsub_def
- \+/\- *lemma* finset.vsub_empty
- \+/\- *lemma* finset.vsub_mem_vsub
- \+/\- *lemma* finset.vsub_nonempty_iff
- \+/\- *lemma* finset.vsub_subset_vsub

Modified src/order/filter/n_ary.lean




## [2022-05-02 20:22:14](https://github.com/leanprover-community/mathlib/commit/1741207)
feat(analysis/normed_space/exponential): `Aeᴮ = eᴮA` if `AB = BA` ([#13881](https://github.com/leanprover-community/mathlib/pull/13881))
This commit shows that the exponenential commutes if the exponent does.
This generalizes a previous weaker result.
#### Estimated changes
Modified src/analysis/normed_space/exponential.lean
- \+/\- *lemma* commute.exp
- \+ *lemma* commute.exp_left
- \+ *lemma* commute.exp_right

Modified src/topology/algebra/infinite_sum.lean
- \+ *lemma* commute.tsum_left
- \+ *lemma* commute.tsum_right



## [2022-05-02 19:32:06](https://github.com/leanprover-community/mathlib/commit/c44091f)
feat(data/zmod/basic): Generalize `zmod.card` ([#13887](https://github.com/leanprover-community/mathlib/pull/13887))
This PR generalizes `zmod.card` from assuming `[fact (0 < n)]` to assuming `[fintype (zmod n)]`.
Note that the latter was already part of the statement, but was previously deduced from the instance `instance fintype : Π (n : ℕ) [fact (0 < n)], fintype (zmod n)` on line 80.
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+/\- *lemma* zmod.card



## [2022-05-02 19:32:04](https://github.com/leanprover-community/mathlib/commit/2b0aeda)
feat(measure/function/l*_space): a sample of useful lemmas on L^p spaces ([#13823](https://github.com/leanprover-community/mathlib/pull/13823))
Used in [#13690](https://github.com/leanprover-community/mathlib/pull/13690)
#### Estimated changes
Modified src/measure_theory/function/l1_space.lean
- \+ *lemma* measure_theory.integrable.abs
- \+ *lemma* measure_theory.integrable.const_mul'
- \- *lemma* measure_theory.integrable.max_zero
- \- *lemma* measure_theory.integrable.min_zero
- \+ *lemma* measure_theory.integrable.mul_const'
- \+ *lemma* measure_theory.integrable.neg_part
- \+ *lemma* measure_theory.integrable.pos_part
- \+ *lemma* measure_theory.integrable_finset_sum'
- \+ *lemma* measure_theory.mem_ℒp.integrable_norm_rpow'
- \+ *lemma* measure_theory.mem_ℒp.integrable_norm_rpow

Modified src/measure_theory/function/l2_space.lean
- \+ *lemma* measure_theory.mem_ℒp.integrable_sq
- \+ *lemma* measure_theory.mem_ℒp_two_iff_integrable_sq
- \+ *lemma* measure_theory.mem_ℒp_two_iff_integrable_sq_norm

Modified src/measure_theory/function/lp_space.lean
- \+ *lemma* measure_theory.mem_ℒp.neg_part
- \+ *lemma* measure_theory.mem_ℒp.norm_rpow_div
- \+ *lemma* measure_theory.mem_ℒp.pos_part
- \+/\- *def* measure_theory.mem_ℒp
- \+ *lemma* measure_theory.mem_ℒp_finset_sum'
- \+ *lemma* measure_theory.mem_ℒp_norm_rpow_iff
- \+ *lemma* measure_theory.mem_ℒp_top_const

Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.mem_ℒp.snorm_eq_integral_rpow_norm

Modified src/measure_theory/measure/ae_measurable.lean
- \+ *lemma* ae_measurable.map_map_of_ae_measurable

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.is_probability_measure_map

Modified src/probability/integration.lean




## [2022-05-02 17:28:50](https://github.com/leanprover-community/mathlib/commit/aa921ef)
docs(set_theory/game/pgame): Fix note on `pgame` ([#13880](https://github.com/leanprover-community/mathlib/pull/13880))
We never actually quotient by extensionality. What we quotient by is game equivalence.
#### Estimated changes
Modified src/set_theory/game/pgame.lean




## [2022-05-02 17:28:49](https://github.com/leanprover-community/mathlib/commit/0606d7c)
feat(set_theory/game/pgame): Negative of `of_lists` ([#13868](https://github.com/leanprover-community/mathlib/pull/13868))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *lemma* pgame.neg_of_lists



## [2022-05-02 17:28:48](https://github.com/leanprover-community/mathlib/commit/3e2f214)
feat(logic/basic): Generalize `congr_fun_heq` ([#13867](https://github.com/leanprover-community/mathlib/pull/13867))
The lemma holds for arbitrary heterogeneous equalities, not only that given by casts.
#### Estimated changes
Modified src/logic/basic.lean
- \- *lemma* congr_fun_heq
- \+ *lemma* congr_heq

Modified src/set_theory/game/ordinal.lean




## [2022-05-02 17:28:47](https://github.com/leanprover-community/mathlib/commit/785f62c)
feat(algebra/star/prod): elementwise `star` operator ([#13856](https://github.com/leanprover-community/mathlib/pull/13856))
The lemmas and instances this provides are inspired by `algebra/star/pi`, and appear in the same order.
We should have these instances anyway for completness, but the motivation is to make it easy to talk about the continuity of `star` on `units R` via the `units.embed_product_star` lemma.
#### Estimated changes
Added src/algebra/star/prod.lean
- \+ *lemma* prod.fst_star
- \+ *lemma* prod.snd_star
- \+ *lemma* prod.star_def
- \+ *lemma* units.embed_product_star



## [2022-05-02 17:28:46](https://github.com/leanprover-community/mathlib/commit/206a5f7)
feat(measure_theory/integral/bochner): Add a rewrite lemma saying the ennreal coercion of an integral of a nonnegative function equals the lintegral of the ennreal coercion of the function. ([#13701](https://github.com/leanprover-community/mathlib/pull/13701))
This PR adds a rewrite lemma `of_real_integral_eq_lintegral_of_real` that is very similar to `lintegral_coe_eq_integral`, but for nonnegative real-valued functions instead of nnreal-valued functions.
#### Estimated changes
Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.of_real_integral_eq_lintegral_of_real



## [2022-05-02 17:28:45](https://github.com/leanprover-community/mathlib/commit/917b527)
feat(topology/metric_space/thickened_indicator): Add definition and lemmas about thickened indicators. ([#13481](https://github.com/leanprover-community/mathlib/pull/13481))
Add thickened indicators, to be used for the proof of the portmanteau theorem.
#### Estimated changes
Modified src/data/real/ennreal.lean
- \+ *lemma* ennreal.div_le_div

Modified src/topology/instances/ennreal.lean


Added src/topology/metric_space/thickened_indicator.lean
- \+ *lemma* continuous_thickened_indicator_aux
- \+ *lemma* thickened_indicator.coe_fn_eq_comp
- \+ *def* thickened_indicator
- \+ *def* thickened_indicator_aux
- \+ *lemma* thickened_indicator_aux_closure_eq
- \+ *lemma* thickened_indicator_aux_le_one
- \+ *lemma* thickened_indicator_aux_lt_top
- \+ *lemma* thickened_indicator_aux_mono
- \+ *lemma* thickened_indicator_aux_one
- \+ *lemma* thickened_indicator_aux_one_of_mem_closure
- \+ *lemma* thickened_indicator_aux_subset
- \+ *lemma* thickened_indicator_aux_tendsto_indicator_closure
- \+ *lemma* thickened_indicator_aux_zero
- \+ *lemma* thickened_indicator_le_one
- \+ *lemma* thickened_indicator_mono
- \+ *lemma* thickened_indicator_one
- \+ *lemma* thickened_indicator_one_of_mem_closure
- \+ *lemma* thickened_indicator_subset
- \+ *lemma* thickened_indicator_tendsto_indicator_closure
- \+ *lemma* thickened_indicator_zero



## [2022-05-02 15:58:17](https://github.com/leanprover-community/mathlib/commit/af11e15)
feat(algebra/big_operators/finprod): add lemma `finprod_eq_prod_of_mul_support_to_finset_subset'` ([#13801](https://github.com/leanprover-community/mathlib/pull/13801))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/algebra/big_operators/finprod.lean
- \+ *lemma* finprod_eq_finset_prod_of_mul_support_subset



## [2022-05-02 15:58:16](https://github.com/leanprover-community/mathlib/commit/65843cd)
feat(analysis/matrix): provide a normed_algebra structure on matrices ([#13518](https://github.com/leanprover-community/mathlib/pull/13518))
This is one of the final pieces needed to defining the matrix exponential.
It would be nice to show:
```lean
lemma l1_linf_norm_to_matrix [nondiscrete_normed_field R] [decidable_eq n]
  (f : (n → R) →L[R] (m → R)) :
  ∥linear_map.to_matrix' (↑f : (n → R) →ₗ[R] (m → R))∥ = ∥f∥ :=
```
but its not clear to me under what generality it holds.
#### Estimated changes
Modified src/analysis/matrix.lean
- \+ *lemma* matrix.linfty_op_nnnorm_col
- \+ *lemma* matrix.linfty_op_nnnorm_def
- \+ *lemma* matrix.linfty_op_nnnorm_diagonal
- \+ *lemma* matrix.linfty_op_nnnorm_mul
- \+ *lemma* matrix.linfty_op_nnnorm_mul_vec
- \+ *lemma* matrix.linfty_op_nnnorm_row
- \+ *lemma* matrix.linfty_op_norm_col
- \+ *lemma* matrix.linfty_op_norm_def
- \+ *lemma* matrix.linfty_op_norm_diagonal
- \+ *lemma* matrix.linfty_op_norm_mul
- \+ *lemma* matrix.linfty_op_norm_mul_vec
- \+ *lemma* matrix.linfty_op_norm_row



## [2022-05-02 15:58:14](https://github.com/leanprover-community/mathlib/commit/90418df)
feat(linear_algebra/finite_dimensional): `finite_dimensional_iff_of_rank_eq_nsmul` ([#13357](https://github.com/leanprover-community/mathlib/pull/13357))
If `V` has a dimension that is a scalar multiple of the dimension of `W`, then `V` is finite dimensional iff `W` is.
#### Estimated changes
Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.finite_dimensional_iff_of_rank_eq_nsmul

Modified src/set_theory/cardinal/basic.lean
- \+ *lemma* cardinal.nsmul_lt_omega_iff
- \+ *lemma* cardinal.nsmul_lt_omega_iff_of_ne_zero



## [2022-05-02 15:58:14](https://github.com/leanprover-community/mathlib/commit/64bc02c)
feat(ring_theory/dedekind_domain): Chinese remainder theorem for Dedekind domains ([#13067](https://github.com/leanprover-community/mathlib/pull/13067))
The general Chinese remainder theorem states `R / I` is isomorphic to a product of `R / (P i ^ e i)`, where `P i` are comaximal, i.e.  `P i + P j = 1` for `i ≠ j`, and the infimum of all `P i` is `I`.
In a Dedekind domain the theorem can be stated in a more friendly way, namely that the `P i` are the factors (in the sense of a unique factorization domain) of `I`. This PR provides two ways of doing so, and includes some more lemmas on the ideals in a Dedekind domain.
#### Estimated changes
Modified src/ring_theory/dedekind_domain/ideal.lean
- \+ *lemma* ideal.coprime_of_no_prime_ge
- \+ *lemma* ideal.count_normalized_factors_eq
- \+ *lemma* ideal.is_prime.mul_mem_pow
- \+ *lemma* ideal.le_mul_of_no_prime_factors
- \+ *lemma* ideal.le_of_pow_le_prime
- \+ *lemma* ideal.pow_le_prime_iff
- \+ *lemma* ideal.prod_le_prime
- \+ *lemma* is_dedekind_domain.inf_prime_pow_eq_prod
- \+ *lemma* is_dedekind_domain.quotient_equiv_pi_factors_mk
- \+ *lemma* ring.dimension_le_one.prime_le_prime_iff_eq



## [2022-05-02 13:45:11](https://github.com/leanprover-community/mathlib/commit/384a7a3)
chore(.github/workflows/merge_conflicts.yaml): use separate token ([#13884](https://github.com/leanprover-community/mathlib/pull/13884))
#### Estimated changes
Modified .github/workflows/merge_conflicts.yml




## [2022-05-02 13:45:10](https://github.com/leanprover-community/mathlib/commit/ad2e936)
feat(topology/homeomorph): add `(co)map_cocompact` ([#13861](https://github.com/leanprover-community/mathlib/pull/13861))
Also rename `filter.comap_cocompact` to `filter.comap_cocompact_le`.
#### Estimated changes
Modified src/number_theory/modular.lean


Modified src/topology/homeomorph.lean
- \+ *lemma* homeomorph.comap_cocompact
- \+ *lemma* homeomorph.map_cocompact

Modified src/topology/subset_properties.lean
- \- *lemma* filter.comap_cocompact
- \+ *lemma* filter.comap_cocompact_le



## [2022-05-02 13:45:09](https://github.com/leanprover-community/mathlib/commit/dbc0339)
feat(category_theory/limits/shapes/types): explicit isos ([#13854](https://github.com/leanprover-community/mathlib/pull/13854))
Requested on Zulip. https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Relating.20the.20categorical.20product.20and.20the.20normal.20product
#### Estimated changes
Modified src/category_theory/limits/shapes/types.lean
- \+ *lemma* category_theory.limits.types.binary_coproduct_iso_inl_comp_hom
- \+ *lemma* category_theory.limits.types.binary_coproduct_iso_inl_comp_inv
- \+ *lemma* category_theory.limits.types.binary_coproduct_iso_inr_comp_hom
- \+ *lemma* category_theory.limits.types.binary_coproduct_iso_inr_comp_inv
- \+ *lemma* category_theory.limits.types.binary_product_iso_hom_comp_fst
- \+ *lemma* category_theory.limits.types.binary_product_iso_hom_comp_snd
- \+ *lemma* category_theory.limits.types.binary_product_iso_inv_comp_fst
- \+ *lemma* category_theory.limits.types.binary_product_iso_inv_comp_snd
- \+ *lemma* category_theory.limits.types.coequalizer_iso_quot_comp_inv
- \+ *lemma* category_theory.limits.types.coequalizer_iso_π_comp_hom
- \+ *lemma* category_theory.limits.types.coproduct_iso_mk_comp_inv
- \+ *lemma* category_theory.limits.types.coproduct_iso_ι_comp_hom
- \+ *lemma* category_theory.limits.types.equalizer_iso_hom_comp_subtype
- \+ *lemma* category_theory.limits.types.equalizer_iso_inv_comp_ι
- \+ *def* category_theory.limits.types.initial_colimit_cocone
- \- *def* category_theory.limits.types.initial_limit_cone
- \+ *lemma* category_theory.limits.types.product_iso_hom_comp_eval
- \+ *lemma* category_theory.limits.types.product_iso_inv_comp_π



## [2022-05-02 13:45:08](https://github.com/leanprover-community/mathlib/commit/9d3db53)
feat(category_theory/preadditive): End X is a division_ring or field when X is simple ([#13849](https://github.com/leanprover-community/mathlib/pull/13849))
Consequences of Schur's lemma
#### Estimated changes
Modified src/category_theory/preadditive/schur.lean
- \+ *def* category_theory.field_End_of_finite_dimensional
- \+/\- *lemma* category_theory.is_iso_iff_nonzero



## [2022-05-02 13:45:07](https://github.com/leanprover-community/mathlib/commit/e5b48f9)
chore(model_theory/basic): golf `countable_empty` ([#13836](https://github.com/leanprover-community/mathlib/pull/13836))
#### Estimated changes
Modified src/model_theory/basic.lean
- \+ *lemma* first_order.language.empty_card



## [2022-05-02 13:45:06](https://github.com/leanprover-community/mathlib/commit/4fe734d)
fix(algebra/indicator_function): add missing decidable instances to lemma statements   ([#13834](https://github.com/leanprover-community/mathlib/pull/13834))
This keeps the definition of `set.indicator` as non-computable, but ensures that when lemmas are applied they generalize to any decidable instances.
#### Estimated changes
Modified src/algebra/indicator_function.lean
- \+/\- *lemma* set.comp_mul_indicator
- \- *def* set.indicator
- \- *def* set.mul_indicator
- \+/\- *lemma* set.mul_indicator_apply
- \- *def* set.mul_indicator_hom
- \+/\- *lemma* set.piecewise_eq_mul_indicator

Modified src/combinatorics/simple_graph/inc_matrix.lean
- \- *def* simple_graph.inc_matrix

Modified src/geometry/euclidean/circumcenter.lean


Modified src/measure_theory/function/conditional_expectation.lean


Modified src/measure_theory/function/uniform_integrable.lean


Modified src/measure_theory/integral/bochner.lean
- \+/\- *lemma* measure_theory.simple_func.integral_eq_sum_filter
- \+/\- *lemma* measure_theory.simple_func.integral_eq_sum_of_subset

Modified src/measure_theory/probability_mass_function/monad.lean


Modified src/topology/instances/ennreal.lean




## [2022-05-02 13:45:04](https://github.com/leanprover-community/mathlib/commit/cf5fa84)
feat(analysis/normed_space/add_torsor_bases): add lemma `smooth_barycentric_coord` ([#13764](https://github.com/leanprover-community/mathlib/pull/13764))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/analysis/normed_space/add_torsor_bases.lean
- \+ *lemma* smooth_barycentric_coord



## [2022-05-02 13:45:03](https://github.com/leanprover-community/mathlib/commit/4113e00)
feat(linear_algebra/affine_space/basis): add lemma `affine_basis.linear_combination_coord_eq_self` ([#13763](https://github.com/leanprover-community/mathlib/pull/13763))
Formalized as part of the Sphere Eversion project.
#### Estimated changes
Modified src/linear_algebra/affine_space/basis.lean
- \+ *lemma* affine_basis.linear_combination_coord_eq_self



## [2022-05-02 13:45:02](https://github.com/leanprover-community/mathlib/commit/b063c28)
fix(src/tactic/alias): Support `alias foo ↔ ..` as documented ([#13743](https://github.com/leanprover-community/mathlib/pull/13743))
the current code and the single(!) use of this feature work only if
you write `alias foo ↔ . .` which is very odd.
#### Estimated changes
Modified src/data/polynomial/degree/definitions.lean


Modified src/tactic/alias.lean




## [2022-05-02 13:45:01](https://github.com/leanprover-community/mathlib/commit/3fde082)
refactor(topology/algebra/order): reorganize, simplify proofs ([#13716](https://github.com/leanprover-community/mathlib/pull/13716))
* Prove `has_compact_mul_support.is_compact_range`
* Simplify the proof of `continuous.exists_forall_le_of_has_compact_mul_support` and `continuous.bdd_below_range_of_has_compact_mul_support` using `has_compact_mul_support.is_compact_range`.
* Reorder `topology.algebra.order.basic` so that `is_compact.bdd_below` and friends are together with all results about `order_closed_topology`.
* Move `continuous.bdd_below_range_of_has_compact_mul_support` (and dual) to `topology.algebra.order.basic`
#### Estimated changes
Modified src/algebra/support.lean
- \+ *lemma* function.range_subset_insert_image_mul_support

Modified src/topology/algebra/order/basic.lean
- \+ *lemma* continuous.bdd_above_range_of_has_compact_mul_support
- \+ *lemma* continuous.bdd_below_range_of_has_compact_mul_support
- \+/\- *lemma* is_compact.bdd_above
- \+/\- *lemma* is_compact.bdd_above_image
- \+/\- *lemma* is_compact.bdd_below
- \+/\- *lemma* is_compact.bdd_below_image

Modified src/topology/algebra/order/compact.lean
- \- *lemma* continuous.bdd_above_range_of_has_compact_mul_support
- \- *lemma* continuous.bdd_below_range_of_has_compact_mul_support

Modified src/topology/support.lean
- \+ *lemma* has_compact_mul_support.is_compact_range
- \+ *lemma* range_eq_image_mul_tsupport_or
- \+ *lemma* range_subset_insert_image_mul_tsupport



## [2022-05-02 13:45:00](https://github.com/leanprover-community/mathlib/commit/52a454a)
feat(category_theory/limits): pushouts and pullbacks in the opposite category ([#13495](https://github.com/leanprover-community/mathlib/pull/13495))
This PR adds duality isomorphisms for the categories `wide_pushout_shape`, `wide_pullback_shape`, `walking_span`, `walking_cospan` and produce pullbacks/pushouts in the opposite category when pushouts/pullbacks exist.
#### Estimated changes
Modified src/category_theory/limits/opposites.lean
- \+ *lemma* category_theory.limits.has_pullbacks_opposite
- \+ *lemma* category_theory.limits.has_pushouts_opposite

Modified src/category_theory/limits/shapes/pullbacks.lean
- \+ *def* category_theory.limits.walking_cospan_op_equiv
- \+ *def* category_theory.limits.walking_span_op_equiv

Modified src/category_theory/limits/shapes/wide_pullbacks.lean
- \+ *def* category_theory.limits.wide_pullback_shape_op
- \+ *def* category_theory.limits.wide_pullback_shape_op_equiv
- \+ *def* category_theory.limits.wide_pullback_shape_op_map
- \+ *def* category_theory.limits.wide_pullback_shape_op_unop
- \+ *def* category_theory.limits.wide_pullback_shape_unop
- \+ *def* category_theory.limits.wide_pullback_shape_unop_op
- \+ *def* category_theory.limits.wide_pushout_shape_op
- \+ *def* category_theory.limits.wide_pushout_shape_op_equiv
- \+ *def* category_theory.limits.wide_pushout_shape_op_map
- \+ *def* category_theory.limits.wide_pushout_shape_op_unop
- \+ *def* category_theory.limits.wide_pushout_shape_unop
- \+ *def* category_theory.limits.wide_pushout_shape_unop_op



## [2022-05-02 11:44:57](https://github.com/leanprover-community/mathlib/commit/61d5d30)
feat(group_theory/group_action/basic): A multiplicative action induces an additive action of the additive group ([#13780](https://github.com/leanprover-community/mathlib/pull/13780))
`mul_action M α` induces `add_action (additive M) α`.
#### Estimated changes
Modified src/group_theory/group_action/defs.lean
- \+ *lemma* additive.of_mul_vadd
- \+ *lemma* multiplicative.of_add_smul



## [2022-05-02 11:44:56](https://github.com/leanprover-community/mathlib/commit/320df45)
refactor(linear_algebra/trace): unbundle `matrix.trace` ([#13712](https://github.com/leanprover-community/mathlib/pull/13712))
These extra type arguments are annoying to work with in many cases, especially when Lean doesn't have any information to infer the mostly-irrelevant `R` argument from. This came up while trying to work with `continuous.matrix_trace`, which is annoying to use for that reason.
The old bundled version is still available as `matrix.trace_linear_map`.
The cost of this change is that we have to copy across the usual set of obvious lemmas about additive maps; but we already do this for `diagonal`, `transpose` etc anyway.
#### Estimated changes
Modified src/algebra/lie/classical.lean


Modified src/combinatorics/simple_graph/adj_matrix.lean
- \+/\- *theorem* simple_graph.trace_adj_matrix

Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.diag_list_sum
- \+ *lemma* matrix.diag_multiset_sum
- \+ *lemma* matrix.diag_sum

Modified src/data/matrix/basis.lean
- \+ *lemma* matrix.std_basis_matrix.trace_eq
- \+/\- *lemma* matrix.std_basis_matrix.trace_zero

Modified src/data/matrix/hadamard.lean
- \+/\- *lemma* matrix.sum_hadamard_eq

Modified src/linear_algebra/matrix/charpoly/coeff.lean
- \+/\- *lemma* zmod.trace_pow_card

Modified src/linear_algebra/matrix/trace.lean
- \+/\- *def* matrix.trace
- \+ *lemma* matrix.trace_add
- \+ *def* matrix.trace_add_monoid_hom
- \- *lemma* matrix.trace_apply
- \+/\- *lemma* matrix.trace_col_mul_row
- \- *lemma* matrix.trace_diag
- \+/\- *lemma* matrix.trace_fin_one
- \+/\- *lemma* matrix.trace_fin_three
- \+/\- *lemma* matrix.trace_fin_two
- \+/\- *lemma* matrix.trace_fin_zero
- \+ *def* matrix.trace_linear_map
- \+ *lemma* matrix.trace_list_sum
- \+/\- *lemma* matrix.trace_mul_comm
- \+/\- *lemma* matrix.trace_mul_cycle'
- \+/\- *lemma* matrix.trace_mul_cycle
- \+ *lemma* matrix.trace_multiset_sum
- \+ *lemma* matrix.trace_neg
- \+/\- *lemma* matrix.trace_one
- \+ *lemma* matrix.trace_smul
- \+ *lemma* matrix.trace_sub
- \+ *lemma* matrix.trace_sum
- \+/\- *lemma* matrix.trace_transpose
- \+/\- *lemma* matrix.trace_transpose_mul
- \+ *lemma* matrix.trace_zero

Modified src/linear_algebra/trace.lean


Modified src/ring_theory/trace.lean


Modified src/topology/instances/matrix.lean
- \+/\- *lemma* continuous.matrix_trace



## [2022-05-02 11:44:55](https://github.com/leanprover-community/mathlib/commit/a627569)
feat(category_theory/monoidal): adjunctions in rigid categories ([#13707](https://github.com/leanprover-community/mathlib/pull/13707))
We construct the bijection on hom-sets `(Yᘁ ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)`
given by "pulling the string on the left" down or up, using right duals in a right rigid category.
As consequences, we show that a left rigid category is monoidal closed (it seems our lefts and rights have got mixed up!!), and that functors from a groupoid to a rigid category is again a rigid category.
#### Estimated changes
Modified src/algebra/category/FinVect.lean


Modified src/category_theory/monoidal/coherence.lean
- \+ *lemma* tactic.coherence.insert_id_lhs
- \+ *lemma* tactic.coherence.insert_id_rhs

Renamed src/category_theory/monoidal/rigid.lean to src/category_theory/monoidal/rigid/basic.lean
- \+ *lemma* category_theory.coevaluation_comp_left_adjoint_mate
- \+ *lemma* category_theory.coevaluation_comp_right_adjoint_mate
- \+ *lemma* category_theory.left_adjoint_mate_comp_evaluation
- \+ *lemma* category_theory.right_adjoint_mate_comp_evaluation
- \+ *def* category_theory.tensor_left_adjunction
- \+ *def* category_theory.tensor_left_hom_equiv
- \+ *lemma* category_theory.tensor_left_hom_equiv_id_tensor_comp_evaluation
- \+ *lemma* category_theory.tensor_left_hom_equiv_naturality
- \+ *lemma* category_theory.tensor_left_hom_equiv_symm_coevaluation_comp_id_tensor
- \+ *lemma* category_theory.tensor_left_hom_equiv_symm_coevaluation_comp_tensor_id
- \+ *lemma* category_theory.tensor_left_hom_equiv_symm_naturality
- \+ *lemma* category_theory.tensor_left_hom_equiv_tensor
- \+ *lemma* category_theory.tensor_left_hom_equiv_tensor_id_comp_evaluation
- \+ *def* category_theory.tensor_right_adjunction
- \+ *def* category_theory.tensor_right_hom_equiv
- \+ *lemma* category_theory.tensor_right_hom_equiv_id_tensor_comp_evaluation
- \+ *lemma* category_theory.tensor_right_hom_equiv_naturality
- \+ *lemma* category_theory.tensor_right_hom_equiv_symm_coevaluation_comp_id_tensor
- \+ *lemma* category_theory.tensor_right_hom_equiv_symm_coevaluation_comp_tensor_id
- \+ *lemma* category_theory.tensor_right_hom_equiv_symm_naturality
- \+ *lemma* category_theory.tensor_right_hom_equiv_tensor
- \+ *lemma* category_theory.tensor_right_hom_equiv_tensor_id_comp_evaluation

Added src/category_theory/monoidal/rigid/functor_category.lean


Modified src/category_theory/monoidal/rigid/of_equivalence.lean




## [2022-05-02 09:54:04](https://github.com/leanprover-community/mathlib/commit/fe44576)
feat(probability/martingale): the optional stopping theorem ([#13630](https://github.com/leanprover-community/mathlib/pull/13630))
We prove the optional stopping theorem (also known as the fair game theorem). This is number 62 on Freek 100 theorems.
#### Estimated changes
Modified docs/100.yaml


Modified src/algebra/indicator_function.lean
- \+ *lemma* set.mul_indicator_mul_compl_eq_piecewise

Modified src/measure_theory/integral/bochner.lean
- \+ *lemma* measure_theory.ae_le_trim_iff
- \+ *lemma* measure_theory.ae_le_trim_of_strongly_measurable

Modified src/measure_theory/integral/set_integral.lean
- \+ *lemma* measure_theory.integral_piecewise

Modified src/measure_theory/measure/measure_space.lean
- \+ *lemma* measure_theory.ae_le_of_ae_le_trim
- \+ *lemma* measure_theory.ae_of_ae_trim

Modified src/probability/martingale.lean
- \+ *lemma* measure_theory.submartingale_iff_expected_stopped_value_mono
- \+ *lemma* measure_theory.submartingale_of_expected_stopped_value_mono
- \+ *lemma* measure_theory.submartingale_of_set_integral_le

Modified src/probability/stopping.lean
- \+ *lemma* measure_theory.is_stopping_time.add
- \+ *lemma* measure_theory.is_stopping_time.add_const_nat
- \+ *lemma* measure_theory.is_stopping_time.piecewise_of_le
- \+ *lemma* measure_theory.is_stopping_time_piecewise_const
- \+ *lemma* measure_theory.stopped_value_const
- \+ *lemma* measure_theory.stopped_value_piecewise_const'
- \+ *lemma* measure_theory.stopped_value_piecewise_const



## [2022-05-02 06:04:17](https://github.com/leanprover-community/mathlib/commit/db0b495)
chore(category_theory/limits/cones): avoid a timeout from @[simps] ([#13877](https://github.com/leanprover-community/mathlib/pull/13877))
This was causing a timeout on another branch.
#### Estimated changes
Modified src/category_theory/limits/cones.lean




## [2022-05-02 06:04:16](https://github.com/leanprover-community/mathlib/commit/67c0e13)
doc(data/polynomial/basic): Remove references to `polynomial.norm2` ([#13847](https://github.com/leanprover-community/mathlib/pull/13847))
`polynomial.norm2` was never added to mathlib.
#### Estimated changes
Modified src/data/polynomial/mirror.lean




## [2022-05-02 06:04:15](https://github.com/leanprover-community/mathlib/commit/03ed4c7)
move(topology/algebra/floor_ring → order/floor): Move topological properties of `⌊x⌋` and `⌈x⌉` ([#13824](https://github.com/leanprover-community/mathlib/pull/13824))
Those belong in an order folder.
#### Estimated changes
Modified src/measure_theory/integral/periodic.lean


Renamed src/topology/algebra/floor_ring.lean to src/topology/algebra/order/floor.lean




## [2022-05-02 06:04:14](https://github.com/leanprover-community/mathlib/commit/aaa167c)
feat(linear_algebra/matrix/adjugate): `adjugate` of a diagonal matrix is diagonal ([#13818](https://github.com/leanprover-community/mathlib/pull/13818))
This proof is a bit ugly...
#### Estimated changes
Modified src/data/matrix/basic.lean
- \+ *lemma* matrix.diagonal_update_column_single
- \+ *lemma* matrix.diagonal_update_row_single

Modified src/linear_algebra/matrix/adjugate.lean
- \+ *lemma* matrix.adjugate_diagonal



## [2022-05-02 06:04:13](https://github.com/leanprover-community/mathlib/commit/34bbec6)
feat(logic/equiv/local_equiv): add `forall_mem_target`/`exists_mem_target` ([#13805](https://github.com/leanprover-community/mathlib/pull/13805))
#### Estimated changes
Modified src/logic/equiv/local_equiv.lean
- \+ *lemma* local_equiv.exists_mem_target
- \+ *lemma* local_equiv.forall_mem_target



## [2022-05-02 06:04:12](https://github.com/leanprover-community/mathlib/commit/179b6c0)
feat(logic/equiv/local_equiv): add inhabited instances ([#13804](https://github.com/leanprover-community/mathlib/pull/13804))
#### Estimated changes
Modified src/logic/equiv/local_equiv.lean




## [2022-05-02 06:04:11](https://github.com/leanprover-community/mathlib/commit/c1f8ac5)
feat(order/zorn): add Zorn lemma on a preorder ([#13803](https://github.com/leanprover-community/mathlib/pull/13803))
#### Estimated changes
Modified src/order/chain.lean
- \+ *lemma* is_chain.mono_rel

Modified src/order/zorn.lean
- \+ *theorem* zorn_nonempty_partial_order
- \- *lemma* zorn_nonempty_partial_order
- \+ *theorem* zorn_nonempty_preorder
- \+ *theorem* zorn_nonempty_preorder₀
- \+/\- *lemma* zorn_partial_order
- \+ *theorem* zorn_partial_order₀
- \- *lemma* zorn_partial_order₀
- \+ *theorem* zorn_preorder
- \+ *theorem* zorn_preorder₀



## [2022-05-02 06:04:10](https://github.com/leanprover-community/mathlib/commit/925c473)
chore(analysis/normed_space/add_torsor): make coefficients explicit in lemmas about eventual dilations ([#13796](https://github.com/leanprover-community/mathlib/pull/13796))
For an example of why we should do this, see: https://github.com/leanprover-community/sphere-eversion/blob/19c461c9fba484090ff0af6f0c0204c623f63713/src/loops/surrounding.lean#L176
#### Estimated changes
Modified src/analysis/normed_space/add_torsor.lean




## [2022-05-02 06:04:09](https://github.com/leanprover-community/mathlib/commit/90b1ddb)
feat(linear_algebra/finite_dimensional): of_injective ([#13792](https://github.com/leanprover-community/mathlib/pull/13792))
#### Estimated changes
Modified src/analysis/normed_space/finite_dimension.lean


Modified src/linear_algebra/finite_dimensional.lean
- \+ *lemma* finite_dimensional.of_injective
- \+ *lemma* finite_dimensional.of_surjective



## [2022-05-02 06:04:08](https://github.com/leanprover-community/mathlib/commit/0587eb1)
feat(data/zmod/basic): Variant of `zmod.val_int_cast` ([#13781](https://github.com/leanprover-community/mathlib/pull/13781))
This PR adds a variant of `zmod.val_int_cast` avoiding the characteristic assumption.
#### Estimated changes
Modified src/data/zmod/basic.lean
- \+ *lemma* zmod.coe_int_cast



## [2022-05-02 06:04:07](https://github.com/leanprover-community/mathlib/commit/fd4188d)
feat(data/zmod/basic): `zmod 0` is infinite ([#13779](https://github.com/leanprover-community/mathlib/pull/13779))
This PR adds an instance stating that `zmod 0` is infinite.
#### Estimated changes
Modified src/data/zmod/basic.lean




## [2022-05-02 06:04:06](https://github.com/leanprover-community/mathlib/commit/5c91490)
refactor(field_theory/separable): move content about polynomial.expand earlier ([#13776](https://github.com/leanprover-community/mathlib/pull/13776))
There were some definitions about polynomial.expand buried in the middle of `field_theory.separable` for no good reason. No changes to content, just moves stuff to an earlier file.
#### Estimated changes
Added src/data/polynomial/expand.lean
- \+ *lemma* polynomial.coe_expand
- \+ *theorem* polynomial.coeff_contract
- \+ *theorem* polynomial.coeff_expand
- \+ *theorem* polynomial.coeff_expand_mul'
- \+ *theorem* polynomial.coeff_expand_mul
- \+ *theorem* polynomial.contract_expand
- \+ *theorem* polynomial.derivative_expand
- \+ *lemma* polynomial.expand_C
- \+ *lemma* polynomial.expand_X
- \+ *theorem* polynomial.expand_char
- \+ *theorem* polynomial.expand_contract
- \+ *theorem* polynomial.expand_eq_C
- \+ *lemma* polynomial.expand_eq_sum
- \+ *theorem* polynomial.expand_eq_zero
- \+ *lemma* polynomial.expand_eval
- \+ *theorem* polynomial.expand_expand
- \+ *theorem* polynomial.expand_inj
- \+ *lemma* polynomial.expand_injective
- \+ *lemma* polynomial.expand_monomial
- \+ *theorem* polynomial.expand_mul
- \+ *theorem* polynomial.expand_one
- \+ *theorem* polynomial.expand_pow
- \+ *theorem* polynomial.expand_zero
- \+ *theorem* polynomial.is_local_ring_hom_expand
- \+ *theorem* polynomial.map_expand
- \+ *theorem* polynomial.map_expand_pow_char
- \+ *lemma* polynomial.monic.expand
- \+ *theorem* polynomial.nat_degree_expand
- \+ *theorem* polynomial.of_irreducible_expand
- \+ *theorem* polynomial.of_irreducible_expand_pow

Modified src/field_theory/finite/basic.lean


Modified src/field_theory/separable.lean
- \- *lemma* polynomial.coe_expand
- \- *theorem* polynomial.coeff_contract
- \- *theorem* polynomial.coeff_expand
- \- *theorem* polynomial.coeff_expand_mul'
- \- *theorem* polynomial.coeff_expand_mul
- \- *theorem* polynomial.contract_expand
- \- *theorem* polynomial.derivative_expand
- \- *lemma* polynomial.expand_C
- \- *lemma* polynomial.expand_X
- \- *theorem* polynomial.expand_char
- \- *theorem* polynomial.expand_contract
- \- *theorem* polynomial.expand_eq_C
- \- *lemma* polynomial.expand_eq_sum
- \- *theorem* polynomial.expand_eq_zero
- \- *lemma* polynomial.expand_eval
- \- *theorem* polynomial.expand_expand
- \- *theorem* polynomial.expand_inj
- \- *lemma* polynomial.expand_injective
- \- *lemma* polynomial.expand_monomial
- \- *theorem* polynomial.expand_mul
- \- *theorem* polynomial.expand_one
- \- *theorem* polynomial.expand_pow
- \- *theorem* polynomial.expand_zero
- \- *theorem* polynomial.is_local_ring_hom_expand
- \- *theorem* polynomial.map_expand
- \- *theorem* polynomial.map_expand_pow_char
- \- *lemma* polynomial.monic.expand
- \- *theorem* polynomial.nat_degree_expand
- \- *theorem* polynomial.of_irreducible_expand
- \- *theorem* polynomial.of_irreducible_expand_pow

Modified src/ring_theory/algebraic.lean




## [2022-05-02 06:04:05](https://github.com/leanprover-community/mathlib/commit/000cae1)
feat(representation_theory): Rep k G is symmetric monoidal ([#13685](https://github.com/leanprover-community/mathlib/pull/13685))
#### Estimated changes
Modified src/representation_theory/Action.lean
- \+ *def* Action.forget_braided
- \+/\- *def* Action.forget_monoidal

Modified src/representation_theory/Rep.lean




## [2022-05-02 06:04:04](https://github.com/leanprover-community/mathlib/commit/1e38549)
feat(analysis/matrix): define the frobenius norm on matrices ([#13497](https://github.com/leanprover-community/mathlib/pull/13497))
#### Estimated changes
Modified src/analysis/matrix.lean
- \+ *lemma* matrix.frobenius_nnnorm_col
- \+ *lemma* matrix.frobenius_nnnorm_def
- \+ *lemma* matrix.frobenius_nnnorm_diagonal
- \+ *lemma* matrix.frobenius_nnnorm_map_eq
- \+ *lemma* matrix.frobenius_nnnorm_mul
- \+ *lemma* matrix.frobenius_nnnorm_one
- \+ *lemma* matrix.frobenius_nnnorm_row
- \+ *lemma* matrix.frobenius_nnnorm_transpose
- \+ *lemma* matrix.frobenius_norm_col
- \+ *lemma* matrix.frobenius_norm_def
- \+ *lemma* matrix.frobenius_norm_diagonal
- \+ *lemma* matrix.frobenius_norm_map_eq
- \+ *lemma* matrix.frobenius_norm_mul
- \+ *lemma* matrix.frobenius_norm_row
- \+ *lemma* matrix.frobenius_norm_transpose
- \+ *def* matrix.frobenius_normed_algebra
- \+ *def* matrix.frobenius_normed_group
- \+ *def* matrix.frobenius_normed_ring
- \+ *def* matrix.frobenius_normed_space
- \+ *def* matrix.frobenius_semi_normed_group
- \+ *lemma* matrix.nnnorm_entry_le_entrywise_sup_nnnorm
- \- *lemma* matrix.nnnorm_entry_le_entrywise_sup_nnorm



## [2022-05-02 05:27:14](https://github.com/leanprover-community/mathlib/commit/3d946a3)
chore(algebraic_geometry/AffineScheme): Speed up `Spec` ([#13866](https://github.com/leanprover-community/mathlib/pull/13866))
`simps` take 38s in local and does not seem to generate any useful lemma.
#### Estimated changes
Modified src/algebraic_geometry/AffineScheme.lean




## [2022-05-02 04:39:58](https://github.com/leanprover-community/mathlib/commit/523adb3)
feat(set_theory/game/nim): Birthday of `nim` ([#13873](https://github.com/leanprover-community/mathlib/pull/13873))
#### Estimated changes
Modified src/set_theory/game/nim.lean
- \+ *lemma* pgame.nim.nim_birthday



## [2022-05-02 04:39:57](https://github.com/leanprover-community/mathlib/commit/039543c)
refactor(set_theory/game/pgame): Simpler definition for `star` ([#13869](https://github.com/leanprover-community/mathlib/pull/13869))
This new definition gives marginally easier proofs for the basic lemmas, and avoids use of the quite incomplete `of_lists` API.
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+/\- *def* pgame.star
- \+/\- *theorem* pgame.star_left_moves
- \+/\- *theorem* pgame.star_move_left
- \+/\- *theorem* pgame.star_move_right
- \+/\- *theorem* pgame.star_right_moves



## [2022-05-02 04:39:56](https://github.com/leanprover-community/mathlib/commit/26e24c7)
feat(set_theory/surreal/basic): `<` is transitive on numeric games ([#13812](https://github.com/leanprover-community/mathlib/pull/13812))
#### Estimated changes
Modified src/set_theory/surreal/basic.lean
- \+ *theorem* pgame.lt_trans'
- \+ *theorem* pgame.lt_trans



## [2022-05-02 02:37:54](https://github.com/leanprover-community/mathlib/commit/922717e)
chore(logic/function/basic): don't unfold set in cantor ([#13822](https://github.com/leanprover-community/mathlib/pull/13822))
This uses `set_of` and `mem` consistently instead of using application everywhere, since `f` has type `A -> set A` instead of `A -> A -> Prop`. (Arguably, it could just be stated for `A -> A -> Prop` instead though.)
#### Estimated changes
Modified src/logic/function/basic.lean
- \+/\- *theorem* function.cantor_injective



## [2022-05-02 01:07:34](https://github.com/leanprover-community/mathlib/commit/afc0700)
feat(linear_algebra/tensor_product): define tensor_tensor_tensor_assoc ([#13864](https://github.com/leanprover-community/mathlib/pull/13864))
#### Estimated changes
Modified src/linear_algebra/tensor_product.lean
- \+ *def* tensor_product.tensor_tensor_tensor_assoc
- \+ *lemma* tensor_product.tensor_tensor_tensor_assoc_symm_tmul
- \+ *lemma* tensor_product.tensor_tensor_tensor_assoc_tmul



## [2022-05-01 21:51:02](https://github.com/leanprover-community/mathlib/commit/b236cb2)
chore(set_theory/surreal/basic): Inline instances ([#13811](https://github.com/leanprover-community/mathlib/pull/13811))
We inline various definitions used only for instances. We also remove the redundant lemma `not_le` (which is more generally true on preorders).
#### Estimated changes
Modified src/set_theory/surreal/basic.lean
- \- *def* surreal.add
- \- *def* surreal.le
- \- *def* surreal.lt
- \- *def* surreal.neg
- \- *theorem* surreal.not_le



## [2022-05-01 21:16:30](https://github.com/leanprover-community/mathlib/commit/f0930c8)
feat(set_theory/pgame/impartial): `star` is impartial ([#13842](https://github.com/leanprover-community/mathlib/pull/13842))
#### Estimated changes
Modified src/set_theory/game/impartial.lean


Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.neg_star



## [2022-05-01 18:53:38](https://github.com/leanprover-community/mathlib/commit/071cb55)
feat(data/set/function): missing mono lemmas ([#13863](https://github.com/leanprover-community/mathlib/pull/13863))
#### Estimated changes
Modified src/data/set/function.lean
- \+ *lemma* antitone_on.mono
- \+ *lemma* monotone_on.mono
- \+ *lemma* strict_anti_on.mono
- \+ *lemma* strict_mono_on.mono



## [2022-05-01 12:36:26](https://github.com/leanprover-community/mathlib/commit/9e7c80f)
docs(*): Wrap some links in < … > ([#13852](https://github.com/leanprover-community/mathlib/pull/13852))
I noticed that many docs say
    See https://stacks.math.columbia.edu/tag/001T.
and the our documentation will include the final `.` in the URL, causing
the URL to not work.
This tries to fix some of these instances. I intentionally applied this
to some URLs ending with a space, because it does not hurt to be
explicit, and the next contributor cargo-culting the URL is more likely
to get this right.
Obligatory xkcd reference: https://xkcd.com/208/
#### Estimated changes
Modified CODE_OF_CONDUCT.md


Modified src/algebraic_geometry/ringed_space.lean


Modified src/category_theory/abelian/basic.lean


Modified src/category_theory/abelian/images.lean


Modified src/category_theory/abelian/transfer.lean


Modified src/category_theory/additive/basic.lean


Modified src/category_theory/adjunction/basic.lean


Modified src/category_theory/adjunction/fully_faithful.lean


Modified src/category_theory/adjunction/limits.lean


Modified src/category_theory/category/basic.lean


Modified src/category_theory/category/preorder.lean


Modified src/category_theory/discrete_category.lean


Modified src/category_theory/equivalence.lean


Modified src/category_theory/essential_image.lean


Modified src/category_theory/filtered.lean


Modified src/category_theory/full_subcategory.lean


Modified src/category_theory/functor/basic.lean


Modified src/category_theory/functor/fully_faithful.lean


Modified src/category_theory/is_connected.lean


Modified src/category_theory/isomorphism.lean


Modified src/category_theory/limits/constructions/limits_of_products_and_equalizers.lean


Modified src/category_theory/limits/final.lean


Modified src/category_theory/limits/is_limit.lean


Modified src/category_theory/limits/presheaf.lean


Modified src/category_theory/limits/shapes/binary_products.lean


Modified src/category_theory/limits/shapes/pullbacks.lean


Modified src/category_theory/limits/types.lean


Modified src/category_theory/monoidal/braided.lean


Modified src/category_theory/monoidal/category.lean


Modified src/category_theory/monoidal/functor.lean


Modified src/category_theory/opposites.lean


Modified src/category_theory/over.lean


Modified src/category_theory/products/basic.lean


Modified src/category_theory/single_obj.lean


Modified src/category_theory/sites/canonical.lean


Modified src/category_theory/sites/cover_lifting.lean


Modified src/category_theory/sites/cover_preserving.lean


Modified src/category_theory/sites/grothendieck.lean


Modified src/category_theory/sites/plus.lean


Modified src/category_theory/sites/pretopology.lean


Modified src/category_theory/sites/sheaf.lean


Modified src/category_theory/sites/sheaf_of_types.lean


Modified src/category_theory/triangulated/basic.lean


Modified src/category_theory/triangulated/pretriangulated.lean


Modified src/category_theory/types.lean


Modified src/category_theory/yoneda.lean


Modified src/topology/category/Top/limits.lean


Modified src/topology/sheaves/forget.lean


Modified src/topology/sheaves/sheafify.lean


Modified src/topology/tietze_extension.lean




## [2022-05-01 05:59:37](https://github.com/leanprover-community/mathlib/commit/232c15e)
feat(set_theory/game/pgame): Add missing basic API ([#13744](https://github.com/leanprover-community/mathlib/pull/13744))
#### Estimated changes
Modified src/set_theory/game/pgame.lean
- \+ *theorem* pgame.half_left_moves
- \+/\- *lemma* pgame.half_move_left
- \+/\- *lemma* pgame.half_move_right
- \+ *theorem* pgame.half_right_moves
- \+ *theorem* pgame.le_zero_of_is_empty_left_moves
- \+ *lemma* pgame.left_moves_of_lists
- \+/\- *def* pgame.of_lists
- \+ *theorem* pgame.of_lists_move_left'
- \+ *theorem* pgame.of_lists_move_left
- \+ *theorem* pgame.of_lists_move_right'
- \+ *theorem* pgame.of_lists_move_right
- \+/\- *lemma* pgame.one_left_moves
- \+/\- *lemma* pgame.one_move_left
- \+/\- *lemma* pgame.one_right_moves
- \+ *lemma* pgame.right_moves_of_lists
- \+/\- *def* pgame.star
- \+ *theorem* pgame.star_left_moves
- \+ *theorem* pgame.star_move_left
- \+ *theorem* pgame.star_move_right
- \+ *theorem* pgame.star_right_moves
- \+ *def* pgame.to_of_lists_left_moves
- \+ *def* pgame.to_of_lists_right_moves
- \+ *theorem* pgame.zero_le_of_is_empty_right_moves
- \+ *theorem* pgame.zero_le_one
- \+/\- *lemma* pgame.zero_left_moves
- \+/\- *theorem* pgame.zero_lt_one
- \+/\- *lemma* pgame.zero_right_moves



## [2022-05-01 03:35:34](https://github.com/leanprover-community/mathlib/commit/51b1e11)
feat(set_theory/game/impartial): Relabelling of impartial game is impartial ([#13843](https://github.com/leanprover-community/mathlib/pull/13843))
#### Estimated changes
Modified src/set_theory/game/impartial.lean
- \+ *theorem* pgame.impartial.impartial_congr



## [2022-05-01 03:00:28](https://github.com/leanprover-community/mathlib/commit/4b92515)
chore(set_theory/game/impartial): golf ([#13841](https://github.com/leanprover-community/mathlib/pull/13841))
#### Estimated changes
Modified src/set_theory/game/impartial.lean


