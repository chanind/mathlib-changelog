### [2021-12-31 22:23:24](https://github.com/leanprover-community/mathlib/commit/8db2fa0)
chore(category_theory/closed/cartesian): make exp right-associative ([#11172](https://github.com/leanprover-community/mathlib/pull/11172))
This makes `X ⟹ Y ⟹ Z` parse as `X ⟹ (Y ⟹ Z)`, like ordinary function types.

### [2021-12-31 22:23:23](https://github.com/leanprover-community/mathlib/commit/559951c)
feat(data/quot): Add quotient pi induction ([#11137](https://github.com/leanprover-community/mathlib/pull/11137))
I am planning to use this later to show that the (pi) product of homotopy classes of paths is well-defined, and prove
properties about that product.

### [2021-12-31 22:23:22](https://github.com/leanprover-community/mathlib/commit/200f47d)
feat(analysis/normed_space/banach_steinhaus): prove the standard Banach-Steinhaus theorem ([#10663](https://github.com/leanprover-community/mathlib/pull/10663))
Here we prove the Banach-Steinhaus theorem for maps from a Banach space into a (semi-)normed space. This is the standard version of the theorem and the proof proceeds via the Baire category theorem. Notably, the version from barelled spaces to locally convex spaces is not included because these spaces do not yet exist in `mathlib`. In addition, it is established that the pointwise limit of continuous linear maps from a Banach space into a normed space is itself a continuous linear map.
- [x] depends on: [#10700](https://github.com/leanprover-community/mathlib/pull/10700)

### [2021-12-31 21:03:20](https://github.com/leanprover-community/mathlib/commit/ea710ca)
feat(data/polynomial/ring_division): golf and generalize `leading_coeff_div_by_monic_of_monic` ([#11077](https://github.com/leanprover-community/mathlib/pull/11077))
No longer require that the underlying ring is a domain.
Also added helper API lemma `leading_coeff_monic_mul`.

### [2021-12-31 21:03:19](https://github.com/leanprover-community/mathlib/commit/8ec59f9)
feat(data/int/gcd): add theorem `gcd_least_linear` ([#10743](https://github.com/leanprover-community/mathlib/pull/10743))
For nonzero integers `a` and `b`, `gcd a b` is the smallest positive integer that can be written in the form `a * x + b * y` for some pair of integers `x` and `y`
This is an extension of Bézout's lemma (`gcd_eq_gcd_ab`), which says that `gcd a b` can be written in that form.

### [2021-12-31 19:13:58](https://github.com/leanprover-community/mathlib/commit/e4607f8)
chore(data/sym/basic): golf and add missing simp lemmas ([#11160](https://github.com/leanprover-community/mathlib/pull/11160))
By changing `cons` to not use pattern matching, `(a :: s).1 = a ::ₘ s.1` is true by `rfl`, which is convenient here and there for golfing.

### [2021-12-31 19:13:57](https://github.com/leanprover-community/mathlib/commit/fbbbdfa)
feat(algebra/star/self_adjoint): define the self-adjoint elements of a star additive group ([#11135](https://github.com/leanprover-community/mathlib/pull/11135))
Given a type `R` with `[add_group R] [star_add_monoid R]`, we define `self_adjoint R` as the additive subgroup of self-adjoint elements, i.e. those such that `star x = x`. To avoid confusion, we move `is_self_adjoint` (which defines this to mean `⟪T x, y⟫ = ⟪x, T y⟫` in an inner product space) to the `inner_product_space` namespace.

### [2021-12-31 19:13:55](https://github.com/leanprover-community/mathlib/commit/fdf09df)
feat(data/polynomial/degree/lemmas): (nat_)degree_sum_eq_of_disjoint ([#11121](https://github.com/leanprover-community/mathlib/pull/11121))
Also two helper lemmas on `nat_degree`.
Generalize `degree_sum_fin_lt` to semirings

### [2021-12-31 16:13:18](https://github.com/leanprover-community/mathlib/commit/c4caf0e)
feat(linear_algebra/multilinear/basic): add dependent version of `multilinear_map.dom_dom_congr_linear_equiv` ([#10474](https://github.com/leanprover-community/mathlib/pull/10474))
Formalized as part of the Sphere Eversion project.

### [2021-12-31 14:15:50](https://github.com/leanprover-community/mathlib/commit/9a38c19)
feat(data/list/indexes): map_with_index_eq_of_fn ([#11163](https://github.com/leanprover-community/mathlib/pull/11163))
Some `list.map_with_index` API.

### [2021-12-31 14:15:49](https://github.com/leanprover-community/mathlib/commit/b92afc9)
chore(data/equiv/basic): missing dsimp lemmas ([#11159](https://github.com/leanprover-community/mathlib/pull/11159))

### [2021-12-31 14:15:48](https://github.com/leanprover-community/mathlib/commit/bcf1d2d)
feat(category_theory/sites/plus): Adds a functorial version of `J.diagram P`, functorial in `P`. ([#11155](https://github.com/leanprover-community/mathlib/pull/11155))

### [2021-12-31 14:15:46](https://github.com/leanprover-community/mathlib/commit/7b38792)
feat(category_theory/limits/functor_category): Some additional isomorphisms involving (co)limits of functors. ([#11152](https://github.com/leanprover-community/mathlib/pull/11152))

### [2021-12-31 14:15:45](https://github.com/leanprover-community/mathlib/commit/b142b69)
feat(data/list/count): add lemma `count_le_count_map` ([#11148](https://github.com/leanprover-community/mathlib/pull/11148))
Generalises `count_map_map`: for any `f : α → β` (not necessarily injective), `count x l ≤ count (f x) (map f l)`

### [2021-12-31 14:15:44](https://github.com/leanprover-community/mathlib/commit/dc57b54)
feat(ring_theory/localization): Transferring `is_localization` along equivs. ([#11146](https://github.com/leanprover-community/mathlib/pull/11146))

### [2021-12-31 14:15:43](https://github.com/leanprover-community/mathlib/commit/bc5e008)
feat(data/dfinsupp/order): Pointwise order on finitely supported dependent functions ([#11138](https://github.com/leanprover-community/mathlib/pull/11138))
This defines the pointwise order on `Π₀ i, α i`, in very much the same way as in `data.finsupp.order`. It also moves `data.dfinsupp` to `data.dfinsupp.basic`.

### [2021-12-31 14:15:42](https://github.com/leanprover-community/mathlib/commit/2e8ebdc)
feat(algebra/homology): Construction of null homotopic chain complex … ([#11125](https://github.com/leanprover-community/mathlib/pull/11125))
…morphisms and one lemma on addivity of homotopies

### [2021-12-31 14:15:41](https://github.com/leanprover-community/mathlib/commit/ff7e837)
feat(combinatorics/configuration): Variant of `exists_injective_of_card_le` ([#11116](https://github.com/leanprover-community/mathlib/pull/11116))
Proves a variant of `exists_injective_of_card_le` that will be useful in an upcoming proof.

### [2021-12-31 14:15:41](https://github.com/leanprover-community/mathlib/commit/1fd70b1)
refactor(algebra/big_operators/basic): Reorder lemmas ([#11113](https://github.com/leanprover-community/mathlib/pull/11113))
This PR does the following things:
- Move `prod_bij` and `prod_bij'` earlier in the file, so that they can be put to use.
- Move `prod_product` and `prod_product'` past `prod_sigma` and `prod_sigma'` down to `prod_product_right` and `prod_product_right'`.
- Use `prod_bij` and `prod_sigma` to give an easier proof of `prod_product`.
- The new proof introduces `prod_finset_product` and the remaining three analogs of the four `prod_product` lemmas.
`prod_finset_product` is a lemma that I found helpful in my own work.

### [2021-12-31 14:15:40](https://github.com/leanprover-community/mathlib/commit/99e3ffb)
feat(data/fin/tuple): new directory and file on sorting ([#11096](https://github.com/leanprover-community/mathlib/pull/11096))
Code written by @kmill at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Permutation.20to.20make.20a.20function.20monotone
Co-authored by: Kyle Miller <kmill31415@gmail.com>

### [2021-12-31 14:15:39](https://github.com/leanprover-community/mathlib/commit/06a0197)
feat(category_theory/bicategory/basic): define bicategories ([#11079](https://github.com/leanprover-community/mathlib/pull/11079))
This PR defines bicategories and gives basic lemmas.

### [2021-12-31 14:15:37](https://github.com/leanprover-community/mathlib/commit/a5573f3)
feat(data/{fin,multi}set/powerset): add some lemmas about powerset_len ([#10866](https://github.com/leanprover-community/mathlib/pull/10866))
For both multisets and finsets
From flt-regular

### [2021-12-31 12:26:01](https://github.com/leanprover-community/mathlib/commit/78a9900)
refactor(algebra/group/hom_instances): relax semiring to non_unital_non_assoc_semiring in add_monoid_hom.mul ([#11165](https://github.com/leanprover-community/mathlib/pull/11165))
Previously `algebra.group.hom_instances` ended with some results showing that left and right multiplication operators are additive monoid homomorphisms between (unital, associative) semirings. The assumptions of a unit and associativity are not required for these results to work, so we relax the condition to `non_unital_non_assoc_semiring`.
Required for [#11073](https://github.com/leanprover-community/mathlib/pull/11073) .

### [2021-12-31 07:44:08](https://github.com/leanprover-community/mathlib/commit/dc1525f)
docs(data/sum/basic): Expand module docstring and cleanup ([#11158](https://github.com/leanprover-community/mathlib/pull/11158))
This moves `data.sum` to `data.sum.basic`, provides a proper docstring for it, cleans it up.
There are no new declarations, just some file rearrangement, variable grouping, unindentation, and a `protected` attribute for `sum.lex.inl`/`sum.lex.inr` to avoid them clashing with `sum.inl`/`sum.inr`.

### [2021-12-30 21:39:31](https://github.com/leanprover-community/mathlib/commit/e1a8b88)
feat(tactic/itauto): add support for [decidable p] assumptions ([#10744](https://github.com/leanprover-community/mathlib/pull/10744))
This allows proving theorems like the following, which use excluded middle selectively through `decidable` assumptions:
```
example (p q r : Prop) [decidable p] : (p → (q ∨ r)) → ((p → q) ∨ (p → r)) := by itauto
```
This also fixes a bug in the proof search order of the original itauto implementation causing nontermination in one of the new tests, which also makes the "big test" at the end run instantly.
Also adds a `!` option to enable decidability for all propositions using classical logic.
Because adding decidability instances can be expensive for proof search, they are disabled by default. You can specify specific decidable instances to add by `itauto [p, q]`, or use `itauto*` which adds all decidable atoms. (The `!` option is useless on its own, and should be combined with `*` or `[p]` options.)

### [2021-12-30 20:16:32](https://github.com/leanprover-community/mathlib/commit/7f92832)
feat(category_theory/currying): `flip` is isomorphic to uncurrying, swapping, and currying. ([#11151](https://github.com/leanprover-community/mathlib/pull/11151))

### [2021-12-30 18:41:23](https://github.com/leanprover-community/mathlib/commit/3dad7c8)
chore(algebra/ring/comp_typeclasses): fix doctrings ([#11150](https://github.com/leanprover-community/mathlib/pull/11150))
This fixes the docstrings of two typeclasses.

### [2021-12-30 16:51:28](https://github.com/leanprover-community/mathlib/commit/682f1e6)
feat(analysis/normed_space/operator_norm): generalize linear_map.bound_of_ball_bound ([#11140](https://github.com/leanprover-community/mathlib/pull/11140))
This was proved over `is_R_or_C` but holds (in a slightly different form) over all nondiscrete normed fields.

### [2021-12-30 16:51:27](https://github.com/leanprover-community/mathlib/commit/c0b5ce1)
feat(data/nat/choose/basic): choose_eq_zero_iff ([#11120](https://github.com/leanprover-community/mathlib/pull/11120))

### [2021-12-30 16:51:27](https://github.com/leanprover-community/mathlib/commit/993a470)
feat(analysis/special_functions/log): add log_div_self_antitone_on ([#10985](https://github.com/leanprover-community/mathlib/pull/10985))
Adds lemma `log_div_self_antitone_on`, which shows that `log x / x` is decreasing when `exp 1 \le x`. Needed for Bertrand's postulate ([#8002](https://github.com/leanprover-community/mathlib/pull/8002)).

### [2021-12-30 14:54:46](https://github.com/leanprover-community/mathlib/commit/ac97675)
feat(data/polynomial/degree/definition): nat_degree_monomial in ite form ([#11123](https://github.com/leanprover-community/mathlib/pull/11123))
Changed the proof usage elsewhere.
This helps deal with sums of over monomials.

### [2021-12-30 14:54:45](https://github.com/leanprover-community/mathlib/commit/424773a)
feat(data/finset/fold): fold_const, fold_ite ([#11122](https://github.com/leanprover-community/mathlib/pull/11122))

### [2021-12-30 14:54:44](https://github.com/leanprover-community/mathlib/commit/c8a5762)
feat(order/galois_connection): gc magic ([#11114](https://github.com/leanprover-community/mathlib/pull/11114))
see [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.28l.E2.82.81.20S.29.2Emap.20.CF.83.20.E2.89.A4.20l.E2.82.82.20.28S.2Emap.20.E2.87.91.CF.83.29).

### [2021-12-30 14:54:43](https://github.com/leanprover-community/mathlib/commit/f6d0f8d)
refactor(analysis/normed_space/operator_norm): split a proof ([#11112](https://github.com/leanprover-community/mathlib/pull/11112))
Split the proof of `continuous_linear_map.complete_space` into
reusable steps.
Motivated by [#9862](https://github.com/leanprover-community/mathlib/pull/9862)

### [2021-12-30 14:54:42](https://github.com/leanprover-community/mathlib/commit/11de867)
feat(data/fin/interval): add lemmas ([#11102](https://github.com/leanprover-community/mathlib/pull/11102))
From flt-regular.

### [2021-12-30 14:54:41](https://github.com/leanprover-community/mathlib/commit/3398efa)
feat(topology/homeomorph): homeo of continuous equivalence from compact to T2 ([#11072](https://github.com/leanprover-community/mathlib/pull/11072))

### [2021-12-30 14:54:40](https://github.com/leanprover-community/mathlib/commit/7b1c775)
chore(category_theory/adjunction/limits): generalize universe ([#11070](https://github.com/leanprover-community/mathlib/pull/11070))

### [2021-12-30 14:54:39](https://github.com/leanprover-community/mathlib/commit/d49ae12)
feat(topology/homotopy): Add homotopy product ([#10946](https://github.com/leanprover-community/mathlib/pull/10946))
Binary product and pi product of homotopies.

### [2021-12-30 14:14:55](https://github.com/leanprover-community/mathlib/commit/52841fb)
feat(ring_theory/polynomial/cyclotomic/basic): add cyclotomic_expand_eq_cyclotomic_mul ([#11005](https://github.com/leanprover-community/mathlib/pull/11005))
We prove that, if `¬p ∣ n`, then `expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`
- [x] depends on: [#10965](https://github.com/leanprover-community/mathlib/pull/10965)

### [2021-12-30 08:19:12](https://github.com/leanprover-community/mathlib/commit/655c2f0)
chore(topology/algebra/weak_dual_topology): review ([#11141](https://github.com/leanprover-community/mathlib/pull/11141))
* Fix universes in `pi.has_continuous_smul`.
* Add `function.injective.embedding_induced` and
  `weak_dual.coe_fn_embedding`.
* Golf some proofs.
* Review `weak_dual.module` etc instances to ensure, e.g.,
  `module ℝ (weak_dual ℂ E)`.

### [2021-12-30 06:52:10](https://github.com/leanprover-community/mathlib/commit/04071ae)
feat(analysis/inner_product_space/adjoint): define the adjoint for linear maps between finite-dimensional spaces ([#11119](https://github.com/leanprover-community/mathlib/pull/11119))
This PR defines the adjoint of a linear map between finite-dimensional inner product spaces. We use the fact that such maps are always continuous and define it as the adjoint of the corresponding continuous linear map.

### [2021-12-30 06:52:09](https://github.com/leanprover-community/mathlib/commit/9443a7b)
feat(data/nat/prime): min fac of a power ([#11115](https://github.com/leanprover-community/mathlib/pull/11115))

### [2021-12-30 06:52:09](https://github.com/leanprover-community/mathlib/commit/0b6f9eb)
feat(logic/small): The image of a small set is small ([#11108](https://github.com/leanprover-community/mathlib/pull/11108))
A followup to [#11029](https://github.com/leanprover-community/mathlib/pull/11029). Only realized this could be easily proved once that PR was approved.

### [2021-12-30 06:52:08](https://github.com/leanprover-community/mathlib/commit/864a43b)
feat(combinatorics/simple_graph): lemmas describing edge set of subgraphs ([#11087](https://github.com/leanprover-community/mathlib/pull/11087))

### [2021-12-30 06:52:06](https://github.com/leanprover-community/mathlib/commit/8f873b7)
chore(data/nat/prime): move some results ([#11066](https://github.com/leanprover-community/mathlib/pull/11066))
I was expecting there'd be more that could be moved, but it doesn't seem like it.

### [2021-12-30 06:04:19](https://github.com/leanprover-community/mathlib/commit/0c149c9)
feat(analysis/special_functions/log): sum of logs is log of product ([#11106](https://github.com/leanprover-community/mathlib/pull/11106))

### [2021-12-30 02:10:59](https://github.com/leanprover-community/mathlib/commit/23fdf99)
chore(measure_theory/function/lp_space): move `fact`s ([#11107](https://github.com/leanprover-community/mathlib/pull/11107))
Move from `measure_theory/function/lp_space` to `data/real/ennreal` the `fact`s
- `fact_one_le_one_ennreal`
- `fact_one_le_two_ennreal`
- `fact_one_le_top_ennreal`
so that they can be used not just in the measure theory development of `Lp` space but also in the new `lp` spaces.

### [2021-12-30 01:02:33](https://github.com/leanprover-community/mathlib/commit/4f3e99a)
feat(topology/algebra): range of `coe_fn : (M₁ →ₛₗ[σ] M₂) → (M₁ → M₂)` is closed ([#11105](https://github.com/leanprover-community/mathlib/pull/11105))
Motivated by [#9862](https://github.com/leanprover-community/mathlib/pull/9862)

### [2021-12-30 00:20:50](https://github.com/leanprover-community/mathlib/commit/ea95523)
feat(analysis/normed_space/dual): add lemmas, golf ([#11132](https://github.com/leanprover-community/mathlib/pull/11132))
* add `polar_univ`, `is_closed_polar`, `polar_gc`, `polar_Union`,
  `polar_union`, `polar_antitone`, `polar_zero`, `polar_closure`;
* extract `polar_ball_subset_closed_ball_div` and
  `closed_ball_inv_subset_polar_closed_ball` out of the proofs of
  `polar_closed_ball` and `polar_bounded_of_nhds_zero`;
* rename `polar_bounded_of_nhds_zero` to
  `bounded_polar_of_mem_nhds_zero`, use `metric.bounded`;
* use `r⁻¹` instead of `1 / r` in `polar_closed_ball`. This is the
  simp normal form (though we might want to change this in the future).

### [2021-12-29 21:58:43](https://github.com/leanprover-community/mathlib/commit/be17b92)
feat(topology/metric_space/lipschitz): image of a bdd set ([#11134](https://github.com/leanprover-community/mathlib/pull/11134))
Prove that `f '' s` is bounded provided that `f` is Lipschitz
continuous and `s` is bounded.

### [2021-12-29 21:58:42](https://github.com/leanprover-community/mathlib/commit/5bfd924)
chore(analysis/normed_space/basic): add `normed_space.unbounded_univ` ([#11131](https://github.com/leanprover-community/mathlib/pull/11131))
Extract it from the proof of `normed_space.noncompact_space`.

### [2021-12-29 21:58:41](https://github.com/leanprover-community/mathlib/commit/5ac8715)
split(data/finsupp/multiset): Split off `data.finsupp.basic` ([#11110](https://github.com/leanprover-community/mathlib/pull/11110))
This moves `finsupp.to_multiset`, `multiset.to_finsupp` and `finsupp.order_iso_multiset` to a new file `data.finsupp.multiset`.

### [2021-12-29 21:58:40](https://github.com/leanprover-community/mathlib/commit/b8833e9)
chore(data/*): Eliminate `finish` ([#11099](https://github.com/leanprover-community/mathlib/pull/11099))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-29 21:58:39](https://github.com/leanprover-community/mathlib/commit/2a929f2)
feat(algebra/ne_zero): typeclass for n ≠ 0 ([#11033](https://github.com/leanprover-community/mathlib/pull/11033))

### [2021-12-29 21:03:06](https://github.com/leanprover-community/mathlib/commit/dd65894)
chore(*): Eliminate some more instances of `finish` ([#11136](https://github.com/leanprover-community/mathlib/pull/11136))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
This (and the previous series of PRs) eliminates the last few instances of `finish` in the main body of mathlib, leaving only instances in the `scripts`, `test`, `tactic`, and `archive` folders.

### [2021-12-29 21:03:05](https://github.com/leanprover-community/mathlib/commit/d67a1dc)
chore(number_theory/quadratic_reciprocity): Eliminate `finish` ([#11133](https://github.com/leanprover-community/mathlib/pull/11133))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-29 21:03:04](https://github.com/leanprover-community/mathlib/commit/c03dbd1)
chore(algebra/continued_fractions/computation/translations): Eliminate `finish` ([#11130](https://github.com/leanprover-community/mathlib/pull/11130))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-29 21:03:03](https://github.com/leanprover-community/mathlib/commit/90d12bb)
chore(computability/NFA): Eliminate `finish` ([#11103](https://github.com/leanprover-community/mathlib/pull/11103))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-29 20:15:05](https://github.com/leanprover-community/mathlib/commit/6703cdd)
chore([normed/charted]_space): Eliminate `finish` ([#11126](https://github.com/leanprover-community/mathlib/pull/11126))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-29 18:18:57](https://github.com/leanprover-community/mathlib/commit/c25bd03)
feat(algebra/order/field): prove `a / a ≤ 1` ([#11118](https://github.com/leanprover-community/mathlib/pull/11118))

### [2021-12-29 16:12:37](https://github.com/leanprover-community/mathlib/commit/395e275)
chore(topology/metric_space/basic): +1 version of Heine-Borel ([#11127](https://github.com/leanprover-community/mathlib/pull/11127))
* Mark `metric.is_compact_of_closed_bounded` as "Heine-Borel" theorem
  too.
* Add `metric.bounded.is_compact_closure`.

### [2021-12-29 16:12:36](https://github.com/leanprover-community/mathlib/commit/cb37df3)
feat(data/list/pairwise): pairwise repeat ([#11117](https://github.com/leanprover-community/mathlib/pull/11117))

### [2021-12-29 14:53:37](https://github.com/leanprover-community/mathlib/commit/d8b4267)
chore(algebra/big_operators/finprod): Eliminate `finish` ([#10923](https://github.com/leanprover-community/mathlib/pull/10923))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-29 12:26:04](https://github.com/leanprover-community/mathlib/commit/e003d6e)
feat(data/polynomial): more API for roots ([#11081](https://github.com/leanprover-community/mathlib/pull/11081))
`leading_coeff_monic_mul`
`leading_coeff_X_sub_C`
`root_multiplicity_C`
`not_is_root_C`
`roots_smul_nonzero`
`leading_coeff_div_by_monic_X_sub_C`
`roots_eq_zero_iff`
also generalized various statements about `X - C a` to `X + C a` over semirings.

### [2021-12-29 02:26:11](https://github.com/leanprover-community/mathlib/commit/268d1a8)
chore(topology/metric_space/basic): golf, add dot notation ([#11111](https://github.com/leanprover-community/mathlib/pull/11111))
* add `cauchy_seq.bounded_range`;
* golf `metric.bounded_range_of_tendsto`.

### [2021-12-28 20:56:25](https://github.com/leanprover-community/mathlib/commit/a82c481)
feat(data/polynomial/basic): `add_submonoid.closure` of monomials is `⊤` ([#11101](https://github.com/leanprover-community/mathlib/pull/11101))
Use it to golf `polynomial.add_hom_ext`.

### [2021-12-28 20:56:24](https://github.com/leanprover-community/mathlib/commit/134ff7d)
feat(data/option/basic): add `eq_of_mem_of_mem` ([#11098](https://github.com/leanprover-community/mathlib/pull/11098))
If `a : α` belongs to both `o1 o2 : option α` then `o1 = o2`

### [2021-12-28 20:56:23](https://github.com/leanprover-community/mathlib/commit/f11d3ca)
feat(analysis/special_functions/pow): `rpow` as an `order_iso` ([#10831](https://github.com/leanprover-community/mathlib/pull/10831))
Bundles `rpow` into an order isomorphism on `ennreal` when the exponent is a fixed positive real.
- [x] depends on: [#10701](https://github.com/leanprover-community/mathlib/pull/10701)

### [2021-12-28 19:49:35](https://github.com/leanprover-community/mathlib/commit/8d41552)
feat(logic/small): The range of a function from a small type is small ([#11029](https://github.com/leanprover-community/mathlib/pull/11029))
That is, you don't actually need an equivalence to build `small α`, a mere function does the trick.

### [2021-12-28 19:49:34](https://github.com/leanprover-community/mathlib/commit/8d24a1f)
refactor(category_theory/shift): make shifts more flexible ([#10573](https://github.com/leanprover-community/mathlib/pull/10573))

### [2021-12-28 18:16:58](https://github.com/leanprover-community/mathlib/commit/0b80d0c)
chore(ring_theory/*): Eliminate `finish` ([#11100](https://github.com/leanprover-community/mathlib/pull/11100))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-28 15:39:49](https://github.com/leanprover-community/mathlib/commit/143fec6)
chore(linear_algebra/*): Eliminate `finish` ([#11074](https://github.com/leanprover-community/mathlib/pull/11074))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-28 13:53:36](https://github.com/leanprover-community/mathlib/commit/d053d57)
feat(topology): missing lemmas for Kyle ([#11076](https://github.com/leanprover-community/mathlib/pull/11076))
Discussion [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Continuous.20bijective.20from.20compact.20to.20T1.20implies.20homeomorphis) revealed gaps in library. This PR fills those gaps and related ones discovered on the way. It will simplify [#11072](https://github.com/leanprover-community/mathlib/pull/11072). Note that it unprotects `topological_space.nhds_adjoint` and puts it into the root namespace. I guess this was protected because it was seen only as a technical tools to prove properties of `nhds`.

### [2021-12-28 12:15:06](https://github.com/leanprover-community/mathlib/commit/10771d7)
doc(combinatorics/configuration): Make comments into docstrings ([#11097](https://github.com/leanprover-community/mathlib/pull/11097))
These comments should have been docstrings.

### [2021-12-28 12:15:05](https://github.com/leanprover-community/mathlib/commit/d3aa0a4)
feat(data/polynomial/coeff): generalize to coeff_X_add_C_pow ([#11093](https://github.com/leanprover-community/mathlib/pull/11093))
That golfs the proof for `coeff_X_add_one_pow`.

### [2021-12-28 12:15:03](https://github.com/leanprover-community/mathlib/commit/afff1bb)
chore(data/polynomial/eval): golf a proof, add versions ([#11092](https://github.com/leanprover-community/mathlib/pull/11092))
* golf the proof of `polynomial.eval_prod`;
* add versions `polynomial.eval_multiset_prod` and
  `polynomial.eval_list_prod`.

### [2021-12-28 11:35:38](https://github.com/leanprover-community/mathlib/commit/c04a42f)
feat(measure_theory/integral/{interval,circle}_integral): add strict inequalities ([#11061](https://github.com/leanprover-community/mathlib/pull/11061))

### [2021-12-28 09:40:04](https://github.com/leanprover-community/mathlib/commit/f452b38)
feat(data/pi): bit[01]_apply simp lemmas ([#11086](https://github.com/leanprover-community/mathlib/pull/11086))

### [2021-12-28 07:03:21](https://github.com/leanprover-community/mathlib/commit/94bb466)
feat(tactic/fin_cases): document `fin_cases with` and add `fin_cases using` ([#11085](https://github.com/leanprover-community/mathlib/pull/11085))
Closes [#11016](https://github.com/leanprover-community/mathlib/pull/11016)

### [2021-12-28 06:21:09](https://github.com/leanprover-community/mathlib/commit/44f22aa)
feat(ring_theory/power_series/basic): add api for coeffs of shifts ([#11082](https://github.com/leanprover-community/mathlib/pull/11082))
Based on the corresponding API for polynomials

### [2021-12-28 03:25:46](https://github.com/leanprover-community/mathlib/commit/f0ca433)
feat(data/set/finite): finite_or_infinite ([#11084](https://github.com/leanprover-community/mathlib/pull/11084))

### [2021-12-28 03:25:45](https://github.com/leanprover-community/mathlib/commit/612a476)
feat(ring_theory/polynomial/cyclotomic/basic): add cyclotomic_expand_eq_cyclotomic ([#10974](https://github.com/leanprover-community/mathlib/pull/10974))
We prove that, if `p ∣ n`, then `expand R p (cyclotomic n R) = cyclotomic (p * n) R`.
- [x] depends on: [#10965](https://github.com/leanprover-community/mathlib/pull/10965)
- [x] depends on: [#10971](https://github.com/leanprover-community/mathlib/pull/10971)

### [2021-12-28 02:46:14](https://github.com/leanprover-community/mathlib/commit/10ea860)
feat(ring_theory/polynomial/cyclotomic/basic): cyclotomic_prime_mul_X_sub_one ([#11063](https://github.com/leanprover-community/mathlib/pull/11063))
From flt-regular.

### [2021-12-27 18:57:58](https://github.com/leanprover-community/mathlib/commit/294e78e)
feat(algebra/group_with_zero/power): With zero lemmas ([#11051](https://github.com/leanprover-community/mathlib/pull/11051))
This proves the `group_with_zero` variant of some lemmas and moves lemmas from `algebra.group_power.basic` to `algebra.group_with_zero.power`.

### [2021-12-27 18:57:57](https://github.com/leanprover-community/mathlib/commit/1332fe1)
fix(tactic/rcases): more with_desc fail ([#11004](https://github.com/leanprover-community/mathlib/pull/11004))
This causes hovers for definitions using `rcases_patt_parse` to print
weird stuff for the parser description.

### [2021-12-27 16:46:26](https://github.com/leanprover-community/mathlib/commit/0e8cca3)
feat(algebra/big_operators/order): `prod_eq_prod_iff_of_le` ([#11068](https://github.com/leanprover-community/mathlib/pull/11068))
If `f i ≤ g i` for all `i ∈ s`, then `∏ i in s, f i = ∏ i in s, g i` if and only if `f i = g i` for all `i ∈ s`.

### [2021-12-27 16:46:25](https://github.com/leanprover-community/mathlib/commit/6ed17fc)
refactor(combinatorics/configuration): Generalize results ([#11065](https://github.com/leanprover-community/mathlib/pull/11065))
This PR slightly generalizes the results in `configuration.lean` by weakening the definitions of `has_points` and `has_lines`. The new definitions are also more natural, in my opinion.

### [2021-12-27 16:46:24](https://github.com/leanprover-community/mathlib/commit/e1133cc)
chore(order/*): Eliminate `finish` ([#11064](https://github.com/leanprover-community/mathlib/pull/11064))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)
Credit to Ruben Van de Velde who suggested the solution for `eventually_lift'_powerset_eventually`

### [2021-12-27 16:46:23](https://github.com/leanprover-community/mathlib/commit/46566c5)
split(data/list/infix): Split off `data.list.basic` ([#11062](https://github.com/leanprover-community/mathlib/pull/11062))
This moves `list.prefix`, `list.subfix`, `list.infix`, `list.inits`, `list.tails` and `insert` lemmas from `data.list.basic` to a new file `data.list.infix`.

### [2021-12-27 16:46:22](https://github.com/leanprover-community/mathlib/commit/2ecf480)
feat(algebra/group/units): generalize `units.coe_lift` ([#11057](https://github.com/leanprover-community/mathlib/pull/11057))
* Generalize `units.coe_lift` from `group_with_zero` to `monoid`; use condition `is_unit` instead of `≠ 0`.
* Add some missing `@[to_additive]` attrs.

### [2021-12-27 16:46:21](https://github.com/leanprover-community/mathlib/commit/de6f57d)
chore(ring_theory/unique_factorization_domain): Eliminate `finish` ([#11055](https://github.com/leanprover-community/mathlib/pull/11055))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-27 16:46:20](https://github.com/leanprover-community/mathlib/commit/d67c469)
feat(combinatorics/simple_graph/basic): edge deletion ([#11054](https://github.com/leanprover-community/mathlib/pull/11054))
Function to delete edges from a simple graph, and some associated lemmas.
Also defines `sym2.to_rel` as an inverse to `sym2.from_rel`.

### [2021-12-27 16:46:19](https://github.com/leanprover-community/mathlib/commit/ca2c344)
split(data/finsupp/order): Split off `data.finsupp.basic` ([#11045](https://github.com/leanprover-community/mathlib/pull/11045))
This moves all order instances about `finsupp` from `data.finsupp.basic` and `data.finsupp.lattice` to a new file `data.finsupp.order`.
I'm crediting
* Johan for [#1216](https://github.com/leanprover-community/mathlib/pull/1216), [#1244](https://github.com/leanprover-community/mathlib/pull/1244)
* Aaron Anderson for [#3335](https://github.com/leanprover-community/mathlib/pull/3335)

### [2021-12-27 16:46:18](https://github.com/leanprover-community/mathlib/commit/463be88)
feat(algebra/group_with_zero): add zero_mul_eq_const and mul_zero_eq_const ([#11021](https://github.com/leanprover-community/mathlib/pull/11021))
These are to match the corresponding lemmas about unapplied application of multiplication by 1. Like those lemmas, these are not marked simp.

### [2021-12-27 16:46:17](https://github.com/leanprover-community/mathlib/commit/a360354)
feat(algebraic_geometry): Basic open set is empty iff section is zero in reduced schemes. ([#11012](https://github.com/leanprover-community/mathlib/pull/11012))

### [2021-12-27 16:46:16](https://github.com/leanprover-community/mathlib/commit/ae8f08f)
feat(combinatorics/simple_graph/connectivity): more lemmas ([#11010](https://github.com/leanprover-community/mathlib/pull/11010))
This is the second chunk of [#8737](https://github.com/leanprover-community/mathlib/pull/8737), which gives some more lemmas for manipulating the support and edge lists of walks. This also turns `is_trail` back into a structure.

### [2021-12-27 16:46:14](https://github.com/leanprover-community/mathlib/commit/f525f93)
chore(*): Eliminate `finish` ([#10970](https://github.com/leanprover-community/mathlib/pull/10970))
Eliminating the use of `finish` in `data/set/basic`, `order/filter/bases`, and `topology/algebra/valued_field`.

### [2021-12-27 16:46:13](https://github.com/leanprover-community/mathlib/commit/2f3b966)
feat(number_theory/cyclotomic/basic): add is_cyclotomic_extension ([#10849](https://github.com/leanprover-community/mathlib/pull/10849))
We add a class `is_cyclotomic_extension S A B` expressing the fact that `B` is obtained by `A` by adding `n`-th
primitive roots of unity, for all `n ∈ S`, where `S : set ℕ+`, and some basic properties.
We will add more properties of cyclotomic extensions in a future work.
From flt-regular.

### [2021-12-27 14:52:07](https://github.com/leanprover-community/mathlib/commit/002b8d9)
feat(algebra/group_with_zero/basic): mul_{left,right}_eq_self₀ ([#11069](https://github.com/leanprover-community/mathlib/pull/11069))
Defined on `cancel_monoid_with_zero`,
copying the name and proofs from `{left,right)_cancel_monoid`s,

### [2021-12-27 12:07:40](https://github.com/leanprover-community/mathlib/commit/b28734c)
feat(data/sym): Provide API for data.sym ([#11032](https://github.com/leanprover-community/mathlib/pull/11032))

### [2021-12-27 08:24:00](https://github.com/leanprover-community/mathlib/commit/7e0b994)
feat(topology/compact_convergence): define compact convergence ([#10967](https://github.com/leanprover-community/mathlib/pull/10967))
And prove that the topology it induces is the compact-open topology

### [2021-12-26 23:49:34](https://github.com/leanprover-community/mathlib/commit/7c9ce5c)
feat(algebra/order/monoid_lemmas): `mul_eq_mul_iff_eq_and_eq` ([#11056](https://github.com/leanprover-community/mathlib/pull/11056))
If `a ≤ c` and `b ≤ d`, then `a * b = c * d` iff `a = c` and `b = d`.

### [2021-12-26 05:05:27](https://github.com/leanprover-community/mathlib/commit/4f02336)
chore(analysis/complex/circle): minor review ([#11059](https://github.com/leanprover-community/mathlib/pull/11059))
* use implicit arg in `mem_circle_iff_abs`;
* rename `abs_eq_of_mem_circle` to `abs_coe_circle` to reflect the type of LHS;
* add `mem_circle_iff_norm_sq`.

### [2021-12-26 03:49:28](https://github.com/leanprover-community/mathlib/commit/daab3ac)
feat(data/pi/interval): Dependent functions to locally finite orders are locally finite ([#11050](https://github.com/leanprover-community/mathlib/pull/11050))
This provides the locally finite order instance for `Π i, α i` where the `α i` are locally finite.

### [2021-12-26 03:49:27](https://github.com/leanprover-community/mathlib/commit/2e2510e)
chore(logic/small): Some golfing ([#11030](https://github.com/leanprover-community/mathlib/pull/11030))

### [2021-12-26 03:49:26](https://github.com/leanprover-community/mathlib/commit/dd6707c)
feat(measure_theory/integral): a couple of lemmas on integrals and integrability ([#10983](https://github.com/leanprover-community/mathlib/pull/10983))
Adds a couple of congruence lemmas for integrating on intervals and integrability

### [2021-12-26 02:00:29](https://github.com/leanprover-community/mathlib/commit/34e79d6)
chore(data/list/prod): remove an out of date comment ([#11058](https://github.com/leanprover-community/mathlib/pull/11058))
Due to changes in the library structure this comment is no longer relevant.

### [2021-12-26 01:20:52](https://github.com/leanprover-community/mathlib/commit/266d12b)
chore(ring_theory/polynomial/bernstein): use `∑` notation ([#11060](https://github.com/leanprover-community/mathlib/pull/11060))
Also rewrite a proof using `calc` mode

### [2021-12-25 21:05:18](https://github.com/leanprover-community/mathlib/commit/abf9657)
feat(algebraic_geometry): Results about open immersions of schemes. ([#10977](https://github.com/leanprover-community/mathlib/pull/10977))

### [2021-12-25 21:05:17](https://github.com/leanprover-community/mathlib/commit/07b578e)
feat(data/int/basic): add lemma `gcd_greatest` ([#10613](https://github.com/leanprover-community/mathlib/pull/10613))
Proving a uniqueness property for `gcd`.  This is (a version of) Theorem 1.3 in Apostol (1976) Introduction to Analytic Number Theory.

### [2021-12-25 19:14:06](https://github.com/leanprover-community/mathlib/commit/8d426f0)
split(algebra/big_operators/multiset): Split off `data.multiset.basic` ([#11043](https://github.com/leanprover-community/mathlib/pull/11043))
This moves
* `multiset.prod`, `multiset.sum` to `algebra.big_operators.multiset`
* `multiset.join`, `multiset.bind`, `multiset.product`, `multiset.sigma` to `data.multiset.bind`. This is needed as `join` is defined
  using `sum`.
The file was quite messy, so I reorganized `algebra.big_operators.multiset` by increasing typeclass assumptions.
I'm crediting Mario for 0663945f55335e51c2b9b3a0177a84262dd87eaf (`prod`, `sum`, `join`), f9de18397dc1a43817803c2fe5d84b282287ed0d (`bind`, `product`), 16d40d7491d1fe8a733d21e90e516e0dd3f41c5b (`sigma`).

### [2021-12-25 17:20:05](https://github.com/leanprover-community/mathlib/commit/4923cfc)
chore(set_theory/ordinal): Removed redundant argument from `enum_typein` ([#11049](https://github.com/leanprover-community/mathlib/pull/11049))

### [2021-12-25 17:20:04](https://github.com/leanprover-community/mathlib/commit/ad99529)
feat(data/set/basic): Added `range_eq_iff` ([#11044](https://github.com/leanprover-community/mathlib/pull/11044))
This serves as a convenient theorem for proving statements of the form `range f = S`.

### [2021-12-25 16:16:30](https://github.com/leanprover-community/mathlib/commit/914250e)
chore(data/real/ennreal): adjust form of `to_real_pos_iff` ([#11047](https://github.com/leanprover-community/mathlib/pull/11047))
We have a principle (which may not have been crystallized at the time of writing of `data/real/ennreal`) that hypotheses of lemmas should contain the weak form `a ≠ ∞`, while conclusions should report the strong form `a < ∞`, and also the same for  `a ≠ 0`, `0 < a`.
In the case of the existing lemma
```lean
lemma to_real_pos_iff : 0 < a.to_real ↔ (0 < a ∧ a ≠ ∞):=
```
it's not clear whether the RHS of the iff should count as a hypothesis or a conclusion.  So I have rewritten to provide two forms,
```lean
lemma to_real_pos_iff : 0 < a.to_real ↔ (0 < a ∧ a < ∞):=
lemma to_real_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.to_real :=
```
Having both versions available shortens many proofs slightly.

### [2021-12-25 10:29:50](https://github.com/leanprover-community/mathlib/commit/c9f47c9)
chore(data/matrix/block): Eliminate `finish` ([#10948](https://github.com/leanprover-community/mathlib/pull/10948))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-25 10:29:49](https://github.com/leanprover-community/mathlib/commit/0aca706)
feat(measure_theory/integral): define `circle_integral` ([#10906](https://github.com/leanprover-community/mathlib/pull/10906))

### [2021-12-25 05:51:25](https://github.com/leanprover-community/mathlib/commit/ef8005c)
chore(category_theory/limits) : Remove instance requirement  ([#11041](https://github.com/leanprover-community/mathlib/pull/11041))

### [2021-12-25 05:51:24](https://github.com/leanprover-community/mathlib/commit/864a12e)
chore(measure_theory/function/lp_space): use notation for `nnnorm` ([#11039](https://github.com/leanprover-community/mathlib/pull/11039))

### [2021-12-25 05:51:23](https://github.com/leanprover-community/mathlib/commit/0f076d2)
chore(algebra/*): Eliminate `finish` ([#11034](https://github.com/leanprover-community/mathlib/pull/11034))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-25 05:51:22](https://github.com/leanprover-community/mathlib/commit/f9561d4)
feat(ring_theory/localization): The localization at a fg submonoid is of finite type. ([#10990](https://github.com/leanprover-community/mathlib/pull/10990))

### [2021-12-25 05:51:21](https://github.com/leanprover-community/mathlib/commit/5719a02)
feat(data/nat/totient): add totient_mul_prime_div ([#10971](https://github.com/leanprover-community/mathlib/pull/10971))
We add `(p * n).totient = p * n.totient` if `p ∣ n`.

### [2021-12-25 05:51:20](https://github.com/leanprover-community/mathlib/commit/d28b3bd)
feat(combinatorics/configuration): Points and lines inequality ([#10772](https://github.com/leanprover-community/mathlib/pull/10772))
If a nondegenerate configuration has a unique line through any two points, then there are at least as many lines as points.

### [2021-12-25 05:09:25](https://github.com/leanprover-community/mathlib/commit/0dd60ae)
feat(algebraic_geometry): Schemes are sober. ([#11040](https://github.com/leanprover-community/mathlib/pull/11040))
Also renamed things in `topology/sober.lean`.

### [2021-12-25 02:17:30](https://github.com/leanprover-community/mathlib/commit/f80c18b)
feat(measure_theory/measure/haar_lebesgue): Lebesgue measure of the image of a set under a linear map ([#11038](https://github.com/leanprover-community/mathlib/pull/11038))
The image of a set `s` under a linear map `f` has measure equal to `μ s` times the absolute value of the determinant of `f`.

### [2021-12-24 23:10:00](https://github.com/leanprover-community/mathlib/commit/aa66909)
chore(algebraic_geometry): Remove unwanted spaces. ([#11042](https://github.com/leanprover-community/mathlib/pull/11042))

### [2021-12-24 23:09:59](https://github.com/leanprover-community/mathlib/commit/d6ecc14)
feat(data/mv_polynomial): API for mv polynomial.rename ([#10921](https://github.com/leanprover-community/mathlib/pull/10921))
Relation between `rename` and `support`, `degrees` and `degree_of` when `f : σ → τ` is injective.
- I'm not sure if we already have something like `sup_map_multiset`.
- I've stated `sup_map_multiset`using `embedding` but I've used `injective` elsewhere because `mv_polynomial.rename` is written using `injective`.
-  I'm not sure if we should have `map_domain_embedding_of_injective`.

### [2021-12-24 23:09:58](https://github.com/leanprover-community/mathlib/commit/f7038c2)
feat(analysis/inner_product_space/adjoint): show that continuous linear maps on a Hilbert space form a C*-algebra ([#10837](https://github.com/leanprover-community/mathlib/pull/10837))
This PR puts a `cstar_ring` instance on `E →L[𝕜] E`, thereby showing that it forms a C*-algebra.
- [x] depends on: [#10825](https://github.com/leanprover-community/mathlib/pull/10825) [which defines the adjoint]

### [2021-12-24 21:14:13](https://github.com/leanprover-community/mathlib/commit/8a997f3)
feat(combinatorics/configuration): Inequality between `point_count` and `line_count` ([#11036](https://github.com/leanprover-community/mathlib/pull/11036))
An inequality between `point_count` and `line_count`.

### [2021-12-24 21:14:12](https://github.com/leanprover-community/mathlib/commit/8181fe8)
feat(measure_theory/covering/besicovitch): covering a set by balls with controlled measure ([#11035](https://github.com/leanprover-community/mathlib/pull/11035))
We show that, in a real vector space, any set `s` can be covered by balls whose measures add up to at most `μ s + ε`, as a consequence of the Besicovitch covering theorem.

### [2021-12-24 21:14:11](https://github.com/leanprover-community/mathlib/commit/a998db6)
refactor(data/nat/prime): redefine nat.prime as irreducible ([#11031](https://github.com/leanprover-community/mathlib/pull/11031))

### [2021-12-24 21:14:10](https://github.com/leanprover-community/mathlib/commit/3588c3a)
feat(data/multiset/basic): empty_or_exists_mem ([#11023](https://github.com/leanprover-community/mathlib/pull/11023))

### [2021-12-24 21:14:09](https://github.com/leanprover-community/mathlib/commit/404a912)
chore(ring_theory/adjoin/power_basis): add `simps` ([#11018](https://github.com/leanprover-community/mathlib/pull/11018))

### [2021-12-24 21:14:08](https://github.com/leanprover-community/mathlib/commit/d5a3e8c)
feat(ring_theory/derivation): add 3 lemmas ([#10996](https://github.com/leanprover-community/mathlib/pull/10996))
Add `map_smul_of_tower`, `map_coe_nat`, and `map_coe_int`.

### [2021-12-24 21:14:07](https://github.com/leanprover-community/mathlib/commit/c4268a8)
feat(topology,analysis): there exists `y ∈ frontier s` at distance `inf_dist x sᶜ` from `x` ([#10976](https://github.com/leanprover-community/mathlib/pull/10976))

### [2021-12-24 19:23:20](https://github.com/leanprover-community/mathlib/commit/5dac1c0)
chore(topology/*): Eliminate `finish` ([#10991](https://github.com/leanprover-community/mathlib/pull/10991))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-24 16:32:31](https://github.com/leanprover-community/mathlib/commit/35b67fd)
feat(algebra/order/field, data/real/basic): lemmas about `Sup` and `is_lub` ([#11013](https://github.com/leanprover-community/mathlib/pull/11013))
Add a lemma stating that for `f : α → ℝ` with `α` empty, `(⨆ i, f i) = 0`; a lemma stating that in an ordered field `is_lub` scales under multiplication by a nonnegative constant, and some variants.

### [2021-12-24 16:32:30](https://github.com/leanprover-community/mathlib/commit/3377bcc)
feat(analysis/inner_product_space/adjoint): define the adjoint of a continuous linear map between Hilbert spaces ([#10825](https://github.com/leanprover-community/mathlib/pull/10825))
This PR defines the adjoint of an operator `A : E →L[𝕜] F` as the unique operator `adjoint A : F →L[𝕜] E` such that `⟪x, A y⟫ = ⟪adjoint A x, y⟫` for all `x` and `y`. We then use this to put a star algebra structure on `E →L[𝕜] E` with the adjoint as the star operation (while leaving the C* property for a subsequent PR).

### [2021-12-24 15:31:49](https://github.com/leanprover-community/mathlib/commit/99c634c)
feat(analysis/normed_space/spectrum): adds easy direction of Gelfand's formula for the spectral radius ([#10847](https://github.com/leanprover-community/mathlib/pull/10847))
This adds the easy direction (i.e., an inequality) of Gelfand's formula for the spectral radius. Namely, we prove that `spectral_radius 𝕜 a ≤ ∥a ^ (n + 1)∥₊ ^ (1 / (n + 1) : ℝ)` for all `n : ℕ` using the spectral mapping theorem for polynomials.
- [x] depends on: [#10783](https://github.com/leanprover-community/mathlib/pull/10783)

### [2021-12-24 13:57:18](https://github.com/leanprover-community/mathlib/commit/ffbab0d)
chore(group_theory/quotient_group): change injective_ker_lift to ker_lift_injective for naming regularisation ([#11027](https://github.com/leanprover-community/mathlib/pull/11027))
Minor change for naming regularisation.

### [2021-12-24 13:57:17](https://github.com/leanprover-community/mathlib/commit/a0993e4)
feat(combinatorics/configuration): Sum of line counts equals sum of point counts ([#11026](https://github.com/leanprover-community/mathlib/pull/11026))
Counting the set `{(p,l) : P × L | p ∈ l}` in two different ways.

### [2021-12-24 13:57:16](https://github.com/leanprover-community/mathlib/commit/04aeb01)
feat(data/polynomial/ring_division): roots.le_of_dvd ([#11025](https://github.com/leanprover-community/mathlib/pull/11025))

### [2021-12-24 13:57:15](https://github.com/leanprover-community/mathlib/commit/c0e613a)
feat(combinatorics/configuration): `nondegenerate.exists_injective_of_card_le` ([#11019](https://github.com/leanprover-community/mathlib/pull/11019))
If a nondegenerate configuration has at least as many points as lines, then there exists an injective function `f` from lines to points, such that `f l` does not lie on `l`.
This is the key lemma for [#10772](https://github.com/leanprover-community/mathlib/pull/10772). The proof is an application of Hall's marriage theorem.

### [2021-12-24 13:57:14](https://github.com/leanprover-community/mathlib/commit/2c4e6df)
feat(data/real/ennreal): trichotomy lemmas ([#11014](https://github.com/leanprover-community/mathlib/pull/11014))
If there is a case split one performs frequently, it can be useful to provide the case split and the standard data-wrangling one performs after the case split together.  I do this here for the `ennreal` case-split lemma
```lean
protected lemma trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.to_real :=
```
and a couple of variants.

### [2021-12-24 13:57:12](https://github.com/leanprover-community/mathlib/commit/7c7195f)
feat(field_theory/adjoin): lemmas about `inf`s of `intermediate_field`s ([#10997](https://github.com/leanprover-community/mathlib/pull/10997))
This adjusts the data in the `galois_insertion` slightly such that this new lemma is true by `rfl`, to match how we handle this in `subalgebra`. As a result, `top_to_subalgebra` is now refl, but `adjoin_univ` is no longer refl.
This also adds a handful of trivial simp lemmas.

### [2021-12-24 13:57:11](https://github.com/leanprover-community/mathlib/commit/d329d6b)
feat(combinatorics/simple_graph/connectivity): walks, paths, cycles ([#10981](https://github.com/leanprover-community/mathlib/pull/10981))
This is the first chunk of [#8737](https://github.com/leanprover-community/mathlib/pull/8737), which gives a type for walks in a simple graph as well as some basic operations.
It is designed to one day generalize to other types of graphs once there is a more generic framework by swapping out the `G.adj u v` argument from `walk`.

### [2021-12-24 13:57:10](https://github.com/leanprover-community/mathlib/commit/028c161)
feat(topology/is_locally_homeomorph): New file ([#10960](https://github.com/leanprover-community/mathlib/pull/10960))
This PR defines local homeomorphisms.

### [2021-12-24 13:57:09](https://github.com/leanprover-community/mathlib/commit/a0f12bc)
feat(field_theory/adjoin): Supremum of finite dimensional intermediate fields ([#10938](https://github.com/leanprover-community/mathlib/pull/10938))
The supremum of finite dimensional intermediate fields is finite dimensional.

### [2021-12-24 13:57:08](https://github.com/leanprover-community/mathlib/commit/084b1ac)
feat(group_theory/specific_groups/cyclic): |G|=expG ↔ G is cyclic ([#10692](https://github.com/leanprover-community/mathlib/pull/10692))

### [2021-12-24 12:49:44](https://github.com/leanprover-community/mathlib/commit/6c6c7da)
feat(topology/connected): add `inducing.is_preconnected_image` ([#11011](https://github.com/leanprover-community/mathlib/pull/11011))
Generalize the proof of `subtype.preconnected_space` to any `inducing`
map. Also golf the proof of `is_preconnected.subset_right_of_subset_union`.

### [2021-12-24 03:30:38](https://github.com/leanprover-community/mathlib/commit/67cf406)
chore(scripts): update nolints.txt ([#11028](https://github.com/leanprover-community/mathlib/pull/11028))
I am happy to remove some nolints for you!

### [2021-12-24 03:30:37](https://github.com/leanprover-community/mathlib/commit/f846a42)
feat(algebra/pointwise): expand API for multiplication / addition of finsets by copying the corresponding API for sets ([#10600](https://github.com/leanprover-community/mathlib/pull/10600))
From flt-regular, I wanted to be able to add finsets so we add a lot of API to show that the existing definition has good algebraic properties by copying the existing set API.
Where possible I tried to give proofs that use the existing set lemmas and cast the finsets to sets to make it clear that these are essentially the same lemmas.
It would be nice to have a better system for duplicating this API of course, some general versions for set_like or Galois insertions perhaps to unify the theories, but I don't know what that would look like.

### [2021-12-24 02:34:32](https://github.com/leanprover-community/mathlib/commit/7b641cb)
chore(number_theory/primorial): golf some proofs ([#11024](https://github.com/leanprover-community/mathlib/pull/11024))

### [2021-12-24 00:43:12](https://github.com/leanprover-community/mathlib/commit/1dd6080)
feat(ring_theory/derivation): drop unused `is_scalar_tower` ([#10995](https://github.com/leanprover-community/mathlib/pull/10995))

### [2021-12-24 00:43:11](https://github.com/leanprover-community/mathlib/commit/f03447f)
feat(analysis/normed_space): a normed space over a nondiscrete normed field is noncompact ([#10994](https://github.com/leanprover-community/mathlib/pull/10994))
Register this as an instance for a nondiscrete normed field and for a real normed vector space. Also add `is_compact.ne_univ`.

### [2021-12-24 00:43:10](https://github.com/leanprover-community/mathlib/commit/0ac9f83)
feat(analysis/mean_inequalities): Minkowski inequality for infinite sums ([#10984](https://github.com/leanprover-community/mathlib/pull/10984))
A few versions of the Minkowski inequality for `tsum` and `has_sum`.

### [2021-12-24 00:43:09](https://github.com/leanprover-community/mathlib/commit/1a780f6)
chore(topology/metric_space): export `is_compact_closed_ball` ([#10973](https://github.com/leanprover-community/mathlib/pull/10973))

### [2021-12-24 00:43:08](https://github.com/leanprover-community/mathlib/commit/36ba1ac)
feat(algebraic_geometry): Define `open_cover`s of Schemes. ([#10931](https://github.com/leanprover-community/mathlib/pull/10931))

### [2021-12-24 00:43:07](https://github.com/leanprover-community/mathlib/commit/c374a3b)
feat(data/nat/nth): add nth function ([#10707](https://github.com/leanprover-community/mathlib/pull/10707))
Split off from [#9457](https://github.com/leanprover-community/mathlib/pull/9457), introduces `nth` and proves theorems about it.

### [2021-12-23 22:35:58](https://github.com/leanprover-community/mathlib/commit/421b9bb)
feat(algebraic_topology): alternating face map complex of a simplicial object ([#10927](https://github.com/leanprover-community/mathlib/pull/10927))
added the alternating face map complex of a simplicial object in a preadditive category and the natural inclusion of the normalized_Moore_complex

### [2021-12-23 22:35:57](https://github.com/leanprover-community/mathlib/commit/dc57de2)
feat(logic/basic): When a dependent If-Then-Else is not one of its arguments ([#10924](https://github.com/leanprover-community/mathlib/pull/10924))
This is the dependent version of [#10800](https://github.com/leanprover-community/mathlib/pull/10800).

### [2021-12-23 22:35:56](https://github.com/leanprover-community/mathlib/commit/1db0052)
feat(group_theory/submonoid/membership): upgrade definition of pow from a set morphism to a monoid morphism ([#10898](https://github.com/leanprover-community/mathlib/pull/10898))
This comes at no extra cost. All the prerequisite definitions and lemmas were already in mathlib.

### [2021-12-23 22:35:55](https://github.com/leanprover-community/mathlib/commit/68aada0)
feat(algebra/algebra/spectrum): prove the spectral mapping theorem for polynomials ([#10783](https://github.com/leanprover-community/mathlib/pull/10783))
Prove the spectral mapping theorem for polynomials. That is, if `p` is a polynomial and `a : A` where `A` is an algebra over a field `𝕜`, then `p (σ a) ⊆ σ (p a)`. Moreover, if `𝕜` is algebraically closed, then this inclusion is an equality.

### [2021-12-23 22:35:54](https://github.com/leanprover-community/mathlib/commit/720fa8f)
feat(data/rat/basic): API around rat.mk ([#10782](https://github.com/leanprover-community/mathlib/pull/10782))

### [2021-12-23 19:11:42](https://github.com/leanprover-community/mathlib/commit/4ce0d04)
feat(data/real/sqrt): add a few lemmas ([#11003](https://github.com/leanprover-community/mathlib/pull/11003))

### [2021-12-23 19:11:41](https://github.com/leanprover-community/mathlib/commit/694b3f8)
chore(measure_theory): golf a proof ([#11002](https://github.com/leanprover-community/mathlib/pull/11002))

### [2021-12-23 19:11:40](https://github.com/leanprover-community/mathlib/commit/3362b1e)
refactor(analysis/seminorm): Weaken typeclasses ([#10999](https://github.com/leanprover-community/mathlib/pull/10999))
This weakens `normed_field` to the appropriate `normed_whatever`.

### [2021-12-23 19:11:39](https://github.com/leanprover-community/mathlib/commit/cce09a6)
feat(ring_theory/finiteness): prove that a surjective endomorphism of a finite module over a comm ring is injective ([#10944](https://github.com/leanprover-community/mathlib/pull/10944))
Using an approach of Vasconcelos, treating the module as a module over the polynomial ring, with action induced by the endomorphism.
This result was rescued from [#1822](https://github.com/leanprover-community/mathlib/pull/1822).

### [2021-12-23 19:11:38](https://github.com/leanprover-community/mathlib/commit/327bacc)
feat(field_theory/adjoin): `intermediate_field.to_subalgebra` distributes over supremum ([#10937](https://github.com/leanprover-community/mathlib/pull/10937))
This PR proves `(E1 ⊔ E2).to_subalgebra = E1.to_subalgebra ⊔ E2.to_subalgebra`, under the assumption that `E1` and `E2` are finite-dimensional over `F`.

### [2021-12-23 19:11:37](https://github.com/leanprover-community/mathlib/commit/e6f4852)
feat(group_theory/exponent): exponent G = ⨆ g : G, order_of g ([#10767](https://github.com/leanprover-community/mathlib/pull/10767))
Precursor to [#10692](https://github.com/leanprover-community/mathlib/pull/10692).

### [2021-12-23 19:11:36](https://github.com/leanprover-community/mathlib/commit/1107693)
feat(combinatorics/simple_graph/basic): add lemmas about the neighbor set of a vertex in the complement graph ([#7138](https://github.com/leanprover-community/mathlib/pull/7138))
Add lemmas about the neighbor set of a vertex in the complement graph, including a lemma proving that the complement of a regular graph is regular. Part of [#5698](https://github.com/leanprover-community/mathlib/pull/5698) in order to prove facts about strongly regular graphs.

### [2021-12-23 18:32:08](https://github.com/leanprover-community/mathlib/commit/63a0936)
ci(.github/workflows/*): cleanup after upload step ([#11008](https://github.com/leanprover-community/mathlib/pull/11008))
cf. https://github.com/actions/upload-artifact/issues/256

### [2021-12-23 16:33:07](https://github.com/leanprover-community/mathlib/commit/cf34598)
chore(tactic/norm_cast): minor cleanup ([#10993](https://github.com/leanprover-community/mathlib/pull/10993))

### [2021-12-23 16:33:06](https://github.com/leanprover-community/mathlib/commit/1a57c79)
feat(analysis/calculus): assorted simple lemmas ([#10975](https://github.com/leanprover-community/mathlib/pull/10975))
Various lemmas from the formalization of the Cauchy integral formula ([#10000](https://github.com/leanprover-community/mathlib/pull/10000) and some later developments on top of it).
Also add `@[measurability]` attrs to theorems like `measurable_fderiv`.

### [2021-12-23 16:33:04](https://github.com/leanprover-community/mathlib/commit/35ede3d)
chore(algebra/algebra/*): add some `simp` lemmas ([#10969](https://github.com/leanprover-community/mathlib/pull/10969))

### [2021-12-23 16:33:03](https://github.com/leanprover-community/mathlib/commit/7defe7d)
feat(field_theory/separable): add expand_eval and expand_monic ([#10965](https://github.com/leanprover-community/mathlib/pull/10965))
Simple properties of `polynomial.expand`.

### [2021-12-23 16:33:01](https://github.com/leanprover-community/mathlib/commit/2be37b0)
feat(combinatorics/set_family/shadow): Upper shadow of a set family ([#10956](https://github.com/leanprover-community/mathlib/pull/10956))
This defines the upper shadow of `𝒜 : finset (finset α)`, which is the dual of the shadow. Instead of removing each element from each set, we add each element not in each set.

### [2021-12-23 16:33:00](https://github.com/leanprover-community/mathlib/commit/60c2b68)
feat(data/sigma/order): The lexicographical order has a bot/top ([#10905](https://github.com/leanprover-community/mathlib/pull/10905))
Also fix localized instances declarations. They weren't using fully qualified names and I had forgotten `sigma.lex.linear_order`.

### [2021-12-23 16:32:59](https://github.com/leanprover-community/mathlib/commit/87fa060)
feat(combinatorics/configuration): Define `line_count` and `point_count` ([#10884](https://github.com/leanprover-community/mathlib/pull/10884))
Adds definitions for the number of lines through a given point and the number of points through a given line.

### [2021-12-23 16:32:57](https://github.com/leanprover-community/mathlib/commit/bd164c7)
feat(data/polynomial/ring_division): add `polynomial.card_le_degree_of_subset_roots` ([#10824](https://github.com/leanprover-community/mathlib/pull/10824))

### [2021-12-23 16:32:55](https://github.com/leanprover-community/mathlib/commit/ec6d9a7)
feat(topology/algebra/group): definitionally better lattice ([#10792](https://github.com/leanprover-community/mathlib/pull/10792))
This provides `(⊓)`, `⊤`, and `⊥` explicitly such that the associated `to_topological_space` lemmas are definitionally equal.

### [2021-12-23 16:32:53](https://github.com/leanprover-community/mathlib/commit/6e9b011)
feat(linear_algebra/orientation): composing with linear equivs and determinant ([#10737](https://github.com/leanprover-community/mathlib/pull/10737))
Add lemmas that composing an alternating map with a linear equiv using
`comp_linear_map`, or composing a basis with a linear equiv using
`basis.map`, produces the same orientation if and only if the
determinant of that linear equiv is positive.

### [2021-12-23 14:26:41](https://github.com/leanprover-community/mathlib/commit/3499323)
chore(data/vector3): Make linter happy ([#10998](https://github.com/leanprover-community/mathlib/pull/10998))
and clean up a bit.

### [2021-12-23 14:26:40](https://github.com/leanprover-community/mathlib/commit/72b4541)
feat(data/option): simple lemmas about orelse ([#10972](https://github.com/leanprover-community/mathlib/pull/10972))
Some simple lemmas about orelse. Analogous to `bind_eq_some` and friends.

### [2021-12-23 14:26:39](https://github.com/leanprover-community/mathlib/commit/db1788c)
feat(ring_theory/tensor_product): Supremum of finite dimensional subalgebras ([#10922](https://github.com/leanprover-community/mathlib/pull/10922))
The supremum of finite dimensional subalgebras is finite dimensional.

### [2021-12-23 12:54:33](https://github.com/leanprover-community/mathlib/commit/f3b380e)
feat(algebraic_geometry): Prime spectrum is sober. ([#10989](https://github.com/leanprover-community/mathlib/pull/10989))

### [2021-12-23 10:36:41](https://github.com/leanprover-community/mathlib/commit/086469f)
chore(order/*): Change `order_hom` notation ([#10988](https://github.com/leanprover-community/mathlib/pull/10988))
This changes the notation for `order_hom` from `α →ₘ β` to `α →o β` to match `order_embedding` and `order_iso`, which are respectively `α ↪o β` and `α ≃o β`. This also solves the conflict with measurable functions.

### [2021-12-23 10:36:40](https://github.com/leanprover-community/mathlib/commit/03062ea)
feat(ring_theory/integral_closure): The product of the leading coeff and the root is integral. ([#10807](https://github.com/leanprover-community/mathlib/pull/10807))

### [2021-12-23 08:49:38](https://github.com/leanprover-community/mathlib/commit/2cfa052)
feat(data/list/count): countp of true and false ([#10986](https://github.com/leanprover-community/mathlib/pull/10986))

### [2021-12-23 07:22:33](https://github.com/leanprover-community/mathlib/commit/08b13ec)
feat(field_theory/adjoin): add dim_bot, finrank_bot ([#10964](https://github.com/leanprover-community/mathlib/pull/10964))
Added two simp lemmas, showing that the dimension and finrank respectively of bottom intermediate fields are 1.

### [2021-12-23 05:35:04](https://github.com/leanprover-community/mathlib/commit/f4e46fd)
feat(data/list/count): count_le_length ([#10982](https://github.com/leanprover-community/mathlib/pull/10982))

### [2021-12-23 03:43:57](https://github.com/leanprover-community/mathlib/commit/04779a3)
feat(order/complete_boolean_algebra): lemmas about binfi ([#10852](https://github.com/leanprover-community/mathlib/pull/10852))
Adds corresponding `binfi` and `Inf` lemmas for existing `infi` results, especially where `rw` struggles to achieve the same thing alone.

### [2021-12-23 02:02:13](https://github.com/leanprover-community/mathlib/commit/f00007d)
feat(analysis/normed_space/pointwise): more on pointwise operations on sets in normed spaces  ([#10820](https://github.com/leanprover-community/mathlib/pull/10820))
Also move all related results to a new file `analysis/normed_space/pointwise`, to shorten `normed_space/basic` a little bit.

### [2021-12-22 23:07:54](https://github.com/leanprover-community/mathlib/commit/e15e015)
split(data/finset/sigma): Split off `data.finset.basic` ([#10957](https://github.com/leanprover-community/mathlib/pull/10957))
This moves `finset.sigma` to a new file `data.finset.sigma`.
I'm crediting Mario for 16d40d7491d1fe8a733d21e90e516e0dd3f41c5b

### [2021-12-22 23:07:53](https://github.com/leanprover-community/mathlib/commit/3f16409)
feat(data/finset/*): Random lemmas ([#10955](https://github.com/leanprover-community/mathlib/pull/10955))
Prove some `compl` lemmas for `finset`, `(s.erase a).card + 1 = s.card` for `list`, `multiset`, `set`, copy over one more `generalized_boolean_algebra` lemma.

### [2021-12-22 23:07:52](https://github.com/leanprover-community/mathlib/commit/2b9ab3b)
split(data/psigma/order): Split off `order.lexicographic` ([#10953](https://github.com/leanprover-community/mathlib/pull/10953))
This moves all the stuff about `Σ' i, α i` to a new file `data.psigma.order`. This mimics the file organisation of `sigma`.
I'm crediting:
* Scott for [#820](https://github.com/leanprover-community/mathlib/pull/820)
* Minchao for [#914](https://github.com/leanprover-community/mathlib/pull/914)

### [2021-12-22 23:07:51](https://github.com/leanprover-community/mathlib/commit/4315973)
feat(quadratic_form/prod): quadratic forms on product and pi types ([#10939](https://github.com/leanprover-community/mathlib/pull/10939))
In order to provide the `pos_def` members, some new API was needed.

### [2021-12-22 23:07:50](https://github.com/leanprover-community/mathlib/commit/c8f0afc)
feat(group_theory/index): Transitivity of finite relative index. ([#10936](https://github.com/leanprover-community/mathlib/pull/10936))
If `H` has finite relative index in `K`, and `K` has finite relative index in `L`, then `H` has finite relative index in `L`. Golfed from [#9545](https://github.com/leanprover-community/mathlib/pull/9545).

### [2021-12-22 23:07:49](https://github.com/leanprover-community/mathlib/commit/24cefb5)
feat(data/real/ennreal): add monotonicity lemmas for ennreal.to_nnreal ([#10556](https://github.com/leanprover-community/mathlib/pull/10556))
Add four lemmas about monotonicity of `to_nnreal` on extended nonnegative reals, `to_nnreal_mono`, `to_nnreal_le_to_nnreal`, `to_nnreal_strict_mono`, `to_nnreal_lt_to_nnreal` (analogous to `to_real_mono`, `to_real_le_to_nnreal`, `to_real_strict_mono`, `to_real_lt_to_real`).

### [2021-12-22 21:32:02](https://github.com/leanprover-community/mathlib/commit/c5bb320)
refactor(*): Random lemmas and modifications from the shifting refactor. ([#10940](https://github.com/leanprover-community/mathlib/pull/10940))

### [2021-12-22 20:39:43](https://github.com/leanprover-community/mathlib/commit/ee25d58)
feat(linear_algebra/quadratic_form/basic): `linear_map.comp_quadratic_form` ([#10950](https://github.com/leanprover-community/mathlib/pull/10950))
The name is taken to mirror `linear_map.comp_multilinear_map`

### [2021-12-22 20:39:42](https://github.com/leanprover-community/mathlib/commit/b2e881b)
feat(linear_algebra/eigenspace): the eigenvalues of a linear endomorphism are in its spectrum ([#10912](https://github.com/leanprover-community/mathlib/pull/10912))
This PR shows that the eigenvalues of `f : End R M` are in `spectrum R f`.

### [2021-12-22 18:48:37](https://github.com/leanprover-community/mathlib/commit/12ee59f)
feat(data/{finset,multiset}/locally_finite): When an `Icc` is a singleton, cardinality generalization ([#10925](https://github.com/leanprover-community/mathlib/pull/10925))
This proves `Icc a b = {c} ↔ a = c ∧ b = c` for sets and finsets, gets rid of the `a ≤ b` assumption in `card_Ico_eq_card_Icc_sub_one` and friends and proves them for multisets.

### [2021-12-22 18:07:18](https://github.com/leanprover-community/mathlib/commit/da07a99)
feat(ring_theory/tensor_product): Range of `tensor_product.product_map` ([#10882](https://github.com/leanprover-community/mathlib/pull/10882))
This PR proves `(product_map f g).range = f.range ⊔ g.range`.

### [2021-12-22 16:18:16](https://github.com/leanprover-community/mathlib/commit/dda469d)
chore(analysis/normed_space/exponential + logic/function/iterate): fix typos in doc-strings ([#10968](https://github.com/leanprover-community/mathlib/pull/10968))
One `m` was missing in 3 different places.

### [2021-12-22 14:28:32](https://github.com/leanprover-community/mathlib/commit/7ca68f8)
chore(*): fix some doc ([#10966](https://github.com/leanprover-community/mathlib/pull/10966))

### [2021-12-22 12:04:48](https://github.com/leanprover-community/mathlib/commit/af683b1)
feat(topology/tietze_extension): Tietze extension theorem ([#10701](https://github.com/leanprover-community/mathlib/pull/10701))

### [2021-12-21 23:32:37](https://github.com/leanprover-community/mathlib/commit/fc66d88)
refactor(ring_theory/derivation): use weaker TC assumptions ([#10952](https://github.com/leanprover-community/mathlib/pull/10952))
Don't assume `[add_cancel_comm_monoid M]`, add `map_one_eq_zero` as an axiom instead. Add a constructor `derivation.mk'` that deduces `map_one_eq_zero` from `leibniz`.
Also generalize `smul`/`module` instances.

### [2021-12-21 19:23:31](https://github.com/leanprover-community/mathlib/commit/55f575f)
feat(linear_algebra/quadratic_form/complex): all non-degenerate quadratic forms over ℂ are equivalent ([#10951](https://github.com/leanprover-community/mathlib/pull/10951))

### [2021-12-21 18:06:48](https://github.com/leanprover-community/mathlib/commit/b434a0d)
feat(data/nat/prime): `prime.dvd_prod_iff`; golf `mem_list_primes_of_dvd_prod` ([#10624](https://github.com/leanprover-community/mathlib/pull/10624))
Adds a generalisation of `prime.dvd_mul`: prime `p` divides the product of `L : list ℕ` iff it divides some `a ∈ L`.   The `.mp` direction of this lemma is the second part of Theorem 1.9 in Apostol (1976) Introduction to Analytic Number Theory.
Also adds the converse `prime.not_dvd_prod`, and uses `dvd_prod_iff` to golf the proof of `mem_list_primes_of_dvd_prod`.

### [2021-12-21 16:21:11](https://github.com/leanprover-community/mathlib/commit/ca554be)
chore(group_theory/quotient_group): make pow definitionally equal ([#10833](https://github.com/leanprover-community/mathlib/pull/10833))
Motivated by a TODO comment.

### [2021-12-21 16:21:10](https://github.com/leanprover-community/mathlib/commit/cea1988)
feat(data/finsupp/basic): add lemma `disjoint_prod_add` ([#10799](https://github.com/leanprover-community/mathlib/pull/10799))
For disjoint finsupps `f1` and `f2`, and function `g`, the product of the products of `g` over `f1` and `f2` equals the product of `g` over `f1 + f2`

### [2021-12-21 15:17:17](https://github.com/leanprover-community/mathlib/commit/4aa7ac6)
feat(data/mv_polynomial): add `mv_polynomial.linear_map_ext` ([#10945](https://github.com/leanprover-community/mathlib/pull/10945))

### [2021-12-21 12:42:47](https://github.com/leanprover-community/mathlib/commit/8dafccc)
chore(data/nat/digits): Eliminate `finish` ([#10947](https://github.com/leanprover-community/mathlib/pull/10947))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-21 12:42:46](https://github.com/leanprover-community/mathlib/commit/7e48e35)
feat(algebra/module/submodule_lattice, linear_algebra/projection): two lemmas about `is_compl` ([#10709](https://github.com/leanprover-community/mathlib/pull/10709))

### [2021-12-21 12:42:45](https://github.com/leanprover-community/mathlib/commit/a6b2f94)
refactor(linear_algebra/sesquilinear_form): Use similar definition as used in `bilinear_map` ([#10443](https://github.com/leanprover-community/mathlib/pull/10443))
Define sesquilinear forms as `M →ₗ[R] M →ₛₗ[I] R`.

### [2021-12-21 10:53:02](https://github.com/leanprover-community/mathlib/commit/d565373)
feat(order/galois_connection, linear_algebra/basic): `x ∈ R ∙ y` is a transitive relation ([#10943](https://github.com/leanprover-community/mathlib/pull/10943))

### [2021-12-21 07:22:28](https://github.com/leanprover-community/mathlib/commit/2ceda78)
feat(order/monovary): Monovariance of a pair of functions. ([#10890](https://github.com/leanprover-community/mathlib/pull/10890))
`f` monovaries with `g` if `g i < g j → f i ≤ f j`. `f` antivaries with `g` if `g i < g j → f j ≤ f i`.
This is a way to talk about functions being monotone together, without needing an order on the index type.

### [2021-12-21 01:43:24](https://github.com/leanprover-community/mathlib/commit/d145e8e)
chore(combinatorics/simple_graph/basic): Golf and cleanup ([#10942](https://github.com/leanprover-community/mathlib/pull/10942))
This kills a few `simp` and fixes typos.

### [2021-12-20 23:36:13](https://github.com/leanprover-community/mathlib/commit/5ac4cd3)
feat(analysis/special_functions/non_integrable): examples of non-integrable functions ([#10788](https://github.com/leanprover-community/mathlib/pull/10788))

### [2021-12-20 21:49:20](https://github.com/leanprover-community/mathlib/commit/c88943f)
feat(algebra/algebra/subalgebra): define the center of a (unital) algebra ([#10910](https://github.com/leanprover-community/mathlib/pull/10910))

### [2021-12-20 21:49:18](https://github.com/leanprover-community/mathlib/commit/3b6bd99)
chore(data/finset/prod): eliminate `finish` ([#10904](https://github.com/leanprover-community/mathlib/pull/10904))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-20 20:42:22](https://github.com/leanprover-community/mathlib/commit/ed250f7)
feat(topology/[path_]connected): add random [path-]connectedness lemmas ([#10932](https://github.com/leanprover-community/mathlib/pull/10932))
From sphere-eversion

### [2021-12-20 19:47:57](https://github.com/leanprover-community/mathlib/commit/7555ea7)
feat(ring_theory/integral_closure): Supremum of integral subalgebras ([#10935](https://github.com/leanprover-community/mathlib/pull/10935))
The supremum of integral subalgebras is integral.

### [2021-12-20 19:47:56](https://github.com/leanprover-community/mathlib/commit/5dd0ede)
refactor(algebra/category/CommRing/constructions): Squeeze a slow simp ([#10934](https://github.com/leanprover-community/mathlib/pull/10934))
`prod_fan_is_limit` was causing timeouts on CI for another PR, so I squeezed one of the simps.

### [2021-12-20 18:57:10](https://github.com/leanprover-community/mathlib/commit/082665e)
feat(group_theory/index): relindex_eq_zero_of_le_right ([#10928](https://github.com/leanprover-community/mathlib/pull/10928))
If H has infinite index in K, then so does any L ≥ K.

### [2021-12-20 16:29:56](https://github.com/leanprover-community/mathlib/commit/d910e83)
chore(*): ensure all open_locales work without any open namespaces ([#10913](https://github.com/leanprover-community/mathlib/pull/10913))
Inspired by [#10905](https://github.com/leanprover-community/mathlib/pull/10905) we clean up the localized notation in all locales by using the full names of declarations, this should mean that `open_locale blah` should almost never error.
The cases I'm aware of where this doesn't hold still are the locales:
- `witt` which hard codes the variable name `p`, if there is no `p` in context this will fail
- `list.func` and `topological_space` opening `list.func` breaks the notation in `topological_space` due to ``notation as `{` m ` ↦ ` a `}` := list.func.set a as m`` in `list.func` and ``localized "notation `𝓝[≠] ` x:100 := nhds_within x {x}ᶜ" in topological_space``
- likewise for `parser` and `kronecker` due to ``localized "infix ` ⊗ₖ `:100 := matrix.kronecker_map (*)" in kronecker``
But we don't fix these in this PR.
There may be others instances like this too as these errors can depend on the ordering chosen and  I didn't check them all.
A very basic script to check this sort of thing is at https://github.com/leanprover-community/mathlib/tree/alexjbest/check_localized

### [2021-12-20 16:29:55](https://github.com/leanprover-community/mathlib/commit/d14ac1f)
feat(*) : added missing lemma for pointwise smul of  submonoid, add_subgroup, add_submonoid, subsemiring, and semiring. ([#10908](https://github.com/leanprover-community/mathlib/pull/10908))

### [2021-12-20 16:29:54](https://github.com/leanprover-community/mathlib/commit/c2debc4)
refactor(combinatorics/configuration): Implicit arguments for `nondegenerate.eq_or_eq` ([#10885](https://github.com/leanprover-community/mathlib/pull/10885))
The arguments `p₁`, `p₂`, `l₁`, `l₂` can be implicit, since they can be inferred from `p₁ ∈ l₁`, `p₂ ∈ l₁`, `p₁ ∈ l₂`, `p₂ ∈ l₂`.

### [2021-12-20 15:51:29](https://github.com/leanprover-community/mathlib/commit/b9fbef8)
feat(tactic/observe): have a claim proved by library_search under the hood ([#10878](https://github.com/leanprover-community/mathlib/pull/10878))

### [2021-12-20 13:27:04](https://github.com/leanprover-community/mathlib/commit/ab654e5)
feat(topology/sober): Specialization & generic points & sober spaces ([#10914](https://github.com/leanprover-community/mathlib/pull/10914))

### [2021-12-20 13:27:01](https://github.com/leanprover-community/mathlib/commit/e473898)
feat(category_theory/glue_data): Some more API for glue_data ([#10881](https://github.com/leanprover-community/mathlib/pull/10881))

### [2021-12-20 13:26:57](https://github.com/leanprover-community/mathlib/commit/6cfc8d8)
feat(algebraic_geometry/locally_ringed_space): LocallyRingedSpace is cocomplete. ([#10791](https://github.com/leanprover-community/mathlib/pull/10791))

### [2021-12-20 11:53:20](https://github.com/leanprover-community/mathlib/commit/b02e2ea)
feat(group_theory/coset): Embeddings of quotients ([#10901](https://github.com/leanprover-community/mathlib/pull/10901))
If `K ≤ L`, then there is an embedding `K ⧸ (H.subgroup_of K) ↪ L ⧸ (H.subgroup_of L)`. Golfed from [#9545](https://github.com/leanprover-community/mathlib/pull/9545).

### [2021-12-20 11:53:19](https://github.com/leanprover-community/mathlib/commit/b4961da)
feat(analysis/calculus/{f,}deriv): generalize `has_fderiv_at_filter.is_O_sub_rev` ([#10897](https://github.com/leanprover-community/mathlib/pull/10897))
Also add `has_deriv_at.is_O_sub_rev`

### [2021-12-20 10:07:40](https://github.com/leanprover-community/mathlib/commit/bcf20b0)
feat(combinatorics/simple_graph/matching): is_matching iff all degrees = 1 ([#10864](https://github.com/leanprover-community/mathlib/pull/10864))

### [2021-12-20 10:07:38](https://github.com/leanprover-community/mathlib/commit/1929025)
feat(ring_theory/polynomial/cyclotomic): generalize a few results to domains ([#10741](https://github.com/leanprover-community/mathlib/pull/10741))
Primarily for flt-regular

### [2021-12-20 09:01:19](https://github.com/leanprover-community/mathlib/commit/5a79047)
feat(group_theory/index): `relindex_eq_zero_of_le_left` ([#10902](https://github.com/leanprover-community/mathlib/pull/10902))
If `K` has infinite index in `L`, then so does any `H ≤ K`.
The `right`-version is forthcoming.
Making the subgroups explicit in `relindex_mul_relindex` makes rewriting much easier (both in this situation, and in others).

### [2021-12-20 09:01:18](https://github.com/leanprover-community/mathlib/commit/5c05ca2)
feat(ring_theory/integral_closure): `is_field_iff_is_field` ([#10875](https://github.com/leanprover-community/mathlib/pull/10875))
If `R/S` is an integral extension, then `R` is a field if and only if `S` is a field. One direction was already in mathlib, and this PR proves the converse direction.

### [2021-12-20 09:01:16](https://github.com/leanprover-community/mathlib/commit/d5de8ea)
feat(data/polynomial): add some simp attributes and commuted versions of coeff_mul_X_pow ([#10868](https://github.com/leanprover-community/mathlib/pull/10868))
I couldn't find these before and accidentally rewrote them from scratch, I think part of the reason is that I would have expected all of these vesions to be simp lemmas, so we add some more versions of these lemmas and tag everything as simp.
From flt-regular

### [2021-12-20 07:48:27](https://github.com/leanprover-community/mathlib/commit/ade581e)
feat(algebraic_geometry): Open immersions of locally ringed spaces have pullbacks ([#10917](https://github.com/leanprover-community/mathlib/pull/10917))

### [2021-12-20 05:51:57](https://github.com/leanprover-community/mathlib/commit/093aef5)
feat(order/monotone): Functions from/to subsingletons are monotone ([#10903](https://github.com/leanprover-community/mathlib/pull/10903))
A few really trivial results about monotonicity/antitonicity of `f : α → β` where `subsingleton α` or `subsingleton β`.
Also fixes the markdown heading levels in this file

### [2021-12-20 04:47:45](https://github.com/leanprover-community/mathlib/commit/1067556)
refactor(data/polynomial/eval): Golf `hom_eval₂` ([#10920](https://github.com/leanprover-community/mathlib/pull/10920))
Here's a much easier proof of `hom_eval₂`.

### [2021-12-20 01:54:00](https://github.com/leanprover-community/mathlib/commit/c40c701)
feat(docs/references) : Added reference for [#10791](https://github.com/leanprover-community/mathlib/pull/10791) ([#10915](https://github.com/leanprover-community/mathlib/pull/10915))

### [2021-12-20 01:53:58](https://github.com/leanprover-community/mathlib/commit/9cbd828)
feat(data/finset/basic): add image_congr ([#10911](https://github.com/leanprover-community/mathlib/pull/10911))
Add `finset.image_congr`

### [2021-12-20 01:53:57](https://github.com/leanprover-community/mathlib/commit/f7b24fa)
refactor(ring_theory/tensor_product): Speed up slow proofs ([#10883](https://github.com/leanprover-community/mathlib/pull/10883))
`alg_hom_of_linear_map_tensor_product` was causing timeouts, due to many uses of `simp`. This refactor speeds up the proofs.

### [2021-12-20 00:57:04](https://github.com/leanprover-community/mathlib/commit/6ab0f90)
chore(category_theory/filtered): avoid `finish` ([#10918](https://github.com/leanprover-community/mathlib/pull/10918))
Removing uses of finish, as discussed on Zulip (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers).

### [2021-12-19 20:49:08](https://github.com/leanprover-community/mathlib/commit/5dd3537)
feat(algebra/algebra/subalgebra): `subalgebra.map` commutes with supremum ([#10899](https://github.com/leanprover-community/mathlib/pull/10899))
This PR proves `(S ⊔ T).map f = S.map f ⊔ T.map f`.

### [2021-12-19 18:51:43](https://github.com/leanprover-community/mathlib/commit/41ced1c)
feat(ring_theory/tensor_product): The tensor product `A ⊗ B` is generated by tensors `a ⊗ₜ b` ([#10900](https://github.com/leanprover-community/mathlib/pull/10900))
The tensor product is generated by tensors, in terms of `algebra.adjoin`. This is an immediate consequence of `span_tmul_eq_top`.

### [2021-12-19 18:51:42](https://github.com/leanprover-community/mathlib/commit/194bde8)
feat(order/monotone): add `monotone_int_of_le_succ` etc ([#10895](https://github.com/leanprover-community/mathlib/pull/10895))
Also use new lemmas to golf `zpow_strict_mono` and prove `zpow_strict_anti`.

### [2021-12-19 18:51:41](https://github.com/leanprover-community/mathlib/commit/a60ef7c)
feat(data/list/sort): subperm sorted implies sublist ([#10892](https://github.com/leanprover-community/mathlib/pull/10892))
A "sub" version of the lemma directly above.

### [2021-12-19 18:51:40](https://github.com/leanprover-community/mathlib/commit/faee358)
feat (order/lexicographic):  add API lemmas ([#10887](https://github.com/leanprover-community/mathlib/pull/10887))

### [2021-12-19 18:51:40](https://github.com/leanprover-community/mathlib/commit/45ed9de)
chore(order/complete_lattice): eliminate `finish` ([#10876](https://github.com/leanprover-community/mathlib/pull/10876))
Removing uses of finish, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-19 17:06:17](https://github.com/leanprover-community/mathlib/commit/68d9b42)
feat(data/list/count): add lemma `list.count_singleton'` ([#10880](https://github.com/leanprover-community/mathlib/pull/10880))
A generalisation of `count_singleton`: `count a [b] = ite (a = b) 1 0`

### [2021-12-19 12:15:00](https://github.com/leanprover-community/mathlib/commit/9e5cbc1)
feat(algebra/group_power/basic): generalize `zpow_neg_one` to `div_inv_monoid` ([#10894](https://github.com/leanprover-community/mathlib/pull/10894))
Drop `zpow_neg_one₀`

### [2021-12-19 11:16:32](https://github.com/leanprover-community/mathlib/commit/3fc32e3)
feat(analysis/asymptotics): add `is_O.inv_rev`, `is_o.inv_rev` ([#10896](https://github.com/leanprover-community/mathlib/pull/10896))

### [2021-12-19 10:01:23](https://github.com/leanprover-community/mathlib/commit/7222463)
chore(algebra/iterate_hom): use to_additive to fill missing lemmas ([#10886](https://github.com/leanprover-community/mathlib/pull/10886))

### [2021-12-19 02:48:13](https://github.com/leanprover-community/mathlib/commit/a2c3b29)
chore(scripts): update nolints.txt ([#10893](https://github.com/leanprover-community/mathlib/pull/10893))
I am happy to remove some nolints for you!

### [2021-12-18 20:11:21](https://github.com/leanprover-community/mathlib/commit/ee17ab3)
refactor(measure_theory/measure/hausdorff): change Hausdorff measure definition at 0 ([#10859](https://github.com/leanprover-community/mathlib/pull/10859))
Currently, our definition of the Hausdorff measure ensures that it has no atom. This differs from the standard definition of the 0-Hausdorff measure, which is the counting measure -- and this convention is better behaved in many respects, for instance in a `d`-dimensional space the `d`-Hausdorff measure is proportional to Lebesgue measure, while currently we only have this for `d > 0`.
This PR refactors the definition of the Hausdorff measure, to conform to the standard definition.

### [2021-12-18 20:11:20](https://github.com/leanprover-community/mathlib/commit/289ebe5)
chore(category_theory/monoidal/End): Adding API for monoidal functors into `C ⥤ C` ([#10841](https://github.com/leanprover-community/mathlib/pull/10841))
Needed for the shift refactor

### [2021-12-18 20:11:19](https://github.com/leanprover-community/mathlib/commit/9f1b9bc)
feat(linear_algebra/determinant): more properties of the determinant of linear maps ([#10809](https://github.com/leanprover-community/mathlib/pull/10809))

### [2021-12-18 20:11:18](https://github.com/leanprover-community/mathlib/commit/0d47369)
feat(topology/metric/hausdorff_distance): more properties of cthickening ([#10808](https://github.com/leanprover-community/mathlib/pull/10808))

### [2021-12-18 18:09:36](https://github.com/leanprover-community/mathlib/commit/a6179f6)
feat(linear_algebra/affine_space/affine_equiv): isomorphism with the units ([#10798](https://github.com/leanprover-community/mathlib/pull/10798))
This adds:
* `affine_equiv.equiv_units_affine_map` (the main point in this PR)
* `affine_map.linear_hom`
* `affine_equiv.linear_hom`
* `simps` configuration for `affine_equiv`. In order to makes `simp` happy, we adjust the order of the implicit variables to all lemmas in this file, so that they match the order of the arguments to `affine_equiv`.
The new definition can be used to majorly golf `homothety_units_mul_hom`

### [2021-12-18 18:09:35](https://github.com/leanprover-community/mathlib/commit/2c4e66f)
split(data/finset/*): Split `data.finset.card` and `data.finset.fin` off `data.finset.basic` ([#10796](https://github.com/leanprover-community/mathlib/pull/10796))
This moves stuff from `data.finset.basic` in two new files:
* Stuff about `finset.card` goes into `data.finset.card`
* Stuff about `finset.fin_range` and `finset.attach_fin` goes into `data.finset.fin`. I expect this file to be shortlived as I'm planning on killing `fin_range`.
I reordered lemmas thematically and it appeared that there were two pairs of duplicated lemmas:
* `finset.one_lt_card`, `finset.one_lt_card_iff`. They differ only for binder order.
* `finset.card_union_eq`, `finset.card_disjoint_union`. They are literally the same.
All are used so I will clean up in a later PR.
I'm crediting:
* Microsoft Corporation, Leonardo, Jeremy for 8dbee5b1ca9680a22ffe90751654f51d6852d7f0
* Chris Hughes for [#231](https://github.com/leanprover-community/mathlib/pull/231)
* Scott for [#3319](https://github.com/leanprover-community/mathlib/pull/3319)

### [2021-12-18 18:09:34](https://github.com/leanprover-community/mathlib/commit/fa46ef1)
feat(linear_algebra/affine_space/combination): vsub distributivity lemmas ([#10786](https://github.com/leanprover-community/mathlib/pull/10786))
Add lemmas about weighted sums of `-ᵥ` expressions in terms of
`weighted_vsub_of_point`, `weighted_vsub` and `affine_combination`,
with special cases where the points on one side of the subtractions
are constant, and lemmas about those three functions for constant
points used to prove those special cases.
These were suggested by one of the lemmas in [#10632](https://github.com/leanprover-community/mathlib/pull/10632); the lemma
`affine_basis.vsub_eq_coord_smul_sum` is a very specific case, but
showed up that these distributivity lemmas were missing (and should
follow immediately from
`sum_smul_const_vsub_eq_vsub_affine_combination` in this PR).

### [2021-12-18 18:09:32](https://github.com/leanprover-community/mathlib/commit/ecec43a)
feat(algebraic_geometry/open_immersion): Easy results about open immersions. ([#10776](https://github.com/leanprover-community/mathlib/pull/10776))

### [2021-12-18 18:09:31](https://github.com/leanprover-community/mathlib/commit/6e59fbe)
feat(field_theory/splitting_field): generalize some results from field to domain ([#10726](https://github.com/leanprover-community/mathlib/pull/10726))
This PR does a few things generalizing / golfing facts related to polynomials and splitting fields.
- Generalize some results in `data.polynomial.field_division` to division rings
- generalize `C_leading_coeff_mul_prod_multiset_X_sub_C` from a field to a domain
- same for `prod_multiset_X_sub_C_of_monic_of_roots_card_eq`
- add a supporting useful lemma `roots_map_of_injective_card_eq_total_degree` saying that if we already have a full (multi)set of roots over a domain, passing along an injection gives the set of roots of the mapped polynomial
Inspired by needs of flt-regular.

### [2021-12-18 18:09:30](https://github.com/leanprover-community/mathlib/commit/fec084c)
feat(order/cover): The covering relation ([#10676](https://github.com/leanprover-community/mathlib/pull/10676))
This defines `a ⋖ b` to mean that `a < b` and there is no element in between. It is generally useful, but in particular in the context of polytopes and successor orders.

### [2021-12-18 16:15:43](https://github.com/leanprover-community/mathlib/commit/011203d)
feat(algebra/group/inj_surj): _pow definitions for surjective too ([#10832](https://github.com/leanprover-community/mathlib/pull/10832))
We already have these three variants for the injective counterparts, added in [#10152](https://github.com/leanprover-community/mathlib/pull/10152).

### [2021-12-18 16:15:42](https://github.com/leanprover-community/mathlib/commit/5915254)
feat(data/matrix/rank): rank of a matrix ([#10826](https://github.com/leanprover-community/mathlib/pull/10826))

### [2021-12-18 16:15:41](https://github.com/leanprover-community/mathlib/commit/915e2b5)
feat(linear_algebra/orientation): add orientation.map ([#10815](https://github.com/leanprover-community/mathlib/pull/10815))
This also adds `alternating_map.dom_lcongr` following the naming established by `finsupp.dom_lcongr`.

### [2021-12-18 16:15:40](https://github.com/leanprover-community/mathlib/commit/e70faf3)
feat(ring_theory/prinicipal_ideal_domain): Bézout's lemma for PIDs ([#10810](https://github.com/leanprover-community/mathlib/pull/10810))

### [2021-12-18 16:15:39](https://github.com/leanprover-community/mathlib/commit/47c676e)
feat(linear_algebra/affine_space/affine_subspace): affine_subspace.comap ([#10795](https://github.com/leanprover-community/mathlib/pull/10795))
This copies a handful of lemmas from `group_theory/subgroup/basic.lean` to get things started.

### [2021-12-18 16:15:38](https://github.com/leanprover-community/mathlib/commit/00454f2)
feat(topology/algebra/mul_action): add an instance in the presence of `is_central_scalar` ([#10787](https://github.com/leanprover-community/mathlib/pull/10787))

### [2021-12-18 16:15:38](https://github.com/leanprover-community/mathlib/commit/5603398)
feat(ring_theory/local_properties): Being finite / of finite type is local. ([#10775](https://github.com/leanprover-community/mathlib/pull/10775))

### [2021-12-18 16:15:36](https://github.com/leanprover-community/mathlib/commit/c10a872)
feat(order): define a `rel_hom_class` for types of relation-preserving maps ([#10755](https://github.com/leanprover-community/mathlib/pull/10755))
Use the design of [#9888](https://github.com/leanprover-community/mathlib/pull/9888) to define a class `rel_hom_class F r s` for types of maps such that all `f : F` satisfy `r a b → s (f a) (f b)`. Requested by @YaelDillies.
`order_hom_class F α β` is defined as an abbreviation for `rel_hom_class F (≤) (≤)`.

### [2021-12-18 14:23:59](https://github.com/leanprover-community/mathlib/commit/af682d3)
feat(algebraic_geometry): A scheme is reduced iff its stalks are reduced. ([#10879](https://github.com/leanprover-community/mathlib/pull/10879))

### [2021-12-18 14:23:58](https://github.com/leanprover-community/mathlib/commit/65118e5)
feat(analysis/calculus/deriv): add `has_deriv_at.tendsto_punctured_nhds` ([#10877](https://github.com/leanprover-community/mathlib/pull/10877))

### [2021-12-18 14:23:57](https://github.com/leanprover-community/mathlib/commit/0108884)
feat(ring_theory/integral_closure): A subalgebra is contained in the integral closure iff it is integral ([#10874](https://github.com/leanprover-community/mathlib/pull/10874))
A subalgebra is contained in the integral closure iff it is integral.

### [2021-12-18 14:23:56](https://github.com/leanprover-community/mathlib/commit/7de517b)
feat(algebra/algebra/subalgebra): Elements of supremum ([#10872](https://github.com/leanprover-community/mathlib/pull/10872))
Adds a few lemmas about elements of a supremum of subalgebras (essentially copied from the analogous lemmas in `group_theory/subgroup.basic`).

### [2021-12-18 14:23:55](https://github.com/leanprover-community/mathlib/commit/df11302)
feat(algebra/algebra/subalgebra): Lemmas about `alg_hom.range` ([#10871](https://github.com/leanprover-community/mathlib/pull/10871))
This PR adds a few lemmas about `alg_hom.range`.

### [2021-12-18 14:23:54](https://github.com/leanprover-community/mathlib/commit/ac10136)
feat(algebraic_geometry): The underlying topological space of a Scheme is T0 ([#10869](https://github.com/leanprover-community/mathlib/pull/10869))

### [2021-12-18 14:23:53](https://github.com/leanprover-community/mathlib/commit/cb0a6f7)
feat(data/int): various lemmas ([#10862](https://github.com/leanprover-community/mathlib/pull/10862))

### [2021-12-18 14:23:52](https://github.com/leanprover-community/mathlib/commit/04e2f5f)
feat(algebra/group/basic): add a few lemmas ([#10856](https://github.com/leanprover-community/mathlib/pull/10856))
* move `inv_eq_one`, `one_eq_inv`, and `inv_ne_one` up;
* move `div_one'` below `div_eq_one` to golf the proof;
* add `div_eq_inv_iff`;
* golf 2 proofs.

### [2021-12-18 14:23:51](https://github.com/leanprover-community/mathlib/commit/5859ec0)
feat(analysis/normed_space/lattice_ordered_group): prove `order_closed_topology` for `normed_lattice_add_comm_group` ([#10838](https://github.com/leanprover-community/mathlib/pull/10838))

### [2021-12-18 12:49:52](https://github.com/leanprover-community/mathlib/commit/6353d6b)
chore(*): more assorted proof simplifications ([#10863](https://github.com/leanprover-community/mathlib/pull/10863))
A few more random small golfs found by linters

### [2021-12-18 11:01:55](https://github.com/leanprover-community/mathlib/commit/0e995a3)
refactor(*): kill a few uses of finish ([#10860](https://github.com/leanprover-community/mathlib/pull/10860))

### [2021-12-18 10:22:17](https://github.com/leanprover-community/mathlib/commit/ec2f350)
feat(field_theory/intermediate_field): Range of `intermediate_field.val` ([#10873](https://github.com/leanprover-community/mathlib/pull/10873))
The range of the algebra homomorphism `S.val` equals `S.to_subalgebra`.

### [2021-12-18 10:22:16](https://github.com/leanprover-community/mathlib/commit/718ea93)
feat(category_theory): Glue data ([#10436](https://github.com/leanprover-community/mathlib/pull/10436))

### [2021-12-18 06:26:17](https://github.com/leanprover-community/mathlib/commit/a252427)
chore(algebra/algebra/basic): fix instances names to make doc links work ([#10834](https://github.com/leanprover-community/mathlib/pull/10834))
The blank lines avoid sentences being pulled into the bulleted list above them.

### [2021-12-17 23:05:39](https://github.com/leanprover-community/mathlib/commit/2043748)
feat(data/finset/basic): add to_list_insert and to_list_cons ([#10840](https://github.com/leanprover-community/mathlib/pull/10840))

### [2021-12-17 21:25:06](https://github.com/leanprover-community/mathlib/commit/fc09b17)
feat(measure_theory/integral/bochner): prove `set_integral_eq_subtype` ([#10858](https://github.com/leanprover-community/mathlib/pull/10858))
Relate integral w.r.t. `μ.restrict s` and w.r.t. `comap (coe : s → α) μ`.

### [2021-12-17 19:23:39](https://github.com/leanprover-community/mathlib/commit/86493f1)
feat(data/nat): decidable exists le instance ([#10857](https://github.com/leanprover-community/mathlib/pull/10857))
Adds the `le` instance for a corresponding `lt` instance above.

### [2021-12-17 19:23:38](https://github.com/leanprover-community/mathlib/commit/70f4ba0)
feat(algebra/group/hom): generalize `semiconj_by.map` and `commute.map` ([#10854](https://github.com/leanprover-community/mathlib/pull/10854))
This generalizes the results in 2 ways: from `monoid_hom` to `mul_hom` and from `mul_hom` to `mul_hom_class`. For use in [#10783](https://github.com/leanprover-community/mathlib/pull/10783).

### [2021-12-17 19:23:37](https://github.com/leanprover-community/mathlib/commit/0b5f0a2)
feat(data/finset/basic): add ite_subset_union, inter_subset_ite for finset ([#10586](https://github.com/leanprover-community/mathlib/pull/10586))
Just a couple of lemmas to simplify expressions involving ite and union / inter on finsets, note that this is not related to `set.ite`.
From flt-regular.

### [2021-12-17 17:22:44](https://github.com/leanprover-community/mathlib/commit/e5a844e)
feat(data/finsupp/basic): add two versions of `finsupp.mul_prod_erase` ([#10708](https://github.com/leanprover-community/mathlib/pull/10708))
Adding a counterpart for `finsupp` of `finset.mul_prod_erase`

### [2021-12-17 15:21:19](https://github.com/leanprover-community/mathlib/commit/c9fe6d1)
feat(algebra/algebra): instantiate `ring_hom_class` for `alg_hom` ([#10853](https://github.com/leanprover-community/mathlib/pull/10853))
This PR provides a `ring_hom_class` instance for `alg_hom`, to be used in [#10783](https://github.com/leanprover-community/mathlib/pull/10783). I'm not quite finished with my design of morphism classes for linear maps, but I expect this instance will stick around anyway: to avoid a dangerous instance `alg_hom_class F R A B → ring_hom_class F A B` (where the base ring `R` can't be inferred), `alg_hom_class` will probably have to be unbundled and take a `ring_hom_class` as a parameter.

### [2021-12-17 15:21:18](https://github.com/leanprover-community/mathlib/commit/ba24b38)
feat(ring_theory/noetherian): fg_pi ([#10845](https://github.com/leanprover-community/mathlib/pull/10845))

### [2021-12-17 13:26:57](https://github.com/leanprover-community/mathlib/commit/5a59800)
feat(data/set/function): Cancelling composition on a set ([#10803](https://github.com/leanprover-community/mathlib/pull/10803))
A few stupid lemmas

### [2021-12-17 12:31:31](https://github.com/leanprover-community/mathlib/commit/6838233)
feat(combinatorics/configuration): New file ([#10773](https://github.com/leanprover-community/mathlib/pull/10773))
This PR defines abstract configurations of points and lines, and provides some basic definitions. Actual results are in the followup PR.

### [2021-12-17 12:31:30](https://github.com/leanprover-community/mathlib/commit/8743573)
feat(data/nat/count): The count function on naturals ([#9457](https://github.com/leanprover-community/mathlib/pull/9457))
Defines `nat.count` a generic counting function on `ℕ`, computing how many numbers under `k` satisfy a given predicate".
Co-authored by:
Yaël Dillies, yael.dillies@gmail.com
Vladimir Goryachev, gor050299@gmail.com
Kyle Miller, kmill31415@gmail.com
Scott Morrison, scott@tqft.net
Eric Rodriguez, ericrboidi@gmail.com

### [2021-12-17 10:49:01](https://github.com/leanprover-community/mathlib/commit/081cb8a)
chore(algebra/associated): split off dependencies of `big_operators` ([#10848](https://github.com/leanprover-community/mathlib/pull/10848))
This prepares for the replacement of `nat.prime` with `_root_.prime` by reducing the amount of dependencies needed to define `_root_.prime`.
Note that there wouldn't be an import loop without this change, just that `data/nat/prime.lean` would have a bigger amount of imports.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/nat.2Eprime

### [2021-12-17 10:49:00](https://github.com/leanprover-community/mathlib/commit/862a68c)
feat(algebra/big_operators/basic): add finset.prod_to_list ([#10842](https://github.com/leanprover-community/mathlib/pull/10842))

### [2021-12-17 09:42:27](https://github.com/leanprover-community/mathlib/commit/5558fd9)
feat(topology/subset_properties): open/closed sets are locally compact spaces ([#10844](https://github.com/leanprover-community/mathlib/pull/10844))
* add `inducing.image_mem_nhds_within`;
* move `inducing.is_compact_iff` up, use it to prove `embedding.is_compact_iff_is_compact_image`;
* prove `closed_embedding.is_compact_preimage`, use it to prove `closed_embedding.tendsto_cocompact`;
* prove `closed_embedding.locally_compact_space`, `open_embedding.locally_compact_space`;
* specialize to `is_closed.locally_compact_space`, `is_open.locally_compact_space`;
* rename `locally_finite.countable_of_sigma_compact` to `locally_finite.countable_univ`, provide `locally_finite.encodable`.

### [2021-12-17 02:13:44](https://github.com/leanprover-community/mathlib/commit/b100af6)
feat(combinatorics/simple_graph/basic): Incidence set lemmas ([#10839](https://github.com/leanprover-community/mathlib/pull/10839))
Some more `simple_graph.incidence_set` API.

### [2021-12-16 21:36:33](https://github.com/leanprover-community/mathlib/commit/9f9015c)
refactor(category_theory/sites/*): Redefine the category of sheaves. ([#10678](https://github.com/leanprover-community/mathlib/pull/10678))
This refactor redefines sheaves and morphisms of sheaves using bespoke structures.
This is an attempt to make automation more useful when dealing with categories of sheaves.
See the associated [zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Redefining.20Sheaves/near/263308542)

### [2021-12-16 17:52:29](https://github.com/leanprover-community/mathlib/commit/601f2ab)
fix(ring_theory/ideal/basic): remove universe restriction ([#10843](https://github.com/leanprover-community/mathlib/pull/10843))

### [2021-12-16 16:16:13](https://github.com/leanprover-community/mathlib/commit/905d887)
chore(field_theory/ratfunc): to_fraction_ring_ring_equiv ([#10806](https://github.com/leanprover-community/mathlib/pull/10806))
Rename the underlying `ratfunc.aux_equiv` for discoverability.

### [2021-12-16 10:58:20](https://github.com/leanprover-community/mathlib/commit/eeef771)
chore(field_theory/ratfunc): has_scalar in terms of localization ([#10828](https://github.com/leanprover-community/mathlib/pull/10828))
Now that `localization.has_scalar` is general enough, fix a TODO

### [2021-12-16 10:58:19](https://github.com/leanprover-community/mathlib/commit/542471f)
feat(data/set/function): Congruence lemmas for `monotone_on` and friends ([#10817](https://github.com/leanprover-community/mathlib/pull/10817))
Congruence lemmas for `monotone_on`, `antitone_on`, `strict_mono_on`, `strict_anti_on` using `set.eq_on`.
`data.set.function` imports `order.monotone` so we must put them here.

### [2021-12-16 10:58:18](https://github.com/leanprover-community/mathlib/commit/b5b19a6)
feat(ring_theory/local_property): Being reduced is a local property. ([#10734](https://github.com/leanprover-community/mathlib/pull/10734))

### [2021-12-16 09:07:54](https://github.com/leanprover-community/mathlib/commit/68ced9a)
chore(analysis/mean_inequalities_pow): nnreal versions of some ennreal inequalities ([#10836](https://github.com/leanprover-community/mathlib/pull/10836))
Make `nnreal` versions of the existing `ennreal` lemmas
```lean
lemma add_rpow_le_rpow_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) :
  a ^ p + b ^ p ≤ (a + b) ^ p 
```
and similar, introduced by @RemyDegenne in [#5828](https://github.com/leanprover-community/mathlib/pull/5828).  Refactor the proofs of the `ennreal` versions to pass through these.

### [2021-12-16 09:07:53](https://github.com/leanprover-community/mathlib/commit/d212f3e)
feat(measure_theory/measure): new class is_finite_measure_on_compacts ([#10827](https://github.com/leanprover-community/mathlib/pull/10827))
We have currently four independent type classes guaranteeing that a measure of compact sets is finite: `is_locally_finite_measure`, `is_regular_measure`, `is_haar_measure` and `is_add_haar_measure`. Instead of repeting lemmas for all these classes, we introduce a new typeclass saying that a measure is finite on compact sets.

### [2021-12-16 08:30:05](https://github.com/leanprover-community/mathlib/commit/87e2f24)
feat(category_theory/adjunction/evaluation): Evaluation has a left and a right adjoint. ([#10793](https://github.com/leanprover-community/mathlib/pull/10793))

### [2021-12-16 02:33:43](https://github.com/leanprover-community/mathlib/commit/8e4b3b0)
chore(data/polynomial/field_division): beta-reduce ([#10835](https://github.com/leanprover-community/mathlib/pull/10835))

### [2021-12-15 21:49:21](https://github.com/leanprover-community/mathlib/commit/5a835b7)
chore(*): tweaks taken from gh-8889 ([#10829](https://github.com/leanprover-community/mathlib/pull/10829))
That PR is stale, but contained some trivial changes we should just take.

### [2021-12-15 21:49:20](https://github.com/leanprover-community/mathlib/commit/8218a78)
feat(analysis/normed_space/basic): formula for `c • sphere x r` ([#10814](https://github.com/leanprover-community/mathlib/pull/10814))

### [2021-12-15 21:49:19](https://github.com/leanprover-community/mathlib/commit/b82c0d2)
feat(topology/metric_space/isometry): (pre)image of a (closed) ball or a sphere ([#10813](https://github.com/leanprover-community/mathlib/pull/10813))
Also specialize for translations in a normed add torsor.

### [2021-12-15 21:49:18](https://github.com/leanprover-community/mathlib/commit/21c9d3b)
feat(topology/metric_space/hausdorff_distance): add more topological properties API to thickenings ([#10661](https://github.com/leanprover-community/mathlib/pull/10661))
More lemmas about thickenings, especially topological properties, still in preparation for the portmanteau theorem on characterizations of weak convergence of Borel probability measures.

### [2021-12-15 19:58:19](https://github.com/leanprover-community/mathlib/commit/ef69cac)
chore(topology/continuous_function/bounded): remove extra typeclass assumption ([#10823](https://github.com/leanprover-community/mathlib/pull/10823))
Remove `[normed_star_monoid β]` from the typeclass assumptions of `[cstar_ring (α →ᵇ β)]` -- it was doing no harm, since it's implied by the assumption `[cstar_ring β]`, but it's unnecessary.

### [2021-12-15 19:58:18](https://github.com/leanprover-community/mathlib/commit/00c55f5)
feat(algebra/module/linear_map): interaction of linear maps and pointwise operations on sets ([#10821](https://github.com/leanprover-community/mathlib/pull/10821))

### [2021-12-15 19:58:17](https://github.com/leanprover-community/mathlib/commit/dfb78f7)
feat(analysis/special_functions/complex): range of `complex.exp (↑x * I)` ([#10816](https://github.com/leanprover-community/mathlib/pull/10816))

### [2021-12-15 19:58:16](https://github.com/leanprover-community/mathlib/commit/81e58c9)
feat(analysis/mean_inequalities): corollary of Hölder inequality ([#10789](https://github.com/leanprover-community/mathlib/pull/10789))
Several versions of the fact that
```
(∑ i in s, f i) ^ p ≤ (card s) ^ (p - 1) * ∑ i in s, (f i) ^ p
```
for `1 ≤ p`.

### [2021-12-15 19:58:15](https://github.com/leanprover-community/mathlib/commit/026e692)
chore(combinatorics/simple_graph): fix name mixup ([#10785](https://github.com/leanprover-community/mathlib/pull/10785))
Fixes the name mixup from [#10778](https://github.com/leanprover-community/mathlib/pull/10778) and reorders lemmas to make the difference more clear.

### [2021-12-15 19:58:13](https://github.com/leanprover-community/mathlib/commit/204aa7e)
feat(data/int/basic): more int.sign API ([#10781](https://github.com/leanprover-community/mathlib/pull/10781))

### [2021-12-15 19:58:12](https://github.com/leanprover-community/mathlib/commit/75b4e5f)
chore(*): remove edge case assumptions from lemmas  ([#10774](https://github.com/leanprover-community/mathlib/pull/10774))
Remove edge case assumptions from lemmas when the result is easy to prove without the assumption.
We clean up a few lemmas in the library which assume something like `n \ne 0`,  `0 < n`, or `set.nonempty` but where the result is easy to prove by case splitting on this instead and then simplifying.
Removing these unneeded assumptions makes such lemmas easier to apply, and lets us minorly golf a few other proofs along the way.
The main external changes are to remove assumptions to around 30 lemmas, and make some arguments explicit when they were no longer inferable, all other lines are just fixing up the proofs, which shortens some proofs in the process.
I also added a couple of lemmas to help simp in a couple of examples.
The code I used to find these is in the branch https://github.com/leanprover-community/mathlib/tree/alexjbest/simple_edge_cases_linter

### [2021-12-15 19:58:10](https://github.com/leanprover-community/mathlib/commit/3f55e02)
feat(data/{multiset, finset}/basic): add card_mono ([#10771](https://github.com/leanprover-community/mathlib/pull/10771))
Add a `@[mono]` lemma for `finset.card`. Also `multiset.card_mono` as an alias of a preexisting lemma.

### [2021-12-15 19:58:08](https://github.com/leanprover-community/mathlib/commit/a0b6bab)
split(logic/nonempty): Split off `logic.basic` ([#10762](https://github.com/leanprover-community/mathlib/pull/10762))
This moves the lemmas about `nonempty` to a new file `logic.basic`
I'm crediting Johannes for 79483182abffcac3a1ddd7098d47a475e75a5ed2

### [2021-12-15 19:58:07](https://github.com/leanprover-community/mathlib/commit/02cdc81)
refactor(order/sup_indep): Get rid of decidable equality assumption ([#10673](https://github.com/leanprover-community/mathlib/pull/10673))
The `erase` in the definition required a `decidable_eq`. We can make do without it while keeping it functionally the same.

### [2021-12-15 19:58:06](https://github.com/leanprover-community/mathlib/commit/9525f5e)
feat(order/zorn): Added some results about chains ([#10658](https://github.com/leanprover-community/mathlib/pull/10658))
Added `chain_empty`, `chain_subsingleton`, and `chain.max_chain_of_chain`.
The first two of these are immediate yet useful lemmas. The last one is a consequence of Zorn's lemma, which generalizes Hausdorff's maximality principle.

### [2021-12-15 19:58:04](https://github.com/leanprover-community/mathlib/commit/accdb8f)
feat(measure_theory/integral/divergence_theorem): specialize for `f : ℝ → E` and `f g : ℝ × ℝ → E` ([#10616](https://github.com/leanprover-community/mathlib/pull/10616))

### [2021-12-15 18:06:00](https://github.com/leanprover-community/mathlib/commit/4ff9b82)
feat(data/set/lattice): new lemma Union_singleton_eq_range ([#10819](https://github.com/leanprover-community/mathlib/pull/10819))

### [2021-12-15 18:05:59](https://github.com/leanprover-community/mathlib/commit/dc732a3)
feat(logic/basic): When an If-Then-Else is not one of its arguments ([#10800](https://github.com/leanprover-community/mathlib/pull/10800))
Conditions for `ite P a b ≠ a` and `ite P a b ≠ b`.

### [2021-12-15 18:05:58](https://github.com/leanprover-community/mathlib/commit/7130d75)
chore(*): introduce notation for left/right/punctured nhds ([#10694](https://github.com/leanprover-community/mathlib/pull/10694))
New notation:
* `𝓝[≤] x`: the filter `nhds_within x (set.Iic x)` of left-neighborhoods of `x`;
* `𝓝[≥] x`: the filter `nhds_within x (set.Ici x)` of right-neighborhoods of `x`;
* `𝓝[<] x`: the filter `nhds_within x (set.Iio x)` of punctured left-neighborhoods of `x`;
* `𝓝[>] x`: the filter `nhds_within x (set.Ioi x)` of punctured right-neighborhoods of `x`;
* `𝓝[≠] x`: the filter `nhds_within x {x}ᶜ` of punctured neighborhoods of `x`.

### [2021-12-15 18:05:57](https://github.com/leanprover-community/mathlib/commit/6043522)
refactor(order/basic): Change definition of `<` on `α × β` ([#10667](https://github.com/leanprover-community/mathlib/pull/10667))
This prove that `a < b` on `prod` is equivalent to `a.1 < b.1 ∧ a.2 ≤ b.2 ∨ a.1 ≤ b.1 ∧ a.2 < b.2`.

### [2021-12-15 18:05:56](https://github.com/leanprover-community/mathlib/commit/6530769)
doc(algebra/algebra/basic): expand the docstring ([#10221](https://github.com/leanprover-community/mathlib/pull/10221))
This doesn't rule out having a better way to spell "non-unital non-associative algebra" in future, but let's document how it can be done today.
Much of this description is taken from [my talk at CICM's FMM](https://eric-wieser.github.io/fmm-2021/#/algebras).

### [2021-12-15 17:00:14](https://github.com/leanprover-community/mathlib/commit/bb51df3)
chore(computability/regular_expressions): eliminate `finish` ([#10811](https://github.com/leanprover-community/mathlib/pull/10811))
Removing uses of `finish`, as discussed in this Zulip thread (https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20sat.20solvers)

### [2021-12-15 17:00:12](https://github.com/leanprover-community/mathlib/commit/5658241)
feat(ring_theory/localization,group_theory/monoid_localization): other scalar action instances ([#10804](https://github.com/leanprover-community/mathlib/pull/10804))
As requested by @pechersky. With this instance it's possible to state:
```lean
import field_theory.ratfunc
import data.complex.basic
import ring_theory.laurent_series
noncomputable example : ratfunc ℂ ≃ₐ[ℂ] fraction_ring (polynomial ℂ) := sorry
```

### [2021-12-15 17:00:11](https://github.com/leanprover-community/mathlib/commit/930ae46)
chore(analysis/special_functions/pow): remove duplicate lemmas concerning monotonicity of `rpow` ([#10794](https://github.com/leanprover-community/mathlib/pull/10794))
The lemmas `rpow_left_monotone_of_nonneg` and `rpow_left_strict_mono_of_pos` were duplicates of `monotone_rpow_of_nonneg` and `strict_mono_rpow_of_pos`, respectively. The duplicates are removed as well as references to them in mathlib in `measure_theory/function/{continuous_function_dense, lp_space}`

### [2021-12-15 15:40:27](https://github.com/leanprover-community/mathlib/commit/61949af)
doc(linear_algebra/std_basis): update module doc ([#10818](https://github.com/leanprover-community/mathlib/pull/10818))
The old module documentation for this file still referred to the removed old `is_basis`-based definitions. This PR updates the documentation to refer to the new bundled `basis`-based definitions.

### [2021-12-15 12:44:42](https://github.com/leanprover-community/mathlib/commit/9f787c2)
doc(undergrad): Link the affine group ([#10797](https://github.com/leanprover-community/mathlib/pull/10797))
This is the statement `group (P₁ ≃ᵃ[k] P₁)`. Per the "Undergrad TODO trivial targets" wiki page, this should [match wikipedia](https://en.wikipedia.org/wiki/Affine_group), which says:
> In mathematics, the affine group or general affine group of any affine space over a field K is the group of all invertible affine transformations from the space into itself.
I guess you could also ask for the statement that `(P₁ ≃ᵃ[k] P₁) ≃ units (P₁ →ᵃ[k] P₁)`, but I'll PR that separately.

### [2021-12-15 10:36:10](https://github.com/leanprover-community/mathlib/commit/c574e38)
feat(data/finsupp/basic): Add `finsupp.erase_of_not_mem_support` ([#10689](https://github.com/leanprover-community/mathlib/pull/10689))
Analogous to `list.erase_of_not_mem`

### [2021-12-15 09:53:43](https://github.com/leanprover-community/mathlib/commit/03a250a)
chore(data/sym/sym2): Better lemma names ([#10801](https://github.com/leanprover-community/mathlib/pull/10801))
Renames
* `mk_has_mem` to `mk_mem_left`
* `mk_has_mem_right` to `mk_mem_right`. Just doesn't follow the convention.
* `mem_other` to `other` in lemma names. The `mem` is confusing and is only part of the fully qualified name for dot notation to work.
* `sym2.elems_iff_eq` to `mem_and_mem_iff`. `elems` is never used elsewhere. Could also be `mem_mem_iff`.
* `is_diag_iff_eq` to `mk_is_diag_iff`. The form of the argument was ambiguous. Adding `mk` solves it.

### [2021-12-15 07:05:10](https://github.com/leanprover-community/mathlib/commit/40cfdec)
chore(algebra/algebra/basic): alg_equiv.map_smul ([#10805](https://github.com/leanprover-community/mathlib/pull/10805))

### [2021-12-15 06:22:11](https://github.com/leanprover-community/mathlib/commit/8f5031a)
docs(undergrad): more links ([#10790](https://github.com/leanprover-community/mathlib/pull/10790))
The only change to existing declaration links is removing wrong claims of having proving Sylvester's law of inertia (we don't have that the number of 1 and -1 is independent from the basis).

### [2021-12-14 14:14:24](https://github.com/leanprover-community/mathlib/commit/e3eb0eb)
feat(measure_theory/integral/set_to_l1): various properties of the set_to_fun construction ([#10713](https://github.com/leanprover-community/mathlib/pull/10713))

### [2021-12-14 12:57:08](https://github.com/leanprover-community/mathlib/commit/1367c19)
feat(algebraic_geometry): LocallyRingedSpace has coproducts. ([#10665](https://github.com/leanprover-community/mathlib/pull/10665))

### [2021-12-14 11:07:17](https://github.com/leanprover-community/mathlib/commit/9078914)
feat(algebra/group): make `map_[z]pow` generic in `monoid_hom_class` ([#10749](https://github.com/leanprover-community/mathlib/pull/10749))
This PR makes `map_pow` take a `monoid_hom_class` instead of specifically a `monoid_hom`.

### [2021-12-14 09:33:38](https://github.com/leanprover-community/mathlib/commit/f46a7a0)
chore(data/equiv/ring): inv_fun_eq_symm ([#10779](https://github.com/leanprover-community/mathlib/pull/10779))
Like what we have for `alg_equiv`.

### [2021-12-14 09:33:37](https://github.com/leanprover-community/mathlib/commit/6d15ea4)
feat(combinatorics/simple_graph): simp lemmas about spanning coe ([#10778](https://github.com/leanprover-community/mathlib/pull/10778))
A couple of lemmas from [#8737](https://github.com/leanprover-community/mathlib/pull/8737) which don't involve connectivity, plus some extra related results.
cc @kmill

### [2021-12-14 09:33:36](https://github.com/leanprover-community/mathlib/commit/05d8767)
feat(group_theory/order_of_element): additivize ([#10766](https://github.com/leanprover-community/mathlib/pull/10766))

### [2021-12-14 07:40:55](https://github.com/leanprover-community/mathlib/commit/85cb4a8)
chore(measure_theory/decomposition/signed_hahn): Fixed a few typos ([#10777](https://github.com/leanprover-community/mathlib/pull/10777))

### [2021-12-14 07:40:54](https://github.com/leanprover-community/mathlib/commit/f070a69)
move(algebra/order/lattice_group): Move from `algebra.lattice_ordered_group` ([#10763](https://github.com/leanprover-community/mathlib/pull/10763))
Rename `algebra.lattice_ordered_group` in `algebra/order/lattice_group`.

### [2021-12-14 07:40:53](https://github.com/leanprover-community/mathlib/commit/f727e12)
chore(logic/basic): tidy `ite` section and misplaced lemmas ([#10761](https://github.com/leanprover-community/mathlib/pull/10761))
Moves a few lemmas down and use `variables`.

### [2021-12-14 07:40:52](https://github.com/leanprover-community/mathlib/commit/dda8a10)
feat(data/mv_polynomial/basic): add `mv_polynomial.support_sum` ([#10731](https://github.com/leanprover-community/mathlib/pull/10731))

### [2021-12-14 07:40:51](https://github.com/leanprover-community/mathlib/commit/9af43e4)
feat(analysis/inner_product_space/basic): inner product as a (continuous) sesquilinear map ([#10684](https://github.com/leanprover-community/mathlib/pull/10684))
This PR replaces `inner_right (v : E) : E →L[𝕜] 𝕜` (the inner product with a fixed left element as a continuous linear map) by `innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 ` and `innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜 `, which bundle the inner product as a sesquilinear map and as a continuous sesquilinear map respectively.

### [2021-12-14 05:36:16](https://github.com/leanprover-community/mathlib/commit/f3fa5e3)
feat(data/mv_polynomial/variables): add `mv_polynomial.degree_of_zero` ([#10768](https://github.com/leanprover-community/mathlib/pull/10768))

### [2021-12-14 05:36:15](https://github.com/leanprover-community/mathlib/commit/ee78812)
feat(number_theory/padics/padic_norm): lemmas ([#10765](https://github.com/leanprover-community/mathlib/pull/10765))

### [2021-12-14 05:36:14](https://github.com/leanprover-community/mathlib/commit/9b1a832)
feat(data/nat/prime): dvd_of_factors_subperm ([#10764](https://github.com/leanprover-community/mathlib/pull/10764))

### [2021-12-14 05:36:13](https://github.com/leanprover-community/mathlib/commit/d9edeea)
refactor(linear_algebra/orientation): add refl, symm, and trans lemma ([#10753](https://github.com/leanprover-community/mathlib/pull/10753))
This restates the `reflexive`, `symmetric`, and `transitive` lemmas in a form understood by `@[refl]`, `@[symm]`, and `@[trans]`.
As a bonus, these versions also work with dot notation.
I've discarded the original statements, since they're always recoverable via the fields of equivalence_same_ray, and keeping them is just noise.

### [2021-12-14 05:36:12](https://github.com/leanprover-community/mathlib/commit/0000497)
feat(order/basic, order/bounded_order): Generalized `preorder` to `has_lt` ([#10695](https://github.com/leanprover-community/mathlib/pull/10695))
This is a continuation of [#10664](https://github.com/leanprover-community/mathlib/pull/10664).

### [2021-12-14 04:24:23](https://github.com/leanprover-community/mathlib/commit/32c24f1)
chore(set_theory/ordinal_arithmetic): simplified proof of `is_normal.le_self` ([#10770](https://github.com/leanprover-community/mathlib/pull/10770))
Thanks to [#10732](https://github.com/leanprover-community/mathlib/pull/10732), this proof is now a one-liner.

### [2021-12-14 01:29:31](https://github.com/leanprover-community/mathlib/commit/cd462cd)
feat(topology/algebra/*, analysis/normed_space/operator_norm): construct bundled {monoid_hom, linear_map} from limits of such maps ([#10700](https://github.com/leanprover-community/mathlib/pull/10700))
Given a function which is a pointwise limit of {`monoid_hom`, `add_monoid_hom`, `linear_map`} maps, construct a bundled version of the corresponding type with that function as its `to_fun`. Then this construction is used to replace the existing in-proof construction that the continuous linear maps into a banach space is itself complete.

### [2021-12-14 00:37:44](https://github.com/leanprover-community/mathlib/commit/77e5248)
feat(algebra/triv_sq_zero_ext): universal property ([#10754](https://github.com/leanprover-community/mathlib/pull/10754))

### [2021-12-13 23:34:29](https://github.com/leanprover-community/mathlib/commit/c3391c2)
feat(analysis/convex/simplicial_complex): Simplicial complexes ([#9762](https://github.com/leanprover-community/mathlib/pull/9762))
This introduces simplicial complexes in modules.

### [2021-12-13 21:33:22](https://github.com/leanprover-community/mathlib/commit/7181b3a)
chore(order/hom): rearrange definitions of `order_{hom,iso,embedding}` ([#10752](https://github.com/leanprover-community/mathlib/pull/10752))
We symmetrize the locations of `rel_{hom,iso,embedding}` and `order_{hom,iso,embedding}` by putting the `rel_` definitions in `order/rel_iso.lean` and the `order_` definitions in `order/hom/basic.lean`. (`order_hom.lean` needed to be split up to fix an import loop.) Requested by @YaelDillies.
## Moved definitions
 * `order_hom`, `order_iso`, `order_embedding` are now in `order/hom/basic.lean`
 * `order_hom.has_sup` ... `order_hom.complete_lattice` are now in `order/hom/lattice.lean`
## Other changes
Some import cleanup.

### [2021-12-13 19:31:53](https://github.com/leanprover-community/mathlib/commit/b351ca9)
chore(algebra/algebra/tower): golf ext lemma ([#10756](https://github.com/leanprover-community/mathlib/pull/10756))
It turns out that we have both `algebra.ext` and `algebra.algebra_ext`, with slightly different statements.
This changes one to be proved in terms of the other.

### [2021-12-13 19:31:52](https://github.com/leanprover-community/mathlib/commit/3b2cf53)
feat(order/well_founded) Added `strict_mono.id_le_of_wo` ([#10732](https://github.com/leanprover-community/mathlib/pull/10732))
This generalizes `strict_mono.id_le`.

### [2021-12-13 19:31:51](https://github.com/leanprover-community/mathlib/commit/c895ddd)
feat(topology/algebra/group): add homeomorph.prod_units ([#10725](https://github.com/leanprover-community/mathlib/pull/10725))

### [2021-12-13 19:31:50](https://github.com/leanprover-community/mathlib/commit/ad88a83)
feat(probability_theory/martingale): add super/sub-martingales ([#10710](https://github.com/leanprover-community/mathlib/pull/10710))

### [2021-12-13 19:31:49](https://github.com/leanprover-community/mathlib/commit/c7e355d)
feat(algebra/big_operators/finprod): add div lemmas ([#10472](https://github.com/leanprover-community/mathlib/pull/10472))

### [2021-12-13 17:35:09](https://github.com/leanprover-community/mathlib/commit/0c0ee7b)
refactor(data/set/pairwise): Make arguments of `set.pairwise` semi-implicit ([#10740](https://github.com/leanprover-community/mathlib/pull/10740))
The previous definition was `∀ x ∈ s, ∀ y ∈ s, x ≠ y → r x y`. It now is `∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y`.
The explicitness resulted in a lot of useless `_` and general pain using `set.pairwise`, `set.pairwise_disjoint`, `zorn.chain`, `is_antichain`...

### [2021-12-13 15:33:28](https://github.com/leanprover-community/mathlib/commit/ee8de4c)
doc(linear_algebra/finite_dimensional): update doc to new definition ([#10758](https://github.com/leanprover-community/mathlib/pull/10758))
`finite_dimensional` is now (since a couple of months) defined to be `module.finite`. The lines modified by this PR are about the old definition.

### [2021-12-13 15:33:27](https://github.com/leanprover-community/mathlib/commit/108eb0b)
feat(combinatorics/additive/salem_spencer): Salem-Spencer sets and Roth numbers ([#10509](https://github.com/leanprover-community/mathlib/pull/10509))
This defines Salem-Spencer sets and Roth numbers in (additive) monoids.

### [2021-12-13 15:33:26](https://github.com/leanprover-community/mathlib/commit/e174736)
feat(ring_theory/unique_factorization_domain): add count lemmas ([#10475](https://github.com/leanprover-community/mathlib/pull/10475))

### [2021-12-13 15:33:25](https://github.com/leanprover-community/mathlib/commit/efbbb76)
feat(ring_theory/graded_algebra): `homogeneous_element` ([#10118](https://github.com/leanprover-community/mathlib/pull/10118))
This pr is about what `homogeneous_element` of graded ring is.
We need this definition to make the definition of homogeneous ideal more natural, i.e. we can say that a homogeneous ideal is just an ideal spanned by homogeneous elements.

### [2021-12-13 13:35:58](https://github.com/leanprover-community/mathlib/commit/1589c7b)
feat(linear_algebra/determinant): determinant of a linear equivalence as a unit ([#10751](https://github.com/leanprover-community/mathlib/pull/10751))

### [2021-12-13 13:35:57](https://github.com/leanprover-community/mathlib/commit/324a605)
chore(order): rename `preorder_hom` to `order_hom` ([#10750](https://github.com/leanprover-community/mathlib/pull/10750))
For consistency with `order_embedding` and `order_iso`, this PR renames `preorder_hom` to `order_hom`, at the request of @YaelDillies.

### [2021-12-13 13:35:56](https://github.com/leanprover-community/mathlib/commit/35cd7c0)
refactor(set_theory/ordinal_arithmetic) Separate `is_normal.lt_iff` ([#10745](https://github.com/leanprover-community/mathlib/pull/10745))
We split off `is_normal.strict_mono` from `is_normal.lt_iff`. The reasoning is that normal functions are usually defined as being strictly monotone, so this should be a separate theorem.

### [2021-12-13 11:53:34](https://github.com/leanprover-community/mathlib/commit/7697ec6)
feat(analysis/special_function/integrals): integral of `x ^ r`, `r : ℝ`, and `x ^ n`, `n : ℤ` ([#10650](https://github.com/leanprover-community/mathlib/pull/10650))
Also generalize `has_deriv_at.div_const` etc.

### [2021-12-13 09:36:41](https://github.com/leanprover-community/mathlib/commit/779517b)
feat(algebra/order/floor): Floor of `a / n` and other lemmas ([#10748](https://github.com/leanprover-community/mathlib/pull/10748))
A few floor lemmas + one `tsub` lemma

### [2021-12-13 09:36:40](https://github.com/leanprover-community/mathlib/commit/563c364)
chore(topology/maps): golf, use section vars ([#10747](https://github.com/leanprover-community/mathlib/pull/10747))
Also add `quotient_map.is_closed_preimage`

### [2021-12-13 09:36:38](https://github.com/leanprover-community/mathlib/commit/10fb7f9)
feat(archive/imo): IMO 2005 problem 4 (modular arithmetic) ([#10746](https://github.com/leanprover-community/mathlib/pull/10746))

### [2021-12-13 09:36:37](https://github.com/leanprover-community/mathlib/commit/9d73418)
split(data/set/prod): split off `data.set.basic` ([#10739](https://github.com/leanprover-community/mathlib/pull/10739))
This moves `set.prod`, `set.pi` and `set.diagonal` from `data.set.basic` to a new file `data.set.prod`.
I'm crediting
* Mario for `set.prod` from bd013e8089378e8057dc7e93c9eaf2c8ebaf25a2
* Johannes for `set.pi` from da7bbd7fc2c80a785f7992bb7751304f6cafe235
* Patrick for `set.diagonal` from [#3118](https://github.com/leanprover-community/mathlib/pull/3118)

### [2021-12-13 09:36:36](https://github.com/leanprover-community/mathlib/commit/e60899c)
feat(linear_algebra/orientation): inherit an action by `units R` on `module.ray R M` ([#10738](https://github.com/leanprover-community/mathlib/pull/10738))
This action is just the action inherited on the elements of the module under the quotient.
We provide it generally for any group `G` that satisfies the required properties, but are only really interested in `G = units R`.
This PR also provides `module.ray.map`, for sending a ray through a linear equivalence.
This generalization also provides us with `mul_action (M ≃ₗ[R] M) (module.ray R M)`, which might also turn out to be useful.

### [2021-12-13 09:36:35](https://github.com/leanprover-community/mathlib/commit/ea88bd6)
refactor(algebra/triv_sq_zero_ext): generalize and cleanup ([#10729](https://github.com/leanprover-community/mathlib/pull/10729))
This:
* Generalizes typeclass assumptions on many lemmas
* Generalizes and adds missing typeclass instances on `triv_sq_zero_ext`, most notably the algebra structure over a different ring.
* Reorders many of the lemmas in the file to ensure that the right arguments are implicit / explicit

### [2021-12-13 09:36:34](https://github.com/leanprover-community/mathlib/commit/e70e22f)
feat(data/{list, multiset, finset}/range): add range_add ([#10706](https://github.com/leanprover-community/mathlib/pull/10706))
Adds `range_add` lemmas

### [2021-12-13 09:36:32](https://github.com/leanprover-community/mathlib/commit/e4b6b5c)
feat(order/galois_connection): add lt_iff_lt ([#10702](https://github.com/leanprover-community/mathlib/pull/10702))
A lemma for galois connections on linear orders.

### [2021-12-13 09:36:31](https://github.com/leanprover-community/mathlib/commit/29fecae)
feat(data/polynomial/degree/definitions): add pow lemmas ([#10698](https://github.com/leanprover-community/mathlib/pull/10698))
Add lemmas `nat_degree_pow_le` and `coeff_pow_degree_mul_degree`

### [2021-12-13 09:36:30](https://github.com/leanprover-community/mathlib/commit/fb81950)
feat(analysis/convex/basic): lemmas about midpoint and segment ([#10682](https://github.com/leanprover-community/mathlib/pull/10682))

### [2021-12-13 09:36:28](https://github.com/leanprover-community/mathlib/commit/f8171e0)
feat(algebra/graded_monoid): dependent products ([#10674](https://github.com/leanprover-community/mathlib/pull/10674))
This introduces `list.dprod`, which takes the (possibly non-commutative) product of a list of graded elements of type `A i`. This definition primarily exist to allow `graded_monoid.mk` and `direct_sum.of` to be pulled outside a product, such as in the new `graded_monoid.mk_list_dprod` and `direct_sum.of_list_dprod` lemmas added in this PR.

### [2021-12-13 09:36:27](https://github.com/leanprover-community/mathlib/commit/309da20)
feat(*): Random lemmas about adjoin/span. ([#10666](https://github.com/leanprover-community/mathlib/pull/10666))

### [2021-12-13 09:36:26](https://github.com/leanprover-community/mathlib/commit/e19473a)
feat(algebra/pointwise): Multiplying a singleton  ([#10660](https://github.com/leanprover-community/mathlib/pull/10660))
and other lemmas about `finset.product` and singletons.

### [2021-12-13 09:36:25](https://github.com/leanprover-community/mathlib/commit/ec48e3b)
feat(analysis/convex/strict): Strictly convex sets ([#10648](https://github.com/leanprover-community/mathlib/pull/10648))
This defines strictly convex sets.

### [2021-12-13 09:36:23](https://github.com/leanprover-community/mathlib/commit/2d47c1d)
feat(ring_theory/polynomial/cyclotomic/*): ɸₙ(1) = 1 ([#10483](https://github.com/leanprover-community/mathlib/pull/10483))
(for `n` not a prime power)

### [2021-12-13 07:53:00](https://github.com/leanprover-community/mathlib/commit/7cd8adb)
chore(category_theory/limits): Generalize universe for preserving limits ([#10736](https://github.com/leanprover-community/mathlib/pull/10736))

### [2021-12-13 07:52:59](https://github.com/leanprover-community/mathlib/commit/381b954)
feat(algebraic_geometry): An integral scheme is reduced and irreducible ([#10733](https://github.com/leanprover-community/mathlib/pull/10733))

### [2021-12-13 07:52:58](https://github.com/leanprover-community/mathlib/commit/214a80f)
feat(data/mv_polynomial/variables): API for mv_polynomial.degree_of ([#10646](https://github.com/leanprover-community/mathlib/pull/10646))
This PR provides some API for `mv_polynomial.degree_of` for `comm_ring` and `comm_semiring`. I don't know which of these lemmas should be simp lemmas.

### [2021-12-13 07:52:57](https://github.com/leanprover-community/mathlib/commit/8b8f08d)
feat(category_theory/limits): The associativity of pullbacks and pushouts. ([#10619](https://github.com/leanprover-community/mathlib/pull/10619))
Also provides the pasting lemma for pullback (pushout) squares

### [2021-12-13 07:52:56](https://github.com/leanprover-community/mathlib/commit/b6b47ed)
feat(algebraic_geometry/presheafed_space): Open immersions of presheafed spaces has pullbacks. ([#10069](https://github.com/leanprover-community/mathlib/pull/10069))

### [2021-12-13 07:15:39](https://github.com/leanprover-community/mathlib/commit/fcd0f11)
feat(category_theory/flat_functor): Generalize results into algebraic categories. ([#10735](https://github.com/leanprover-community/mathlib/pull/10735))
Also proves that the identity is flat, and compositions of flat functors are flat.

### [2021-12-13 00:12:14](https://github.com/leanprover-community/mathlib/commit/0690542)
feat(data/nat/prime): add `prime.dvd_mul_of_dvd_ne` ([#10727](https://github.com/leanprover-community/mathlib/pull/10727))

### [2021-12-13 00:12:12](https://github.com/leanprover-community/mathlib/commit/0c248b7)
feat(algebra/{group,ring}/opposite): `{ring,monoid}_hom.from_opposite` ([#10723](https://github.com/leanprover-community/mathlib/pull/10723))
We already have the `to_opposite` versions.

### [2021-12-13 00:12:11](https://github.com/leanprover-community/mathlib/commit/4b07949)
chore(algebra/module/submodule): missing is_central_scalar instance ([#10720](https://github.com/leanprover-community/mathlib/pull/10720))

### [2021-12-13 00:12:10](https://github.com/leanprover-community/mathlib/commit/41def6a)
feat(algebra/tropical/big_operators): sum, prod, Inf ([#10544](https://github.com/leanprover-community/mathlib/pull/10544))

### [2021-12-12 23:25:29](https://github.com/leanprover-community/mathlib/commit/b9f2440)
chore(linear_algebra/orientation): golf a proof ([#10742](https://github.com/leanprover-community/mathlib/pull/10742))

### [2021-12-12 21:34:23](https://github.com/leanprover-community/mathlib/commit/19dd4be)
chore(tactic/reserved_notation): change precedence of sup and inf ([#10623](https://github.com/leanprover-community/mathlib/pull/10623))
Put the precedence of `⊔` and `⊓` at 68 and 69 respectively, which is above `+` (65), `∑` and `∏` (67), and below `*` (70). This makes sure that inf and sup behave in the same way in expressions where arithmetic operations appear (which was not the case before).
Discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/inf.20and.20sup.20don't.20bind.20similarly

### [2021-12-12 15:54:29](https://github.com/leanprover-community/mathlib/commit/61b0f41)
refactor(data/{mv_,}polynomial): lemmas about `adjoin` ([#10670](https://github.com/leanprover-community/mathlib/pull/10670))
Prove `adjoin {X} = ⊤` and `adjoin (range X) = ⊤` for `polynomial`s
and `mv_polynomial`s much earlier and use these equalities to golf
some proofs.
Also drop some `comm_` in typeclass assumptions.

### [2021-12-12 06:54:07](https://github.com/leanprover-community/mathlib/commit/e68fcf8)
move(data/bool/*): Move `bool` files in one folder ([#10718](https://github.com/leanprover-community/mathlib/pull/10718))
* renames `data.bool` to `data.bool.basic`
* renames `data.set.bool` to `data.bool.set`
* splits `data.bool.all_any` off `data.list.basic`

### [2021-12-12 01:37:53](https://github.com/leanprover-community/mathlib/commit/50e318e)
feat(algebra/order/ring): pos_iff_pos_of_mul_pos, neg_iff_neg_of_mul_pos ([#10634](https://github.com/leanprover-community/mathlib/pull/10634))
Add four lemmas, deducing equivalence of `a` and `b` being positive or
negative from such a hypothesis for their product, that don't currently
seem to be present.

### [2021-12-11 21:21:53](https://github.com/leanprover-community/mathlib/commit/f361373)
chore(order/boolean_algebra): add `compl_sdiff` ([#10722](https://github.com/leanprover-community/mathlib/pull/10722))
Also mark `sdiff_compl` and `top_sdiff` as `@[simp]`.

### [2021-12-11 21:21:52](https://github.com/leanprover-community/mathlib/commit/f9fff7c)
feat(measure_theory): integral is mono in measure ([#10721](https://github.com/leanprover-community/mathlib/pull/10721))
* Bochner integral of a nonnegative function is monotone in measure;
* set integral of a nonnegative function is monotone in set (generalize existing lemma);
* interval integral of a nonnegative function is monotone in interval.

### [2021-12-11 21:21:51](https://github.com/leanprover-community/mathlib/commit/cc5ff8c)
feat(group_theory/submonoid): The submonoid of left inverses of a submonoid ([#10679](https://github.com/leanprover-community/mathlib/pull/10679))

### [2021-12-11 21:21:50](https://github.com/leanprover-community/mathlib/commit/1c2b742)
feat(ring_theory/polynomial/cyclotomic/eval): `cyclotomic_pos` ([#10482](https://github.com/leanprover-community/mathlib/pull/10482))

### [2021-12-11 19:31:57](https://github.com/leanprover-community/mathlib/commit/f068b9d)
refactor(algebra/group/basic): Migrate add_comm_group section into comm_group section ([#10565](https://github.com/leanprover-community/mathlib/pull/10565))
Currently mathlib has a rich set of lemmas connecting the addition, subtraction and negation additive commutative group operations, but a far thinner collection of results for multiplication, division and inverse multiplicative commutative group operations, despite the fact that the former can be generated easily from the latter via to_additive.
This PR refactors the additive results in the `add_comm_group` section as the equivalent multiplicative results in the `comm_group` section and then recovers the additive results via to_additive. There is a complication in that unfortunately the multiplicative forms of the names of some of the `add_comm_group` lemmas collide with existing names in `group_with_zero`. I have worked around this by appending an apostrophe to the name and then manually overriding the names generated by to_additive. In a few cases, names with `1...n` appended apostrophes already existed. In these cases I have appended `n+1` apostrophes.
Previous discussion
The `add_group` section was previously tackled in [#10532](https://github.com/leanprover-community/mathlib/pull/10532).

### [2021-12-11 13:03:44](https://github.com/leanprover-community/mathlib/commit/294753e)
Fix comment typo ([#10715](https://github.com/leanprover-community/mathlib/pull/10715))

### [2021-12-11 11:06:55](https://github.com/leanprover-community/mathlib/commit/9741766)
feat(analysis/normed_space): normed space is homeomorphic to the unit ball ([#10690](https://github.com/leanprover-community/mathlib/pull/10690))

### [2021-12-11 09:33:55](https://github.com/leanprover-community/mathlib/commit/08d30d6)
chore(algebra/pointwise): Better `variables` management ([#10686](https://github.com/leanprover-community/mathlib/pull/10686))
Moves a few variables from lemma statements to `variables`.

### [2021-12-11 04:23:13](https://github.com/leanprover-community/mathlib/commit/d856bf9)
feat(ring_theory/localization): Clearing denominators ([#10668](https://github.com/leanprover-community/mathlib/pull/10668))

### [2021-12-10 23:48:44](https://github.com/leanprover-community/mathlib/commit/0b87b0a)
chore(algebra/group_with_zero/defs: Rename `comm_cancel_monoid_with_zero` to `cancel_comm_monoid_with_zero` ([#10669](https://github.com/leanprover-community/mathlib/pull/10669))
We currently have `cancel_comm_monoid` but `comm_cancel_monoid_with_zero`. This renames the latter to follow the former.
Replaced `comm_cancel_` by `cancel_comm_` everywhere.

### [2021-12-10 21:59:37](https://github.com/leanprover-community/mathlib/commit/52c2f74)
docs(topology/homotopy): add namespace in docstring to fix links ([#10711](https://github.com/leanprover-community/mathlib/pull/10711))
Currently all the occurences of `homotopy` in the docs link to `algebra/homology/homotopy`.

### [2021-12-10 21:59:36](https://github.com/leanprover-community/mathlib/commit/a12fc70)
feat(logic/function/basic): surjective function is an epimorphism ([#10691](https://github.com/leanprover-community/mathlib/pull/10691))
* Move proofs about `surjective`/`injective` and `epi`/`mono` to `logic.function.basic` (formulated in terms of injectivity of composition), make them universe polymorphic.
* drop `forall_iff_forall_surj`, use `function.surjective.forall` instead.

### [2021-12-10 20:23:28](https://github.com/leanprover-community/mathlib/commit/3e1d4d3)
feat(algebra/gcd_monoid): `associates` lemmas ([#10705](https://github.com/leanprover-community/mathlib/pull/10705))

### [2021-12-10 19:12:57](https://github.com/leanprover-community/mathlib/commit/b7ac833)
feat(ring_theory/discriminant): add the discriminant of a family of vectors ([#10350](https://github.com/leanprover-community/mathlib/pull/10350))
We add the definition and some basic results about the discriminant.
From FLT-regular.
- [x] depends on: [#10657](https://github.com/leanprover-community/mathlib/pull/10657)

### [2021-12-10 17:07:55](https://github.com/leanprover-community/mathlib/commit/71e9f90)
feat(order/basic): Slightly generalized `densely_ordered` ([#10664](https://github.com/leanprover-community/mathlib/pull/10664))
Changed `[preorder α]` to `[has_lt α]`.

### [2021-12-10 15:16:09](https://github.com/leanprover-community/mathlib/commit/12e18e8)
feat(data/nat/gcd): coprime add mul lemmas ([#10588](https://github.com/leanprover-community/mathlib/pull/10588))
Adds `coprime m (n + k * m) ↔ coprime m n` for nats, (and permutations thereof).

### [2021-12-10 15:16:08](https://github.com/leanprover-community/mathlib/commit/18ce3a8)
feat(group_theory/group_action/defs): add a typeclass to show that an action is central (aka symmetric) ([#10543](https://github.com/leanprover-community/mathlib/pull/10543))
This adds a new `is_central_scalar` typeclass to indicate that `op m • a = m • a` (or rather, to indicate that a type has the same right and left scalar action on another type).
The main instance for this is `comm_semigroup.is_central_scalar`, for when `m • a = m * a` and `op m • a = a * m`, and then all the other instances follow transitively when `has_scalar R (f M)` is derived from `has_scalar R M`:
* `prod`
* `pi`
* `ulift`
* `finsupp`
* `dfinsupp`
* `monoid_algebra`
* `add_monoid_algebra`
* `polynomial`
* `mv_polynomial`
* `matrix`
* `add_monoid_hom`
* `linear_map`
* `complex`
* `pointwise` instances on:
  * `set`
  * `submonoid`
  * `add_submonoid`
  * `subgroup`
  * `add_subgroup`
  * `subsemiring`
  * `subring`
  * `submodule`

### [2021-12-10 13:26:26](https://github.com/leanprover-community/mathlib/commit/94d51b9)
chore(algebraic_geometry/presheafed_space): Make `has_colimits` work faster ([#10703](https://github.com/leanprover-community/mathlib/pull/10703))

### [2021-12-10 13:26:25](https://github.com/leanprover-community/mathlib/commit/c29b706)
feat(data/int/gcd): another version of Euclid's lemma ([#10622](https://github.com/leanprover-community/mathlib/pull/10622))
We already have something described as "Euclid's lemma" in `ring_theory/unique_factorization_domain`, but not this specific statement of the lemma.
This is Theorem 1.5 in Apostol (1976) Introduction to Analytic Number Theory

### [2021-12-10 13:26:24](https://github.com/leanprover-community/mathlib/commit/4471de6)
feat(order/lattice): define a lattice structure using an injective map to another lattice ([#10615](https://github.com/leanprover-community/mathlib/pull/10615))
This is done similarly to `function.injective.group` etc.

### [2021-12-10 13:26:23](https://github.com/leanprover-community/mathlib/commit/ebbb991)
feat(ring_theory/principal_ideal_domain): add some corollaries about is_coprime ([#10601](https://github.com/leanprover-community/mathlib/pull/10601))

### [2021-12-10 13:26:22](https://github.com/leanprover-community/mathlib/commit/46ac3c4)
feat(*): introduce classes for types of homomorphism ([#9888](https://github.com/leanprover-community/mathlib/pull/9888))
This PR is the main proof-of-concept in my plan to use typeclasses to reduce duplication surrounding `hom` classes. Essentially, I want to take each type of bundled homs, such as `monoid_hom`, and add a class `monoid_hom_class` which has an instance for each *type* extending `monoid_hom`. Declarations that now take a parameter of the specific type `monoid_hom M N` can instead take a more general `{F : Type*} [monoid_hom_class F M N] (f : F)`; this means we don't need to duplicate e.g. `monoid_hom.map_prod` to `ring_hom.map_prod`, `mul_equiv.map_prod`, `ring_equiv.map_prod`, or `monoid_hom.map_div` to `ring_hom.map_div`, `mul_equiv.map_div`, `ring_equiv.map_div`, ...
Basically, instead of having `O(n * k)` declarations for `n` types of homs and `k` lemmas, following the plan we only need `O(n + k)`.
## Overview
 * Change `has_coe_to_fun` to include the type of the function as a parameter (rather than a field of the structure) (**done** as part of [#7033](https://github.com/leanprover-community/mathlib/pull/7033))
 * Define a class `fun_like`, analogous to `set_like`, for types of bundled function + proof (**done** in [#10286](https://github.com/leanprover-community/mathlib/pull/10286))
 * Extend `fun_like` for each `foo_hom` to create a `foo_hom_class` (**done** in this PR for `ring_hom` and its ancestors, **todo** in follow-up for the rest)
 * Change parameters of type `foo_hom A B` to take `{F : Type*} [foo_hom_class F A B] (f : F)` instead (**done** in this PR for `map_{add,zero,mul,one,sub,div}`, **todo** in follow-up for remaining declarations)
## API changes
Lemmas matching `*_hom.map_{add,zero,mul,one,sub,div}` are deprecated. Use the new `simp` lemmas called simply `map_add`, `map_zero`, ...
Namespaced lemmas of the form `map_{add,zero,mul,one,sub,div}` are now protected. This includes e.g. `polynomial.map_add` and `multiset.map_add`, which involve `polynomial.map` and `multiset.map` respectively. In fact, it should be possible to turn those `map` definitions into bundled maps, so we don't even need to worry about the name change.
## New classes
 * `zero_hom_class`, `one_hom_class` defines `map_zero`, `map_one`
 * `add_hom_class`, `mul_hom_class` defines `map_add`, `map_mul`
 * `add_monoid_hom_class`, `monoid_hom_class` extends `{zero,one}_hom_class`, `{add,mul}_hom_class`
 * `monoid_with_zero_hom_class` extends `monoid_hom_class` and `zero_hom_class`
 * `ring_hom_class` extends `monoid_hom_class`, `add_monoid_hom_class` and `monoid_with_zero_hom_class`
## Classes still to be implemented
Some of the core algebraic homomorphisms are still missing their corresponding classes:
 * `mul_action_hom_class` defines `map_smul`
 * `distrib_mul_action_hom_class`, `mul_semiring_action_hom_class` extends the above
 * `linear_map_class` extends `add_hom_class` and defines `map_smulₛₗ`
 * `alg_hom_class` extends `ring_hom_class` and defines `commutes`
We could also add an `equiv_like` and its descendants `add_equiv_class`, `mul_equiv_class`, `ring_equiv_class`, `linear_equiv_class`, ...
## Other changes
`coe_fn_coe_base` now has an appropriately low priority, so it doesn't take precedence over `fun_like.has_coe_to_fun`.
## Why are you unbundling the morphisms again?
It's not quite the same thing as unbundling. When using unbundled morphisms, parameters have the form `(f : A → B) (hf : is_foo_hom f)`; bundled morphisms look like `(f : foo_hom A B)` (where `foo_hom A B` is equivalent to `{ f : A → B // is_foo_hom f }`; typically you would use a custom structure instead of `subtype`). This plan puts a predicate on the *type* `foo_hom` rather than the *elements* of the type as you would with unbundled morphisms. I believe this will preserve the advantages of the bundled approach (being able to talk about the identity map, making it work with `simp`), while addressing one of its disadvantages (needing to duplicate all the lemmas whenever extending the type of morphisms).
## Discussion
Main Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclasses.20for.20morphisms
Some other threads referencing this plan:
 * https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Morphism.20refactor
 * https://leanprover.zulipchat.com/#narrow/stream/263328-triage/topic/issue.20.231044.3A.20bundling.20morphisms
 * [#1044](https://github.com/leanprover-community/mathlib/pull/1044)
 * [#4985](https://github.com/leanprover-community/mathlib/pull/4985)

### [2021-12-10 11:52:56](https://github.com/leanprover-community/mathlib/commit/165e055)
refactor(group_theory/quotient_group): use `con` ([#10699](https://github.com/leanprover-community/mathlib/pull/10699))
Use `con` to define `group` structure on `G ⧸ N` instead of repeating the construction in this case.

### [2021-12-10 11:52:55](https://github.com/leanprover-community/mathlib/commit/9a24b3e)
chore(ring_theory/noetherian): rename `submodule.fg_map` to `submodule.fg.map` ([#10688](https://github.com/leanprover-community/mathlib/pull/10688))
This renames:
* `submodule.fg_map` to `submodule.fg.map` (to match `submonoid.fg.map` and enable dot notation)
* `submodule.map_fg_of_fg` to `ideal.fg.map`
* `submodule.fg_ker_ring_hom_comp` to `ideal.fg_ker_comp` to match `submodule.fg_ker_comp`
and defines a new `ideal.fg` alias to avoid unfolding to `submodule R R` and `submodule.span`.

### [2021-12-10 11:52:54](https://github.com/leanprover-community/mathlib/commit/24cf723)
feat(ring_theory/polynomial/cyclotomic): generalize `is_root_cyclotomic` ([#10687](https://github.com/leanprover-community/mathlib/pull/10687))

### [2021-12-10 11:52:52](https://github.com/leanprover-community/mathlib/commit/3dcdf93)
feat(group_theory/finiteness): Lemmas about finitely generated submonoids ([#10681](https://github.com/leanprover-community/mathlib/pull/10681))

### [2021-12-10 11:52:50](https://github.com/leanprover-community/mathlib/commit/508fc18)
feat(ring_theory/ideal): Power of a spanning set is a spanning set ([#10656](https://github.com/leanprover-community/mathlib/pull/10656))

### [2021-12-10 09:20:23](https://github.com/leanprover-community/mathlib/commit/ce0e2c4)
feat(category_theory/limits): Pullback API ([#10620](https://github.com/leanprover-community/mathlib/pull/10620))
Needed for constructing fibered products of Schemes

### [2021-12-10 03:16:48](https://github.com/leanprover-community/mathlib/commit/e7959fb)
chore(scripts): update nolints.txt ([#10697](https://github.com/leanprover-community/mathlib/pull/10697))
I am happy to remove some nolints for you!

### [2021-12-10 00:34:16](https://github.com/leanprover-community/mathlib/commit/1ecdf71)
chore(algebra/punit_instances): add `comm_cancel_monoid_with_zero`, `normalized_gcd_monoid`, and scalar action instances ([#10312](https://github.com/leanprover-community/mathlib/pull/10312))
Motivated by [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Is.200.20not.20equal.20to.201.3F/near/261366868). 
This also moves the simp lemmas closer to the instances they refer to.

### [2021-12-09 21:51:35](https://github.com/leanprover-community/mathlib/commit/61dd343)
feat(probability_theory/martingale): define martingales ([#10625](https://github.com/leanprover-community/mathlib/pull/10625))

### [2021-12-09 19:38:25](https://github.com/leanprover-community/mathlib/commit/e618cfe)
feat(topology/continuous_function/bounded): register instances of `star` structures ([#10570](https://github.com/leanprover-community/mathlib/pull/10570))
Prove that the bounded continuous functions which take values in a normed C⋆-ring themselves form a C⋆-ring. Moreover, if the codomain is a normed algebra and a star module over a normed ⋆-ring, then so are the bounded continuous functions. Thus the bounded continuous functions form a C⋆-algebra when the codomain is a C⋆-algebra.

### [2021-12-09 17:18:51](https://github.com/leanprover-community/mathlib/commit/2538626)
fix(tactic/ring): instantiate metavariables ([#10589](https://github.com/leanprover-community/mathlib/pull/10589))
Fixes the issue reported in [#10572](https://github.com/leanprover-community/mathlib/pull/10572).
- [x] depends on: [#10572](https://github.com/leanprover-community/mathlib/pull/10572)

### [2021-12-09 16:26:29](https://github.com/leanprover-community/mathlib/commit/94783be)
feat(algebra/algebra/spectrum): lemmas when scalars are a field ([#10476](https://github.com/leanprover-community/mathlib/pull/10476))
Prove some properties of the spectrum when the underlying scalar ring
is a field, and mostly assuming the algebra is itself nontrivial.
Show that the spectrum of a scalar (i.e., `algebra_map 𝕜 A k`) is
the singleton `{k}`. Prove that `σ (a * b) \ {0} = σ (b * a) \ {0}`.

### [2021-12-09 14:52:57](https://github.com/leanprover-community/mathlib/commit/08215b5)
feat(data/finsupp/basic): lemmas on the support of the `tsub` of `finsupp`s ([#10651](https://github.com/leanprover-community/mathlib/pull/10651))

### [2021-12-09 14:52:56](https://github.com/leanprover-community/mathlib/commit/9ef122d)
feat(measure_theory/integral/set_to_l1): properties of (dominated_)fin_meas_additive ([#10590](https://github.com/leanprover-community/mathlib/pull/10590))
Various properties of `fin_meas_additive` and `dominated_fin_meas_additive` which will be useful to generalize results about integrals to `set_to_fun`.

### [2021-12-09 13:20:38](https://github.com/leanprover-community/mathlib/commit/c23b54c)
feat(group_theory/submonoid): The monoid_hom from a submonoid to its image. ([#10680](https://github.com/leanprover-community/mathlib/pull/10680))

### [2021-12-09 13:20:36](https://github.com/leanprover-community/mathlib/commit/97e4468)
feat(analysis/calculus/deriv): generalize some lemmas ([#10639](https://github.com/leanprover-community/mathlib/pull/10639))
Generalize lemmas about the chain rule to work with different fields.

### [2021-12-09 11:18:26](https://github.com/leanprover-community/mathlib/commit/bfe595d)
feat(order/filter,topology/instances/real): lemmas about `at_top`, `at_bot`, and `cocompact` ([#10652](https://github.com/leanprover-community/mathlib/pull/10652))
* prove `comap abs at_top = at_bot ⊔ at_top`;
* prove `comap coe at_top = at_top` and `comap coe at_bot = at_bot` for coercion from `ℕ`, `ℤ`, or `ℚ` to an archimedian semiring, ring, or field, respectively;
* prove `cocompact ℤ = at_bot ⊔ at_top` and `cocompact ℝ = at_bot ⊔ at_top`.

### [2021-12-09 09:57:14](https://github.com/leanprover-community/mathlib/commit/e3d9adf)
chore(measure_theory/function/conditional_expectation): change condexp notation ([#10584](https://github.com/leanprover-community/mathlib/pull/10584))
The previous definition and notation showed the `measurable_space` argument only through the other argument `m \le m0`, which tends to be replaced by `_` in the goal view if it becomes complicated.

### [2021-12-09 08:54:18](https://github.com/leanprover-community/mathlib/commit/70171ac)
feat(topology/instances/real_vector_space): add an `is_scalar_tower` instance ([#10490](https://github.com/leanprover-community/mathlib/pull/10490))
There is at most one topological real vector space structure on a topological additive group, so `[is_scalar_tower real A E]` holds automatically as long as `A` is a topological real algebra and `E` is a topological module over `A`.

### [2021-12-09 07:29:46](https://github.com/leanprover-community/mathlib/commit/4efa9d8)
chore(algebra/direct_limit): remove module.directed_system ([#10636](https://github.com/leanprover-community/mathlib/pull/10636))
This typeclass duplicated `_root_.directed_system`

### [2021-12-09 05:38:21](https://github.com/leanprover-community/mathlib/commit/11bf7e5)
feat(analysis/normed_space/weak_dual): add polar sets in preparation for Banach-Alaoglu theorem ([#9836](https://github.com/leanprover-community/mathlib/pull/9836))
The first of two parts to add the Banach-Alaoglu theorem about the compactness of the closed unit ball (and more generally polar sets of neighborhoods of the origin) of the dual of a normed space in the weak-star topology.
This first half is about polar sets (for a set `s` in a normed space `E`, the `polar s` is the subset of `weak_dual _ E` consisting of the functionals that evaluate to something of norm at most one at all elements of `s`).

### [2021-12-09 03:56:43](https://github.com/leanprover-community/mathlib/commit/fc3116f)
doc(data/nat/prime): fix links ([#10677](https://github.com/leanprover-community/mathlib/pull/10677))

### [2021-12-09 03:56:42](https://github.com/leanprover-community/mathlib/commit/ab31673)
feat(data/finset/basic): val_le_iff_val_subset ([#10603](https://github.com/leanprover-community/mathlib/pull/10603))
I'm not sure if we have something like this already on mathlib. The application of `val_le_of_val_subset` that I have in mind is to deduce
```
theorem polynomial.card_roots'' {F : Type u} [field F]{p : polynomial F}(h : p ≠ 0)
{Z : finset F} (hZ : ∀ z ∈ Z, polynomial.eval z p = 0) : Z.card ≤ p.nat_degree
```
from [polynomial.card_roots' ](https://github.com/leanprover-community/mathlib/blob/1376f53dacd3c3ccd3c345b6b8552cce96c5d0c8/src/data/polynomial/ring_division.lean#L318)
If this approach seems right, I will send the proof of `polynomial.card_roots''` in a follow up PR.

### [2021-12-09 01:13:05](https://github.com/leanprover-community/mathlib/commit/60c1d60)
feat(data/mv_polynomial/basic)  induction_on'' ([#10621](https://github.com/leanprover-community/mathlib/pull/10621))
A new flavor of `induction_on` which is useful when we do not have ` h_add : ∀p q, M p → M q → M (p + q)` but we have
```
h_add_weak : ∀ (a : σ →₀ ℕ) (b : R) (f : (σ →₀ ℕ) →₀ R),  a ∉ f.support → b ≠ 0 → M f → M (monomial a b + f)
```

### [2021-12-09 01:13:04](https://github.com/leanprover-community/mathlib/commit/e14dc11)
feat(data/int/basic): add `nat_abs_eq_nat_abs_iff_*` lemmas for nonnegative and nonpositive arguments ([#10611](https://github.com/leanprover-community/mathlib/pull/10611))

### [2021-12-08 22:28:20](https://github.com/leanprover-community/mathlib/commit/baab5d3)
refactor(data/matrix): reverse the direction of `matrix.minor_mul_equiv` ([#10657](https://github.com/leanprover-community/mathlib/pull/10657))
In [#10350](https://github.com/leanprover-community/mathlib/pull/10350) this change was proposed, since we apparently use that backwards way more than we use it forwards.
We also change `reindex_linear_equiv_mul`, which is similarly much more popular backwards than forwards.
Closes: [#10638](https://github.com/leanprover-community/mathlib/pull/10638)

### [2021-12-08 22:28:19](https://github.com/leanprover-community/mathlib/commit/2ea1fb6)
feat(data/list/range): fin_range_succ_eq_map ([#10654](https://github.com/leanprover-community/mathlib/pull/10654))

### [2021-12-08 22:28:18](https://github.com/leanprover-community/mathlib/commit/fdb773a)
chore(algebra/tropical/basic): golf and clean ([#10633](https://github.com/leanprover-community/mathlib/pull/10633))

### [2021-12-08 22:28:16](https://github.com/leanprover-community/mathlib/commit/bcd9a74)
refactor(data/complex/is_R_or_C): `finite_dimensional.proper_is_R_or_C` is not an `instance` anymore ([#10629](https://github.com/leanprover-community/mathlib/pull/10629))
This instance caused a search for `[finite_dimensional ?x E]` with an unknown `?x`. Turn it into a lemma and add `haveI` to some proofs. Also add an instance for `K ∙ x`.

### [2021-12-08 22:28:15](https://github.com/leanprover-community/mathlib/commit/e289343)
feat(algebra/graded_monoid): add lemmas about power and product membership ([#10627](https://github.com/leanprover-community/mathlib/pull/10627))
This adds:
* `set_like.graded_monoid.pow_mem`
* `set_like.graded_monoid.list_prod_map_mem`
* `set_like.graded_monoid.list_prod_of_fn_mem`
It doesn't bother to add the multiset and finset versions for now, because these are not imported at this point, and require the ring to be commutative.

### [2021-12-08 18:44:55](https://github.com/leanprover-community/mathlib/commit/1d0bb86)
fix(data/finsupp/basic): add missing decidable arguments ([#10672](https://github.com/leanprover-community/mathlib/pull/10672))
`finsupp` is classical, meaning that `def`s should just use noncomputable decidable instances rather than taking arguments that make more work for mathematicians.
However, this doesn't mean that lemma _statements_ should use noncomputable decidable instances, as this just makes the lemma less general and harder to apply (as shown by the `congr` removed elsewhere in the diff).
These were found by removing `open_locale classical` from the top of the file, adding `by classical; exact` to some definitions, and then fixing the broken lemma statements. In future we should detect this type of mistake with a linter.

### [2021-12-08 17:16:46](https://github.com/leanprover-community/mathlib/commit/2ce95ca)
refactor(data/finsupp): use `{f : α →₀ M | ∃ a b, f = single a b}` instead of union of ranges ([#10671](https://github.com/leanprover-community/mathlib/pull/10671))

### [2021-12-08 17:16:44](https://github.com/leanprover-community/mathlib/commit/8ab1b3b)
feat(measure_theory/probability_mass_function): Calculate supports of pmf constructions ([#10371](https://github.com/leanprover-community/mathlib/pull/10371))
This PR gives explicit descriptions for the `support` of the various `pmf` constructions in mathlib. 
This also tries to clean up the variable declarations in the different sections, so that all the lemmas don't need to specify them explicitly.

### [2021-12-08 15:28:51](https://github.com/leanprover-community/mathlib/commit/678566f)
feat(topology/algebra/group): Addition of interiors ([#10659](https://github.com/leanprover-community/mathlib/pull/10659))
This proves `interior s * t ⊆ interior (s * t)`, a few prerequisites, and generalizes to `is_open.mul_left`/`is_open.mul_right`.

### [2021-12-08 13:44:00](https://github.com/leanprover-community/mathlib/commit/eedb906)
feat(measure_theory/integral): `∫ x in b..b+a, f x = ∫ x in c..c + a, f x` for a periodic `f` ([#10477](https://github.com/leanprover-community/mathlib/pull/10477))

### [2021-12-08 05:53:32](https://github.com/leanprover-community/mathlib/commit/4d56716)
fix(data/finsupp/basic): add missing decidable argument ([#10649](https://github.com/leanprover-community/mathlib/pull/10649))
While `finsupp.erase` is classical and requires no decidability, `finset.erase` is not so.
Without this argument, this lemma does not apply in the general case, and introduces mismatching decidable instances. With it, a `congr` is no longer needed elsewhere in mathlib.

### [2021-12-08 05:53:31](https://github.com/leanprover-community/mathlib/commit/e5ba338)
fix(algebra/direct_sum): change `ring_hom_ext` to not duplicate `ring_hom_ext'` ([#10640](https://github.com/leanprover-community/mathlib/pull/10640))
These two lemmas differed only in the explicitness of their binders.
The statement of the unprimed version has been changed to be fully applied.
This also renames `alg_hom_ext` to `alg_hom_ext'` to make way for the fully applied version. This is consistent with `direct_sum.add_hom_ext` vs `direct_sum.add_hom_ext'`.

### [2021-12-08 04:59:26](https://github.com/leanprover-community/mathlib/commit/b495fdf)
feat(category_theory): Filtered colimits preserves finite limits in algebraic categories ([#10604](https://github.com/leanprover-community/mathlib/pull/10604))

### [2021-12-08 03:50:05](https://github.com/leanprover-community/mathlib/commit/2bfa768)
feat(analysis/normed_space/operator_norm): module and norm instances on continuous semilinear maps ([#10494](https://github.com/leanprover-community/mathlib/pull/10494))
This PR adds a module and a norm instance on continuous semilinear maps, generalizes most of the results in `operator_norm.lean` to the semilinear case. Many of these results require the ring homomorphism to be isometric, which is expressed via the new typeclass `[ring_hom_isometric σ]`.

### [2021-12-08 02:36:46](https://github.com/leanprover-community/mathlib/commit/1a92bc9)
chore(scripts): update nolints.txt ([#10662](https://github.com/leanprover-community/mathlib/pull/10662))
I am happy to remove some nolints for you!

### [2021-12-07 21:13:01](https://github.com/leanprover-community/mathlib/commit/eaa9e87)
chore(measure_theory/integral/set_to_l1): change definition of dominated_fin_meas_additive ([#10585](https://github.com/leanprover-community/mathlib/pull/10585))
Change the definition to check the property only on measurable sets with finite measure (like every other property in that file).
Also make some arguments of `set_to_fun` explicit to improve readability.

### [2021-12-07 19:16:26](https://github.com/leanprover-community/mathlib/commit/54aeec7)
feat(topology/algebra/ordered/basic): Interior of `{x | f x ≤ g x}` ([#10653](https://github.com/leanprover-community/mathlib/pull/10653))
and golf the dual one: `closure_lt_subset_le`

### [2021-12-07 18:28:16](https://github.com/leanprover-community/mathlib/commit/a803e21)
feat(measure_theory/lattice): define typeclasses for measurability of lattice operations, define a lattice on ae_eq_fun ([#10591](https://github.com/leanprover-community/mathlib/pull/10591))
As was previously done for measurability of arithmetic operations, I define typeclasses for the measurability of sup and inf in a lattice. In the borel_space file, instances of these are provided when the lattice operations are continuous.
Finally I've put a lattice structure on `ae_eq_fun`.

### [2021-12-07 15:39:30](https://github.com/leanprover-community/mathlib/commit/ae7a88d)
feat(field_theory/finite/basic): generalize lemma from field to integral domain ([#10655](https://github.com/leanprover-community/mathlib/pull/10655))

### [2021-12-07 15:39:28](https://github.com/leanprover-community/mathlib/commit/9a2c299)
feat(data/pi): add `pi.single_inj` ([#10644](https://github.com/leanprover-community/mathlib/pull/10644))

### [2021-12-07 15:39:27](https://github.com/leanprover-community/mathlib/commit/03dd404)
feat(algebra/category): (co)limits in CommRing ([#10593](https://github.com/leanprover-community/mathlib/pull/10593))

### [2021-12-07 14:45:55](https://github.com/leanprover-community/mathlib/commit/173a21a)
feat(topology/sheaves): `F(U ⨿ V) = F(U) × F(V)` ([#10597](https://github.com/leanprover-community/mathlib/pull/10597))

### [2021-12-07 06:39:50](https://github.com/leanprover-community/mathlib/commit/ba1cbfa)
feat(topology/algebra/ordered/basic): Add alternative formulations of four lemmas. ([#10630](https://github.com/leanprover-community/mathlib/pull/10630))
Add alternative formulations of lemmas about interiors and frontiers of `Iic` and `Ici`. The existing formulations make typeclass assumptions `[no_top_order]` or `[no_bot_order]`. These alternative formulations assume instead that the endpoint of the interval is not top or bottom; and as such they can be applied in, e.g., `nnreal` and `ennreal`.
Also, some lemmas now assume `(Ioi a).nonempty` or `(Iio a).nonempty` instead of `{b} (h : a < b)` or `{b} (h : b < a)`, respectively.

### [2021-12-07 00:26:04](https://github.com/leanprover-community/mathlib/commit/9031989)
chore(*): fix last line length and notation style linter errors ([#10642](https://github.com/leanprover-community/mathlib/pull/10642))
These are the last non-module doc style linter errors (from https://github.com/leanprover-community/mathlib/blob/master/scripts/style-exceptions.txt).

### [2021-12-07 00:26:03](https://github.com/leanprover-community/mathlib/commit/cd857f7)
feat(data/int/basic): four lemmas about integer divisibility ([#10602](https://github.com/leanprover-community/mathlib/pull/10602))
Theorem 1.1, parts (c), (i), (j), and (k) of Apostol (1976) Introduction to Analytic Number Theory

### [2021-12-06 22:38:00](https://github.com/leanprover-community/mathlib/commit/eec4b70)
feat(algebra/geom_sum): criteria for 0 < geom_sum ([#10567](https://github.com/leanprover-community/mathlib/pull/10567))

### [2021-12-06 21:05:46](https://github.com/leanprover-community/mathlib/commit/a8c086f)
feat(linear_algebra/determinant): linear_equiv.det_mul_det_symm ([#10635](https://github.com/leanprover-community/mathlib/pull/10635))
Add lemmas that the determinants of a `linear_equiv` and its
inverse multiply to 1.  There are a few other lemmas involving
determinants and `linear_equiv`, but apparently not this one.

### [2021-12-06 19:23:02](https://github.com/leanprover-community/mathlib/commit/1d5202a)
feat(data/multiset): add some lemmas about filter (eq x) ([#10626](https://github.com/leanprover-community/mathlib/pull/10626))

### [2021-12-06 14:45:34](https://github.com/leanprover-community/mathlib/commit/8124314)
feat(linear_algebra/multilinear/basic,linear_algebra/alternating): comp_linear_map lemmas ([#10631](https://github.com/leanprover-community/mathlib/pull/10631))
Add more lemmas about composing multilinear and alternating maps with
linear maps in each argument.
Where I wanted a lemma for either of multilinear or alternating maps,
I added it for both.  There are however some lemmas for
`alternating_map.comp_linear_map` that don't have equivalents at
present for `multilinear_map.comp_linear_map` (I added one such
equivalent `multilinear_map.zero_comp_linear_map` because I needed it
for another lemma, but didn't try adding such equivalents of existing
lemmas where I didn't need them).

### [2021-12-06 13:25:54](https://github.com/leanprover-community/mathlib/commit/f50984d)
chore(linear_algebra/affine_space/basis): remove unhelpful coercion ([#10637](https://github.com/leanprover-community/mathlib/pull/10637))
It is more useful to have a statement of equality of linear maps than
of raw functions.

### [2021-12-06 06:48:34](https://github.com/leanprover-community/mathlib/commit/e6ad0f2)
chore(analysis/inner_product/projections): generalize some lemmas ([#10608](https://github.com/leanprover-community/mathlib/pull/10608))
* generalize a few lemmas from `[finite_dimensional 𝕜 ?x]` to `[complete_space ?x]`;
* drop unneeded TC assumption in `isometry.tendsto_nhds_iff`;
* image of a complete set/submodule under an isometry is a complete set/submodule.

### [2021-12-06 05:02:03](https://github.com/leanprover-community/mathlib/commit/e726945)
refactor(order/atoms): is_simple_order from is_simple_lattice ([#10537](https://github.com/leanprover-community/mathlib/pull/10537))
Rename `is_simple_lattice` to `is_simple_order`, still stating that every element is either `bot` or `top` are, and that it is nontrivial.
To state `is_simple_order`, `has_le` and `bounded_order` are required to be defined. This allows for an order where `⊤ ≤ ⊥` (the always true order). 
Many proofs/statements about `is_simple_order`s have been generalized to require solely `partial_order` and not `lattice`. The statements themselves have not been changed. 
The `is_simple_order.distrib_lattice` instance has been downgraded into a `def` to prevent loops.
Helper defs have been added like `is_simple_order.preorder` (which is true given the `has_le` `bounded_order` axioms) `is_simple_order.linear_order`, and `is_simple_order.lattice` (which are true when `partial_order`, implying `⊥ < ⊤`.).

### [2021-12-05 19:54:45](https://github.com/leanprover-community/mathlib/commit/e7bd49f)
chore(scripts/mk_all.sh): allow 'mk_all.sh ../test' ([#10628](https://github.com/leanprover-community/mathlib/pull/10628))
Helpful for mathport CI, cf https://github.com/leanprover-community/mathport/pull/64

### [2021-12-05 18:05:59](https://github.com/leanprover-community/mathlib/commit/2b2d116)
chore(combinatorics/simple_graph/coloring): remove extra asterisk ([#10618](https://github.com/leanprover-community/mathlib/pull/10618))

### [2021-12-05 16:33:11](https://github.com/leanprover-community/mathlib/commit/8c1f2b5)
feat(ring_theory/graded_algebra): projection map of graded algebra ([#10116](https://github.com/leanprover-community/mathlib/pull/10116))
This pr defines and proves some property about `graded_algebra.proj : A →ₗ[R] A`

### [2021-12-05 11:46:50](https://github.com/leanprover-community/mathlib/commit/428b9e5)
feat(topology/continuous_function/bounded): continuous bounded real-valued functions form a normed vector lattice ([#10322](https://github.com/leanprover-community/mathlib/pull/10322))
feat(topology/continuous_function/bounded): continuous bounded real-valued functions form a normed vector lattice

### [2021-12-05 03:46:59](https://github.com/leanprover-community/mathlib/commit/37f343c)
chore(data/stream): merge `basic` into `init` ([#10617](https://github.com/leanprover-community/mathlib/pull/10617))

### [2021-12-04 15:25:01](https://github.com/leanprover-community/mathlib/commit/6eeb54e)
fix(topology/algebra/uniform_field): remove unnecessary topological_r… ([#10614](https://github.com/leanprover-community/mathlib/pull/10614))
…ing variable
Right now the last three definitions in `topology.algebra.uniform_field` (after line 115) have `[topological_division_ring K]` and `[topological_ring K]`. For example
```
mul_hat_inv_cancel :
  ∀ {K : Type u_1} [_inst_1 : field K] [_inst_2 : uniform_space K] [_inst_3 : topological_division_ring K]
  [_inst_4 : completable_top_field K] [_inst_5 : uniform_add_group K] [_inst_6 : topological_ring K]
  {x : uniform_space.completion K}, x ≠ 0 → x * hat_inv x = 1
```
Whilst it is not obvious from the notation, both of these are `Prop`s so there is no danger of diamonds. The full logic is: `field` and `uniform_space` are data, and the rest are Props (so should be called things like `is_topological_ring` etc IMO). `topological_division_ring` is the assertion of continuity of `add`, `neg`, `mul` and `inv` (away from 0), `completable_top_field` is another assertion about how inversion plays well with the topology (and which is not implied by `topological_division_ring`), `uniform_add_group` is the assertion about `add` and `neg` playing well with the uniform structure, and then `topological_ring` is a prop which is implied by `topological_division_ring`. I am not sure I see the benefits of carrying around the extra `topological_ring` for these three definitions so I've removed it to see if mathlib still compiles. Edit: it does.

### [2021-12-04 15:25:00](https://github.com/leanprover-community/mathlib/commit/c940e47)
chore(topology/continuous_function): remove forget_boundedness ([#10612](https://github.com/leanprover-community/mathlib/pull/10612))
It is the same as `to_continuous_map`.

### [2021-12-04 13:36:16](https://github.com/leanprover-community/mathlib/commit/b3b7fe6)
chore(algebra/module): generalize `char_zero.of_algebra` to `char_zero.of_module` ([#10609](https://github.com/leanprover-community/mathlib/pull/10609))

### [2021-12-04 08:58:37](https://github.com/leanprover-community/mathlib/commit/5d0e65a)
chore(order/galois_connection): upgrade `is_glb_l` to `is_least_l` ([#10606](https://github.com/leanprover-community/mathlib/pull/10606))
* upgrade `galois_connection.is_glb_l` to `galois_connection.is_least_l`;
* upgrade `galois_connection.is_lub_l` to `galois_connection.is_greatest_l`.

### [2021-12-04 07:14:54](https://github.com/leanprover-community/mathlib/commit/3479b7f)
chore(order/complete_lattice): golf a proof ([#10607](https://github.com/leanprover-community/mathlib/pull/10607))
Also reformulate `le_Sup_iff` in terms of `upper_bounds`.

### [2021-12-04 05:05:06](https://github.com/leanprover-community/mathlib/commit/9c4e41a)
feat(number_theory/modular): the action of `SL(2, ℤ)` on the upper half plane ([#8611](https://github.com/leanprover-community/mathlib/pull/8611))
We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in `analysis.complex.upper_half_plane`). We then define the standard fundamental domain `𝒟` for this action and show that any point in `ℍ` can be moved inside `𝒟`.

### [2021-12-04 03:25:04](https://github.com/leanprover-community/mathlib/commit/2da25ed)
feat(combinatorics/simple_graph): Graph coloring and partitions ([#10287](https://github.com/leanprover-community/mathlib/pull/10287))

### [2021-12-04 01:52:50](https://github.com/leanprover-community/mathlib/commit/ef3540a)
chore(measure_theory/function/conditional_expectation): golf condexp_L1 proofs using set_to_fun lemmas ([#10592](https://github.com/leanprover-community/mathlib/pull/10592))

### [2021-12-04 01:52:49](https://github.com/leanprover-community/mathlib/commit/23dfe70)
feat(*): `A ⧸ B` notation for quotients in algebra ([#10501](https://github.com/leanprover-community/mathlib/pull/10501))
We introduce a class `has_quotient` that provides `⧸` (U+29F8 BIG SOLIDUS) notation for quotients, e.g. if `H : subgroup G` then `quotient_group.quotient H` is now written as `G ⧸ H`. Thanks to @jcommelin for suggesting the initial design.
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Notation.20for.20group.28module.2Cideal.29.20quotients

### [2021-12-04 00:14:36](https://github.com/leanprover-community/mathlib/commit/0bd9b6a)
feat(group_theory/order_of_element): order of a product of elements ([#10399](https://github.com/leanprover-community/mathlib/pull/10399))
The lemma is: If `x` and `y` are commuting elements of coprime orders, then the order of `x * y` is the product of the orders of `x` and `y`. This also gives a version for the minimal period in dynamics from which the algebraic statement is derived.

### [2021-12-03 20:46:31](https://github.com/leanprover-community/mathlib/commit/1376f53)
feat(analysis.normed_space.lattice_ordered_group): Add `two_inf_sub_two_inf_le`, `two_sup_sub_two_sup_le` and supporting lemmas ([#10514](https://github.com/leanprover-community/mathlib/pull/10514))
feat(analysis.normed_space.lattice_ordered_group): Add `two_inf_sub_two_inf_le`, `two_sup_sub_two_sup_le` and supporting lemmas

### [2021-12-03 19:27:08](https://github.com/leanprover-community/mathlib/commit/cd2230b)
chore(data/nat/prime): golf some proofs ([#10599](https://github.com/leanprover-community/mathlib/pull/10599))

### [2021-12-03 19:27:05](https://github.com/leanprover-community/mathlib/commit/bddc16a)
fix(tactic/abel): handle smul on groups ([#10587](https://github.com/leanprover-community/mathlib/pull/10587))
The issue was that `abel` expects to see only `smulg` used for groups and only `smul` for monoids, but you can also use `smul` on groups so we have to normalize that away.
fixes [#8456](https://github.com/leanprover-community/mathlib/pull/8456)

### [2021-12-03 17:46:34](https://github.com/leanprover-community/mathlib/commit/46e9a23)
feat(probability_theory/stopping): generalize a lemma ([#10598](https://github.com/leanprover-community/mathlib/pull/10598))

### [2021-12-03 17:46:33](https://github.com/leanprover-community/mathlib/commit/1e89745)
feat(data/finset/lattice): add sup_eq_bot_iff and inf_eq_top_iff ([#10596](https://github.com/leanprover-community/mathlib/pull/10596))
From flt-regular.

### [2021-12-03 17:46:32](https://github.com/leanprover-community/mathlib/commit/92fafba)
feat(data/(mv_)polynomial): add aeval_prod and aeval_sum for (mv_)polynomial ([#10594](https://github.com/leanprover-community/mathlib/pull/10594))
Another couple of small polynomial helper lemmas from flt-regular.

### [2021-12-03 17:46:31](https://github.com/leanprover-community/mathlib/commit/4de0773)
feat(category_theory/limits): Strict terminal objects. ([#10582](https://github.com/leanprover-community/mathlib/pull/10582))

### [2021-12-03 17:46:29](https://github.com/leanprover-community/mathlib/commit/d45708f)
feat(topology/sheaves): The empty component of a sheaf is terminal ([#10578](https://github.com/leanprover-community/mathlib/pull/10578))

### [2021-12-03 16:11:45](https://github.com/leanprover-community/mathlib/commit/1e18e93)
chore(algebra/lattice_ordered_group): review (names, spaces, golf...) ([#10595](https://github.com/leanprover-community/mathlib/pull/10595))
This is a review of `algebra/lattice_ordered_group` and `analysis/normed_space/lattice_ordered_group`:
- delete or add spaces at many places
- add brackets around goals
- replace `apply` by `exact` when closing a goal
- change many names to better fit the naming convention
- cut some big proofs into several lemmas
- add a few `simp` attributes
- remove a non-terminal simp
- golf
- add some simple API lemmas
I did not do anything about the docstrings of the lemmas. Some of them don't interact correctly with `to_additive` (the additive comment is shown for the multiplicative lemma in the doc, for example).

### [2021-12-03 16:11:43](https://github.com/leanprover-community/mathlib/commit/a7b4018)
fix(tactic/ring): bugfixes in ring_nf ([#10572](https://github.com/leanprover-community/mathlib/pull/10572))
As reported by @hrmacbeth:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60ring_nf.60.20behaves.20strangely.20with.20def.20in.20original.20goal

### [2021-12-03 16:11:41](https://github.com/leanprover-community/mathlib/commit/df93166)
feat(algebraic_geometry): Explicit description of the colimit of presheafed spaces. ([#10466](https://github.com/leanprover-community/mathlib/pull/10466))

### [2021-12-03 16:11:40](https://github.com/leanprover-community/mathlib/commit/b7ed03f)
feat(algebraic_geometry): Open immersions of presheafed spaces ([#10437](https://github.com/leanprover-community/mathlib/pull/10437))

### [2021-12-03 16:11:38](https://github.com/leanprover-community/mathlib/commit/2f44ac8)
feat(algebra/monoid_algebra/grading): internal graded structure for an arbitrary degree function ([#10435](https://github.com/leanprover-community/mathlib/pull/10435))
This gives an internal graded structure of an additive monoid algebra for the grading given by an arbitrary degree function. The grading in the original file is redefined as the grading for the identity degree function.

### [2021-12-03 16:11:37](https://github.com/leanprover-community/mathlib/commit/f0a1cd1)
feat(category_theory/*): Representably flat functors ([#9519](https://github.com/leanprover-community/mathlib/pull/9519))
Defined representably flat functors as functors `F : C ⥤ D` such that `(X/F)` is cofiltered for each `X : C`.
- Proved that if `C` has all finite limits and `F` preserves them, then `F` is flat.
- Proved that flat functors preserves finite limits.
In particular, if `C` is finitely complete, then flat iff left exact.
- Proved that if `C, D` are small, then `F` flat implies `Lan F.op` preserves finite limits implies `F` preserves finite limits.
In particular, if `C` is finitely cocomplete, then flat iff `Lan F.op` is left exact.

### [2021-12-03 14:32:19](https://github.com/leanprover-community/mathlib/commit/8bb26a7)
chore(*): protect `to_fun` and `map_{add,zero,mul,one,div}` ([#10580](https://github.com/leanprover-community/mathlib/pull/10580))
This PR prepares for [#9888](https://github.com/leanprover-community/mathlib/pull/9888) by namespacing all usages of `to_fun` and `map_{add,zero,mul,one,div}` that do not involve the classes of [#9888](https://github.com/leanprover-community/mathlib/pull/9888). This includes e.g. `polynomial.map_add` and `multiset.map_add`, which involve `polynomial.map` and `multiset.map` respectively.

### [2021-12-03 14:32:17](https://github.com/leanprover-community/mathlib/commit/235e583)
feat(topology/metric_space/hausdorff_distance): add definition and lemmas about closed thickenings of subsets ([#10542](https://github.com/leanprover-community/mathlib/pull/10542))
Add definition and basic API about closed thickenings of subsets in metric spaces, in preparation for the portmanteau theorem on characterizations of weak convergence of Borel probability measures.

### [2021-12-03 12:40:48](https://github.com/leanprover-community/mathlib/commit/6533500)
feat(data/mv_polynomial): add total_degree_add_of_total_degree_lt ([#10571](https://github.com/leanprover-community/mathlib/pull/10571))
A helpful lemma to compute total degrees from flt-regular.

### [2021-12-03 12:40:47](https://github.com/leanprover-community/mathlib/commit/672e2b2)
feat(src/algebra/gcd_monoid,src/ring_theory): add some exists_associated_pow_of_mul_eq_pow variants ([#10560](https://github.com/leanprover-community/mathlib/pull/10560))

### [2021-12-03 12:40:46](https://github.com/leanprover-community/mathlib/commit/89697a2)
feat(data/fintype/order): complete order instances for fintype ([#7123](https://github.com/leanprover-community/mathlib/pull/7123))
This PR adds several instances (as defs) for fintypes:
* `order_bot` from `semilattice_inf`, `order_top` from `semilattice_sup`, `bounded_order` from `lattice`.
* `complete_lattice` from `lattice`.
* `complete_linear_order` from `linear_order`.
We use this last one to give a `complete_linear_order` instance for `fin (n + 1)` .

### [2021-12-03 10:55:10](https://github.com/leanprover-community/mathlib/commit/e0c27fe)
feat(order/bounded_order): a few more `simp` lemmas ([#10533](https://github.com/leanprover-community/mathlib/pull/10533))
Inspired by [#10486](https://github.com/leanprover-community/mathlib/pull/10486)

### [2021-12-03 10:55:09](https://github.com/leanprover-community/mathlib/commit/970f074)
feat(analysis/convex/star): Star-convex sets ([#10524](https://github.com/leanprover-community/mathlib/pull/10524))
This defines `star_convex 𝕜 x s` to mean that a set is star-convex (aka star-shaped, radially convex, or a star domain) at `x`. This means that every segment from `x` to a point in `s` is a subset of `s`.

### [2021-12-03 10:55:08](https://github.com/leanprover-community/mathlib/commit/44b649c)
doc(algebra.lattice_ordered_group): Remove verbose docstrings ([#10468](https://github.com/leanprover-community/mathlib/pull/10468))
doc(algebra.lattice_ordered_group): Remove verbose docstrings

### [2021-12-03 08:57:31](https://github.com/leanprover-community/mathlib/commit/2648e68)
chore(int/*): dedup lemma ([#10583](https://github.com/leanprover-community/mathlib/pull/10583))

### [2021-12-03 08:57:30](https://github.com/leanprover-community/mathlib/commit/0453320)
feat(category_theory/limits): The product is the pullback over the terminal objects. ([#10581](https://github.com/leanprover-community/mathlib/pull/10581))

### [2021-12-03 08:57:28](https://github.com/leanprover-community/mathlib/commit/bfccd1b)
chore(topology/{metric_space,instances/real}): cleanup ([#10577](https://github.com/leanprover-community/mathlib/pull/10577))
* merge `real.ball_eq` and `real.ball_eq_Ioo` into `real.ball_eq_Ioo`;
* merge `real.closed_ball_eq` and `real.closed_ball_eq_Icc` into `real.closed_ball_eq_Icc`;
* add missing `real.Icc_eq_closed_ball`;
* generalize lemmas about `*bounded_Ixx` so that they work for (indexed) products of conditionally complete linear orders.

### [2021-12-03 08:57:27](https://github.com/leanprover-community/mathlib/commit/158263c)
feat(ring_theory): Nilradical and reduced ring ([#10576](https://github.com/leanprover-community/mathlib/pull/10576))

### [2021-12-03 08:57:26](https://github.com/leanprover-community/mathlib/commit/c176aa5)
refactor(data/stream): swap args of `stream.nth` ([#10559](https://github.com/leanprover-community/mathlib/pull/10559))
This way it agrees with (a) `list.nth`; (b) a possible redefinition
```lean
structure stream (α : Type*) := (nth : nat → α)
```

### [2021-12-03 08:57:25](https://github.com/leanprover-community/mathlib/commit/55b64b6)
chore(group_theory/*): additivise! ([#10557](https://github.com/leanprover-community/mathlib/pull/10557))

### [2021-12-03 08:57:23](https://github.com/leanprover-community/mathlib/commit/56c9cab)
feat(data/sigma{lex,order}): Lexicographic and disjoint orders on a sigma type ([#10552](https://github.com/leanprover-community/mathlib/pull/10552))
This defines the two natural order on a sigma type: the one where we just juxtapose the summands with their respective order, and the one where we also add in an order between summands.

### [2021-12-03 08:57:22](https://github.com/leanprover-community/mathlib/commit/d62b517)
feat(category_theory/limits): Walking parallel pair equiv to its op. ([#10516](https://github.com/leanprover-community/mathlib/pull/10516))

### [2021-12-03 08:57:21](https://github.com/leanprover-community/mathlib/commit/c151a12)
feat(algebra/gcd_monoid/*): assorted lemmas ([#10508](https://github.com/leanprover-community/mathlib/pull/10508))
From flt-regular.

### [2021-12-03 08:57:20](https://github.com/leanprover-community/mathlib/commit/c093d04)
feat(data/nat/basic): Monotonicity of `nat.find_greatest` ([#10507](https://github.com/leanprover-community/mathlib/pull/10507))
This proves that `nat.find_greatest` is monotone in both arguments.

### [2021-12-03 08:57:19](https://github.com/leanprover-community/mathlib/commit/00e9e90)
feat(topology/urysohns_bounded): +2 versions of Urysohn's lemma ([#10479](https://github.com/leanprover-community/mathlib/pull/10479))

### [2021-12-03 07:10:46](https://github.com/leanprover-community/mathlib/commit/403d9c0)
feat(category_theory/adjunction): Added simp lemmas for `left_adjoint_uniq` and `right_adjoint_uniq` ([#10551](https://github.com/leanprover-community/mathlib/pull/10551))

### [2021-12-03 07:10:45](https://github.com/leanprover-community/mathlib/commit/30185dc)
feat(topology/algebra/group): group topologies on a given group form a complete lattice ([#10531](https://github.com/leanprover-community/mathlib/pull/10531))

### [2021-12-03 07:10:44](https://github.com/leanprover-community/mathlib/commit/cfecf72)
feat(algebra/module): push forward the action of `R` on `M` along `f : R → S` ([#10502](https://github.com/leanprover-community/mathlib/pull/10502))
If `f : R →+* S` is compatible with the `R`-module structure on `M`, and the scalar action of `S` on `M`, then `M` gets an `S`-module structure too. Additionally, if `R` is a ring and the kernel of `f` acts on `M` by sending it to `0`, then we don't need to specify the scalar action of `S` on `M` (but it is still possible for defeq purposes).
These definitions should allow you to turn an action of `R` on `M` into an action of `R/I` on `M/N` via the (previously defined) action of `R` on `M/N`.

### [2021-12-03 07:10:43](https://github.com/leanprover-community/mathlib/commit/461051a)
feat(algebraic_geometry): Localization map is an embedding. ([#10471](https://github.com/leanprover-community/mathlib/pull/10471))

### [2021-12-03 07:10:41](https://github.com/leanprover-community/mathlib/commit/6bd6b45)
feat(algebraic_geometry): Isomorphisms of presheafed space. ([#10461](https://github.com/leanprover-community/mathlib/pull/10461))

### [2021-12-03 07:10:40](https://github.com/leanprover-community/mathlib/commit/f8f28da)
feat(linear_algebra/orientation): orientations of modules and rays in modules ([#10306](https://github.com/leanprover-community/mathlib/pull/10306))
Define orientations of modules, along the lines of a definition
suggested by @hrmacbeth: equivalence classes of nonzero alternating
maps.  See:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/adding.20angles/near/243856522
Rays are defined in an arbitrary module over an
`ordered_comm_semiring`, then orientations are considered as the case
of rays for the space of alternating maps.  That definition uses an
arbitrary index type; the motivating use case is where this has the
cardinality of a basis (two-dimensional use cases will use an index
type that is definitionally `fin 2`, for example).
The motivating use case is over the reals, but the definitions and
lemmas are for `ordered_comm_semiring`, `ordered_comm_ring`,
`linear_ordered_comm_ring` or `linear_ordered_field` as appropriate (a
`nontrivial` `ordered_comm_semiring` looks like it's the weakest case
for which much useful can be done with this definition).
Given an intended use case (oriented angles for Euclidean geometry)
where it will make sense for many proofs (and notation) to fix a
choice of orientation throughout, there is also a `module.oriented`
type class so the choice of orientation can be implicit in such proofs
and the lemmas they use.  However, nothing yet makes use of the type
class; everything so far is for explicit rays or orientations.
I expect more definitions and lemmas about orientations will need
adding to make much use of orientations.  In particular, I expect to
need to add more about orientations in relation to bases
(e.g. extracting a basis that gives a given orientation, in positive
dimension).

### [2021-12-03 07:10:39](https://github.com/leanprover-community/mathlib/commit/2bb627f)
feat(analysis/convex/[basic, topology]): generalize path connectedness of convex sets to topological real vector spaces ([#10011](https://github.com/leanprover-community/mathlib/pull/10011))

### [2021-12-03 06:35:10](https://github.com/leanprover-community/mathlib/commit/8915dc8)
feat(ring_theory/polynomial/cyclotomic): `is_root_cyclotomic_iff` ([#10422](https://github.com/leanprover-community/mathlib/pull/10422))
From the flt-regular project.

### [2021-12-03 05:24:46](https://github.com/leanprover-community/mathlib/commit/6f745cd)
feat(category_theory/limits): Lemmas about preserving pullbacks ([#10438](https://github.com/leanprover-community/mathlib/pull/10438))

### [2021-12-02 23:23:50](https://github.com/leanprover-community/mathlib/commit/c791747)
feat(algebra/tropical/basic): various API ([#10487](https://github.com/leanprover-community/mathlib/pull/10487))
Generalize some order instance to just require `has_le` of the base `R`.
`(un)trop_monotone`
`trop_(min|inf)`
iffs between addition and order
`tropical.add_comm_monoid` (in parallel to [#10486](https://github.com/leanprover-community/mathlib/pull/10486))
`(co|contra)variant` instances

### [2021-12-02 22:04:36](https://github.com/leanprover-community/mathlib/commit/ac76745)
feat(data/finsupp/basic): add `finsupp.prod_congr` and `sum_congr` ([#10568](https://github.com/leanprover-community/mathlib/pull/10568))
These are the counterparts for `finsupp` of a simpler form of `finset.prod_congr`

### [2021-12-02 20:44:25](https://github.com/leanprover-community/mathlib/commit/42d3cbc)
feat(data/finsupp/basic): add `nat.cast_finsupp_prod` and 3 others ([#10579](https://github.com/leanprover-community/mathlib/pull/10579))
Add counterparts for `finsupp` of `nat.cast_prod` etc., as discussed in this thread https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/push_cast

### [2021-12-02 19:28:48](https://github.com/leanprover-community/mathlib/commit/4cfe637)
chore(category_theory/sites/*): Adjust some `simp` lemmas. ([#10574](https://github.com/leanprover-community/mathlib/pull/10574))
The primary change is removing some `simp` tags from the definition of `sheafify` and friends, so that the sheafification related constructions are not unfolded to the `plus` constructions.
Also -- added coercion from Sheaves to presheaves, and some `rfl` simp lemmas which help some proofs move along.
Some proofs cleaned up as well.

### [2021-12-02 19:28:46](https://github.com/leanprover-community/mathlib/commit/cbb2d2c)
feat(data/nat/prime): Add lemma `count_factors_mul_of_pos` ([#10536](https://github.com/leanprover-community/mathlib/pull/10536))
Adding the counterpart to `count_factors_mul_of_coprime` for positive `a` and `b`

### [2021-12-02 17:52:35](https://github.com/leanprover-community/mathlib/commit/38ae0c9)
feat(data/nat/prime): add coprime_of_prime lemmas ([#10534](https://github.com/leanprover-community/mathlib/pull/10534))
Adds `coprime_of_lt_prime` and `eq_or_coprime_of_le_prime`, which help one to prove a number is coprime to a prime. Spun off of [#9080](https://github.com/leanprover-community/mathlib/pull/9080).

### [2021-12-02 14:23:28](https://github.com/leanprover-community/mathlib/commit/5e02292)
feat(data/finset/*): Diverse lemmas ([#10388](https://github.com/leanprover-community/mathlib/pull/10388))
A bunch of simple lemmas

### [2021-12-02 14:23:27](https://github.com/leanprover-community/mathlib/commit/790d637)
feat(combinatorics/set_family/compression/uv): UV-compression of a set family ([#10238](https://github.com/leanprover-community/mathlib/pull/10238))
This defines the UV-compression of a set family, along with a bunch of preliminary definitions and some basic results.

### [2021-12-02 12:47:03](https://github.com/leanprover-community/mathlib/commit/17c2209)
feat(probability_theory/stopping): define filtration and stopping time ([#10553](https://github.com/leanprover-community/mathlib/pull/10553))
This PR defines filtrations and stopping times which are used in stochastic processes. This is the first step towards creating a theory of martingales in lean.

### [2021-12-02 12:47:02](https://github.com/leanprover-community/mathlib/commit/6806050)
feat(category_theory/sites/adjunction): Adjunctions between categories of sheaves. ([#10541](https://github.com/leanprover-community/mathlib/pull/10541))
We construct adjunctions between categories of sheaves obtained by composition (and sheafification) with functors which form a given adjunction.
Will be used in LTE.

### [2021-12-02 12:47:00](https://github.com/leanprover-community/mathlib/commit/3e72feb)
feat(ring_theory/localization): The localization of a localization is a localization. ([#10456](https://github.com/leanprover-community/mathlib/pull/10456))
Also provides an easy consequence : the map of `Spec M⁻¹R ⟶ Spec R` is isomorphic on stalks.

### [2021-12-02 11:02:49](https://github.com/leanprover-community/mathlib/commit/fed2929)
chore(*): golf some proofs ([#10575](https://github.com/leanprover-community/mathlib/pull/10575))
Also add `strict_mono_on.monotone_on` and `strict_anti_on.antitone_on`.

### [2021-12-02 05:21:48](https://github.com/leanprover-community/mathlib/commit/665c13a)
chore(*): clean up/golf proofs with unneeded or case splits ([#10569](https://github.com/leanprover-community/mathlib/pull/10569))
Golf/simplify/clean up some more proofs with unnecessary case splits, this time found by linting for `or.dcases_on` with branches proving the more general fact.

### [2021-12-02 03:37:51](https://github.com/leanprover-community/mathlib/commit/34758d3)
doc(group_theory/index): add a theorem name and fix a to_additive ([#10564](https://github.com/leanprover-community/mathlib/pull/10564))
I wanted to find the theorem I know as "Lagrange's theorem" but couldn't by searching.
This PR adds the name Lagrange's theorem to the relevant file, and also fixes an extra eager `to_additive` renaming that creates a lemma `add_subgroup.index_add_card` which talks about multiplication previously.

### [2021-12-02 03:37:50](https://github.com/leanprover-community/mathlib/commit/7043521)
chore(algebra/order/*): drop some `[nontrivial _]` assumptions ([#10550](https://github.com/leanprover-community/mathlib/pull/10550))
Use `pullback_nonzero` to deduce `nontrivial _` in some `function.injective.*` constructors.

### [2021-12-02 03:37:49](https://github.com/leanprover-community/mathlib/commit/0f12400)
chore(*): more cleanups of by_cases ([#10549](https://github.com/leanprover-community/mathlib/pull/10549))
Follow up  [#10523](https://github.com/leanprover-community/mathlib/pull/10523) with more tool-assisted golfing, see that PR for details.

### [2021-12-01 17:04:54](https://github.com/leanprover-community/mathlib/commit/c09501d)
feat(*): assorted `finset` lemmas ([#10566](https://github.com/leanprover-community/mathlib/pull/10566))

### [2021-12-01 11:46:33](https://github.com/leanprover-community/mathlib/commit/cc60470)
feat(data/nat/prime): Add lemma `factors_count_pow` ([#10554](https://github.com/leanprover-community/mathlib/pull/10554))

### [2021-12-01 03:17:51](https://github.com/leanprover-community/mathlib/commit/599a511)
feat(analysis/normed_space/star and data/complex/is_R_or_C): register instances of `cstar_ring` ([#10555](https://github.com/leanprover-community/mathlib/pull/10555))
Register instances `cstar_ring ℝ` and `cstar_ring K` when `[is_R_or_C K]`

### [2021-12-01 02:41:28](https://github.com/leanprover-community/mathlib/commit/3f7d0cf)
chore(scripts): update nolints.txt ([#10563](https://github.com/leanprover-community/mathlib/pull/10563))
I am happy to remove some nolints for you!