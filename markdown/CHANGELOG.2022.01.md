### [2022-01-31 22:22:23](https://github.com/leanprover-community/mathlib/commit/731d93b)
feat(group_theory/sylow): the normalizer is self-normalizing ([#11638](https://github.com/leanprover-community/mathlib/pull/11638))
with hat tip to Thomas Browning for a proof on Zuplip.

### [2022-01-31 22:22:22](https://github.com/leanprover-community/mathlib/commit/5964343)
feat(data/equiv): define `mul_equiv_class` ([#10760](https://github.com/leanprover-community/mathlib/pull/10760))
This PR defines a class of types of multiplicative (additive) equivalences, along the lines of [#9888](https://github.com/leanprover-community/mathlib/pull/9888).

### [2022-01-31 20:42:48](https://github.com/leanprover-community/mathlib/commit/a0bb6ea)
feat(algebraic_geometry): Open covers of the fibred product. ([#11733](https://github.com/leanprover-community/mathlib/pull/11733))

### [2022-01-31 20:42:46](https://github.com/leanprover-community/mathlib/commit/6130e57)
feat(topology/metric_space/basic): add some lemmas about spheres ([#11719](https://github.com/leanprover-community/mathlib/pull/11719))

### [2022-01-31 20:42:45](https://github.com/leanprover-community/mathlib/commit/ca17a18)
feat(algebra/pointwise): introduce `canonically_ordered_comm_semiring` on `set_semiring` ... ([#11580](https://github.com/leanprover-community/mathlib/pull/11580))
... assuming multiplication is commutative (there is no `canonically_ordered_`~~comm~~`_semiring` structure).
Also prove the relevant `no_zero_divisors` and `covariant_class` properties of addition and multiplication.

### [2022-01-31 20:42:43](https://github.com/leanprover-community/mathlib/commit/719b7b0)
feat(set_theory/ordinal_arithmetic, set_theory/cardinal_ordinal): `deriv` and `aleph` are enumerators ([#10987](https://github.com/leanprover-community/mathlib/pull/10987))
We prove `deriv_eq_enum_fp`, `ord_aleph'_eq_enum_card`, and `ord_aleph_eq_enum_card`.

### [2022-01-31 19:55:53](https://github.com/leanprover-community/mathlib/commit/750f53c)
feat(analysis/seminorm): define the topology induced by a family of seminorms ([#11604](https://github.com/leanprover-community/mathlib/pull/11604))
Define the topology induced by a single seminorm and by a family of seminorms and show that boundedness of linear maps implies continuity.

### [2022-01-31 15:42:13](https://github.com/leanprover-community/mathlib/commit/ccbb848)
feat(set_theory/ordinal_arithmetic): `lt_add_of_limit` ([#11748](https://github.com/leanprover-community/mathlib/pull/11748))
Both `lt_mul_of_limit` and `lt_opow_of_limit` already existed, so this exclusion is odd to say the least.

### [2022-01-31 15:42:12](https://github.com/leanprover-community/mathlib/commit/c0be8dc)
feat(model_theory/basic): define quotient structures ([#11747](https://github.com/leanprover-community/mathlib/pull/11747))
Defines prestructures and quotient structures

### [2022-01-31 15:42:10](https://github.com/leanprover-community/mathlib/commit/792d3e5)
feat(group_theory/order_of_element): pow_eq_pow_iff_modeq ([#11737](https://github.com/leanprover-community/mathlib/pull/11737))
From flt-regular.

### [2022-01-31 15:42:09](https://github.com/leanprover-community/mathlib/commit/76b2a0e)
feat(group_theory/nilpotent): abelian iff nilpotency class ≤ 1 ([#11718](https://github.com/leanprover-community/mathlib/pull/11718))

### [2022-01-31 15:42:08](https://github.com/leanprover-community/mathlib/commit/ff02774)
feat(algebra/squarefree): norm_num extension for squarefree ([#11666](https://github.com/leanprover-community/mathlib/pull/11666))
Adds two methods for computing `squarefree`: an improved algorithm for VM computation of squarefreedom via the `min_sq_fac` function, and a proof procedure which follows the same evaluation strategy as a `norm_num` extension.

### [2022-01-31 15:42:06](https://github.com/leanprover-community/mathlib/commit/c04daaf)
feat(measure_theory): typeclass for measures positive on nonempty opens ([#11652](https://github.com/leanprover-community/mathlib/pull/11652))
Add a typeclass for measures positive on nonempty opens, migrate `is(_add?)_haar_measure` to this API.

### [2022-01-31 15:42:05](https://github.com/leanprover-community/mathlib/commit/d6440a8)
feat(group_theory/nilpotent): add lemmas about `G / center G` ([#11592](https://github.com/leanprover-community/mathlib/pull/11592))
in particular its nilpotency class and an induction principle based on
that.

### [2022-01-31 15:42:04](https://github.com/leanprover-community/mathlib/commit/06bb5b6)
feat(topology/nhds_set): define neighborhoods of a set ([#11520](https://github.com/leanprover-community/mathlib/pull/11520))
* Co-authored by @PatrickMassot
* From the sphere eversion project

### [2022-01-31 15:42:02](https://github.com/leanprover-community/mathlib/commit/366d13e)
feat(scripts/lint_style): Add a check for unfreeze_local_instances ([#11509](https://github.com/leanprover-community/mathlib/pull/11509))

### [2022-01-31 14:14:34](https://github.com/leanprover-community/mathlib/commit/ada43f0)
feat(order/hom/complete_lattice): Complete lattice homomorphisms ([#11741](https://github.com/leanprover-community/mathlib/pull/11741))
Define frame homs and complete lattice homs using the `fun_like` along with weaker homomorphisms that only preserve `Sup`, `Inf`.

### [2022-01-31 14:14:32](https://github.com/leanprover-community/mathlib/commit/08fed82)
feat(category_theory/preadditive): the Yoneda embedding for preadditive categories ([#11740](https://github.com/leanprover-community/mathlib/pull/11740))

### [2022-01-31 14:14:30](https://github.com/leanprover-community/mathlib/commit/323287e)
feat(data/polynomial/reverse): lemmas about evaluating reversed polynomials ([#11705](https://github.com/leanprover-community/mathlib/pull/11705))

### [2022-01-31 14:14:27](https://github.com/leanprover-community/mathlib/commit/bb2b58e)
feat(data/{nat,int}/parity): add division lemmas ([#11570](https://github.com/leanprover-community/mathlib/pull/11570))
Add lemmas of the form `even n → n / 2 * 2 = n` and `odd n → n / 2 * 2 + 1 = n`

### [2022-01-31 14:14:26](https://github.com/leanprover-community/mathlib/commit/6e016d2)
feat(linear_algebra/{tensor,exterior,clifford}_algebra): these algebras are graded by powers of the submodules of their generators ([#11542](https://github.com/leanprover-community/mathlib/pull/11542))
This shows that:
* The tensor and exterior algebras are `nat`-graded algebras, with each grade `n` corresponding to the submodule `(ι R).range ^ n`
* The clifford algebra is a superalgebra (`zmod 2`-graded algebra), with even and odd grades corresponding to even and odd powers of the submodule `(ι Q).range`
Eventually we'll also want to show that the tensor algebra is also graded with pieces in `pi_tensor_prod`, but that's a job for another time.

### [2022-01-31 12:36:17](https://github.com/leanprover-community/mathlib/commit/45cfb25)
refactor(order/bounded_order): Use `is_min`/`is_max` ([#11408](https://github.com/leanprover-community/mathlib/pull/11408))
Golf `order.bounded_order` and `data.set.basic` using `is_min`/`is_max`.

### [2022-01-31 11:21:34](https://github.com/leanprover-community/mathlib/commit/2e1d8d6)
feat(ring_theory/roots_of_unity): `fun_like` support ([#11735](https://github.com/leanprover-community/mathlib/pull/11735))
- feat(ring_theory/roots_of_unity): ring_hom_class
- oops these could've been monoid homs from the start

### [2022-01-31 11:21:33](https://github.com/leanprover-community/mathlib/commit/406719e)
feat(order/hom/lattice): Composition of lattice homs ([#11676](https://github.com/leanprover-community/mathlib/pull/11676))
Define `top_hom.comp`, `bot_hom.comp`, `sup_hom.comp`, `inf_hom.comp`, `lattice_hom.comp`, `bounded_lattice_hom.comp`, `order_hom.to_lattice_hom`.

### [2022-01-31 09:46:30](https://github.com/leanprover-community/mathlib/commit/16274f6)
chore(analysis/inner_product_space/lax_milgram): docs fixes ([#11745](https://github.com/leanprover-community/mathlib/pull/11745))
A couple of corrections, and a couple of additions of namespaces to docstrings so that they get hyperlinks when docgen is run.

### [2022-01-31 09:46:29](https://github.com/leanprover-community/mathlib/commit/4388743)
feat(algebra/algebra/basic): add 1-related lemmas for `aut` ([#11738](https://github.com/leanprover-community/mathlib/pull/11738))
from flt-regular

### [2022-01-31 09:46:28](https://github.com/leanprover-community/mathlib/commit/7468d8d)
feat(measure_theory/integral/lebesgue): weaken assumptions for with_density lemmas ([#11711](https://github.com/leanprover-community/mathlib/pull/11711))
We state more precise versions of some lemmas about the measure `μ.with_density f`, making it possible to remove some assumptions down the road. For instance, the lemma
```lean
  integrable g (μ.with_density f) ↔ integrable (λ x, g x * (f x).to_real) μ
```
currently requires the measurability of `g`, while we can completely remove it with the new lemmas.
We also make `lintegral` irreducible.

### [2022-01-31 09:46:27](https://github.com/leanprover-community/mathlib/commit/0c0ab69)
feat(topology/algebra/continuous_monoid_hom): Add `topological_group` instance ([#11707](https://github.com/leanprover-community/mathlib/pull/11707))
This PR proves that continuous monoid homs form a topological group.

### [2022-01-31 09:46:26](https://github.com/leanprover-community/mathlib/commit/b3ad3f2)
feat(data/set/lattice): review ([#11672](https://github.com/leanprover-community/mathlib/pull/11672))
* generalize `set.Union_coe_set` and `set.Inter_coe_set` to dependent functions;
* add `bInter_Union`, `sUnion_Union`;
* drop `sUnion_bUnion`, `sInter_bUnion`.

### [2022-01-31 09:17:53](https://github.com/leanprover-community/mathlib/commit/6319a23)
feat(number_theory/cyclotomic): simplify `ne_zero`s ([#11715](https://github.com/leanprover-community/mathlib/pull/11715))
For flt-regular.

### [2022-01-31 07:25:05](https://github.com/leanprover-community/mathlib/commit/8a67cf5)
feat(ring_theory/roots_of_unity): turn `is_primitive_root` into a member of `roots_of_unity` ([#11739](https://github.com/leanprover-community/mathlib/pull/11739))
from flt-regular

### [2022-01-31 00:40:09](https://github.com/leanprover-community/mathlib/commit/50cdb95)
fix(tactic/suggest): make `library_search` aware of definition of `ne` ([#11742](https://github.com/leanprover-community/mathlib/pull/11742))
`library_search` wasn't including results like `¬ a = b` to solve goals like `a ≠ b` and vice-versa.
Closes [#3428](https://github.com/leanprover-community/mathlib/pull/3428)

### [2022-01-30 23:01:38](https://github.com/leanprover-community/mathlib/commit/07735b8)
fix(tactic/squeeze_simp): "match failed" when `simp` works ([#11659](https://github.com/leanprover-community/mathlib/pull/11659))
Closes [#11196](https://github.com/leanprover-community/mathlib/pull/11196).

### [2022-01-30 18:57:22](https://github.com/leanprover-community/mathlib/commit/b0fc10a)
chore(ring_theory/polynomial/chebyshev): simplify argument using new `linear_combination` tactic ([#11736](https://github.com/leanprover-community/mathlib/pull/11736))
cc @agoldb10 @robertylewis

### [2022-01-30 15:41:10](https://github.com/leanprover-community/mathlib/commit/97f61df)
feat(group_theory/sylow): preimages of sylow groups ([#11722](https://github.com/leanprover-community/mathlib/pull/11722))

### [2022-01-30 14:09:00](https://github.com/leanprover-community/mathlib/commit/02c720e)
chore(*): Rename `prod_dvd_prod` ([#11734](https://github.com/leanprover-community/mathlib/pull/11734))
In [#11693](https://github.com/leanprover-community/mathlib/pull/11693) I introduced the counterpart for `multiset` of `finset.prod_dvd_prod`.  It makes sense for these to have the same name, but there's already a different lemma called `multiset.prod_dvd_prod`, so the new lemma was named `multiset.prod_dvd_prod_of_dvd` instead.  As discussed with @riccardobrasca and @ericrbg at [#11693](https://github.com/leanprover-community/mathlib/pull/11693), this PR brings the names of the two counterpart lemmas into alignment, and also renames `multiset.prod_dvd_prod` to something more informative.
Renaming as follows:
`multiset.prod_dvd_prod` to `multiset.prod_dvd_prod_of_le`
`finset.prod_dvd_prod` to `finset.prod_dvd_prod_of_dvd`

### [2022-01-30 11:14:54](https://github.com/leanprover-community/mathlib/commit/a248bef)
feat(data/pnat/basic): 0 < n as a fact ([#11729](https://github.com/leanprover-community/mathlib/pull/11729))

### [2022-01-30 10:31:37](https://github.com/leanprover-community/mathlib/commit/dde904e)
chore(ring_theory/localization) weaken hypothesis from field to comm_ring ([#11713](https://github.com/leanprover-community/mathlib/pull/11713))
also making `B` an explicit argument

### [2022-01-30 09:39:36](https://github.com/leanprover-community/mathlib/commit/1ea49d0)
feat(tactic/linear_combination): add tactic for combining equations ([#11646](https://github.com/leanprover-community/mathlib/pull/11646))
This new tactic attempts to prove a target equation by creating a linear combination of a list of equalities.  The name of this tactic is currently `linear_combination`, but I am open to other possible names.
An example of how to use this tactic is shown below:
```
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by linear_combination (h1, 1) (h2, -2)
```

### [2022-01-30 07:28:22](https://github.com/leanprover-community/mathlib/commit/73e45c6)
chore(analysis/normed_space/star): create new folder for normed star rings ([#11732](https://github.com/leanprover-community/mathlib/pull/11732))
This PR moves the file `analysis/normed_space/star.lean` to the new folder `analysis/normed_space/star` (where it of course becomes `basic.lean`).
I expect a lot of material about C*-algebras to land in this folder in the (hopefully) near future.

### [2022-01-30 05:38:03](https://github.com/leanprover-community/mathlib/commit/09d4f48)
chore(measure_theory/function/conditional_expectation): fix typo ([#11731](https://github.com/leanprover-community/mathlib/pull/11731))

### [2022-01-30 00:12:37](https://github.com/leanprover-community/mathlib/commit/af1290c)
feat(field_theory/ratfunc): rational functions as Laurent series ([#11276](https://github.com/leanprover-community/mathlib/pull/11276))

### [2022-01-29 21:10:10](https://github.com/leanprover-community/mathlib/commit/ff35218)
feat(analysis/convex/topology): add lemmas ([#11615](https://github.com/leanprover-community/mathlib/pull/11615))

### [2022-01-29 20:28:18](https://github.com/leanprover-community/mathlib/commit/4085363)
feat(number_theory/prime_counting): The prime counting function ([#9080](https://github.com/leanprover-community/mathlib/pull/9080))
With an eye to implementing [this proof](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.238002/near/251178921), I am adding a file to define the prime counting function and prove a simple upper bound on it.

### [2022-01-29 19:47:13](https://github.com/leanprover-community/mathlib/commit/74250a0)
chore(representation_theory/maschke): remove recover ([#11721](https://github.com/leanprover-community/mathlib/pull/11721))

### [2022-01-29 14:01:52](https://github.com/leanprover-community/mathlib/commit/49b8b91)
feat(data/fintype/order): `bool` is a boolean algebra ([#11694](https://github.com/leanprover-community/mathlib/pull/11694))
Provide the `boolean_algebra` instance for `bool` and use the machinery from `data.fintype.order` to deduce `complete_boolean_algebra bool` and `complete_linear_order bool`.

### [2022-01-29 03:47:21](https://github.com/leanprover-community/mathlib/commit/fc4e471)
feat(measure_theory/group/basic): make is_[add|mul]_[left|right]_invariant classes ([#11655](https://github.com/leanprover-community/mathlib/pull/11655))
* Simplify the definitions of these classes
* Generalize many results about topological groups to measurable groups (still to do in `group/prod`)
* Simplify some proofs
* Make function argument of `integral_mul_[left|right]_eq_self` explicit (otherwise it is hard to apply this lemma in case the function is not a variable)

### [2022-01-29 01:17:00](https://github.com/leanprover-community/mathlib/commit/44105f8)
feat(analysis/inner_product_space): proof of the Lax Milgram theorem ([#11491](https://github.com/leanprover-community/mathlib/pull/11491))
My work on the Lax Milgram theorem, as suggested by @hrmacbeth. Done following the [slides from Peter Howard (Texas A&M University)](https://www.math.tamu.edu/~phoward/m612/s20/elliptic2.pdf).
Closes [#10213](https://github.com/leanprover-community/mathlib/pull/10213).

### [2022-01-29 00:33:42](https://github.com/leanprover-community/mathlib/commit/f51d6bf)
chore(ring_theory/polynomial/tower): weaken comm_semiring hypothesis to semiring ([#11712](https://github.com/leanprover-community/mathlib/pull/11712))
…to semiring

### [2022-01-29 00:04:55](https://github.com/leanprover-community/mathlib/commit/601ea91)
feat(data/nat/mul_ind): generalise rec_on_prime to assume positivity ([#11714](https://github.com/leanprover-community/mathlib/pull/11714))
This makes the multiplicative induction principles slightly stronger, as the coprimality part can assume the given values are positive.

### [2022-01-28 16:51:38](https://github.com/leanprover-community/mathlib/commit/d58ce5a)
feat(number_theory/cyclotomic/zeta): add is_cyclotomic_extension.zeta ([#11695](https://github.com/leanprover-community/mathlib/pull/11695))
We add `is_cyclotomic_extension.zeta n A B`: any primitive `n`-th root of unity in a cyclotomic extension.
From flt-regular.

### [2022-01-28 16:51:36](https://github.com/leanprover-community/mathlib/commit/02c3146)
feat(analysis/complex): removable singularity theorem ([#11686](https://github.com/leanprover-community/mathlib/pull/11686))

### [2022-01-28 16:51:34](https://github.com/leanprover-community/mathlib/commit/7e8cb75)
refactor(algebra/linear_ordered_comm_group_with_zero, *): mostly take advantage of the new classes for `linear_ordered_comm_group_with_zero` ([#7645](https://github.com/leanprover-community/mathlib/pull/7645))
This PR continues the refactor of the `ordered` hierarchy, begun in [#7371](https://github.com/leanprover-community/mathlib/pull/7371).
In this iteration, I weakened the assumptions of the lemmas in `ordered_group`.  The bulk of the changes are in the two files
* `algebra/ordered_monoid_lemmas`
* `algebra/ordered_group`
while the remaining files have been edited mostly to accommodate for name/assumption changes.
I have tried to be careful to maintain the **exact** assumptions of each one of the `norm_num` and `linarith` lemmas.  For this reason, some lemmas have a proof that is simply an application of a lemma with weaker assumptions.  The end result is that no lemma whose proof involved a call to `norm_num` or `linarith` broke.

### [2022-01-28 15:19:21](https://github.com/leanprover-community/mathlib/commit/dddf6eb)
feat(data/fintype/order): More and better instances ([#11702](https://github.com/leanprover-community/mathlib/pull/11702))
In a fintype, this allows to promote 
* `distrib_lattice` to `complete_distrib_lattice`
* `boolean_algebra` to `complete_boolean_algebra`
Also strengthen
* `fintype.to_order_bot`
* `fintype.to_order_top`
* `fintype.to_bounded_order`
* `complete_linear_order.to_conditionally_complete_linear_order_bot`

### [2022-01-28 15:19:20](https://github.com/leanprover-community/mathlib/commit/6ca08e8)
feat(algebra/ne_zero): add `coe_trans` instance ([#11700](https://github.com/leanprover-community/mathlib/pull/11700))
This is super-useful for `flt_regular`, meaning we don't have to write all of our lemmata as `ne_zero ((n : ℕ) : R)`.

### [2022-01-28 15:19:19](https://github.com/leanprover-community/mathlib/commit/de27bfc)
feat(algebra/big_operators/{basic,multiset}): two `multiset.prod` lemmas ([#11693](https://github.com/leanprover-community/mathlib/pull/11693))
Two lemmas suggested by Riccardo Brasca on [#11572](https://github.com/leanprover-community/mathlib/pull/11572):
`to_finset_prod_dvd_prod`: `S.to_finset.prod id ∣ S.prod`
`prod_dvd_prod_of_dvd`: For any `S : multiset α`, if `∀ a ∈ S, g1 a ∣ g2 a` then `S.prod g1 ∣ S.prod g2` (a counterpart to `finset.prod_dvd_prod`)

### [2022-01-28 15:19:17](https://github.com/leanprover-community/mathlib/commit/c50a60d)
feat(analysis/convex/specific_functions): sin is strictly concave ([#11688](https://github.com/leanprover-community/mathlib/pull/11688))

### [2022-01-28 15:19:16](https://github.com/leanprover-community/mathlib/commit/92c64c4)
feat(group_theory/nilpotent): add upper_central_series_eq_top_iff_nilpotency_class_le ([#11670](https://github.com/leanprover-community/mathlib/pull/11670))
and the analogue for the lower central series.

### [2022-01-28 15:19:15](https://github.com/leanprover-community/mathlib/commit/7a485b1)
feat(topology/continuous_function/algebra): `C(α, β)` is a topological group ([#11665](https://github.com/leanprover-community/mathlib/pull/11665))
This PR proves that `C(α, β)` is a topological group. I had to borrow the fix from [#11229](https://github.com/leanprover-community/mathlib/pull/11229) to avoid a diamond.

### [2022-01-28 15:19:14](https://github.com/leanprover-community/mathlib/commit/113ab32)
feat(ring_theory/power_series/basic): API about inv ([#11617](https://github.com/leanprover-community/mathlib/pull/11617))
Also rename protected lemmas
`mul_inv`  to `mul_inv_cancel`
`inv_mul` to `inv_mul_cancel`

### [2022-01-28 15:19:13](https://github.com/leanprover-community/mathlib/commit/36dd6a6)
feat(algebra/squarefree): squarefree iff no square irreducible divisors ([#11544](https://github.com/leanprover-community/mathlib/pull/11544))

### [2022-01-28 15:19:11](https://github.com/leanprover-community/mathlib/commit/fb9c5d3)
feat(cyclotomic/basic): diverse roots of unity lemmas ([#11473](https://github.com/leanprover-community/mathlib/pull/11473))
From flt-regular.

### [2022-01-28 15:19:10](https://github.com/leanprover-community/mathlib/commit/91a1afb)
feat(algebraic_geometry): The function field is the fraction field of stalks ([#11129](https://github.com/leanprover-community/mathlib/pull/11129))

### [2022-01-28 15:19:08](https://github.com/leanprover-community/mathlib/commit/0b6330d)
feat(data/finsupp/interval): Finitely supported functions to a locally finite order are locally finite ([#10930](https://github.com/leanprover-community/mathlib/pull/10930))
... when the codomain itself is locally finite.
This allows getting rid of `finsupp.Iic_finset`.

### [2022-01-28 13:31:09](https://github.com/leanprover-community/mathlib/commit/445be96)
fix(tactic/squeeze): `squeeze_simp` providing invalid suggestions ([#11696](https://github.com/leanprover-community/mathlib/pull/11696))
`squeeze_simp` was previously permuting the lemmas passed to `simp`, which caused failures in cases where the lemma order mattered. The fix is to ensure that `squeeze_simp` does not change the order of passed lemmas.
Closes [#3097](https://github.com/leanprover-community/mathlib/pull/3097)

### [2022-01-28 13:31:08](https://github.com/leanprover-community/mathlib/commit/3837abc)
feat(data/list/*): subperm_singleton_iff ([#11680](https://github.com/leanprover-community/mathlib/pull/11680))

### [2022-01-28 13:31:06](https://github.com/leanprover-community/mathlib/commit/1e44add)
feat(order/filter/countable_Inter): review ([#11673](https://github.com/leanprover-community/mathlib/pull/11673))
- drop `_sets` in more names;
- add `filter.of_countable_Inter` and instances for
  `filter.map`/`filter.comap`;
- add docs.

### [2022-01-28 13:31:05](https://github.com/leanprover-community/mathlib/commit/680733c)
feat(order/hom/basic): `compl` as a dual order isomorphism ([#11630](https://github.com/leanprover-community/mathlib/pull/11630))

### [2022-01-28 13:31:04](https://github.com/leanprover-community/mathlib/commit/ff241e1)
feat(order/max): Predicate for minimal/maximal elements, typeclass for orders without bottoms ([#11618](https://github.com/leanprover-community/mathlib/pull/11618))
This defines
* `is_min`: Predicate for a minimal element
* `is_max`: Predicate for a maximal element
* `no_bot_order`: Predicate for an order without bottoms
* `no_top_order`: Predicate for an order without tops

### [2022-01-28 13:31:02](https://github.com/leanprover-community/mathlib/commit/2fa5977)
feat(category_theory/bicategory/natural_transformation): define oplax natural transformations ([#11404](https://github.com/leanprover-community/mathlib/pull/11404))
This PR define oplax natural transformations between oplax functors.
We give a composition and a category structure on oplax natural transformations.

### [2022-01-28 13:31:00](https://github.com/leanprover-community/mathlib/commit/b9db169)
chore(order/locally_finite): fill in finset interval API ([#11338](https://github.com/leanprover-community/mathlib/pull/11338))
A bunch of statements about finset intervals, mimicking the set interval API and mostly proved using it. `simp` attributes are  chosen as they were for sets. Also some golf.

### [2022-01-28 13:03:39](https://github.com/leanprover-community/mathlib/commit/924aab1)
feat(ring_theory/polynomial/eisenstein): add miscellaneous results about Eisenstein polynomials ([#11697](https://github.com/leanprover-community/mathlib/pull/11697))
Miscellaneous results about Eisenstein polynomials
From flt-regular.

### [2022-01-28 11:11:22](https://github.com/leanprover-community/mathlib/commit/e290b29)
feat(data/quot): add subsingleton instances ([#11668](https://github.com/leanprover-community/mathlib/pull/11668))

### [2022-01-28 08:38:09](https://github.com/leanprover-community/mathlib/commit/bf347f9)
feat(algebraic_geometry): Fiber products of schemes ([#10605](https://github.com/leanprover-community/mathlib/pull/10605))

### [2022-01-28 07:26:07](https://github.com/leanprover-community/mathlib/commit/67dcdef)
feat(data/mv_polynomial/derivation): derivations of `mv_polynomial`s ([#9145](https://github.com/leanprover-community/mathlib/pull/9145))

### [2022-01-28 06:58:36](https://github.com/leanprover-community/mathlib/commit/6687cf1)
feat(group_theory/sylow): `fintype (sylow p H)` from `fintype (sylow p G)` ([#11664](https://github.com/leanprover-community/mathlib/pull/11664))
If the number of Sylow `p`-subgroups of `G` is finite, then the number of Sylow `p`-subgroups of `H` is finite.

### [2022-01-28 03:07:32](https://github.com/leanprover-community/mathlib/commit/f5d63f9)
feat(topology/category/Compactum): forget creates limits ([#11690](https://github.com/leanprover-community/mathlib/pull/11690))
Will likely be used in LTE.

### [2022-01-28 00:40:24](https://github.com/leanprover-community/mathlib/commit/24cfb88)
chore(set_theory/ordinal_arithmetic): Golf some instances of `lt_irrefl _ h` down to `h.false` ([#11699](https://github.com/leanprover-community/mathlib/pull/11699))

### [2022-01-28 00:40:23](https://github.com/leanprover-community/mathlib/commit/bac0f55)
chore(order/conditionally_complete_lattice): move code to a new file ([#11698](https://github.com/leanprover-community/mathlib/pull/11698))
This is the first step towards adding a `complete_lattice` instance for `Icc`/`interval`.

### [2022-01-27 23:05:41](https://github.com/leanprover-community/mathlib/commit/21cea47)
feat(analysis/special_functions/log): log of natural power ([#11685](https://github.com/leanprover-community/mathlib/pull/11685))
The rpow versions are already present, but the natural/integer versions can also be very helpful (eg for squares).

### [2022-01-27 23:05:40](https://github.com/leanprover-community/mathlib/commit/79e6cb0)
feat(order/succ_pred/relation): `succ`/`pred` inductions on relations ([#11518](https://github.com/leanprover-community/mathlib/pull/11518))
* Rename file `order.succ_pred` -> `order.succ_pred.basic`
* Generalize induction principles `succ.rec` and `pred.rec`, make the argument order more "induction-like" and add the attribute `@[elab_as_eliminator]`
* Proof properties about `refl_trans_gen` and `trans_gen` in a `is_succ_archimedean` order.
* Proof some monotonicity properties of closure operations.

### [2022-01-27 23:05:38](https://github.com/leanprover-community/mathlib/commit/0a721cc)
feat(data/nat): a predicate for prime powers ([#11313](https://github.com/leanprover-community/mathlib/pull/11313))
Adds a predicate for prime powers, in preparation for defining the von Mangoldt function.
cc @stuart-presnell since you might be needing this material soon, and @jcommelin if you have thoughts about generalising this to rings/UFDs?

### [2022-01-27 22:03:42](https://github.com/leanprover-community/mathlib/commit/7458476)
chore(set_theory/ordinal_arithmetic): golf proof into term mode ([#11691](https://github.com/leanprover-community/mathlib/pull/11691))

### [2022-01-27 20:16:32](https://github.com/leanprover-community/mathlib/commit/02c08d9)
doc(polynomial/eval): why map_ring_hom can't replace map ([#11537](https://github.com/leanprover-community/mathlib/pull/11537))

### [2022-01-27 10:01:14](https://github.com/leanprover-community/mathlib/commit/05e1845)
feat(archive/100-theorems-list): add proof of the solution of the cubic ([#11635](https://github.com/leanprover-community/mathlib/pull/11635))
Gives solution to the cubic equation, based on the cardano's formula. The base field should have cube root of unity and characteristic neither 2 nor 3.

### [2022-01-27 05:30:47](https://github.com/leanprover-community/mathlib/commit/0844597)
feat(set_theory/ordinal_arithmetic): Update header ([#11681](https://github.com/leanprover-community/mathlib/pull/11681))
Added definitions from my previous PRs, and made myself an author.

### [2022-01-27 01:40:11](https://github.com/leanprover-community/mathlib/commit/a6ace8c)
feat(set_theory/ordinal_arithmetic): Proved `sup_eq_lsub_iff_lt_sup` ([#11660](https://github.com/leanprover-community/mathlib/pull/11660))

### [2022-01-26 23:35:18](https://github.com/leanprover-community/mathlib/commit/92ee748)
chore(analysis/complex/cauchy_integral): use `dslope` to golf a proof ([#11675](https://github.com/leanprover-community/mathlib/pull/11675))

### [2022-01-26 23:35:16](https://github.com/leanprover-community/mathlib/commit/a1e1ffd)
feat(order/filter): +1 version of `mem_inf_principal` ([#11674](https://github.com/leanprover-community/mathlib/pull/11674))

### [2022-01-26 23:35:15](https://github.com/leanprover-community/mathlib/commit/52e9fd5)
chore(*): don't use tactic internal lemmas in proofs ([#11641](https://github.com/leanprover-community/mathlib/pull/11641))
Some lemmas that are intended as internals to a tactic get picked up by library search and end up in proofs.
We replace a few of these tactic lemma uses with actual library lemmas which should be more maintainable, de-coupling tactic internals from the actual library.

### [2022-01-26 22:45:31](https://github.com/leanprover-community/mathlib/commit/577e3a2)
chore(topology/algebra/uniform_group): Remove newline after docstring ([#11671](https://github.com/leanprover-community/mathlib/pull/11671))
Yael pointed out that [#11662](https://github.com/leanprover-community/mathlib/pull/11662) added an erroneous newline after a docstring. This PR removes that newline.

### [2022-01-26 20:52:57](https://github.com/leanprover-community/mathlib/commit/946454a)
feat(data/nat/factorization): various theorems on factorization and division ([#11663](https://github.com/leanprover-community/mathlib/pull/11663))

### [2022-01-26 20:14:54](https://github.com/leanprover-community/mathlib/commit/97e01cd)
feat(group_theory/free_abelian_group_finsupp): various equiv.of_free_*_group lemmas ([#11469](https://github.com/leanprover-community/mathlib/pull/11469))
Namely `equiv.of_free_abelian_group_linear_equiv`,
`equiv.of_free_abelian_group_equiv` and `equiv.of_free_group_equiv`

### [2022-01-26 17:10:48](https://github.com/leanprover-community/mathlib/commit/8fbc009)
feat(data/{dfinsupp,finsupp}/basic): `fun_like` instances for `Π₀ i, α i` and `ι →₀ α` ([#11667](https://github.com/leanprover-community/mathlib/pull/11667))
This provides the `fun_like` instances for `finsupp` and `dfinsupp` and deprecates the lemmas that are now provided by the `fun_like` API.

### [2022-01-26 17:10:46](https://github.com/leanprover-community/mathlib/commit/c447a31)
feat(algebraic_geometry): Stalk is localization of affine open.  ([#11640](https://github.com/leanprover-community/mathlib/pull/11640))

### [2022-01-26 15:22:43](https://github.com/leanprover-community/mathlib/commit/b8fcac5)
feat(data/nat/basic): three small `dvd_iff...` lemmas ([#11669](https://github.com/leanprover-community/mathlib/pull/11669))
Three biconditionals for proving `d ∣ n`

### [2022-01-26 13:30:01](https://github.com/leanprover-community/mathlib/commit/c5a8a81)
refactor(topology/algebra/uniform_group): Use `to_additive`. ([#11662](https://github.com/leanprover-community/mathlib/pull/11662))
This PR refactors `topology/algebra/uniform_group` to use `to_additive`.

### [2022-01-26 13:30:00](https://github.com/leanprover-community/mathlib/commit/5472f0a)
feat(group_theory/subgroup/basic): add lemmas related to map, comap, normalizer ([#11637](https://github.com/leanprover-community/mathlib/pull/11637))
which are useful when `H < K < G` and one needs to move from `subgroup
G` to `subgroup K`

### [2022-01-26 13:29:59](https://github.com/leanprover-community/mathlib/commit/2b25723)
feat(group_theory/sylow): add characteristic_of_normal ([#11636](https://github.com/leanprover-community/mathlib/pull/11636))
A normal sylow subgroup is characteristic.

### [2022-01-26 13:29:58](https://github.com/leanprover-community/mathlib/commit/1a72f88)
feat(analysis/inner_product_space/basic): isometries and orthonormal families ([#11631](https://github.com/leanprover-community/mathlib/pull/11631))
Add various lemmas and definitions about the action of isometries on
orthonormal families of vectors.  An isometry preserves the property
of being orthonormal; a linear map sending an orthonormal basis to an
orthonormal family is a linear isometry, and a linear equiv sending an
orthonormal basis to an orthonormal family is a linear isometry equiv.
A definition `orthonormal.equiv` is provided that uses `basis.equiv`
to provide a linear isometry equiv mapping a given orthonormal basis
to another given orthonormal basis, and lemmas are provided analogous
to those for `basis.equiv` (`orthonormal.map_equiv` isn't a `simp`
lemma because `simp` can prove it).

### [2022-01-26 13:29:57](https://github.com/leanprover-community/mathlib/commit/631f339)
feat(measure_theory/measure/haar_lebesgue): a density point for closed balls is a density point for rescalings of arbitrary sets ([#11620](https://github.com/leanprover-community/mathlib/pull/11620))
Consider a point `x` in a finite-dimensional real vector space with a Haar measure, at which a set `s` has density one, with respect to closed balls (i.e., a Lebesgue density point of `s`). Then `s` has also density one at `x` with respect to any measurable set `t`: the proportion of points in `s` belonging to a rescaled copy `{x} + r • t` of `t` tends to one as `r` tends to zero. In particular, `s ∩ ({x} + r • t)` is nonempty for small enough `r`.

### [2022-01-26 13:29:54](https://github.com/leanprover-community/mathlib/commit/590b5eb)
feat(analysis/seminorm): The norm as a seminorm, balanced and absorbent lemmas ([#11487](https://github.com/leanprover-community/mathlib/pull/11487))
This
* defines `norm_seminorm`, the norm as a seminorm. This is useful to translate seminorm lemmas to norm lemmas
* proves many lemmas about `balanced`, `absorbs`, `absorbent`
* generalizes many lemmas about the aforementioned predicates. In particular, `one_le_gauge_of_not_mem` now takes `(star_convex ℝ 0 s) (absorbs ℝ s {x})` instead of `(convex ℝ s) ((0 : E) ∈ s) (is_open s)`. The new `star_convex` lemmas justify that it's a generalization.
* proves `star_convex_zero_iff`
* proves `ne_zero_of_norm_ne_zero` and friends
* makes `x` implicit in `convex.star_convex`
* renames `balanced.univ` to `balanced_univ`

### [2022-01-26 13:29:53](https://github.com/leanprover-community/mathlib/commit/573ca83)
feat(analysis/seminorm): add some lemmas for seminorm balls ([#11471](https://github.com/leanprover-community/mathlib/pull/11471))
Add some lemmas for seminorm balls.

### [2022-01-26 13:29:52](https://github.com/leanprover-community/mathlib/commit/07d8ca6)
feat(combinatorics/configuration): Formula for cardinality of a projective plane ([#11462](https://github.com/leanprover-community/mathlib/pull/11462))
This PR proves the formula for the cardinality of a projective plane in terms of the order.

### [2022-01-26 11:53:03](https://github.com/leanprover-community/mathlib/commit/7f0f3f1)
feat(algebra/order/hom/monoid): Ordered monoid/group homomorphisms ([#11633](https://github.com/leanprover-community/mathlib/pull/11633))
Define
* `order_add_monoid_hom` with notation `→+o`
* `order_monoid_hom` with notation `→*o`
* `order_monoid_with_zero_hom` with notation `→*₀o`
and their corresponding hom classes.
Also add a few missing API lemmas in `algebra.group.hom` and `order.hom.basic`.

### [2022-01-26 11:25:56](https://github.com/leanprover-community/mathlib/commit/20aae83)
feat(order/hom/lattice): Lattice homomorphisms ([#11610](https://github.com/leanprover-community/mathlib/pull/11610))
This defines (bounded) lattice homomorphisms using the `fun_like` along with weaker homomorphisms that only preserve `sup`, `inf`, `top`, `bot`.

### [2022-01-26 10:04:22](https://github.com/leanprover-community/mathlib/commit/09c6ce8)
feat(group_theory/subgroup/basic): add normalizer_condition definition ([#11587](https://github.com/leanprover-community/mathlib/pull/11587))
and an equivalent formula that is a bit easier to work with.

### [2022-01-26 09:10:25](https://github.com/leanprover-community/mathlib/commit/c294e4b)
feat(topology/*): replace some `a < b` assumptions with `a ≠ b` ([#11650](https://github.com/leanprover-community/mathlib/pull/11650))

### [2022-01-25 23:46:56](https://github.com/leanprover-community/mathlib/commit/20a461f)
feat(algebra/big_operators/order): The size of a finset of disjoint finsets is less than the size of its union ([#11654](https://github.com/leanprover-community/mathlib/pull/11654))
Prove `card_le_card_bUnion`, its corollary `card_le_card_bUnion_add_card_fiber` where we drop the nonemptiness condition in exchange of a `+` card of the fiber of `∅` on the RHS, and its useful special case `card_le_card_bUnion_add_one`.

### [2022-01-25 22:24:52](https://github.com/leanprover-community/mathlib/commit/b237af5)
refactor(set_theory/ordinal_arithmetic): Rename `lsub_le_iff_lt` to `lsub_le` ([#11661](https://github.com/leanprover-community/mathlib/pull/11661))
This way, it directly corresponds to `sup_le`. Ditto for `blsub_le_iff_lt`.

### [2022-01-25 22:24:51](https://github.com/leanprover-community/mathlib/commit/b0a1812)
chore(data/buffer/parser/numeral): fix backticks ([#11658](https://github.com/leanprover-community/mathlib/pull/11658))

### [2022-01-25 22:24:50](https://github.com/leanprover-community/mathlib/commit/033dd3c)
feat(analysis/special_functions/complex/circle): `real.angle.exp_map_circle` ([#11627](https://github.com/leanprover-community/mathlib/pull/11627))
Add a version of `exp_map_circle` that applies to a `real.angle`
argument.

### [2022-01-25 22:24:49](https://github.com/leanprover-community/mathlib/commit/f5b11ad)
feat(algebra/lie/{nilpotent,of_associative}): a representation of an associative algebra gives a representation of a Lie algebra ([#11558](https://github.com/leanprover-community/mathlib/pull/11558))
The lemma `lie_algebra.non_trivial_center_of_is_nilpotent` is unrelated.

### [2022-01-25 20:59:08](https://github.com/leanprover-community/mathlib/commit/99608cc)
feat(group_theory/sub{monoid,group}, linear_algebra/basic): add `supr_induction` for `submonoid`, `add_submonoid`, `subgroup`, `add_subgroup`, and `submodule` ([#11556](https://github.com/leanprover-community/mathlib/pull/11556))
This also adds dependent versions, which match the style of the dependent versions of `submodule.span_induction` and `submonoid.closure_induction` in [#11555](https://github.com/leanprover-community/mathlib/pull/11555).
Primarily it's the group and module versions that are useful here, as they remove the inv and smul obligations that would appear if using `closure_induction` or `span_induction`.

### [2022-01-25 20:59:07](https://github.com/leanprover-community/mathlib/commit/25d1341)
feat(group_theory/sub{monoid,group}, linear_algebra/basic): remove specialization to subtypes from dependent recursors ([#11555](https://github.com/leanprover-community/mathlib/pull/11555))
The following recursors (the first of which was added in [#4984](https://github.com/leanprover-community/mathlib/pull/4984)) are more generally applicable than to subtypes alone:
* `submonoid.closure_induction'`
* `add_submonoid.closure_induction'`
* `subgroup.closure_induction'`
* `add_subgroup.closure_induction'`
* `submodule.span_induction'`
Now that these live right next to their non-dependent version, there is little need to repeat the docstring.

### [2022-01-25 20:59:06](https://github.com/leanprover-community/mathlib/commit/7e09827)
feat(analysis/inner_product_space/adjoint): matrix and linear map adjoints agree ([#11551](https://github.com/leanprover-community/mathlib/pull/11551))

### [2022-01-25 20:59:04](https://github.com/leanprover-community/mathlib/commit/84f2e93)
feat(group_theory/free_abelian_group): add free_abelian_group.basis ([#11465](https://github.com/leanprover-community/mathlib/pull/11465))
Although a statement about `free_abelian_group`, it lives in
`free_abelian_group_finsupp` because it uses the isomorphism between
`free_abelian_group X` and `X →₀ ℤ`

### [2022-01-25 19:51:28](https://github.com/leanprover-community/mathlib/commit/009cec0)
feat(set_theory/cardinal_ordinal): Aleph is positive ([#11657](https://github.com/leanprover-community/mathlib/pull/11657))

### [2022-01-25 17:30:28](https://github.com/leanprover-community/mathlib/commit/6184db1)
feat(topology/algebra/mul_action2): quotient by a properly discontinuous group action is t2 ([#10465](https://github.com/leanprover-community/mathlib/pull/10465))
We prove that the quotient of a Hausdorff (t2) locally compact space by a properly discontinuous group action is itself Hausdorff.

### [2022-01-25 13:19:58](https://github.com/leanprover-community/mathlib/commit/4d761f4)
feat(algebra/group/hom): Notation for `monoid_with_zero_hom` ([#11632](https://github.com/leanprover-community/mathlib/pull/11632))
Introduce notation `→*₀` for `monoid_with_zero_hom` and use it everywhere.

### [2022-01-25 12:25:39](https://github.com/leanprover-community/mathlib/commit/1b3da83)
feat(combinatorics/simple_graph/coloring): add inequalities from embeddings ([#11548](https://github.com/leanprover-community/mathlib/pull/11548))
Also add a lemma that the chromatic number of an infinite complete graph is zero (i.e., it needs infinitely many colors), as suggested by @arthurpaulino.

### [2022-01-25 12:25:38](https://github.com/leanprover-community/mathlib/commit/158c0ea)
feat(group_theory/abelianization): add abelianization_of_comm_group ([#11467](https://github.com/leanprover-community/mathlib/pull/11467))

### [2022-01-25 10:49:34](https://github.com/leanprover-community/mathlib/commit/494f719)
feat(data/fun_like): define `embedding_like` and `equiv_like` ([#10759](https://github.com/leanprover-community/mathlib/pull/10759))
These extend `fun_like` with a proof of injectivity resp. an inverse.
The number of new generic lemmas is quite low at the moment, so their use is more in defining derived classes such as `mul_equiv_class`.

### [2022-01-25 10:04:17](https://github.com/leanprover-community/mathlib/commit/6b32241)
feat(model_theory/basic): Terms, formulas, and definable sets ([#11067](https://github.com/leanprover-community/mathlib/pull/11067))
Defines first-order terms, formulas, sentences and theories
Defines the boolean algebra of definable sets
(Several of these definitions are based on those from the flypitch project.)

### [2022-01-25 08:35:58](https://github.com/leanprover-community/mathlib/commit/4883d11)
feat(README.md): add Kyle Miller as new maintainer ([#11653](https://github.com/leanprover-community/mathlib/pull/11653))

### [2022-01-25 07:42:56](https://github.com/leanprover-community/mathlib/commit/bf71feb)
feat(number_theory/quadratic_reciprocity): generalise legendre_sym to allow integer first argument ([#11573](https://github.com/leanprover-community/mathlib/pull/11573))
Talking about the legendre symbol of -1 mod p is quite natural, so we generalize to include this case.
So far in a minimal way without changing any existing lemmas

### [2022-01-25 07:15:51](https://github.com/leanprover-community/mathlib/commit/f7a597a)
feat(group_theory/nilpotent): add nilpotency_class inequalities ([#11585](https://github.com/leanprover-community/mathlib/pull/11585))
Every theorem that proves `nilpotency G'` (e.g. for subgroups, images,
preimages) should be accompanied by a lemma relating their
`nilpotency_class`, so add thse lmmeas for subgroups and preimages.
Also add nilpotency lemmas for surjective homomorphisms and quotions,
including nilpotency_class lemmas.

### [2022-01-25 06:08:03](https://github.com/leanprover-community/mathlib/commit/f278663)
feat(README.md): add Frédéric Dupuis as new maintainer ([#11651](https://github.com/leanprover-community/mathlib/pull/11651))

### [2022-01-25 05:11:24](https://github.com/leanprover-community/mathlib/commit/b3cd0e6)
chore(order/filter, *): enhancing `filter_upwards` tactic ([#11624](https://github.com/leanprover-community/mathlib/pull/11624))

### [2022-01-25 03:33:34](https://github.com/leanprover-community/mathlib/commit/8cc2ff4)
refactor(order/{bounded, rel_classes}): Moved `bounded` into the `set` namespace ([#11594](https://github.com/leanprover-community/mathlib/pull/11594))
As per the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/bounded.2Emono). Closes [#11589](https://github.com/leanprover-community/mathlib/pull/11589).

### [2022-01-25 03:33:32](https://github.com/leanprover-community/mathlib/commit/b834415)
chore(topology/metric_space/gromov_hausdorff): Golf some theorems ([#11591](https://github.com/leanprover-community/mathlib/pull/11591))

### [2022-01-25 03:33:31](https://github.com/leanprover-community/mathlib/commit/88479be)
feat(algebra/big_operators/basic): add lemma `finset.prod_dvd_prod` ([#11521](https://github.com/leanprover-community/mathlib/pull/11521))
For any `S : finset α`, if `∀ a ∈ S, g1 a ∣ g2 a` then `S.prod g1 ∣ S.prod g2`.

### [2022-01-25 01:56:07](https://github.com/leanprover-community/mathlib/commit/4f5d6ac)
refactor(tactic/interactive): rename tactic.interactive.triv to tactic.interactive.trivial' ([#11643](https://github.com/leanprover-community/mathlib/pull/11643))
The difference between `tactic.interactive.trivial` and `tactic.interactive.triv` is that the latter expands only reducible constants; the first uses `tactic.triv` and the latter uses `tactic.triv'`. This name change is to improve consistency.
Also (slipping in a new feature) add `tactic.interactive.triv`, which is the old `tactic.interactive.triv` but does not run `contradiction`. This is useful for teaching.

### [2022-01-24 22:53:51](https://github.com/leanprover-community/mathlib/commit/0d172ba)
feat(README.md): add Riccardo Brasca as new maintainer ([#11647](https://github.com/leanprover-community/mathlib/pull/11647))
Add myself as new maintainer and test my superpowers :)

### [2022-01-24 22:53:50](https://github.com/leanprover-community/mathlib/commit/12fde09)
feat(data/finset/finsupp): Finitely supported product of finsets ([#11639](https://github.com/leanprover-community/mathlib/pull/11639))
Define
* `finsupp.indicator`: Similar to `finsupp.on_finset` except that it only requires a partially defined function. This is more compatible with `finset.pi`.
* `finset.finsupp : finset ι → (ι → finset α) → finset (ι →₀ α)`: Finitely supported product of finsets.
* `finsupp.pi : (ι →₀ finset α) → finset (ι →₀ α)`: The set of finitely supported functions whose `i`-th value lies in the `i`-th of a given `finset`-valued `finsupp`.

### [2022-01-24 21:01:29](https://github.com/leanprover-community/mathlib/commit/32052b8)
chore(ci): remove working directory on self-hosted ([#11645](https://github.com/leanprover-community/mathlib/pull/11645))
Mathlib now takes several gigabytes to build.  This addresses some of the space issues on the CI machines.

### [2022-01-24 21:01:26](https://github.com/leanprover-community/mathlib/commit/511aa35)
feat(algebra/pointwise): add partial order to `set_semiring` ([#11567](https://github.com/leanprover-community/mathlib/pull/11567))
This PR introduces the natural inclusion order on sets on `set_semiring`.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Ordered.20semirings)

### [2022-01-24 21:01:25](https://github.com/leanprover-community/mathlib/commit/9e799a0)
feat(algebra/pointwise): Scalar multiplication lemmas ([#11486](https://github.com/leanprover-community/mathlib/pull/11486))
This proves a bunch of lemmas about pointwise scalar multiplication of sets, moves `has_vsub` to `algebra.group.defs` and pointwise `vsub` lemmas to `algebra.pointwise`.
I'm also adding a few sections because having `{s t : set α}` is nice for multiplication but not for scalar multiplication.

### [2022-01-24 20:18:07](https://github.com/leanprover-community/mathlib/commit/6aea8ac)
chore(probability_theory/stopping): fix names in documentation ([#11644](https://github.com/leanprover-community/mathlib/pull/11644))

### [2022-01-24 18:04:16](https://github.com/leanprover-community/mathlib/commit/1bbed96)
doc(tactic/interactive): mention triv uses contradiction ([#11502](https://github.com/leanprover-community/mathlib/pull/11502))
Adding the fact that `triv` tries `contradiction` to the docstring for `triv`.

### [2022-01-24 16:03:59](https://github.com/leanprover-community/mathlib/commit/eccd8dd)
feat(algebra/lie/nilpotent): generalise lower central series to start with given Lie submodule ([#11625](https://github.com/leanprover-community/mathlib/pull/11625))
The advantage of this approach is that we can regard the terms of the lower central series of a Lie submodule as Lie submodules of the enclosing Lie module.
In particular, this is useful when considering the lower central series of a Lie ideal.

### [2022-01-24 16:03:56](https://github.com/leanprover-community/mathlib/commit/a631839)
feat(analysis/special_functions/pow): add nnreal variant of rpow_pos ([#11619](https://github.com/leanprover-community/mathlib/pull/11619))
This matches the lemma for ennreal.

### [2022-01-24 16:03:55](https://github.com/leanprover-community/mathlib/commit/155c330)
feat(analysis/convex/{basic,function}): add lemmas, golf ([#11608](https://github.com/leanprover-community/mathlib/pull/11608))
* add `segment_subset_iff`, `open_segment_subset_iff`, use them to golf some proofs;
* add `mem_segment_iff_div`, `mem_open_segment_iff_div`, use the
  former in the proof of `convex_iff_div`;
* move the proof of `mpr` in `convex_on_iff_convex_epigraph` to a new
  lemma;
* prove that the strict epigraph of a convex function include the open
  segment provided that one of the endpoints is in the strong epigraph
  and the other is in the epigraph; use it in the proof of
  `convex_on.convex_strict_epigraph`.

### [2022-01-24 16:03:53](https://github.com/leanprover-community/mathlib/commit/a52ce83)
feat(combinatorics/configuration): The order of a projective plane is at least 2 ([#11550](https://github.com/leanprover-community/mathlib/pull/11550))
This PR proves that the order of a projective plane is strictly larger than 1.

### [2022-01-24 16:03:52](https://github.com/leanprover-community/mathlib/commit/9150268)
feat (algebraic_geometry): Constructions of fibred products of schemes ([#11450](https://github.com/leanprover-community/mathlib/pull/11450))
This is the first half of the PRs about constructing fibred products of schemes, where we
construct all the relevant schemes and morphisms but yet to show that they are actually
fibred products.

### [2022-01-24 14:20:36](https://github.com/leanprover-community/mathlib/commit/4a6709b)
feat(data/{int,nat}/gcd): add `nat.gcd_greatest` ([#11611](https://github.com/leanprover-community/mathlib/pull/11611))
Add lemma characterising `gcd` in `ℕ`, counterpart of `int.gcd_greatest`.  Also add shorter proof of `int.gcd_greatest`.

### [2022-01-24 14:20:33](https://github.com/leanprover-community/mathlib/commit/bc2f73f)
feat(topology/uniform_space/uniform_convergence): Product of `tendsto_uniformly` ([#11562](https://github.com/leanprover-community/mathlib/pull/11562))
This PR adds lemmas `tendsto_uniformly_on.prod` and `tendsto_uniformly.prod`.

### [2022-01-24 12:47:20](https://github.com/leanprover-community/mathlib/commit/f99af7d)
chore(data/set/lattice): Generalize more `⋃`/`⋂` lemmas to dependent families ([#11516](https://github.com/leanprover-community/mathlib/pull/11516))
The "bounded union" and "bounded intersection" are both instances of nested `⋃`/`⋂`. But they only apply when the inner one runs over a predicate `p : ι → Prop`, and the resulting set couldn't depend on `p`. This generalizes to `κ : ι → Sort*` and allows dependence on `κ i`.
The lemmas are renamed from `bUnion`/`bInter` to `Union₂`/`Inter₂` to show that they are more general. Some generalizations lead to unification problems, so I've kept the `b` version around.
Some lemmas were missing between `⋃` and `⋂` or between `⋃`/`⋂` and nested `⋃`/`⋂`, so I'm adding them as well.
Renames

### [2022-01-24 12:18:54](https://github.com/leanprover-community/mathlib/commit/ee36571)
feat(algebra/lie/cartan_subalgebra): add self-normalizing characterisation for Lie subalgebra ([#11598](https://github.com/leanprover-community/mathlib/pull/11598))

### [2022-01-24 11:34:45](https://github.com/leanprover-community/mathlib/commit/dac4f40)
feat(analysis/normed_space/linear_isometry): `to_linear_equiv_trans` ([#11628](https://github.com/leanprover-community/mathlib/pull/11628))
Add a lemma relating `trans` for `linear_isometry_equiv` and
`linear_equiv`.

### [2022-01-24 11:34:44](https://github.com/leanprover-community/mathlib/commit/ed90301)
feat(group_theory/commuting_probability): Commuting probability inequalities ([#11564](https://github.com/leanprover-community/mathlib/pull/11564))
This PR adds some inequalities for the commuting probability.

### [2022-01-24 10:02:38](https://github.com/leanprover-community/mathlib/commit/9ef7f6b)
feat(linear_algebra/orientation): `eq_neg_iff_eq_neg` ([#11629](https://github.com/leanprover-community/mathlib/pull/11629))
Add two more `module.ray` lemmas about negation.

### [2022-01-24 10:02:37](https://github.com/leanprover-community/mathlib/commit/7ddb9a3)
refactor(order/ideal): Generalize definition and lemmas ([#11421](https://github.com/leanprover-community/mathlib/pull/11421))
* Generalize the `order_top` instance to `[nonempty P] [is_directed P (≤)]`.
* Delete `order.ideal.ideal_inter_nonempty` in favor of the equivalent condition `is_directed P (swap (≤))`.
* Delete `order.ideal.sup`/`order.ideal.inf` in favor of a direct instance declaration.
* Generalize defs/lemmas from `preorder` to `has_le` or `partial_order` to `preorder`.
* Two more `is_directed` lemmas and instances for `order_bot` and `order_top`.

### [2022-01-24 10:02:36](https://github.com/leanprover-community/mathlib/commit/9becbc7)
feat(algebra/order/rearrangement) : Rearrangement Inequality ([#10861](https://github.com/leanprover-community/mathlib/pull/10861))
A range of variants of the rearrangement inequality.
This is stated with scalar multiplication of a linear ring over an additive linear group, rather than having everything be in a linear ring. We couldn't find general statements of the rearrangement inequality in the literature, but this very much seems like an improvement.

### [2022-01-24 07:24:57](https://github.com/leanprover-community/mathlib/commit/8c64be0)
chore(category_theory/abelian): Moved more stuff into `pseudoelement` locale ([#11621](https://github.com/leanprover-community/mathlib/pull/11621))
The `ext` lemma triggers unwantedly in lots of places.

### [2022-01-24 05:54:29](https://github.com/leanprover-community/mathlib/commit/8f73b07)
feat(set_theory/surreal/dyadic): define add_monoid_hom structure on dyadic map ([#11052](https://github.com/leanprover-community/mathlib/pull/11052))
The proof is mechanical and mostly requires unraveling definitions.
The above map cannot be extended to ring morphism as so far there's not multiplication structure on surreal numbers.

### [2022-01-24 03:52:26](https://github.com/leanprover-community/mathlib/commit/32cd278)
feat(analysis/asymptotics): add a few lemmas ([#11623](https://github.com/leanprover-community/mathlib/pull/11623))
* rename `is_o.tendsto_0` to `is_o.tendsto_div_nhds_zero`, add `is_o.tendsto_inv_smul_nhds_zero`;
* add `is_o_const_left` and `filter.is_bounded_under.is_o_sub_self_inv`.

### [2022-01-24 02:18:18](https://github.com/leanprover-community/mathlib/commit/095c46c)
feat(linear_algebra/basis): `reindex_refl` ([#11626](https://github.com/leanprover-community/mathlib/pull/11626))
Add a `simp` lemma about applying `basis.reindex` with `equiv.refl`.

### [2022-01-23 15:43:45](https://github.com/leanprover-community/mathlib/commit/5449ffa)
feat(data/nat/prime): factors of non-prime powers ([#11546](https://github.com/leanprover-community/mathlib/pull/11546))
Adds the result `pow_factors_to_finset`, fills in `factors_mul_to_finset_of_coprime` for the sake of completion, and adjusts statements to take `ne_zero` rather than pos assumptions.

### [2022-01-23 13:55:13](https://github.com/leanprover-community/mathlib/commit/59ef8ce)
feat(measure_theory/measure): assorted lemmas ([#11612](https://github.com/leanprover-community/mathlib/pull/11612))
* add `ae_disjoint_compl_left/right`;
* deduce `restrict_to_measurable` and `restrict_to_measurable_of_sigma_finite` from @sgouezel 's lemmas about measures of intersections;
* add `ae_restrict_mem₀`;
* add `ae_eq_univ`.

### [2022-01-23 10:59:21](https://github.com/leanprover-community/mathlib/commit/d0f392e)
feat(analysis/calculus/inverse): a map which approximates a linear map on a set admits a nice global extension ([#11568](https://github.com/leanprover-community/mathlib/pull/11568))
And several other results on maps that are well approximated by linear maps on some subset of the space (not necessarily open).

### [2022-01-23 07:44:41](https://github.com/leanprover-community/mathlib/commit/b1ad301)
feat(number_theory/cyclotomic/basic): add missing lemmas ([#11451](https://github.com/leanprover-community/mathlib/pull/11451))
We add some missing lemmas about cyclotomic extensions.
From flt-regular.

### [2022-01-23 03:26:11](https://github.com/leanprover-community/mathlib/commit/9a517cf)
chore(analysis/normed/group/completion): fix attribution ([#11614](https://github.com/leanprover-community/mathlib/pull/11614))
This code was written by @jcommelin in [#6189](https://github.com/leanprover-community/mathlib/pull/6189) but somehow acquired my name during a refactor ([#10055](https://github.com/leanprover-community/mathlib/pull/10055)).  I don't think I've ever touched it!

### [2022-01-23 02:45:45](https://github.com/leanprover-community/mathlib/commit/2babfeb)
chore(data/complex/is_R_or_C): squeeze simps ([#11251](https://github.com/leanprover-community/mathlib/pull/11251))
This PR squeezes most of the simps in `is_R_or_C`, and updates the module docstring.

### [2022-01-22 23:39:48](https://github.com/leanprover-community/mathlib/commit/84dbe7b)
feat(measure_theory/covering): Lebesgue density points ([#11554](https://github.com/leanprover-community/mathlib/pull/11554))
We show in the general context of differentiation of measures that `μ (s ∩ a) / μ a` converges, when `a` shrinks towards a point `x`, to `1` for almost every `x` in `s`, and to `0` for almost every point outside of `s`. In other words, almost every point of `s` is a Lebesgue density points of `s`. Of course, this requires assumptions on allowed sets `a`. We state this in the general context of Vitali families. We also give easier to use versions in spaces with the Besicovitch property (e.g., final dimensional real vector spaces), where one can take for `a` the closed balls centered at `x`.

### [2022-01-22 22:28:56](https://github.com/leanprover-community/mathlib/commit/a196f9b)
chore(measure_theory/probability_mass_function): Move pmf monad operations into a seperate file ([#11579](https://github.com/leanprover-community/mathlib/pull/11579))
This PR moves the `pure`, `bind`, and `bind_on_support` operations on `pmf` into a new `probability_mass_function/monad.lean` file.

### [2022-01-22 22:28:55](https://github.com/leanprover-community/mathlib/commit/31db25b)
feat(topology/instances/ennreal): continuity of subtraction on ennreal ([#11527](https://github.com/leanprover-community/mathlib/pull/11527))

### [2022-01-22 20:53:55](https://github.com/leanprover-community/mathlib/commit/159d9ac)
split(order/max): Split off `order.basic` ([#11603](https://github.com/leanprover-community/mathlib/pull/11603))
This moves `is_bot`, `is_top`, `no_min_order`, `no_max_order` to a new file `order.max`.

### [2022-01-22 20:00:08](https://github.com/leanprover-community/mathlib/commit/5080d64)
feat(topology): add a few lemmas ([#11607](https://github.com/leanprover-community/mathlib/pull/11607))
* add `homeomorph.preimage_interior`, `homeomorph.image_interior`,
  reorder lemmas;
* add `is_open.smul₀` and `interior_smul₀`.

### [2022-01-22 18:38:06](https://github.com/leanprover-community/mathlib/commit/bd3b892)
move(order/hom/order): Move from `order.hom.lattice` ([#11601](https://github.com/leanprover-community/mathlib/pull/11601))
Rename `order.hom.lattice` into `order.hom.order` to make space for lattice homomorphisms, as opposed to the lattice of order homomorphisms.

### [2022-01-22 18:38:05](https://github.com/leanprover-community/mathlib/commit/206b56e)
doc(group_theory.quotient_group): Fix typos in main statement list ([#11581](https://github.com/leanprover-community/mathlib/pull/11581))
This now matches the docstring for the declaration in question.

### [2022-01-22 18:38:03](https://github.com/leanprover-community/mathlib/commit/155cf1d)
feat(group_theory/abelianization): add mul_equiv.abelianization_congr ([#11466](https://github.com/leanprover-community/mathlib/pull/11466))

### [2022-01-22 18:05:24](https://github.com/leanprover-community/mathlib/commit/7ba08d3)
fix(category_theory/triangulated): Fix definition of pretriangulated ([#11596](https://github.com/leanprover-community/mathlib/pull/11596))
The original definition unfolds to `(T₁ : triangle C) (T₁ ∈ distinguished_triangles) (T₂ : triangle C) (T₁ : triangle C) (e : T₁ ≅ T₂)`, where the two `T₁` are referring to different triangles.

### [2022-01-22 17:00:41](https://github.com/leanprover-community/mathlib/commit/d1b5165)
chore(group_theory/nilpotent): golf some proofs ([#11599](https://github.com/leanprover-community/mathlib/pull/11599))

### [2022-01-22 16:18:02](https://github.com/leanprover-community/mathlib/commit/fbf3c64)
chore(analysis/normed_space/star): golf some lemmas ([#11600](https://github.com/leanprover-community/mathlib/pull/11600))

### [2022-01-22 13:06:18](https://github.com/leanprover-community/mathlib/commit/504e1f6)
feat(group_theory.nilpotent): add *_central_series_one G 1 = … simp lemmas ([#11584](https://github.com/leanprover-community/mathlib/pull/11584))
analogously to the existing `_zero` lemmas

### [2022-01-22 13:06:17](https://github.com/leanprover-community/mathlib/commit/b630b8c)
feat(order/antichain): Strong antichains ([#11400](https://github.com/leanprover-community/mathlib/pull/11400))
This introduces a predicate `is_strong_antichain` to state that a set is a strong antichain with respect to a relation.
`s` is a strong (upward) antichain wrt `r` if for all `a ≠ b` in `s` there is some `c` such that `¬ r a c` or `¬ r b c`. A strong downward antichain of the swapped relation.

### [2022-01-22 12:01:38](https://github.com/leanprover-community/mathlib/commit/0ca7795)
feat(algebra/algebra/operations): remove two hypotheses from `submodule.mul_induction_on` ([#11533](https://github.com/leanprover-community/mathlib/pull/11533))
`h0 : C 0` followed trivially from `hm 0 _ 0 _`.
`hs : ∀ (r : R) x, C x → C (r • x)` follows nontrivially from an analogy to the `add_submonoid` case.
This also adds:
* a `pow_induction` variant.
* primed variants for when the motive depends on the proof term (such as the proof field in a subtype)

### [2022-01-21 23:07:46](https://github.com/leanprover-community/mathlib/commit/5e9c0a5)
feat(group_theory/subgroup/basic): add center_le_normalizer ([#11590](https://github.com/leanprover-community/mathlib/pull/11590))

### [2022-01-21 22:19:47](https://github.com/leanprover-community/mathlib/commit/d99f2fd)
chore(analysis/normed/group/basic): merge `norm` and `semi_norm` lemmas on `prod` and `pi` ([#11492](https://github.com/leanprover-community/mathlib/pull/11492))
`norm` and `semi_norm` are the same operator, so there is no need to have two sets of lemmas.
As a result the elaborator needs a few hints for some applications of the `pi` lemmas, but this is par for the course for pi typeclass instances anyway.

### [2022-01-21 21:34:00](https://github.com/leanprover-community/mathlib/commit/0653975)
chore(category_theory/sites): Generalize universes for the comparison lemma. ([#11588](https://github.com/leanprover-community/mathlib/pull/11588))

### [2022-01-21 19:30:19](https://github.com/leanprover-community/mathlib/commit/049d2ac)
feat(analysis/fourier): Fourier series for functions in L2; Parseval's identity ([#11320](https://github.com/leanprover-community/mathlib/pull/11320))

### [2022-01-21 15:40:51](https://github.com/leanprover-community/mathlib/commit/9c39019)
refactor(src/order/bounded): Invert iff direction ([#11582](https://github.com/leanprover-community/mathlib/pull/11582))
That way, `unbounded_gt_iff_unbounded_ge` corresponds to `unbounded_lt_iff_unbounded_le`.

### [2022-01-21 10:54:30](https://github.com/leanprover-community/mathlib/commit/ca79513)
feat(order/bounded): Proved many lemmas about bounded and unbounded sets ([#11179](https://github.com/leanprover-community/mathlib/pull/11179))
These include more convenient characterizations of unboundedness in preorders and linear orders, and many results about bounded intervals and initial segments.

### [2022-01-21 04:46:35](https://github.com/leanprover-community/mathlib/commit/884d813)
chore(analysis/inner_product_space/dual): remove unneeded `complete_space` assumption in four lemmas ([#11578](https://github.com/leanprover-community/mathlib/pull/11578))
We remove the `[complete_space E]` assumption in four lemmas.

### [2022-01-21 03:07:37](https://github.com/leanprover-community/mathlib/commit/80e072e)
feat(data/finset/basic): random golf ([#11576](https://github.com/leanprover-community/mathlib/pull/11576))

### [2022-01-21 00:16:10](https://github.com/leanprover-community/mathlib/commit/d71cab9)
feat(analysis/seminorm): add composition with linear maps ([#11477](https://github.com/leanprover-community/mathlib/pull/11477))
This PR defines the composition of seminorms with linear maps and shows that composition is monotone and calculates the seminorm ball of the composition.

### [2022-01-20 22:45:37](https://github.com/leanprover-community/mathlib/commit/6c97821)
feat(group_theory/submonoid/pointwise): add pointwise multiplication to `add_submonoid`s ([#11522](https://github.com/leanprover-community/mathlib/pull/11522))

### [2022-01-20 19:35:50](https://github.com/leanprover-community/mathlib/commit/adadd4a)
feat(measure_theory/function/lp_space): some variations of Markov's inequality formulated using `snorm` ([#11478](https://github.com/leanprover-community/mathlib/pull/11478))

### [2022-01-20 18:13:27](https://github.com/leanprover-community/mathlib/commit/8c9074f)
chore(*): Remove tactic.unfreeze_local_instances ([#11507](https://github.com/leanprover-community/mathlib/pull/11507))

### [2022-01-20 17:46:05](https://github.com/leanprover-community/mathlib/commit/dfca2b0)
feat(data/sym/sym2): add lemma that eq from distinct common members ([#11563](https://github.com/leanprover-community/mathlib/pull/11563))
Two terms of type `sym2 a` are equal if one can find two distinct elements of type `a` that are members of both.

### [2022-01-20 16:52:21](https://github.com/leanprover-community/mathlib/commit/b87449a)
feat(group_theory/nilpotent): Add equality theorems for nilpotency class ([#11540](https://github.com/leanprover-community/mathlib/pull/11540))
the nilpotency class can be defined as the length of the
upper central series, the lower central series, or as the shortest
length across all ascending or descending series.
In order to use the equivalence proofs between the various definition
of nilpotency in these lemmas, I had to reorder them to put the `∃n` in
front.

### [2022-01-20 16:01:23](https://github.com/leanprover-community/mathlib/commit/b5e542d)
feat(measure_theory/measurable_space): defining a measurable function on countably many pieces ([#11532](https://github.com/leanprover-community/mathlib/pull/11532))
Also, remove `open_locale classical` in this file and add decidability assumptions where needed. And add a few isolated useful lemmas.

### [2022-01-20 15:29:30](https://github.com/leanprover-community/mathlib/commit/1d762c7)
feat(ring_theory/{norm.lean, trace.lean}): improve two statements. ([#11569](https://github.com/leanprover-community/mathlib/pull/11569))
These statement are more precise.
From flt-regular.

### [2022-01-20 11:33:03](https://github.com/leanprover-community/mathlib/commit/447928c)
feat(topology/uniform_space/uniform_convergence): Composition on the left ([#11560](https://github.com/leanprover-community/mathlib/pull/11560))
Composing on the left by a uniformly continuous function preserves uniform convergence.

### [2022-01-20 10:32:33](https://github.com/leanprover-community/mathlib/commit/5a40c33)
feat(analysis/inner_product_space/l2): a Hilbert space is isometrically isomorphic to `ℓ²` ([#11255](https://github.com/leanprover-community/mathlib/pull/11255))
Define `orthogonal_family.linear_isometry_equiv`: the isometric isomorphism of a Hilbert space `E` with a Hilbert sum of a family of Hilbert spaces `G i`, induced by individual isometries of each `G i` into `E` whose images are orthogonal and span a dense subset of `E`.
Define a Hilbert basis of `E` to be an isometric isomorphism of `E` with `ℓ²(ι, 𝕜)`, the Hilbert sum of `ι` copies of `𝕜`.  Prove that an orthonormal family of vectors in `E` whose span is dense in `E` has an associated Hilbert basis.
Prove that every Hilbert space admit a Hilbert basis.
Delete three lemmas `maximal_orthonormal_iff_dense_span`, `exists_subset_is_orthonormal_dense_span`, `exists_is_orthonormal_dense_span` which previously expressed this existence theorem in a more awkward way (before the definition `ℓ²(ι, 𝕜)` was available).

### [2022-01-20 08:57:41](https://github.com/leanprover-community/mathlib/commit/53650a0)
feat(*): lemmas about `disjoint` on `set`s and `filter`s ([#11549](https://github.com/leanprover-community/mathlib/pull/11549))

### [2022-01-20 07:43:43](https://github.com/leanprover-community/mathlib/commit/e96e55d)
feat(analysis/normed_space/finite_dimension): extending partially defined Lipschitz functions ([#11530](https://github.com/leanprover-community/mathlib/pull/11530))
Any Lipschitz function on a subset of a metric space, into a finite-dimensional real vector space, can be extended to a globally defined Lipschitz function (up to worsening slightly the Lipschitz constant).

### [2022-01-20 02:36:41](https://github.com/leanprover-community/mathlib/commit/0a8848a)
chore(topology/uniform_space/uniform_convergence): Golf some proofs ([#11561](https://github.com/leanprover-community/mathlib/pull/11561))
This PR golfs a couple proofs.

### [2022-01-20 00:11:03](https://github.com/leanprover-community/mathlib/commit/656372c)
doc(group_theory/free_group): fix linkify ([#11565](https://github.com/leanprover-community/mathlib/pull/11565))

### [2022-01-19 22:49:35](https://github.com/leanprover-community/mathlib/commit/0bb4272)
chore(*): to_additive related cleanup ([#11559](https://github.com/leanprover-community/mathlib/pull/11559))
A few to_additive related cleanups
* Move measurability before to_additive to avoid having to manually do it later (or forget).
* Ensure anything tagged to_additive, mono has the additive version also mono'd
* Move simp before to_additive

### [2022-01-19 19:16:21](https://github.com/leanprover-community/mathlib/commit/7ee41aa)
feat(data/finsupp/basic): lemmas about map domain with only inj_on hypotheses ([#11484](https://github.com/leanprover-community/mathlib/pull/11484))
Also a lemma `sum_update_add` expressing the sum of an update in a monoid in terms of the original sum and the value of the update.
And golf `map_domain_smul`.
From flt-regular.

### [2022-01-19 17:41:05](https://github.com/leanprover-community/mathlib/commit/bbd0f76)
chore(*): clean up comment strings in docstrings ([#11557](https://github.com/leanprover-community/mathlib/pull/11557))
The syntax for these was wrong and showed up in doc-gen output unintentionally e.g.
https://leanprover-community.github.io/mathlib_docs/algebra/group/opposite.html#add_monoid_hom.op

### [2022-01-19 16:05:57](https://github.com/leanprover-community/mathlib/commit/a90f969)
feat(data/finset/slice): More `finset.slice` and antichain lemmas ([#11397](https://github.com/leanprover-community/mathlib/pull/11397))
Also move `finset.coe_bUnion` to a more sensible location.

### [2022-01-19 15:39:30](https://github.com/leanprover-community/mathlib/commit/c72e709)
feat(data/sum/interval): The disjoint sum of two locally finite orders is locally finite ([#11351](https://github.com/leanprover-community/mathlib/pull/11351))
This proves `locally_finite_order (α ⊕ β)` where `α` and `β` are locally finite themselves.

### [2022-01-19 13:06:48](https://github.com/leanprover-community/mathlib/commit/dbf59ba)
feat(algebra/roots_of_unity): basic constructor ([#11504](https://github.com/leanprover-community/mathlib/pull/11504))
from flt-regular

### [2022-01-19 11:58:04](https://github.com/leanprover-community/mathlib/commit/7ddaf10)
chore(algebra/algebra): algebra_map_int_eq ([#11474](https://github.com/leanprover-community/mathlib/pull/11474))
from flt-regular

### [2022-01-19 10:24:24](https://github.com/leanprover-community/mathlib/commit/4ad74ae)
chore(algebra/order/sub): Generalize to `preorder` and `add_comm_semigroup` ([#11463](https://github.com/leanprover-community/mathlib/pull/11463))
This generalizes a bunch of lemmas from `partial_order` to `preorder` and from `add_comm_monoid` to `add_comm_semigroup`.
It also adds `tsub_tsub_le_tsub_add : a - (b - c) ≤ a - b + c`.

### [2022-01-19 06:53:49](https://github.com/leanprover-community/mathlib/commit/1cfb97d)
feat(analysis/normed/group/pointwise): the closed thickening of a compact set is the addition of a closed ball. ([#11528](https://github.com/leanprover-community/mathlib/pull/11528))

### [2022-01-19 06:53:48](https://github.com/leanprover-community/mathlib/commit/ff9b757)
feat(category_theory/bicategory/locally_discrete): define locally discrete bicategory ([#11402](https://github.com/leanprover-community/mathlib/pull/11402))
This PR defines the locally discrete bicategory on a category.

### [2022-01-18 21:06:28](https://github.com/leanprover-community/mathlib/commit/6dd6525)
feat(measure_theory/measure/measure_space): better definition of to_measurable ([#11529](https://github.com/leanprover-community/mathlib/pull/11529))
Currently, `to_measurable μ t` picks a measurable superset of `t` with the same measure. When the measure of `t` is infinite, it is most often useless. This PR adjusts the definition so that, in the case of sigma-finite spaces, `to_measurable μ t` has good properties even when `t` has infinite measure.

### [2022-01-18 20:38:47](https://github.com/leanprover-community/mathlib/commit/de53f9c)
feat(data/nat/factorization): add two convenience lemmas ([#11543](https://github.com/leanprover-community/mathlib/pull/11543))
Adds convenience lemmas `prime_of_mem_factorization` and `pos_of_mem_factorization`.
Also adds a different proof of `factorization_prod_pow_eq_self` that doesn't depend on `multiplicative_factorization` and so can appear earlier in the file.

### [2022-01-18 17:08:36](https://github.com/leanprover-community/mathlib/commit/5a1cbe3)
feat(linear_algebra,algebra,group_theory): miscellaneous lemmas linking some additive monoid and module operations ([#11525](https://github.com/leanprover-community/mathlib/pull/11525))
This adds:
* `submodule.map_to_add_submonoid`
* `submodule.sup_to_add_submonoid`
* `submodule.supr_to_add_submonoid`
As well as some missing `add_submonoid` lemmas copied from the `submodule` API:
* `add_submonoid.closure_singleton_le_iff_mem`
* `add_submonoid.mem_supr`
* `add_submonoid.supr_eq_closure`
Finally, it generalizes some indices in `supr` and `infi` lemmas from `Type*` to `Sort*`.
This is pre-work for removing a redundant hypothesis from `submodule.mul_induction_on`.

### [2022-01-18 16:08:17](https://github.com/leanprover-community/mathlib/commit/a0ff65d)
feat(ring_theory/norm): add is_integral_norm ([#11489](https://github.com/leanprover-community/mathlib/pull/11489))
We add `is_integral_norm`.
From flt-regular

### [2022-01-18 15:13:28](https://github.com/leanprover-community/mathlib/commit/6f23973)
feat(ring_theory/graded_algebra/basic): add a helper for construction from an alg hom ([#11541](https://github.com/leanprover-community/mathlib/pull/11541))
Most graded algebras are already equipped with some kind of universal property which gives an easy way to build such an `alg_hom`.
This lemma makes it easier to discharge the associated proof obligations to show that this alg hom forms a decomposition.
This also relaxes a `ring` argument to `semiring`.

### [2022-01-18 12:22:37](https://github.com/leanprover-community/mathlib/commit/496a744)
feat(measure_theory): generalize `null_of_locally_null` to `outer_measure`, add versions ([#11535](https://github.com/leanprover-community/mathlib/pull/11535))
* generalize `null_of_locally_null`;
* don't intersect with `s` twice;
* add a contraposed version;
* golf.

### [2022-01-18 12:22:35](https://github.com/leanprover-community/mathlib/commit/be9a5de)
feat(topology/separation): add `t1_space_tfae` ([#11534](https://github.com/leanprover-community/mathlib/pull/11534))
Also add some lemmas about `filter.disjoint`.

### [2022-01-18 12:22:34](https://github.com/leanprover-community/mathlib/commit/135a92d)
feat(data/set): two simple lemmas ([#11531](https://github.com/leanprover-community/mathlib/pull/11531))

### [2022-01-18 12:22:32](https://github.com/leanprover-community/mathlib/commit/5bbc187)
feat(algebra/lie/nilpotent): a non-trivial nilpotent Lie module has non-trivial maximal trivial submodule ([#11515](https://github.com/leanprover-community/mathlib/pull/11515))
The main result is `lie_module.nontrivial_max_triv_of_is_nilpotent`

### [2022-01-18 10:53:40](https://github.com/leanprover-community/mathlib/commit/a0da4f1)
feat(algebra/big_operators/basic): Reindexing a product with a permutation ([#11344](https://github.com/leanprover-community/mathlib/pull/11344))
This proves `(∏ x in s, f (σ x)) = ∏ x in s, f x` for a permutation `σ`.

### [2022-01-18 09:14:43](https://github.com/leanprover-community/mathlib/commit/8d5caba)
chore(order/bounded_order): golf ([#11538](https://github.com/leanprover-community/mathlib/pull/11538))

### [2022-01-18 09:14:41](https://github.com/leanprover-community/mathlib/commit/a217b9c)
feat(measure_theory): drop some `measurable_set` assumptions ([#11536](https://github.com/leanprover-community/mathlib/pull/11536))
* make `exists_subordinate_pairwise_disjoint` work for `null_measurable_set`s;
* use `ae_disjoint` in `measure_Union₀`, drop `measure_Union_of_null_inter`;
* prove `measure_inter_add_diff` for `null_measurable_set`s;
* drop some `measurable_set` assumptions in `measure_union`, `measure_diff`, etc;
* golf.

### [2022-01-18 09:14:39](https://github.com/leanprover-community/mathlib/commit/f23c00f)
chore(algebra/order/ring): move lemmas about invertible into a new file ([#11511](https://github.com/leanprover-community/mathlib/pull/11511))
The motivation here is to eventually be able to use the `one_pow` lemma in `algebra.group.units`. This is one very small step in that direction.

### [2022-01-18 07:45:51](https://github.com/leanprover-community/mathlib/commit/01fa7f5)
feat(data/fintype/basic): `one_lt_card_iff` and `two_lt_card_iff` ([#11524](https://github.com/leanprover-community/mathlib/pull/11524))
This PR adds `one_lt_card_iff` and `two_lt_card_iff`.

### [2022-01-18 07:09:41](https://github.com/leanprover-community/mathlib/commit/e895c8f)
chore(cone_category): generalize universes ([#11539](https://github.com/leanprover-community/mathlib/pull/11539))

### [2022-01-18 03:54:41](https://github.com/leanprover-community/mathlib/commit/813a191)
chore(logic/basic): Make higher `forall_congr`/`exists_congr` lemmas dependent ([#11490](https://github.com/leanprover-community/mathlib/pull/11490))
Currently, `forall₂_congr` and friends take as arguments non dependent propositions like `p q : α → β → Prop`. This prevents them being useful virtually anywhere as most often foralls are nested like `∀ a, a ∈ s → ...` and `a ∈ s` depends on `a`.
This PR turns them into `Π a, β a → Prop` (and similar for higher arities).
As a bonus, it adds the `5`-ary version and golfs all occurrences of nested `forall_congr`s.

### [2022-01-18 00:10:59](https://github.com/leanprover-community/mathlib/commit/99e9036)
chore(algebra/algebra/subalgebra): lemmas about top and injectivity ([#11514](https://github.com/leanprover-community/mathlib/pull/11514))

### [2022-01-17 23:42:43](https://github.com/leanprover-community/mathlib/commit/1e4da8d)
refactor(linear_algebra/{tensor,exterior}_algebra): convert to a directory ([#11513](https://github.com/leanprover-community/mathlib/pull/11513))
These files can be quite slow, so it's useful to be able to add new definitions and lemmas in standalone files, rather than in the same file.
There are a number of open PRs of mine that make this move as part of a new feature, so let's just move them pre-emptively.

### [2022-01-17 22:39:19](https://github.com/leanprover-community/mathlib/commit/5b36c86)
feat(analysis/normed_space/finite_dimension): the determinant is continuous on the space of continuous linear maps ([#11526](https://github.com/leanprover-community/mathlib/pull/11526))

### [2022-01-17 22:11:44](https://github.com/leanprover-community/mathlib/commit/4072512)
feat(src/group_theory/nilpotent): solvable_of_nilpotent ([#11512](https://github.com/leanprover-community/mathlib/pull/11512))
following the proof on
<https://groupprops.subwiki.org/wiki/Nilpotent_implies_solvable>

### [2022-01-17 21:04:13](https://github.com/leanprover-community/mathlib/commit/274b530)
feat(data/equiv/basic): add `add_equiv.to_int_linear_equiv` ([#11456](https://github.com/leanprover-community/mathlib/pull/11456))
as written by @adamtopaz on [zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/injections.20to.20equiv/near/268038978)

### [2022-01-17 19:54:14](https://github.com/leanprover-community/mathlib/commit/1fbef63)
feat(order/filter): add two lemmas ([#11519](https://github.com/leanprover-community/mathlib/pull/11519))
Two easy lemmas (from the sphere eversion project) and some minor style changes.

### [2022-01-17 19:54:13](https://github.com/leanprover-community/mathlib/commit/e096b99)
refactor(set_theory/ordinal_arithmetic): Rename `power` to `opow` ([#11279](https://github.com/leanprover-community/mathlib/pull/11279))

### [2022-01-17 19:08:49](https://github.com/leanprover-community/mathlib/commit/2a8a01b)
chore(measure_theory/integral/bochner): use set_to_fun lemmas to prove integral properties ([#10717](https://github.com/leanprover-community/mathlib/pull/10717))

### [2022-01-17 15:56:24](https://github.com/leanprover-community/mathlib/commit/905871f)
feat(analysis/normed_space/spectrum): an algebra homomorphism into the base field is bounded ([#11494](https://github.com/leanprover-community/mathlib/pull/11494))
We prove basic facts about `φ : A →ₐ[𝕜] 𝕜` when `A` is a Banach algebra, namely that `φ` maps elements of `A` to their spectrum, and that `φ` is bounded.

### [2022-01-17 15:10:20](https://github.com/leanprover-community/mathlib/commit/4e31396)
feat(measure_theory/measure): define `ae_disjoint` ([#11500](https://github.com/leanprover-community/mathlib/pull/11500))
I am going to migrate most `disjoint` assumptions to `ae_disjoint`.

### [2022-01-17 14:43:23](https://github.com/leanprover-community/mathlib/commit/50bdb29)
feat(analysis/complex/cauchy_integral): review docs, add versions without `off_countable` ([#11417](https://github.com/leanprover-community/mathlib/pull/11417))

### [2022-01-17 11:46:31](https://github.com/leanprover-community/mathlib/commit/391bd21)
doc(src/data/equiv/transfer_instances): nontrivial, not nonzero ([#11508](https://github.com/leanprover-community/mathlib/pull/11508))
small docs typo, it seems.

### [2022-01-17 10:14:51](https://github.com/leanprover-community/mathlib/commit/6b475a4)
feat(data/finset/basic): `finset.two_lt_card` ([#11505](https://github.com/leanprover-community/mathlib/pull/11505))
This PR adds lemmas `finset.two_lt_card` and `finset.two_lt_card_iff`, similar to `finset.one_lt_card` and `finset.one_lt_card_iff`.
These lemmas are also similar to `finset.card_eq_three`.

### [2022-01-17 10:14:50](https://github.com/leanprover-community/mathlib/commit/079fb16)
feat(analysis/special_functions/complex/arg): `arg_neg` lemmas ([#11503](https://github.com/leanprover-community/mathlib/pull/11503))
Add lemmas about the value of `arg (-x)`: one each for positive and
negative sign of `x.im`, two `iff` lemmas saying exactly when it's
equal to `arg x - π` or `arg x + π`, and a simpler lemma giving the
value of `(arg (-x) : real.angle)` for any nonzero `x`.
These replace the previous lemmas
`arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg` and
`arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg`, which are strictly less
general (they have a hypothesis `x.re < 0` that's not needed unless
the imaginary part is 0).  Those two lemmas are unused in current
mathlib (they were used in the proof of `cos_arg` before the golfing
in [#10365](https://github.com/leanprover-community/mathlib/pull/10365)) and it seems reasonable to me to replace them with the more
general lemmas.

### [2022-01-17 10:14:49](https://github.com/leanprover-community/mathlib/commit/1c56a8d)
feat(order/well_founded_set): Antichains in a partial well order are finite ([#11286](https://github.com/leanprover-community/mathlib/pull/11286))
and when the relation is reflexive and symmetric, it's actually an equivalent condition.

### [2022-01-17 08:42:46](https://github.com/leanprover-community/mathlib/commit/0d5bfd7)
feat(*): add a few lemmas about `function.extend` ([#11498](https://github.com/leanprover-community/mathlib/pull/11498))
I'm going to use `function.extend` as another way to get from
`[encodable ι] (s : ι → set α)` to `t : ℕ → set α` in measure theory.

### [2022-01-17 08:42:45](https://github.com/leanprover-community/mathlib/commit/9b70cc6)
feat(data/equiv/encodable): add a few lemmas ([#11497](https://github.com/leanprover-community/mathlib/pull/11497))
* add `simp` lemmas `encodable.encode_inj` and
  `encodable.decode₂_encode`;
* add `encodable.decode₂_eq_some`;
* avoid non-final `simp` in the proof of `encodable.Union_decode₂_disjoint_on`.

### [2022-01-17 08:42:44](https://github.com/leanprover-community/mathlib/commit/ac76eb3)
feat(algebra/star/unitary): lemmas about group_with_zero ([#11493](https://github.com/leanprover-community/mathlib/pull/11493))

### [2022-01-17 08:42:43](https://github.com/leanprover-community/mathlib/commit/a88ae0c)
refactor(data/set/lattice): Generalize `mem_bUnion_iff` and `mem_bInter_iff` to dependent families ([#11485](https://github.com/leanprover-community/mathlib/pull/11485))
They're now called `mem_Union₂` and `mem_Inter₂`.

### [2022-01-17 07:55:11](https://github.com/leanprover-community/mathlib/commit/83eff32)
feat(topology/metric_space): more lemmas about disjoint balls ([#11506](https://github.com/leanprover-community/mathlib/pull/11506))
* drop unused lemmas `metric.ball_disjoint` and
  `metric.ball_disjoint_same`; the former was a duplicate of
  `metric.ball_disjoint_ball`;
* add `metric.closed_ball_disjoint_ball`, `metric.closed_ball_disjoint_closed_ball`.

### [2022-01-17 07:55:09](https://github.com/leanprover-community/mathlib/commit/2f342b8)
feat(measure_theory): generalize some lemmas to `outer_measure` ([#11501](https://github.com/leanprover-community/mathlib/pull/11501))

### [2022-01-17 07:20:57](https://github.com/leanprover-community/mathlib/commit/43bbaee)
feat(measure_theory/measure): add lemmas, drop `measurable_set` assumptions ([#11499](https://github.com/leanprover-community/mathlib/pull/11499))
* `restrict_eq_self` no longer requires measurability of either set;
* `restrict_apply_self` no longer requires measurability of the set;
* add `restrict_apply_superset` and `restrict_restrict_of_subset` ;
* add `restrict_restrict'` that assumes measurability of the other
  set, drop one `measurable_set` assumption in `restrict_comm`;
* drop measurability assumptions in `restrict_congr_mono`.

### [2022-01-17 00:42:46](https://github.com/leanprover-community/mathlib/commit/6d19eba)
feat(*): add to_sub* lemmas for `map`, `fg` ([#11480](https://github.com/leanprover-community/mathlib/pull/11480))
From flt-regular.

### [2022-01-16 23:52:06](https://github.com/leanprover-community/mathlib/commit/4ed7316)
feat(analysis/special_functions/pow): tendsto rpow lemma for ennreals ([#11475](https://github.com/leanprover-community/mathlib/pull/11475))

### [2022-01-16 23:11:56](https://github.com/leanprover-community/mathlib/commit/2c2338e)
chore(data/complex/basic): add of_real_eq_one ([#11496](https://github.com/leanprover-community/mathlib/pull/11496))

### [2022-01-16 23:11:54](https://github.com/leanprover-community/mathlib/commit/1f6bbf9)
feat(analysis/special_functions/complex/arg): `arg_conj`, `arg_inv` lemmas ([#11479](https://github.com/leanprover-community/mathlib/pull/11479))
Add lemmas giving the values of `arg (conj x)` and `arg x⁻¹`, both for
`arg` as a real number and `arg` coerced to `real.angle` (the latter
function being better behaved because it avoids case distinctions
around getting a result into the interval (-π, π]).

### [2022-01-16 22:44:43](https://github.com/leanprover-community/mathlib/commit/f4b93c8)
feat(analysis/special_functions/trigonometric/angle): more 2π = 0 lemmas ([#11482](https://github.com/leanprover-community/mathlib/pull/11482))
Add some more lemmas useful for manipulation of `real.angle` expressions.

### [2022-01-16 22:07:26](https://github.com/leanprover-community/mathlib/commit/ed57bdd)
feat(number_field): notation for 𝓞 K, an algebra & ∈ 𝓞 K iff ([#11476](https://github.com/leanprover-community/mathlib/pull/11476))
From flt-regular.

### [2022-01-16 21:15:07](https://github.com/leanprover-community/mathlib/commit/5f5bcd8)
feat(order/filter/ultrafilter): add some comap_inf_principal lemmas ([#11495](https://github.com/leanprover-community/mathlib/pull/11495))
...in the setting of ultrafilters
These lemmas are useful to prove e.g. that the continuous image of a
compact set is compact in the setting of convergence spaces.

### [2022-01-16 15:00:06](https://github.com/leanprover-community/mathlib/commit/d7f8f58)
feat(algebra/star/unitary): (re)define unitary elements of a star monoid ([#11457](https://github.com/leanprover-community/mathlib/pull/11457))
This PR defines `unitary R` for a star monoid `R` as the submonoid containing the elements that satisfy both `star U * U = 1` and `U * star U = 1`. We show basic properties (i.e. that this forms a group) and show that they
preserve the norm when `R` is a C* ring.
Note that this replaces `unitary_submonoid`, which only included the condition `star U * U = 1` -- see [the discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/unitary.20submonoid) on Zulip.

### [2022-01-16 15:00:04](https://github.com/leanprover-community/mathlib/commit/1d1f384)
feat(analysis/calculus/dslope): define dslope ([#11432](https://github.com/leanprover-community/mathlib/pull/11432))

### [2022-01-16 13:30:27](https://github.com/leanprover-community/mathlib/commit/1aee8a8)
chore(*): Put `simp` attribute before `to_additive` ([#11488](https://github.com/leanprover-community/mathlib/pull/11488))
A few lemmas were tagged in the wrong order. As tags are applied from left to right, `@[to_additive, simp]` only marks the multiplicative lemma as `simp`. The correct order is thus `@[simp, to_additive]`.

### [2022-01-16 13:30:25](https://github.com/leanprover-community/mathlib/commit/02a4775)
refactor(analysis/normed_space): merge `normed_space` and `semi_normed_space` ([#8218](https://github.com/leanprover-community/mathlib/pull/8218))
There are no theorems which are true for `[normed_group M] [normed_space R M]` but not `[normed_group M] [semi_normed_space R M]`; so there is about as much value to the `semi_normed_space` / `normed_space` distinction as there was between `module` / `semimodule`. Since we eliminated `semimodule`, we should eliminte `semi_normed_space` too.
This relaxes the typeclass arguments of `normed_space` to make it a drop-in replacement for `semi_normed_space`; or viewed another way, this removes `normed_space` and renames `semi_normed_space` to replace it.
This does the same thing to `normed_algebra` and `seminormed_algebra`, but these are hardly used anyway.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/semi_normed_space.20vs.20normed_space/near/245089933)
As with any typeclass refactor, this randomly breaks elaboration in a few places; presumably, it was able to unify arguments from one particular typeclass path, but not from another. To fix this, some type ascriptions have to be added where previously none were needed. In a few rare cases, the elaborator gets so confused that we have to enter tactic mode to produce a term.
This isn't really a new problem - this PR just makes these issues all visible at once, whereas normally we'd only run into one or two at a time. Optimistically Lean 4 will fix all this, but we won't really know until we try.

### [2022-01-16 13:03:59](https://github.com/leanprover-community/mathlib/commit/d60541c)
feat(analysis/seminorm): Add `has_add` and `has_scalar nnreal` ([#11414](https://github.com/leanprover-community/mathlib/pull/11414))
Add instances of `has_add` and `has_scalar nnreal` type classes for `seminorm`.

### [2022-01-16 09:33:17](https://github.com/leanprover-community/mathlib/commit/3fb5b82)
feat(algebra/star/basic): change `star_ring_aut` (notably, complex conjugation) from `ring_equiv` to `ring_hom` and make type argument explicit ([#11418](https://github.com/leanprover-community/mathlib/pull/11418))
Change the underlying object notated by `conj` from
```lean
def star_ring_aut [comm_semiring R] [star_ring R] : ring_aut R :=
```
to
```lean
def star_ring_end [comm_semiring R] [star_ring R] : R →+* R :=
```
and also make the `R` argument explicit.  These two changes allow the notation for conjugate-linear maps, `E →ₗ⋆[R] F` and variants, to pretty-print, see
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Pretty.20printer.20omits.20notation
This is a partial reversion of [#9640](https://github.com/leanprover-community/mathlib/pull/9640), in which complex conjugation was upgraded from `ring_hom` to `ring_equiv`.

### [2022-01-15 21:32:40](https://github.com/leanprover-community/mathlib/commit/1a29adc)
feat(measure_theory/integral): weaker assumptions on Ioi integrability ([#11090](https://github.com/leanprover-community/mathlib/pull/11090))
To show a function is integrable given an `ae_cover` it suffices to show boundedness along a filter, not necessarily convergence. This PR adds these generalisations, and uses them to show the older convergence versions.

### [2022-01-15 20:09:30](https://github.com/leanprover-community/mathlib/commit/1f266d6)
feat(data/pnat/basic): `succ_nat_pred` ([#11455](https://github.com/leanprover-community/mathlib/pull/11455))

### [2022-01-15 18:38:48](https://github.com/leanprover-community/mathlib/commit/0b4f07f)
feat(data/set/basic): add singleton_injective ([#11464](https://github.com/leanprover-community/mathlib/pull/11464))

### [2022-01-15 17:32:48](https://github.com/leanprover-community/mathlib/commit/37cf695)
feat(measure_theory/integral/set_to_l1): monotonicity properties of set_to_fun ([#10714](https://github.com/leanprover-community/mathlib/pull/10714))
We prove that in a `normed_lattice_add_comm_group`, if `T` is such that `0 ≤ T s x` for `0 ≤ x`,  then `set_to_fun μ T` verifies
- `set_to_fun_mono_left (h : ∀ s x, T' s x ≤ T'' s x) : set_to_fun μ T' hT' f ≤ set_to_fun μ T'' hT'' f`
- `set_to_fun_nonneg (hf : 0 ≤ᵐ[μ] f) : 0 ≤ set_to_fun μ T hT f`
- `set_to_fun_mono (hfg : f ≤ᵐ[μ] g) : set_to_fun μ T hT f ≤ set_to_fun μ T hT g`

### [2022-01-15 15:30:16](https://github.com/leanprover-community/mathlib/commit/51c5a40)
feat(analysis/special_functions/trigonometric/angle): `neg_coe_pi` ([#11460](https://github.com/leanprover-community/mathlib/pull/11460))
Add the lemma that `-π` and `π` are the same `real.angle` (angle mod 2π).

### [2022-01-15 14:19:28](https://github.com/leanprover-community/mathlib/commit/ce62dbc)
feat(algebra/star/self_adjoint): module instance on self-adjoint elements of a star algebra ([#11322](https://github.com/leanprover-community/mathlib/pull/11322))
We put a module instance on `self_adjoint A`, where `A` is a `[star_module R A]` and `R` has a trivial star operation. A new typeclass `[has_trivial_star R]` is created for this purpose with an instance on `ℝ`. This allows us to express the fact that e.g. the space of complex Hermitian matrices is a real vector space.

### [2022-01-15 10:42:41](https://github.com/leanprover-community/mathlib/commit/0d1d4c9)
feat(data/finset/basic): strengthen `finset.nonempty.cons_induction` ([#11452](https://github.com/leanprover-community/mathlib/pull/11452))
This change makes it strong enough to be used in three other lemmas.

### [2022-01-15 09:16:04](https://github.com/leanprover-community/mathlib/commit/ff19c95)
chore(algebra/group_power/basic): collect together ring lemmas ([#11446](https://github.com/leanprover-community/mathlib/pull/11446))
This reorders the lemmas so that all the ring and comm_ring lemmas can be put in a single section.

### [2022-01-15 07:39:52](https://github.com/leanprover-community/mathlib/commit/df2d70d)
refactor(analysis/inner_product_space/basic): generalize `orthogonal_family` from submodules to maps ([#11254](https://github.com/leanprover-community/mathlib/pull/11254))
The old definition of `orthogonal_family` was a predicate on `V : ι → submodule 𝕜 E`, a family of submodules of an inner product space `E`; the new definition is a predicate on 
```lean
{G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)] (V : Π i, G i →ₗᵢ[𝕜] E)
```
a family of inner product spaces and (injective, generally not surjective) isometries of these inner product spaces into `E`.
The new definition subsumes the old definition, but also applies more cleanly to orthonormal sets of vectors.  An orthonormal set `{v : ι → E}` of vectors in `E` induces an `orthogonal_family` of the new style with `G i` chosen to be `𝕜`, for each `i`, and `V i : G i →ₗᵢ[𝕜] E` the map from `𝕜` to the span of `v i` in `E`.
In [#11255](https://github.com/leanprover-community/mathlib/pull/11255) we write down the induced isometry from the l2 space `lp G 2` into `E` induced by "summing" all the isometries in an orthogonal family.  This works for either the old definition or the new definition.  But with the old definition, an orthonormal set of vectors induces an isometry from the weird l2 space `lp (λ i, span 𝕜 (v i)) 2` into `E`, whereas with the new definition it induces an isometry from the standard l2 space `lp (λ i, 𝕜) 2` into `E`.  This is much more elegant!

### [2022-01-15 02:46:13](https://github.com/leanprover-community/mathlib/commit/fa41b7a)
feat(topology/algebra/uniform_group): Condition for uniform convergence ([#11391](https://github.com/leanprover-community/mathlib/pull/11391))
This PR adds a lemma regarding uniform convergence on a topological group `G`, placed right after the construction of the `uniform_space` structure on `G`.

### [2022-01-14 21:29:54](https://github.com/leanprover-community/mathlib/commit/323e388)
feat(algebraic_geometry): More lemmas about affine schemes and basic open sets ([#11449](https://github.com/leanprover-community/mathlib/pull/11449))

### [2022-01-14 19:02:35](https://github.com/leanprover-community/mathlib/commit/f770d6e)
feat(topology/separation): generalize two lemmas ([#11454](https://github.com/leanprover-community/mathlib/pull/11454))

### [2022-01-14 19:02:34](https://github.com/leanprover-community/mathlib/commit/d54375e)
feat(data/nat/totient): `totient_even` ([#11436](https://github.com/leanprover-community/mathlib/pull/11436))

### [2022-01-14 17:47:21](https://github.com/leanprover-community/mathlib/commit/49079c1)
feat(data/finsupp/basic): add `finset_sum_apply` and `coe_fn_add_hom` ([#11423](https://github.com/leanprover-community/mathlib/pull/11423))
`finset_sum_apply`: Given a family of functions `f i : α → ℕ` indexed over `S : finset ι`, the sum of this family over `S` is a function `α → ℕ` whose value at `p : α` is `∑ (i : ι) in S, (f i) p`
`coe_fn_add_monoid_hom`: Coercion from a `finsupp` to a function type is an `add_monoid_hom`. Proved by Alex J. Best

### [2022-01-14 17:47:19](https://github.com/leanprover-community/mathlib/commit/757eaf4)
chore(analysis/calculus/{deriv,mean_value}): use `slope` ([#11419](https://github.com/leanprover-community/mathlib/pull/11419))

### [2022-01-14 17:47:18](https://github.com/leanprover-community/mathlib/commit/653fe45)
feat(analysis/seminorm): `semilattice_sup` on seminorms and lemmas about `ball` ([#11329](https://github.com/leanprover-community/mathlib/pull/11329))
Define `bot` and the the binary `sup` on seminorms, and some lemmas about the supremum of a finite number of seminorms.
Shows that the unit ball of the supremum is given by the intersection of the unit balls.

### [2022-01-14 16:49:58](https://github.com/leanprover-community/mathlib/commit/2ce607e)
Docs typo in set_theory/cardinal: Wrong type product symbol ([#11453](https://github.com/leanprover-community/mathlib/pull/11453))

### [2022-01-14 15:12:25](https://github.com/leanprover-community/mathlib/commit/d8aed79)
chore(analysis/inner_product_space/projection): Speedup `linear_isometry_equiv.reflections_generate_dim_aux` ([#11443](https://github.com/leanprover-community/mathlib/pull/11443))
This takes it from around 17s to around 6s on my machine.
IMO using `e * f` instead of `f.trans e` makes this proof a little easier to follow, as then we don't have to translate between the two different spellings mid proof (and `prod` uses the `*` spelling internally)

### [2022-01-14 15:12:24](https://github.com/leanprover-community/mathlib/commit/22a9f2e)
feat(algebra/field/basic): `div_neg_self`, `neg_div_self` ([#11438](https://github.com/leanprover-community/mathlib/pull/11438))
I think these two lemmas are useful as `simp` lemmas, but they don't
seem to be there already.

### [2022-01-14 14:12:17](https://github.com/leanprover-community/mathlib/commit/201aeaa)
chore(algebra/char_p): ring_char.eq is better in the other direction, with instances, and explicit arguments ([#11439](https://github.com/leanprover-community/mathlib/pull/11439))

### [2022-01-14 13:04:30](https://github.com/leanprover-community/mathlib/commit/011a599)
feat(algebraic_geometry): Gluing morphisms from an open cover. ([#11441](https://github.com/leanprover-community/mathlib/pull/11441))

### [2022-01-14 10:58:50](https://github.com/leanprover-community/mathlib/commit/44351a9)
chore(analysis/complex/circle): add to_units and golf ([#11435](https://github.com/leanprover-community/mathlib/pull/11435))

### [2022-01-14 10:58:49](https://github.com/leanprover-community/mathlib/commit/38eb719)
feat(data/matrix/notation): relax typeclass assumptions ([#11429](https://github.com/leanprover-community/mathlib/pull/11429))

### [2022-01-14 10:58:47](https://github.com/leanprover-community/mathlib/commit/a861839)
feat(ring_theory/discriminant): add discr_mul_is_integral_mem_adjoin ([#11396](https://github.com/leanprover-community/mathlib/pull/11396))
We add `discr_mul_is_integral_mem_adjoin`: let `K` be the fraction field of an integrally closed domain `R` and let `L` be a finite
separable extension of `K`. Let `B : power_basis K L` be such that `is_integral R B.gen`. Then for all `z : L` that are integral over `R`, we have `(discr K B.basis) • z ∈ adjoin R ({B.gen} : set L)`.
From flt-regular.

### [2022-01-14 10:07:46](https://github.com/leanprover-community/mathlib/commit/5a6c13b)
feat(algebraic_geometry/open_immersion): Operations on open covers.  ([#11442](https://github.com/leanprover-community/mathlib/pull/11442))

### [2022-01-14 10:07:44](https://github.com/leanprover-community/mathlib/commit/e286012)
feat(algebra/ne_zero): `pos_of_ne_zero_coe` ([#11437](https://github.com/leanprover-community/mathlib/pull/11437))

### [2022-01-14 10:07:43](https://github.com/leanprover-community/mathlib/commit/021baae)
feat(analysis/normed_space/linear_isometry): coercion injectivity lemmas and add_monoid_hom_class ([#11434](https://github.com/leanprover-community/mathlib/pull/11434))
This also registers `linear_isometry` and `linear_isometry_equiv` with `add_monoid_hom_class`.
I found myself wanting one of these while squeezing a simp, so may as well have all of them now.

### [2022-01-14 10:07:42](https://github.com/leanprover-community/mathlib/commit/61054f7)
feat(topology): some improvements ([#11424](https://github.com/leanprover-community/mathlib/pull/11424))
* Prove a better version of `continuous_on.comp_fract`. Rename `continuous_on.comp_fract` -> `continuous_on.comp_fract''`.
* Rename `finset.closure_Union` -> `finset.closure_bUnion`
* Add `continuous.congr` and `continuous.subtype_coe`

### [2022-01-14 08:37:20](https://github.com/leanprover-community/mathlib/commit/3c1740a)
feat(combinatorics/configuration): Define the order of a projective plane ([#11430](https://github.com/leanprover-community/mathlib/pull/11430))
This PR defines the order of a projective plane, and proves a couple lemmas.

### [2022-01-14 08:37:18](https://github.com/leanprover-community/mathlib/commit/5a3abca)
feat(topology/subset_properties): some compactness properties ([#11425](https://github.com/leanprover-community/mathlib/pull/11425))
* Add some lemmas about the existence of compact sets
* Add `is_compact.eventually_forall_of_forall_eventually`
* Some cleanup in `topology/subset_properties` and `topology/separation`

### [2022-01-14 08:37:17](https://github.com/leanprover-community/mathlib/commit/feaf6f5)
feat(algebraic_geometry): lemmas about basic opens in schemes ([#11393](https://github.com/leanprover-community/mathlib/pull/11393))

### [2022-01-14 08:37:16](https://github.com/leanprover-community/mathlib/commit/85accb8)
feat(data/{multiset,finset}/sum): Disjoint sum of multisets/finsets ([#11355](https://github.com/leanprover-community/mathlib/pull/11355))
This defines the disjoint union of two multisets/finsets as `multiset (α ⊕ β)`/`finset (α ⊕ β)`.

### [2022-01-14 08:37:15](https://github.com/leanprover-community/mathlib/commit/9a94993)
feat(analysis/inner_product_space/l2): Inner product space structure on `l2` ([#11315](https://github.com/leanprover-community/mathlib/pull/11315))

### [2022-01-14 08:37:14](https://github.com/leanprover-community/mathlib/commit/fb2b1a0)
fix(algebra/star/basic): redefine `star_ordered_ring` ([#11213](https://github.com/leanprover-community/mathlib/pull/11213))
This PR redefines `star_ordered_ring` to remove the `ordered_semiring` assumption, which includes undesirable axioms such as `∀ (a b c : α), a < b → 0 < c → c * a < c * b`. See the discussion on Zulip [here](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Star.20ordered.20ring).

### [2022-01-14 06:59:50](https://github.com/leanprover-community/mathlib/commit/60c77d4)
feat(tactic/lint): include linter name in github output ([#11413](https://github.com/leanprover-community/mathlib/pull/11413))

### [2022-01-14 06:28:53](https://github.com/leanprover-community/mathlib/commit/d248447)
feat(algebraic_geometry): Gluing schemes ([#11431](https://github.com/leanprover-community/mathlib/pull/11431))

### [2022-01-13 23:16:00](https://github.com/leanprover-community/mathlib/commit/48fd9f2)
chore(data/list/big_operators): rename vars, reorder lemmas ([#11433](https://github.com/leanprover-community/mathlib/pull/11433))
* use better variable names;
* move lemmas to proper sections;
* relax `[comm_semiring R]` to `[semiring R]` in `dvd_sum`.

### [2022-01-13 21:10:22](https://github.com/leanprover-community/mathlib/commit/e830348)
feat(set_theory/ordinal_arithmetic): Families of ordinals ([#11278](https://github.com/leanprover-community/mathlib/pull/11278))
This PR introduces some API to convert from `ι → β` indexed families to `Π o < b, β` indexed families. This simplifies and contextualizes some existing results.

### [2022-01-13 20:16:58](https://github.com/leanprover-community/mathlib/commit/6fa2e46)
feat(algebra/lie/nilpotent): central extensions of nilpotent Lie modules / algebras are nilpotent ([#11422](https://github.com/leanprover-community/mathlib/pull/11422))
The main result is `lie_algebra.nilpotent_of_nilpotent_quotient`.

### [2022-01-13 19:34:18](https://github.com/leanprover-community/mathlib/commit/432e85e)
feat(analysis/normed_space/linear_isometry): add congr_arg and congr_fun ([#11428](https://github.com/leanprover-community/mathlib/pull/11428))
Two trivial lemmas that are missing from this bundled morphism but present on most others.
Turns out I didn't actually need these in the branch I created them in, but we should have them anyway.

### [2022-01-13 19:34:17](https://github.com/leanprover-community/mathlib/commit/8a13846)
feat(analysis/mean_inequalities): Hölder's inequality for infinite sums ([#11314](https://github.com/leanprover-community/mathlib/pull/11314))
State a few versions of Hölder's inequality for infinite sums.
The specific forms of the inequality chosen are parallel to those for Minkowski's inequality in [#10984](https://github.com/leanprover-community/mathlib/pull/10984).

### [2022-01-13 17:57:13](https://github.com/leanprover-community/mathlib/commit/0504425)
feat(analysis/inner_product_space/basic): criterion for summability ([#11224](https://github.com/leanprover-community/mathlib/pull/11224))
In a complete inner product space `E`, a family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(λ i, ∥f i∥ ^ 2)` is summable.

### [2022-01-13 17:19:26](https://github.com/leanprover-community/mathlib/commit/6446ba8)
feat(ring_theory/{trace,norm}): add trace_gen_eq_next_coeff_minpoly and norm_gen_eq_coeff_zero_minpoly  ([#11420](https://github.com/leanprover-community/mathlib/pull/11420))
We add `trace_gen_eq_next_coeff_minpoly` and `norm_gen_eq_coeff_zero_minpoly`.
From flt-regular.

### [2022-01-13 16:52:43](https://github.com/leanprover-community/mathlib/commit/ea9f964)
fix(analysis/calculus/fderiv_symmetric): speed up tactic block from 3.6s to 180ms ([#11426](https://github.com/leanprover-community/mathlib/pull/11426))
The timings are measured for the single small begin/end block. The proof as a whole is still around 7.6s, down from 11s.
The fault here was likely the `convert`, which presumably spent a lot of time trying to unify typeclass arguments.

### [2022-01-13 16:52:42](https://github.com/leanprover-community/mathlib/commit/0f79668)
feat(measure_theory/function/uniform_integrable): Egorov's theorem ([#11328](https://github.com/leanprover-community/mathlib/pull/11328))
This PR proves Egorov's theorem which is necessary for the Vitali convergence theorem which is vital for the martingale convergence theorems.

### [2022-01-13 15:18:51](https://github.com/leanprover-community/mathlib/commit/a16a5b5)
chore(order/lattice_intervals): review ([#11416](https://github.com/leanprover-community/mathlib/pull/11416))
* use `@[reducible] protected def`;
* add `is_least.order_bot` and `is_greatest.order_top`, use them;
* weaken TC assumptions on `set.Ici.bounded_order` and `set.Iic.bounded_order`.

### [2022-01-13 12:25:21](https://github.com/leanprover-community/mathlib/commit/cd4f5c4)
feat(linear_algebra/{cross_product,vectors}): cross product ([#11181](https://github.com/leanprover-community/mathlib/pull/11181))
Defines the cross product for R^3 and gives localized notation for that and the dot product.
Was https://github.com/leanprover-community/mathlib/pull/10959

### [2022-01-13 12:25:20](https://github.com/leanprover-community/mathlib/commit/799cdbb)
feat(data/nat/periodic): periodic functions for nat ([#10888](https://github.com/leanprover-community/mathlib/pull/10888))
Adds a lemma saying that the cardinality of an Ico of length `a` filtered over a periodic predicate of period `a` is the same as the cardinality of `range a` filtered over that predicate.

### [2022-01-13 12:25:18](https://github.com/leanprover-community/mathlib/commit/6609204)
feat(algebraic_geometry): Gluing presheafed spaces ([#10269](https://github.com/leanprover-community/mathlib/pull/10269))

### [2022-01-13 07:08:20](https://github.com/leanprover-community/mathlib/commit/e6db245)
chore(ring_theory/roots_of_unity): change argument order ([#11415](https://github.com/leanprover-community/mathlib/pull/11415))
this is for easier dot notation in situations such as `refine`.

### [2022-01-13 07:08:19](https://github.com/leanprover-community/mathlib/commit/0c84456)
feat(order,data/set/intervals): lemmas about `is_bot`/`is_top` ([#11412](https://github.com/leanprover-community/mathlib/pull/11412))
* add `is_top.Iic_eq`, `is_bot.Ici_eq`, `is_top.Ioi_eq`,
  `is_bot.Iio_eq`, `set.Ioi_top`, `set.Iio_bot`;
* rename `set.Ici_singleton_of_top` and `set.Iic_singleton_of_bot` to
  `is_top.Ici_eq` and `is_bot.Iic_eq`;
* add `is_top_or_exists_gt`, `is_bot_or_exists_lt`, `is_top_top`, and
  `is_bot_bot`;
* add `is_top.to_dual` and `is_bot.to_dual`;
* add `set.empty_ssubset`.

### [2022-01-13 07:08:17](https://github.com/leanprover-community/mathlib/commit/3f1ac6c)
doc(number_theory/cyclotomic/basic): fix docstrings ([#11411](https://github.com/leanprover-community/mathlib/pull/11411))

### [2022-01-13 07:08:16](https://github.com/leanprover-community/mathlib/commit/e839c9a)
feat(combinatorics/configuration): Cardinality results for projective plane. ([#11406](https://github.com/leanprover-community/mathlib/pull/11406))
This PR proves several cardinality results for projective planes (e.g., number of points = number of lines, number of points on given line = number of lines on given point).
It looks like the `exists_config` (whose sole purpose is to rule out [the 7th example here](https://en.wikipedia.org/wiki/Projective_plane#Degenerate_planes)) can be weakened slightly.

### [2022-01-13 06:20:13](https://github.com/leanprover-community/mathlib/commit/12b6b99)
refactor(linear_algebra/affine_space): move def of `slope` to a new file ([#11361](https://github.com/leanprover-community/mathlib/pull/11361))
Also add a few trivial lemmas.

### [2022-01-13 01:42:28](https://github.com/leanprover-community/mathlib/commit/3fed75a)
doc(data/pfun): fix a typo ([#11410](https://github.com/leanprover-community/mathlib/pull/11410))

### [2022-01-13 01:42:26](https://github.com/leanprover-community/mathlib/commit/dfad4c6)
fix(data/equiv/set): Fix doc comment syntax ([#11409](https://github.com/leanprover-community/mathlib/pull/11409))

### [2022-01-13 01:42:25](https://github.com/leanprover-community/mathlib/commit/1f370bb)
feat(linear_algebra/pi): linear_map.vec_cons and friends ([#11343](https://github.com/leanprover-community/mathlib/pull/11343))
The idea of these definitions is to be able to define a map as `x ↦ ![f₁ x, f₂ x, f₃ x]`, where
`f₁ f₂ f₃` are already linear maps, as `f₁.vec_cons $ f₂.vec_cons $ f₃.vec_cons $ vec_empty`.
This adds the same thing for bilinear maps as `x y ↦ ![f₁ x y, f₂ x y, f₃ x y]`.
While the same thing could be achieved using `linear_map.pi ![f₁, f₂, f₃]`, this is not
definitionally equal to the result using `linear_map.vec_cons`, as `fin.cases` and function
application do not commute definitionally.
Versions for when `f₁ f₂ f₃` are bilinear maps are also provided.

### [2022-01-12 22:49:45](https://github.com/leanprover-community/mathlib/commit/e6fab1d)
refactor(order/directed): Make `is_directed` a Prop mixin ([#11238](https://github.com/leanprover-community/mathlib/pull/11238))
This turns `directed_order` into a Prop-valued mixin `is_directed`. The design follows the unbundled relation classes found in core Lean.
The current design created obscure problems when showing that a `semilattice_sup` is directed and we couldn't even state that `semilattice_inf` is codirected. Further, it was kind of already used as a mixin, because there was no point inserting it in the hierarchy.

### [2022-01-12 20:51:38](https://github.com/leanprover-community/mathlib/commit/2a38097)
feat(combinatorics/configuration): Define projective planes ([#11390](https://github.com/leanprover-community/mathlib/pull/11390))
This PR defines abstract projective planes and their duals. More will be PRed later.

### [2022-01-12 17:52:39](https://github.com/leanprover-community/mathlib/commit/5e48b21)
feat(number_theory/cyclotomic/basic): add cyclotomic_field and cyclotomic_ring ([#11383](https://github.com/leanprover-community/mathlib/pull/11383))
We add `cyclotomic_field` and `cyclotomic_ring`, that provide an explicit cyclotomic extension of a given field/ring.
From flt-regular

### [2022-01-12 17:52:38](https://github.com/leanprover-community/mathlib/commit/fa9d2bf)
feat(data/mv_polynomial/variables): add mv_polynomial.total_deg_finset_sum ([#11375](https://github.com/leanprover-community/mathlib/pull/11375))
Total degree of a sum of mv_polynomials is less than or equal to the maximum of all their degrees.

### [2022-01-12 17:52:37](https://github.com/leanprover-community/mathlib/commit/258686f)
fix(order/complete_lattice): fix diamond in sup vs max and min vs inf ([#11309](https://github.com/leanprover-community/mathlib/pull/11309))
`complete_linear_order` has separate `max` and `sup` fields. There is no need to have both, so this removes one of them by telling the structure compiler to merge the two fields. The same is true of `inf` and `min`.
As well as diamonds being possible in the abstract case, a handful of concrete example of this diamond existed.
`linear_order` instances with default-populated fields were usually to blame.

### [2022-01-12 16:25:20](https://github.com/leanprover-community/mathlib/commit/975031d)
feat(data/nat/factorization): add lemma `factorization_prod` ([#11395](https://github.com/leanprover-community/mathlib/pull/11395))
For any `p : ℕ` and any function `g : α → ℕ` that's non-zero on `S : finset α`, the power of `p` in `S.prod g` equals the sum over `x ∈ S` of the powers of `p` in `g x`.
Generalises `factorization_mul`, which is the special case where `S.card = 2` and `g = id`.

### [2022-01-12 16:25:17](https://github.com/leanprover-community/mathlib/commit/67593dc)
fix(tactic/ring_exp): fix normalization proof of unchanged subexpressions ([#11394](https://github.com/leanprover-community/mathlib/pull/11394))
When trying to simplify a goal (instead of proving equalities), `ring_exp` will rewrite subexpressions to a normal form, then simplify this normal form by removing extraneous `+ 0`s and `* 1`s. Both steps return a new expression and a proof that the *step*'s input expression equals the output expression.
In some cases where the normal form and simplified form coincide, `ex.simplify` would instead output a proof that *ring_exp*'s input expression equals the output expression, so we'd get a type error in trying to compose a proof that `a = b` with a proof that `a = b`.
This PR fixes that bug by returning instead a proof that `b = b`, as expected.

### [2022-01-12 13:36:56](https://github.com/leanprover-community/mathlib/commit/aece00a)
feat(data/sigma/interval): A disjoint sum of locally finite orders is locally finite ([#10929](https://github.com/leanprover-community/mathlib/pull/10929))
This provides `locally_finite_order (Σ i, α i)` in a new file `data.sigma.interval`. This also makes `<` a primitive on `Σ i, α i`.

### [2022-01-12 11:08:51](https://github.com/leanprover-community/mathlib/commit/e8eb7d9)
feat(order/cover): `f a` covers `f b` iff `a` covers `b`  ([#11392](https://github.com/leanprover-community/mathlib/pull/11392))
... for order isomorphisms, and also weaker statements.

### [2022-01-12 10:06:13](https://github.com/leanprover-community/mathlib/commit/912c47d)
feat(topology/algebra/continuous_monoid_hom): New file ([#11304](https://github.com/leanprover-community/mathlib/pull/11304))
This PR defines continuous monoid homs.

### [2022-01-12 07:31:06](https://github.com/leanprover-community/mathlib/commit/c1f3f1a)
feat(analysis/complex/basic): determinant of `conj_lie` ([#11389](https://github.com/leanprover-community/mathlib/pull/11389))
Add lemmas giving the determinant of `conj_lie`, as a linear map and
as a linear equiv, deduced from the corresponding lemmas for `conj_ae`
which is used to define `conj_lie`.  This completes the basic lemmas
about determinants of linear isometries of `ℂ` (which can thus be used
to talk about how those isometries affect orientations), since we also
have `linear_isometry_complex` describing all such isometries in terms
of `rotation` and `conj_lie`.

### [2022-01-12 07:31:04](https://github.com/leanprover-community/mathlib/commit/72c86c3)
chore(algebra/ring/basic): generalize `is_domain.to_cancel_monoid_with_zero` to `no_zero_divisors` ([#11387](https://github.com/leanprover-community/mathlib/pull/11387))
This generalization doesn't work for typeclass search as `cancel_monoid_with_zero` implies `no_zero_divisors` which would form a loop, but it can be useful for a `letI` in another proof.
Independent of whether this turns out to be useful, it's nice to show that nontriviality doesn't affect the fact that rings with no zero divisors are cancellative.

### [2022-01-12 07:31:03](https://github.com/leanprover-community/mathlib/commit/cb1b6d9)
feat(algebra/order/floor): adds some missing floor API ([#11336](https://github.com/leanprover-community/mathlib/pull/11336))

### [2022-01-12 07:31:02](https://github.com/leanprover-community/mathlib/commit/bfe9515)
feat(data/multiset/basic): add map_count_true_eq_filter_card ([#11306](https://github.com/leanprover-community/mathlib/pull/11306))
Add a lemma about counting over a map. Spun off of [#10888](https://github.com/leanprover-community/mathlib/pull/10888).

### [2022-01-12 07:31:00](https://github.com/leanprover-community/mathlib/commit/9fd03e1)
chore(order/lexicographic): cleanup ([#11299](https://github.com/leanprover-community/mathlib/pull/11299))
Changes include:
* factoring out `prod.lex.trans` from the proof of `le_trans` in `prod.lex.has_le`, and similarly for `antisymm` and `is_total`
* adding some missing `to_lex` annotations in the `prod.lex.{le,lt}_def` lemmas
* avoiding reproving decidability of `prod.lex`
* replacing some proofs with pattern matching to avoid getting type-incorrect goals where `prod.lex.has_le` appears comparing terms that are not of type `lex`.

### [2022-01-12 07:30:59](https://github.com/leanprover-community/mathlib/commit/deac58a)
feat(topology/uniform_space/compact_convergence): when the domain is locally compact, compact convergence is just locally uniform convergence ([#11292](https://github.com/leanprover-community/mathlib/pull/11292))
Also, locally uniform convergence is just uniform convergence when the domain is compact.

### [2022-01-12 07:30:58](https://github.com/leanprover-community/mathlib/commit/2099725)
feat(topology/homotopy/product): Product of homotopic paths ([#11153](https://github.com/leanprover-community/mathlib/pull/11153))
Specialize homotopy products to paths and prove some theorems about the product of paths.

### [2022-01-12 05:04:58](https://github.com/leanprover-community/mathlib/commit/15b5e24)
feat(data/polynomial/taylor): taylor's formula ([#11139](https://github.com/leanprover-community/mathlib/pull/11139))
Via proofs about `hasse_deriv`.
Added some monomial API too.

### [2022-01-12 04:02:53](https://github.com/leanprover-community/mathlib/commit/af074c8)
feat(analysis/normed_space/lp_space): API for `lp.single` ([#11307](https://github.com/leanprover-community/mathlib/pull/11307))
Definition and basic properties for `lp.single`, an element of `lp` space supported at one point.

### [2022-01-12 02:31:11](https://github.com/leanprover-community/mathlib/commit/cdd44cd)
refactor(topology/algebra/uniform_group): Use `to_additive` ([#11366](https://github.com/leanprover-community/mathlib/pull/11366))
This PR replace the definition
`def topological_add_group.to_uniform_space : uniform_space G :=`
with the definition
`@[to_additive] def topological_group.to_uniform_space : uniform_space G :=`

### [2022-01-12 00:08:22](https://github.com/leanprover-community/mathlib/commit/89f4786)
feat(analysis/special_functions/pow): norm_num extension for rpow ([#11382](https://github.com/leanprover-community/mathlib/pull/11382))
Fixes [#11374](https://github.com/leanprover-community/mathlib/pull/11374)

### [2022-01-12 00:08:21](https://github.com/leanprover-community/mathlib/commit/647598b)
feat(data/nat/factorization): add lemma `factorization_le_iff_dvd` ([#11377](https://github.com/leanprover-community/mathlib/pull/11377))
For non-zero `d n : ℕ`, `d.factorization ≤ n.factorization ↔ d ∣ n`

### [2022-01-11 20:49:16](https://github.com/leanprover-community/mathlib/commit/a5f7909)
fix(algebra/tropical/basic): provide explicit min and max ([#11380](https://github.com/leanprover-community/mathlib/pull/11380))
This also renames `tropical.add` to `tropical.has_add`, since this matches how we normally do this, and it makes unfolding easier.
Without this change, we have a diamond where `linear_order.min` is not defeq to `lattice.inf`.

### [2022-01-11 20:49:15](https://github.com/leanprover-community/mathlib/commit/73847ff)
feat(algebra/indicator_function): add primed version for `mul_indicator_mul` and `indicator_sub` ([#11379](https://github.com/leanprover-community/mathlib/pull/11379))

### [2022-01-11 20:49:14](https://github.com/leanprover-community/mathlib/commit/d1c4961)
feat(data/real/ennreal): add ennreal lemma for `a / 3 + a / 3 + a / 3 = a`  ([#11378](https://github.com/leanprover-community/mathlib/pull/11378))

### [2022-01-11 20:49:13](https://github.com/leanprover-community/mathlib/commit/57a8933)
feat(group_theory/free_group): promote free_group_congr to a mul_equiv ([#11373](https://github.com/leanprover-community/mathlib/pull/11373))
Also some various golfs and cleanups

### [2022-01-11 20:49:12](https://github.com/leanprover-community/mathlib/commit/8db96a8)
feat(combinatorics/double_counting): Double-counting the edges of a bipartite graph ([#11372](https://github.com/leanprover-community/mathlib/pull/11372))
This proves a classic of double-counting arguments: If each element of the `|α|` elements on the left is connected to at least `m` elements on the right and each of the `|β|` elements on the right is connected to at most `n` elements on the left, then `|α| * m ≤ |β| * n` because the LHS is less than the number of edges which is less than the RHS.
This is put in a new file `combinatorics.double_counting` with the idea that we could gather double counting arguments here, much as is done with `combinatorics.pigeonhole`.

### [2022-01-11 20:49:11](https://github.com/leanprover-community/mathlib/commit/93e7741)
feat(ring_theory/witt_vector): Witt vectors over a domain are a domain ([#11346](https://github.com/leanprover-community/mathlib/pull/11346))

### [2022-01-11 20:49:09](https://github.com/leanprover-community/mathlib/commit/83b0355)
feat(analysis/complex/isometry): `rotation` matrix representation and determinant ([#11339](https://github.com/leanprover-community/mathlib/pull/11339))
Add lemmas giving the matrix representation of `rotation` (with
respect to `basis_one_I`), and its determinant (both as a linear map
and as a linear equiv).  This is preparation for doing things about
how isometries affect orientations.

### [2022-01-11 20:49:08](https://github.com/leanprover-community/mathlib/commit/e4a41e6)
feat(data/complex/module,data/complex/determinant): `conj_ae` matrix representation and determinant ([#11337](https://github.com/leanprover-community/mathlib/pull/11337))
Add lemmas giving the matrix representation of `conj_ae` (with respect
to `basis_one_I`), and its determinant (both as a linear map and as a
linear equiv).  This is preparation for doing things about how
isometries affect orientations (so it's actually `conj_lie` I'm
interested in, but `conj_lie` is defined in terms of `conj_ae` so
proving things first for `conj_ae` seems appropriate).

### [2022-01-11 20:49:07](https://github.com/leanprover-community/mathlib/commit/aa7a439)
feat(algebra/*): injective hom into kernel `map_eq_*_iff` ([#11275](https://github.com/leanprover-community/mathlib/pull/11275))

### [2022-01-11 20:49:06](https://github.com/leanprover-community/mathlib/commit/94fd004)
feat(order/minimal): Subset of minimal/maximal elements ([#11268](https://github.com/leanprover-community/mathlib/pull/11268))
This defines `minimals r s`/`maximals r s` the minimal/maximal elements of `s` with respect to relation `r`.

### [2022-01-11 20:49:04](https://github.com/leanprover-community/mathlib/commit/490847e)
feat(data/polynomial/degree/lemmas): add induction principle for non-constant polynomials ([#8463](https://github.com/leanprover-community/mathlib/pull/8463))
This PR introduces an induction principle to prove that a property holds for non-constant polynomials.  It suffices to check that the property holds for
* the sum of a constant polynomial and any polynomial for which the property holds;
* the sum of any two polynomials for which the property holds;
* for non-constant monomials.
I plan to use this to show that polynomials with coefficients in `ℕ` are monotone.

### [2022-01-11 17:36:45](https://github.com/leanprover-community/mathlib/commit/b710771)
chore(*): update to 3.38.0c ([#11371](https://github.com/leanprover-community/mathlib/pull/11371))

### [2022-01-11 13:55:35](https://github.com/leanprover-community/mathlib/commit/b8d2aff)
refactor(ring_theory/discriminant): refactor discr_not_zero_of_linear_independent ([#11370](https://github.com/leanprover-community/mathlib/pull/11370))
`(hcard : fintype.card ι = finite_dimensional.finrank K L) (hli : linear_independent K b)` is better expressed as `b : basis ι K L`.

### [2022-01-11 13:55:34](https://github.com/leanprover-community/mathlib/commit/380e28e)
chore(set_theory/ordinal_arithmetic): Golfed some proofs ([#11369](https://github.com/leanprover-community/mathlib/pull/11369))

### [2022-01-11 13:55:33](https://github.com/leanprover-community/mathlib/commit/2963d7c)
feat(analysis/asymptotics/asymptotics): add `is_bounded_under.is_O_const` ([#11367](https://github.com/leanprover-community/mathlib/pull/11367))

### [2022-01-11 13:55:32](https://github.com/leanprover-community/mathlib/commit/8f5303a)
refactor(topology/connected): drop `local attribute [instance] connected_component_setoid` ([#11365](https://github.com/leanprover-community/mathlib/pull/11365))
Add a coercion from `X` to `connected_components X` instead.

### [2022-01-11 13:55:30](https://github.com/leanprover-community/mathlib/commit/c1c0fa4)
feat(analysis/calculus/{f,}deriv): add some `iff` lemmas ([#11363](https://github.com/leanprover-community/mathlib/pull/11363))

### [2022-01-11 13:55:28](https://github.com/leanprover-community/mathlib/commit/02181c7)
feat(algebra/group/conj): `conj_classes.map` preserves surjectivity ([#11362](https://github.com/leanprover-community/mathlib/pull/11362))
If `f : α →* β` is surjective, then so is `conj_classes.map f : conj_classes α → conj_classes β`.

### [2022-01-11 13:55:13](https://github.com/leanprover-community/mathlib/commit/c94a17c)
feat(topology): a few simple lemmas ([#11360](https://github.com/leanprover-community/mathlib/pull/11360))

### [2022-01-11 13:55:12](https://github.com/leanprover-community/mathlib/commit/56d6a91)
chore(order/basic): Rename `no_bot_order`/`no_top_order` to `no_min_order`/`no_max_order` ([#11357](https://github.com/leanprover-community/mathlib/pull/11357))
because that's really what they are.
`∀ a, ∃ b, b < a` precisely means that every `a` is not a minimal element. The correct statement for an order without bottom elements is `∀ a, ∃ b, ¬ a ≤ b`, which is a weaker condition in general. Both conditions are equivalent over a linear order.
Renames
* `no_bot_order` -> `no_min_order`
* `no_top_order` -> `no_max_order`
* `no_bot` -> `exists_lt`
* `no_top` -> `exists_gt`

### [2022-01-11 13:55:09](https://github.com/leanprover-community/mathlib/commit/be4c5aa)
feat(scripts/lint_mathlib): implement github annotations for mathlib linters ([#11345](https://github.com/leanprover-community/mathlib/pull/11345))
Resolves the last part of [#5863](https://github.com/leanprover-community/mathlib/pull/5863)
This causes `lean --run lint_mathlib --github` to produce error messages understood by github actions, which will tag the lines causing linter failures with annotations in the files changed tab

### [2022-01-11 13:55:08](https://github.com/leanprover-community/mathlib/commit/e138d3b)
feat(algebra/big_operators/finprod): `finprod_eq_one_of_forall_eq_one` ([#11335](https://github.com/leanprover-community/mathlib/pull/11335))

### [2022-01-11 13:55:07](https://github.com/leanprover-community/mathlib/commit/eb9c152)
feat(algebra/order/field): lemmas relating `a / b` and `a` when `1 ≤ b` and `1 < b` ([#11333](https://github.com/leanprover-community/mathlib/pull/11333))
This PR is a collection of items that https://github.com/leanprover-community/mathlib/pull/7891 adds in and that aren't declared on `master` yet. Please let me know if I overlooked something.
After merging it, https://github.com/leanprover-community/mathlib/pull/7891 can theoretically be closed.

### [2022-01-11 13:55:05](https://github.com/leanprover-community/mathlib/commit/2865d8c)
refactor(data/set/prod): add notation class for set-like product ([#11300](https://github.com/leanprover-community/mathlib/pull/11300))
This PR adds notation class `has_set_prod` for product of sets and subobjects. I also add an instance for `set`s. Later I want to migrate `finset`s and `sub*` product to this notation class.

### [2022-01-11 13:55:04](https://github.com/leanprover-community/mathlib/commit/3cd9088)
feat(ring_theory/polynomial/cyclotomic/basic): add lemmas  ([#11266](https://github.com/leanprover-community/mathlib/pull/11266))
From flt-regular.

### [2022-01-11 13:55:02](https://github.com/leanprover-community/mathlib/commit/4ac13d9)
feat(data/dfinsupp/interval): Finitely supported dependent functions to locally finite orders are locally finite ([#11175](https://github.com/leanprover-community/mathlib/pull/11175))
This provides the ` locally_finite_order` instance for `Π₀ i, α i` in a new file `data.dfinsupp.interval`.

### [2022-01-11 11:13:20](https://github.com/leanprover-community/mathlib/commit/40b6b45)
feat(category_theory): `Cat` is a strict bicategory ([#11348](https://github.com/leanprover-community/mathlib/pull/11348))
This PR defines a bicategory structure on `Cat`. This also introduces the propositional type class `bicategory.strict`, and proves that `Cat` is an instance of this class.

### [2022-01-11 11:13:19](https://github.com/leanprover-community/mathlib/commit/a4052f9)
feat(ring_theory/hahn_series): order_pow ([#11334](https://github.com/leanprover-community/mathlib/pull/11334))
Generalize to have `no_zero_divisors (hahn_series Γ R)`,
which generalizes `order_mul`.
Also provide `coeff_eq_zero_of_lt_order`.

### [2022-01-11 11:13:18](https://github.com/leanprover-community/mathlib/commit/90ba054)
feat(algebraic_geometry): Define the category of `AffineScheme`s ([#11326](https://github.com/leanprover-community/mathlib/pull/11326))

### [2022-01-11 11:13:17](https://github.com/leanprover-community/mathlib/commit/c03bd32)
feat(analysis/normed_space/star): add lemmas about continuity and norm of identity ([#11324](https://github.com/leanprover-community/mathlib/pull/11324))

### [2022-01-11 11:13:16](https://github.com/leanprover-community/mathlib/commit/ebbc973)
feat(data/mv_polynomial): assorted mv_polynomial and finsupp lemmas ([#11319](https://github.com/leanprover-community/mathlib/pull/11319))
Mostly around total degree, supports and homogeneous components.
From flt-regular.

### [2022-01-11 11:13:15](https://github.com/leanprover-community/mathlib/commit/c500b99)
feat(ring_theory/laurent): coe from R[[x]] to R((x)) ([#11318](https://github.com/leanprover-community/mathlib/pull/11318))
And actually the changes reported in [#11295](https://github.com/leanprover-community/mathlib/pull/11295)
Generalize `power_series.coeff_smul`

### [2022-01-11 11:13:14](https://github.com/leanprover-community/mathlib/commit/be594eb)
feat(linear_algebra/finite_dimensional): Define rank of set of vectors ([#11290](https://github.com/leanprover-community/mathlib/pull/11290))
Added in the definition of "rank of a set of vectors" and a useful lemma about the rank when one set is a subset of the other.
Read the zulip stream here: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/First.20Time.20Contributing

### [2022-01-11 11:13:13](https://github.com/leanprover-community/mathlib/commit/b7f8f72)
feat(category_theory/bicategory/functor): define oplax functors and their composition ([#11277](https://github.com/leanprover-community/mathlib/pull/11277))
This PR defines oplax functors between bicategories and their composition.

### [2022-01-11 11:13:11](https://github.com/leanprover-community/mathlib/commit/624cb70)
feat(set_theory/ordinal_arithmetic): Extra lemmas about suprema ([#11178](https://github.com/leanprover-community/mathlib/pull/11178))
Proved lemmas pertaining to when suprema or least strict upper bounds are zero.

### [2022-01-11 08:13:33](https://github.com/leanprover-community/mathlib/commit/de9944b)
refactor(analysis/complex/circle): The circle group is commutative ([#11368](https://github.com/leanprover-community/mathlib/pull/11368))
This PR upgrades the `group circle` instance to a `comm_group circle` instance.

### [2022-01-11 08:13:31](https://github.com/leanprover-community/mathlib/commit/e8839a3)
refactor(logic/small, *): Infer `f : α → β` when followed by a simple condition on `f` ([#11037](https://github.com/leanprover-community/mathlib/pull/11037))

### [2022-01-11 02:45:39](https://github.com/leanprover-community/mathlib/commit/89bff5e)
feat(algebra/big_operators): add product versions of some sum lemmas ([#11358](https://github.com/leanprover-community/mathlib/pull/11358))
and to_additive to get the old ones back

### [2022-01-11 02:45:38](https://github.com/leanprover-community/mathlib/commit/d8a75bd)
chore(simple_graph/basic): Fix typo in docstring: adjacent vertices, not edges ([#11356](https://github.com/leanprover-community/mathlib/pull/11356))

### [2022-01-10 23:30:59](https://github.com/leanprover-community/mathlib/commit/8910f6d)
feat(ring_theory/discriminant): remove an assumption ([#11359](https://github.com/leanprover-community/mathlib/pull/11359))
We remove a `nonempty` assumption.

### [2022-01-10 23:30:58](https://github.com/leanprover-community/mathlib/commit/fd51bda)
feat(analysis/normed_space/linear_isometry): basis ext lemmas ([#11331](https://github.com/leanprover-community/mathlib/pull/11331))
Add lemmas that two linear isometries / linear isometric equivalences
are equal if they are equal on basis vectors, similar to such lemmas
for equality on basis vectors of other kinds of maps.

### [2022-01-10 23:30:57](https://github.com/leanprover-community/mathlib/commit/3b55b94)
feat(analysis/inner_product_space/basic): inner products of linear combinations of orthonormal vectors ([#11323](https://github.com/leanprover-community/mathlib/pull/11323))
There are some lemmas about the inner product of a linear combination
of orthonormal vectors with one vector from that orthonormal family.
Add similar lemmas where both sides of the inner product are linear
combinations.

### [2022-01-10 23:30:55](https://github.com/leanprover-community/mathlib/commit/fd52481)
feat(group_theory/abelianization): Add fintype instance ([#11302](https://github.com/leanprover-community/mathlib/pull/11302))
Adds `fintype` instance for `abelianization`.

### [2022-01-10 23:30:54](https://github.com/leanprover-community/mathlib/commit/2642c89)
feat(analysis/inner_product_space/orientation): orientations of real inner product spaces ([#11269](https://github.com/leanprover-community/mathlib/pull/11269))
Add definitions and lemmas relating to orientations of real inner
product spaces, in particular constructing an orthonormal basis with a
given orientation in finite positive dimension.
This is in a new file since nothing else about inner product spaces
needs to depend on orientations.

### [2022-01-10 23:30:52](https://github.com/leanprover-community/mathlib/commit/4e7e5a6)
feat(set_theory/ordinal_arithmetic): Enumerating unbounded sets of ordinals with ordinals ([#10979](https://github.com/leanprover-community/mathlib/pull/10979))
This PR introduces `enum_ord`, which enumerates an unbounded set of ordinals using ordinals. This is used to build an explicit order isomorphism `enum_ord.order_iso`.

### [2022-01-10 23:30:51](https://github.com/leanprover-community/mathlib/commit/8e92af1)
feat(algebra/associated): add lemmas to split [#9345](https://github.com/leanprover-community/mathlib/pull/9345) ([#10941](https://github.com/leanprover-community/mathlib/pull/10941))
This PR contains lemmas from PR [[#9345](https://github.com/leanprover-community/mathlib/pull/9345)](https://github.com/leanprover-community/mathlib/pull/9345), which was starting to get quite lengthy.

### [2022-01-10 23:30:50](https://github.com/leanprover-community/mathlib/commit/4bf4859)
feat(data/finsupp/pointwise): add a definition of the pointwise action of functions on finsupps ([#10933](https://github.com/leanprover-community/mathlib/pull/10933))
I couldn't find this, and it seems like quite a natural way to talk about multiplying functions with finsupps.
I'm not sure what additional lemmas would be useful yet, as I don't have a particular application in mind at present so suggestions/additions are welcome

### [2022-01-10 19:54:28](https://github.com/leanprover-community/mathlib/commit/2e003c9)
feat(data/set/basic): add decidable instances for boolean operations ([#11354](https://github.com/leanprover-community/mathlib/pull/11354))
Add decidability instances for `a ∈ s ∩ t`, etc.

### [2022-01-10 19:54:26](https://github.com/leanprover-community/mathlib/commit/427e5b5)
feat(data/nat/factorization): Evaluating a multiplicative function over prime power divisors ([#11167](https://github.com/leanprover-community/mathlib/pull/11167))
For any multiplicative function `f` with `f 1 = 1` and any `n > 0`, we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n`.
Also provides an alternative version that swaps the `0 < n` condition for an extra `f 0 = 1` condition, as suggested by @ericrbg. 
This allows a very simple proof that `n.factorization.prod pow = n`

### [2022-01-10 16:17:20](https://github.com/leanprover-community/mathlib/commit/dc3cbb7)
feat(data/polynomial/erase_lead): introduce two lemmas to compute `nat_degree`s under certain maps ([#11265](https://github.com/leanprover-community/mathlib/pull/11265))
This PR is a step in the direction of simplifying [#11139](https://github.com/leanprover-community/mathlib/pull/11139).
It contains a proof of the helper lemmas `map_nat_degree_eq_sub` and `map_nat_degree_eq_nat_degree` to shorten the proof of `nat_degree_hasse_deriv` and `nat_degree_taylor`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2311139.20taylor.20sum.20and.20nat_degree_taylor)

### [2022-01-10 16:17:19](https://github.com/leanprover-community/mathlib/commit/168ad7f)
feat(data/nat/cast): generalize to `fun_like` ([#11128](https://github.com/leanprover-community/mathlib/pull/11128))

### [2022-01-10 13:08:00](https://github.com/leanprover-community/mathlib/commit/1533f15)
feat(logic/basic): add eq_true_eq_id ([#11341](https://github.com/leanprover-community/mathlib/pull/11341))
Adds the simp lemma `eq_true_eq_id : eq true = id`, a sort of curried version of `eq_true : (a = true) = a` in core.

### [2022-01-10 13:07:59](https://github.com/leanprover-community/mathlib/commit/fabc510)
feat(linear_algebra/determinant): `linear_equiv.det_conj` ([#11340](https://github.com/leanprover-community/mathlib/pull/11340))
Add a version of the `linear_map.det_conj` lemma for `linear_equiv.det`.

### [2022-01-10 13:07:57](https://github.com/leanprover-community/mathlib/commit/48b21e5)
feat(probability_theory/martingale): one direction of the optional stopping theorem ([#11007](https://github.com/leanprover-community/mathlib/pull/11007))

### [2022-01-10 10:18:16](https://github.com/leanprover-community/mathlib/commit/7782157)
feat (data/finset/lattice): add more finset induction lemmas ([#10889](https://github.com/leanprover-community/mathlib/pull/10889))
2 more finset induction lemmas based on the order imposed by a function.

### [2022-01-10 01:23:46](https://github.com/leanprover-community/mathlib/commit/99fe7ac)
chore(data/set/function): move inv_fun_on out of `logic/function/basic` ([#11330](https://github.com/leanprover-community/mathlib/pull/11330))
This removes `function.inv_fun_on_eq'` as it is a duplicate of `inj_on.left_inv_on_inv_fun_on`.

### [2022-01-09 23:15:30](https://github.com/leanprover-community/mathlib/commit/6a10939)
fix(docs/references.bib): syntax error ([#11342](https://github.com/leanprover-community/mathlib/pull/11342))
This broke the docs build.

### [2022-01-09 21:08:06](https://github.com/leanprover-community/mathlib/commit/ce17b65)
feat(topology/algebra/monoid): to_additivize some lemmas ([#11310](https://github.com/leanprover-community/mathlib/pull/11310))
Uncomment a commented out to additive line that looks like its been there
for 3 years (since
https://github.com/leanprover-community/mathlib/commit/581cf19bf1885ef874c39c9902a93f579bc8c22d)
The changes to to_additive in the past few years now make the
generated lemma useful.
Also to_additivize a bunch of other lemmas in this file.

### [2022-01-09 18:06:11](https://github.com/leanprover-community/mathlib/commit/d13b3a4)
chore(*): update to 3.37.0c ([#11325](https://github.com/leanprover-community/mathlib/pull/11325))
the major breaking change this version is making `default`'s parameters
implicit, as opposed to explicit. there was also some slight "free"
golfing due to the better `out_param` simp support.

### [2022-01-09 18:06:09](https://github.com/leanprover-community/mathlib/commit/47a8d5a)
refactor(data/{sigma,psigma}/order): Use `lex` synonym and new notation ([#11235](https://github.com/leanprover-community/mathlib/pull/11235))
This introduces notations `Σₗ i, α i` and `Σₗ' i, α i` for `lex (Σ i, α i)` and `lex (Σ' i, α i)` and use them instead of the instance switch with locale `lex`.

### [2022-01-09 16:18:25](https://github.com/leanprover-community/mathlib/commit/2bb25f0)
feat(algebra/periodic): lifting to function on quotient group ([#11321](https://github.com/leanprover-community/mathlib/pull/11321))
I want to make more use of the type `real.angle` in
`analysis.special_functions.trigonometric.angle`, including defining
functions from this type in terms of periodic functions from `ℝ`.  To
support defining such functions, add a definition `periodic.lift` that
lifts a periodic function from `α` to a function from
`α ⧸ (add_subgroup.zmultiples c)`, along with a lemma
`periodic.lift_coe` about the values of the resulting function.

### [2022-01-09 16:18:24](https://github.com/leanprover-community/mathlib/commit/49ba33e)
feat(vscode): add a snippet for inserting a module docstring template ([#11312](https://github.com/leanprover-community/mathlib/pull/11312))
We already have a vscode snippet for adding copyright headers, this PR adds a similar one to generate a default module docstring with many of the common sections stubbed out.
By default it takes the filename, converts underscores to spaces and capitalizes each word to create the title, as this seems a sensible default. But otherwise all text is a static default example following the documentation style page to make it easier to remember the various recommended secitons.
To test do `ctrl+shift+p` to open the command pallette, type insert snippet, enter, and type module and it should show up.
See also [#3186](https://github.com/leanprover-community/mathlib/pull/3186)

### [2022-01-09 16:18:23](https://github.com/leanprover-community/mathlib/commit/fadbd95)
feat(field_theory/ratfunc): ratfunc.lift_on without is_domain ([#11227](https://github.com/leanprover-community/mathlib/pull/11227))
We might want to state results about rational functions without assuming
that the base ring is an integral domain.
Cf. Misconceptions about $K_X$, Kleiman, Steven; Stacks01X1

### [2022-01-09 13:09:57](https://github.com/leanprover-community/mathlib/commit/9c224ff)
split(data/set/functor): Split off `data.set.lattice` ([#11327](https://github.com/leanprover-community/mathlib/pull/11327))
This moves the functor structure of `set` in a new file `data.set.functor`.
Also adds `alternative set` because it's quick and easy.

### [2022-01-09 07:58:15](https://github.com/leanprover-community/mathlib/commit/ad4ea53)
chore(*): miscellaneous to_additive related cleanup ([#11316](https://github.com/leanprover-community/mathlib/pull/11316))
A few cleanup changes related to to_additive:
* After https://github.com/leanprover-community/lean/pull/618 was merged, we no longer need to add namespaces manually in filtered_colimits and open subgroup
* to_additive can now generate some more lemmas in big_operators/fin
* to_additive now handles a proof in measure/haar better than it used to
  so remove a workaround there

### [2022-01-09 06:06:07](https://github.com/leanprover-community/mathlib/commit/ca5e55c)
feat(linear_algebra/basis): `basis.ext`, `basis.ext'` for semilinear maps ([#11317](https://github.com/leanprover-community/mathlib/pull/11317))
Extend `basis.ext` and `basis.ext'` to apply to the general
(semilinear) case of `linear_map` and `linear_equiv`.

### [2022-01-09 03:54:54](https://github.com/leanprover-community/mathlib/commit/a58553d)
feat(data/nat/factorization): Add lemmas on factorizations of pairs of coprime numbers ([#10850](https://github.com/leanprover-community/mathlib/pull/10850))

### [2022-01-09 01:21:32](https://github.com/leanprover-community/mathlib/commit/d4846b3)
chore(ring_theory/fractional_ideal): fix typo ([#11311](https://github.com/leanprover-community/mathlib/pull/11311))

### [2022-01-08 23:10:53](https://github.com/leanprover-community/mathlib/commit/22ff4eb)
feat(combinatorics/simple_graph/matchings): even_card_vertices_of_perfect_matching ([#11083](https://github.com/leanprover-community/mathlib/pull/11083))

### [2022-01-08 21:54:48](https://github.com/leanprover-community/mathlib/commit/0a75fdf)
feat(linear_algebra/eigenspace): prove eigenvalues are exactly elements of the spectrum when the space is finite dimensional ([#10961](https://github.com/leanprover-community/mathlib/pull/10961))
This adds `has_eigenvalue_iff_mem_spectrum` and then uses it to golf `exists_eigenvalue`
- [x] depends on: [#10912](https://github.com/leanprover-community/mathlib/pull/10912) 
- [x] depends on: [#10919](https://github.com/leanprover-community/mathlib/pull/10919)

### [2022-01-08 18:36:59](https://github.com/leanprover-community/mathlib/commit/ee136d9)
chore(set_theory/game/domineering): extract repeated goal into lemma and golf ([#11298](https://github.com/leanprover-community/mathlib/pull/11298))
`fst_pred_mem_erase_of_mem_right` and `snd_pred_mem_erase_of_mem_left` were common subgoals that appeared in two lemmas each.

### [2022-01-08 18:36:57](https://github.com/leanprover-community/mathlib/commit/84dbe31)
feat(topology/basic): add explicit definition of continuous_at ([#11296](https://github.com/leanprover-community/mathlib/pull/11296))
This was convenient in a demo.

### [2022-01-08 18:36:56](https://github.com/leanprover-community/mathlib/commit/25704ca)
docs(algebra/covariant_and_contravariant): minor typos ([#11293](https://github.com/leanprover-community/mathlib/pull/11293))

### [2022-01-08 18:36:54](https://github.com/leanprover-community/mathlib/commit/09f6989)
chore(analysis/normed_space/banach): move more to the `continuous_linear_map` NS ([#11263](https://github.com/leanprover-community/mathlib/pull/11263))
## Rename
* `open_mapping` → `continuous_linear_map.is_open_map`;
* `open_mapping_affine` → `affine_map.is_open_map`;
### New lemmas
* `continuous_linear_map.quotient_map`,
* `continuous_linear_map.interior_preimage`,
* `continuous_linear_map.closure_preimage`,
* `continuous_linear_map.frontier_preimage`.

### [2022-01-08 18:36:52](https://github.com/leanprover-community/mathlib/commit/60e279b)
chore(*): update to lean 3.36.0 ([#11253](https://github.com/leanprover-community/mathlib/pull/11253))
The main breaking change is the change in elaboration of double membership binders into x hx y hy, from x y hx hy.

### [2022-01-08 16:29:06](https://github.com/leanprover-community/mathlib/commit/dd1242d)
feat(algebra/associated): generalize nat.prime.pow_dvd_of_dvd_mul_{left,right} ([#11301](https://github.com/leanprover-community/mathlib/pull/11301))

### [2022-01-08 16:29:05](https://github.com/leanprover-community/mathlib/commit/c76e113)
feat(ring_theory/laurent): coercion of R[x] to R((x)) lemmas ([#11295](https://github.com/leanprover-community/mathlib/pull/11295))
Make the coercion be `simp`-normal as opposed to `(algebra_map _ _)`.
Also generalize `of_power_series Γ R (power_series.C R r) = hahn_series.C r` and similarly for `X` to be true for any `[ordered semiring Γ]`, not just `ℤ`.

### [2022-01-08 16:29:04](https://github.com/leanprover-community/mathlib/commit/1162509)
chore(data/fin/vec_notation): generalize smul_cons ([#11285](https://github.com/leanprover-community/mathlib/pull/11285))

### [2022-01-08 16:29:01](https://github.com/leanprover-community/mathlib/commit/56f021a)
feat(data/polynomial/{erase_lead + denoms_clearable}): strengthen a lemma ([#11257](https://github.com/leanprover-community/mathlib/pull/11257))
This PR is a step in the direction of simplifying [#11139](https://github.com/leanprover-community/mathlib/pull/11139) .
It strengthens lemma `induction_with_nat_degree_le` by showing that restriction can be strengthened on one of the assumptions.
~~It proves a lemma computing the `nat_degree` under functions on polynomials that include the shift of a variable.~~
EDIT: the lemma was moved to the later PR [#11265](https://github.com/leanprover-community/mathlib/pull/11265).
It fixes the unique use of lemma `induction_with_nat_degree_le`.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2311139.20taylor.20sum.20and.20nat_degree_taylor)

### [2022-01-08 16:28:59](https://github.com/leanprover-community/mathlib/commit/b181a12)
refactor(combinatorics/quiver): split into several files ([#11006](https://github.com/leanprover-community/mathlib/pull/11006))
This PR splits `combinatorics/quiver.lean` into several files. The main reason for this is to ensure that the category theory library only imports the necessary definitions (and not for example the stuff on arborescences).
Also adds some more documentation, and fixes a bug in the definition of weakly connected components.

### [2022-01-08 16:28:58](https://github.com/leanprover-community/mathlib/commit/9b3fec5)
feat(algebraic_geometry): Gamma-Spec adjunction ([#9802](https://github.com/leanprover-community/mathlib/pull/9802))
Define the adjunction between the functors Gamma (global sections) and Spec (to LocallyRingedSpace).
I'm currently working on a more general version in http://arxiv.org/pdf/1103.2139.pdf (Theorem 2), which may require refactoring `structure_sheaf` and `Spec`.

### [2022-01-08 15:04:37](https://github.com/leanprover-community/mathlib/commit/b1955dc)
feat(data/matrix/basic): infix notation for matrix.dot_product in locale matrix ([#11289](https://github.com/leanprover-community/mathlib/pull/11289))
I created an infix notation for `matrix.dot_product` in locale `matrix`. The notation was consulted with @eric-wieser in [#11181](https://github.com/leanprover-community/mathlib/pull/11181).

### [2022-01-08 15:04:36](https://github.com/leanprover-community/mathlib/commit/4304127)
feat(ring_theory/power_series): teach simp to simplify more coercions of polynomials  to power series ([#11287](https://github.com/leanprover-community/mathlib/pull/11287))
So that simp can prove that the polynomial `5 * X^2 + X + 1` coerced to a power series is the same thing with the power series generator `X`. Likewise for `mv_power_series`.

### [2022-01-08 15:04:35](https://github.com/leanprover-community/mathlib/commit/e871386)
feat(number_theory/cyclotomic/basic): add lemmas ([#11264](https://github.com/leanprover-community/mathlib/pull/11264))
From flt-regular.

### [2022-01-08 15:04:33](https://github.com/leanprover-community/mathlib/commit/c7fa66e)
feat(data/nat/prime): power to factor count divides natural ([#11226](https://github.com/leanprover-community/mathlib/pull/11226))

### [2022-01-08 15:04:32](https://github.com/leanprover-community/mathlib/commit/4d79d5f)
chore(measure_theory/group/arithmetic): use implicit argument for measurable_space ([#11205](https://github.com/leanprover-community/mathlib/pull/11205))
The `measurable_space` argument is inferred from other arguments (like `measurable f` or a measure for example) instead of being a type class. This ensures that the lemmas are usable without `@` when several measurable space structures are used for the same type.
Also use more `variables`.

### [2022-01-08 14:24:00](https://github.com/leanprover-community/mathlib/commit/2231173)
feat(group_theory/commuting_probability): New file ([#11243](https://github.com/leanprover-community/mathlib/pull/11243))
This PR introduces commuting probabilities of finite groups.

### [2022-01-08 07:22:54](https://github.com/leanprover-community/mathlib/commit/07f9b8e)
feat(data/sum/order): Linear and disjoint sums of orders ([#11157](https://github.com/leanprover-community/mathlib/pull/11157))
This defines the disjoint sum of two orders on `α ⊕ β` and the linear (aka lexicographic) sum of two orders on `α ⊕ₗ β` (a type synonym of `α ⊕ β`) in a new file `data.sum.order`.

### [2022-01-08 00:14:42](https://github.com/leanprover-community/mathlib/commit/303e77c)
feat(topology/metric_space/hausdorff_distance): make iffs ([#11288](https://github.com/leanprover-community/mathlib/pull/11288))
* Make `exists_edist_lt_of_inf_edist_lt` and `exists_dist_lt_of_inf_edist_lt` iffs. Rename to `inf_[e]dist_lt_iff`.
* Simplify some proofs

### [2022-01-07 18:21:53](https://github.com/leanprover-community/mathlib/commit/5cbfddd)
feat(data/finset/sym): Symmetric powers of a finset ([#11142](https://github.com/leanprover-community/mathlib/pull/11142))
This defines `finset.sym` and `finset.sym2`, which are the `finset` analogs of `sym` and `sym2`, in a new file `data.finset.sym`.

### [2022-01-07 18:21:52](https://github.com/leanprover-community/mathlib/commit/a8d37c1)
feat(data/nat/factorization): Defining `factorization` ([#10540](https://github.com/leanprover-community/mathlib/pull/10540))
Defining `factorization` as a `finsupp`, as discussed in
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Prime.20factorizations
and 
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Proof.20of.20Euler's.20product.20formula.20for.20totient
This is the first of a series of PRs to build up the infrastructure needed for the proof of Euler's product formula for the totient function.

### [2022-01-07 18:21:50](https://github.com/leanprover-community/mathlib/commit/3b02ad7)
feat(topology/homotopy/equiv): Add homotopy equivalences between topological spaces ([#10529](https://github.com/leanprover-community/mathlib/pull/10529))

### [2022-01-07 16:25:53](https://github.com/leanprover-community/mathlib/commit/13e99c7)
feat(algebra,linear_algebra,ring_theory): more is_central_scalar instances ([#11297](https://github.com/leanprover-community/mathlib/pull/11297))
This provides new transitive scalar actions:
* on `lie_submodule R L M` that match the actions on `submodule R M`
* on quotients by `lie_submodule R L M` that match the actions on quotients by `submodule R M`
The rest of the instances in this PR live in `Prop` so do not define any further actions.
This also fixes some overly verbose instance names.

### [2022-01-07 16:25:52](https://github.com/leanprover-community/mathlib/commit/b8f5d0a)
chore(category_theory/abelian/basic): abelian categories have finite limits and finite colimits. ([#11271](https://github.com/leanprover-community/mathlib/pull/11271))

### [2022-01-07 14:24:20](https://github.com/leanprover-community/mathlib/commit/b430316)
chore(topology/algebra/module/basic): add continuous_linear_map.is_central_scalar ([#11291](https://github.com/leanprover-community/mathlib/pull/11291))

### [2022-01-07 14:24:17](https://github.com/leanprover-community/mathlib/commit/3b7a783)
feat(topology/*): Gluing topological spaces ([#9864](https://github.com/leanprover-community/mathlib/pull/9864))

### [2022-01-07 12:43:41](https://github.com/leanprover-community/mathlib/commit/6fb638b)
feat(*): add lemmas, golf ([#11294](https://github.com/leanprover-community/mathlib/pull/11294))
### New lemmas
* `function.mul_support_nonempty_iff` and `function.support_nonempty_iff`;
* `set.infinite_union`;
* `nat.exists_subseq_of_forall_mem_union` (to be used in an upcoming mass golfing of `is_pwo`/`is_wf`);
* `hahn_series.coeff_inj`, `hahn_series.coeff_injective`, `hahn_series.coeff_fun_eq_zero_iff`, `hahn_series.support_eq_empty_iff`;
* `nat.coe_order_embedding_of_set` (`simp` + `rfl`);
* `nat.subtype.of_nat_range`, `nat.subtype.coe_comp_of_nat_range`.
### Golfed proofs
* `set.countable.prod`;
*  `nat.order_embedding_of_set_range`;
*  `hahn-series.support_nonempty_iff`;
### Renamed
* `set.finite.union_iff` → `set.finite_union`, add `@[simp]` attr;
* `set.finite.diff` → `set.finite.of_diff`, drop 1 arg;

### [2022-01-06 19:34:08](https://github.com/leanprover-community/mathlib/commit/0b96630)
feat(algebra/{monoid_algebra/basic,free_non_unital_non_assoc_algebra,lie/free}): generalize typeclasses ([#11283](https://github.com/leanprover-community/mathlib/pull/11283))
This fixes a number of missing or problematic typeclasses:
* The smul typeclasses on `monoid_algebra` had overly strong assumptions
* `add_comm_group (monoid_algebra k G)` was missing.
* `monoid_algebra` had diamonds in its int-module structures, which were different between the one inferred from `ring` and `add_group`.
* `monoid_algebra` was missing an instance of the new `non_unital_non_assoc_ring`.
* `free_non_unital_non_assoc_algebra` was missing a lot of smul typeclasses and transitive module structures that it should inherit from `monoid_algebra`. Since every instance should just be inherited, we change `free_non_unital_non_assoc_algebra` to an abbreviation.
* `free_lie_algebra` had diamonds in its int-module and nat-module structures.
* `free_lie_algebra` was missing transitive module structures.
This also golfs some proofs about `free_non_unital_non_assoc_algebra`, and removes the `irreducible` attributes since these just make some obvious proofs more awkward.

### [2022-01-06 17:51:55](https://github.com/leanprover-community/mathlib/commit/d0bf8bd)
feat(set_theory/ordinal): `ordinal` is a successor order ([#11284](https://github.com/leanprover-community/mathlib/pull/11284))
This provides the `succ_order` instance for `ordinal`.

### [2022-01-06 17:51:52](https://github.com/leanprover-community/mathlib/commit/5893fbf)
feat(data/polynomial/monic): add two lemmas on degrees of monic polynomials ([#11259](https://github.com/leanprover-community/mathlib/pull/11259))
This PR is a step in the direction of simplifying [#11139](https://github.com/leanprover-community/mathlib/pull/11139).
The two lemmas involve computing the degree of a power of monic polynomials.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2311139.20taylor.20sum.20and.20nat_degree_taylor)

### [2022-01-06 14:41:11](https://github.com/leanprover-community/mathlib/commit/9b39ab2)
feat(algebra/group/freiman): Freiman homomorphisms ([#10497](https://github.com/leanprover-community/mathlib/pull/10497))
This defines Freiman homomorphisms, which are maps preserving products of `n` elements (but only in the codomain. One can never get back to the domain).
This is useful in additive combinatorics.

### [2022-01-06 12:39:56](https://github.com/leanprover-community/mathlib/commit/d2428fa)
feat(ring_theory/localization): Localization is the localization of localization. ([#11145](https://github.com/leanprover-community/mathlib/pull/11145))

### [2022-01-06 10:39:24](https://github.com/leanprover-community/mathlib/commit/54c2567)
feat(category_theory/sites): The pushforward pullback adjunction ([#11273](https://github.com/leanprover-community/mathlib/pull/11273))

### [2022-01-06 10:39:23](https://github.com/leanprover-community/mathlib/commit/7af5e86)
feat(algebra/big_operators/multiset): Multiset product under some usual maps ([#10907](https://github.com/leanprover-community/mathlib/pull/10907))
Product of the image of a multiset under `λ a, (f a)⁻¹`, `λ a, f a / g a`, `λ a, f a ^ n` (for `n` in `ℕ` and `ℤ`).

### [2022-01-06 09:57:30](https://github.com/leanprover-community/mathlib/commit/c391512)
feat(topology/metric_space/kuratowski): make the Kuratowski embedding have codomain the "true" ℓ^∞(ℕ) ([#11280](https://github.com/leanprover-community/mathlib/pull/11280))
(Previously, we didn't have the "true" ℓ^∞(ℕ), so we used the space of bounded continuous functions on `ℕ` equipped with the discrete topology.)

### [2022-01-06 07:55:41](https://github.com/leanprover-community/mathlib/commit/f07f87e)
feat(ring_theory/power_series/basic): algebra, solving TODOs ([#11267](https://github.com/leanprover-community/mathlib/pull/11267))
`algebra (mv_polynomial σ R) (mv_power_series σ A)`
`algebra (mv_power_series σ R) (mv_power_series σ A)`
`algebra (polynomial R) (power_series A)`
`algebra (power_series R) (power_series A)`
`coe_to_mv_power_series.alg_hom`
`coe_to_power_series.alg_hom`
And API about the injectivity of coercions

### [2022-01-06 07:55:40](https://github.com/leanprover-community/mathlib/commit/6952172)
feat(data/nat/digits): digits_len ([#11187](https://github.com/leanprover-community/mathlib/pull/11187))
Via a new `data.nat.log` import.
Also unprivate `digits_eq_cons_digits_div`.
The file needs a refactor to make the names more mathlib-like,
otherwise I would have named it `length_digits`.

### [2022-01-06 07:05:28](https://github.com/leanprover-community/mathlib/commit/b3260f3)
feat(measure_theory/constructions/borel_space): new lemma tendsto_measure_cthickening ([#11009](https://github.com/leanprover-community/mathlib/pull/11009))
Prove that, when `r` tends to `0`, the measure of the `r`-thickening of a set `s` tends to the measure of `s`.

### [2022-01-05 23:45:35](https://github.com/leanprover-community/mathlib/commit/9f28b5d)
chore(ci): update some workflows to use custom bot token ([#11274](https://github.com/leanprover-community/mathlib/pull/11274))

### [2022-01-05 23:45:33](https://github.com/leanprover-community/mathlib/commit/e718965)
feat(topology/uniform_space/compact_convergence): when the domain is compact, compact convergence is just uniform convergence ([#11262](https://github.com/leanprover-community/mathlib/pull/11262))

### [2022-01-05 23:45:32](https://github.com/leanprover-community/mathlib/commit/a7611b2)
chore(*): notation for `units` ([#11236](https://github.com/leanprover-community/mathlib/pull/11236))

### [2022-01-05 23:45:31](https://github.com/leanprover-community/mathlib/commit/cac4e19)
feat(set_theory/ordinal_arithmetic): Proved characterization of `log` ([#11192](https://github.com/leanprover-community/mathlib/pull/11192))
As well as a few simple missing lemmas.

### [2022-01-05 23:45:29](https://github.com/leanprover-community/mathlib/commit/b67857e)
refactor(set_theory/ordinal_arithmetic): Reworked `sup` and `bsup` API ([#11048](https://github.com/leanprover-community/mathlib/pull/11048))
This PR does two things:
- It reworks and matches, for the most part, the API for `ordinal.sup` and `ordinal.bsup`.
- It introduces `ordinal.lsub` and `ordinal.blsub` for (bounded) least strict upper bounds, and proves the expected results.

### [2022-01-05 22:31:56](https://github.com/leanprover-community/mathlib/commit/771d144)
feat(analysis/normed_space/lp_space): completeness of the lp space on `Π i, E i` ([#11094](https://github.com/leanprover-community/mathlib/pull/11094))

### [2022-01-05 19:08:16](https://github.com/leanprover-community/mathlib/commit/8b2d181)
feat(ring_theory/laurent_series): laurent_series is_fraction_ring over power_series ([#11220](https://github.com/leanprover-community/mathlib/pull/11220))

### [2022-01-05 17:28:18](https://github.com/leanprover-community/mathlib/commit/f6dfea6)
feat(measure_theory/integral): Cauchy integral formula for a circle ([#10000](https://github.com/leanprover-community/mathlib/pull/10000))

### [2022-01-05 16:16:53](https://github.com/leanprover-community/mathlib/commit/6bf9041)
doc(analysis/normed/group/basic): show notation in the typeclass docstring ([#11260](https://github.com/leanprover-community/mathlib/pull/11260))

### [2022-01-05 16:16:51](https://github.com/leanprover-community/mathlib/commit/3ab1c1c)
feat(algebra/polynomial/big_operators): lemmas about polynomial degree of products ([#11258](https://github.com/leanprover-community/mathlib/pull/11258))
These already existed for `nat_degree` but `degree` versions seemed missing.
from flt-regular

### [2022-01-05 16:16:50](https://github.com/leanprover-community/mathlib/commit/a1f4ac3)
chore(topology): move 3 files to `topology/algebra/module/` ([#11242](https://github.com/leanprover-community/mathlib/pull/11242))

### [2022-01-05 14:15:46](https://github.com/leanprover-community/mathlib/commit/9fd7a02)
feat(category_theory/sites/left_exact): Sheafification is left exact. ([#11252](https://github.com/leanprover-community/mathlib/pull/11252))

### [2022-01-05 14:15:44](https://github.com/leanprover-community/mathlib/commit/a580727)
chore(topology/omega_complete_partial_order): golf ([#11250](https://github.com/leanprover-community/mathlib/pull/11250))

### [2022-01-05 14:15:40](https://github.com/leanprover-community/mathlib/commit/802f23c)
feat(data/fintype/basic): `set_fintype_card_eq_univ_iff` ([#11244](https://github.com/leanprover-community/mathlib/pull/11244))
Adds companion lemma to `set_fintype_card_le_univ`. This PR also moves several `set.to_finset` lemmas earlier in the file.

### [2022-01-05 14:15:39](https://github.com/leanprover-community/mathlib/commit/b27e33a)
feat(data/{fin/vec_notation, matrix/notation}): `cons_{add,sub,dot_product}_cons` ([#11241](https://github.com/leanprover-community/mathlib/pull/11241))
While these can be proved by `simp`, they are not rejected by the simp linter.

### [2022-01-05 14:15:38](https://github.com/leanprover-community/mathlib/commit/98b64f4)
feat(linear_algebra/orientation): bases from orientations ([#11234](https://github.com/leanprover-community/mathlib/pull/11234))
Add a lemma giving the orientation of a basis constructed with
`units_smul`, and thus definitions and lemmas to construct a basis
from an orientation.

### [2022-01-05 14:15:37](https://github.com/leanprover-community/mathlib/commit/33b5d26)
feat(analysis/complex): `re`, `im`, and `closure`/`interior`/`frontier` ([#11215](https://github.com/leanprover-community/mathlib/pull/11215))

### [2022-01-05 14:15:35](https://github.com/leanprover-community/mathlib/commit/3115ced)
feat(ring_theory/non_zero_divisors): mul_{left,right}_cancel API ([#11211](https://github.com/leanprover-community/mathlib/pull/11211))
Not all `monoid_with_zero` are `cancel_monoid_with_zero`,
so we can't use `mul_right_cancel₀` everywhere. However, by definition,
multiplication by non-zero-divisors is 0 iff the multiplicand is 0.
In the context of a ring, that allows us to `mul_cancel_right`

### [2022-01-05 14:15:34](https://github.com/leanprover-community/mathlib/commit/3bd2044)
chore(data/nat/prime): reuse a result from algebra.big_operators.associated ([#11143](https://github.com/leanprover-community/mathlib/pull/11143))

### [2022-01-05 14:15:33](https://github.com/leanprover-community/mathlib/commit/57a9f8b)
chore(group_theory/sub{monoid,group}, linear_algebra/basic): rename equivalences to mapped subobjects ([#11075](https://github.com/leanprover-community/mathlib/pull/11075))
This makes the names shorter and more uniform:
* `add_equiv.map_add_submonoid`
* `add_equiv.map_add_subgroup`
* `linear_equiv.map_submodule`

### [2022-01-05 14:15:32](https://github.com/leanprover-community/mathlib/commit/7e5eebd)
feat(linear_algebra/clifford_algebra/equivs): There is a clifford algebra isomorphic to the dual numbers ([#10730](https://github.com/leanprover-community/mathlib/pull/10730))
This adds a brief file on the dual numbers, and then shows that they are equivalent to the clifford algebra with `Q = (0 : quadratic_form R R)`.

### [2022-01-05 12:21:49](https://github.com/leanprover-community/mathlib/commit/cef3258)
chore(group_theory/group_action/defs): add instances to copy statements about left actions to right actions when the two are equal ([#10949](https://github.com/leanprover-community/mathlib/pull/10949))
While these instances are usually available elsewhere, these shortcuts can reduce the number of typeclass assumptions other lemmas needs.
Since the instances carry no data, the only harm they can cause is performance.
There were some typeclass loops brought on by some bad instance unification, similar to the ones removed by @Vierkantor in 9ee2a50aa439d092c8dea16c1f82f7f8e1f1ea2c. We turn these into `lemma`s and  duplicate the docstring explaining the problem. That commit has a much longer explanation of the problem.

### [2022-01-05 11:32:02](https://github.com/leanprover-community/mathlib/commit/8d5830e)
chore(measure_theory/measurable_space): use implicit measurable_space argument ([#11230](https://github.com/leanprover-community/mathlib/pull/11230))
The `measurable_space` argument is inferred from other arguments (like `measurable f` or a measure for example) instead of being a type class. This ensures that the lemmas are usable without `@` when several measurable space structures are used for the same type.

### [2022-01-05 08:10:47](https://github.com/leanprover-community/mathlib/commit/4912740)
chore(analysis/inner_product_space/basic): extract common `variables` ([#11214](https://github.com/leanprover-community/mathlib/pull/11214))

### [2022-01-05 08:10:46](https://github.com/leanprover-community/mathlib/commit/b72d2ab)
feat(algebra/ring/basic): Introduce non-unital, non-associative rings ([#11124](https://github.com/leanprover-community/mathlib/pull/11124))
Adds the class `non_unital_non_assoc_ring` to `algebra.ring.basic` to represent rings which are not assumed to be unital or associative and shows that (unital, associative) rings are instances of `non_unital_non_assoc_ring`.
Needed by [#11073](https://github.com/leanprover-community/mathlib/pull/11073).

### [2022-01-05 06:18:07](https://github.com/leanprover-community/mathlib/commit/58b1429)
chore(algebra/group/pi): `pow_apply` can be `rfl` ([#11249](https://github.com/leanprover-community/mathlib/pull/11249))

### [2022-01-05 01:44:24](https://github.com/leanprover-community/mathlib/commit/4093834)
feat(measure_theory/measure/finite_measure_weak_convergence): add definition and lemmas of pairing measures with nonnegative continuous test functions. ([#9430](https://github.com/leanprover-community/mathlib/pull/9430))
Add definition and lemmas about pairing of `finite_measure`s and `probability_measure`s with nonnegative continuous test functions. These pairings will be used in the definition of the topology of weak convergence (convergence in distribution): the topology will be defined as an induced topology based on them.

### [2022-01-04 23:41:45](https://github.com/leanprover-community/mathlib/commit/5c8243f)
fix(algebra/group/type_tags): resolve an instance diamond caused by over-eager unfolding ([#11240](https://github.com/leanprover-community/mathlib/pull/11240))
By setting the `one` and `zero` fields manually, we ensure that they are syntactically equal to the ones found via `has_one` and `has_zero`, rather than potentially having typeclass arguments resolved in a different way.
This seems to fix the failing test.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Diamond.20in.20multiplicative.20nat/near/266824443)

### [2022-01-04 22:10:13](https://github.com/leanprover-community/mathlib/commit/862854e)
chore(ring_theory/localization): fix typo in module docstring ([#11245](https://github.com/leanprover-community/mathlib/pull/11245))
There was a mismatch in the module docstring to the decl name later.

### [2022-01-04 18:47:59](https://github.com/leanprover-community/mathlib/commit/dc352a6)
chore(.github): include co-author attributions in PR template ([#11239](https://github.com/leanprover-community/mathlib/pull/11239))

### [2022-01-04 18:47:58](https://github.com/leanprover-community/mathlib/commit/692b6b7)
chore(analysis/inner_product_space/basic): adjust decidability assumptions ([#11212](https://github.com/leanprover-community/mathlib/pull/11212))
Eliminate the `open_locale classical` in `inner_product_space.basic` and replace by specific decidability assumptions.

### [2022-01-04 18:47:57](https://github.com/leanprover-community/mathlib/commit/49cbce2)
chore(data/fintype/basic): set.to_finset_univ generalization ([#11174](https://github.com/leanprover-community/mathlib/pull/11174))

### [2022-01-04 18:47:56](https://github.com/leanprover-community/mathlib/commit/037147e)
feat(probability_theory/stopping): define stopped process ([#10851](https://github.com/leanprover-community/mathlib/pull/10851))

### [2022-01-04 16:45:27](https://github.com/leanprover-community/mathlib/commit/5df2e7b)
chore(data/polynomial, data/finset/lattice): basic lemmas ([#11237](https://github.com/leanprover-community/mathlib/pull/11237))

### [2022-01-04 16:45:25](https://github.com/leanprover-community/mathlib/commit/5f3f01f)
feat(set_theory/ordinal_arithmetic): Proved `add_log_le_log_mul` ([#11228](https://github.com/leanprover-community/mathlib/pull/11228))
That is, `log b u + log b v ≤ log b (u * v)`. The other direction holds only when `b ≠ 2` and `b` is principal multiplicative, and will be added at a much later PR.

### [2022-01-04 16:45:24](https://github.com/leanprover-community/mathlib/commit/18330f6)
feat(tactic/abel): support 0 in group expressions ([#11201](https://github.com/leanprover-community/mathlib/pull/11201))
[As reported on Zulip.](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60abel.60.20not.20rewriting.20with.20.60sub_zero.60/near/266645648)
fixes [#11200](https://github.com/leanprover-community/mathlib/pull/11200)

### [2022-01-04 16:45:23](https://github.com/leanprover-community/mathlib/commit/b0f2f55)
feat(set_theory/ordinal_arithmetic): Proved `dvd_iff_mod_eq_zero` ([#11195](https://github.com/leanprover-community/mathlib/pull/11195))

### [2022-01-04 16:45:22](https://github.com/leanprover-community/mathlib/commit/7f244cf)
feat(category_theory/limits/filtered_colimits_commute_with_finite_limits): A curried variant of the fact that filtered colimits commute with finite limits. ([#11154](https://github.com/leanprover-community/mathlib/pull/11154))

### [2022-01-04 16:45:20](https://github.com/leanprover-community/mathlib/commit/06c3ab2)
feat(ring_theory/discriminant): add of_power_basis_eq_norm ([#11149](https://github.com/leanprover-community/mathlib/pull/11149))
From flt-regular.

### [2022-01-04 16:45:19](https://github.com/leanprover-community/mathlib/commit/4a0e844)
feat(data/finset): to_finset empty iff ([#11088](https://github.com/leanprover-community/mathlib/pull/11088))

### [2022-01-04 16:45:18](https://github.com/leanprover-community/mathlib/commit/68d2d21)
feat(testing/slim_check): teach slim_check about `finsupp`s ([#10916](https://github.com/leanprover-community/mathlib/pull/10916))
We add some instances so that `slim_check` can generate `finsupp`s and hence try to provide counterexamples for them.
As the way the original slim_check for functions works is to generate a finite list of random values and pick a default for the rest of the values these `total_functions` are quite close to finsupps already, we just have to map the default value to zero, and prove various things about the support.
There might be conceptually nicer ways of building this instance but this seems functional enough.
Seeing as many finsupp defs are classical (and noncomputable) this isn't quite as useful for generating counterexamples as I originally hoped.
See the test at `test/slim_check.lean` for a basic example of usage
I wrote this while working on flt-regular but it is hopefully useful outside of that

### [2022-01-04 16:45:16](https://github.com/leanprover-community/mathlib/commit/7d42ded)
chore(*): Rename instances ([#9200](https://github.com/leanprover-community/mathlib/pull/9200))
Rename
* `lattice_of_linear_order` -> `linear_order.to_lattice`
* `distrib_lattice_of_linear_order` -> `linear_order.to_distrib_lattice`
to follow the naming convention (well, it's currently not explicitly written there, but autogenerated names follow that).

### [2022-01-04 15:37:18](https://github.com/leanprover-community/mathlib/commit/b99a98e)
doc(category_theory/limits/shapes/pullbacks): fix doc ([#11225](https://github.com/leanprover-community/mathlib/pull/11225))
the link doesn't work with the full stop

### [2022-01-04 13:36:42](https://github.com/leanprover-community/mathlib/commit/a30375e)
feat(topology/fiber_bundle): a topological fiber bundle is a quotient map ([#11194](https://github.com/leanprover-community/mathlib/pull/11194))
* The projection map of a topological fiber bundle (pre)trivialization
  is surjective onto its base set.
* The projection map of a topological fiber bundle with a nonempty
  fiber is surjective. Since it is also a continuous open map, it is a
  quotient map.
* Golf a few proofs.

### [2022-01-04 13:36:33](https://github.com/leanprover-community/mathlib/commit/aa82ba0)
feat(algebra/opposites): add `add_opposite` ([#11080](https://github.com/leanprover-community/mathlib/pull/11080))
Add `add_opposite`, add `to_additive` here and there. More `to_additive` can be added as needed later.

### [2022-01-04 13:36:24](https://github.com/leanprover-community/mathlib/commit/a7aa2c8)
feat(data/finset/sigma): A way to lift `finset`-valued functions to a sigma type ([#10958](https://github.com/leanprover-community/mathlib/pull/10958))
This defines `finset.sigma_lift : (Π i, α i → β i → finset (γ i)) → Σ i, α i → Σ i, β i → finset (Σ i, γ i)` as the function which returns the finset corresponding to the first coordinate of `a b : Σ i, α i` if they have the same, or the empty set else.

### [2022-01-04 13:36:16](https://github.com/leanprover-community/mathlib/commit/8bd2059)
feat(data/finset/slice): `r`-sets and slice ([#10685](https://github.com/leanprover-community/mathlib/pull/10685))
Two simple nonetheless useful definitions about set families. A family of `r`-sets is a set of finsets of cardinality `r`. The slice of a set family is its subset of `r`-sets.

### [2022-01-04 12:08:44](https://github.com/leanprover-community/mathlib/commit/1aec9a1)
feat(analysis/inner_product_space/dual,adjoint): add some lemmas about extensionality with respect to a basis ([#11176](https://github.com/leanprover-community/mathlib/pull/11176))
This PR adds some lemmas about extensionality in inner product spaces with respect to a basis.

### [2022-01-04 09:44:51](https://github.com/leanprover-community/mathlib/commit/03872fd)
feat(*): Prerequisites for the Spec gamma adjunction ([#11209](https://github.com/leanprover-community/mathlib/pull/11209))

### [2022-01-04 09:44:50](https://github.com/leanprover-community/mathlib/commit/9a8e9fa)
chore(category_theory/limits): Generalize universes for `preserves/shapes/pullback.lean` ([#10780](https://github.com/leanprover-community/mathlib/pull/10780))

### [2022-01-04 07:46:59](https://github.com/leanprover-community/mathlib/commit/044c1de)
feat(analysis/special_functions/trigonometric): a few lemmas ([#11217](https://github.com/leanprover-community/mathlib/pull/11217))
Add a few trivial lemmas about `arcsin`/`arccos`.

### [2022-01-04 07:46:58](https://github.com/leanprover-community/mathlib/commit/3045014)
feat(algebra/order/ring): turn `mul_self_pos` into an `iff` ([#11216](https://github.com/leanprover-community/mathlib/pull/11216))

### [2022-01-04 07:46:57](https://github.com/leanprover-community/mathlib/commit/85784b0)
feat(linear_algebra/determinant): `det_units_smul` and `det_is_unit_smul` ([#11206](https://github.com/leanprover-community/mathlib/pull/11206))
Add lemmas giving the determinant of a basis constructed with
`units_smul` or `is_unit_smul` with respect to the original basis.

### [2022-01-04 07:46:56](https://github.com/leanprover-community/mathlib/commit/1fc7a93)
chore(topology/metric_space/hausdorff_distance): slightly tidy some proofs ([#11203](https://github.com/leanprover-community/mathlib/pull/11203))

### [2022-01-04 07:46:55](https://github.com/leanprover-community/mathlib/commit/9d1503a)
feat(field_theory.intermediate_field): add intermediate_field.map_map ([#11020](https://github.com/leanprover-community/mathlib/pull/11020))

### [2022-01-04 06:31:42](https://github.com/leanprover-community/mathlib/commit/71dc1ea)
feat(topology/maps): preimage of closure/frontier under an open map ([#11189](https://github.com/leanprover-community/mathlib/pull/11189))
We had lemmas about `interior`. Add versions about `frontier` and `closure`.

### [2022-01-04 03:53:12](https://github.com/leanprover-community/mathlib/commit/8f391aa)
chore(algebra/module/submodule): switch `subtype_eq_val` to `coe_subtype` ([#11210](https://github.com/leanprover-community/mathlib/pull/11210))
Change the name and form of a lemma, from
```lean
lemma subtype_eq_val : ((submodule.subtype p) : p → M) = subtype.val := rfl
```
to
```lean
lemma coe_subtype : ((submodule.subtype p) : p → M) = coe := rfl
```
The latter is the simp-normal form so I claim it should be preferred.

### [2022-01-04 01:48:54](https://github.com/leanprover-community/mathlib/commit/4daaff0)
feat(data/nat/prime): factors sublist of product ([#11104](https://github.com/leanprover-community/mathlib/pull/11104))
This PR changes the existing `factors_subset_right` to give a stronger sublist conclusion (which trivially can be used to reproduce the subst version).

### [2022-01-03 20:30:05](https://github.com/leanprover-community/mathlib/commit/62d814a)
refactor(order/lexicographic): Change the `lex` synonym ([#10926](https://github.com/leanprover-community/mathlib/pull/10926))
At least five types have a natural lexicographic order, namely:
* `α ⊕ β` where everything on the left is smaller than everything on the right
* `Σ i, α i` where things are first ordered following `ι`, then following `α i`
* `Σ' i, α i` where things are first ordered following `ι`, then following `α i`
* `α × β` where things are first ordered following `α`, then following `β`
* `finset α`, which is in a specific sene the dual of `finset.colex`.
And we could even add `Π i, α i`, `ι →₀ α`, `Π₀ i, α i`, etc... although those haven't come up yet in practice.
Hence, we generalize the `lex` synonym away from `prod` to make it a general purpose synonym to equip a type with its lexicographical order. What was `lex α β` now is `α ×ₗ β`.
Note that this PR doesn't add any of the aforementioned instances.

### [2022-01-03 18:55:41](https://github.com/leanprover-community/mathlib/commit/9d0fd52)
feat(measure_theory/function/lp_space): use has_measurable_add2 instead of second_countable_topology ([#11202](https://github.com/leanprover-community/mathlib/pull/11202))
Use the weaker assumption `[has_measurable_add₂ E]` instead of `[second_countable_topology E]` in 4 lemmas.

### [2022-01-03 16:25:35](https://github.com/leanprover-community/mathlib/commit/7249895)
feat(analysis/inner_product_space/basic): negating orthonormal vectors ([#11208](https://github.com/leanprover-community/mathlib/pull/11208))
Add a lemma that, given an orthonormal family, negating some of the
vectors in it produces another orthonormal family.

### [2022-01-03 15:26:28](https://github.com/leanprover-community/mathlib/commit/83f4036)
feat(*/cyclotomic): update is_root_cyclotomic_iff to use ne_zero ([#11071](https://github.com/leanprover-community/mathlib/pull/11071))

### [2022-01-03 14:30:17](https://github.com/leanprover-community/mathlib/commit/236d978)
feat(linear_algebra/matrix/basis): `to_matrix_units_smul` and `to_matrix_is_unit_smul` ([#11191](https://github.com/leanprover-community/mathlib/pull/11191))
Add lemmas that applying `to_matrix` to a basis constructed with
`units_smul` or `is_unit_smul` produces the corresponding diagonal
matrix.

### [2022-01-03 12:49:02](https://github.com/leanprover-community/mathlib/commit/4b3198b)
feat(combinatorics/configuration): `has_lines` implies `has_points`, and vice versa ([#11170](https://github.com/leanprover-community/mathlib/pull/11170))
If `|P| = |L|`, then `has_lines` and `has_points` are equivalent!

### [2022-01-03 11:27:40](https://github.com/leanprover-community/mathlib/commit/a10cb2f)
feat(algebra/big_operators/associated): `dvd_prod_iff` for `finset` and `finsupp` ([#10675](https://github.com/leanprover-community/mathlib/pull/10675))
Adding the counterparts of `dvd_prod_iff` (in [#10624](https://github.com/leanprover-community/mathlib/pull/10624)) for `finset` and `finsupp`.

### [2022-01-03 10:32:11](https://github.com/leanprover-community/mathlib/commit/a813cf5)
chore(algebra/algebra/spectrum): move `exists_spectrum_of_is_alg_closed_of_finite_dimensional` ([#10919](https://github.com/leanprover-community/mathlib/pull/10919))
Move a lemma from `field_theory/is_alg_closed/basic` into `algebra/algebra/spectrum` which belongs in this relatively new file. Also, rename (now in `spectrum` namespace) and refactor it slightly; and update the two references to it accordingly.
- [x] depends on: [#10783](https://github.com/leanprover-community/mathlib/pull/10783)

### [2022-01-03 07:35:22](https://github.com/leanprover-community/mathlib/commit/49bf3d3)
feat(data/polynomial/taylor): taylor_mul ([#11193](https://github.com/leanprover-community/mathlib/pull/11193))

### [2022-01-03 07:35:21](https://github.com/leanprover-community/mathlib/commit/a49ee49)
feat(data/finset/functor): Functor structures for `finset` ([#10980](https://github.com/leanprover-community/mathlib/pull/10980))
This defines the monad, the commutative applicative and the (almost) traversable functor structures on `finset`.
It all goes in a new file `data.finset.functor` and picks up the `functor` instance that was stranded in `data.finset.basic` by Scott in [#2997](https://github.com/leanprover-community/mathlib/pull/2997).

### [2022-01-03 06:54:39](https://github.com/leanprover-community/mathlib/commit/138c61f)
chore(field_theory/ratfunc): comm_ring (ratfunc K) ([#11188](https://github.com/leanprover-community/mathlib/pull/11188))
Previously, the file only gave a `field (ratfunc K)` instance,
requiring `comm_ring K` and `is_domain K`.
In fact, `ratfunc K` is a `comm_ring` regardless of the `is_domain`.
The upstream instance is proven first, with a generalized tactic.

### [2022-01-02 23:55:46](https://github.com/leanprover-community/mathlib/commit/03a5482)
chore(topology/continuous_on): fix a typo ([#11190](https://github.com/leanprover-community/mathlib/pull/11190))
`eventually_nhds_with_of_forall` → `eventually_nhds_within_of_forall`

### [2022-01-02 17:21:44](https://github.com/leanprover-community/mathlib/commit/3f77761)
feat(ring_theory/algebraic): algebraic functions ([#11156](https://github.com/leanprover-community/mathlib/pull/11156))
Accessible via a new `algebra (polynomial R) (R → R)`
and a generalization that gives `algebra (polynomial R) (S → S)` when `[algebra R S]`.

### [2022-01-01 20:23:07](https://github.com/leanprover-community/mathlib/commit/ebdbe6b)
feat(topology/algebra/ordered): new lemmas, update ([#11184](https://github.com/leanprover-community/mathlib/pull/11184))
* In `exists_seq_strict_mono_tendsto'` and `exists_seq_strict_anti_tendsto'`, prove that `u n` belongs to the corresponding open interval.
* Add `exists_seq_strict_anti_strict_mono_tendsto`.
* Rename `is_lub_of_tendsto` to `is_lub_of_tendsto_at_top`, rename `is_glb_of_tendsto` to `is_glb_of_tendsto_at_bot`.
* Add `is_lub_of_tendsto_at_bot`, `is_glb_of_tendsto_at_top`.

### [2022-01-01 19:07:15](https://github.com/leanprover-community/mathlib/commit/02d02df)
chore(measure_theory): fix TC assumptions in 2 lemmas ([#11185](https://github.com/leanprover-community/mathlib/pull/11185))
With new assumptions, these lemmas work, e.g., for `β = ι → ℝ`.

### [2022-01-01 19:07:13](https://github.com/leanprover-community/mathlib/commit/c1b1041)
feat(topology/metric_space/basic): add `fin.dist_insert_nth_insert_nth` ([#11183](https://github.com/leanprover-community/mathlib/pull/11183))

### [2022-01-01 17:09:52](https://github.com/leanprover-community/mathlib/commit/6486e9b)
chore(order/rel_classes): Removed unnecessary `classical` ([#11180](https://github.com/leanprover-community/mathlib/pull/11180))
Not sure what that was doing here.

### [2022-01-01 15:44:59](https://github.com/leanprover-community/mathlib/commit/93cf56c)
feat(algebraic_geometry/*): The map `F.stalk y ⟶ F.stalk x` for `x ⤳ y` ([#11144](https://github.com/leanprover-community/mathlib/pull/11144))

### [2022-01-01 14:44:14](https://github.com/leanprover-community/mathlib/commit/892d465)
feat(linear_algebra/multilinear/basic): the space of multilinear maps is finite-dimensional when the components are finite-dimensional ([#10504](https://github.com/leanprover-community/mathlib/pull/10504))
Formalized as part of the Sphere Eversion project.

### [2022-01-01 13:55:32](https://github.com/leanprover-community/mathlib/commit/5353369)
feat(combinatorics/configuration): Line count equals point count ([#11169](https://github.com/leanprover-community/mathlib/pull/11169))
In a configuration satisfying `has_lines` or `has_points`, if the number of points equals the number of lines, then the number of lines through a given point equals the number of points on a given line.

### [2022-01-01 13:55:31](https://github.com/leanprover-community/mathlib/commit/a6c82af)
feat(group_theory/specific_groups/*): computes the exponents of the dihedral and generalised quaternion groups ([#11166](https://github.com/leanprover-community/mathlib/pull/11166))
This PR shows that the exponent of the dihedral group of order `2n` is equal to `lcm n 2` and that the exponent of the generalised quaternion group of order `4n` is `2 * lcm n 2`

### [2022-01-01 13:55:30](https://github.com/leanprover-community/mathlib/commit/ad76a5e)
feat(data/nat/log): log_mul, log_div ([#11164](https://github.com/leanprover-community/mathlib/pull/11164))
Even with division over natural, the log "spec" holds.

### [2022-01-01 11:59:04](https://github.com/leanprover-community/mathlib/commit/23b01cc)
feat(algebraic_geometry): The function field of an integral scheme ([#11147](https://github.com/leanprover-community/mathlib/pull/11147))

### [2022-01-01 02:32:45](https://github.com/leanprover-community/mathlib/commit/1594b0c)
feat(normed_space/lp_space): Lp space for `Π i, E i` ([#11015](https://github.com/leanprover-community/mathlib/pull/11015))
For a family `Π i, E i` of normed spaces, define the subgroup with finite lp norm, and prove it is a `normed_group`.  Many parts adapted from the development of `measure_theory.Lp` by @RemyDegenne.
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Lp.20space

### [2022-01-01 00:20:37](https://github.com/leanprover-community/mathlib/commit/742ec88)
feat(data/set/*): lemmas about `monotone`/`antitone` and sets/intervals ([#11173](https://github.com/leanprover-community/mathlib/pull/11173))
* Rename `set.monotone_inter` and `set.monotone_union` to
  `monotone.inter` and `monotone.union`.
* Add `antitone` versions of some `monotone` lemmas.
* Specialize `Union_Inter_of_monotone` for `set.pi`.
* Add lemmas about `⋃ x, Ioi (f x)`, `⋃ x, Iio (f x)`, and `⋃ x, Ioo (f x) (g x)`.
* Add dot notation lemmas `monotone.Ixx` and `antitone.Ixx`.

### [2022-01-01 00:20:36](https://github.com/leanprover-community/mathlib/commit/979f2e7)
fix(order/filter/ultrafilter): dedup instance names ([#11171](https://github.com/leanprover-community/mathlib/pull/11171))

### [2022-01-01 00:20:35](https://github.com/leanprover-community/mathlib/commit/da54388)
feat(combinatorics/simple_graph/srg): is_SRG_with for complete graphs, edgeless graphs, and complements ([#5698](https://github.com/leanprover-community/mathlib/pull/5698))
We add the definition of a strongly regular graph and prove some useful lemmas about them.