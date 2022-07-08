### [2021-02-28 22:54:58](https://github.com/leanprover-community/mathlib/commit/13f30e5)
feat(geometry/manifold): `ext_chart_at` is smooth on its source ([#6473](https://github.com/leanprover-community/mathlib/pull/6473))

### [2021-02-28 22:54:57](https://github.com/leanprover-community/mathlib/commit/83bc663)
feat(category_theory/monoidal): skeleton of a monoidal category is a monoid ([#6444](https://github.com/leanprover-community/mathlib/pull/6444))

### [2021-02-28 22:54:56](https://github.com/leanprover-community/mathlib/commit/1e45472)
feat(analysis/calculus): Lagrange multipliers ([#6431](https://github.com/leanprover-community/mathlib/pull/6431))

### [2021-02-28 20:56:20](https://github.com/leanprover-community/mathlib/commit/18804b2)
chore(category/equivalence): remove functor.fun_inv_id ([#6450](https://github.com/leanprover-community/mathlib/pull/6450))
`F.fun_inv_id` was just a confusing alternative way to write `F.as_equivalence.unit_iso.symm`, and meant that many lemmas couldn't fire.
Deletes the definitions `functor.fun_inv_id` and `functor.inv_hom_id`, and the lemmas `is_equivalence.functor_unit_comp` and `is_equivalence.inv_fun_id_inv_comp`.

### [2021-02-28 20:56:19](https://github.com/leanprover-community/mathlib/commit/ac3c478)
feat(archive/100-theorems-list/9_area_of_a_circle): area of a disc ([#6374](https://github.com/leanprover-community/mathlib/pull/6374))
Freek № 9: The area of a disc with radius _r_ is _πr²_.
Also included are an `of_le` version of [FTC-2 for the open set](https://leanprover-community.github.io/mathlib_docs/find/interval_integral.integral_eq_sub_of_has_deriv_at') and the definition `nnreal.pi`.
Co-authored by @asouther4  and @jamesa9283.

### [2021-02-28 17:40:43](https://github.com/leanprover-community/mathlib/commit/b181866)
feat(data/set): more lemmas ([#6474](https://github.com/leanprover-community/mathlib/pull/6474))

### [2021-02-28 10:49:48](https://github.com/leanprover-community/mathlib/commit/ef5c1d5)
feat(analysis/special_functions/pow): smoothness of `complex.cpow` ([#6447](https://github.com/leanprover-community/mathlib/pull/6447))
* `x ^ y` is smooth in both variables at `(x, y)`, if `0 < re x` or
  `im x ≠ 0`;
* `x ^ y` is smooth in `y` if `x ≠ 0` or `y ≠ 0`.

### [2021-02-28 07:50:15](https://github.com/leanprover-community/mathlib/commit/abb3121)
chore(*): more line lengths ([#6472](https://github.com/leanprover-community/mathlib/pull/6472))

### [2021-02-28 04:58:12](https://github.com/leanprover-community/mathlib/commit/f153a85)
chore(category_theory/*): fix long lines ([#6471](https://github.com/leanprover-community/mathlib/pull/6471))

### [2021-02-28 04:58:11](https://github.com/leanprover-community/mathlib/commit/c7a2d67)
refactor(analysis/calculus/specific_functions): add params to `smooth_bump_function` ([#6467](https://github.com/leanprover-community/mathlib/pull/6467))
In the construction of a partition of unity we need a smooth bump
function that vanishes outside of `ball x R` and equals one on
`closed_ball x r` with arbitrary `0 < r < R`.

### [2021-02-28 04:58:10](https://github.com/leanprover-community/mathlib/commit/cc3e2c7)
feat(linear_algebra/basic): f x ∈ submodule.span R (f '' s) ([#6453](https://github.com/leanprover-community/mathlib/pull/6453))

### [2021-02-28 01:58:42](https://github.com/leanprover-community/mathlib/commit/ee1947d)
chore(scripts): update nolints.txt ([#6468](https://github.com/leanprover-community/mathlib/pull/6468))
I am happy to remove some nolints for you!

### [2021-02-28 01:58:42](https://github.com/leanprover-community/mathlib/commit/5b18369)
feat(ring_theory/power_series): coeff multiplication lemmas ([#6462](https://github.com/leanprover-community/mathlib/pull/6462))
Some lemmas used in combinatorics, from [#4259](https://github.com/leanprover-community/mathlib/pull/4259).

### [2021-02-28 01:58:41](https://github.com/leanprover-community/mathlib/commit/11f1801)
feat(linear_algebra/quadratic_form): add associated_eq_self_apply ([#6458](https://github.com/leanprover-community/mathlib/pull/6458))

### [2021-02-28 01:58:40](https://github.com/leanprover-community/mathlib/commit/9668bdd)
feat(algebra/category/Mon/adjunctions): adjoin_unit adjunction from Semigroup ([#6440](https://github.com/leanprover-community/mathlib/pull/6440))
This PR provides the adjoin_unit-forgetful adjunction between `Semigroup` and `Mon` and additionally the second to last module doc in algebra, namely `algebra.group.with_one`.

### [2021-02-27 23:21:06](https://github.com/leanprover-community/mathlib/commit/09d572d)
feat(algebra/big_operators): additive versions of multiset lemmas ([#6463](https://github.com/leanprover-community/mathlib/pull/6463))

### [2021-02-27 19:21:16](https://github.com/leanprover-community/mathlib/commit/aa0b274)
chore(*): split lines and move module doc `measure_theory/category/Meas` ([#6459](https://github.com/leanprover-community/mathlib/pull/6459))

### [2021-02-27 19:21:15](https://github.com/leanprover-community/mathlib/commit/d1b7a67)
feat(ring_theory/power_series/basic): coeff_zero_X_mul ([#6445](https://github.com/leanprover-community/mathlib/pull/6445))

### [2021-02-27 16:06:18](https://github.com/leanprover-community/mathlib/commit/a19af60)
feat(data/option): add `option.forall` and `option.exists` ([#6419](https://github.com/leanprover-community/mathlib/pull/6419))

### [2021-02-27 12:58:12](https://github.com/leanprover-community/mathlib/commit/4b02853)
feat(tactic/apply_fun): work on the goal as well ([#6439](https://github.com/leanprover-community/mathlib/pull/6439))
Extend the functionality of `apply_fun`, to "apply" functions to inequalities in the goal, as well.
```
Apply a function to an equality or inequality in either a local hypothesis or the goal.
* If we have `h : a = b`, then `apply_fun f at h` will replace this with `h : f a = f b`.
* If we have `h : a ≤ b`, then `apply_fun f at h` will replace this with `h : f a ≤ f b`,
  and create a subsidiary goal `monotone f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using `mono`,
  or an explicit solution can be provided with `apply_fun f at h using P`, where `P : monotone f`.
* If the goal is `a ≠ b`, `apply_fun f` will replace this with `f a ≠ f b`.
* If the goal is `a = b`, `apply_fun f` will replace this with `f a = f b`,
  and create a subsidiary goal `injective f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using local hypotheses,
  or if `f` is actually an `equiv`,
  or an explicit solution can be provided with `apply_fun f using P`, where `P : injective f`.
* If the goal is `a ≤ b` (or similarly for `a < b`), and `f` is actually an `order_iso`,
  `apply_fun f` will replace the goal with `f a ≤ f b`.
  If `f` is anything else (e.g. just a function, or an `equiv`), `apply_fun` will fail.
```

### [2021-02-27 09:13:13](https://github.com/leanprover-community/mathlib/commit/7256361)
chore(data/nat/choose): fix namespace of theorems ([#6451](https://github.com/leanprover-community/mathlib/pull/6451))

### [2021-02-27 09:13:12](https://github.com/leanprover-community/mathlib/commit/5f68d0e)
feat(ring_theory/power_series/basic): rescale_inj ([#6446](https://github.com/leanprover-community/mathlib/pull/6446))
Authored-by Ashvni Narayanan

### [2021-02-27 09:13:11](https://github.com/leanprover-community/mathlib/commit/f33418a)
feat(algebra/homology/chain_complex): pushforward of complex w.r.t. additive functor ([#6403](https://github.com/leanprover-community/mathlib/pull/6403))
This PR adds a definition for the pushforward of a homological complex with respect to an additive functor.

### [2021-02-27 06:20:12](https://github.com/leanprover-community/mathlib/commit/7ce01bb)
feat(category_theory/skeletal): skeleton of a general category ([#6443](https://github.com/leanprover-community/mathlib/pull/6443))
Construct the skeleton of a category using choice.

### [2021-02-27 01:15:38](https://github.com/leanprover-community/mathlib/commit/1af882b)
chore(scripts): update nolints.txt ([#6449](https://github.com/leanprover-community/mathlib/pull/6449))
I am happy to remove some nolints for you!

### [2021-02-26 23:38:23](https://github.com/leanprover-community/mathlib/commit/d38b5a5)
feat(category_theory/monoidal): construct the monoidal inverse to a functor ([#6442](https://github.com/leanprover-community/mathlib/pull/6442))
I worked out what was mentioned here: https://github.com/leanprover-community/mathlib/blob/20b49fbd453fc42c91c36ee30ecb512d70f48172/src/category_theory/monoidal/transport.lean#L283-L287
except for uniqueness, not sure how important that is

### [2021-02-26 21:29:04](https://github.com/leanprover-community/mathlib/commit/a225e12)
feat(linear_algebra/basic): add is_scalar_tower instance for hom type ([#6331](https://github.com/leanprover-community/mathlib/pull/6331))
This instance tells Lean that if R is an S-algebra with R and S both commutative semirings, then the R-action on Hom_R(M,N) is compatible with the S-action.
`linear_map.is_scalar_tower_extend_scalars` is just a special case of this new instance with the `smul_comm_class` arguments populated with `is_scalar_tower.to_smul_comm_class` and `smul_comm_class_self`, so has been removed.

### [2021-02-26 20:32:43](https://github.com/leanprover-community/mathlib/commit/407615e)
feat(algebra/lie/solvable): images of solvable Lie algebras are solvable ([#6413](https://github.com/leanprover-community/mathlib/pull/6413))
Summary of changes:
New definition:
 - `lie_hom.range_restrict`
New lemmas:
 - `lie_ideal.derived_series_map_eq`
 - `function.surjective.lie_algebra_is_solvable`
 - `lie_algebra.solvable_iff_equiv_solvable`
 - `lie_hom.is_solvable_range`
 - `lie_hom.mem_range_self`
 - `lie_hom.range_restrict_apply`
 - `lie_hom.surjective_range_restrict`
Renamed lemmas:
 - `lie_algebra.is_solvable_of_injective` → `function.injective.lie_algebra_is_solvable`
 - `lie_ideal.derived_series_map_le_derived_series` → `lie_ideal.derived_series_map_le`

### [2021-02-26 19:47:44](https://github.com/leanprover-community/mathlib/commit/ddefd96)
feat(category_theory/subobject): kernels and images as subobjects ([#6301](https://github.com/leanprover-community/mathlib/pull/6301))
Further work on subobjects,  building on the initial definition in [#6278](https://github.com/leanprover-community/mathlib/pull/6278).
* Add noncomputable functions to obtain representatives of subobjects.
* Realise kernel/equalizer/image as subobjects.

### [2021-02-26 15:56:35](https://github.com/leanprover-community/mathlib/commit/11e1cc3)
feat(data/equiv/basic): Add `fin_succ_above_equiv` ([#5145](https://github.com/leanprover-community/mathlib/pull/5145))

### [2021-02-26 13:13:36](https://github.com/leanprover-community/mathlib/commit/20b49fb)
feat(linear_algebra/tensor_product): allow different semirings in linear_map.flip ([#6414](https://github.com/leanprover-community/mathlib/pull/6414))
This also means the `map_*₂` lemmas are more generally applicable to linear_maps over different rings, such as `linear_map.prod_equiv.to_linear_map`.
To avoid breakage, this leaves `mk₂ R` for when R is commutative, and introduces `mk₂' R S` for when two different rings are wanted.

### [2021-02-26 13:13:35](https://github.com/leanprover-community/mathlib/commit/47b62ea)
feat(algebra/big_operators): add lemmas about `sum` and `pi.single` ([#6390](https://github.com/leanprover-community/mathlib/pull/6390))

### [2021-02-26 10:06:30](https://github.com/leanprover-community/mathlib/commit/aeda3fb)
feat(topology/instances/real, topology/metric_space/basic, algebra/floor): integers are a proper space ([#6437](https://github.com/leanprover-community/mathlib/pull/6437))
The metric space `ℤ` is a proper space.  Also, under the coercion from `ℤ` to `ℝ`, inverse images of compact sets are finite.
The key point for both facts is to express the inverse image of an `ℝ`-interval under the coercion as an appropriate `ℤ`-interval, using floor or ceiling of the endpoints -- I provide these facts as simp-lemmas.
Indirectly related discussion:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Finiteness.20of.20balls.20in.20the.20integers

### [2021-02-26 10:06:29](https://github.com/leanprover-community/mathlib/commit/ff5fa52)
chore(data/finsupp/basic): add coe_{neg,sub,smul} lemmas to match coe_{zero,add,fn_sum} ([#6350](https://github.com/leanprover-community/mathlib/pull/6350))
This also:
* merges together `smul_apply'` and `smul_apply`, since the latter is just a special case of the former.
* changes the implicitness of arguments to all of the `finsupp.*_apply` lemmas so that all the variables and none of the types are explicit
The whitespace style here matches how `coe_add` is spaced.

### [2021-02-26 10:06:28](https://github.com/leanprover-community/mathlib/commit/dd5363b)
feat(algebraic_topology): introduce the simplex category ([#6173](https://github.com/leanprover-community/mathlib/pull/6173))
* introduce `simplex_category`, with objects `nat` and morphisms `n ⟶ m` order-preserving maps from `fin (n+1)` to `fin (m+1)`.
* prove the simplicial identities
* show the category is equivalent to `NonemptyFinLinOrd`
This is the start of simplicial sets, moving and completing some of the material from @jcommelin's `sset` branch. Dold-Kan is the obvious objective; apparently we're going to need it for `lean-liquid` at some point.
The proofs of the simplicial identities are bad and slow. They involve extravagant use of nonterminal simp (`simp?` doesn't seem to give good answers) and lots of `linarith` bashing. Help welcome, especially if you love playing with inequalities in `nat` involving lots of `-1`s.

### [2021-02-26 07:13:25](https://github.com/leanprover-community/mathlib/commit/2f1de3f)
feat(polynomial/eval): lemmas relating eval/map on numerals ([#6438](https://github.com/leanprover-community/mathlib/pull/6438))

### [2021-02-26 07:13:24](https://github.com/leanprover-community/mathlib/commit/300e81d)
feat(analysis/complex/basic): complex conjugation is a linear isometry ([#6436](https://github.com/leanprover-community/mathlib/pull/6436))
Complex conjugation is a linear isometry (and various corollaries, eg it is a continuous linear map).
Also rewrite the results that `re` and `im` are continuous linear maps, to deduce from explicit bounds rather than passing through `linear_map.continuous_of_finite_dimensional`.

### [2021-02-26 07:13:23](https://github.com/leanprover-community/mathlib/commit/274042d)
feat(data/polynomial): basic lemmas ([#6434](https://github.com/leanprover-community/mathlib/pull/6434))

### [2021-02-26 07:13:22](https://github.com/leanprover-community/mathlib/commit/cca22d7)
feat(data/polynomial/degree/trailing_degree): Trailing degree of multiplication by X^n ([#6425](https://github.com/leanprover-community/mathlib/pull/6425))
A lemma about the trailing degree of a shifted polynomial.
(this PR is part of the irreducibility saga)

### [2021-02-26 07:13:21](https://github.com/leanprover-community/mathlib/commit/24ed74a)
feat(algebra/category/Semigroup/basic): categories of magmas and semigroups ([#6387](https://github.com/leanprover-community/mathlib/pull/6387))
This PR introduces the category of magmas and the category of semigroups, together with their additive versions.

### [2021-02-26 07:13:20](https://github.com/leanprover-community/mathlib/commit/aafa5fe)
feat(ring_theory/flat): definition of flat module ([#6284](https://github.com/leanprover-community/mathlib/pull/6284))

### [2021-02-26 07:13:19](https://github.com/leanprover-community/mathlib/commit/d451876)
doc(data/finset/basic): rewrite finset module doc ([#5893](https://github.com/leanprover-community/mathlib/pull/5893))

### [2021-02-26 04:07:32](https://github.com/leanprover-community/mathlib/commit/07d6d3f)
feat(algebra/algebra/basic): smul_mul_smul ([#6423](https://github.com/leanprover-community/mathlib/pull/6423))
An identity for algebras.
(this PR is part of the irreducibility saga)

### [2021-02-26 04:07:31](https://github.com/leanprover-community/mathlib/commit/0035e2d)
chore(*): upgrade to Lean 3.27.0c ([#6411](https://github.com/leanprover-community/mathlib/pull/6411))

### [2021-02-26 04:07:31](https://github.com/leanprover-community/mathlib/commit/5fbebf6)
fix(logic/{function}/basic): remove simp lemmas `function.injective.eq_iff` and `imp_iff_right` ([#6402](https://github.com/leanprover-community/mathlib/pull/6402))
* `imp_iff_right` is a conditional simp lemma that matches a lot and should never successfully rewrite.
* `function.injective.eq_iff` is a conditional simp lemma that matches a lot and is rarely used. Since you almost always need to give the proof `hf : function.injective f` as an argument to `simp`, you can replace it with `hf.eq_iff`.

### [2021-02-26 03:21:37](https://github.com/leanprover-community/mathlib/commit/0938880)
chore(scripts): update nolints.txt ([#6432](https://github.com/leanprover-community/mathlib/pull/6432))
I am happy to remove some nolints for you!

### [2021-02-26 00:42:52](https://github.com/leanprover-community/mathlib/commit/521b821)
feat(data/polynomial/basic): monomial_left_inj ([#6430](https://github.com/leanprover-community/mathlib/pull/6430))
A version of `finsupp.single_left_inj` for monomials, so that it works with `rw.`
(this PR is part of the irreducibility saga)

### [2021-02-26 00:42:51](https://github.com/leanprover-community/mathlib/commit/84ca016)
feat(data/polynomial/coeff): Alternate form of coeff_mul_X_pow ([#6424](https://github.com/leanprover-community/mathlib/pull/6424))
An `ite`-version of `coeff_mul_X_pow` that sometimes works better with `rw`.
(this PR is part of the irreducibility saga)

### [2021-02-26 00:42:50](https://github.com/leanprover-community/mathlib/commit/49d2191)
feat(data/polynomial/basic): monomial_neg ([#6422](https://github.com/leanprover-community/mathlib/pull/6422))
The monomial of a negation is the negation of the monomial.
(this PR is part of the irreducibility saga)

### [2021-02-26 00:42:49](https://github.com/leanprover-community/mathlib/commit/f34fa5f)
feat(algebra/algebra/subalgebra): use opt_param for redundant axioms ([#6417](https://github.com/leanprover-community/mathlib/pull/6417))

### [2021-02-26 00:42:48](https://github.com/leanprover-community/mathlib/commit/9d5088a)
feat(linear_algebra/pi): add `linear_equiv.pi` ([#6415](https://github.com/leanprover-community/mathlib/pull/6415))

### [2021-02-26 00:42:47](https://github.com/leanprover-community/mathlib/commit/61028ed)
chore(number_theory/bernoulli): use factorial notation ([#6412](https://github.com/leanprover-community/mathlib/pull/6412))

### [2021-02-26 00:42:46](https://github.com/leanprover-community/mathlib/commit/2755939)
feat(data/pnat/basic): add induction principle ([#6410](https://github.com/leanprover-community/mathlib/pull/6410))
An induction principle for `pnat`.  The proof is by Mario Carneiro.  If there are mistakes, I introduced them!
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/torsion.20free/near/227748865

### [2021-02-26 00:42:45](https://github.com/leanprover-community/mathlib/commit/6ed8b4b)
feat(linear_algebra/finite_dimensional): lemmas for zero dimensional vector spaces ([#6397](https://github.com/leanprover-community/mathlib/pull/6397))

### [2021-02-25 21:38:34](https://github.com/leanprover-community/mathlib/commit/d496676)
feat(geometry/manifold): manifold modelled on locally compact vector space is locally compact ([#6394](https://github.com/leanprover-community/mathlib/pull/6394))
Also connect `locally_compact_space` to `filter.has_basis`.

### [2021-02-25 21:38:33](https://github.com/leanprover-community/mathlib/commit/8770f5c)
refactor(topology/subset_properties): more properties of `compact_covering` ([#6328](https://github.com/leanprover-community/mathlib/pull/6328))
Modify the definition of `compact_covering α n` to ensure that it is monotone in `n`.
Also, in a locally compact space, prove the existence of a compact exhaustion, i.e. a sequence which satisfies the properties for `compact_covering` and in which, moreover, the interior of the next set includes the previous set.

### [2021-02-25 15:43:34](https://github.com/leanprover-community/mathlib/commit/85b5d5c)
refactor(logic/basic): turn *_prop_of_* into congr lemma ([#6406](https://github.com/leanprover-community/mathlib/pull/6406))
Alternative solution to the exists part of [#6404](https://github.com/leanprover-community/mathlib/pull/6404).

### [2021-02-25 09:50:19](https://github.com/leanprover-community/mathlib/commit/e3ae6cd)
feat(data/equiv/basic): lemmas about images and preimages ([#6398](https://github.com/leanprover-community/mathlib/pull/6398))

### [2021-02-25 07:29:30](https://github.com/leanprover-community/mathlib/commit/56f2c05)
chore(algebra/regular): rename lemma is_regular_of_cancel_monoid_with_zero to is_regular_of_ne_zero ([#6408](https://github.com/leanprover-community/mathlib/pull/6408))
Change the name of lemma is_regular_of_cancel_monoid_with_zero to the shorter is_regular_of_ne_zero.
Zulip reference:
https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics

### [2021-02-25 04:10:42](https://github.com/leanprover-community/mathlib/commit/4b6680a)
chore(scripts): update nolints.txt ([#6407](https://github.com/leanprover-community/mathlib/pull/6407))
I am happy to remove some nolints for you!

### [2021-02-25 04:10:41](https://github.com/leanprover-community/mathlib/commit/caed841)
feat(order/complete_lattice): add complete_lattice.independent.disjoint{_Sup,} ([#6405](https://github.com/leanprover-community/mathlib/pull/6405))

### [2021-02-25 04:10:40](https://github.com/leanprover-community/mathlib/commit/9d748f0)
feat(data/finset/basic): mem_map_equiv ([#6399](https://github.com/leanprover-community/mathlib/pull/6399))
This adds a version of `mem_map` specialized to equivs, which has a better simp-nf.

### [2021-02-25 04:10:39](https://github.com/leanprover-community/mathlib/commit/eba9be5)
feat(ring_theory/power_series/basic): remove const coeff ([#6383](https://github.com/leanprover-community/mathlib/pull/6383))
This shows that we can factor out X when the constant coefficient is removed from a power series.

### [2021-02-25 04:10:38](https://github.com/leanprover-community/mathlib/commit/a31d06a)
feat(data/zmod/basic): Explicitly state computable right_inverses instead of just surjectivity ([#5797](https://github.com/leanprover-community/mathlib/pull/5797))

### [2021-02-25 00:30:10](https://github.com/leanprover-community/mathlib/commit/a518fb8)
feat(data/list/basic): take_init, take_eq_nil ([#6380](https://github.com/leanprover-community/mathlib/pull/6380))

### [2021-02-24 22:06:41](https://github.com/leanprover-community/mathlib/commit/e66e136)
feat(data/mv_polynomial/basic): add two equivs ([#6324](https://github.com/leanprover-community/mathlib/pull/6324))
Two small lemma about `mv_polynomial` as `R`-algebra.

### [2021-02-24 21:08:03](https://github.com/leanprover-community/mathlib/commit/ead4731)
feat(geometry/manifold): `model_with_corners` is a `closed_embedding` ([#6393](https://github.com/leanprover-community/mathlib/pull/6393))

### [2021-02-24 21:08:02](https://github.com/leanprover-community/mathlib/commit/27b6110)
feat(algebra/lie/cartan_subalgebra): define Cartan subalgebras ([#6385](https://github.com/leanprover-community/mathlib/pull/6385))
We do this via the normalizer of a Lie subalgebra, which is also defined here.

### [2021-02-24 17:52:02](https://github.com/leanprover-community/mathlib/commit/25ea499)
feat(data/multiset/basic): subsingleton_equiv_apply' ([#6400](https://github.com/leanprover-community/mathlib/pull/6400))

### [2021-02-24 17:52:00](https://github.com/leanprover-community/mathlib/commit/6271fe5)
fix(tactic/delta_instance): beta reduce type of instance ([#6396](https://github.com/leanprover-community/mathlib/pull/6396))
The delta derive handler was creating instances that weren't beta reduced, which isn't a problem for type class inference but can be unexpected. @gebner fixed the line in doc-gen that assumed beta reduction, but we should also produce the expected instance in the first place.
Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/doc-gen.20is.20failing

### [2021-02-24 15:23:35](https://github.com/leanprover-community/mathlib/commit/3d9e790)
fix(topology/metric_space/cau_seq_filter): remove non-terminal simp ([#6401](https://github.com/leanprover-community/mathlib/pull/6401))

### [2021-02-24 11:31:20](https://github.com/leanprover-community/mathlib/commit/12afc98)
chore(data/matrix/basic): instances for unique, subsing, nontriv, coe ([#6296](https://github.com/leanprover-community/mathlib/pull/6296))
This adds a coercion to the underlying scalar if the matrix is 1 x 1.

### [2021-02-24 09:53:02](https://github.com/leanprover-community/mathlib/commit/85636f9)
feat(data/complex|matrix): instances of star_ordered_ring and star_ordered_algebra ([#4686](https://github.com/leanprover-community/mathlib/pull/4686))

### [2021-02-24 06:44:15](https://github.com/leanprover-community/mathlib/commit/196c2a8)
feat(topology/separation): a cont. function with a cont. left inverse is a closed embedding ([#6329](https://github.com/leanprover-community/mathlib/pull/6329))

### [2021-02-24 03:38:57](https://github.com/leanprover-community/mathlib/commit/9bad59c)
chore(scripts): update nolints.txt ([#6389](https://github.com/leanprover-community/mathlib/pull/6389))
I am happy to remove some nolints for you!

### [2021-02-24 03:38:56](https://github.com/leanprover-community/mathlib/commit/4a391c9)
fix(data/int/basic,category_theory/equivalence): use neg not minus in lemma names ([#6384](https://github.com/leanprover-community/mathlib/pull/6384))

### [2021-02-24 03:38:55](https://github.com/leanprover-community/mathlib/commit/358fdf2)
feat(category_theory/abelian/additive_functor): Adds definition of additive functors ([#6367](https://github.com/leanprover-community/mathlib/pull/6367))
This PR adds the basic definition of an additive functor.
See associated [zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Additive.20functors/near/227295322).

### [2021-02-24 00:38:48](https://github.com/leanprover-community/mathlib/commit/b4d2ce4)
chore(data/equiv/local_equiv,topology/local_homeomorph,data/set/function): review ([#6306](https://github.com/leanprover-community/mathlib/pull/6306))
## `data/equiv/local_equiv`:
* move `local_equiv.inj_on` lemmas closer to each other, add missing lemmas;
* rename `local_equiv.bij_on_source` to `local_equiv.bij_on`;
* rename `local_equiv.inv_image_target_eq_souce` to `local_equiv.symm_image_target_eq_souce`;
## `data/set/function`
* add `set.inj_on.mem_of_mem_image`, `set.inj_on.mem_image_iff`, `set.inj_on.preimage_image_inter`;
* add `set.left_inv_on.image_image'` and `set.left_inv_on.image_image`;
* add `function.left_inverse.right_inv_on_range`;
* move `set.inj_on.inv_fun_on_image` to golf the proof;
## `topology/local_homeomorph`
* add lemmas like `local_homeomorph.inj_on`;
* golf the definition of `open_embedding.to_local_homeomorph`, make `f` explicit.

### [2021-02-23 21:11:54](https://github.com/leanprover-community/mathlib/commit/387db0d)
feat(data/real/sqrt): add continuity attributes ([#6388](https://github.com/leanprover-community/mathlib/pull/6388))
I add continuity attributes to `continuous_sqrt` and `continuous.sqrt`.

### [2021-02-23 21:11:53](https://github.com/leanprover-community/mathlib/commit/8cfada1)
doc(measure_theory/interval_integral): move comment ([#6386](https://github.com/leanprover-community/mathlib/pull/6386))

### [2021-02-23 21:11:52](https://github.com/leanprover-community/mathlib/commit/2d51a44)
feat(data/list/basic): nth_drop ([#6381](https://github.com/leanprover-community/mathlib/pull/6381))

### [2021-02-23 21:11:50](https://github.com/leanprover-community/mathlib/commit/63e7535)
chore(group_theory/coset): right_coset additions and module doc ([#6371](https://github.com/leanprover-community/mathlib/pull/6371))
This PR dualises two results from left_coset to right_coset and adds a module doc.

### [2021-02-23 17:14:41](https://github.com/leanprover-community/mathlib/commit/750d117)
feat(logic/basic): subsingleton_iff_forall_eq ([#6379](https://github.com/leanprover-community/mathlib/pull/6379))

### [2021-02-23 17:14:40](https://github.com/leanprover-community/mathlib/commit/59bf982)
feat(algebra/lie/nilpotent): basic facts about nilpotent Lie algebras ([#6378](https://github.com/leanprover-community/mathlib/pull/6378))

### [2021-02-23 17:14:39](https://github.com/leanprover-community/mathlib/commit/4b22c39)
feat(ring_theory/power_series/well_known): sum of power of exponentials ([#6368](https://github.com/leanprover-community/mathlib/pull/6368))

### [2021-02-23 17:14:38](https://github.com/leanprover-community/mathlib/commit/e3d6cf8)
feat(measure_theory/integration): add theorems about the product of independent random variables ([#6106](https://github.com/leanprover-community/mathlib/pull/6106))
Consider the integral of the product of two random variables. Two random variables are independent if the preimage of all measurable sets are independent variables. Alternatively, if there is a pair of independent measurable spaces (as sigma algebras are independent), then two random variables are independent if they are measurable with respect to them.

### [2021-02-23 14:09:45](https://github.com/leanprover-community/mathlib/commit/f84f5b2)
feat(category_theory/subobject): the semilattice_inf/sup of subobjects ([#6278](https://github.com/leanprover-community/mathlib/pull/6278))
# The lattice of subobjects
We define `subobject X` as the quotient (by isomorphisms) of
`mono_over X := {f : over X // mono f.hom}`.
Here `mono_over X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not a partial order.
We provide
* `def pullback [has_pullbacks C] (f : X ⟶ Y) : subobject Y ⥤ subobject X`
* `def map (f : X ⟶ Y) [mono f] : subobject X ⥤ subobject Y`
* `def «exists» [has_images C] (f : X ⟶ Y) : subobject X ⥤ subobject Y`
(each first at the level of `mono_over`), and prove their basic properties and relationships.
We also provide the `semilattice_inf_top (subobject X)` instance when `[has_pullback C]`,
and the `semilattice_inf (subobject X)` instance when `[has_images C] [has_finite_coproducts C]`.
## Notes
This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Scott Morrison.

### [2021-02-23 14:09:44](https://github.com/leanprover-community/mathlib/commit/7f46c81)
feat(chain_complex): lemmas about eq_to_hom ([#6250](https://github.com/leanprover-community/mathlib/pull/6250))
Adds two lemmas relating `eq_to_hom` to differentials and chain maps. Useful in the ubiquitous circumstance of having to apply identities in the index of a chain complex.
Also add some `@[reassoc]` tags for convenience.

### [2021-02-23 14:09:43](https://github.com/leanprover-community/mathlib/commit/8d3efb7)
feat(data/buffer/basic): read and to_buffer lemmas ([#6048](https://github.com/leanprover-community/mathlib/pull/6048))

### [2021-02-23 10:52:40](https://github.com/leanprover-community/mathlib/commit/391c90a)
feat(logic/basic): subsingleton_of_forall_eq ([#6376](https://github.com/leanprover-community/mathlib/pull/6376))

### [2021-02-23 10:52:39](https://github.com/leanprover-community/mathlib/commit/e6d23d2)
feat(ring_theory/power_series/basic): coeff_succ_X_mul ([#6370](https://github.com/leanprover-community/mathlib/pull/6370))

### [2021-02-23 09:46:58](https://github.com/leanprover-community/mathlib/commit/3ff9248)
feat({group,ring}_theory/free_*): make free_ring.lift and free_comm_ring.lift equivs ([#6364](https://github.com/leanprover-community/mathlib/pull/6364))
This also adds `free_ring.hom_ext` and `free_comm_ring.hom_ext`, and deduplicates the definitions of the two lifts by introducing `abelian_group.lift_monoid`.

### [2021-02-23 06:48:15](https://github.com/leanprover-community/mathlib/commit/b7a7b3d)
feat(algebra/regular): lemmas for powers of regular elements ([#6356](https://github.com/leanprover-community/mathlib/pull/6356))
Prove that an element is (left/right-)regular iff a power of it is (left/right-)regular.

### [2021-02-23 06:48:15](https://github.com/leanprover-community/mathlib/commit/ec36fc0)
fix(data/set/finite): add decidable assumptions ([#6264](https://github.com/leanprover-community/mathlib/pull/6264))
Yury's rule of thumb https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/classicalize/near/224871122 says that we should have decidable instances here, because the statements of the lemmas need them (rather than the proofs). I'm making this PR to see if anything breaks.

### [2021-02-23 06:48:14](https://github.com/leanprover-community/mathlib/commit/680e8ed)
feat(order/well_founded_set): defining `is_partially_well_ordered` to prove `is_wf.add` ([#6226](https://github.com/leanprover-community/mathlib/pull/6226))
Defines `set.is_partially_well_ordered s`, equivalent to any infinite sequence to `s` contains an infinite monotone subsequence
Provides a basic API for `set.is_partially_well_ordered`
Proves `is_wf.add` and `is_wf.mul`

### [2021-02-23 05:21:51](https://github.com/leanprover-community/mathlib/commit/5931c5c)
lint(set_theory/ordinal): fix def/lemma ([#6369](https://github.com/leanprover-community/mathlib/pull/6369))

### [2021-02-23 01:14:10](https://github.com/leanprover-community/mathlib/commit/3c66fd1)
chore(scripts): update nolints.txt ([#6373](https://github.com/leanprover-community/mathlib/pull/6373))
I am happy to remove some nolints for you!

### [2021-02-22 21:32:01](https://github.com/leanprover-community/mathlib/commit/7a91822)
feat(data/fintype/intervals): Add set.finite lemmas for integer intervals ([#6365](https://github.com/leanprover-community/mathlib/pull/6365))

### [2021-02-22 21:32:00](https://github.com/leanprover-community/mathlib/commit/c038984)
chore(data/equiv/*): add missing coercion lemmas for equivs ([#6268](https://github.com/leanprover-community/mathlib/pull/6268))
This does not affect the simp-normal form.
This tries to make a lot of lemma names and statements more consistent:
* restates `linear_map.mk_apply` to be `linear_map.coe_mk` to match `monoid_hom.coe_mk`
* adds `linear_map.to_linear_map_eq_coe`
* adds the simp lemma `linear_map.coe_to_equiv`
* adds the simp lemma `linear_map.linear_map.coe_to_linear_map`
* adds the simp lemma `linear_map.to_fun_eq_coe`
* adds the missing `ancestor` attributes required to make `to_additive` work for things like `add_equiv.to_add_hom`
* restates `add_equiv.to_fun_apply` to be `add_equiv.to_fun_eq_coe`
* restates `add_equiv.to_equiv_apply` to be `add_equiv.coe_to_equiv`
* adds the simp lemma `add_equiv.coe_to_mul_hom`
* removes `add_equiv.to_add_monoid_hom_apply` since `add_equiv.coe_to_add_monoid_hom` is a shorter and more general statement
* restates `ring_equiv.to_fun_apply` to be `ring_equiv.to_fun_eq_coe`
* restates `ring_equiv.coe_mul_equiv` to be `ring_equiv.coe_to_mul_equiv`
* restates `ring_equiv.coe_add_equiv` to be `ring_equiv.coe_to_add_equiv`
* restates `ring_equiv.coe_ring_hom` to be `ring_equiv.coe_to_ring_hom`
* adds `ring_equiv.to_ring_hom_eq_coe`
* adds `ring_equiv.to_add_equiv_eq_coe`
* adds `ring_equiv.to_mul_equiv_eq_coe`

### [2021-02-22 18:48:55](https://github.com/leanprover-community/mathlib/commit/283aaff)
feat(ring_theory/power_series/well_known): power of exponential ([#6330](https://github.com/leanprover-community/mathlib/pull/6330))
Co-authored by Fabian Kruse

### [2021-02-22 18:48:54](https://github.com/leanprover-community/mathlib/commit/0fb6ada)
chore(topology): move `exists_compact_superset`, drop assumption `t2_space` ([#6327](https://github.com/leanprover-community/mathlib/pull/6327))
Also golf the proof of `is_compact.elim_finite_subcover_image`

### [2021-02-22 18:48:53](https://github.com/leanprover-community/mathlib/commit/db00ee4)
feat(ring_theory/polynomial/basic): add quotient_equiv_quotient_mv_polynomial ([#6287](https://github.com/leanprover-community/mathlib/pull/6287))
I've added `quotient_equiv_quotient_mv_polynomial` that says that `(R/I)[x_i] ≃+* (R[x_i])/I` where `I` is an ideal of `R`. I've included also a version for `R`-algebras. The proof is very similar to the case of (one variable) polynomials.

### [2021-02-22 18:48:52](https://github.com/leanprover-community/mathlib/commit/cc9d3ab)
feat(algebra/module,linear_algebra): generalize `smul_eq_zero` ([#6199](https://github.com/leanprover-community/mathlib/pull/6199))
Moves the theorem on division rings `smul_eq_zero` to a typeclass `no_zero_smul_divisors` with instances for the previously existing cases. The motivation for this change is that [#6178](https://github.com/leanprover-community/mathlib/pull/6178) added another `smul_eq_zero`, which could be captured neatly as an instance of the typeclass.
I didn't spend a lot of time yet on figuring out all the necessary instances, first let's see whether this compiles.

### [2021-02-22 17:14:14](https://github.com/leanprover-community/mathlib/commit/7abfbc9)
doc(references.bib): add witt vector references and normalize ([#6366](https://github.com/leanprover-community/mathlib/pull/6366))
Now that we're actually displaying these bib links we should pay more attention to them.
Two commits: one adds references for the Witt vector files, the other normalizes the bib file. We can drop the second if people don't care.

### [2021-02-22 17:14:13](https://github.com/leanprover-community/mathlib/commit/70d7114)
feat(nat/choose): lemmas regarding binomial coefficients ([#6362](https://github.com/leanprover-community/mathlib/pull/6362))

### [2021-02-22 17:14:10](https://github.com/leanprover-community/mathlib/commit/4daac66)
chore(field_theory/mv_polynomial): generalised to comm_ring and module doc ([#6341](https://github.com/leanprover-community/mathlib/pull/6341))
This PR generalises most of `field_theory/mv_polynomial` from polynomial rings over fields to polynomial rings over commutative rings. This is put into a separate file. 
Also renamed the field to K and did one tiny golf.

### [2021-02-22 14:12:42](https://github.com/leanprover-community/mathlib/commit/6d2726c)
feat(number_theory/bernoulli): definition and properties of Bernoulli numbers ([#6363](https://github.com/leanprover-community/mathlib/pull/6363))

### [2021-02-22 14:12:41](https://github.com/leanprover-community/mathlib/commit/46fb0d8)
feat(big_operators/intervals): lemma on dependent double sum ([#6361](https://github.com/leanprover-community/mathlib/pull/6361))

### [2021-02-22 14:12:40](https://github.com/leanprover-community/mathlib/commit/12bb9ae)
chore(linear_algebra/*): split lines and doc `direct_sum/tensor_product` ([#6360](https://github.com/leanprover-community/mathlib/pull/6360))
This PR provides a short module doc to `direct_sum/tensor_product` (the file contains only one result). Furthermore, it splits lines in the `linear_algebra` folder.

### [2021-02-22 14:12:39](https://github.com/leanprover-community/mathlib/commit/a10c19d)
doc(group_theory/*): module docs for `quotient_group` and `presented_group` ([#6358](https://github.com/leanprover-community/mathlib/pull/6358))

### [2021-02-22 14:12:38](https://github.com/leanprover-community/mathlib/commit/590442a)
feat(topology/subset_properties): locally finite family on a compact space is finite ([#6352](https://github.com/leanprover-community/mathlib/pull/6352))

### [2021-02-22 14:12:37](https://github.com/leanprover-community/mathlib/commit/120feb1)
refactor(order/filter,topology): review API ([#6347](https://github.com/leanprover-community/mathlib/pull/6347))
### Filters
* move old `filter.map_comap` to `filter.map_comap_of_mem`;
* add a new `filter.map_comap` that doesn't assume `range m ∈ f` but
  gives `map m (comap m f) = f ⊓ 𝓟 (range m)` instead of
  `map m (comap m f) = f`;
* add `filter.comap_le_comap_iff`, use it to golf a couple of proofs;
* move some lemmas using `filter.map_comap`/`filter.map_comap_of_mem`
  closure to these lemmas;
* use `function.injective m` instead of `∀ x y, m x = m y → x = y` in
  some lemmas;
* drop `filter.le_map_comap_of_surjective'`,
  `filter.map_comap_of_surjective'`, and
  `filter.le_map_comap_of_surjective`: the inequalities easily follow
  from equalities, and `filter.map_comap_of_surjective'` is just
  `filter.map_comap_of_mem`+`filter.mem_sets_of_superset`;
### Topology
* add `closed_embedding_subtype_coe`, `ennreal.open_embedding_coe`;
* drop `inducing_open`, `inducing_is_closed`, `embedding_open`, and
  `embedding_is_closed` replace them with `inducing.is_open_map` and
  `inducing.is_closed_map`;
* move old `inducing.map_nhds_eq` to `inducing.map_nhds_of_mem`, the
  new `inducing.map_nhds_eq` says `map f (𝓝 a) = 𝓝[range f] (f a)`;
* add `inducing.is_closed_iff`;
* move old `embedding.map_nhds_eq` to `embedding.map_nhds_of_mem`, the
  new `embedding.map_nhds_eq` says `map f (𝓝 a) = 𝓝[range f] (f a)`;
* add `open_embedding.map_nhds_eq`;
* change signature of `is_closed_induced_iff` to match other similar
  lemmas;
* move old `map_nhds_induced_eq` to `map_nhds_induced_of_mem`, the new
  `map_nhds_induced_eq` give `𝓝[range f] (f a)` instead of `𝓝 (f a)`.

### [2021-02-22 14:12:36](https://github.com/leanprover-community/mathlib/commit/26e6d4c)
feat(algebra/lie/{subalgebra,submodule}): grab bag of new lemmas ([#6342](https://github.com/leanprover-community/mathlib/pull/6342))
I'm splitting these off from other work to simplify subsequent reviews.
Cosmetic changes aside, the following summarises what I am proposing:
New definitions:
 - `lie_subalgebra.of_le`
Definition tweaks:
 - `lie_hom.range` [use coercion instead of `lie_hom.to_linear_map`]
 - `lie_ideal.map` [factor through `submodule.map` to avoid dropping all the way down to `set.image`]
New lemmas:
 - `lie_ideal.coe_to_lie_subalgebra_to_submodule`
 - `lie_ideal.incl_range`
 - `lie_hom.ideal_range_eq_lie_span_range`
 - `lie_hom.is_ideal_morphism_iff`
 - `lie_subalgebra.mem_range`
 - `lie_subalgebra.mem_map`
 - `lie_subalgebra.mem_of_le`
 - `lie_subalgebra.of_le_eq_comap_incl`
 - `lie_subalgebra.exists_lie_ideal_coe_eq_iff`
 - `lie_subalgebra.exists_nested_lie_ideal_coe_eq_iff`
 - `submodule.exists_lie_submodule_coe_eq_iff`
 - `lie_submodule.coe_lie_span_submodule_eq_iff`
Deleted lemma:
 - `lie_hom.range_bracket`
New simp attributes:
 - `lie_subalgebra.mem_top`
 - `lie_submodule.mem_top`

### [2021-02-22 14:12:35](https://github.com/leanprover-community/mathlib/commit/78eb83a)
feat(linear_algebra/pi): add `pi.lsum` ([#6335](https://github.com/leanprover-community/mathlib/pull/6335))

### [2021-02-22 14:12:34](https://github.com/leanprover-community/mathlib/commit/aa730c6)
feat(linear_algebra): a module has a unique submodule iff it has a unique element ([#6281](https://github.com/leanprover-community/mathlib/pull/6281))
Also strengthens the related lemmas about subgroup and submonoid

### [2021-02-22 14:12:33](https://github.com/leanprover-community/mathlib/commit/ffb6a58)
feat(data/sigma/basic): add a more convenient ext lemma for equality of sigma types over subtypes ([#6257](https://github.com/leanprover-community/mathlib/pull/6257))

### [2021-02-22 14:12:32](https://github.com/leanprover-community/mathlib/commit/9d54837)
feat(data/polynomial/degree): lemmas on nat_degree and behaviour under multiplication by constants ([#6224](https://github.com/leanprover-community/mathlib/pull/6224))
These lemmas extend the API for nat_degree
I intend to use them to work with integrality statements

### [2021-02-22 10:42:24](https://github.com/leanprover-community/mathlib/commit/87a021c)
feat(data/quot): `quotient.rec_on_subsingleton` with implicit setoid ([#6346](https://github.com/leanprover-community/mathlib/pull/6346))

### [2021-02-22 10:42:23](https://github.com/leanprover-community/mathlib/commit/69b93fc)
fix(data/finsupp/basic): delta-reduce the definition of coe_fn_injective ([#6344](https://github.com/leanprover-community/mathlib/pull/6344))
Without this, `apply coe_fn_injective` leaves a messy goal that usually has to be `dsimp`ed in order to make progress with `rw`.
With this change, `dsimp` now fails as the goal is already fully delta-reduced.

### [2021-02-22 08:31:25](https://github.com/leanprover-community/mathlib/commit/0e51976)
feat(data/polynomial/reverse): Trailing degree is multiplicative ([#6351](https://github.com/leanprover-community/mathlib/pull/6351))
Uses `polynomial.reverse` to prove that `nat_trailing_degree` behaves well under multiplication.

### [2021-02-22 06:58:33](https://github.com/leanprover-community/mathlib/commit/a3d951b)
feat(data/nat/digits): digits injective at fixed base ([#6338](https://github.com/leanprover-community/mathlib/pull/6338))

### [2021-02-22 06:58:32](https://github.com/leanprover-community/mathlib/commit/2b6dec0)
feat(algebraic_geometry/prime_spectrum): specialization order ([#6286](https://github.com/leanprover-community/mathlib/pull/6286))

### [2021-02-22 03:13:35](https://github.com/leanprover-community/mathlib/commit/dc78177)
chore(scripts): update nolints.txt ([#6354](https://github.com/leanprover-community/mathlib/pull/6354))
I am happy to remove some nolints for you!

### [2021-02-22 03:13:34](https://github.com/leanprover-community/mathlib/commit/2134d0c)
feat(algebra/group_power/basic): `abs_lt_abs_of_sqr_lt_sqr` ([#6277](https://github.com/leanprover-community/mathlib/pull/6277))
These lemmas are (almost) the converses of some of the lemmas I added in [#5933](https://github.com/leanprover-community/mathlib/pull/5933).

### [2021-02-22 00:01:15](https://github.com/leanprover-community/mathlib/commit/b8b8755)
feat(data/list/basic): repeat injectivity ([#6337](https://github.com/leanprover-community/mathlib/pull/6337))

### [2021-02-21 21:41:23](https://github.com/leanprover-community/mathlib/commit/87f8db2)
feat(data/dfinsupp): add coe lemmas ([#6343](https://github.com/leanprover-community/mathlib/pull/6343))
These lemmas already exist for `finsupp`, let's add them for `dfinsupp` too.

### [2021-02-21 21:41:22](https://github.com/leanprover-community/mathlib/commit/96ae2ad)
docs(undergrad.yaml): recent changes ([#6313](https://github.com/leanprover-community/mathlib/pull/6313))

### [2021-02-21 18:45:11](https://github.com/leanprover-community/mathlib/commit/4355d17)
chore(topology/order): drop an unneeded argument ([#6345](https://github.com/leanprover-community/mathlib/pull/6345))
`closure_induced` doesn't need `f` to be injective.

### [2021-02-21 18:45:10](https://github.com/leanprover-community/mathlib/commit/ab03ebe)
feat(data/list/basic): drop_eq_nil_iff_le ([#6336](https://github.com/leanprover-community/mathlib/pull/6336))
The iff version of a recently added lemma.

### [2021-02-21 15:22:22](https://github.com/leanprover-community/mathlib/commit/473bb7d)
feat(topology/locally_constant): basics on locally constant functions ([#6192](https://github.com/leanprover-community/mathlib/pull/6192))
From `lean-liquid`

### [2021-02-21 06:06:38](https://github.com/leanprover-community/mathlib/commit/f470cc6)
feat(measure_theory/interval_integral): add simp attribute to `integral_const` ([#6334](https://github.com/leanprover-community/mathlib/pull/6334))
By adding a `simp` attribute to `interval_integral.integral_const`, the likes of the following become possible:
```
import measure_theory.interval_integral
example : ∫ x:ℝ in 5..19, (12:ℝ) = 168 := by norm_num
```

### [2021-02-21 01:15:37](https://github.com/leanprover-community/mathlib/commit/4d4c7bb)
chore(scripts): update nolints.txt ([#6332](https://github.com/leanprover-community/mathlib/pull/6332))
I am happy to remove some nolints for you!

### [2021-02-20 21:10:00](https://github.com/leanprover-community/mathlib/commit/93d1760)
chore(topology/bases): golf a proof ([#6326](https://github.com/leanprover-community/mathlib/pull/6326))
Also add some supporting lemmas

### [2021-02-20 21:09:59](https://github.com/leanprover-community/mathlib/commit/08ea23b)
refactor(group_theory/free_*): remove API duplicated by lift, promote lift functions to equivs ([#6311](https://github.com/leanprover-community/mathlib/pull/6311))
This removes:
* `free_group.to_group.to_fun` and `free_group.to_group`, as these are both subsumed by the stronger `lift`.
* `abelianization.hom_equiv` as this is now `abelianization.lift.symm`
* `free_abelian_group.hom_equiv` as this is now `free_abelian_group.lift.symm`

### [2021-02-20 17:42:12](https://github.com/leanprover-community/mathlib/commit/dccc542)
fix(algebra/group/pi): remove unnecessary add_monoid requirement from pi.single_zero ([#6325](https://github.com/leanprover-community/mathlib/pull/6325))
Follows on from [#6317](https://github.com/leanprover-community/mathlib/pull/6317)

### [2021-02-20 17:42:11](https://github.com/leanprover-community/mathlib/commit/f0aad50)
feat(data/equiv/basic): injective iff injective after composing with equiv ([#6283](https://github.com/leanprover-community/mathlib/pull/6283))

### [2021-02-20 17:42:10](https://github.com/leanprover-community/mathlib/commit/ee8708e)
feat(algebra/regular): define regular elements ([#6282](https://github.com/leanprover-community/mathlib/pull/6282))
The goal of this PR is to start the API for regular elements.  The final goal is to talk about non-zero-divisors.
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/is_regular

### [2021-02-20 15:00:59](https://github.com/leanprover-community/mathlib/commit/1855bd5)
chore(*): split lines ([#6323](https://github.com/leanprover-community/mathlib/pull/6323))

### [2021-02-20 11:52:21](https://github.com/leanprover-community/mathlib/commit/ed55502)
doc(algebraic_geometry/is_open_comap_C): add reference to Stacks project ([#6322](https://github.com/leanprover-community/mathlib/pull/6322))
Updated the doc-strings to reference the Stacks project.
Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/stacks.20tags

### [2021-02-20 11:52:20](https://github.com/leanprover-community/mathlib/commit/52e2937)
feat(topology): the currying homeomorphism ([#6319](https://github.com/leanprover-community/mathlib/pull/6319))

### [2021-02-20 11:52:19](https://github.com/leanprover-community/mathlib/commit/26d287c)
doc(ring_theory/*): two module docs ([#6318](https://github.com/leanprover-community/mathlib/pull/6318))
This PR provides module docs for `ring_theory.polynomial.scale_roots` as well as `ring_theory.multiplicity`. Furthermore, some lines are split in those two files.

### [2021-02-20 11:52:19](https://github.com/leanprover-community/mathlib/commit/c7c40a7)
feat(*/pi): add lemmas about how `single` interacts with operators ([#6317](https://github.com/leanprover-community/mathlib/pull/6317))
This also adds a missing pi instances for `monoid_with_zero`.

### [2021-02-20 09:02:14](https://github.com/leanprover-community/mathlib/commit/4d2dcdb)
chore(*): fix broken Zulip archive links ([#6321](https://github.com/leanprover-community/mathlib/pull/6321))

### [2021-02-20 01:44:35](https://github.com/leanprover-community/mathlib/commit/3e381ad)
chore(ring_theory/*): split lines ([#6316](https://github.com/leanprover-community/mathlib/pull/6316))

### [2021-02-20 01:44:34](https://github.com/leanprover-community/mathlib/commit/32b9b21)
refactor(linear_algebra/pi): add `linear_map.single` to match `add_monoid_hom.single` ([#6315](https://github.com/leanprover-community/mathlib/pull/6315))
This changes the definition of `std_basis` to be exactly `linear_map.single`, but proves equality with the old definition.
In future, it might make sense to remove `std_basis` entirely.

### [2021-02-20 01:44:33](https://github.com/leanprover-community/mathlib/commit/d483bc2)
chore(data/indicator_function): add a formula for the support of `indicator` ([#6314](https://github.com/leanprover-community/mathlib/pull/6314))
* rename `set.support_indicator` to `set.support_indicator_subset`;
* add a new `set.support_indicator`;
* add `function.support_comp_eq_preimage`.

### [2021-02-20 01:01:26](https://github.com/leanprover-community/mathlib/commit/3ab9818)
chore(scripts): update nolints.txt ([#6320](https://github.com/leanprover-community/mathlib/pull/6320))
I am happy to remove some nolints for you!

### [2021-02-19 14:14:19](https://github.com/leanprover-community/mathlib/commit/845654a)
feat(analysis/calculus): define a smooth bump function ([#4458](https://github.com/leanprover-community/mathlib/pull/4458))
Define an infinitely smooth function which is `1` on the closed ball of radius `1` and is `0` outside of the open ball of radius `2`.

### [2021-02-19 12:23:04](https://github.com/leanprover-community/mathlib/commit/f6eef43)
doc(ring_theory): move some module docstring to correct place ([#6312](https://github.com/leanprover-community/mathlib/pull/6312))

### [2021-02-19 12:23:03](https://github.com/leanprover-community/mathlib/commit/aaab837)
doc(ring_theory/witt_vector/witt_polynomial): move module docstring up ([#6310](https://github.com/leanprover-community/mathlib/pull/6310))

### [2021-02-19 12:23:02](https://github.com/leanprover-community/mathlib/commit/0df1998)
doc(set_theory/*): more documentation about cardinals and ordinals ([#6247](https://github.com/leanprover-community/mathlib/pull/6247))

### [2021-02-19 12:23:01](https://github.com/leanprover-community/mathlib/commit/114f8ef)
chore(data/buffer/parser/numeral): derive mono for numeral ([#5463](https://github.com/leanprover-community/mathlib/pull/5463))
Thanks to Rob Lewis, using classes, instances, and the `delta_instance_handler`, transferring over instances becomes very easy.

### [2021-02-19 09:04:38](https://github.com/leanprover-community/mathlib/commit/e5c7789)
fix(lint/type_classes): fix instance_priority bug ([#6305](https://github.com/leanprover-community/mathlib/pull/6305))
The linter now doesn't fail if the type is a beta redex

### [2021-02-19 07:04:09](https://github.com/leanprover-community/mathlib/commit/a0e2b3c)
chore(topology/Profinite): reduce universe variables ([#6300](https://github.com/leanprover-community/mathlib/pull/6300))
See https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/universe.20issue

### [2021-02-19 07:04:08](https://github.com/leanprover-community/mathlib/commit/64d86f7)
feat(topology/{subset_properties,separation}): closed subsets of compact t0 spaces contain a closed point ([#6273](https://github.com/leanprover-community/mathlib/pull/6273))
This adds two statements.  The first is that nonempty closed subsets of a compact space have a minimal nonempty closed subset, and the second is that when the space is additionally T0 then that minimal subset is a singleton.
(This PR does not do this, but one can go on to show that there is functor from compact T0 spaces to T1 spaces by taking the set of closed points, and it preserves nonemptiness.)

### [2021-02-19 04:14:30](https://github.com/leanprover-community/mathlib/commit/626a4b5)
chore(scripts): update nolints.txt ([#6303](https://github.com/leanprover-community/mathlib/pull/6303))
I am happy to remove some nolints for you!

### [2021-02-19 04:14:29](https://github.com/leanprover-community/mathlib/commit/75149c3)
feat(data/list/basic): tail_drop, cons_nth_le_drop_succ ([#6265](https://github.com/leanprover-community/mathlib/pull/6265))

### [2021-02-19 00:43:42](https://github.com/leanprover-community/mathlib/commit/1fecd52)
fix(tactic/push_neg): fully simplify expressions not named `h` ([#6297](https://github.com/leanprover-community/mathlib/pull/6297))
A final pass of `push_neg` is intended to turn `¬ a = b` into `a ≠ b`.
Unfortunately, when you use `push_neg at ...`, this is applied to the hypothesis literally named `h`.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60push_neg.60.20behaviour.20depends.20on.20variable.20name)

### [2021-02-18 23:50:16](https://github.com/leanprover-community/mathlib/commit/3a8d976)
fix(archive/100/82): remove nonterminal simps ([#6299](https://github.com/leanprover-community/mathlib/pull/6299))

### [2021-02-18 23:50:15](https://github.com/leanprover-community/mathlib/commit/8696990)
feat(category_theory/adjunction/reflective): show compositions of reflective are reflective ([#6298](https://github.com/leanprover-community/mathlib/pull/6298))
Show compositions of reflective are reflective.

### [2021-02-18 20:23:11](https://github.com/leanprover-community/mathlib/commit/96f8933)
perf(tactic/lint/frontend): run linters in parallel ([#6293](https://github.com/leanprover-community/mathlib/pull/6293))
With this change it takes 5 minutes instead of 33 minutes to lint mathlib (on my machine...).
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/linting.20time

### [2021-02-18 16:34:50](https://github.com/leanprover-community/mathlib/commit/619c1b0)
chore({algebra, algebraic_geometry}/*): move 1 module doc and split lines ([#6294](https://github.com/leanprover-community/mathlib/pull/6294))
This moves the module doc for `algebra/ordered_group` so that it gets recognised by the linter. Furthermore, several lines are split in the algebra and algebraic_geometry folder.

### [2021-02-18 11:09:39](https://github.com/leanprover-community/mathlib/commit/5b579a2)
feat(topology/category/profinite): show Profinite is reflective in CompHaus ([#6219](https://github.com/leanprover-community/mathlib/pull/6219))
Show Profinite is reflective in CompHaus.

### [2021-02-18 09:36:21](https://github.com/leanprover-community/mathlib/commit/5a59781)
fix(doc/references.bib): fix syntax ([#6290](https://github.com/leanprover-community/mathlib/pull/6290))

### [2021-02-18 08:05:51](https://github.com/leanprover-community/mathlib/commit/2a7eafa)
feat(order/pfilter): add preorder filters, dual to preorder ideals ([#5928](https://github.com/leanprover-community/mathlib/pull/5928))
Named `pfilter` to not conflict with the existing `order/filter`,
which is a much more developed theory of a special case of this.

### [2021-02-18 05:31:27](https://github.com/leanprover-community/mathlib/commit/017acae)
feat(linear_algebra/dual): adds dual annihilators ([#6078](https://github.com/leanprover-community/mathlib/pull/6078))

### [2021-02-18 02:18:27](https://github.com/leanprover-community/mathlib/commit/7c267df)
chore(scripts): update nolints.txt ([#6289](https://github.com/leanprover-community/mathlib/pull/6289))
I am happy to remove some nolints for you!

### [2021-02-17 23:53:33](https://github.com/leanprover-community/mathlib/commit/7592a8f)
chore(analysis/normed_space/finite_dimension,topology/metric_space): golf ([#6285](https://github.com/leanprover-community/mathlib/pull/6285))
* golf two proofs about `finite_dimension`;
* move `proper_image_of_proper` to `antilipschitz`, rename to
  `antilipschitz_with.proper_space`, golf.

### [2021-02-17 23:53:32](https://github.com/leanprover-community/mathlib/commit/bc1c4f2)
feat(data/zmod/basic): add simp lemmas about coercions, tidy lemma names ([#6280](https://github.com/leanprover-community/mathlib/pull/6280))
Split from [#5797](https://github.com/leanprover-community/mathlib/pull/5797). This takes the new proofs without introducing the objectionable names.
This also renames a bunch of lemmas from `zmod.cast_*` to `zmod.nat_cast_*` and `zmod.int_cast_*`, in order to distinguish lemmas about `zmod.cast` from lemmas about `nat.cast` and `int.cast` applied with a zmod argument.
As an example, `zmod.cast_val` has been renamed to `zmod.nat_cast_zmod_val`, as the lemma statement is defeq to `(nat.cast : ℕ → zmod n) (zmod.val x) = x`, and `zmod.nat_cast_val` is already taken by `nat.cast (zmod.val x) = (x : R)`.
The full list of renames:
* `zmod.cast_val` → `zmod.nat_cast_zmod_val`
* `zmod.cast_self` → `zmod.nat_cast_self`
* `zmod.cast_self'` → `zmod.nat_cast_self'`
* `zmod.cast_mod_nat` → `zmod.nat_cast_mod`
* `zmod.cast_mod_int` → `zmod.int_cast_mod`
* `zmod.val_cast_nat` → `zmod.val_nat_cast`
* `zmod.coe_to_nat` → `zmod.nat_cast_to_nat`
* `zmod.cast_unit_of_coprime` → `coe_unit_of_coprime`
* `zmod.cast_nat_abs_val_min_abs` → `zmod.nat_cast_nat_abs_val_min_abs`

### [2021-02-17 20:29:45](https://github.com/leanprover-community/mathlib/commit/75f3346)
feat(analysis/normed_space/multilinear): generalized `curry` ([#6270](https://github.com/leanprover-community/mathlib/pull/6270))

### [2021-02-17 20:29:44](https://github.com/leanprover-community/mathlib/commit/152bf15)
feat(data/fin): pred_above_monotone ([#6170](https://github.com/leanprover-community/mathlib/pull/6170))

### [2021-02-17 15:49:57](https://github.com/leanprover-community/mathlib/commit/4bae1c4)
doc(tactic/algebra): document @[ancestor] ([#6272](https://github.com/leanprover-community/mathlib/pull/6272))

### [2021-02-17 15:49:55](https://github.com/leanprover-community/mathlib/commit/07a1b8d)
feat(ring_theory/simple_module): introduce `is_semisimple_module` ([#6215](https://github.com/leanprover-community/mathlib/pull/6215))
Defines `is_semisimple_module` to mean that the lattice of submodules is complemented
Shows that this is equivalent to the module being the `Sup` of its simple submodules

### [2021-02-17 11:38:42](https://github.com/leanprover-community/mathlib/commit/f066eb1)
feat(algebra/lie/subalgebra): define lattice structure for Lie subalgebras ([#6279](https://github.com/leanprover-community/mathlib/pull/6279))
We already have the lattice structure for Lie submodules but not for subalgebras.
This is mostly a lightly-edited copy-paste of the corresponding subset of results
for Lie submodules that remain true for subalgebras.
The results which hold for Lie submodules but not for Lie subalgebras are:
  - `sup_coe_to_submodule` and `mem_sup`
  - `is_modular_lattice`
I have also made a few tweaks to bring the structure and naming of Lie
subalgebras a little closer to that of Lie submodules.

### [2021-02-17 11:38:41](https://github.com/leanprover-community/mathlib/commit/d43a3ba)
feat(analysis/normed_space/inner_product): norm is smooth at `x ≠ 0` ([#6275](https://github.com/leanprover-community/mathlib/pull/6275))

### [2021-02-17 11:38:40](https://github.com/leanprover-community/mathlib/commit/b190131)
feat(data/int/basic): lemmas about int and int.to_nat ([#6253](https://github.com/leanprover-community/mathlib/pull/6253))
Golfing welcome.
This adds a `@[simp]` lemma `int.add_minus_one : i + -1 = i - 1`, which I think is mostly helpful, but needs to be turned off in `data/num/lemmas.lean`, which is perhaps an argument against it.
I've also added a lemma
```
@[simp] lemma lt_self_iff_false [preorder α] (a : α) : a < a ↔ false :=
```
(not just for `int`), which I've often found useful (e.g. `simpa` works well when it can reduce a hypothesis to `false`). This lemma seems harmless, but I'm happy to hear objections if it is too general.

### [2021-02-17 11:38:39](https://github.com/leanprover-community/mathlib/commit/8b8a5a2)
feat(category/eq_to_hom): lemmas to replace rewriting in objects with eq_to_hom ([#6252](https://github.com/leanprover-community/mathlib/pull/6252))
This adds two lemmas which replace expressions in which we've used `eq.mpr` to rewrite the source or target of a morphism, replacing the `eq.mpr` by composition with an `eq_to_hom`.
Possibly we just shouldn't add these

### [2021-02-17 11:38:38](https://github.com/leanprover-community/mathlib/commit/ea1cff4)
feat(linear_algebra/pi): ext lemma for `f : (Π i, M i) →ₗ[R] N` ([#6233](https://github.com/leanprover-community/mathlib/pull/6233))

### [2021-02-17 11:38:37](https://github.com/leanprover-community/mathlib/commit/0c61fc4)
feat(group_theory): prove the 2nd isomorphism theorem for groups ([#6187](https://github.com/leanprover-community/mathlib/pull/6187))
Define an `inclusion` homomorphism from a subgroup `H` contained in `K` to `K`. Add instance of `subgroup.normal` to `H ∩ N` in `H` whenever `N` is normal and use it to prove the 2nd isomorphism theorem for groups.

### [2021-02-17 11:38:36](https://github.com/leanprover-community/mathlib/commit/9b3008e)
feat(algebra/ordered_monoid): inequalities involving mul/add ([#6171](https://github.com/leanprover-community/mathlib/pull/6171))
I couldn't find some statements about inequalities, so I'm adding them. I included all the useful variants I could think of.

### [2021-02-17 11:38:35](https://github.com/leanprover-community/mathlib/commit/3c15751)
feat(ring_theory/ideal/operations) : add lemma prod_eq_bot ([#5795](https://github.com/leanprover-community/mathlib/pull/5795))
Add lemma `prod_eq_bot` showing that a product of ideals in an integral domain is zero if and only if one of the terms
is zero.

### [2021-02-17 07:54:59](https://github.com/leanprover-community/mathlib/commit/11f054b)
chore(topology/sheaves): speed up slow proofs by tidy ([#6274](https://github.com/leanprover-community/mathlib/pull/6274))
No changes, just making some proofs by tidy explicit, so the file is not quite as slow as previously. Now compiles with `-T40000`.

### [2021-02-17 07:54:58](https://github.com/leanprover-community/mathlib/commit/5258de0)
feat(data/fin): refactor `pred_above` ([#6125](https://github.com/leanprover-community/mathlib/pull/6125))
Currently the signature of `pred_above` is
```lean
def pred_above (p : fin (n+1)) (i : fin (n+1)) (hi : i ≠ p) : fin n := ...
```
and its behaviour is "subtract one from `i` if it is greater than `p`".
There are two reasons I don't like this much:
1. It's not a total function.
2. Since `succ_above` is exactly a simplicial face map, I'd like `pred_above` to be a simplicial degeneracy map.
In this PR I propose replacing this with
```lean
def pred_above (p : fin n) (i : fin (n+1)) : fin n :=
```
again with the behaviour "subtract one from `i` if it is greater than `p`".
~~Unfortunately, it seems the current `pred_above` really is needed for the sake of `fin.insert_nth`, so this PR has ended up as a half-hearted attempt to replace `pred_above`

### [2021-02-17 03:54:44](https://github.com/leanprover-community/mathlib/commit/b2dbfd6)
chore(scripts): update nolints.txt ([#6276](https://github.com/leanprover-community/mathlib/pull/6276))
I am happy to remove some nolints for you!

### [2021-02-17 03:54:43](https://github.com/leanprover-community/mathlib/commit/d4ef2e8)
feat(topology/category/Top): nonempty inverse limit of compact Hausdorff spaces ([#6271](https://github.com/leanprover-community/mathlib/pull/6271))
The limit of an inverse system of nonempty compact Hausdorff spaces is nonempty, and this can be seen as a generalization of Kőnig's lemma.  A future PR will address the weaker generalization that the limit of an inverse system of nonempty finite types is nonempty.
This result could be generalized more, to the inverse limit of nonempty compact T0 spaces where all the maps are closed, but I think it involves an essentially different method.

### [2021-02-17 03:54:42](https://github.com/leanprover-community/mathlib/commit/bf9ca8b)
feat(data/set/finite): complement of finite set is infinite ([#6266](https://github.com/leanprover-community/mathlib/pull/6266))
Add two missing lemmas. One-line proofs due to Yakov Pechersky.

### [2021-02-16 23:59:06](https://github.com/leanprover-community/mathlib/commit/7a7a559)
feat(option/basic): add join_eq_none ([#6269](https://github.com/leanprover-community/mathlib/pull/6269))

### [2021-02-16 23:59:05](https://github.com/leanprover-community/mathlib/commit/781cc63)
feat(data/real/liouville, ring_theory/algebraic): a Liouville number is transcendental! ([#6204](https://github.com/leanprover-community/mathlib/pull/6204))
This is an annotated proof.  It finishes the first half of the Liouville PR.
A taste of what is to come in a future PR: a proof that Liouville numbers actually exist!

### [2021-02-16 23:59:04](https://github.com/leanprover-community/mathlib/commit/efa6877)
feat(algebra/category/Module): the free/forgetful adjunction for R-modules ([#6168](https://github.com/leanprover-community/mathlib/pull/6168))

### [2021-02-16 23:59:03](https://github.com/leanprover-community/mathlib/commit/3bf7241)
feat(algebra/algebra,linear_algebra): add *_equiv.of_left_inverse ([#6167](https://github.com/leanprover-community/mathlib/pull/6167))
The main purpose of this change is to add equivalences onto the range of a function with a left-inverse:
* `algebra_equiv.of_left_inverse`
* `linear_equiv.of_left_inverse`
* `ring_equiv.of_left_inverse`
* `ring_equiv.sof_left_inverse` (the sub***S***emiring version)
This also:
* Renames `alg_hom.alg_equiv.of_injective` to `alg_equiv.of_injective`
* Adds `subalgebra.mem_range_self` and `subsemiring.mem_srange_self` for consistency with `subring.mem_range_self`
* Replaces `subring.surjective_onto_range` with `subring.range_restrict_surjective`, which have defeq statements
These are computable versions of `*_equiv.of_injective`, with the benefit of having a known inverse, and in the case of `linear_equiv` working for `semiring` and not just `ring`.

### [2021-02-16 21:22:44](https://github.com/leanprover-community/mathlib/commit/2289b18)
chore(topology/basic): add `continuous_at_congr` and `continuous_at.congr` ([#6267](https://github.com/leanprover-community/mathlib/pull/6267))

### [2021-02-16 18:36:50](https://github.com/leanprover-community/mathlib/commit/0b4823c)
doc(*): remove `\\` hack for latex backslashes in markdown ([#6263](https://github.com/leanprover-community/mathlib/pull/6263))
With leanprover-community/doc-gen[#110](https://github.com/leanprover-community/mathlib/pull/110), these should no longer be needed.

### [2021-02-16 18:36:49](https://github.com/leanprover-community/mathlib/commit/16eb4af)
doc(algebraic_geometry/structure_sheaf): fix latex ([#6262](https://github.com/leanprover-community/mathlib/pull/6262))
This is broken regardless of the markdown processor: <https://leanprover-community.github.io/mathlib_docs/algebraic_geometry/structure_sheaf.html#algebraic_geometry.structure_sheaf.is_locally_fraction>

### [2021-02-16 18:36:48](https://github.com/leanprover-community/mathlib/commit/7459c21)
feat(analysis/special_functions): strict differentiability of `real.exp` and `real.log` ([#6256](https://github.com/leanprover-community/mathlib/pull/6256))

### [2021-02-16 18:36:47](https://github.com/leanprover-community/mathlib/commit/b0071f3)
feat(analysis/special_functions): `sqrt` is infinitely smooth at `x ≠ 0` ([#6255](https://github.com/leanprover-community/mathlib/pull/6255))
Also move lemmas about differentiability of `sqrt` out from `special_functions/pow` to a new file.

### [2021-02-16 18:36:46](https://github.com/leanprover-community/mathlib/commit/8a43163)
feat(topology/algebra/normed_group): completion of normed groups ([#6189](https://github.com/leanprover-community/mathlib/pull/6189))
From `lean-liquid`

### [2021-02-16 18:36:45](https://github.com/leanprover-community/mathlib/commit/35c070f)
chore(linear_algebra/dfinsupp): make lsum a linear_equiv ([#6185](https://github.com/leanprover-community/mathlib/pull/6185))
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20inference.20can't.20fill.20in.20parameters/near/226019081) with a summary of the problem which required the nasty `semimodule_of_linear_map` present here.

### [2021-02-16 15:40:57](https://github.com/leanprover-community/mathlib/commit/2411d68)
doc(algebra/big_operators): fix formatting of library note ([#6261](https://github.com/leanprover-community/mathlib/pull/6261))
The name of a library note is already used as its title: <https://leanprover-community.github.io/mathlib_docs_demo/notes.html#operator%20precedence%20of%20big%20operators>

### [2021-02-16 12:05:22](https://github.com/leanprover-community/mathlib/commit/362619e)
chore(data/equiv/basic): add lemmas about `equiv.cast` ([#6246](https://github.com/leanprover-community/mathlib/pull/6246))

### [2021-02-16 12:05:21](https://github.com/leanprover-community/mathlib/commit/841b007)
doc(control/fold): fix bad markdown ([#6245](https://github.com/leanprover-community/mathlib/pull/6245))

### [2021-02-16 12:05:20](https://github.com/leanprover-community/mathlib/commit/beee5d8)
doc(topology/category/*): 5 module docs ([#6240](https://github.com/leanprover-community/mathlib/pull/6240))
This PR provides module docs to `Top.basic`, `Top.limits`, `Top.adjuntions`, `Top.epi_mono` , `TopCommRing`.
Furthermore, a few lines are split to please the line length linter.

### [2021-02-16 12:05:19](https://github.com/leanprover-community/mathlib/commit/0716fa4)
feat(data/set/intervals/basic): not_mem of various intervals ([#6238](https://github.com/leanprover-community/mathlib/pull/6238))
`c` is not in a given open/closed/unordered interval if it is outside the bounds of that interval (or if it is not in a superset of that interval).

### [2021-02-16 12:05:17](https://github.com/leanprover-community/mathlib/commit/914517b)
feat(order/well_founded_set): finite antidiagonal of well-founded sets ([#6208](https://github.com/leanprover-community/mathlib/pull/6208))
Defines `set.add_antidiagonal s t a`, the set of pairs of an element from `s` and an element from `t` that add to `a`
If `s` and `t` are well-founded, then constructs a finset version, `finset.add_antidiagonal_of_is_wf`

### [2021-02-16 12:05:16](https://github.com/leanprover-community/mathlib/commit/1a43888)
feat(analysis/normed_space/operator_norm): bundle more arguments ([#6207](https://github.com/leanprover-community/mathlib/pull/6207))
* Drop `lmul_left` in favor of a partially applied `lmul`.
* Use `lmul_left_right` in `has_fderiv_at_ring_inverse` and related lemmas.
* Add bundled `compL`, `lmulₗᵢ`, `lsmul`.
* Make `𝕜` argument in `of_homothety` implicit.
* Add `deriv₂` and `bilinear_comp`.

### [2021-02-16 12:05:15](https://github.com/leanprover-community/mathlib/commit/8d9eb26)
chore(linear_algebra/finsupp): make lsum a linear_equiv ([#6183](https://github.com/leanprover-community/mathlib/pull/6183))

### [2021-02-16 12:05:14](https://github.com/leanprover-community/mathlib/commit/314f5ad)
feat(ring_theory/finiteness): add quotient of finitely presented ([#6098](https://github.com/leanprover-community/mathlib/pull/6098))
I've added `algebra.finitely_presented.quotient`: the quotient of a finitely presented algebra by a finitely generated ideal is finitely presented. To do so I had to prove some preliminary results about finitely generated modules.

### [2021-02-16 12:05:12](https://github.com/leanprover-community/mathlib/commit/3cec1cf)
feat(apply_fun): handle implicit arguments ([#6091](https://github.com/leanprover-community/mathlib/pull/6091))
I've modified the way `apply_fun` handles inequalities, by building an intermediate expression before calling `mono` to discharge the `monotone f` subgoal. This has the effect of sometimes filling in implicit arguments successfully, so that `mono` works.
In `tests/apply_fun.lean` I've added an example showing this in action

### [2021-02-16 12:05:11](https://github.com/leanprover-community/mathlib/commit/d3c5667)
feat(number_theory/bernoulli): the odd Bernoulli numbers (greater than 1) are zero ([#6056](https://github.com/leanprover-community/mathlib/pull/6056))
The proof requires a ring homomorphism between power series to be defined, `eval_mul_hom` . This PR defines it and states some of its properties, along with the result that `e^(ax) * e^(bx) = e^((a + b) x)`, which is needed for the final result, `bernoulli_odd_eq_zero`.

### [2021-02-16 12:05:10](https://github.com/leanprover-community/mathlib/commit/2da1ab4)
feat(data/equiv): Add lemmas to reduce `@finset.univ (perm (fin n.succ)) _` ([#5593](https://github.com/leanprover-community/mathlib/pull/5593))
The culmination of these lemmas is that `matrix.det` can now be reduced by a minimally steered simp:
```lean
import data.matrix.notation
import group_theory.perm.fin
import linear_algebra.determinant
open finset
example {α : Type} [comm_ring α] {a b c d : α} :
  matrix.det ![![a, b], ![c, d]] = a * d - b * c :=
begin
  simp [matrix.det, univ_perm_fin_succ, ←univ_product_univ, sum_product, fin.sum_univ_succ, fin.prod_univ_succ],
  ring
end
```

### [2021-02-16 09:30:21](https://github.com/leanprover-community/mathlib/commit/dc917df)
feat(category/limits/shapes/zero): lemmas about is_isomorphic 0 ([#6251](https://github.com/leanprover-community/mathlib/pull/6251))

### [2021-02-16 09:30:20](https://github.com/leanprover-community/mathlib/commit/d7003c1)
feat(algebra/category/Module): allow writing (0 : Module R) ([#6249](https://github.com/leanprover-community/mathlib/pull/6249))

### [2021-02-16 09:30:19](https://github.com/leanprover-community/mathlib/commit/2961e79)
feat(topology/connected.lean): define pi_0 and prove basic properties ([#6188](https://github.com/leanprover-community/mathlib/pull/6188))
Define and prove basic properties of pi_0, the functor quotienting a space by its connected components. 
For dot notation convenience, this PR renames `subset_connected_component` to `is_preconnected.subset_connected_component` and also defines the weaker version `is_connected.subset_connected_component`.

### [2021-02-16 08:09:48](https://github.com/leanprover-community/mathlib/commit/acf2b6d)
docs(algebraic_geometry/Scheme): fix typo in module docstring ([#6254](https://github.com/leanprover-community/mathlib/pull/6254))

### [2021-02-16 06:42:40](https://github.com/leanprover-community/mathlib/commit/dbe586c)
chore(scripts): update nolints.txt ([#6248](https://github.com/leanprover-community/mathlib/pull/6248))
I am happy to remove some nolints for you!

### [2021-02-16 00:20:31](https://github.com/leanprover-community/mathlib/commit/97f7b52)
chore(data/logic/unique): there is a unique function with domain pempty ([#6243](https://github.com/leanprover-community/mathlib/pull/6243))

### [2021-02-15 21:04:25](https://github.com/leanprover-community/mathlib/commit/65fe78a)
feat(analysis/special_functions/trigonometric): add missing continuity attributes ([#6236](https://github.com/leanprover-community/mathlib/pull/6236))
I added continuity attributes to lemmas about the continuity of trigonometric functions, e.g. `continuous_sin`, `continuous_cos`, `continuous_tan`, etc. This came up in [this Zulip conversation](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/What's.20new.20in.20Lean.20maths.3F/near/221511451)
I also added `real.continuous_tan`.

### [2021-02-15 17:15:21](https://github.com/leanprover-community/mathlib/commit/0ed6f7c)
feat(data/real/liouville, topology/metric_space/basic): further preparations for Liouville ([#6201](https://github.com/leanprover-community/mathlib/pull/6201))
These lemmas are used to show that a Liouville number is transcendental.
The statement that Liouville numbers are transcendental is the next PR in this sequence!

### [2021-02-15 13:26:17](https://github.com/leanprover-community/mathlib/commit/26c6fb5)
chore(data/set/basic): set.union_univ and set.univ_union ([#6239](https://github.com/leanprover-community/mathlib/pull/6239))

### [2021-02-15 13:26:16](https://github.com/leanprover-community/mathlib/commit/d6db038)
refactor(analysis/normed_space/multilinear): use `≃ₗᵢ` for `curry` equivs ([#6232](https://github.com/leanprover-community/mathlib/pull/6232))
Also copy some `continuous_linear_equiv` API to `linear_isometry_equiv` (e.g., all API in `analysis.calculus.fderiv`).

### [2021-02-15 13:26:15](https://github.com/leanprover-community/mathlib/commit/f5c55ae)
feat(analysis/normed_space/basic): uniform_continuous_norm ([#6162](https://github.com/leanprover-community/mathlib/pull/6162))
From `lean-liquid`

### [2021-02-15 13:26:14](https://github.com/leanprover-community/mathlib/commit/0fa1312)
feat(linear_algebra/unitary_group): add unitary/orthogonal groups ([#5702](https://github.com/leanprover-community/mathlib/pull/5702))

### [2021-02-15 10:01:44](https://github.com/leanprover-community/mathlib/commit/9f0687c)
feat(order/liminf_limsup): liminf_nat_add and liminf_le_of_frequently_le' ([#6220](https://github.com/leanprover-community/mathlib/pull/6220))
Add `liminf_nat_add (f : ℕ → α) (k : ℕ) : at_top.liminf f = at_top.liminf (λ i, f (i + k))`. Same for `limsup`.
Add `liminf_le_of_frequently_le'`, variant of `liminf_le_of_frequently_le` in which the lattice is complete but there is no linear order. Same for `limsup`.

### [2021-02-15 03:01:16](https://github.com/leanprover-community/mathlib/commit/1f0bf33)
chore(scripts): update nolints.txt ([#6234](https://github.com/leanprover-community/mathlib/pull/6234))
I am happy to remove some nolints for you!

### [2021-02-15 03:01:15](https://github.com/leanprover-community/mathlib/commit/0469268)
doc(topology/subset_properties): minor change to docstring of `is_compact` ([#6231](https://github.com/leanprover-community/mathlib/pull/6231))
I'm learning (for the first time) about how to do topology with filters, and this docstring confused me for a second. If there are linguistic reasons for leaving it as it is then fair enough, but it wasn't clear to me on first reading that `a` was independent of the set in the filter.

### [2021-02-15 03:01:14](https://github.com/leanprover-community/mathlib/commit/5a6c893)
feat(topology/algebra/module): 2 new ext lemmas ([#6211](https://github.com/leanprover-community/mathlib/pull/6211))
Add ext lemmas for maps `f : M × M₂ →L[R] M₃` and `f : R →L[R] M`.

### [2021-02-15 03:01:13](https://github.com/leanprover-community/mathlib/commit/c94577a)
feat(group_theory/free_abelian_group): add module doc and some equivs ([#6062](https://github.com/leanprover-community/mathlib/pull/6062))
Also add some API for `free_abelian_group.map`.

### [2021-02-14 23:17:58](https://github.com/leanprover-community/mathlib/commit/6f99407)
feat(analysis/calculus/inverse): a function with onto strict derivative is locally onto ([#6229](https://github.com/leanprover-community/mathlib/pull/6229))
Removes a useless assumption in `map_nhds_eq_of_complemented` (no need to have a completemented subspace).
The proof of the local inverse theorem breaks into two parts, local injectivity and local surjectivity. We refactor the local surjectivity part, assuming in the proof only that the derivative is onto. The result is stronger, but the proof is less streamlined since there is no contracting map any more: we give a naive proof from first principles instead of reducing to the fixed point theorem for contracting maps.

### [2021-02-14 19:41:17](https://github.com/leanprover-community/mathlib/commit/22b26d3)
chore(algebra/group/basic): remove three redundant lemmas ([#6197](https://github.com/leanprover-community/mathlib/pull/6197))
The following lemmas are changed in this PR (long list because of the additive versions:
* `mul_eq_left_iff` for `left_cancel_monoid` is renamed to `mul_right_eq_self` which previously was stated for `group`
* `add_eq_left_iff` the additive version is automatically renamed to `add_right_eq_self`
* `mul_eq_right_iff` for `right_cancel_monoid` is renamed to `mul_left_eq_self` which previously was stated for `group`
* `add_eq_right_iff` the additive version is automatically renamed to `add_left_eq_self`
* `left_eq_mul_iff` is renamed to `self_eq_mul_right` to fit the convention above
* `left_eq_add_iff` is renamed to `self_eq_add_right` to fit the convention above
* `right_eq_mul_iff` is renamed to `self_eq_mul_left` to fit the convention above
* `right_eq_add_iff` is renamed to `self_eq_add_left` to fit the convention above
* the duplicate `mul_left_eq_self` and `add_left_eq_self` for groups are removed
* the duplicate `mul_right_eq_self` and `add_right_eq_self` for groups are removed
* `mul_self_iff_eq_one` and `add_self_iff_eq_zero` deal only with the special case `a=b` of the other lemmas. It is therefore removed and the few instances in the library are replaced by one of the above. 
While I was at it, I provided a module doc for this file.

### [2021-02-14 16:06:00](https://github.com/leanprover-community/mathlib/commit/c35672b)
feat(analysis/special_functions): strict differentiability of some functions ([#6228](https://github.com/leanprover-community/mathlib/pull/6228))

### [2021-02-14 16:05:59](https://github.com/leanprover-community/mathlib/commit/713432f)
chore(.github/PULL_REQUEST_TEMPLATE.md): clarify instructions ([#6222](https://github.com/leanprover-community/mathlib/pull/6222))

### [2021-02-14 14:16:51](https://github.com/leanprover-community/mathlib/commit/b9af22d)
fix(*): arsinh and complex.basic had module docs at the wrong position ([#6230](https://github.com/leanprover-community/mathlib/pull/6230))
This is fixed and the module doc for `complex.basic` is expanded slightly.

### [2021-02-14 03:41:08](https://github.com/leanprover-community/mathlib/commit/c54a8d0)
chore(scripts): update nolints.txt ([#6227](https://github.com/leanprover-community/mathlib/pull/6227))
I am happy to remove some nolints for you!

### [2021-02-14 01:28:45](https://github.com/leanprover-community/mathlib/commit/86e8a5d)
fix(data/real/basic): remove `decidable_le` field in `real.conditionally_complete_linear_order` ([#6223](https://github.com/leanprover-community/mathlib/pull/6223))
Because of this field, `@conditionally_complete_linear_order.to_linear_order ℝ real.conditionally_complete_linear_order` and `real.linear_order` were not defeq
See : https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Different.20linear.20orders.20on.20reals/near/226257434
Co-authored by @urkud

### [2021-02-13 22:35:47](https://github.com/leanprover-community/mathlib/commit/b0aae27)
feat(algebra/category/Group/adjunctions): free_group-forgetful adjunction ([#6190](https://github.com/leanprover-community/mathlib/pull/6190))
Furthermore, a module doc for `group_theory/free_group` is provided and a few lines in this file are split.

### [2021-02-13 22:35:46](https://github.com/leanprover-community/mathlib/commit/07600ee)
feat(computability/epsilon_nfa): epsilon-NFA definition ([#6108](https://github.com/leanprover-community/mathlib/pull/6108))

### [2021-02-13 19:32:58](https://github.com/leanprover-community/mathlib/commit/ac19b4a)
refactor(measure_theory/l1_space): remove one of the two definitions of L1 space ([#6058](https://github.com/leanprover-community/mathlib/pull/6058))
Currently, we have two independent versions of the `L^1` space in mathlib: one coming from the general family of `L^p` spaces, the other one is an ad hoc construction based on the `integrable` predicate used in the construction of the Bochner integral.
We remove the second construction, and use instead the `L^1` space coming from the family of `L^p` spaces to construct the Bochner integral. Still, we keep the `integrable` predicate as it is generally useful, and show that it coincides with the `mem_Lp 1` predicate.

### [2021-02-13 17:23:27](https://github.com/leanprover-community/mathlib/commit/ad5a81d)
chore(measure_theory/measure_space): add some `simp`/`mono` tags ([#6221](https://github.com/leanprover-community/mathlib/pull/6221))

### [2021-02-13 14:34:16](https://github.com/leanprover-community/mathlib/commit/3cfaa0b)
feat(measure_theory/measure_space): add ae_imp_iff ([#6218](https://github.com/leanprover-community/mathlib/pull/6218))
This is `filter.eventually_imp_distrib_left` specialized to the measure.ae filter.

### [2021-02-13 12:18:12](https://github.com/leanprover-community/mathlib/commit/d0456d3)
feat(measure_theory/borel_space): add ae_measurable versions of finset.measurable_prod and measurable.ennreal_tsum ([#6217](https://github.com/leanprover-community/mathlib/pull/6217))
Also add an ae_measurable version of `ae_lt_top`.

### [2021-02-13 12:18:11](https://github.com/leanprover-community/mathlib/commit/42bb0c4)
feat(ring_theory/ideal/operations): add first isomorphism theorem for rings and algebras ([#6166](https://github.com/leanprover-community/mathlib/pull/6166))
The first isomorphism theorem for commutative rings `quotient_ker_equiv_of_surjective` and algebras `quotient_ker_alg_equiv_of_surjective`.

### [2021-02-13 12:18:10](https://github.com/leanprover-community/mathlib/commit/8b59d97)
feat(linear_algebra/pi_tensor_product): tmul distributes over tprod ([#6126](https://github.com/leanprover-community/mathlib/pull/6126))
This adds the equivalence `(⨂[R] i : ι, M) ⊗[R] (⨂[R] i : ι₂, M) ≃ₗ[R] ⨂[R] i : ι ⊕ ι₂, M`.
Working with dependently-typed `M` here is more trouble than it's worth, as we don't have any typeclass structures on `sum.elim M N` right now,
This is one of the pieces needed to provide a ring structure on `⨁ n, ⨂[R] i : fin n, M`, but that's left for another time.

### [2021-02-13 09:47:57](https://github.com/leanprover-community/mathlib/commit/445e6fc)
refactor(topology/{basic,continuous_on}): review `continuous_if` etc ([#6182](https://github.com/leanprover-community/mathlib/pull/6182))
* move `continuous_if` to `topology/continuous_on`, use weaker assumptions;
* add `piecewise` versions of various `if` lemmas;
* add a specialized `continuous_if_le` version;
* use dot notation for `continuous_on.if` and `continuous_on.if'`;
* minor golfing here and there.

### [2021-02-13 09:47:56](https://github.com/leanprover-community/mathlib/commit/5c22531)
doc(data/polynomial/denoms_clearable): fix typo in the doc-string ([#6174](https://github.com/leanprover-community/mathlib/pull/6174))

### [2021-02-13 07:17:57](https://github.com/leanprover-community/mathlib/commit/5bee826)
feat(data/int/gcd): some missing lemmas about int.gcd ([#6212](https://github.com/leanprover-community/mathlib/pull/6212))
As requested [on zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/different.20gcd's.3F/near/226203698).

### [2021-02-13 07:17:56](https://github.com/leanprover-community/mathlib/commit/0544641)
chore(analysis/special_functions/pow): review lemmas about measurability of `cpow`/`rpow` ([#6209](https://github.com/leanprover-community/mathlib/pull/6209))
* prove that `complex.cpow` is measurable;
* deduce measurability of `real.rpow` from definition, not continuity.

### [2021-02-13 07:17:55](https://github.com/leanprover-community/mathlib/commit/ee9197a)
chore(topology/algebra/module): review `coe` lemmas ([#6206](https://github.com/leanprover-community/mathlib/pull/6206))
* add `@[simp]` to `continuous_linear_equiv.coe_coe`, remove from `continuous_linear_equiv.coe_apply`;
* golf `continuous_linear_equiv.ext`;
* given `(e e' : M ≃L[R] M₂)`, simplify `(e : M →L[R] M₂) = e'` to `e = e'`;
* add `@[simp]` to `continuous_linear_equiv.symm_comp_self` and `continuous_linear_equiv.self_comp_symm`;
* drop `symm_comp_self'` and `self_comp_symm'`: now `coe_coe` simplifies LHS to `symm_comp_self`/`self_comp_symm`;
* `continuous_linear_equiv.coord` is no longer an `abbreviation`: without this change `coe_coe` prevents us from using lemmas about `coord`;

### [2021-02-13 07:17:54](https://github.com/leanprover-community/mathlib/commit/43bfd90)
chore(group_theory/free_group): clean up unnecessary lemmas ([#6200](https://github.com/leanprover-community/mathlib/pull/6200))
This removes:
* `free_abelian_group.lift.{add,sub,neg,zero}` as these exist already as `(free_abelian_group.lift _).map_{add,sub,neg,zero}` 
* `free_group.to_group.{mul,one,inv}` as these exist already as `(free_group.to_group _).map_{mul,one,inv}`
* `free_group.map.{mul,one,inv}` as these exist already as `(free_group.map _).map_{mul,one,inv}`
* `free_group.prod.{mul,one,inv}` as these exist already as `free_group.prod.map_{mul,one,inv}`
* `to_group.is_group_hom` as this is provided automatically for `monoid_hom`s
and renames
* `free_group.sum.{mul,one,inv}` to `free_group.sum.map_{mul,one,inv}`
These lemmas are already simp lemmas thanks to the functions they relate to being bundled homs.
While the new spelling is slightly longer, it makes it clear that the entire set of `monoid_hom` lemmas apply, not just the three that were copied across.
This also wraps some lines to make the linter happier about these files.

### [2021-02-13 05:21:53](https://github.com/leanprover-community/mathlib/commit/759ebc0)
chore(analysis/calculus/local_extr): minor golfing ([#6214](https://github.com/leanprover-community/mathlib/pull/6214))

### [2021-02-13 03:56:07](https://github.com/leanprover-community/mathlib/commit/5869039)
chore(scripts): update nolints.txt ([#6213](https://github.com/leanprover-community/mathlib/pull/6213))
I am happy to remove some nolints for you!

### [2021-02-13 00:49:42](https://github.com/leanprover-community/mathlib/commit/37459ee)
doc(docs/overview.yaml): Added Hall's theorem ([#6205](https://github.com/leanprover-community/mathlib/pull/6205))
Also fixed module documentation to use inline math mode (and removed the dreaded "any").

### [2021-02-13 00:49:41](https://github.com/leanprover-community/mathlib/commit/06fdc08)
chore(algebra/group/pi): replace a lemma with @[simps] ([#6203](https://github.com/leanprover-community/mathlib/pull/6203))

### [2021-02-13 00:49:40](https://github.com/leanprover-community/mathlib/commit/e79bf05)
feat(number_theory/ADE_inequality): the inequality 1/p + 1/q + 1/r > 1 ([#6156](https://github.com/leanprover-community/mathlib/pull/6156))

### [2021-02-13 00:49:38](https://github.com/leanprover-community/mathlib/commit/30c2c5b)
feat(data/fin): cast_succ_mk and other lemmas ([#6094](https://github.com/leanprover-community/mathlib/pull/6094))
* add lemmas for all the `fin.cast_*` functions which describe what happens to an "explicitly presented" term of `fin n`, built from the constructor
* fixes some errors in doc-strings

### [2021-02-13 00:49:36](https://github.com/leanprover-community/mathlib/commit/152ad1f)
feat(measure_theory/measure_space): add theorems about restrict and subtraction ([#5000](https://github.com/leanprover-community/mathlib/pull/5000))
This is the next tranche of theorems toward Lebesgue-Radon-Nikodym.

### [2021-02-12 21:14:37](https://github.com/leanprover-community/mathlib/commit/dd13f00)
feat(data/set/intervals/basic): 24 lemmas about membership of arithmetic operations ([#6202](https://github.com/leanprover-community/mathlib/pull/6202))

### [2021-02-12 14:15:57](https://github.com/leanprover-community/mathlib/commit/254c3ee)
feat(analysis/special_functions/exp_log): added `log_div` ([#6196](https://github.com/leanprover-community/mathlib/pull/6196))
`∀ x y : ℝ, x ≠ 0 → y ≠ 0 → log (x / y) = log x - log y`

### [2021-02-12 14:15:56](https://github.com/leanprover-community/mathlib/commit/a5ccba6)
feat(analysis/calculus): generalize `has_strict_fderiv_at.map_nhds_eq` ([#6193](https://github.com/leanprover-community/mathlib/pull/6193))
Generalize `has_strict_fderiv_at.map_nhds_eq` to a function that satisfies assumptions of the implicit function theorem.

### [2021-02-12 12:44:07](https://github.com/leanprover-community/mathlib/commit/74d3270)
fix(topology/topological_fiber_bundle): fix definition, review ([#6184](https://github.com/leanprover-community/mathlib/pull/6184))
* fix definition of `is_topological_fiber_bundle`;
* add `is_trivial_topological_fiber_bundle`;
* more lemmas, golf here and there;
* define induced fiber bundle.

### [2021-02-12 10:09:14](https://github.com/leanprover-community/mathlib/commit/2d70880)
feat(topology/subset_properties): compact discrete spaces are finite ([#6191](https://github.com/leanprover-community/mathlib/pull/6191))
From `lean-liquid`

### [2021-02-12 02:51:33](https://github.com/leanprover-community/mathlib/commit/159e807)
chore(scripts): update nolints.txt ([#6194](https://github.com/leanprover-community/mathlib/pull/6194))
I am happy to remove some nolints for you!

### [2021-02-12 02:51:32](https://github.com/leanprover-community/mathlib/commit/72141fd)
feat(combinatorics/hall): Hall's marriage theorem ([#5695](https://github.com/leanprover-community/mathlib/pull/5695))
We state and prove Hall's marriage theorem with respect to fintypes and relations. 
Coauthor: @b-mehta @kmill

### [2021-02-11 23:33:03](https://github.com/leanprover-community/mathlib/commit/db305fb)
feat(data/set/finite): fintype_of_univ_finite ([#6164](https://github.com/leanprover-community/mathlib/pull/6164))
From `lean-liquid`

### [2021-02-11 23:33:02](https://github.com/leanprover-community/mathlib/commit/2f56620)
feat(data/real/irrational): define Liouville numbers ([#6158](https://github.com/leanprover-community/mathlib/pull/6158))
Prove that a Liouville number is irrational

### [2021-02-11 20:21:07](https://github.com/leanprover-community/mathlib/commit/64914d3)
chore(group_theory/perm, linear_algebra/alternating): add some helper lemmas for gh-5269 ([#6186](https://github.com/leanprover-community/mathlib/pull/6186))

### [2021-02-11 20:21:06](https://github.com/leanprover-community/mathlib/commit/cee5ddf)
chore(topology/homeomorph): review, add `prod_punit`/`punit_prod` ([#6180](https://github.com/leanprover-community/mathlib/pull/6180))
* use `to_equiv := e` instead of `.. e` to have definitional equality
  `h.to_equiv = e`;
* add some `@[simp]` lemmas;
* add `homeomorph.prod_punit` and `homeomorph.punit_prod`;
* generalize `unit.topological_space` to `punit.topological_space`.

### [2021-02-11 20:21:05](https://github.com/leanprover-community/mathlib/commit/6c602c7)
feat(data/nat/bitwise): test bits of powers of two ([#6070](https://github.com/leanprover-community/mathlib/pull/6070))

### [2021-02-11 16:21:09](https://github.com/leanprover-community/mathlib/commit/1ad29d6)
refactor(algebra/lie/of_associative): remove `ring_commutator` namespace; use `ring` instead ([#6181](https://github.com/leanprover-community/mathlib/pull/6181))
The `old_structure_cmd` change to `lie_algebra.is_simple` is unrelated and is
included here only for convenience.
`ring_commutator.commutator` -> `ring.lie_def`

### [2021-02-11 16:21:06](https://github.com/leanprover-community/mathlib/commit/abf72e6)
refactor(algebra/lie/*): rename `lie_algebra.morphism` --> `lie_hom`, `lie_algebra.equiv` --> `lie_equiv` ([#6179](https://github.com/leanprover-community/mathlib/pull/6179))
Also renaming the field `map_lie` to `map_lie'` in both `lie_algebra.morphism` and `lie_module_hom`
for consistency with the pattern elsewhere in Mathlib.

### [2021-02-11 16:21:04](https://github.com/leanprover-community/mathlib/commit/b3347e5)
doc(algebra/field): added module doc ([#6177](https://github.com/leanprover-community/mathlib/pull/6177))

### [2021-02-11 16:21:00](https://github.com/leanprover-community/mathlib/commit/af8b60b)
feat(algebra/lie/submodule): Lie submodules form a modular lattice ([#6176](https://github.com/leanprover-community/mathlib/pull/6176))

### [2021-02-11 16:20:58](https://github.com/leanprover-community/mathlib/commit/b9354dd)
feat(algebra/ordered_ring): a product is at least one if both factors are ([#6172](https://github.com/leanprover-community/mathlib/pull/6172))
Add single lemma one_le_mul_of_one_le_of_one_le
The lemma is stated for an `ordered_semiring`, but only multiplication is used.  There does not seem to be an `ordered_monoid` class where this lemma would fit.
Relevant Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/ordered_monoid.3F

### [2021-02-11 16:20:56](https://github.com/leanprover-community/mathlib/commit/194ec66)
feat(group_theory/subgroup): prove relation between pointwise product of submonoids/subgroups and their join ([#6165](https://github.com/leanprover-community/mathlib/pull/6165))
If `H` and `K` are subgroups/submonoids then `H ⊔ K = closure (H * K)`, where `H * K` is the pointwise set product. When `H` or `K` is a normal subgroup, it is proved that `(↑(H ⊔ K) : set G) = H * K`.
<!--
put comments you want to keep out of the PR commit here.
If this PR depends on other PRs, please list them below this comment,
using the following format:
- [ ] depends on: #abc [optional extra text]
- [ ] depends on: #xyz [optional extra text]
-->

### [2021-02-11 16:20:55](https://github.com/leanprover-community/mathlib/commit/f151da2)
feat(field_theory/polynomial_galois_group): Restriction from splitting field of composition ([#6148](https://github.com/leanprover-community/mathlib/pull/6148))
Defines the surjective restriction map from the splitting field of a composition

### [2021-02-11 16:20:52](https://github.com/leanprover-community/mathlib/commit/7b4a9e5)
feat(order/well_founded_set) : Define when a set is well-founded with `set.is_wf` ([#6113](https://github.com/leanprover-community/mathlib/pull/6113))
Defines a predicate for when a set within an ordered type is well-founded (`set.is_wf`)
Proves basic lemmas about well-founded sets

### [2021-02-11 16:20:48](https://github.com/leanprover-community/mathlib/commit/a557f8b)
feat(data/complex): order structure ([#4684](https://github.com/leanprover-community/mathlib/pull/4684))

### [2021-02-11 14:27:06](https://github.com/leanprover-community/mathlib/commit/39090c8)
doc(analysis/analytic/inverse): fix mathjax output ([#6175](https://github.com/leanprover-community/mathlib/pull/6175))
`\\` in source code is converted to `\` in the generated html file, so one should have `\\\\` to generate proper line break for mathjax.

### [2021-02-11 11:51:02](https://github.com/leanprover-community/mathlib/commit/58632ac)
feat(topology/order): discrete_topology_bot ([#6163](https://github.com/leanprover-community/mathlib/pull/6163))
From `lean-liquid`

### [2021-02-11 11:50:59](https://github.com/leanprover-community/mathlib/commit/fdace95)
feat(linear_algebra/matrix): generalize some `is_basis.to_matrix` results ([#6127](https://github.com/leanprover-community/mathlib/pull/6127))
This PR contains some changes to the lemmas involving `is_basis.to_matrix`, allowing the bases involved to differ in their index type. Although you can prove there exists an `equiv` between those types, it's easier to not have to transport along that equiv.
The PR also generalizes `linear_map.to_matrix_id` to a form with two different bases, `linear_map.to_matrix_id_eq_basis_to_matrix`. Marking the second as `simp` means the first can be proved automatically, hence the removal of `simp` on that one.

### [2021-02-11 09:21:58](https://github.com/leanprover-community/mathlib/commit/d405c5e)
chore(scripts): update nolints.txt ([#6169](https://github.com/leanprover-community/mathlib/pull/6169))
I am happy to remove some nolints for you!

### [2021-02-11 09:21:57](https://github.com/leanprover-community/mathlib/commit/59daf53)
refactor(topology/subset_properties.lean): split the subset_properties.lean file ([#6161](https://github.com/leanprover-community/mathlib/pull/6161))
split the file subset_properties.lean into another file called connected.lean which contains the properties that relate to connectivity. This is in preparation for a future PR proving properties about the quotient of a space by its connected components and it would add roughly 300 lines.

### [2021-02-11 09:21:55](https://github.com/leanprover-community/mathlib/commit/97a56e6)
refactor(algebra/lie/basic): split giant file into pieces ([#6141](https://github.com/leanprover-community/mathlib/pull/6141))

### [2021-02-11 06:02:45](https://github.com/leanprover-community/mathlib/commit/97f89af)
doc(algebra/euclidean_domain): module doc ([#6107](https://github.com/leanprover-community/mathlib/pull/6107))

### [2021-02-11 06:02:43](https://github.com/leanprover-community/mathlib/commit/906e03d)
chore(field_theory,ring_theory): reduce dependencies of `power_basis.lean` ([#6104](https://github.com/leanprover-community/mathlib/pull/6104))
I was having trouble with circular imports related to `power_basis.lean`, so I decided to reshuffle some definitions to make `power_basis.lean` have less dependencies. That way, something depending on `power_basis` doesn't also need to depend on `intermediate_field.adjoin`.
The following (main) declarations are moved:
 - `algebra.adjoin`: from `ring_theory/adjoin.lean` to `ring_theory/adjoin/basic.lean` (renamed file)
 - `algebra.adjoin.power_basis`: from `ring_theory/power_basis.lean` to `ring_theory/adjoin/power_basis.lean` (new file)
 - `adjoin_root.power_basis`: from `ring_theory/power_basis.lean` to `ring_theory/adjoin_root.lean`
 - `intermediate_field.adjoin.power_basis`: from `ring_theory/power_basis.lean` to `field_theory/adjoin.lean`
 - `is_scalar_tower.polynomial`: from `ring_theory/algebra_tower.lean` to `ring_theory/polynomial/tower.lean` (new file)
The following results are new:
 - `is_integral.linear_independent_pow` and `is_integral.mem_span_pow`: generalize `algebra.adjoin.linear_independent_power_basis` and `algebra.adjoin.mem_span_power_basis`.

### [2021-02-11 06:02:41](https://github.com/leanprover-community/mathlib/commit/330129d)
feat(data/finset/lattice): `inf` and `sup` on complete_linear_orders produce an element of the set ([#6103](https://github.com/leanprover-community/mathlib/pull/6103))

### [2021-02-11 06:02:39](https://github.com/leanprover-community/mathlib/commit/3959a8b)
perf(ring_theory/{noetherian,ideal/basic}): Simplify proofs of Krull's theorem and related theorems ([#6082](https://github.com/leanprover-community/mathlib/pull/6082))
Move `submodule.singleton_span_is_compact_element` and `submodule.is_compactly_generated` to more appropriate locations. Add trivial order isomorphisms and order-iso lemmas. Show that `is_atomic` and `is_coatomic` are respected by order isomorphisms. Greatly simplify `is_noetherian_iff_well_founded`. Provide an `is_coatomic` instance on the ideal lattice of a ring and simplify `ideal.exists_le_maximal`.

### [2021-02-11 00:37:06](https://github.com/leanprover-community/mathlib/commit/030107f)
feat(order/compactly_generated): A compactly-generated modular lattice is complemented iff atomistic ([#6071](https://github.com/leanprover-community/mathlib/pull/6071))
Shows that a compactly-generated modular lattice is complemented iff it is atomistic
Proves extra lemmas about atomistic or compactly-generated lattices
Proves extra lemmas about `complete_lattice.independent`
Fix the name of `is_modular_lattice.sup_inf_sup_assoc`

### [2021-02-11 00:37:04](https://github.com/leanprover-community/mathlib/commit/7fb7fb3)
feat(ring_theory/polynomial/chebyshev/dickson): Introduce generalised Dickson polynomials ([#5869](https://github.com/leanprover-community/mathlib/pull/5869))
and replace lambdashev with dickson 1 1.

### [2021-02-11 00:37:02](https://github.com/leanprover-community/mathlib/commit/c70feeb)
feat(analysis/analytic/inverse): convergence of the inverse of a power series ([#5854](https://github.com/leanprover-community/mathlib/pull/5854))
If a formal multilinear series has a positive radius of convergence, then its inverse also does.

### [2021-02-11 00:37:00](https://github.com/leanprover-community/mathlib/commit/19f24ce)
feat(algebra/subalgebra): Trivial subalgebra has trivial automorphism group ([#5672](https://github.com/leanprover-community/mathlib/pull/5672))
Adds a lemma stating that if top=bot in the subalgebra type then top=bot in the subgroup type.

### [2021-02-11 00:36:58](https://github.com/leanprover-community/mathlib/commit/983cb90)
feat(archive/imo): formalize 1987Q1 ([#4731](https://github.com/leanprover-community/mathlib/pull/4731))

### [2021-02-10 21:01:42](https://github.com/leanprover-community/mathlib/commit/13c9ed3)
refactor(data/finset/basic): simplify proof ([#6160](https://github.com/leanprover-community/mathlib/pull/6160))
... of `bUnion_filter_eq_of_maps_to`
looks nicer, slightly faster elaboration, 13% smaller proof term
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-02-10 21:01:40](https://github.com/leanprover-community/mathlib/commit/0bc7fc1)
refactor(ring_theory/perfection): faster proof of `coeff_frobenius` ([#6159](https://github.com/leanprover-community/mathlib/pull/6159))
4X smaller proof term, elaboration 800ms -> 50ms
Co-authors: `lean-gptf`, Stanislas Polu
Note: supplying `coeff_pow_p f n` also works but takes 500ms to
elaborate

### [2021-02-10 21:01:38](https://github.com/leanprover-community/mathlib/commit/6e52dfe)
feat(algebra/category/Group/adjunctions): adjunction of abelianization and forgetful functor ([#6154](https://github.com/leanprover-community/mathlib/pull/6154))
Abelianization has been defined in `group_theory/abelianization` without realising it in category theory. This PR adds this feature. Furthermore, a module doc for abelianization is added and the one for adjunctions is expanded.

### [2021-02-10 21:01:36](https://github.com/leanprover-community/mathlib/commit/bce1cb3)
feat(linear_algebra/matrix): lemmas for `reindex({_linear,_alg}_equiv)?` ([#6153](https://github.com/leanprover-community/mathlib/pull/6153))
This PR contains a couple of `simp` lemmas for `reindex` and its bundled equivs. Namely, it adds `reindex_refl` (reindexing along the identity map is the identity), and `reindex_apply` (the same as `coe_reindex`, but no `λ i j` on the RHS, which makes it more useful for `rw`'ing.) The previous `reindex_apply` is renamed `coe_reindex` for disambiguation.

### [2021-02-10 21:01:35](https://github.com/leanprover-community/mathlib/commit/eca4f38)
feat(data/int/basic): an integer of absolute value less than one is zero ([#6151](https://github.com/leanprover-community/mathlib/pull/6151))
lemma eq_zero_iff_abs_lt_one

### [2021-02-10 21:01:33](https://github.com/leanprover-community/mathlib/commit/14a1fd7)
feat(data/nat/basic): le_of_add_le_* ([#6145](https://github.com/leanprover-community/mathlib/pull/6145))

### [2021-02-10 21:01:31](https://github.com/leanprover-community/mathlib/commit/dbbac3b)
chore(algebra/module/pi): add missing smul_comm_class instances ([#6139](https://github.com/leanprover-community/mathlib/pull/6139))
There are three families of these for consistency with how we have three families of `is_scalar_tower` instances.

### [2021-02-10 21:01:30](https://github.com/leanprover-community/mathlib/commit/56fde49)
feat(data/polynomial/denoms_clearable): add lemma about clearing denominators in evaluating a polynomial ([#6122](https://github.com/leanprover-community/mathlib/pull/6122))
Evaluating a polynomial with integer coefficients at a rational number and clearing denominators, yields a number greater than or equal to one.  The target can be any `linear_ordered_field K`.
The assumption on `K` could be weakened to `linear_ordered_comm_ring` assuming that the
image of the denominator is invertible in `K`.
Reference: Liouville PR [#4301](https://github.com/leanprover-community/mathlib/pull/4301).

### [2021-02-10 21:01:28](https://github.com/leanprover-community/mathlib/commit/db0fa61)
feat(category_theory/differential_object): the shift functor ([#6111](https://github.com/leanprover-community/mathlib/pull/6111))
Requested by @jcommelin.

### [2021-02-10 17:50:05](https://github.com/leanprover-community/mathlib/commit/f0413da)
refactor(combinatorics/simple_graph/basic): change statement of mem_decidable to more general version ([#6157](https://github.com/leanprover-community/mathlib/pull/6157))
Change statement of `mem_decidable` to more general version.

### [2021-02-10 17:50:03](https://github.com/leanprover-community/mathlib/commit/83118da)
feat(data/nat/basic): prove an inequality of natural numbers ([#6155](https://github.com/leanprover-community/mathlib/pull/6155))
Add lemma mul_lt_mul_pow_succ, proving the inequality `n * q < a * q ^ (n + 1)`.
Reference: Liouville PR [#4301](https://github.com/leanprover-community/mathlib/pull/4301).

### [2021-02-10 17:50:01](https://github.com/leanprover-community/mathlib/commit/ca8e009)
feat(data/polynomial/ring_division): comp_eq_zero_iff ([#6147](https://github.com/leanprover-community/mathlib/pull/6147))
Condition for a composition of polynomials to be zero (assuming that the ring is an integral domain).

### [2021-02-10 17:49:59](https://github.com/leanprover-community/mathlib/commit/41530ae)
feat(field_theory/splitting_field): splits_of_nat_degree_le_one ([#6146](https://github.com/leanprover-community/mathlib/pull/6146))
Adds the analogs of `splits_of_degree_eq_one` and `splits_of_degree_le_one` for `nat_degree`

### [2021-02-10 17:49:57](https://github.com/leanprover-community/mathlib/commit/3fae96c)
feat(algebra/ordered_monoid): min_*_distrib ([#6144](https://github.com/leanprover-community/mathlib/pull/6144))
Also provide a `canonically_linear_ordered_add_monoid` instances for `nat`, `nnreal`, `cardinal` and `with_top`.

### [2021-02-10 17:49:55](https://github.com/leanprover-community/mathlib/commit/3cc398b)
feat(linear_algebra/prod): add an ext lemma that recurses into products ([#6124](https://github.com/leanprover-community/mathlib/pull/6124))
Combined with [#6105](https://github.com/leanprover-community/mathlib/pull/6105), this means that applying `ext` when faced with an equality between `A × (B ⊗[R] C) →ₗ[R] D`s now expands to two goals, the first taking `a : A` and the second taking `b : B` and `c : C`.
Again, this comes at the expense of sometimes needing to `simp [prod.mk_fst, linear_map.inr_apply]` after using `ext`, but those are all covered by `dsimp` anyway.

### [2021-02-10 15:17:41](https://github.com/leanprover-community/mathlib/commit/0854536)
feat(topology/constructions): add `map_fst_nhds` and `map_snd_nhds` ([#6142](https://github.com/leanprover-community/mathlib/pull/6142))
* Move the definition of `nhds_within` to `topology/basic`. The theory is still in `continuous_on`.
* Add `filter.map_inf_principal_preimage`.
* Add `map_fst_nhds_within`, `map_fst_nhds`, `map_snd_nhds_within`, and `map_snd_nhds`.

### [2021-02-10 15:17:39](https://github.com/leanprover-community/mathlib/commit/7fd4dcf)
feat(analysis/normed_space/operator_norm): bundle more arguments ([#6140](https://github.com/leanprover-community/mathlib/pull/6140))
* bundle the first argument of `continuous_linear_map.smul_rightL`;
* add `continuous_linear_map.flip` and `continuous_linear_map.flipₗᵢ`;
* use `flip` to redefine `apply`.

### [2021-02-10 15:17:37](https://github.com/leanprover-community/mathlib/commit/d5e2029)
refactor(linear_algebra/basic): extract definitions about pi types to a new file ([#6130](https://github.com/leanprover-community/mathlib/pull/6130))
This makes it consistent with how the `prod` definitions are in their own file.
With each in its own file, it should be easier to unify the APIs between them.
This does not do anything other than copy across the definitions.

### [2021-02-10 11:14:03](https://github.com/leanprover-community/mathlib/commit/7a51c0f)
refactor(data/set/intervals/basic): simpler proof of `Iio_union_Ioo'` ([#6132](https://github.com/leanprover-community/mathlib/pull/6132))
proof term 2577 -> 1587 chars
elaboration time 130ms -> 75ms
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-10 05:02:51](https://github.com/leanprover-community/mathlib/commit/5a2eac6)
refactor(order/closure): golf `closure_inter_le` ([#6138](https://github.com/leanprover-community/mathlib/pull/6138))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-10 03:37:24](https://github.com/leanprover-community/mathlib/commit/0731a70)
chore(scripts): update nolints.txt ([#6143](https://github.com/leanprover-community/mathlib/pull/6143))
I am happy to remove some nolints for you!

### [2021-02-10 00:03:36](https://github.com/leanprover-community/mathlib/commit/922ecb0)
chore(group_theory/perm/sign): speed up sign_aux_swap_zero_one proof ([#6128](https://github.com/leanprover-community/mathlib/pull/6128))

### [2021-02-10 00:03:34](https://github.com/leanprover-community/mathlib/commit/18b378d)
chore(data/fin): reorder file to group declarations ([#6109](https://github.com/leanprover-community/mathlib/pull/6109))
The `data/fin` file has a lot of definitions and lemmas. This reordering groups declarations and places ones that do not rely on `fin` operations first, like order. No definitions or lemma statements have been changed. A minimal amount of proofs have been rephrased. No reformatting of style has been done. Section titles have been added.
This is useful in preparation for redefining `fin` operations (lean[#527](https://github.com/leanprover-community/mathlib/pull/527)). Additionally, it allows for better organization for other refactors like making `pred` and `pred_above` total.

### [2021-02-10 00:03:32](https://github.com/leanprover-community/mathlib/commit/4c1c11c)
feat(data/equiv/mul_add): monoids/rings with one element are isomorphic ([#6079](https://github.com/leanprover-community/mathlib/pull/6079))
Monoids (resp. add_monoids, semirings) with one element are isomorphic.

### [2021-02-10 00:03:30](https://github.com/leanprover-community/mathlib/commit/b34da00)
feat(algebra/geom_sum): adds further variants ([#6077](https://github.com/leanprover-community/mathlib/pull/6077))
This adds further variants for the value of `geom_series\2`. Additionally, a docstring is provided.
Thanks to Patrick Massot for help with the reindexing of sums.

### [2021-02-10 00:03:28](https://github.com/leanprover-community/mathlib/commit/49e50ee)
feat(measure_theory/lp_space): add more API on Lp spaces ([#6042](https://github.com/leanprover-community/mathlib/pull/6042))
Flesh out the file on `L^p` spaces, notably adding facts on the composition with Lipschitz functions. This makes it possible to define in one go the positive part of an `L^p` function, and its image under a continuous linear map.
The file `ae_eq_fun.lean` is split into two, to solve a temporary issue: this file defines a global emetric space instance (of `L^1` type) on the space of function classes. This passes to subtypes, and clashes with the topology on `L^p` coming from the distance. This did not show up before as there were not enough topological statements on `L^p`, but I have been bitten by this when adding new results. For now, we move this part of `ae_eq_fun.lean` to another file which is not imported by `lp_space.lean`, to avoid the clash. This will be solved in a subsequent PR in which I will remove the global instance, and construct the integral based on the specialization of `L^p` to `p = 1` instead of the ad hoc construction we have now (note that, currently, we have two different `L^1` spaces in mathlib, denoted `Lp E 1 μ` and `α →₁[μ] E` -- I will remove the second one in a later PR).

### [2021-02-10 00:03:26](https://github.com/leanprover-community/mathlib/commit/7c77279)
feat(category_theory/monad): use bundled monads everywhere ([#5889](https://github.com/leanprover-community/mathlib/pull/5889))
This PR makes bundled monads the default (adapting definitions by @adamtopaz). The main motivation for this is that the category of algebras for a monad is currently not "hygienic" in that isomorphic monads don't have equivalent Eilenberg-Moore categories, but further that the notion of monad isomorphism is tricky to express, in particular this makes the definition of a monadic functor not preserved by isos either despite not explicitly having monads or algebras in the type.
We can now say:
```
@[simps]
def algebra_equiv_of_iso_monads {T₁ T₂ : monad C} (h : T₁ ≅ T₂) :
  algebra T₁ ≌ algebra T₂ :=
```
Other than this new data, virtually everything in this PR is just refactoring - in particular there's quite a bit of golfing and generalisation possible, but to keep the diff here minimal I'll do those in later PRs

### [2021-02-09 20:17:00](https://github.com/leanprover-community/mathlib/commit/ba9e06e)
refactor(algebra/lie/basic): rm extraneous rewrite hypothesis ([#6137](https://github.com/leanprover-community/mathlib/pull/6137))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 20:16:58](https://github.com/leanprover-community/mathlib/commit/456bdb7)
refactor(measure_theory/measure_space): simplify proof ([#6136](https://github.com/leanprover-community/mathlib/pull/6136))
2X smaller proof term
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 20:16:56](https://github.com/leanprover-community/mathlib/commit/c377e68)
refactor(ring_theory/polynomial/symmetric): simplify proof ([#6135](https://github.com/leanprover-community/mathlib/pull/6135))
... of `mv_polynomial.is_symmetric.sub`
2X smaller proof term
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 20:16:55](https://github.com/leanprover-community/mathlib/commit/eb2dcba)
refactor(*): remove uses of omega in the library ([#6129](https://github.com/leanprover-community/mathlib/pull/6129))
The transition to Lean 4 will be easier if we don't have to port omega.

### [2021-02-09 20:16:52](https://github.com/leanprover-community/mathlib/commit/296899e)
refactor(data/string/basic): simplify proof of `to_list_nonempty` ([#6117](https://github.com/leanprover-community/mathlib/pull/6117))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 20:16:49](https://github.com/leanprover-community/mathlib/commit/d9d56eb)
feat(analysis/special_functions/trigonometric): `complex.log` is smooth away from `(-∞, 0]` ([#6041](https://github.com/leanprover-community/mathlib/pull/6041))

### [2021-02-09 16:47:39](https://github.com/leanprover-community/mathlib/commit/e8f383c)
refactor(analysis/special_functions/trigonometric): simpler proof ([#6133](https://github.com/leanprover-community/mathlib/pull/6133))
... of `complex.tan_int_mul_pi`
3X faster elaboration, 2X smaller proof term
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 16:47:37](https://github.com/leanprover-community/mathlib/commit/bf1465c)
refactor(data/fintype/basic): golf `card_eq_one_of_forall_eq` ([#6131](https://github.com/leanprover-community/mathlib/pull/6131))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 16:47:34](https://github.com/leanprover-community/mathlib/commit/fdbd4bf)
feat(archive/imo): formalize solution to IMO 2013 problem Q1 ([#6110](https://github.com/leanprover-community/mathlib/pull/6110))

### [2021-02-09 14:41:24](https://github.com/leanprover-community/mathlib/commit/aa9e2b8)
feat(analysis/normed_space/operator_norm): lemmas about `E →L[𝕜] F →L[𝕜] G` ([#6102](https://github.com/leanprover-community/mathlib/pull/6102))

### [2021-02-09 14:41:22](https://github.com/leanprover-community/mathlib/commit/766146b)
fix(topology/algebra/infinite_sum): remove hard-coding of ℕ and ℝ ([#6096](https://github.com/leanprover-community/mathlib/pull/6096))
It may be possible to make these assumptions stricter, but they're weak enough to still cover the original use case.
Hopefully that can be handled by @alexjbest's upcoming linter to relax assumptions.

### [2021-02-09 11:14:56](https://github.com/leanprover-community/mathlib/commit/2d50cce)
refactor(geometry/euclidean): shorten proof ([#6121](https://github.com/leanprover-community/mathlib/pull/6121))
... of `eq_reflection_of_eq_subspace`
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 11:14:54](https://github.com/leanprover-community/mathlib/commit/aaab113)
refactor(linear_algebra/prod): split out prod and coprod defs and lemmas  ([#6059](https://github.com/leanprover-community/mathlib/pull/6059))
Lemmas are moved without modification.
I expect this will take a few builds of adding missing imports.

### [2021-02-09 11:14:52](https://github.com/leanprover-community/mathlib/commit/17448c6)
feat(group_theory/perm/sign): induced permutation on a subtype that is a fintype ([#5706](https://github.com/leanprover-community/mathlib/pull/5706))
If a permutation on a type maps a subtype into itself and the subtype is a fintype, then we get a permutation on the subtype. Similar to the subtype_perm definition in the same file.

### [2021-02-09 07:26:19](https://github.com/leanprover-community/mathlib/commit/342bccf)
refactor(group_theory/solvable): `simp` -> assumption ([#6120](https://github.com/leanprover-community/mathlib/pull/6120))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 07:26:17](https://github.com/leanprover-community/mathlib/commit/ec8f2ac)
refactor(data/ordmap/ordset): simpler proof of `not_le_delta` ([#6119](https://github.com/leanprover-community/mathlib/pull/6119))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 07:26:15](https://github.com/leanprover-community/mathlib/commit/7e5ff2f)
refactor(computability/partrec): simpler proof of `subtype_mk` ([#6118](https://github.com/leanprover-community/mathlib/pull/6118))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 07:26:13](https://github.com/leanprover-community/mathlib/commit/183f4fc)
refactor(category_theory/adjunction/mates): faster proof ([#6116](https://github.com/leanprover-community/mathlib/pull/6116))
Co-authors: `lean-gptf`, Stanislas Polu
elaboration 750ms -> 350ms
5X smaller proof term
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 07:26:11](https://github.com/leanprover-community/mathlib/commit/1611b30)
refactor(combinatorics/simple_graph): simplify proofs ([#6115](https://github.com/leanprover-community/mathlib/pull/6115))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 07:26:10](https://github.com/leanprover-community/mathlib/commit/d06b11a)
refactor(algebra/lie/basic): golf `lie_algebra.morphism.map_bot_iff` ([#6114](https://github.com/leanprover-community/mathlib/pull/6114))
Co-authors: `lean-gptf`, Stanislas Polu
This was found by `formal-lean-wm-to-tt-m1-m2-v4-c4` when we evaluated it on theorems added to `mathlib` after we last extracted training data.

### [2021-02-09 07:26:06](https://github.com/leanprover-community/mathlib/commit/6b65c37)
refactor(linear_algebra/tensor_product): Use a more powerful lemma for ext ([#6105](https://github.com/leanprover-community/mathlib/pull/6105))
This means that the `ext` tactic can recurse into both the left and the right of the tensor product.
The downside is that `compr₂_apply, mk_apply` needs to be added to some `simp only`s.
Notably this makes `ext` able to prove `tensor_product.ext_fourfold` (which is still needed to cut down elaboration time for the `pentagon` proof), and enables `ext` to be used on things like tensor products of a tensor_algebra and a free_algebra.

### [2021-02-09 07:26:04](https://github.com/leanprover-community/mathlib/commit/7b1945e)
feat(logic/basic): dite_eq_ite ([#6095](https://github.com/leanprover-community/mathlib/pull/6095))
Simplify `dite` to `ite` when possible.

### [2021-02-09 05:58:46](https://github.com/leanprover-community/mathlib/commit/8fd8636)
feat(field_theory/minpoly): add `minpoly.nat_degree_pos` ([#6100](https://github.com/leanprover-community/mathlib/pull/6100))
I needed this lemma and noticed that `minpoly.lean` actually uses this result more than `minpoly.degree_pos` (including in the proof of `degree_pos` itself). So I took the opportunity to golf a couple of proofs.

### [2021-02-09 03:30:54](https://github.com/leanprover-community/mathlib/commit/69bf484)
chore(scripts): update nolints.txt ([#6112](https://github.com/leanprover-community/mathlib/pull/6112))
I am happy to remove some nolints for you!

### [2021-02-09 00:54:24](https://github.com/leanprover-community/mathlib/commit/117e729)
chore(linear_algebra/basic, analysis/normed_space/operator_norm): bundle another argument into the homs ([#5899](https://github.com/leanprover-community/mathlib/pull/5899))

### [2021-02-08 21:41:41](https://github.com/leanprover-community/mathlib/commit/7f11d72)
feat(analysis/normed_space): `continuous_linear_map.prod` as a `linear_isometry_equiv` ([#6099](https://github.com/leanprover-community/mathlib/pull/6099))
* add lemma `continuous_linear_map.op_norm_prod`;
* add `continuous_linear_map.prodₗ` and `continuous_linear_map.prodₗᵢ`;
* add `prod.topological_semimodule`;
* drop unused `is_bounded_linear_map_prod_iso`.

### [2021-02-08 21:41:39](https://github.com/leanprover-community/mathlib/commit/03074b1)
doc(algebra/{field_power, punit_instances}): module docs ([#6097](https://github.com/leanprover-community/mathlib/pull/6097))
Additionally `ordered_field` is aligned with the style guidelines.

### [2021-02-08 19:30:23](https://github.com/leanprover-community/mathlib/commit/d62d793)
feat(differential_object/iso_app): extract the isomorphism of underlying objects ([#6083](https://github.com/leanprover-community/mathlib/pull/6083))
From `lean-liquid`.

### [2021-02-08 19:30:20](https://github.com/leanprover-community/mathlib/commit/0c6fa28)
feat(linear_algebra/basis): if `(p : submodule K V) < ⊤`, then there exists `f : V →ₗ[K] K`, `p ≤ ker f` ([#6074](https://github.com/leanprover-community/mathlib/pull/6074))

### [2021-02-08 19:30:18](https://github.com/leanprover-community/mathlib/commit/4e9fbb9)
feat(measure_theory/probability_mass_function): Add definitions for filtering pmfs on a predicate ([#6033](https://github.com/leanprover-community/mathlib/pull/6033))

### [2021-02-08 19:30:16](https://github.com/leanprover-community/mathlib/commit/f6504f1)
feat(computability/DFA): the pumping lemma ([#5925](https://github.com/leanprover-community/mathlib/pull/5925))

### [2021-02-08 16:17:44](https://github.com/leanprover-community/mathlib/commit/1d49f87)
chore(data/finset): golf some proofs ([#6101](https://github.com/leanprover-community/mathlib/pull/6101))
* prove that `finset.min'` and `finset.max'` are `is_least` and
  `is_greatest` elements of the corresponding sets;
* use this fact to golf some proofs;
  generalize `min'_lt_max'` to `is_glb_lt_is_lub_of_ne`;
* add `finset.card_le_one` and `finset.one_lt_card`.

### [2021-02-08 16:17:43](https://github.com/leanprover-community/mathlib/commit/1a0f84c)
feat(linear_algebra/basic): bundle prod and coprod into linear_equivs ([#5992](https://github.com/leanprover-community/mathlib/pull/5992))
In order to do this, this has to reorder some definitions to make the semimodule structure on linear maps available earlier.

### [2021-02-08 14:15:50](https://github.com/leanprover-community/mathlib/commit/8a23aa3)
feat(topology/instances/{nnreal,ennreal}): add tendsto_cofinite_zero_of_summable ([#6093](https://github.com/leanprover-community/mathlib/pull/6093))
For `f : a -> nnreal`, `summable f` implies `tendsto f cofinite (nhds 0)`.
For `f : a -> ennreal`, `tsum f < \top` implies `tendsto f cofinite (nhds 0)`.
Add versions of these lemmas with `at_top` instead of `cofinite` when `a = N`.
Also add `ennreal.tendsto_at_top_zero`, a simpler statement for a particular case of `ennreal.tendsto_at_top`.

### [2021-02-08 14:15:49](https://github.com/leanprover-community/mathlib/commit/8e3e79a)
feat(category_theory/pi): extract components of isomorphisms of indexed objects ([#6086](https://github.com/leanprover-community/mathlib/pull/6086))
From `lean-liquid`.

### [2021-02-08 14:15:47](https://github.com/leanprover-community/mathlib/commit/f075a69)
feat(category_theory/differential_object): lifting a functor ([#6084](https://github.com/leanprover-community/mathlib/pull/6084))
From `lean-liquid`.

### [2021-02-08 14:15:44](https://github.com/leanprover-community/mathlib/commit/6561639)
feat(topology/local_extr): not locally surjective at a local extr ([#6076](https://github.com/leanprover-community/mathlib/pull/6076))

### [2021-02-08 14:15:42](https://github.com/leanprover-community/mathlib/commit/054b467)
feat(analysis/calculus): derivatives of `f : E → Π i, F i` ([#6075](https://github.com/leanprover-community/mathlib/pull/6075))

### [2021-02-08 14:15:40](https://github.com/leanprover-community/mathlib/commit/dc48a84)
feat(linear_algebra/pi_tensor_product): add reindex and pempty_equiv ([#6069](https://github.com/leanprover-community/mathlib/pull/6069))

### [2021-02-08 10:21:58](https://github.com/leanprover-community/mathlib/commit/d7a4f72)
feat(norm_cast): dite_cast to match ite_cast ([#6092](https://github.com/leanprover-community/mathlib/pull/6092))
There's already an `ite_cast` lemma, for pushing a cast inside an `ite`. This adds the analogous `dite_cast`.

### [2021-02-08 10:21:56](https://github.com/leanprover-community/mathlib/commit/b338240)
feat(topology/constructions): a finite product of discrete spaces is discrete ([#6088](https://github.com/leanprover-community/mathlib/pull/6088))
From `lean-liquid`.

### [2021-02-08 10:21:55](https://github.com/leanprover-community/mathlib/commit/e4369fe)
chore(algebra/module/prod): add missing instances ([#6055](https://github.com/leanprover-community/mathlib/pull/6055))
This adds the following instances for `prod`:
* `is_scalar_tower`
* `smul_comm_class`
* `mul_action`
* `distrib_mul_action`
It also renames the type variables to match the usual convention for modules

### [2021-02-08 08:08:37](https://github.com/leanprover-community/mathlib/commit/90702a0)
feat(topology/continuous_map): missing coe_mk lemma ([#6087](https://github.com/leanprover-community/mathlib/pull/6087))

### [2021-02-08 05:08:19](https://github.com/leanprover-community/mathlib/commit/a6fc6bd)
feat(finset/lattice): max'_insert ([#6089](https://github.com/leanprover-community/mathlib/pull/6089))
From `lean-liquid`.

### [2021-02-08 02:16:50](https://github.com/leanprover-community/mathlib/commit/6b83e72)
chore(scripts): update nolints.txt ([#6090](https://github.com/leanprover-community/mathlib/pull/6090))
I am happy to remove some nolints for you!

### [2021-02-08 02:16:48](https://github.com/leanprover-community/mathlib/commit/5bf92e1)
chore(analysis/calculus/local_extr): review ([#6085](https://github.com/leanprover-community/mathlib/pull/6085))
* golf 2 proofs;
* don't use explicit section `variables`;
* add 2 docstrings.

### [2021-02-07 23:41:53](https://github.com/leanprover-community/mathlib/commit/45f9544)
feat(topology/separation): an injective map on a compact space is an embedding ([#6057](https://github.com/leanprover-community/mathlib/pull/6057))

### [2021-02-07 23:41:49](https://github.com/leanprover-community/mathlib/commit/9411b00)
feat(algebra/lie/basic): define the center of a Lie algebra and prove some related results ([#6013](https://github.com/leanprover-community/mathlib/pull/6013))

### [2021-02-07 23:41:48](https://github.com/leanprover-community/mathlib/commit/d989ff4)
feat(measure_theory/lebesgue_measure): integral as volume between graphs ([#5932](https://github.com/leanprover-community/mathlib/pull/5932))
I show that the integral can compute the volume between two real-valued functions. I start with the definition `region_between`, I prove that the region between two functions is a `measurable_set`, and then I prove two integral theorems. 
Help from @hrmacbeth and @benjamindavidson.

### [2021-02-07 21:13:03](https://github.com/leanprover-community/mathlib/commit/f3b0295)
chore(measure_theory): use `∞` notation for `(⊤ : ℝ≥0∞)` ([#6080](https://github.com/leanprover-community/mathlib/pull/6080))

### [2021-02-07 21:13:00](https://github.com/leanprover-community/mathlib/commit/5d4d815)
feat(analysis): prove that a polynomial function is equivalent to its leading term along at_top, and consequences ([#5354](https://github.com/leanprover-community/mathlib/pull/5354))
The main result is `eval_is_equivalent_at_top_eval_lead`, which states that for
any polynomial `P` of degree `n` with leading coeff `a`, the corresponding polynomial
function is equivalent to `a * x^n` as `x` goes to +∞.
We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coeffs of the considered polynomials.

### [2021-02-07 19:35:43](https://github.com/leanprover-community/mathlib/commit/99fe12a)
refactor(measure_theory/ae_eq_fun): move emetric to `ae_eq_fun_metric` ([#6081](https://github.com/leanprover-community/mathlib/pull/6081))
Cherry-picked from [#6042](https://github.com/leanprover-community/mathlib/pull/6042)

### [2021-02-07 19:35:41](https://github.com/leanprover-community/mathlib/commit/5a25827)
chore(measure_theory/measure_space): move definition of `measure.ae` up ([#6051](https://github.com/leanprover-community/mathlib/pull/6051))

### [2021-02-07 19:35:39](https://github.com/leanprover-community/mathlib/commit/132b0fe)
fix(scripts): make lint-style.* work on macos and windows ([#6047](https://github.com/leanprover-community/mathlib/pull/6047))
Make lint-style.sh use a POSIX-portable way of checking for executable bits, and make it always open files as UTF-8.
Also makes CI run the sanity checks across all 3 OSes to ensure this stays working.

### [2021-02-07 15:56:24](https://github.com/leanprover-community/mathlib/commit/288cc2e)
feat(logic/function/basic): add lemma stating that dite of two injective functions is injective if images are disjoint ([#5866](https://github.com/leanprover-community/mathlib/pull/5866))
Add lemma stating that dite of two injective functions is injective if their images are disjoint. Part of [#5695](https://github.com/leanprover-community/mathlib/pull/5695) in order to prove Hall's Marriage Theorem.

### [2021-02-07 13:33:58](https://github.com/leanprover-community/mathlib/commit/c25dad9)
refactor(analysis/calculus/mean_value): use `is_R_or_C` in more lemmas ([#6022](https://github.com/leanprover-community/mathlib/pull/6022))
* use `is_R_or_C` in `convex.norm_image_sub_le*` lemmas;
* replace `strict_fderiv_of_cont_diff` with
  `has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at` and
  `has_strict_deriv_at_of_has_deriv_at_of_continuous_at`, slightly change assumptions;
* add `has_ftaylor_series_up_to_on.has_fderiv_at`,
  `has_ftaylor_series_up_to_on.eventually_has_fderiv_at`,
  `has_ftaylor_series_up_to_on.differentiable_at`;
* add `times_cont_diff_at.has_strict_deriv_at` and
  `times_cont_diff_at.has_strict_deriv_at'`;
* prove that `complex.exp` is strictly differentiable and is an open map;
* add `simp` lemma `interior_mem_nhds`.

### [2021-02-07 06:54:51](https://github.com/leanprover-community/mathlib/commit/8b1f323)
feat(ring_theory/polynomial): Almost Vieta's formula on products of (X + r) ([#5696](https://github.com/leanprover-community/mathlib/pull/5696))
The main result is `prod_X_add_C_eq_sum_esymm`, which proves that a product of linear terms is equal to a linear combination of symmetric polynomials. Evaluating the variables of the symmetric polynomials gives Vieta's Formula.

### [2021-02-07 04:02:36](https://github.com/leanprover-community/mathlib/commit/4b035fc)
refactor(analysis/normed_space): upgrade `linear_map.to_continuous_linear_map` to `linear_equiv` ([#6072](https://github.com/leanprover-community/mathlib/pull/6072))
This way Lean will simplify, e.g., `f.to_continuous_linear_map = 0` to
`f = 0`.

### [2021-02-07 02:14:17](https://github.com/leanprover-community/mathlib/commit/736929e)
chore(scripts): update nolints.txt ([#6073](https://github.com/leanprover-community/mathlib/pull/6073))
I am happy to remove some nolints for you!

### [2021-02-06 22:54:57](https://github.com/leanprover-community/mathlib/commit/7f467fa)
feat(algebra/group/hom): add inv_comp and comp_inv ([#6046](https://github.com/leanprover-community/mathlib/pull/6046))
Two missing lemmas. Used in the Liquid Tensor Experiment.
Inversion for monoid hom is (correctly) only defined when the target is a comm_group; this explains the choice of typeclasses. I follow `inv_apply` and use `{}` rather than `[]`, but this is certainly not my area of expertise.

### [2021-02-06 22:54:56](https://github.com/leanprover-community/mathlib/commit/7c53a16)
feat(algebra/ordered_ring): add lemma ([#6031](https://github.com/leanprover-community/mathlib/pull/6031))
Add a lemma in algebra.ordered_ring proving the inequality `a + (2 + b) ≤ a * (2 + b)`.
This is again part of the Liouville PR.

### [2021-02-06 21:31:25](https://github.com/leanprover-community/mathlib/commit/7ec4fcc)
feat(category_theory): connected components of a category ([#5425](https://github.com/leanprover-community/mathlib/pull/5425))

### [2021-02-06 20:09:52](https://github.com/leanprover-community/mathlib/commit/a1ebf54)
refactor(data/buffer/parser/basic): make valid a class and rename to mono ([#6015](https://github.com/leanprover-community/mathlib/pull/6015))

### [2021-02-06 15:06:18](https://github.com/leanprover-community/mathlib/commit/dbf038d)
feat(topology/category): constructor for compact hausdorff spaces ([#6068](https://github.com/leanprover-community/mathlib/pull/6068))
`CompHaus.of` constructor. From the lean-liquid project.

### [2021-02-06 12:13:41](https://github.com/leanprover-community/mathlib/commit/767e6ae)
refactor(topology): make two definitions irreducible from the start ([#6060](https://github.com/leanprover-community/mathlib/pull/6060))

### [2021-02-06 08:37:26](https://github.com/leanprover-community/mathlib/commit/2bdeda9)
doc(number_theory/*): provide docstrings for basic and dioph ([#6063](https://github.com/leanprover-community/mathlib/pull/6063))
The main purpose of this PR is to provide docstrings for the two remaining files without docstring in number_theory, basic and dioph. Furthermore, lines are split in other files, so that there should be no number_theory entries in the style_exceptions file.

### [2021-02-06 05:00:08](https://github.com/leanprover-community/mathlib/commit/d951b2b)
feat(data/nat): division of powers ([#6067](https://github.com/leanprover-community/mathlib/pull/6067))
A small missing lemma.

### [2021-02-06 01:48:21](https://github.com/leanprover-community/mathlib/commit/b8a6f81)
chore(scripts): update nolints.txt ([#6066](https://github.com/leanprover-community/mathlib/pull/6066))
I am happy to remove some nolints for you!

### [2021-02-06 01:48:19](https://github.com/leanprover-community/mathlib/commit/b6b90e2)
fix(ring_theory/power_series/basic): fix algebra arguments ([#6065](https://github.com/leanprover-community/mathlib/pull/6065))
`power_series` is just an alias for `mv_power_series` over `unit`, yet it did not correctly inherit the algebra instance

### [2021-02-06 01:48:17](https://github.com/leanprover-community/mathlib/commit/94033d8)
feat(data/list/basic): simp iffs about *fix nil ([#6064](https://github.com/leanprover-community/mathlib/pull/6064))

### [2021-02-05 22:20:21](https://github.com/leanprover-community/mathlib/commit/0926e67)
feat(algebra/star): star_ordered_ring ([#4685](https://github.com/leanprover-community/mathlib/pull/4685))

### [2021-02-05 15:46:37](https://github.com/leanprover-community/mathlib/commit/bd38c5f)
chore(linear_algebra): move `is_basis_std_basis` to `std_basis.lean` ([#6054](https://github.com/leanprover-community/mathlib/pull/6054))
This is a follow-up to [#6020](https://github.com/leanprover-community/mathlib/pull/6020) which moved `std_basis` to a new file: now move results from `basis.lean` to that same file.
CC @eric-wieser

### [2021-02-05 15:46:35](https://github.com/leanprover-community/mathlib/commit/b5c23ce)
feat(data/nat/factorial): non-strict inequality on factorial ([#6052](https://github.com/leanprover-community/mathlib/pull/6052))
Add lemmas add_factorial_le_factorial_add and  add_factorial_le_factorial_add'.  These are still used in the Liouville PR.
I should have added them to the previous PR on factorials, but they got lost on the way!

### [2021-02-05 15:46:33](https://github.com/leanprover-community/mathlib/commit/1ab7cf6)
feat(algebra/ordered_ring): proof that `a + b ≤ a * b` ([#6043](https://github.com/leanprover-community/mathlib/pull/6043))
This is Johan's proof of the fact above.  If you are curious about the assumptions, there is an extensive discussion on
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/canonically_ordered.20pathology

### [2021-02-05 15:46:31](https://github.com/leanprover-community/mathlib/commit/fa9bf62)
feat(algebra/char_zero): add char_zero lemma for ordered_semirings ([#6038](https://github.com/leanprover-community/mathlib/pull/6038))
Relevant Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members

### [2021-02-05 15:46:28](https://github.com/leanprover-community/mathlib/commit/c2c686e)
feat(linear_algebra/multilinear): add more `curry` equivs ([#6012](https://github.com/leanprover-community/mathlib/pull/6012))
* `multilinear_map (λ i : ι ⊕ ι', E) F` is equivalent to
  `multilinear_map (λ i : ι, E) (multilinear_map (λ i : ι', E) F)`;
* given `s : finset (fin n)`, `s.card = k`, and `sᶜ.card = l`,
  `multilinear_map (λ i : fin n, E) F` is equivalent to
  `multilinear_map (λ i : fin k, E) (multilinear_map (λ i : fin l, E) F)`.

### [2021-02-05 15:46:26](https://github.com/leanprover-community/mathlib/commit/dc98547)
feat(linear_algebra/projection): Extending maps from complement submodules to the entire module ([#5981](https://github.com/leanprover-community/mathlib/pull/5981))
Given two linear maps from complement submodules, `of_is_comp` is the linear map extended to the entire module. 
This is useful whenever we would like to extend a linear map from a submodule to a map on the entire module.

### [2021-02-05 12:11:35](https://github.com/leanprover-community/mathlib/commit/34e366c)
refactor(*): remove uses of @[class] def  ([#6028](https://github.com/leanprover-community/mathlib/pull/6028))
Preparation for lean 4, which does not support this idiom.

### [2021-02-05 12:11:33](https://github.com/leanprover-community/mathlib/commit/c6c7eaf)
refactor(topology/algebra/module,analysis/*): merge some `smul` lemmas and defs ([#5987](https://github.com/leanprover-community/mathlib/pull/5987))
Generalize some definitions and lemmas about `smul`  and `f : E →L[k] F` so that now they allow scalars from an algebra over `k`. This way we can get rid of `smul_algebra` definitions and lemmas.
In particular, now `continuous_linear_map.smul_right` accepts functions with values in an algebra over `k`, so `smul_right 1 f` now needs a type annotation on `1`.

### [2021-02-05 12:11:32](https://github.com/leanprover-community/mathlib/commit/392ebec)
chore(algebra/algebra/basic): show that the ℚ-algebra structure is unique ([#5980](https://github.com/leanprover-community/mathlib/pull/5980))
Note that we already have similar lemmas showing that ℕ and ℤ modules are unique.
The name is based on `rat.algebra_rat`, which provides a canonical instance.

### [2021-02-05 12:11:29](https://github.com/leanprover-community/mathlib/commit/915bff4)
feat(field_theory/polynomial_galois_group): Restriction is surjective ([#5961](https://github.com/leanprover-community/mathlib/pull/5961))
Proves surjectivity of `restrict` and `restrict_dvd`.

### [2021-02-05 12:11:27](https://github.com/leanprover-community/mathlib/commit/e1db909)
feat(order/filter): add lattice instance to order.ideal ([#5937](https://github.com/leanprover-community/mathlib/pull/5937))
Add lattice instance to `order.ideal P` when the preorder `P` is
actually a `semilattice_sup_bot` (that is, when `P` is a partial
order with all finite suprema).

### [2021-02-05 12:11:25](https://github.com/leanprover-community/mathlib/commit/70269f3)
feat(order/*): introduces complemented lattices ([#5747](https://github.com/leanprover-community/mathlib/pull/5747))
Defines `is_complemented` on bounded lattices
Proves facts about complemented modular lattices
Provides two instances of `is_complemented` on submodule lattices

### [2021-02-05 08:47:31](https://github.com/leanprover-community/mathlib/commit/5391433)
feat(algebra/group_power/basic): `pow_add_pow_le` ([#6037](https://github.com/leanprover-community/mathlib/pull/6037))
For natural `n ≠ 0` and nonnegative `x, y` in an `ordered_semiring`, `x ^ n + y ^ n ≤ (x + y) ^ n`.

### [2021-02-05 04:22:35](https://github.com/leanprover-community/mathlib/commit/5cb2865)
chore(scripts): update nolints.txt ([#6049](https://github.com/leanprover-community/mathlib/pull/6049))
I am happy to remove some nolints for you!

### [2021-02-05 00:51:27](https://github.com/leanprover-community/mathlib/commit/80c7ac1)
feat(algebra/big_operators/order): add fintype.sum_mono and fintype.sum_strict_mono ([#6040](https://github.com/leanprover-community/mathlib/pull/6040))

### [2021-02-05 00:51:25](https://github.com/leanprover-community/mathlib/commit/a101788)
fix(tactic/congr): fix trivial congr/convert ([#6011](https://github.com/leanprover-community/mathlib/pull/6011))
Now `convert` will prove reflexivity goals even at the top level, before
applying any congruence rules. Under the interpretation of the depth
argument as the number of nested congruence rules applied, we allow
proofs by assumption or reflexivity to work even at depth 0.
Also fixes a bug where
```lean
example {α} (a b : α) : a = b := by congr'
```
would succeed, because `apply proof_irrel` will unify the universe
metavariable in the type of `α` to `Prop`, causing surprising behavior.

### [2021-02-05 00:51:23](https://github.com/leanprover-community/mathlib/commit/59cfa02)
chore(data/quot): rename `lift_on_beta` to `lift_on_mk` ([#5921](https://github.com/leanprover-community/mathlib/pull/5921))
This also renames some other `lift_*_beta` lemmas to match their statement.
The [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/quotient.20.22on_beta.22.20vs.20.22on_mk.22) was unanimously in favor of this rename.

### [2021-02-04 21:33:38](https://github.com/leanprover-community/mathlib/commit/b9e559b)
feat(data/real/ennreal): use notation for ennreal ([#6044](https://github.com/leanprover-community/mathlib/pull/6044))
The notation for `ennreal` is `ℝ≥0∞` and it is localized to `ennreal` (though I guess it doesn't have to be?).
Zulip: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Notation.20for.20ennreal

### [2021-02-04 21:33:36](https://github.com/leanprover-community/mathlib/commit/7734d38)
refactor(data/real/basic): make ℝ a structure ([#6024](https://github.com/leanprover-community/mathlib/pull/6024))
Preparation for :four_leaf_clover:, which doesn't have irreducible.

### [2021-02-04 21:33:34](https://github.com/leanprover-community/mathlib/commit/d293822)
feat(topology/algebra/infinite_sum, topology/instances/ennreal): extend tsum API ([#6017](https://github.com/leanprover-community/mathlib/pull/6017))
Lemma `tsum_lt_of_nonneg` shows that if a sequence `f` with non-negative terms is dominated by a sequence `g` with summable series and at least one term of `f` is strictly smaller than the corresponding term in `g`, then the series of `f` is strictly smaller than the series of `g`.
Besides this lemma, I also added the relevant API in topology.algebra.infinite_sum.

### [2021-02-04 21:33:32](https://github.com/leanprover-community/mathlib/commit/1ee00c8)
feat(number_theory/bernoulli): Results regarding Bernoulli numbers as a generating function ([#5957](https://github.com/leanprover-community/mathlib/pull/5957))
We prove that the Bernoulli numbers are generating functions for t/(e^t - 1). Most of the results are proved by @kbuzzard.

### [2021-02-04 18:03:59](https://github.com/leanprover-community/mathlib/commit/49cf0be)
refactor(real): protect real.pi ([#6039](https://github.com/leanprover-community/mathlib/pull/6039))
Currently, `real.pi` is not protected. This can conflict with `set.pi`. Since it is most often used as `π` through the `real` locale, let's protect it.

### [2021-02-04 18:03:58](https://github.com/leanprover-community/mathlib/commit/1a7fb7e)
feat(data/list/sort): add sorted.rel_of_mem_take_of_mem_drop ([#6027](https://github.com/leanprover-community/mathlib/pull/6027))
Also renames the existing lemmas to enable dot notation

### [2021-02-04 18:03:56](https://github.com/leanprover-community/mathlib/commit/b98b5f6)
chore(data/dfinsupp): add simp lemmas about sum_add_hom, remove commutativity requirement ([#5939](https://github.com/leanprover-community/mathlib/pull/5939))
Note that `dfinsupp.sum_add_hom` and `dfinsupp.sum` are not defeq, so its valuable to repeat these lemmas.
The former is often easier to work with because there are no decidability requirements to juggle on equality with zero.
`dfinsupp.single_eq_of_sigma_eq` was a handy lemma for constructing a term-mode proof of `dfinsupp.single` equality.
A lot of the lemmas about `lift_add_hom` have to be repeated for `sum_add_hom` because the former simplifies to the latter before its lemmas get a chance to apply. At least the proofs can be reused.

### [2021-02-04 18:03:54](https://github.com/leanprover-community/mathlib/commit/6d153f1)
feat(data/equiv/basic): perm.subtype_congr ([#5875](https://github.com/leanprover-community/mathlib/pull/5875))

### [2021-02-04 18:03:51](https://github.com/leanprover-community/mathlib/commit/bbf9774)
feat(data/fintype/basic): inv of inj on deceq ([#5872](https://github.com/leanprover-community/mathlib/pull/5872))

### [2021-02-04 18:03:49](https://github.com/leanprover-community/mathlib/commit/9993a50)
feat(tactic/norm_swap): simplify numeral swaps ([#5637](https://github.com/leanprover-community/mathlib/pull/5637))
Explicitly applied swap equalities over `nat` can be proven to be true using `dec_trivial`. However, if occurring in the middle of a larger expression, a separate specialized hypothesis would be necessary to reduce them down. This is an initial attempt at a `norm_num` extension which seeks to reduce down expressions of the `swap X Y Z` form. Handles `nat`, `int`, `rat`, and `fin` swaps.

### [2021-02-04 14:28:12](https://github.com/leanprover-community/mathlib/commit/4d26028)
chore(order/basic): add a lemma expanding `le` on pi types ([#6023](https://github.com/leanprover-community/mathlib/pull/6023))

### [2021-02-04 14:28:10](https://github.com/leanprover-community/mathlib/commit/e61db52)
chore(linear_algebra/quadratic_form): add polar_self, polar_zero_left, and polar_zero_right simp lemmas ([#6003](https://github.com/leanprover-community/mathlib/pull/6003))
This also reorders the existing lemmas to keep the polar ones separate from the non-polar ones

### [2021-02-04 12:05:37](https://github.com/leanprover-community/mathlib/commit/1a2eb0b)
feat(analysis/special_functions/trigonometric): add mistakenly omitted lemma ([#6036](https://github.com/leanprover-community/mathlib/pull/6036))

### [2021-02-04 12:05:35](https://github.com/leanprover-community/mathlib/commit/16be8e3)
refactor(analysis/normed_space): simpler proof of `norm_sub_pow_two` ([#6035](https://github.com/leanprover-community/mathlib/pull/6035))
Co-authors: `lean-gptf`, Stanislas Polu

### [2021-02-04 12:05:34](https://github.com/leanprover-community/mathlib/commit/894ff7a)
doc(number_theory/{pell, sum_of_four_squares}): docstring to pell  ([#6030](https://github.com/leanprover-community/mathlib/pull/6030))
and additionally fixing the syntax for the docstring of sum_of_four_squares.

### [2021-02-04 12:05:32](https://github.com/leanprover-community/mathlib/commit/0aed8b1)
refactor(analysis/asymptotics): make definitions immediately irreducible ([#6021](https://github.com/leanprover-community/mathlib/pull/6021))

### [2021-02-04 12:05:30](https://github.com/leanprover-community/mathlib/commit/97781b9)
chore(linear_algebra/std_basis): move std_basis to a new file ([#6020](https://github.com/leanprover-community/mathlib/pull/6020))
linear_algebra/basic is _very_ long. This reduces its length by about 5%.
Authorship of the std_basis stuff seems to come almost entirely from 10a586b1d82098af32e13c8d8448696022132f17.
None of the lemmas have changed, and the variables are kept in exactly the same order as before.

### [2021-02-04 07:48:51](https://github.com/leanprover-community/mathlib/commit/6df1501)
feat(algebra/ordered_ring): weaken hypotheses for one_le_two ([#6034](https://github.com/leanprover-community/mathlib/pull/6034))
Adjust `one_le_two` to not require nontriviality.

### [2021-02-04 03:30:09](https://github.com/leanprover-community/mathlib/commit/3309490)
chore(scripts): update nolints.txt ([#6032](https://github.com/leanprover-community/mathlib/pull/6032))
I am happy to remove some nolints for you!

### [2021-02-04 03:30:08](https://github.com/leanprover-community/mathlib/commit/7812afa)
feat(data/list/basic): drop_eq_nil_of_le ([#6029](https://github.com/leanprover-community/mathlib/pull/6029))

### [2021-02-04 03:30:06](https://github.com/leanprover-community/mathlib/commit/cbd67cf)
feat(order/(complete_lattice, compactly_generated)): independent sets in a complete lattice ([#5971](https://github.com/leanprover-community/mathlib/pull/5971))
Defines `complete_lattice.independent`
Shows that this notion of independence is finitary in compactly generated lattices

### [2021-02-04 03:30:04](https://github.com/leanprover-community/mathlib/commit/5f328b6)
feat(linear_algebra/free_algebra): Show that free_monoid forms a basis over free_algebra ([#5868](https://github.com/leanprover-community/mathlib/pull/5868))

### [2021-02-03 23:29:31](https://github.com/leanprover-community/mathlib/commit/36b3510)
feat(data/nat/factorial): additional inequalities ([#6026](https://github.com/leanprover-community/mathlib/pull/6026))
I added two lemmas about factorials.  I use them in the Liouville PR [#4301](https://github.com/leanprover-community/mathlib/pull/4301).

### [2021-02-03 17:44:44](https://github.com/leanprover-community/mathlib/commit/360fa07)
feat(data/real/sqrt): added some missing sqrt lemmas ([#5933](https://github.com/leanprover-community/mathlib/pull/5933))
I noticed that some facts about `sqrt` and `abs` are missing, so I am adding them.

### [2021-02-03 16:02:37](https://github.com/leanprover-community/mathlib/commit/bb15b1c)
chore(analysis/calculus): rename `has_f?deriv_at_unique` to `has_f?deriv_at.unique` ([#6019](https://github.com/leanprover-community/mathlib/pull/6019))
Also make some lemmas `protected`.

### [2021-02-03 12:26:39](https://github.com/leanprover-community/mathlib/commit/235a7c4)
doc(lint/simp): typesetting issues in simp_nf library note ([#6018](https://github.com/leanprover-community/mathlib/pull/6018))

### [2021-02-03 12:26:38](https://github.com/leanprover-community/mathlib/commit/9a0d2b2)
chore(data/nat/parity): rename type variable ([#6016](https://github.com/leanprover-community/mathlib/pull/6016))

### [2021-02-03 12:26:36](https://github.com/leanprover-community/mathlib/commit/fa8df59)
feat(algebra/polynomial/big_operators): add degree_prod lemma ([#5979](https://github.com/leanprover-community/mathlib/pull/5979))
This PR adds a degree_prod lemma next to the nat_degree_prod lemma. This version of the lemma works for the interpretation of 'degree' which says the degree of the zero polynomial is \bot

### [2021-02-03 12:26:34](https://github.com/leanprover-community/mathlib/commit/5a9ca8d)
feat(linear_algebra/sesquilinear_form): add composition between sesquilinear forms and linear maps ([#5729](https://github.com/leanprover-community/mathlib/pull/5729))
Add composition lemmas for sesquilinear forms, that is, given a sesquilinear form and linear maps, a new sesquilinear form is induced by applying the arguments with the linear map.

### [2021-02-03 09:45:38](https://github.com/leanprover-community/mathlib/commit/e1ca806)
doc(algebra/{archimedean, char_zero}): provide docstrings ([#6010](https://github.com/leanprover-community/mathlib/pull/6010))

### [2021-02-03 04:39:23](https://github.com/leanprover-community/mathlib/commit/e66ad5f)
chore(scripts): update nolints.txt ([#6014](https://github.com/leanprover-community/mathlib/pull/6014))
I am happy to remove some nolints for you!

### [2021-02-03 04:39:21](https://github.com/leanprover-community/mathlib/commit/79ca6e2)
feat(order/compactly_generated): Show that the sublattice below a compact element is coatomic ([#5942](https://github.com/leanprover-community/mathlib/pull/5942))
Show that the sublattice below a compact element is coatomic. Introduce a lemma stating that any set lying strictly below a compact element has Sup strictly below that element.
<!--
put comments you want to keep out of the PR commit here.
If this PR depends on other PRs, please list them below this comment,
using the following format:
- [ ] depends on: #abc [optional extra text]
- [ ] depends on: #xyz [optional extra text]
-->

### [2021-02-03 01:05:51](https://github.com/leanprover-community/mathlib/commit/fcad25f)
feat(algebra/ring): add mk_mul_self_of_two_ne_zero ([#5862](https://github.com/leanprover-community/mathlib/pull/5862))
Which allows us to make a ring homomorphism from an additive hom which maps squares to squares assuming a couple of  things, this is especially useful in ordered fields where it allows us to think only of positive elements.

### [2021-02-02 23:11:29](https://github.com/leanprover-community/mathlib/commit/2153dc3)
feat(data/fintype/sort): add `fin_sum_equiv_of_finset` ([#6008](https://github.com/leanprover-community/mathlib/pull/6008))

### [2021-02-02 21:38:31](https://github.com/leanprover-community/mathlib/commit/1b1ad15)
refactor(measure_theory/*): rename `is_(null_)?measurable` to `(null_)?measurable_set` ([#6001](https://github.com/leanprover-community/mathlib/pull/6001))
Search & replace:
* `is_null_measurable` → `null_measurable`;
* `is_measurable` → `measurable_set'`;
* `measurable_set_set` → `measurable_set`;
* `measurable_set_spanning_sets` → `measurable_spanning_sets`;
* `measurable_set_superset` → `measurable_superset`.

### [2021-02-02 18:29:12](https://github.com/leanprover-community/mathlib/commit/2b2edc9)
chore(analysis/normed_space/basic): use explicit arg `𝕜'` in lemmas about `normed_algebra` ([#6009](https://github.com/leanprover-community/mathlib/pull/6009))

### [2021-02-02 18:29:10](https://github.com/leanprover-community/mathlib/commit/4e78654)
fix(tactic/delta_instance): improve naming of instances with multiple arguments ([#6007](https://github.com/leanprover-community/mathlib/pull/6007))

### [2021-02-02 18:29:08](https://github.com/leanprover-community/mathlib/commit/fe9c021)
feat(geometry/manifold/instances): sphere is a smooth manifold ([#5607](https://github.com/leanprover-community/mathlib/pull/5607))
Put a smooth manifold structure on the sphere, and provide tools for constructing smooth maps to and from the sphere.

### [2021-02-02 14:44:00](https://github.com/leanprover-community/mathlib/commit/dbb5ca1)
refactor(group_theory/perm): move perm.subtype_perm to basic ([#6005](https://github.com/leanprover-community/mathlib/pull/6005))
Both `perm.subtype_perm` and `perm.of_subtype` can be moved up the import hierarchy out of `group_theory/perm/sign` since they do not rely on any finiteness assumption.

### [2021-02-02 14:43:58](https://github.com/leanprover-community/mathlib/commit/9b3dc41)
feat(nat/basic): more nat.find lemmas ([#6002](https://github.com/leanprover-community/mathlib/pull/6002))
also merge two sections on nat.find

### [2021-02-02 14:43:56](https://github.com/leanprover-community/mathlib/commit/6633a70)
feat(analysis/normed_space/inner_product): remove unnecessary `nonneg_im` field ([#5999](https://github.com/leanprover-community/mathlib/pull/5999))
The `nonneg_im` property already follows from `conj_sym`.

### [2021-02-02 14:43:54](https://github.com/leanprover-community/mathlib/commit/508c265)
feat(logic/function/basic): add bijective.iff_exists_unique and projections ([#5995](https://github.com/leanprover-community/mathlib/pull/5995))

### [2021-02-02 14:43:51](https://github.com/leanprover-community/mathlib/commit/3732fb9)
refactor(data/polynomial/eval): change eval_smul lemmas to use * instead of 2nd smul ([#5991](https://github.com/leanprover-community/mathlib/pull/5991))

### [2021-02-02 14:43:49](https://github.com/leanprover-community/mathlib/commit/ff05d3a)
feat(algebra/group_power/lemmas): sign of even/odd powers ([#5990](https://github.com/leanprover-community/mathlib/pull/5990))
Added theorems about the sign of even and odd natural powers.

### [2021-02-02 14:43:46](https://github.com/leanprover-community/mathlib/commit/25c34e0)
refactor(linear_algebra,algebra/algebra): generalize `linear_map.smul_right` ([#5967](https://github.com/leanprover-community/mathlib/pull/5967))
* the new `linear_map.smul_right` generalizes both the old
  `linear_map.smul_right` and the old `linear_map.smul_algebra_right`;
* add `smul_comm_class` for `linear_map`s.

### [2021-02-02 14:43:44](https://github.com/leanprover-community/mathlib/commit/fc7daa3)
feat(data/nat/parity): addition/subtraction of even/odd nats ([#5934](https://github.com/leanprover-community/mathlib/pull/5934))
 Added various theorems pertaining to the addition and subtraction of even and odd natural numbers.

### [2021-02-02 14:43:42](https://github.com/leanprover-community/mathlib/commit/893ce8b)
feat(tactic/norm_fin): tactic for normalizing `fin n` expressions ([#5820](https://github.com/leanprover-community/mathlib/pull/5820))
This is based on [#5791](https://github.com/leanprover-community/mathlib/pull/5791), with a new implementation using the
`normalize_fin` function.

### [2021-02-02 11:46:18](https://github.com/leanprover-community/mathlib/commit/75a7ce9)
refactor(*): rename subtype_congr to subtype_equiv ([#6004](https://github.com/leanprover-community/mathlib/pull/6004))
This definition is closely related to `perm.subtype_perm`, so renaming will bring them closer in use. Also releavnt is [#5875](https://github.com/leanprover-community/mathlib/pull/5875) which defines a separate `perm.subtype_congr`.

### [2021-02-02 07:14:15](https://github.com/leanprover-community/mathlib/commit/fec8ee4)
chore(topology/bases): rewrite 2 proofs using tactic mode ([#5996](https://github.com/leanprover-community/mathlib/pull/5996))
IMHO they're more readable that way

### [2021-02-02 04:14:06](https://github.com/leanprover-community/mathlib/commit/0c26bb0)
feat(data/finset/basic): add lemmas about bUnion and images of functions on finsets ([#5887](https://github.com/leanprover-community/mathlib/pull/5887))
Add lemmas about bUnion and images of functions on finsets. Part of [#5695](https://github.com/leanprover-community/mathlib/pull/5695) in order to prove Hall's marriage theorem.
Coauthors: @kmill @b-mehta

### [2021-02-02 02:06:24](https://github.com/leanprover-community/mathlib/commit/2c62c0b)
chore(scripts): update nolints.txt ([#6006](https://github.com/leanprover-community/mathlib/pull/6006))
I am happy to remove some nolints for you!

### [2021-02-02 02:06:21](https://github.com/leanprover-community/mathlib/commit/a301ef7)
feat(order/compactly_generated, ring_theory/noetherian): the lattice of submodules is compactly generated ([#5944](https://github.com/leanprover-community/mathlib/pull/5944))
Redefines `is_compactly_generated` as a class
Provides an instance of `is_compactly_generated` on `submodule R M`

### [2021-02-01 22:55:52](https://github.com/leanprover-community/mathlib/commit/4d3b26f)
feat(combinatorics/simple_graph/basic): add decidable instance for adjacency of complement ([#6000](https://github.com/leanprover-community/mathlib/pull/6000))
Add instance that states that, if the adjacency relation for a simple graph is decidable, the adjacency relation for its complement is also decidable.

### [2021-02-01 22:55:50](https://github.com/leanprover-community/mathlib/commit/1706e55)
feat(data/list/basic) add update_nth_comm ([#5989](https://github.com/leanprover-community/mathlib/pull/5989))
As requested on Zulip at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/list.2Eupdate_nth_comm/near/223007424

### [2021-02-01 22:55:48](https://github.com/leanprover-community/mathlib/commit/9b779f4)
refactor(ring_theory/ideal/*, ring_theory/jacobson): use `comm_semiring` instead of `comm_ring` for ideals ([#5954](https://github.com/leanprover-community/mathlib/pull/5954))
This is the second pass at refactoring the definition of `ideal`.  I have changed a `comm_ring` assumption to a `comm_semiring` assumption on many of the lemmas in `ring_theory/ideal/basic`.  Most implied changes were very simple, with the usual exception of `jacobson`.
I also moved out of `jacobson` the lemmas that were left-over from the previous refactor in this sequence.
Besides changing such assumptions on other files, many of the lemmas in `ring_theory/ideal/basic` still using `comm_ring` and without explicit subtractions, deal with quotients.

### [2021-02-01 19:15:19](https://github.com/leanprover-community/mathlib/commit/829c1a5)
chore(group_theory/coset): rename lemmas to follow naming conventions ([#5998](https://github.com/leanprover-community/mathlib/pull/5998))
Rename `normal_of_eq_cosets` and `eq_cosets_of_normal` to follow naming conventions. Conclusion should be stated before the `of`.

### [2021-02-01 19:15:16](https://github.com/leanprover-community/mathlib/commit/684f4f5)
chore(*): split some long lines ([#5997](https://github.com/leanprover-community/mathlib/pull/5997))

### [2021-02-01 19:15:14](https://github.com/leanprover-community/mathlib/commit/acabfa6)
fix(archive/imo/*): fixed syntax for docstrings ([#5994](https://github.com/leanprover-community/mathlib/pull/5994))

### [2021-02-01 19:15:11](https://github.com/leanprover-community/mathlib/commit/a84a80d)
fix(topology/algebra/infinite_sum): add missing decidable arguments ([#5993](https://github.com/leanprover-community/mathlib/pull/5993))
These decidable instances were being inferred as classical instances, which meant these lemmas would not match other instances.

### [2021-02-01 19:15:09](https://github.com/leanprover-community/mathlib/commit/64283ce)
feat(list/{zip,indexes}): Add `zip_with` and `map_with_index` lemmas ([#5974](https://github.com/leanprover-community/mathlib/pull/5974))
All proofs are due to @pechersky.

### [2021-02-01 15:46:19](https://github.com/leanprover-community/mathlib/commit/cbd88d6)
chore(*) add mod_add_div' and div_add_mod' and golf proofs ([#5962](https://github.com/leanprover-community/mathlib/pull/5962))
Resolves issue [#1534](https://github.com/leanprover-community/mathlib/pull/1534).
Name of nat.mod_add_div shouldn't be changed as this is in core. Better name suggestions for mod_add_div' and div_add_mod' welcome.

### [2021-02-01 12:31:43](https://github.com/leanprover-community/mathlib/commit/866e4fd)
chore(linear_algebra/quadratic_form): add two missing simp lemmas about subtraction ([#5985](https://github.com/leanprover-community/mathlib/pull/5985))
This also reorders the instance definitions to keep the lemmas about subtraction near the ones about negation, and uses the `add := (+)` pattern to make definitions unfold more nicely, even though it probably doesn't make any difference.

### [2021-02-01 12:31:41](https://github.com/leanprover-community/mathlib/commit/f2c84aa)
doc(algebra/category/*): provide two short docstrings and shorten lines ([#5984](https://github.com/leanprover-community/mathlib/pull/5984))
also fixed one minor typo.

### [2021-02-01 12:31:39](https://github.com/leanprover-community/mathlib/commit/b1ab310)
chore(analysis/normed_space/inner_product): add {bilin,sesq}_form_of_inner_apply simp lemmas ([#5982](https://github.com/leanprover-community/mathlib/pull/5982))

### [2021-02-01 12:31:37](https://github.com/leanprover-community/mathlib/commit/398e7ad)
feat(data/pnat/basic) pnat can_lift instances ([#5977](https://github.com/leanprover-community/mathlib/pull/5977))
Add can_lift instances for pnat from nat and int

### [2021-02-01 12:31:35](https://github.com/leanprover-community/mathlib/commit/89c7963)
feat(category_theory/nat_iso): dsimp lemma for natural isomorphisms ([#5973](https://github.com/leanprover-community/mathlib/pull/5973))
a little simp lemma

### [2021-02-01 12:31:33](https://github.com/leanprover-community/mathlib/commit/8273588)
chore(category_theory/monad): generate simp lemmas ([#5972](https://github.com/leanprover-community/mathlib/pull/5972))
Adds a missing simps command to generate simp lemmas for the functor.

### [2021-02-01 12:31:31](https://github.com/leanprover-community/mathlib/commit/3f9b035)
chore(category_theory/adjunction): reflective lemmas ([#5968](https://github.com/leanprover-community/mathlib/pull/5968))
Improves the docstring and changes the name to be more appropriate (the lemma has nothing to do with essential images).

### [2021-02-01 09:10:42](https://github.com/leanprover-community/mathlib/commit/c5e0d10)
chore(*): split some long lines ([#5988](https://github.com/leanprover-community/mathlib/pull/5988))

### [2021-02-01 03:11:45](https://github.com/leanprover-community/mathlib/commit/f060e09)
chore(*): golf some proofs ([#5983](https://github.com/leanprover-community/mathlib/pull/5983))
API changes:
* new lemmas `finset.card_filter_le`, `finset.compl_filter`, `finset.card_lt_univ_of_not_mem`, `fintype.card_le_of_embedding`, `fintype.card_lt_of_injective_not_surjective`;
* rename `finset.card_le_of_inj_on` → `finset.le_card_of_inj_on_range`;
* rename `card_lt_of_injective_of_not_mem` to `fintype.card_lt_of_injective_of_not_mem`;
* generalize `card_units_lt` to a `monoid_with_zero`.

### [2021-02-01 01:50:40](https://github.com/leanprover-community/mathlib/commit/609f5f7)
chore(scripts): update nolints.txt ([#5986](https://github.com/leanprover-community/mathlib/pull/5986))
I am happy to remove some nolints for you!