### [2022-04-30 20:50:46](https://github.com/leanprover-community/mathlib/commit/49342e3)
feat(set_theory/cardinal/basic): Add `simp` lemmas on `cardinal.sum` ([#13838](https://github.com/leanprover-community/mathlib/pull/13838))

### [2022-04-30 16:49:17](https://github.com/leanprover-community/mathlib/commit/0420dd8)
chore(measure_theory/measurable_space_def): make measurable_space arguments implicit ([#13832](https://github.com/leanprover-community/mathlib/pull/13832))

### [2022-04-30 11:26:15](https://github.com/leanprover-community/mathlib/commit/26310e7)
feat(algebra/*): a sample of easy useful lemmas ([#13696](https://github.com/leanprover-community/mathlib/pull/13696))
Lemmas needed for [#13690](https://github.com/leanprover-community/mathlib/pull/13690)

### [2022-04-30 10:51:30](https://github.com/leanprover-community/mathlib/commit/1c3ab8c)
feat(probability/notations): fix some notations, add a new one ([#13828](https://github.com/leanprover-community/mathlib/pull/13828))

### [2022-04-30 05:24:54](https://github.com/leanprover-community/mathlib/commit/9141960)
feat(model_theory/syntax): Free variables ([#13529](https://github.com/leanprover-community/mathlib/pull/13529))
Defines `term.var_finset` and `bounded_formula.free_var_finset` to consist of all (free) variables used in a term or formula.
Defines `term.restrict_var` and `bounded_formula.restrict_free_var` to restrict formulas to sets of their variables.

### [2022-04-30 02:26:48](https://github.com/leanprover-community/mathlib/commit/bb45687)
feat(model_theory/syntax, semantics): Substitution of variables in terms and formulas ([#13632](https://github.com/leanprover-community/mathlib/pull/13632))
Defines `first_order.language.term.subst` and `first_order.language.bounded_formula.subst`, which substitute free variables in terms and formulas with terms.

### [2022-04-29 22:22:48](https://github.com/leanprover-community/mathlib/commit/a34ee7b)
chore(set_theory/game/basic): golf proof ([#13810](https://github.com/leanprover-community/mathlib/pull/13810))

### [2022-04-29 22:22:48](https://github.com/leanprover-community/mathlib/commit/24bc2e1)
feat(set_theory/surreal/basic): add `pgame.numeric.left_lt_right` ([#13809](https://github.com/leanprover-community/mathlib/pull/13809))
Also compress some trivial proofs into a single line

### [2022-04-29 22:22:47](https://github.com/leanprover-community/mathlib/commit/a70166a)
feat(ring_theory): factorize a non-unit into irreducible factors without multiplying a unit ([#13682](https://github.com/leanprover-community/mathlib/pull/13682))
Used in https://proofassistants.stackexchange.com/a/1312/93. Also adds simp lemma `multiset.prod_erase` used in the main proof and the auto-generated additive version, which is immediately analogous to [list.prod_erase](https://leanprover-community.github.io/mathlib_docs/data/list/big_operators.html#list.prod_erase). Also removes some extraneous namespace prefix.

### [2022-04-29 20:31:27](https://github.com/leanprover-community/mathlib/commit/059c8eb)
chore(set_theory/game/basic): fix a single space ([#13806](https://github.com/leanprover-community/mathlib/pull/13806))

### [2022-04-29 20:31:26](https://github.com/leanprover-community/mathlib/commit/8910228)
chore(data/polynomial): use dot notation for sub lemmas ([#13799](https://github.com/leanprover-community/mathlib/pull/13799))
To match the additive versions

### [2022-04-29 20:31:25](https://github.com/leanprover-community/mathlib/commit/e56b8fe)
feat(model_theory/graph): First-order language and theory of graphs ([#13720](https://github.com/leanprover-community/mathlib/pull/13720))
Defines `first_order.language.graph`, the language of graphs
Defines `first_order.Theory.simple_graph`, the theory of simple graphs
Produces models of the theory of simple graphs from simple graphs and vice versa.

### [2022-04-29 20:31:23](https://github.com/leanprover-community/mathlib/commit/1d4ed4a)
chore(topology/algebra/valuation): use forgetful inheritance pattern for valued fields ([#13691](https://github.com/leanprover-community/mathlib/pull/13691))
This allows us to solve a `uniform_space` diamond problem that arises when extending valuations to the completion of a valued field.
More precisely, the main goal of this PR is to make the following work:
```lean
import topology.algebra.valued_field
example  {K Γ₀ : Type*} [field K] [linear_ordered_comm_group_with_zero Γ₀] [valued K Γ₀] :
  uniform_space.completion.uniform_space K = valued.to_uniform_space :=
rfl
```

### [2022-04-29 20:31:22](https://github.com/leanprover-community/mathlib/commit/90bd6f5)
feat(model_theory/encoding): A bound on the number of bounded formulas ([#13616](https://github.com/leanprover-community/mathlib/pull/13616))
Gives an encoding `first_order.language.bounded_formula.encoding` of bounded formulas as lists.
Uses the encoding to bound the number of bounded formulas with `first_order.language.bounded_formula.card_le`.

### [2022-04-29 20:31:21](https://github.com/leanprover-community/mathlib/commit/9ce5e95)
feat(model_theory/syntax, semantics): A theory of infinite structures ([#13580](https://github.com/leanprover-community/mathlib/pull/13580))
Defines `first_order.language.infinite_theory`, a theory of infinite structures
Adjusts the API of the theory of nonempty structures to match

### [2022-04-29 20:31:20](https://github.com/leanprover-community/mathlib/commit/812518d)
feat(model_theory/semantics, satisfiability): Complete Theories ([#13558](https://github.com/leanprover-community/mathlib/pull/13558))
Defines `first_order.language.Theory.is_complete`, indicating that a theory is complete.
Defines `first_order.language.complete_theory`, the complete theory of a structure.
Shows that the complete theory of a structure is complete.

### [2022-04-29 20:31:19](https://github.com/leanprover-community/mathlib/commit/812e17f)
feat(analysis/normed_space/pointwise): Addition of balls ([#13381](https://github.com/leanprover-community/mathlib/pull/13381))
Adding two balls yields another ball.

### [2022-04-29 18:38:48](https://github.com/leanprover-community/mathlib/commit/a54db9a)
feat(data/finset/basic): A finset that's a subset of a `directed` union is contained in one element ([#13727](https://github.com/leanprover-community/mathlib/pull/13727))
Proves `directed.exists_mem_subset_of_finset_subset_bUnion`
Renames `finset.exists_mem_subset_of_subset_bUnion_of_directed_on` to `directed_on.exists_mem_subset_of_finset_subset_bUnion`

### [2022-04-29 17:28:05](https://github.com/leanprover-community/mathlib/commit/8624f6d)
chore(analysis/normed/group/basic): add `nnnorm_sum_le_of_le` ([#13795](https://github.com/leanprover-community/mathlib/pull/13795))
This is to match `norm_sum_le_of_le`.
Also tidies up the coercion syntax a little in `pi.semi_normed_group`.
The definition is syntactically identical, just with fewer unecessary type annotations.

### [2022-04-29 17:28:03](https://github.com/leanprover-community/mathlib/commit/8360f2c)
feat(model_theory/language_map, bundled): Reducts of structures ([#13745](https://github.com/leanprover-community/mathlib/pull/13745))
Defines `first_order.language.Lhom.reduct` which pulls a structure back along a language map.
Defines `first_order.language.Theory.Model.reduct` which sends a model of `(φ.on_Theory T)` to its reduct as a model of `T`.

### [2022-04-29 15:59:00](https://github.com/leanprover-community/mathlib/commit/50c3028)
chore(analysis/normed_space/operator_norm): move `continuous_linear_map.op_norm_lsmul` into the correct section ([#13790](https://github.com/leanprover-community/mathlib/pull/13790))
This was in the "seminorm" section but was about regular norms.
Also relaxes some other typeclasses in the file. This file is still a mess with regards to assuming `nondiscrete_normed_field` when `normed_field` is enough, but that would require substantially more movement within the file.
This cleans up after [#13165](https://github.com/leanprover-community/mathlib/pull/13165) and [#13538](https://github.com/leanprover-community/mathlib/pull/13538)

### [2022-04-29 15:58:59](https://github.com/leanprover-community/mathlib/commit/64b3576)
feat(ring_theory/valuation/extend_to_localization): Extending valuations to localizations. ([#13610](https://github.com/leanprover-community/mathlib/pull/13610))

### [2022-04-29 14:39:20](https://github.com/leanprover-community/mathlib/commit/fe2917a)
feat(number_theory/primes_congruent_one): attempt to golf ([#13787](https://github.com/leanprover-community/mathlib/pull/13787))
As suggested in the reviews of [#12595](https://github.com/leanprover-community/mathlib/pull/12595) we try to golf the proof using the bound proved there.
This doesn't end up being as much of a golf as hoped due to annoying edge cases, but seems conceptually simpler.

### [2022-04-29 14:39:18](https://github.com/leanprover-community/mathlib/commit/a3beb62)
feat(analysis/*): a sample of easy useful lemmas ([#13697](https://github.com/leanprover-community/mathlib/pull/13697))
Lemmas needed for [#13690](https://github.com/leanprover-community/mathlib/pull/13690)

### [2022-04-29 14:39:17](https://github.com/leanprover-community/mathlib/commit/7373832)
chore(analysis/convex): move `convex_on_norm`, change API ([#13631](https://github.com/leanprover-community/mathlib/pull/13631))
* Move `convex_on_norm` from `specific_functions` to `topology`, use it to golf the proof of `convex_on_dist`.
* The old `convex_on_norm` is now called `convex_on_univ_norm`. The new `convex_on_norm` is about convexity on any convex set.
* Add `convex_on_univ_dist` and make `s : set E` an implicit argument in `convex_on_dist`.
This way APIs about convexity of norm and distance agree.

### [2022-04-29 14:39:15](https://github.com/leanprover-community/mathlib/commit/ce79a27)
feat(analysis/normed_space/pi_Lp): add lemmas about `pi_Lp.equiv` ([#13569](https://github.com/leanprover-community/mathlib/pull/13569))
Most of these are trivial `dsimp` lemmas, but they also let us talk about the norm of constant vectors.

### [2022-04-29 14:39:14](https://github.com/leanprover-community/mathlib/commit/e561264)
feat(algebra/order/monoid_lemmas_zero_lt): add instances ([#13376](https://github.com/leanprover-community/mathlib/pull/13376))

### [2022-04-29 12:25:32](https://github.com/leanprover-community/mathlib/commit/58552fe)
feat(set_theory/cardinal/basic): cardinality of a powerset ([#13786](https://github.com/leanprover-community/mathlib/pull/13786))

### [2022-04-29 12:25:31](https://github.com/leanprover-community/mathlib/commit/b2e0a2d)
feat(group_theory/subgroup/basic): `inclusion` lemmas ([#13754](https://github.com/leanprover-community/mathlib/pull/13754))
A few lemmas for `set.inclusion`, `subgroup.inclusion`, `subalgebra.inclusion`.

### [2022-04-29 12:25:30](https://github.com/leanprover-community/mathlib/commit/8eb2564)
feat(topology/instances/matrix): add `matrix` lemmas about `tsum` ([#13677](https://github.com/leanprover-community/mathlib/pull/13677))
This adds lemmas about how `tsum` interacts with `diagonal` and `transpose`, along with the helper `summable` and `has_sum` lemmas.
This also moves `topology/algebra/matrix` to `topology/instances/matrix`, since that seems to align better with how other types are handled.

### [2022-04-29 11:14:10](https://github.com/leanprover-community/mathlib/commit/889e956)
chore(analysis/asymptotics/asymptotics): relax `normed_group` to `semi_normed_group` in lemmas ([#13642](https://github.com/leanprover-community/mathlib/pull/13642))
This file already uses `E` vs `E'` for `has_norm` vs `normed_group`. This adds an `E''` to this naming scheme for `normed_group`, and repurposes `E'` to `semi_normed_group`. The majority of the lemmas in this file generalize without any additional work.
I've not attempted to relax the assumptions on lemmas where any proofs would have to change. Most of them would need their assumptions changing from `c ≠ 0` to `∥c∥ ≠ 0`, which is likely to be annoying.
In one place this results in dot notation breaking as the typeclass can no longer be found by unification.

### [2022-04-29 09:31:57](https://github.com/leanprover-community/mathlib/commit/aab0b2d)
feat(algebra/algebra/basic): add some lemmas about `subsemiring` and `algebra_map` ([#13767](https://github.com/leanprover-community/mathlib/pull/13767))
These are analogs of `algebra_map_of_subring`, `coe_algebra_map_of_subring` and `algebra_map_of_subring_apply`.

### [2022-04-29 08:26:15](https://github.com/leanprover-community/mathlib/commit/8abfb3b)
feat(representation_theory/Rep): Rep k G is abelian ([#13689](https://github.com/leanprover-community/mathlib/pull/13689))

### [2022-04-29 06:35:27](https://github.com/leanprover-community/mathlib/commit/bc65b7c)
feat(data/list/basic): add `list.range_map` ([#13777](https://github.com/leanprover-community/mathlib/pull/13777))
* add `list.range_map` and `list.range_map_coe`;
* add `submonoid.closure_eq_image_prod` and `add_submonoid.closure_eq_image_prod`.

### [2022-04-29 06:35:26](https://github.com/leanprover-community/mathlib/commit/992e26f)
feat(topology/algebra/affine): a sufficiently small dilation of a point in the interior of a set lands in the interior ([#13766](https://github.com/leanprover-community/mathlib/pull/13766))
Formalized as part of the Sphere Eversion project.

### [2022-04-29 06:35:25](https://github.com/leanprover-community/mathlib/commit/b4cad37)
chore(ring_theory/mv_polynomial/basic): golf ([#13765](https://github.com/leanprover-community/mathlib/pull/13765))

### [2022-04-29 06:35:24](https://github.com/leanprover-community/mathlib/commit/5c1ee35)
feat(set_theory/game/pgame): `x - 0 = x + 0` ([#13731](https://github.com/leanprover-community/mathlib/pull/13731))

### [2022-04-29 04:24:26](https://github.com/leanprover-community/mathlib/commit/7170b66)
chore(scripts): update nolints.txt ([#13775](https://github.com/leanprover-community/mathlib/pull/13775))
I am happy to remove some nolints for you!

### [2022-04-29 04:24:25](https://github.com/leanprover-community/mathlib/commit/ead85e6)
chore(*/equiv): add simp to refl_apply and trans_apply where missing ([#13760](https://github.com/leanprover-community/mathlib/pull/13760))

### [2022-04-29 04:24:24](https://github.com/leanprover-community/mathlib/commit/e294500)
feat(category_theory/monoidal): transport rigid structure over an equivalence ([#13736](https://github.com/leanprover-community/mathlib/pull/13736))

### [2022-04-29 04:24:23](https://github.com/leanprover-community/mathlib/commit/ccb9d64)
feat(category_theory/braiding): pull back a braiding along a faithful functor ([#13684](https://github.com/leanprover-community/mathlib/pull/13684))
I intend to use this to define the braiding/symmetry on `Rep k G` using the existing braiding/symmetry on `Module k`.

### [2022-04-29 03:48:10](https://github.com/leanprover-community/mathlib/commit/8edb3d1)
feat(representation_theory/Rep): the category of representations ([#13683](https://github.com/leanprover-community/mathlib/pull/13683))
We define `Rep k G`, the category of `k`-linear representations of a monoid `G`.
Happily, by abstract nonsense we get that this has (co)limits and a monoidal structure for free.
This should play well with the new design for representations in [#13573](https://github.com/leanprover-community/mathlib/pull/13573).

### [2022-04-29 00:29:56](https://github.com/leanprover-community/mathlib/commit/11a4a74)
feat(ring_theory/localization/basic): generalize to semiring ([#13459](https://github.com/leanprover-community/mathlib/pull/13459))
The main ingredient of this PR is the definition of `is_localization.lift` that works for semirings. The previous definition uses `ring_hom.mk'` that essentially states that `f 0 = 0` follows from other conditions. This does not holds for semirings. Instead, this PR defines the localization of monoid with zero, and uses this to define `is_localization.lift`.
- I think definitions around `localization_with_zero_map` might be ad hoc, and any suggestions for improvement are welcome!
- I plan to further generalize the localization API for semirings. This needs generalization of other ring theory stuff such as `local_ring` and `is_domain` (generalizing `local_ring` is partially done in [#13341](https://github.com/leanprover-community/mathlib/pull/13341)).

### [2022-04-28 22:42:55](https://github.com/leanprover-community/mathlib/commit/214e2f1)
chore(set_theory/surreal/basic): Allow dot notation on `pgame.numeric` ([#13768](https://github.com/leanprover-community/mathlib/pull/13768))
Rename `numeric_neg`/`numeric_add` to `numeric.add`/`numeric.neg`. Prove `numeric.sub` in passing.

### [2022-04-28 21:23:33](https://github.com/leanprover-community/mathlib/commit/ccd3774)
chore(ring_theory/*): dot notation for `submodule.fg` and `subalgebra.fg` ([#13737](https://github.com/leanprover-community/mathlib/pull/13737))

### [2022-04-28 21:23:32](https://github.com/leanprover-community/mathlib/commit/220d4b8)
doc(order/filter/small_sets): fix in doc ([#13648](https://github.com/leanprover-community/mathlib/pull/13648))

### [2022-04-28 20:49:01](https://github.com/leanprover-community/mathlib/commit/c096a33)
feat(set_theory/game/birthday): Game birthday is zero iff empty ([#13715](https://github.com/leanprover-community/mathlib/pull/13715))

### [2022-04-28 19:47:12](https://github.com/leanprover-community/mathlib/commit/8a32fdf)
feat(cyclotomic/eval): (q - 1) ^ totient n < |ϕₙ(q)| ([#12595](https://github.com/leanprover-community/mathlib/pull/12595))
Originally from the Wedderburn PR, but generalized to include an exponent.

### [2022-04-28 17:35:20](https://github.com/leanprover-community/mathlib/commit/0d3f8a7)
feat(ring_theory/submonoid/membership): generalize a few lemmas to `mul_mem_class` ([#13748](https://github.com/leanprover-community/mathlib/pull/13748))
This generalizes lemmas relating to the additive closure of a multiplicative monoid so that they also apply to multiplicative semigroups using `mul_mem_class`

### [2022-04-28 15:47:51](https://github.com/leanprover-community/mathlib/commit/c5bf480)
fix(group_theory/subsemigroup/basic): change `mul_one_class` to `has_mul` ([#13747](https://github.com/leanprover-community/mathlib/pull/13747))

### [2022-04-28 13:52:30](https://github.com/leanprover-community/mathlib/commit/1c92dfd)
chore(*/equiv): missing refl_symm lemmas ([#13761](https://github.com/leanprover-community/mathlib/pull/13761))

### [2022-04-28 08:07:58](https://github.com/leanprover-community/mathlib/commit/0cb20fc)
feat(set_theory/ordinal/basic): `max a 0 = a` ([#13734](https://github.com/leanprover-community/mathlib/pull/13734))

### [2022-04-28 08:07:57](https://github.com/leanprover-community/mathlib/commit/98e7848)
feat(set_theory/game/pgame): Right moves of nat game are empty ([#13730](https://github.com/leanprover-community/mathlib/pull/13730))

### [2022-04-28 07:28:19](https://github.com/leanprover-community/mathlib/commit/a0af147)
feat(set_theory/game/pgame): An empty game is a relabelling of `0` ([#13753](https://github.com/leanprover-community/mathlib/pull/13753))

### [2022-04-27 23:52:26](https://github.com/leanprover-community/mathlib/commit/e89510c)
fix(ring_theory/subsemiring/basic): make `inclusion` a `ring_hom`, not a `monoid_hom` ([#13746](https://github.com/leanprover-community/mathlib/pull/13746))

### [2022-04-27 20:32:15](https://github.com/leanprover-community/mathlib/commit/60bb071)
feat(logic/unit): Make `punit.star` simp normal form of `default : punit` ([#13741](https://github.com/leanprover-community/mathlib/pull/13741))

### [2022-04-27 15:34:59](https://github.com/leanprover-community/mathlib/commit/dc589c8)
fix(topology/bornology): turn `bounded_space` into a `mixin` ([#13615](https://github.com/leanprover-community/mathlib/pull/13615))
Otherwise, we would need `bounded_pseudo_metric_space`,
`bounded_metric_space` etc.
Also add `set.finite.is_bounded`, `bornology.is_bounded.all`, and
`bornology.is_bounded_univ`.

### [2022-04-27 14:57:36](https://github.com/leanprover-community/mathlib/commit/d399744)
feat(measure_theory/measure/finite_measure_weak_convergence): define the topology of weak convergence of measures and prove some lemmas about it. ([#9943](https://github.com/leanprover-community/mathlib/pull/9943))
This PR has the definition of the topology of weak convergence ("convergence in law" / "convergence in distribution") on `finite_measure _` and on `probability_measure _`.

### [2022-04-27 10:54:41](https://github.com/leanprover-community/mathlib/commit/ccefda0)
perf(representation_theory/basic): speed up `representation.lin_hom` by a factor of 20 ([#13739](https://github.com/leanprover-community/mathlib/pull/13739))
`ext` was over-expanding, and the `simp`s were not all squeezed.
This is causing timeouts in other PRs.

### [2022-04-27 07:01:45](https://github.com/leanprover-community/mathlib/commit/5ac5c92)
feat(combinatorics/simple_graph/regularity/uniform): Witnesses of non-uniformity ([#13155](https://github.com/leanprover-community/mathlib/pull/13155))
Provide ways to pick witnesses of non-uniformity.

### [2022-04-27 02:01:16](https://github.com/leanprover-community/mathlib/commit/cb2b02f)
feat(representation_theory/basic): representation theory without scalar actions ([#13573](https://github.com/leanprover-community/mathlib/pull/13573))
This PR rewrites the files `representation_theory/basic` and `representation_theory/invariants` so that they avoid making use of scalar actions. It also includes the new definitions and lemmas of PR [#13502](https://github.com/leanprover-community/mathlib/pull/13502) written with this new approach.

### [2022-04-27 00:04:48](https://github.com/leanprover-community/mathlib/commit/79e309b)
feat(set_theory/game/pgame): Define `is_option` relation ([#13700](https://github.com/leanprover-community/mathlib/pull/13700))

### [2022-04-26 22:05:34](https://github.com/leanprover-community/mathlib/commit/48997d7)
fix(data/set/basic): fix name of `has_mem.mem.out` ([#13721](https://github.com/leanprover-community/mathlib/pull/13721))

### [2022-04-26 20:19:00](https://github.com/leanprover-community/mathlib/commit/b00a7f8)
refactor(number_theory/padics/padic_norm): split file ([#13576](https://github.com/leanprover-community/mathlib/pull/13576))
This PR splits the initial part of the `padic_norm.lean` file that defines p-adic valuations into a new file called `padic_val.lean`. This split makes sense to me since it seems most files importing this don't actually use the norm, so those files can build more in parallel. It also seems like a good organizational change: This way people can look at the files in this directory and see immediately where the valuation is defined, and people looking for the definition of `padic_norm` in `padic_norm.lean` don't have to scroll.

### [2022-04-26 18:41:44](https://github.com/leanprover-community/mathlib/commit/de79a76)
chore(topology/continuous_function/zero_at_infty): add `is_central_scalar` instance ([#13710](https://github.com/leanprover-community/mathlib/pull/13710))

### [2022-04-26 18:41:43](https://github.com/leanprover-community/mathlib/commit/76de6f7)
feat(group_theory/subsemigroup/operations): port from submonoid  ([#12112](https://github.com/leanprover-community/mathlib/pull/12112))
Taken from `group_theory.submonoid.operations`, trying to keep as much API as possible

### [2022-04-26 17:50:15](https://github.com/leanprover-community/mathlib/commit/560d1a7)
chore(topology/continuous_function/continuous_map): add missing instances for `continuous_map` ([#13717](https://github.com/leanprover-community/mathlib/pull/13717))
This adds instances related to the ring variants, i.e., non-unital, non-associative (semi)rings.
To avoid introducing accidental diamonds, this also changes how the existing instances are constructed, such that they now go through the `function.injective.*` definitions.

### [2022-04-26 17:50:14](https://github.com/leanprover-community/mathlib/commit/325dbc8)
refactor(number_theory/legendre_symbol/quadratic_reciprocity.lean): change definition of legendre_sym, simplify proofs, add lemmas ([#13667](https://github.com/leanprover-community/mathlib/pull/13667))
This changes the definition of `legendre_sym` to use `quadratic_char`.
The proof of some of the statements can then be simplified by using the corresponding statements for quadratic characters.
Some new API lemmas are added, including the fact that the Legendre symbol is multiplicative,
Also, a few `simps` are squeezed in `.../quadratic_char.lean`.

### [2022-04-26 15:51:40](https://github.com/leanprover-community/mathlib/commit/8b14d48)
feat(logic/relation): Transitive closure of well-founded relation is well-founded ([#13698](https://github.com/leanprover-community/mathlib/pull/13698))

### [2022-04-26 13:36:55](https://github.com/leanprover-community/mathlib/commit/e77dbe0)
doc(data/list/*): Fix file links ([#13711](https://github.com/leanprover-community/mathlib/pull/13711))
They were linking to `data.list.data.list.defs`.

### [2022-04-26 13:36:53](https://github.com/leanprover-community/mathlib/commit/bfa0ba5)
feat(analysis/normed_space/pointwise): The closure of a thickening ([#13708](https://github.com/leanprover-community/mathlib/pull/13708))
Prove `closure (thickening δ s) = cthickening δ s` and golf "thickening a thickening" lemmas.

### [2022-04-26 13:36:52](https://github.com/leanprover-community/mathlib/commit/e6c6764)
feat(logic/relation): Add missing instances ([#13704](https://github.com/leanprover-community/mathlib/pull/13704))

### [2022-04-26 13:36:51](https://github.com/leanprover-community/mathlib/commit/3d5e5ee)
feat(data/list/*): Miscellaneous lemmas ([#13577](https://github.com/leanprover-community/mathlib/pull/13577))
A few lemmas about `list.chain`, `list.pairwise`. Also rename `list.chain_of_pairwise` to `list.pairwise.chain` for dot notation.

### [2022-04-26 11:29:38](https://github.com/leanprover-community/mathlib/commit/c83488b)
feat(topology/order/priestley): Priestley spaces ([#12044](https://github.com/leanprover-community/mathlib/pull/12044))
Define `priestley_space`, a Prop-valued mixin for an ordered topological space to respect Priestley's separation axiom.

### [2022-04-26 09:51:42](https://github.com/leanprover-community/mathlib/commit/b0efdbb)
feat(algebra/module/linear_map) : cancel_right and cancel_left for linear_maps ([#13703](https://github.com/leanprover-community/mathlib/pull/13703))

### [2022-04-26 09:51:41](https://github.com/leanprover-community/mathlib/commit/5172448)
feat(set_theory/game/pgame): Conway induction on games ([#13699](https://github.com/leanprover-community/mathlib/pull/13699))
This is a more convenient restatement of the induction principle of the type.

### [2022-04-26 09:51:40](https://github.com/leanprover-community/mathlib/commit/4c6b373)
feat(group_theory/subgroup/basic): `zpowers_le` ([#13693](https://github.com/leanprover-community/mathlib/pull/13693))
This PR adds a lemma `zpowers_le : zpowers g ≤ H ↔ g ∈ H`. I also fixed the `to_additive` name of a lemma from a previous PR.

### [2022-04-26 09:51:39](https://github.com/leanprover-community/mathlib/commit/b94ea15)
refactor(linear_algebra/matrix/trace): unbundle `matrix.diag` ([#13687](https://github.com/leanprover-community/mathlib/pull/13687))
The bundling makes it awkward to work with, as the base ring has to be specified even though it doesn't affect the computation.
This brings it in line with `matrix.diagonal`.
The bundled version is now available as `matrix.diag_linear_map`.
This adds a handful of missing lemmas about `diag` inspired by those about `diagonal`; almost all of which are just `rfl`.

### [2022-04-26 07:55:34](https://github.com/leanprover-community/mathlib/commit/6ae00ad)
chore(tactic/field_simp): fix docstring ([#13695](https://github.com/leanprover-community/mathlib/pull/13695))

### [2022-04-26 07:55:33](https://github.com/leanprover-community/mathlib/commit/a02f11f)
feat(algebra/ring/equiv): generalize `ring_equiv` material to allow for non-unital rings ([#13626](https://github.com/leanprover-community/mathlib/pull/13626))

### [2022-04-26 07:55:32](https://github.com/leanprover-community/mathlib/commit/1b1ae61)
feat(analysis/normed_space/pointwise): Thickening a thickening ([#13380](https://github.com/leanprover-community/mathlib/pull/13380))
In a real normed space, thickening twice is the same as thickening once.

### [2022-04-26 07:21:28](https://github.com/leanprover-community/mathlib/commit/093b583)
feat(set_theory/game/pgame): `ordinal.to_pgame` ([#13628](https://github.com/leanprover-community/mathlib/pull/13628))
We define the canonical map from ordinals to pre-games and prove it's an order embedding.

### [2022-04-26 04:54:38](https://github.com/leanprover-community/mathlib/commit/bf67d47)
chore(scripts): update nolints.txt ([#13706](https://github.com/leanprover-community/mathlib/pull/13706))
I am happy to remove some nolints for you!

### [2022-04-26 04:54:37](https://github.com/leanprover-community/mathlib/commit/748ea79)
feat(order/filter/basic): more lemmas about `filter.comap` ([#13619](https://github.com/leanprover-community/mathlib/pull/13619))
* add `set.compl_def`, `set.finite_image_fst_and_snd_iff`, and `set.forall_finite_image_eval_iff`;
* add `filter.coext`, an extensionality lemma that is more useful for "cofilters";
* rename `filter.eventually_comap'` to `filter.eventually.comap`;
* add `filter.mem_comap'`, `filter.mem_comap_iff_compl`, and `filter.compl_mem_comap`;
* add `filter.compl_mem_coprod`, replace `filter.compl_mem_Coprod_iff` with a simpler `filter.compl_mem_Coprod`;
* add `filter.map_top`;
* use new lemmas to golf some proofs.

### [2022-04-26 02:57:32](https://github.com/leanprover-community/mathlib/commit/4de6527)
feat(algebra/ring/basic): define non-unital commutative (semi)rings ([#13476](https://github.com/leanprover-community/mathlib/pull/13476))
This adds the classes of non-unital commutative (semi)rings. These are necessary to talk about, for example, non-unital commutative C∗-algebras such as `C₀(X, ℂ)` which are vital for the continuous functional calculus.
In addition, we weaken many type class assumptions in `algebra/ring/basic` to `non_unital_non_assoc_ring`.

### [2022-04-26 01:09:50](https://github.com/leanprover-community/mathlib/commit/24a8bb9)
feat(order/well-founded): Remove redundant arguments ([#13702](https://github.com/leanprover-community/mathlib/pull/13702))
All of these are inferred as `{α : Type*}` (as opposed to `{α : Sort*}`), and there is already a `variables {α : Type*}` at the top of the file.

### [2022-04-25 23:11:10](https://github.com/leanprover-community/mathlib/commit/438b39a)
feat(set_theory/cardinal/basic): Distributivity of `cardinal.sum` and + ([#13643](https://github.com/leanprover-community/mathlib/pull/13643))
`cardinal.sum_add_distrib` shows that `cardinal.sum` distributes over +.

### [2022-04-25 19:25:37](https://github.com/leanprover-community/mathlib/commit/8f604aa)
feat(data/nat/totient): totient equals one iff ([#13688](https://github.com/leanprover-community/mathlib/pull/13688))

### [2022-04-25 17:22:45](https://github.com/leanprover-community/mathlib/commit/4e50b68)
feat(category_theory/abelian): if D is abelian so is C ⥤ D ([#13686](https://github.com/leanprover-community/mathlib/pull/13686))
Needed for LTE, and also useful to show `Rep k G` is abelian.

### [2022-04-25 17:22:44](https://github.com/leanprover-community/mathlib/commit/43e84cd)
feat(data/fin/succ_pred): `fin` is an archimedean succ/pred order ([#12792](https://github.com/leanprover-community/mathlib/pull/12792))

### [2022-04-25 15:23:31](https://github.com/leanprover-community/mathlib/commit/4481a56)
feat(algebra/group_power/order): Add sq_zero_iff ([#13670](https://github.com/leanprover-community/mathlib/pull/13670))
Tiny lemma that seems to be missing.
Should this be a simp lemma?

### [2022-04-25 15:23:30](https://github.com/leanprover-community/mathlib/commit/e2f5696)
feat(analysis/normed_space/exponential): add `pi.exp_apply` ([#13488](https://github.com/leanprover-community/mathlib/pull/13488))
The statement is a bit weird, but this structure is useful because it allows us to push `exp` through `matrix.diagonal` and into its elements.

### [2022-04-25 15:23:29](https://github.com/leanprover-community/mathlib/commit/85075bc)
refactor(category_theory/monoidal): rearrange simp lemmas to work better with coherence ([#13409](https://github.com/leanprover-community/mathlib/pull/13409))
Change the direction of some simp lemma for monoidal categories, and remove some unused lemmas.
This PR is effectively a "no-op": no substantial changes to proofs. However, it should enable making `coherence` more powerful soon (following suggestions of @yuma-mizuno)!

### [2022-04-25 15:23:28](https://github.com/leanprover-community/mathlib/commit/9f75d75)
feat(analysis/convex/measure): a convex set is null-measurable ([#13138](https://github.com/leanprover-community/mathlib/pull/13138))

### [2022-04-25 15:23:27](https://github.com/leanprover-community/mathlib/commit/2c15ce1)
feat(data/nat/choose): add facts about the multiplicity of primes in the factorisation of central binomial coefficients ([#9925](https://github.com/leanprover-community/mathlib/pull/9925))
A number of bounds on the multiplicity of primes in the factorisation of central binomial coefficients. These are of interest because they form part of the proof of Bertrand's postulate.

### [2022-04-25 13:21:34](https://github.com/leanprover-community/mathlib/commit/2825f35)
feat(data/set/prod): add `set.eval_image_pi_subset` ([#13613](https://github.com/leanprover-community/mathlib/pull/13613))
Also reorder lemmas like `fst_image_prod_subset` so that simpler
lemmas go first.

### [2022-04-25 13:21:32](https://github.com/leanprover-community/mathlib/commit/14b0e32)
chore(data/finsupp/fin): golf some proofs ([#13607](https://github.com/leanprover-community/mathlib/pull/13607))

### [2022-04-25 13:21:31](https://github.com/leanprover-community/mathlib/commit/b7538a3)
feat(algebra/periodic): add lemmas `periodic.prod`, `periodic.smul`, `antiperiodic.smul` ([#13496](https://github.com/leanprover-community/mathlib/pull/13496))
Formalized as part of the Sphere Eversion project.

### [2022-04-25 11:19:25](https://github.com/leanprover-community/mathlib/commit/4bfae3d)
feat(set_theory/game/pgame): remove nolint ([#13680](https://github.com/leanprover-community/mathlib/pull/13680))
We remove `@[nolint has_inhabited_instance]` from `left_moves` and `right_moves` by providing the appropriate instances for `star`.

### [2022-04-25 11:19:24](https://github.com/leanprover-community/mathlib/commit/9e8d107)
feat(dynamics/periodic_pts): `pow_smul_eq_iff_minimal_period_dvd` ([#13676](https://github.com/leanprover-community/mathlib/pull/13676))
This PR adds a lemma `pow_smul_eq_iff_minimal_period_dvd`, along with additive and integer versions.

### [2022-04-25 11:19:22](https://github.com/leanprover-community/mathlib/commit/7231172)
feat(topology/algebra): actions on the opposite type are continuous ([#13671](https://github.com/leanprover-community/mathlib/pull/13671))
This also adds the missing `t2_space` instance.

### [2022-04-25 11:19:21](https://github.com/leanprover-community/mathlib/commit/ed10ba2)
feat(ring_theory/witt_vector/frobenius): add `witt_vector.frobenius_equiv` ([#13666](https://github.com/leanprover-community/mathlib/pull/13666))
This promotes the bijection to an equivalence with an explicit inverse

### [2022-04-25 11:19:20](https://github.com/leanprover-community/mathlib/commit/6d3ca07)
feat(data/zmod/basic): `-1 : zmod n` lifts to `n - 1` ([#13665](https://github.com/leanprover-community/mathlib/pull/13665))
This PR adds a lemma stating that `-1 : zmod n` lifts to `n - 1 : R` for any ring `R`. The proof is surprisingly painful, but maybe someone can find a nicer way?

### [2022-04-25 11:19:19](https://github.com/leanprover-community/mathlib/commit/ad0a3e6)
feat(dynamics/periodic_pts): Iteration is injective below the period ([#13660](https://github.com/leanprover-community/mathlib/pull/13660))
This PR adds `iterate_injective_of_lt_minimal_period`, generalizing `pow_injective_of_lt_order_of`.

### [2022-04-25 10:43:44](https://github.com/leanprover-community/mathlib/commit/6710d65)
feat(analysis/complex/roots_of_unity): arg of a primitive root ([#13583](https://github.com/leanprover-community/mathlib/pull/13583))

### [2022-04-25 08:04:59](https://github.com/leanprover-community/mathlib/commit/b35ed40)
feat(algebra/order/hom/ring): There's at most one hom between linear ordered fields ([#13601](https://github.com/leanprover-community/mathlib/pull/13601))
There is at most one ring homomorphism from a linear ordered field to an archimedean linear ordered field. Also generalize `map_rat_cast` to take in `ring_hom_class`.

### [2022-04-25 08:04:57](https://github.com/leanprover-community/mathlib/commit/d795ea4)
feat(number_theory/legendre_symbol/quadratic_reciprocity): Alternate forms of `exists_sq_eq_neg_one` ([#13594](https://github.com/leanprover-community/mathlib/pull/13594))
Also, renamed `exists_sq_eq_neg_one_iff_mod_four_ne_three` to `exists_sq_eq_neg_one` for consistency with `exists_sq_eq_two` and for convenience.

### [2022-04-25 08:04:56](https://github.com/leanprover-community/mathlib/commit/e251ef7)
feat(logic/basic): `congr_fun` for heterogeneous equality ([#13591](https://github.com/leanprover-community/mathlib/pull/13591))

### [2022-04-25 08:04:55](https://github.com/leanprover-community/mathlib/commit/e059fdf)
feat(algebra/big_operators/basic): mk0_prod ([#13582](https://github.com/leanprover-community/mathlib/pull/13582))

### [2022-04-25 08:04:54](https://github.com/leanprover-community/mathlib/commit/f02c784)
feat(special_functions/gamma): recurrence relation for Gamma function ([#13156](https://github.com/leanprover-community/mathlib/pull/13156))

### [2022-04-25 06:24:12](https://github.com/leanprover-community/mathlib/commit/ef3769d)
feat(group_theory/subgroup/basic): Cyclic subgroups are commutative ([#13663](https://github.com/leanprover-community/mathlib/pull/13663))
This PR adds an instance stating that the cyclic subgroups `zpowers g` are commutative.

### [2022-04-25 06:24:11](https://github.com/leanprover-community/mathlib/commit/b0fe3cd)
feat(order/filter): add `filter.coprod_bot` etc ([#13662](https://github.com/leanprover-community/mathlib/pull/13662))

### [2022-04-25 06:24:10](https://github.com/leanprover-community/mathlib/commit/feb9aed)
feat(group_theory/group_action/basic): More API for `quotient_action` ([#13661](https://github.com/leanprover-community/mathlib/pull/13661))
This PR adds a couple more API lemmas for `quotient_action`.

### [2022-04-25 06:24:09](https://github.com/leanprover-community/mathlib/commit/46563c5)
refactor(analysis/convex/basic): rewrite a few proofs ([#13658](https://github.com/leanprover-community/mathlib/pull/13658))
* prove that a closed segment is the union of the corresponding open segment and the endpoints;
* use this lemma to golf some proofs;
* make the "field" argument of `mem_open_segment_of_ne_left_right` implicit.
* use section variables.

### [2022-04-25 06:24:07](https://github.com/leanprover-community/mathlib/commit/7d64215)
chore(analysis/convex/topology): generalize a few lemmas ([#13656](https://github.com/leanprover-community/mathlib/pull/13656))
This way they work for `𝕜 = ℚ` too.

### [2022-04-25 06:24:04](https://github.com/leanprover-community/mathlib/commit/c24f1f2)
chore(number_theory/padics/*): tidy some proofs ([#13652](https://github.com/leanprover-community/mathlib/pull/13652))

### [2022-04-25 06:24:00](https://github.com/leanprover-community/mathlib/commit/962bfcd)
chore(field_theory/finite/polynomial): tidy + remove nolints ([#13645](https://github.com/leanprover-community/mathlib/pull/13645))
Some of these definitions only make full sense over a field (for example the indicator function can be nonsensical in non-field rings) but there's also no reason not to define them more generally. This removes all `nolint`s related to this file, and all of the generalisation linter suggestions too.

### [2022-04-25 06:24:00](https://github.com/leanprover-community/mathlib/commit/b6a4be4)
chore(ring_theory/witt_vector/isocrystal): speed up the proof ([#13644](https://github.com/leanprover-community/mathlib/pull/13644))
to remove a timeout in [#13459](https://github.com/leanprover-community/mathlib/pull/13459)

### [2022-04-25 06:23:59](https://github.com/leanprover-community/mathlib/commit/9c861e3)
feat(topology/algebra/matrix): `matrix.block_diagonal` is continuous ([#13641](https://github.com/leanprover-community/mathlib/pull/13641))
`continuous.if_const` isn't suitable for the primed `matrix.block_diagonal'` case, as the `if` is dependent.

### [2022-04-25 06:23:58](https://github.com/leanprover-community/mathlib/commit/b1b2cab)
feat(group_theory/complement): The range of a section `G ⧸ H → G` is a transversal ([#13623](https://github.com/leanprover-community/mathlib/pull/13623))
This PR adds left and right versions of the statement that the range of a section `G ⧸ H → G` is a transversal.

### [2022-04-25 06:23:57](https://github.com/leanprover-community/mathlib/commit/6cbf986)
refactor(group_theory/schur_zassenhaus): Golf proof of abelian case ([#13622](https://github.com/leanprover-community/mathlib/pull/13622))
This PR golfs the proof of the abelian case of Schur-Zassenhaus by switching from a nonstandard definition of the difference of two left transversals to the definition used in `transfer.lean`.

### [2022-04-25 06:23:56](https://github.com/leanprover-community/mathlib/commit/b6c8c0d)
refactor(linear_algebra/quotient): Use the same quotient relation as add_subgroup ([#13620](https://github.com/leanprover-community/mathlib/pull/13620))
This means that the quotient by `p` and `p.to_add_subgroup` are defeq as types, and the instances defined on them are defeq too.
This removes a TODO comment by Mario; I can only assume it resolves it in the right direction

### [2022-04-25 06:23:55](https://github.com/leanprover-community/mathlib/commit/91b8084)
chore(analysis/normed_space/finite_dimension): extract some lemmas from existentials ([#13600](https://github.com/leanprover-community/mathlib/pull/13600))
A few proofs in this file prove an existential where a stronger statement in terms of the witness exists.
This:
* Removes `basis.sup_norm_le_norm` and replaces it with the more general statement `pi.sum_norm_apply_le_norm`
* Renames `basis.op_norm_le` to `basis.exists_op_norm_le`
* Creates a new `basis.op_norm_le` stated without the existential
* Adds the `nnnorm` version of some `norm` lemmas. In some cases it's easier to prove these first, and derive the `norm` versions from them.

### [2022-04-25 05:10:33](https://github.com/leanprover-community/mathlib/commit/070c21b)
chore(data/matrix): generalisation linter ([#13655](https://github.com/leanprover-community/mathlib/pull/13655))

### [2022-04-25 04:29:05](https://github.com/leanprover-community/mathlib/commit/df4066c)
refactor(order/ideal): Make `order.ideal` extend `lower_set` ([#13070](https://github.com/leanprover-community/mathlib/pull/13070))
* Redefine `order.ideal` to extend `lower_set`.
* `set_like` instance
* Get rid of `order.ideal.ideal_Inter_nonempty` in favor of `order_bot`
* Make arguments to `order.ideal.sup_mem` semi-implicit
* Reorder sections according to typeclass assumptions (some were outdated since Yakov's `order_bot`/`order_top` refactor)

### [2022-04-25 03:54:20](https://github.com/leanprover-community/mathlib/commit/d4d5b6d)
chore(scripts): update nolints.txt ([#13679](https://github.com/leanprover-community/mathlib/pull/13679))
I am happy to remove some nolints for you!

### [2022-04-25 03:54:18](https://github.com/leanprover-community/mathlib/commit/65edf25)
feat(set_theory/game/pgame): `x.move_left i < x` and variants  ([#13654](https://github.com/leanprover-community/mathlib/pull/13654))

### [2022-04-25 01:54:43](https://github.com/leanprover-community/mathlib/commit/454b884)
chore(topology/metric_space/basic): golf an instance ([#13664](https://github.com/leanprover-community/mathlib/pull/13664))
Golf the proof of `prod.pseudo_metric_space_max` using
`pseudo_emetric_space.to_pseudo_metric_space_of_dist`.

### [2022-04-25 01:54:42](https://github.com/leanprover-community/mathlib/commit/9101c48)
docs(number_theory/sum_two_squares): Update docs ([#13593](https://github.com/leanprover-community/mathlib/pull/13593))
We add a remark for an alternate name for the theorem, and a todo note for a generalization of it.

### [2022-04-25 01:54:41](https://github.com/leanprover-community/mathlib/commit/045fc44)
docs(tactic/algebra): Module docstring ([#13571](https://github.com/leanprover-community/mathlib/pull/13571))
Write the module docstring.

### [2022-04-25 00:39:20](https://github.com/leanprover-community/mathlib/commit/54d1ddd)
feat(algebra/polynomial/big_operators): add a lemma, reduce assumptions, golf ([#13264](https://github.com/leanprover-community/mathlib/pull/13264))

### [2022-04-24 20:37:26](https://github.com/leanprover-community/mathlib/commit/0d16bb4)
refactor(*): migrate from `filter.lift' _ powerset` to `filter.small_sets` ([#13673](https://github.com/leanprover-community/mathlib/pull/13673))

### [2022-04-24 17:23:52](https://github.com/leanprover-community/mathlib/commit/53a484e)
chore(order/filter/small_sets): redefine, golf ([#13672](https://github.com/leanprover-community/mathlib/pull/13672))
The new definition is defeq to the old one.

### [2022-04-24 13:05:30](https://github.com/leanprover-community/mathlib/commit/42b9cdf)
feat(data/quot): Decidability of `quotient.lift` and friends ([#13589](https://github.com/leanprover-community/mathlib/pull/13589))
and make `antisymmetrization.linear_order` computable.

### [2022-04-24 11:06:15](https://github.com/leanprover-community/mathlib/commit/63da426)
refactor(linear_algebra/dimension): further generalisations to division_ring ([#13657](https://github.com/leanprover-community/mathlib/pull/13657))

### [2022-04-24 08:21:40](https://github.com/leanprover-community/mathlib/commit/8126255)
feat(set_theory/surreal/basic): Definitional characterization of `numeric` ([#13653](https://github.com/leanprover-community/mathlib/pull/13653))

### [2022-04-24 06:52:55](https://github.com/leanprover-community/mathlib/commit/e006f38)
feat(algebra/hom/iterate): Iterating an action ([#13659](https://github.com/leanprover-community/mathlib/pull/13659))
This PR adds `smul_iterate`, generalizing  `mul_left_iterate` and `mul_right_iterate`.

### [2022-04-24 04:20:58](https://github.com/leanprover-community/mathlib/commit/b8b8bf3)
refactor(category_theory/monoidal): prove coherence lemmas by coherence ([#13406](https://github.com/leanprover-community/mathlib/pull/13406))
Now that we have a basic monoidal coherence tactic, we can replace some boring proofs of particular coherence lemmas with `by coherence`.
I've also simply deleted a few lemmas which are not actually used elsewhere in mathlib, and can be proved `by coherence`.

### [2022-04-24 02:22:31](https://github.com/leanprover-community/mathlib/commit/92ca136)
feat(set_theory/game/pgame): Birthdays of pre-games ([#13636](https://github.com/leanprover-community/mathlib/pull/13636))

### [2022-04-24 02:22:30](https://github.com/leanprover-community/mathlib/commit/5998b49)
chore(order/filter/basic): golf 2 proofs ([#13614](https://github.com/leanprover-community/mathlib/pull/13614))

### [2022-04-24 02:22:28](https://github.com/leanprover-community/mathlib/commit/946f253)
chore(set_theory/game/pgame): Cleanup ([#13612](https://github.com/leanprover-community/mathlib/pull/13612))
We remove redundant parentheses, and make arguments explicit when they can't be inferred.

### [2022-04-24 02:22:27](https://github.com/leanprover-community/mathlib/commit/b0552c1)
docs(tactic/lint/default): Module docstring ([#13570](https://github.com/leanprover-community/mathlib/pull/13570))
Write the module docstring.

### [2022-04-24 00:36:50](https://github.com/leanprover-community/mathlib/commit/2d0ff32)
chore(algebra/*): move function instances ([#13650](https://github.com/leanprover-community/mathlib/pull/13650))
These should have been much earlier, but I put them in their current places to avoid large build times in what was an already large refactor.

### [2022-04-23 22:43:27](https://github.com/leanprover-community/mathlib/commit/cc406db)
feat(algebra/ring/basic): generalisation linter suggestions ([#13649](https://github.com/leanprover-community/mathlib/pull/13649))

### [2022-04-23 22:43:26](https://github.com/leanprover-community/mathlib/commit/1abfde6)
chore(group_theory/exponent): generalise ([#13647](https://github.com/leanprover-community/mathlib/pull/13647))
Generalises a few lemmas to not require cancellativity.

### [2022-04-23 22:43:25](https://github.com/leanprover-community/mathlib/commit/34b1cfd)
feat(set_theory/game/pgame): Strengthen `move_{left/right}_mk` ([#13646](https://github.com/leanprover-community/mathlib/pull/13646))

### [2022-04-23 22:43:24](https://github.com/leanprover-community/mathlib/commit/44a05db)
fix(topology/algebra/matrix): correct a lemma name ([#13640](https://github.com/leanprover-community/mathlib/pull/13640))

### [2022-04-23 21:10:27](https://github.com/leanprover-community/mathlib/commit/09eb35f)
feat(data/part): add get_or_else_of_dom ([#13588](https://github.com/leanprover-community/mathlib/pull/13588))
Adds a lemma

### [2022-04-23 09:50:22](https://github.com/leanprover-community/mathlib/commit/afd8a52)
feat(order/hom/basic): add simp lemmas for `strict_mono.order_iso` and friends ([#13606](https://github.com/leanprover-community/mathlib/pull/13606))
Formalized as part of the Sphere Eversion project.

### [2022-04-23 05:39:49](https://github.com/leanprover-community/mathlib/commit/8c262da)
chore(analysis/normed_space/ray): golf ([#13629](https://github.com/leanprover-community/mathlib/pull/13629))
Golf 2 proofs

### [2022-04-23 05:39:48](https://github.com/leanprover-community/mathlib/commit/4ad7dc9)
chore(algebra/ring/equiv): protect ring equiv lemmas for big operators ([#13624](https://github.com/leanprover-community/mathlib/pull/13624))

### [2022-04-23 05:39:47](https://github.com/leanprover-community/mathlib/commit/fe435de)
feat(algebra/algebra/basic,analysis/normed_space/basic): The zero ring is a (normed) algebra ([#13618](https://github.com/leanprover-community/mathlib/pull/13618))
This instance probably isn't very useful, but it's nice to have in the docs as an example of what `normed_algebra` permits.

### [2022-04-23 05:39:45](https://github.com/leanprover-community/mathlib/commit/0bea7a0)
feat(set_theory/pgame): Lemmas about order and left/right moves ([#13590](https://github.com/leanprover-community/mathlib/pull/13590))

### [2022-04-23 04:08:28](https://github.com/leanprover-community/mathlib/commit/26b2d72)
feat(set_theory/game/pgame): Empty instances ([#13635](https://github.com/leanprover-community/mathlib/pull/13635))

### [2022-04-23 04:08:27](https://github.com/leanprover-community/mathlib/commit/94f970a)
feat(linear_algebra/basic): add a simp lemma for comp_right ([#13625](https://github.com/leanprover-community/mathlib/pull/13625))

### [2022-04-23 04:08:26](https://github.com/leanprover-community/mathlib/commit/b62b531)
doc(analysis/normed_space/basic): Explain how to use non-unital normed algebras ([#13605](https://github.com/leanprover-community/mathlib/pull/13605))
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20Is.20the.20zero.20algebra.20normed.3F/near/279555566)

### [2022-04-23 03:26:36](https://github.com/leanprover-community/mathlib/commit/79ea30c)
chore(scripts): update nolints.txt ([#13637](https://github.com/leanprover-community/mathlib/pull/13637))
I am happy to remove some nolints for you!

### [2022-04-22 23:37:56](https://github.com/leanprover-community/mathlib/commit/9923362)
doc(measure_theory): add some missing `to_additive` docstrings ([#13456](https://github.com/leanprover-community/mathlib/pull/13456))

### [2022-04-22 22:31:59](https://github.com/leanprover-community/mathlib/commit/976c544)
feat(algebra/order/archimedean): Comparing with rationals determines the order ([#13602](https://github.com/leanprover-community/mathlib/pull/13602))
In a linear ordered field, if `q < x → q ≤ y` for all `q : ℚ`, then `x ≤ y`, and similar results.

### [2022-04-22 22:31:58](https://github.com/leanprover-community/mathlib/commit/b98bd41)
feat(topology/uniform_space/matrix): Add the uniform_space structure on matrices ([#13534](https://github.com/leanprover-community/mathlib/pull/13534))

### [2022-04-22 20:06:20](https://github.com/leanprover-community/mathlib/commit/4547076)
chore(*): use zero_lt_two/two_ne_zero lemmas more ([#13609](https://github.com/leanprover-community/mathlib/pull/13609))

### [2022-04-22 20:06:19](https://github.com/leanprover-community/mathlib/commit/9eb3858)
feat(combinatorics/pigeonhole): Pigeons in linear commutative rings ([#13308](https://github.com/leanprover-community/mathlib/pull/13308))
Duplicate almost all the pigeonhole principle API to work in `linear_ordered_comm_ring`s.

### [2022-04-22 20:06:18](https://github.com/leanprover-community/mathlib/commit/7be21e0)
feat(topology/algebra/group): quotient by a closed subgroup is regular ([#13278](https://github.com/leanprover-community/mathlib/pull/13278))

### [2022-04-22 20:06:16](https://github.com/leanprover-community/mathlib/commit/ad3e667)
feat(order/chain): Flags ([#13089](https://github.com/leanprover-community/mathlib/pull/13089))
Define the type of maximal chains, aka flags, of an order.

### [2022-04-22 18:15:50](https://github.com/leanprover-community/mathlib/commit/9c3cb72)
feat(data/int/basic): Add unit lemmas ([#13565](https://github.com/leanprover-community/mathlib/pull/13565))
This PR adds a few more unit lemmas, and cleans up some of the proofs.

### [2022-04-22 18:15:49](https://github.com/leanprover-community/mathlib/commit/695e0b7)
feat(analysis/convex/strict_convex_space): Verify strict convexity from fixed scalars ([#13548](https://github.com/leanprover-community/mathlib/pull/13548))
Prove that `∀ x y : E, ∥x∥ ≤ 1 → ∥y∥ ≤ 1 → x ≠ y → ∥a • x + b • y∥ < 1` for **fixed** `a` and `b` is enough for `E` to be a strictly convex space.

### [2022-04-22 18:15:48](https://github.com/leanprover-community/mathlib/commit/2e83d61)
feat(topology/metric_space/hausdorff_distance): Thickening the closure ([#13515](https://github.com/leanprover-community/mathlib/pull/13515))
`thickening δ (closure s) = thickening δ s` and other simple lemmas. Also rename `inf_edist_le_inf_edist_of_subset` to `inf_edist_anti` and make arguments to `mem_thickening_iff` implicit.

### [2022-04-22 15:16:45](https://github.com/leanprover-community/mathlib/commit/355d68a)
chore(ring_theory/roots_of_unity): primitive roots are not zero ([#13587](https://github.com/leanprover-community/mathlib/pull/13587))

### [2022-04-22 15:16:44](https://github.com/leanprover-community/mathlib/commit/79ac4c8)
chore(data/polynomial/degree/definitions): simplify sum_fin, degree_C_le ([#13564](https://github.com/leanprover-community/mathlib/pull/13564))

### [2022-04-22 15:16:42](https://github.com/leanprover-community/mathlib/commit/a74df9b)
feat(number_theory/legendre_symbol): add file quadratic_char.lean ([#13503](https://github.com/leanprover-community/mathlib/pull/13503))
This adds the file `quadratic_char.lean` in `number_theory/legendre_symbol/`.
This file contains (apart from some more general stuff on finite fields that is useful for what is done in the file) the definition of the quadratic character on a finite field `F` (with values in the integers) and a number of statements of properties.
It also defines quadratic characters on `zmod 4` and `zmod 8` that will be useful for the supplements to the law of quadratic reciprocity.

### [2022-04-22 12:15:36](https://github.com/leanprover-community/mathlib/commit/631890b)
chore(data/rat/basic): tidy some proofs ([#13603](https://github.com/leanprover-community/mathlib/pull/13603))

### [2022-04-22 12:15:35](https://github.com/leanprover-community/mathlib/commit/f7dac5e)
feat(logic/basic): add `auto_param.out` and `opt_param.out` ([#13599](https://github.com/leanprover-community/mathlib/pull/13599))

### [2022-04-22 12:15:34](https://github.com/leanprover-community/mathlib/commit/6729cca)
feat(set_theory/game/pgame): simp + private ([#13596](https://github.com/leanprover-community/mathlib/pull/13596))

### [2022-04-22 12:15:32](https://github.com/leanprover-community/mathlib/commit/62205c2)
refactor(data/nat/factorization): Infer arguments ([#13595](https://github.com/leanprover-community/mathlib/pull/13595))

### [2022-04-22 11:41:15](https://github.com/leanprover-community/mathlib/commit/9abfff3)
chore(analysis/inner_product_space/lax_milgram): tidy some proofs ([#13604](https://github.com/leanprover-community/mathlib/pull/13604))

### [2022-04-22 08:34:36](https://github.com/leanprover-community/mathlib/commit/3d24b09)
feat(algebra/ring/basic): define non-unital ring homs ([#13430](https://github.com/leanprover-community/mathlib/pull/13430))
This defines a new bundled hom type and associated class for non-unital (even non-associative) (semi)rings. The associated notation introduced for these homs is `α →ₙ+* β` to parallel the `ring_hom` notation `α →+* β`, where `ₙ` stands for "non-unital".

### [2022-04-22 06:47:42](https://github.com/leanprover-community/mathlib/commit/394dec3)
feat(order/filter/small_sets): define the filter of small sets ([#13467](https://github.com/leanprover-community/mathlib/pull/13467))
* Main author is @PatrickMassot 
* From the sphere eversion project
* Required for convolutions
Co-authored by: Patrick Massot <patrick.massot@u-psud.fr>

### [2022-04-22 06:47:41](https://github.com/leanprover-community/mathlib/commit/9db5916)
fix(data/fintype/basic): fix `fintype_of_option_equiv` ([#13466](https://github.com/leanprover-community/mathlib/pull/13466))
A type is a `fintype` if its successor (using `option`) is a `fintype`
This fixes an error introduced in [#13086](https://github.com/leanprover-community/mathlib/pull/13086).

### [2022-04-22 06:47:40](https://github.com/leanprover-community/mathlib/commit/0d77f29)
feat(analysis/calculus/specific_functions): define normed bump functions ([#13463](https://github.com/leanprover-community/mathlib/pull/13463))
* Normed bump functions have integral 1 w.r.t. the specified measure.
* Also add a few more properties of bump functions, including its smoothness in all arguments (including midpoint and the two radii).
* From the sphere eversion project
* Required for convolutions

### [2022-04-22 06:47:39](https://github.com/leanprover-community/mathlib/commit/06a6044)
feat(analysis/normed_space/exponential): Weaken typeclass requirements ([#13444](https://github.com/leanprover-community/mathlib/pull/13444))
This allows the exponential to be defined independently of a choice of norm.

### [2022-04-22 04:34:08](https://github.com/leanprover-community/mathlib/commit/2b902eb)
chore(scripts): update nolints.txt ([#13597](https://github.com/leanprover-community/mathlib/pull/13597))
I am happy to remove some nolints for you!

### [2022-04-22 04:34:07](https://github.com/leanprover-community/mathlib/commit/79bc6ad)
feat(data/mv_polynomial/equiv): API for `mv_polynomial.fin_succ_equiv` ([#10812](https://github.com/leanprover-community/mathlib/pull/10812))
This PR provides API for `mv_polynomial.fin_succ_equiv`: coefficients, degree, coefficientes of coefficients, degree_of of coefficients, etc.
To state and prove these lemmas I had to define `cons` and `tail` for maps `fin (n+1) →₀ M` and prove the usual properties for these. I'm not sure if this is necessary or the correct approach to do this.

### [2022-04-22 01:34:22](https://github.com/leanprover-community/mathlib/commit/17d2424)
feat(polynomial/cyclotomic): `eval_apply` ([#13586](https://github.com/leanprover-community/mathlib/pull/13586))

### [2022-04-22 01:34:21](https://github.com/leanprover-community/mathlib/commit/40fc58c)
feat(data/quot): `quotient.out` is injective ([#13584](https://github.com/leanprover-community/mathlib/pull/13584))

### [2022-04-22 01:34:20](https://github.com/leanprover-community/mathlib/commit/821e7c8)
doc(category_theory/limits/has_limits): fix two docstrings ([#13581](https://github.com/leanprover-community/mathlib/pull/13581))

### [2022-04-22 01:34:19](https://github.com/leanprover-community/mathlib/commit/7b92db7)
chore(set_theory/cardinal/basic): Fix spacing ([#13562](https://github.com/leanprover-community/mathlib/pull/13562))

### [2022-04-22 01:34:17](https://github.com/leanprover-community/mathlib/commit/1da12b5)
fix(analysis/normed_space/basic): allow the zero ring to be a normed algebra ([#13544](https://github.com/leanprover-community/mathlib/pull/13544))
This replaces `norm_algebra_map_eq : ∀ x : 𝕜, ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥` with `norm_smul_le : ∀ (r : 𝕜) (x : 𝕜'), ∥r • x∥ ≤ ∥r∥ * ∥x∥` in `normed_algebra`. With this change, `normed_algebra` means nothing more than "a normed module that is also an algebra", which seems to be the only notion actually used in mathlib anyway. In practice, this change really just removes any constraints on `∥1∥`.
The old meaning of `[normed_algebra R A]` is now achieved with `[normed_algebra R A] [norm_one_class A]`.
As a result, lemmas like `normed_algebra.norm_one_class` and `normed_algebra.nontrivial` have been removed, as they no longer make sense now that the two typeclasses are entirely orthogonal.
Notably this means that the following `normed_algebra` instances hold more generally than before:
* `continuous_linear_map.to_normed_algebra`
* `pi.normed_algebra`
* `bounded_continuous_function.normed_algebra`
* `continuous_map.normed_algebra`
* Instances not yet in mathlib:
  * Matrices under the `L1-L_inf` norm are a normed algebra even if the matrix is empty
  * Matrices under the frobenius norm are a normed algebra (note `∥(1 : matrix n n 𝕜')∥ = \sqrt (fintype.card n)` with that norm)
This last one is the original motivation for this PR; otherwise every lemma about a matrix exponential has to case on whether the matrices are empty.
It is possible that some of the `[norm_one_class A]`s added in `spectrum.lean` are unnecessary; however, the assumptions are no stronger than they were before, and I'm not interested in trying to generalize them as part of this PR.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Is.20the.20zero.20algebra.20normed.3F/near/279515954)

### [2022-04-22 01:34:16](https://github.com/leanprover-community/mathlib/commit/77236cd)
refactor(category_theory): make has_zero_object a Prop  ([#13517](https://github.com/leanprover-community/mathlib/pull/13517))

### [2022-04-22 01:34:15](https://github.com/leanprover-community/mathlib/commit/dced133)
feat(group_theory/group_action/basic): Right multiplication satisfies the `quotient_action` axiom ([#13475](https://github.com/leanprover-community/mathlib/pull/13475))
This PR adds a `quotient_action` instance for right multiplication.

### [2022-04-22 01:34:14](https://github.com/leanprover-community/mathlib/commit/bb9d1c5)
chore(*): remove `subst` when not necessary ([#13453](https://github.com/leanprover-community/mathlib/pull/13453))
Where possible, this replaces `subst` with `obtain rfl` (which is equivalent to `have` and then `subst`, golfing a line).
This also tidies some non-terminal `simp`s.

### [2022-04-21 23:36:55](https://github.com/leanprover-community/mathlib/commit/afb4392)
feat(linear_algebra/prod): two lemmas about prod_map ([#13572](https://github.com/leanprover-community/mathlib/pull/13572))

### [2022-04-21 23:36:54](https://github.com/leanprover-community/mathlib/commit/d444a27)
feat(group_theory/transfer): Define the transfer homomorphism ([#13446](https://github.com/leanprover-community/mathlib/pull/13446))
This PR adds a definition of the transfer homomorphism.

### [2022-04-21 23:36:53](https://github.com/leanprover-community/mathlib/commit/b1a1ece)
feat(ring_theory/valuation/valuation_subring): The order structure on valuation subrings of a field ([#13429](https://github.com/leanprover-community/mathlib/pull/13429))
This PR shows that for a valuation subring `R` of a field `K`, the coarsenings of `R` are in (anti)ordered bijections with the prime ideals of `R`. As a corollary, the collection of such coarsenings is totally ordered.

### [2022-04-21 23:36:51](https://github.com/leanprover-community/mathlib/commit/1e76b9e)
feat(topology/constructions): more convenient lemmas ([#13423](https://github.com/leanprover-community/mathlib/pull/13423))
* Define `continuous.fst'` and friends and `continuous.comp₂` and friends for convenience (and to help with elaborator issues)
* Cleanup in `topology/constructions`
* Define `set.preimage_inl_image_inr` and `set.preimage_inr_image_inl` and prove the `range` versions in terms of these. This required reordering some lemmas (moving general lemmas about `range` above the lemmas of interactions with `range` and specific functions).
* From the sphere eversion project

### [2022-04-21 23:36:50](https://github.com/leanprover-community/mathlib/commit/63ee558)
feat(algebra/big_operators): split products and sums over fin (a+b) ([#13291](https://github.com/leanprover-community/mathlib/pull/13291))

### [2022-04-21 23:36:49](https://github.com/leanprover-community/mathlib/commit/4d7683b)
feat(group_theory/torsion): torsion-free groups and quotients by torsion subgroups ([#13173](https://github.com/leanprover-community/mathlib/pull/13173))

### [2022-04-21 23:36:48](https://github.com/leanprover-community/mathlib/commit/e728cfd)
feat(order/grade): Graded orders ([#11308](https://github.com/leanprover-community/mathlib/pull/11308))
Define graded orders. To be the most general, we use `is_min`/`is_max` rather than `order_bot`/`order_top`. A grade is a function that respects the covering relation and eventually minimality/maximality.

### [2022-04-21 23:36:46](https://github.com/leanprover-community/mathlib/commit/8110ab9)
feat(number_theory/modular): fundamental domain part 2 ([#8985](https://github.com/leanprover-community/mathlib/pull/8985))
This completes the argument that the standard open domain `{z : |z|>1, |\Re(z)|<1/2}` is a fundamental domain for the action of `SL(2,\Z)` on `\H`. The first PR ([#8611](https://github.com/leanprover-community/mathlib/pull/8611)) showed that every point in the upper half plane has a representative inside its closure, and here we show that representatives in the open domain are unique.

### [2022-04-21 20:30:58](https://github.com/leanprover-community/mathlib/commit/ba556a7)
chore(algebra/algebra/spectrum): lemmas about the zero ring ([#13568](https://github.com/leanprover-community/mathlib/pull/13568))

### [2022-04-21 20:30:57](https://github.com/leanprover-community/mathlib/commit/8145333)
ci(gitpod): update leanproject version ([#13567](https://github.com/leanprover-community/mathlib/pull/13567))

### [2022-04-21 20:30:56](https://github.com/leanprover-community/mathlib/commit/aeef727)
chore(set_theory/ordinal/basic): Small style tweaks ([#13561](https://github.com/leanprover-community/mathlib/pull/13561))

### [2022-04-21 20:30:55](https://github.com/leanprover-community/mathlib/commit/efab188)
refactor(group_theory/{submonoid, subsemigroup}/basic): move `mul_mem_class` ([#13559](https://github.com/leanprover-community/mathlib/pull/13559))
This moves `mul_mem_class` (and `add_mem_class`) from `group_theory/submonoid/basic` to `group_theory/subsemigroup/basic` so that `subsemigroup` can be an instance. We then protect `subsemigroup.mul_mem`. In addition, we add an induction principle for binary predicates to better parallel `group_theory/submonoid/basic`.

### [2022-04-21 20:30:54](https://github.com/leanprover-community/mathlib/commit/afe1421)
feat(data/nat/pow): add theorem `nat.pow_mod` ([#13551](https://github.com/leanprover-community/mathlib/pull/13551))
Add theorem that states `∀ (a b n : ℕ) : a ^ b % n = (a % n) ^ b % n`.

### [2022-04-21 20:30:53](https://github.com/leanprover-community/mathlib/commit/090e59d)
feat(analysis/normed_space/operator_norm): norm of `lsmul` ([#13538](https://github.com/leanprover-community/mathlib/pull/13538))
* From the sphere eversion project
* Required for convolutions

### [2022-04-21 20:30:51](https://github.com/leanprover-community/mathlib/commit/8430aae)
feat(algebra/group_power/lemmas): More lemmas through `to_additive` ([#13537](https://github.com/leanprover-community/mathlib/pull/13537))
Use `to_additive` to generate a bunch of old `nsmul`/`zsmul` lemmas from new `pow`/`zpow` ones. Also protect `nat.nsmul_eq_mul` as it should have been.

### [2022-04-21 20:30:50](https://github.com/leanprover-community/mathlib/commit/08323cd)
feat(data/real/ennreal): `tsub` lemmas ([#13525](https://github.com/leanprover-community/mathlib/pull/13525))
Inherit lemmas about subtraction on `ℝ≥0∞` from `algebra.order.sub`. Generalize `add_le_cancellable.tsub_lt_self` in passing.
New `ennreal` lemmas

### [2022-04-21 20:30:49](https://github.com/leanprover-community/mathlib/commit/3a06179)
refactor(category_theory): reverse simp lemmas about (co)forks ([#13519](https://github.com/leanprover-community/mathlib/pull/13519))
Makes `fork.ι` instead of `t.π.app zero` so that we avoid any unnecessary references to `walking_parallel_pair` in (co)fork  homs. This induces quite a lot of changes in other files, but I think it's worth the pain. The PR also changes `fork.is_limit.mk` to avoid stating redundant morphisms.

### [2022-04-21 17:29:16](https://github.com/leanprover-community/mathlib/commit/b7cba57)
chore(set_theory/game/*): Protect ambiguous lemmas ([#13557](https://github.com/leanprover-community/mathlib/pull/13557))
Protect `pgame.neg_zero` and inline `pgame.add_le_add_left` and friends into `covariant_class` instances.

### [2022-04-21 17:29:14](https://github.com/leanprover-community/mathlib/commit/b6c96ef)
feat(combinatorics/simple_graph/clique): Clique-free graphs ([#13552](https://github.com/leanprover-community/mathlib/pull/13552))
... and the finset of cliques of a finite graph.

### [2022-04-21 17:29:13](https://github.com/leanprover-community/mathlib/commit/e49ac91)
feat(analysis/calculus/cont_diff): add more prod lemmas ([#13521](https://github.com/leanprover-community/mathlib/pull/13521))
* Add `cont_diff.fst`, `cont_diff.comp₂`, `cont_diff_prod_mk_left` and many variants.
* From the sphere eversion project
* Required for convolutions
* PR [#13423](https://github.com/leanprover-community/mathlib/pull/13423) is similar for continuity

### [2022-04-21 17:29:12](https://github.com/leanprover-community/mathlib/commit/62b3333)
chore(algebra/star/chsh): `repeat`ed golf ([#13499](https://github.com/leanprover-community/mathlib/pull/13499))
Instead of having a real Gröbner tactic, we can leverage a loop of `ring, simp` to reach a goal.

### [2022-04-21 17:29:11](https://github.com/leanprover-community/mathlib/commit/777d1ec)
feat(measure_theory/measure/measure_space): add some lemmas for the counting measure ([#13485](https://github.com/leanprover-community/mathlib/pull/13485))

### [2022-04-21 17:29:10](https://github.com/leanprover-community/mathlib/commit/6490ee3)
feat(topology/instances/ennreal): Add lemmas about continuity of ennreal subtraction. ([#13448](https://github.com/leanprover-community/mathlib/pull/13448))
`ennreal` does not have continuous `sub`. This PR adds `ennreal.continuous_on_sub` and related lemmas, which give the continuity of the subtraction in more restricted/specialized setups.

### [2022-04-21 15:20:01](https://github.com/leanprover-community/mathlib/commit/91cbe46)
feat(algebra/monoid_algebra/basic): lifts of (add_)monoid_algebras ([#13382](https://github.com/leanprover-community/mathlib/pull/13382))
We show that homomorphisms of the grading (add) monoids of (add) monoid algebras lift to ring/algebra homs of the algebras themselves.
This PR is preparation for introducing Laurent polynomials (see [adomani_laurent_polynomials](https://github.com/leanprover-community/mathlib/tree/adomani_laurent_polynomials), file `data/polynomial/laurent` for a preliminary version).
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Laurent.20polynomials)

### [2022-04-21 15:19:59](https://github.com/leanprover-community/mathlib/commit/8044794)
feat(topology/algebra/module/basic): continuous linear maps are automatically uniformly continuous ([#13276](https://github.com/leanprover-community/mathlib/pull/13276))
Generalize `continuous_linear_map.uniform_continuous`, `continuous_linear_equiv.uniform_embedding` and `linear_equiv.uniform_embedding` form `normed_space`s to `uniform_add_group`s and move them to `topology/algebra/module/basic`.

### [2022-04-21 15:19:58](https://github.com/leanprover-community/mathlib/commit/79abf67)
fix(tactic/apply_rules): separate single rules and attribute names in syntax ([#13227](https://github.com/leanprover-community/mathlib/pull/13227))
@hrmacbeth reported an issue with `apply_rules` [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/monotonicity.2Eattr.20with.20apply_rules). It boiled down to `apply_rules` not properly distinguishing between attribute names, the names of `user_attribute` declarations, and the names of normal declarations. There's an example of using `apply_rules` with attributes in the docs:
```lean
@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }
local attribute [mono_rules] add_le_add
example (a b c d : α) : a + b ≤ c + d :=
begin
  apply_rules mono_rules, -- takes action
end
```
but this only worked by coincidence because the attribute name and the name of the `user_attribute` declaration were the same.
With this change, expressions and names of attributes are now separated: the latter are specified after `with`. The call above becomes `apply_rules with mono_rules`. This mirrors the syntax of `simp`. Note that this feature was only used in meta code in mathlib.
The example from Zulip (modified for proper syntax) still doesn't work with my change:
```lean
import tactic.monotonicity
variables {α : Type*} [linear_ordered_add_comm_group α]
example (a b c d : α) : a + b ≤ c + d :=
begin
  apply_rules with mono,
end
```
but it seems to fail because the `mono` rules cause `apply_rules` to loop -- that is, the rule set is getting applied correctly.

### [2022-04-21 15:19:56](https://github.com/leanprover-community/mathlib/commit/e8b581a)
feat(order/countable_dense_linear_order): Relax conditions of `embedding_from_countable_to_dense` ([#12928](https://github.com/leanprover-community/mathlib/pull/12928))
We prove that any countable order embeds in any nontrivial dense order. We also slightly golf the rest of the file.

### [2022-04-21 12:10:04](https://github.com/leanprover-community/mathlib/commit/0f9edf9)
feat(data/set/[basic|prod]): make `×ˢ` bind more strongly, and define `mem.out` ([#13422](https://github.com/leanprover-community/mathlib/pull/13422))
* This means that  `×ˢ` does not behave the same as `∪` or `∩` around `⁻¹'` or `''`, but I think that is fine.
* From the sphere eversion project

### [2022-04-21 12:10:02](https://github.com/leanprover-community/mathlib/commit/c956647)
feat(order/basic): Simple shortcut lemmas ([#13421](https://github.com/leanprover-community/mathlib/pull/13421))
Add convenience lemmas to make the API a bit more symmetric and easier to translate between `transitive` and `is_trans`. Also rename `_ge'` to `_le` in lemmas and fix the `is_max_` aliases.

### [2022-04-21 12:10:00](https://github.com/leanprover-community/mathlib/commit/22c4291)
chore(number_theory/dioph): Cleanup ([#13403](https://github.com/leanprover-community/mathlib/pull/13403))
Clean up, including:
* Move prerequisites to the correct files
* Make equalities in `poly` operations defeq
* Remove defeq abuse around `set`
* Slightly golf proofs by tweaking explicitness of lemma arguments
Renames

### [2022-04-21 12:09:59](https://github.com/leanprover-community/mathlib/commit/e5f8236)
feat(analysis/normed_space/exponential): ring homomorphisms are preserved by the exponential ([#13402](https://github.com/leanprover-community/mathlib/pull/13402))
The new results here are:
* `prod.fst_exp`
* `prod.snd_exp`
* `exp_units_conj`
* `exp_conj`
* `map_exp`
* `map_exp_of_mem_ball`
This last lemma does all the heavy lifting, and also lets us golf `algebra_map_exp_comm`.
This doesn't bother to duplicate the rest of these lemmas for the `*_of_mem_ball` version, since the proofs are trivial and those lemmas probably wouldn't be used.
This also generalizes some of the lemmas about infinite sums to work with `add_monoid_hom_class`.

### [2022-04-21 12:09:58](https://github.com/leanprover-community/mathlib/commit/0821eef)
feat(algebraic_geometry/projective_spectrum): degree zero part of a localized ring ([#13398](https://github.com/leanprover-community/mathlib/pull/13398))
If we have a graded ring A and some element f of A, the the localised ring A away from f has a degree zero part. This construction is useful because proj locally is spec of degree zero part of some localised ring.
Perhaps this ring belongs to some other file or different name, suggestions are very welcome

### [2022-04-21 12:09:57](https://github.com/leanprover-community/mathlib/commit/f1091b3)
feat(set_theory/cardinal): A set of cardinals is small iff it's bounded ([#13373](https://github.com/leanprover-community/mathlib/pull/13373))
We move `mk_subtype_le` and `mk_set_le` earlier within the file in order to better accomodate for the new result, `bdd_above_iff_small`.  We need this result right above the `Sup` stuff, as we'll make heavy use of it in a following refactor for `cardinal.sup`.

### [2022-04-21 12:09:56](https://github.com/leanprover-community/mathlib/commit/c30131f)
feat(data/polynomial/{derivative, iterated_deriv}): reduce assumptions ([#13368](https://github.com/leanprover-community/mathlib/pull/13368))

### [2022-04-21 12:09:55](https://github.com/leanprover-community/mathlib/commit/761801f)
feat(algebra/monoid_algebra/grading): Use the new graded_algebra API ([#13360](https://github.com/leanprover-community/mathlib/pull/13360))
This removes `to_grades_by` and `of_grades_by`, and prefers `graded_algebra.decompose` as the canonical spelling.
This might undo some of the performance improvements in [#13169](https://github.com/leanprover-community/mathlib/pull/13169), but it's not clear where to apply the analogous changes here, or whether they're really needed any more anyway,

### [2022-04-21 12:09:54](https://github.com/leanprover-community/mathlib/commit/5c2088e)
feat(algebra/group/to_additive): let @[to_additive] mimic alias’s docstrings ([#13330](https://github.com/leanprover-community/mathlib/pull/13330))
many of our `nolint.txt` entires are due to code of this shape:
    @[to_additive add_foo]
    lemma foo := .. /- no docstring -/
    alias foo <- bar
    attribute [to_additive add_bar] bar
where now `bar` has a docstring (from `alias`), but `bar_add` does not.
This PR makes `to_additive` detect that `bar` is an alias, and unless an 
explicit docstring is passed to `to_additive`, creates an “alias of add_foo”
docstring.

### [2022-04-21 12:09:53](https://github.com/leanprover-community/mathlib/commit/7d61199)
feat(set_theory/cofinality): Basic fundamental sequences ([#13326](https://github.com/leanprover-community/mathlib/pull/13326))

### [2022-04-21 12:09:51](https://github.com/leanprover-community/mathlib/commit/ba455ea)
feat(special_functions/pow): continuity of real to complex power ([#13244](https://github.com/leanprover-community/mathlib/pull/13244))
Some lemmas excised from my Gamma-function project. The main result is that for a complex `s` with `re s > 0`, the function `(λ x, x ^ s : ℝ → ℂ)` is continuous on all of `ℝ`.

### [2022-04-21 12:09:50](https://github.com/leanprover-community/mathlib/commit/cf3b996)
feat(group_theory/torsion): extension closedness, and torsion scalars in modules ([#13172](https://github.com/leanprover-community/mathlib/pull/13172))
Co-authored by: Alex J. Best <alex.j.best@gmail.com>

### [2022-04-21 12:09:49](https://github.com/leanprover-community/mathlib/commit/82ef19a)
feat(category_theory/path_category): canonical quotient of a path category ([#13159](https://github.com/leanprover-community/mathlib/pull/13159))

### [2022-04-21 12:09:48](https://github.com/leanprover-community/mathlib/commit/8261501)
refactor(number_theory/padics/padic_norm): Switch nat and rat definitions ([#12454](https://github.com/leanprover-community/mathlib/pull/12454))
Switches the order in which `padic_val_nat` and `padic_val_rat` are defined.
This PR has also expanded to add `padic_val_int` and some API lemmas for that.

### [2022-04-21 11:02:58](https://github.com/leanprover-community/mathlib/commit/21bbe90)
feat(analysis/normed): more lemmas about the sup norm on pi types and matrices ([#13536](https://github.com/leanprover-community/mathlib/pull/13536))
For now we name the matrix lemmas as `matrix.norm_*` and `matrix.nnnorm_*` to match `matrix.norm_le_iff` and `matrix.nnnorm_le_iff`.
We should consider renaming these in future to indicate which norm they refer to, but should probably deal with agreeing on a name in a separate PR.

### [2022-04-21 11:02:57](https://github.com/leanprover-community/mathlib/commit/b87e193)
fix(category_theory/monoidal): improve hygiene in coherence tactic ([#13507](https://github.com/leanprover-community/mathlib/pull/13507))

### [2022-04-21 11:02:56](https://github.com/leanprover-community/mathlib/commit/9f22a36)
feat(src/number_theory/cyclotomic/discriminant): add discr_prime_pow_ne_two ([#13465](https://github.com/leanprover-community/mathlib/pull/13465))
We add `discr_prime_pow_ne_two`, the discriminant of the `p^n`-th cyclotomic field.
From flt-regular

### [2022-04-21 08:48:23](https://github.com/leanprover-community/mathlib/commit/16ecb3d)
chore(algebra/group/type_tags): missing simp lemmas ([#13553](https://github.com/leanprover-community/mathlib/pull/13553))
To have `simps` generate these in an appropriate form, this inserts explicits coercions between the type synonyms.

### [2022-04-21 08:48:22](https://github.com/leanprover-community/mathlib/commit/839f508)
feat(measure_theory): allow measurability to prove ae_strongly_measurable ([#13427](https://github.com/leanprover-community/mathlib/pull/13427))
Adds `measurable.ae_strongly_measurable` to the `measurability` list

### [2022-04-21 06:55:01](https://github.com/leanprover-community/mathlib/commit/6012c21)
refactor(algebra/hom/group): generalize a few lemmas to `monoid_hom_class` ([#13447](https://github.com/leanprover-community/mathlib/pull/13447))
This generalizes a few lemmas to `monoid_hom_class` from `monoid_hom`. In particular, `monoid_hom.injective_iff` has been generalized and renamed to `injective_iff_map_eq_one`.
This also deletes `add_monoid_hom.injective_iff`, `ring_hom.injective_iff` and `alg_hom.injective_iff`. All of these are superseded by the generically applicable `injective_iff_map_eq_zero`.

### [2022-04-21 03:36:38](https://github.com/leanprover-community/mathlib/commit/e0f78ab)
chore(data/list/cycle): Add basic `simp` lemmas + minor golfing ([#13533](https://github.com/leanprover-community/mathlib/pull/13533))

### [2022-04-21 03:36:36](https://github.com/leanprover-community/mathlib/commit/2f1a4af)
feat(algebra/hom/non_unital_alg): introduce notation for non-unital algebra homomorphisms ([#13470](https://github.com/leanprover-community/mathlib/pull/13470))
This introduces the notation `A →ₙₐ[R] B` for `non_unital_alg_hom R A B` to mirror that of `non_unital_ring_hom R S` as `R →ₙ+* S` from [#13430](https://github.com/leanprover-community/mathlib/pull/13430). Here, the `ₙ` stands for "non-unital".

### [2022-04-21 01:41:41](https://github.com/leanprover-community/mathlib/commit/c93b99f)
chore(algebra/group/defs): Declare `field_simps` attribute earlier ([#13543](https://github.com/leanprover-community/mathlib/pull/13543))
Declaring `field_simps` earlier make the relevant lemmas taggable as they are declared.

### [2022-04-20 22:44:21](https://github.com/leanprover-community/mathlib/commit/b2518be)
feat(analysis/normed/normed_field): add `one_le_(nn)norm_one` for nontrivial normed rings ([#13556](https://github.com/leanprover-community/mathlib/pull/13556))

### [2022-04-20 22:44:20](https://github.com/leanprover-community/mathlib/commit/81c8f31)
refactor(analysis/calculus/cont_diff): reorder the file ([#13468](https://github.com/leanprover-community/mathlib/pull/13468))
* There are no functional changes in this PR (except the order of implicit arguments in some lemmas)
* This PR tries to move `cont_diff.comp` above some other lemmas. In a follow-up PR I will use this to add lemmas like `cont_diff.fst` which requires `cont_diff.comp`, but after this PR we can add it near `cont_diff_fst`.
* We also add `{m n : with_top ℕ}` as variables, so that we don't have to repeat this in every lemma

### [2022-04-20 21:15:06](https://github.com/leanprover-community/mathlib/commit/b86b927)
move(set_theory/*): Organize in folders ([#13530](https://github.com/leanprover-community/mathlib/pull/13530))
Create folders `cardinal`, `ordinal` and `game`. Most files under `set_theory` belong to a least one of them.

### [2022-04-20 20:40:18](https://github.com/leanprover-community/mathlib/commit/741d285)
chore(number_theory/zsqrtd/basic): simplify le_total proof ([#13555](https://github.com/leanprover-community/mathlib/pull/13555))

### [2022-04-20 18:42:11](https://github.com/leanprover-community/mathlib/commit/9d6d8c2)
feat(group_theory/perm/basic): Iterating a permutation is the same as taking a power ([#13554](https://github.com/leanprover-community/mathlib/pull/13554))

### [2022-04-20 18:42:10](https://github.com/leanprover-community/mathlib/commit/27a8328)
feat(data/real/sqrt): `sqrt x < y ↔ x < y^2` ([#13546](https://github.com/leanprover-community/mathlib/pull/13546))
Prove `real.sqrt_lt_iff` and generalize `real.lt_sqrt`.

### [2022-04-20 18:42:09](https://github.com/leanprover-community/mathlib/commit/242d687)
feat(algebra/hom/group and *): introduce `mul_hom M N` notation `M →ₙ* N` ([#13526](https://github.com/leanprover-community/mathlib/pull/13526))
The discussion and poll related to this new notation can be found in this [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/ring_hom.20notation.20and.20friends/near/279313301)

### [2022-04-20 17:09:57](https://github.com/leanprover-community/mathlib/commit/7bfaa5c)
feat(group_theory/schreier): Schreier's lemma in terms of `group.fg` and `group.rank` ([#13361](https://github.com/leanprover-community/mathlib/pull/13361))
This PR adds statements of Schreier's lemma in terms of `group.fg` and `group.rank`.

### [2022-04-20 17:09:56](https://github.com/leanprover-community/mathlib/commit/b0805a5)
feat(linear_algebra/trace): dual_tensor_hom is an equivalence + basis-free characterization of the trace ([#10372](https://github.com/leanprover-community/mathlib/pull/10372))

### [2022-04-20 16:01:13](https://github.com/leanprover-community/mathlib/commit/311ca72)
feat(order/filter/basic): allow functions between different types in lemmas about [co]map by a constant function ([#13542](https://github.com/leanprover-community/mathlib/pull/13542))

### [2022-04-20 14:05:05](https://github.com/leanprover-community/mathlib/commit/d79f6f3)
feat(data/finset/basic): simp `to_finset_eq_empty` ([#13531](https://github.com/leanprover-community/mathlib/pull/13531))

### [2022-04-20 12:56:15](https://github.com/leanprover-community/mathlib/commit/8ba7df8)
feat(topology/algebra/algebra): ℚ-scalar multiplication is continuous ([#13458](https://github.com/leanprover-community/mathlib/pull/13458))

### [2022-04-20 10:38:26](https://github.com/leanprover-community/mathlib/commit/a3a166b)
chore(model_theory/encoding): Improve the encoding of terms  ([#13532](https://github.com/leanprover-community/mathlib/pull/13532))
Makes it so that the encoding of terms no longer requires the assumption `inhabited (L.term A)`.
Adjusts following lemmas to use the `encoding` API more directly.

### [2022-04-20 10:38:25](https://github.com/leanprover-community/mathlib/commit/d9a8d6e)
feat(topology/separation): Finite sets in T2 spaces ([#12845](https://github.com/leanprover-community/mathlib/pull/12845))
We prove the following theorem: given a finite set in a T2 space, one can choose an open set around each point so that these are pairwise disjoint.

### [2022-04-20 10:04:20](https://github.com/leanprover-community/mathlib/commit/8d351dc)
feat(analysis/inner_product_space/gram_schmidt_ortho): Gram-Schmidt Orthogonalization and Orthonormalization ([#12857](https://github.com/leanprover-community/mathlib/pull/12857))
Formalize Gram-Schmidt Orthogonalization and Orthonormalization

### [2022-04-20 08:56:47](https://github.com/leanprover-community/mathlib/commit/92f6eb6)
chore(algebra/big_operators/fin): golf finset.prod_range ([#13535](https://github.com/leanprover-community/mathlib/pull/13535))

### [2022-04-19 23:26:34](https://github.com/leanprover-community/mathlib/commit/71b470f)
chore(analysis/normed_space/star): make an argument explicit ([#13523](https://github.com/leanprover-community/mathlib/pull/13523))

### [2022-04-19 20:26:49](https://github.com/leanprover-community/mathlib/commit/5038a4a)
feat(*): `op_op_op_comm` lemmas ([#13528](https://github.com/leanprover-community/mathlib/pull/13528))
A handful of lemmas of the form `op (op a b) (op c d) = op (op a c) (op b d)`.

### [2022-04-19 20:26:48](https://github.com/leanprover-community/mathlib/commit/cf5aea0)
chore(data/real/nnreal): add commuted version of `nnreal.mul_finset_sup` ([#13512](https://github.com/leanprover-community/mathlib/pull/13512))
Also make the argument explicit

### [2022-04-19 20:26:47](https://github.com/leanprover-community/mathlib/commit/094b1f5)
chore(*/matrix): order `m` and `n` alphabetically ([#13510](https://github.com/leanprover-community/mathlib/pull/13510))
In a few places this also reorders `(n) [fintype n] (m) [fintype m]` to `(m n) [fintype m] [fintype n]` which seems to be where we prefer to put typeclasses.

### [2022-04-19 19:41:21](https://github.com/leanprover-community/mathlib/commit/3ac979a)
feat(analysis/calculus/specific_functions): trivial extra lemmas ([#13516](https://github.com/leanprover-community/mathlib/pull/13516))

### [2022-04-19 17:41:07](https://github.com/leanprover-community/mathlib/commit/70759ef)
feat(analysis): lemmas about nnnorm and nndist ([#13498](https://github.com/leanprover-community/mathlib/pull/13498))
Most of these lemmas follow trivially from the `norm` versions. This is far from exhaustive.
Additionally:
* `nnreal.coe_supr` and `nnreal.coe_infi` are added
* The old `is_primitive_root.nnnorm_eq_one` is renamed to `is_primitive_root.norm'_eq_one` as it was not about `nnnorm` at all. The unprimed name is already taken in reference to `algebra.norm`.
* `parallelogram_law_with_norm_real` is removed since it's syntactically identical to `parallelogram_law_with_norm ℝ` and also not used anywhere.

### [2022-04-19 15:52:32](https://github.com/leanprover-community/mathlib/commit/f06dca7)
feat(data/int/basic): add lemma `int.abs_le_one_iff` ([#13513](https://github.com/leanprover-community/mathlib/pull/13513))
Also renaming `int.eq_zero_iff_abs_lt_one`.
The proof is due to @Ruben-VandeVelde 
Discussed on Zulip [here](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Integers.20of.20norm.20at.20most.20one)

### [2022-04-19 15:52:31](https://github.com/leanprover-community/mathlib/commit/634eab1)
feat(category_theory/limits): add characteristic predicate for zero objects ([#13511](https://github.com/leanprover-community/mathlib/pull/13511))

### [2022-04-19 14:04:47](https://github.com/leanprover-community/mathlib/commit/5dc8c1c)
feat(order/filter/n_ary): Add lemma equating map₂ to map on the product ([#13490](https://github.com/leanprover-community/mathlib/pull/13490))
Proof that map₂ is the image of the corresponding function `α × β → γ`.
Discussion: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/filter.20map.E2.82.82.20as.20map

### [2022-04-19 14:04:46](https://github.com/leanprover-community/mathlib/commit/8fa3263)
fix(analysis/locally_convex/balanced_hull_core): minimize import ([#13450](https://github.com/leanprover-community/mathlib/pull/13450))
I'm doing this because I need to have `balanced_hull_core` before `normed_space.finite_dimensional` and this little change seems to be enough for that, but I think at some point we'll need to move lemmas so that normed_spaces come as late as possible

### [2022-04-19 14:04:45](https://github.com/leanprover-community/mathlib/commit/ba6a985)
feat(order/cover): define `wcovby` ([#13424](https://github.com/leanprover-community/mathlib/pull/13424))
* This defines the reflexive closure of `covby`, which I call `wcovby` ("weakly covered by")
* This is useful, since some results about `covby` still hold for `wcovby`. 
* Use `wcovby` in the proofs of the properties for `covby`.
* Also define `wcovby_insert` (the motivating example, since I really want `(wcovby_insert _ _).eq_or_eq`)

### [2022-04-19 14:04:44](https://github.com/leanprover-community/mathlib/commit/8f7e10b)
refactor(group_theory/group_action/big_operators): extract to a new file ([#13340](https://github.com/leanprover-community/mathlib/pull/13340))
`basic` is a misleading name, as `group_action.basic` imports a lot of things.
For now I'm not renaming it, but I've adding a skeletal docstring.
Splitting out the big operator lemmas allows access to big operators before modules and quotients.
This also performs a drive-by generalization of the typeclasses on `smul_cancel_of_non_zero_divisor`.
Authorship is from [#1910](https://github.com/leanprover-community/mathlib/pull/1910)

### [2022-04-19 12:11:00](https://github.com/leanprover-community/mathlib/commit/3e78c23)
fix(algebra/hom/units): better defeq in `is_unit.lift_right` ([#13508](https://github.com/leanprover-community/mathlib/pull/13508))
… and fix a timeout introduced by this change and remove some extraneous parentheses there.

### [2022-04-19 10:05:03](https://github.com/leanprover-community/mathlib/commit/5a4bae1)
feat(algebra/*/basic): add trivial lemmas ([#13416](https://github.com/leanprover-community/mathlib/pull/13416))
These save you from having to fiddle with `mul_one` when you want to rewrite them the other way, or allow easier commutativity rewrites.

### [2022-04-19 08:07:49](https://github.com/leanprover-community/mathlib/commit/9202b6d)
feat(order/succ_pred/basic): Intervals and `succ`/`pred` ([#13486](https://github.com/leanprover-community/mathlib/pull/13486))
Relate `order.succ`, `order.pred` and `set.Ixx`.

### [2022-04-19 06:50:55](https://github.com/leanprover-community/mathlib/commit/d19e8cb)
chore(docs): don't use deprecated is_subring ([#13505](https://github.com/leanprover-community/mathlib/pull/13505))

### [2022-04-19 05:04:57](https://github.com/leanprover-community/mathlib/commit/828ef48)
fix(category_theory/monoidal): increase class search depth in coherence tactic ([#13413](https://github.com/leanprover-community/mathlib/pull/13413))
There were two places, not just one, where the class search depth needs to be increased.

### [2022-04-19 03:39:47](https://github.com/leanprover-community/mathlib/commit/fb44330)
feat(data/matrix/block): `matrix.block_diagonal` is a ring homomorphism ([#13489](https://github.com/leanprover-community/mathlib/pull/13489))
This is one of the steps on the path to showing that the matrix exponential of a block diagonal matrix is a block diagonal matrix of the exponents of the blocks.
As well as adding the new bundled homomorphisms, this generalizes the typeclasses in this file and tidies up the order of arguments.
Finally, this protects some `map_*` lemmas to prevent clashes with the global lemmas of the same name.

### [2022-04-19 01:03:57](https://github.com/leanprover-community/mathlib/commit/eb22ba4)
chore(algebra/monoid_algebra/basic): use the homomorphism typeclasses ([#13389](https://github.com/leanprover-community/mathlib/pull/13389))
This replaces `mul_hom` with `mul_hom_class` and `add_hom` with `add_hom_class`.
Also adds two trivial lemmas, `monoid_algebra.map_domain_one` and `add_monoid_algebra.map_domain_one`.

### [2022-04-18 20:47:04](https://github.com/leanprover-community/mathlib/commit/37d02d3)
chore(ring_theory/hahn_series, topology/locally_constant/algebra): add missing `non_unital_non_assoc_ring` instances ([#13504](https://github.com/leanprover-community/mathlib/pull/13504))

### [2022-04-18 19:11:39](https://github.com/leanprover-community/mathlib/commit/3c20253)
chore(algebra/ring/{pi, prod}): fix errors in `ring_hom` for `pi` and `prod`. ([#13501](https://github.com/leanprover-community/mathlib/pull/13501))
Looks like some things were incorrectly changed when copied from the corresponding `monoid_hom` files.

### [2022-04-18 19:11:38](https://github.com/leanprover-community/mathlib/commit/b54591f)
chore(analysis/normed_space/finite_dimension): golf a proof ([#13491](https://github.com/leanprover-community/mathlib/pull/13491))
These `letI`s just made this proof convoluted, the instances were not needed.
Without them, we don't even need the import.
Similarly, the `classical` was the cause of the need for the `congr`.

### [2022-04-18 19:11:37](https://github.com/leanprover-community/mathlib/commit/fd08afe)
chore(data/nat/factorization): golf `dvd_iff_prime_pow_dvd_dvd` ([#13473](https://github.com/leanprover-community/mathlib/pull/13473))
Golfing the edge-case proof added in https://github.com/leanprover-community/mathlib/pull/13316

### [2022-04-18 17:14:07](https://github.com/leanprover-community/mathlib/commit/d89160b)
feat(order/bounded_order): Strictly monotone functions preserve maximality ([#13434](https://github.com/leanprover-community/mathlib/pull/13434))
Prove `f a = f ⊤ ↔ a = ⊤` and `f a = f ⊥ ↔ a = ⊥` for strictly monotone/antitone functions. Also fix `is_max.eq_top` and friends and delete `eq_top_of_maximal` (which accidentally survived the last refactor).

### [2022-04-18 17:14:06](https://github.com/leanprover-community/mathlib/commit/5c75390)
feat(data/real/ennreal): Order properties of addition ([#13371](https://github.com/leanprover-community/mathlib/pull/13371))
Inherit algebraic order lemmas from `with_top`. Also protect `ennreal.add_lt_add_iff_left` and `ennreal.add_lt_add_iff_right`, as they should have been.

### [2022-04-18 17:14:05](https://github.com/leanprover-community/mathlib/commit/546618e)
feat(order/upper_lower): Principal upper/lower sets ([#13069](https://github.com/leanprover-community/mathlib/pull/13069))
Define `upper_set.Ici` and `lower_set.Iic`. Also add membership lemmas for the lattice operations.

### [2022-04-18 15:45:35](https://github.com/leanprover-community/mathlib/commit/d790b4b)
feat(set_theory/cardinal): `lt_omega_of_fintype` ([#13365](https://github.com/leanprover-community/mathlib/pull/13365))

### [2022-04-18 10:31:05](https://github.com/leanprover-community/mathlib/commit/e18ea79)
feat(number_theory/legendre_symbol/quadratic_reciprocity): replace `[fact (p % 2 = 1)]` arguments by `(p ≠ 2)` ([#13474](https://github.com/leanprover-community/mathlib/pull/13474))
This removes implicit arguments of the form `[fact (p % 2 = 1)]` and replaces them by explicit arguments `(hp : p ≠ 2)`.
(See the short discussion on April 9 in [this topic](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Hilbert.20symbol.20over.20.E2.84.9A).)

### [2022-04-18 05:37:15](https://github.com/leanprover-community/mathlib/commit/82348a6)
feat(computability/partrec_code): add eval prec helpers ([#11945](https://github.com/leanprover-community/mathlib/pull/11945))
A few helpers to clarify the definition of `eval`.

### [2022-04-18 03:41:36](https://github.com/leanprover-community/mathlib/commit/279b7f3)
chore(scripts): update nolints.txt ([#13493](https://github.com/leanprover-community/mathlib/pull/13493))
I am happy to remove some nolints for you!

### [2022-04-17 15:18:45](https://github.com/leanprover-community/mathlib/commit/e6322c6)
feat(analysis/convex): golf some proofs ([#13451](https://github.com/leanprover-community/mathlib/pull/13451))

### [2022-04-17 15:18:44](https://github.com/leanprover-community/mathlib/commit/b90e770)
feat(data/fin/tuple/nat_antidiagonal): add `list.nat.antidiagonal_tuple_pairwise_pi_lex` ([#13339](https://github.com/leanprover-community/mathlib/pull/13339))
This proof feels a little clumsy, but maybe that's unavoidable.

### [2022-04-17 13:47:06](https://github.com/leanprover-community/mathlib/commit/9380977)
chore(algebra/big_operators/fin): moving lemmas ([#13331](https://github.com/leanprover-community/mathlib/pull/13331))
This PR moves lemmas about products and sums over `fin n` from `data/fintype/card.lean` to `algebra/big_operators/fin.lean`.

### [2022-04-17 12:41:22](https://github.com/leanprover-community/mathlib/commit/7c7f351)
feat(topology/[separation, homeomorph]): separation properties are topological invariants ([#13401](https://github.com/leanprover-community/mathlib/pull/13401))

### [2022-04-17 10:27:47](https://github.com/leanprover-community/mathlib/commit/49e41eb)
feat(topology/algebra/order): extreme value thm for a function continuous on a closed set ([#13348](https://github.com/leanprover-community/mathlib/pull/13348))

### [2022-04-17 03:57:45](https://github.com/leanprover-community/mathlib/commit/f4f46cd)
chore(scripts): update nolints.txt ([#13482](https://github.com/leanprover-community/mathlib/pull/13482))
I am happy to remove some nolints for you!

### [2022-04-16 19:28:42](https://github.com/leanprover-community/mathlib/commit/d4fda04)
feat(data/finsupp/basic): add a few lemmas, mostly about `finsupp.filter` ([#13457](https://github.com/leanprover-community/mathlib/pull/13457))

### [2022-04-16 17:33:14](https://github.com/leanprover-community/mathlib/commit/96667b5)
chore(number_theory/*): Weaken assumptions ([#13443](https://github.com/leanprover-community/mathlib/pull/13443))
Follow @alexjbest's generalization linter to weaken typeclass assumptions in number theory.

### [2022-04-16 17:33:13](https://github.com/leanprover-community/mathlib/commit/018e9b5)
chore(order/bounded_order): Match the `with_bot` and `with_top` API ([#13419](https://github.com/leanprover-community/mathlib/pull/13419))
The API for `with_top` and the API for `with_bot` somehow evolved independently from each other, which created frustating disparity in lemmas and argument implicitness. This synchronizes everything (including the layout), generalize a few lemmas from `preorder`/`partial_order` to `has_le`/`has_lt`, and removes the duplicated `is_total (with_bot α) (≤)`/`is_total (with_top α) (≤)` instances.

### [2022-04-16 17:33:12](https://github.com/leanprover-community/mathlib/commit/8decd4b)
chore(logic/encodable/basic): Rename `encodable` instances ([#13396](https://github.com/leanprover-community/mathlib/pull/13396))
The instances were called `encodable.foo` instead of `foo.encodable` as the naming convention preconizes.

### [2022-04-16 17:33:11](https://github.com/leanprover-community/mathlib/commit/91a43e7)
feat(algebra/order/monoid): Co/contravariant classes for `with_bot`/`with_top` ([#13369](https://github.com/leanprover-community/mathlib/pull/13369))
Add the `covariant_class (with_bot α) (with_bot α) (+) (≤)` and `contravariant_class (with_bot α) (with_bot α) (+) (<)` instances, as well as the lemmas that `covariant_class (with_bot α) (with_bot α) (+) (<)` and `contravariant_class (with_bot α) (with_bot α) (+) (≤)` almost hold.
On the way, match the APIs for `with_bot`/`with_top` by adding missing lemmas.

### [2022-04-16 16:18:59](https://github.com/leanprover-community/mathlib/commit/874dde5)
feat(data/polynomial/eval): generalize smul lemmas ([#13479](https://github.com/leanprover-community/mathlib/pull/13479))

### [2022-04-16 14:27:42](https://github.com/leanprover-community/mathlib/commit/010f09e)
feat(data/polynomial/taylor): add `taylor_alg_hom` ([#13477](https://github.com/leanprover-community/mathlib/pull/13477))

### [2022-04-16 12:38:45](https://github.com/leanprover-community/mathlib/commit/f7430cd)
feat(data/polynomial/eval): add `protected` on some lemmas about `polynomial.map` ([#13478](https://github.com/leanprover-community/mathlib/pull/13478))
These clash with global lemmas.

### [2022-04-16 05:39:36](https://github.com/leanprover-community/mathlib/commit/862a585)
feat(topology/stone_cech): add stone_cech_hom_ext ([#13472](https://github.com/leanprover-community/mathlib/pull/13472))
The universal property that characterises the Stone–Čech compactification of a topological space X is that any function from X to a compact Hausdorff space extends uniquely to a continuous function on βX. Existence is already provided by `unique_stone_cech_extend`, but it seems that the uniqueness lemma was intentionally omitted previously. Easy, but probably worth being explicit about.

### [2022-04-15 20:29:48](https://github.com/leanprover-community/mathlib/commit/449e06a)
feat(algebraic_topology/fundamental_groupoid/fundamental_group): add type checker helpers for convertings paths to/from elements of fundamental group ([#13182](https://github.com/leanprover-community/mathlib/pull/13182))
This pr adds the following helper functions for converting paths to and from elements of the fundamental group:
- `to_arrow`: converts element of the fundamental group to an arrow in the fundamental groupoid
- `to_path`: converts element of the fundamental group to a (quotient of homotopic) path in the space
- `from_arrow`: constructs an element of the fundamental group from a self-arrow in the fundamental groupoid
- `from_path`: constructs an element of the fundamental group from a (quotient of homotopic) path in the space
These parallel  the similarly named functions for the fundamental group [here](https://github.com/leanprover-community/mathlib/blob/743ed5d1dd54fffd65e3a7f3522e4a4e85472964/src/algebraic_topology/fundamental_groupoid/basic.lean#L339-L355). They will prove helpful in doing computations with the fundamental group later e.g. for the disk, circle, etc.

### [2022-04-15 17:50:17](https://github.com/leanprover-community/mathlib/commit/c988c62)
chore(number_theory/function_field): fix typo ([#13464](https://github.com/leanprover-community/mathlib/pull/13464))

### [2022-04-15 17:50:16](https://github.com/leanprover-community/mathlib/commit/fbff76b)
refactor(number_theory/legendre_symbol/): move Gauss/Eisenstein lemma code to separate file ([#13449](https://github.com/leanprover-community/mathlib/pull/13449))
In preparation of further changes to number_theory/legendre_symbol/quadratic_reciprocity, this takes most of the code dealing with the lemmas of Gauss and Eisenstein out of quadratic_reciprocity.lean into a new file gauss_eisenstein_lemmas.lean.
Since I am not planning to do much (if anything) to this part of the code and it is rather involved and slows down Lean when I'm editing quadratic_reciprocity.lean, it makes sense to separate this code from the remainder of the file.

### [2022-04-15 17:09:01](https://github.com/leanprover-community/mathlib/commit/0c2d68a)
feat(data/sym/sym2): mem_map/mem_congr/map_id' ([#13437](https://github.com/leanprover-community/mathlib/pull/13437))
Additional simplification lemmas, one to address non-simp-normal-form. (Also did a few proof simplifications.)

### [2022-04-15 15:03:07](https://github.com/leanprover-community/mathlib/commit/d6c1cf1)
feat(analysis/normed_space/pointwise): Balls disjointness ([#13379](https://github.com/leanprover-community/mathlib/pull/13379))
Two balls in a real normed space are disjoint iff the sum of their radii is less than the distance between their centers.

### [2022-04-15 15:03:06](https://github.com/leanprover-community/mathlib/commit/2194eef)
chore(ring_theory/ideal/local_ring): generalize to semirings ([#13341](https://github.com/leanprover-community/mathlib/pull/13341))

### [2022-04-15 15:03:05](https://github.com/leanprover-community/mathlib/commit/c65bebb)
feat(number_theory/padics/padic_numbers): add padic.add_valuation ([#12939](https://github.com/leanprover-community/mathlib/pull/12939))
We define the p-adic additive valuation on `Q_[p]`, as an `add_valuation` with values in `with_top Z`.

### [2022-04-15 13:10:57](https://github.com/leanprover-community/mathlib/commit/bbbea1c)
chore(*): clean up unnecessary uses of nat.cases_on ([#13454](https://github.com/leanprover-community/mathlib/pull/13454))

### [2022-04-15 11:12:38](https://github.com/leanprover-community/mathlib/commit/ebc8b44)
feat(analysis/normed_space/basic): `pi` and `prod` are `normed_algebra`s ([#13442](https://github.com/leanprover-community/mathlib/pull/13442))
Note that over an empty index type, `pi` is not a normed_algebra since it is trivial as a ring.

### [2022-04-15 10:39:09](https://github.com/leanprover-community/mathlib/commit/d13f291)
feat(group_theory/group_action/conj_act): conjugation by the units of a monoid ([#13439](https://github.com/leanprover-community/mathlib/pull/13439))
I suspect we can make this even more general in future by introducing a compatibility typeclass, but this is good enough for me for now.
This also adds a stronger typeclass for the existing action of `conj_act K` where `K` is a `division_ring`.

### [2022-04-15 09:02:46](https://github.com/leanprover-community/mathlib/commit/dd51529)
feat(combinatorics/simple_graph/subgraph): delete_edges ([#13306](https://github.com/leanprover-community/mathlib/pull/13306))
Construct a subgraph from another by deleting edges.

### [2022-04-15 04:32:08](https://github.com/leanprover-community/mathlib/commit/d6a46b7)
chore(scripts): update nolints.txt ([#13455](https://github.com/leanprover-community/mathlib/pull/13455))
I am happy to remove some nolints for you!

### [2022-04-15 03:41:29](https://github.com/leanprover-community/mathlib/commit/6a5764b)
chore(analysis/normed_space/multilinear): use notation ([#13452](https://github.com/leanprover-community/mathlib/pull/13452))
* use notation `A [×n]→L[𝕜] B`;
* use `A → B` instead of `Π x : A, B`.

### [2022-04-15 02:47:13](https://github.com/leanprover-community/mathlib/commit/d81cedb)
feat(topology/algebra/module/multilinear): relax requirements for `continuous_multilinear_map.mk_pi_algebra` ([#13426](https://github.com/leanprover-community/mathlib/pull/13426))
`continuous_multilinear_map.mk_pi_algebra` and `continuous_multilinear_map.mk_pi_algebra_fin` do not need a norm on either the algebra or base ring; all they need is a topology on the algebra compatible with multiplication.
The much weaker typeclasses cause some elaboration issues in a few places, as the normed space can no longer be found by unification. Adding a non-dependent version of `continuous_multilinear_map.has_op_norm` largely resolves this, although a few  API proofs about `mk_pi_algebra` and `mk_pi_algebra_fin` end up quite underscore heavy.
This is the first step in being able to define `exp` without first choosing a `norm`.

### [2022-04-14 20:31:11](https://github.com/leanprover-community/mathlib/commit/1506335)
chore(number_theory/zsqrtd/*): Missing docstrings and cleanups ([#13445](https://github.com/leanprover-community/mathlib/pull/13445))
Add docstrings to `gaussian_int` and `zsqrtd.norm` and inline definitions which did not have a docstring nor deserved one.

### [2022-04-14 17:32:49](https://github.com/leanprover-community/mathlib/commit/cbf3062)
feat(combinatorics/simple_graph/connectivity): define connected components ([#12766](https://github.com/leanprover-community/mathlib/pull/12766))

### [2022-04-14 15:31:41](https://github.com/leanprover-community/mathlib/commit/251bd84)
feat(group_theory/subgroup/basic): One more `mem_normalizer_iff` lemma ([#13395](https://github.com/leanprover-community/mathlib/pull/13395))
This PR golfs `mem_normalizer_iff'` and adds `mem_normalizer_iff''`. There are not so easy to deduce from each other, so it's nice to have these variations available.

### [2022-04-14 15:31:40](https://github.com/leanprover-community/mathlib/commit/8bbc5ac)
feat(combinatorics/additive/salem_spencer): Salem-Spencer sets under images ([#13279](https://github.com/leanprover-community/mathlib/pull/13279))
A set `s` is Salem-Spencer iff its image under an injective Freiman hom is.

### [2022-04-14 14:09:05](https://github.com/leanprover-community/mathlib/commit/fecdd4b)
feat(measure_theory/card_measurable_space): `generate_measurable_rec s` gives precisely the generated sigma-algebra ([#12462](https://github.com/leanprover-community/mathlib/pull/12462))

### [2022-04-14 13:04:58](https://github.com/leanprover-community/mathlib/commit/adfe9c7)
feat(topology/algebra/order/compact): Sup is continuous ([#13347](https://github.com/leanprover-community/mathlib/pull/13347))
* Prove that the `Sup` of a binary function over a compact set is continuous in the second variable
* Some other lemmas about `Sup`
* Move and generalize `is_compact.bdd_[above|below]_image`
* from the sphere eversion project

### [2022-04-14 11:12:39](https://github.com/leanprover-community/mathlib/commit/936eb7e)
feat(analysis/normed_space/finite_dimension): a finite dimensional affine subspace is closed ([#13440](https://github.com/leanprover-community/mathlib/pull/13440))

### [2022-04-14 11:12:38](https://github.com/leanprover-community/mathlib/commit/9631a91)
feat(ring_theory/multiplicity): int.nat_abs ([#13420](https://github.com/leanprover-community/mathlib/pull/13420))
Spinning off of [#12454](https://github.com/leanprover-community/mathlib/pull/12454)

### [2022-04-14 11:12:37](https://github.com/leanprover-community/mathlib/commit/88ba31c)
feat(measure_theory/constructions/pi): more `measure_preserving` lemmas ([#13404](https://github.com/leanprover-community/mathlib/pull/13404))
* Reformulate `map_pi_equiv_pi_subtype_prod` in terms of
  `measure_preserving`.
* Add more equivalences (bare equivalences, order isomorphisms, and
  measurable equivalences) on pi types.

### [2022-04-14 11:12:36](https://github.com/leanprover-community/mathlib/commit/dd34ffa)
refactor(group_theory/schur_zassenhaus): Golf using `is_complement'_stabilizer` ([#13392](https://github.com/leanprover-community/mathlib/pull/13392))
This PR golfs the proof of the abelian case of Schur-Zassenhaus using the new lemma `is_complement'_stabilizer`.

### [2022-04-14 11:12:35](https://github.com/leanprover-community/mathlib/commit/15b764d)
feat(group_theory/complement): Add more API for the action on left transversals ([#13363](https://github.com/leanprover-community/mathlib/pull/13363))
This PR adds more API for the action on left transversals.

### [2022-04-14 11:12:34](https://github.com/leanprover-community/mathlib/commit/769ec8c)
feat(group_theory/group_action/basic): Right multiplication satisfies the `quotient_action` axiom ([#13362](https://github.com/leanprover-community/mathlib/pull/13362))
This PR adds an instance stating that the right multiplication action of `H.normalizer.opposite` on `G` satisfies the `quotient_action` axiom. In particular, we automatically get the induced action of `H.normalizer.opposite` on `G ⧸ H`, so we can delete the existing instance. (Technically, the existing instance was stated in terms of `H.normalizerᵐᵒᵖ`, but I think `H.normalizer.opposite` is a more natural way to write it).

### [2022-04-14 11:12:33](https://github.com/leanprover-community/mathlib/commit/3676f11)
chore(order/complete_lattice): General cleanup ([#13323](https://github.com/leanprover-community/mathlib/pull/13323))

### [2022-04-14 11:12:32](https://github.com/leanprover-community/mathlib/commit/7bb1081)
feat(category_theory): turn a split mono with cokernel into a biproduct ([#13184](https://github.com/leanprover-community/mathlib/pull/13184))

### [2022-04-14 10:16:39](https://github.com/leanprover-community/mathlib/commit/2693ab5)
feat(number_theory/legendre_symbol): add directory legendre_symbol and move quadratic_reciprocity.lean into it ([#13441](https://github.com/leanprover-community/mathlib/pull/13441))
In preparation of adding more code in a structured way, this sets up a new directory `legendre_symbol` below `number_theory` and moves the file `quadratic_reciprocity.lean` there.
The imports in `src/number_theory/zsqrtd/gaussian_int.lean` and `archive/imo/imp2008_q3.lean` are changed accordingly.

### [2022-04-14 10:16:38](https://github.com/leanprover-community/mathlib/commit/eb2780b)
feat(topology/unit_interval): add lemmas ([#13344](https://github.com/leanprover-community/mathlib/pull/13344))
* also change the statement of `unit_interval.mul_mem`
* from the sphere eversion project

### [2022-04-14 08:29:02](https://github.com/leanprover-community/mathlib/commit/87f8076)
chore(data/nat/factorial): tidy ([#13436](https://github.com/leanprover-community/mathlib/pull/13436))
I noticed this file had non-terminal simps, so I tidied it a little whilst removing them.

### [2022-04-14 08:29:00](https://github.com/leanprover-community/mathlib/commit/dac4f18)
feat(data/mv_polynomial): add support_X_pow ([#13435](https://github.com/leanprover-community/mathlib/pull/13435))
A simple lemma to match the `polynomial` API
from flt-regular

### [2022-04-14 08:28:58](https://github.com/leanprover-community/mathlib/commit/1378eab)
feat(complex/roots_of_unity):  extensionality ([#13431](https://github.com/leanprover-community/mathlib/pull/13431))
Primitive roots are equal iff their arguments are equal. Adds some useful specialisations, too.

### [2022-04-14 06:30:11](https://github.com/leanprover-community/mathlib/commit/2249a24)
chore(*): suggestions from the generalisation linter ([#13092](https://github.com/leanprover-community/mathlib/pull/13092))
Prompted by zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/An.20example.20of.20why.20formalization.20is.20useful
These are the "reasonable" suggestions from @alexjbest's generalisation linter up to `algebra.group.basic`.

### [2022-04-14 03:43:29](https://github.com/leanprover-community/mathlib/commit/a565471)
chore(scripts): update nolints.txt ([#13438](https://github.com/leanprover-community/mathlib/pull/13438))
I am happy to remove some nolints for you!

### [2022-04-14 02:07:07](https://github.com/leanprover-community/mathlib/commit/b62626e)
feat(complex/arg): arg_eq_zero_iff ([#13432](https://github.com/leanprover-community/mathlib/pull/13432))

### [2022-04-13 23:29:58](https://github.com/leanprover-community/mathlib/commit/0765994)
chore(order/category/Preorder): reduce imports ([#13301](https://github.com/leanprover-community/mathlib/pull/13301))
Because `punit_instances` comes at the very end of the algebraic import hierarchy, we were requiring the entire algebraic hierarchy before we could begin compiling the theory of categorical limits.
This tweak substantially reduces the import dependencies.

### [2022-04-13 22:15:36](https://github.com/leanprover-community/mathlib/commit/6f401ac)
feat(data/polynomial/*): suggestions from the generalization linter ([#13342](https://github.com/leanprover-community/mathlib/pull/13342))

### [2022-04-13 18:43:15](https://github.com/leanprover-community/mathlib/commit/76c969b)
chore(algebra/polynomial/big_operators): drop some nontrivial assumptions ([#13428](https://github.com/leanprover-community/mathlib/pull/13428))

### [2022-04-13 17:31:46](https://github.com/leanprover-community/mathlib/commit/da13598)
feat(model_theory/encoding): Bundled encoding of terms ([#13226](https://github.com/leanprover-community/mathlib/pull/13226))
Bundles `term.list_encode` and `term.list_decode` into a `computability.encoding`

### [2022-04-13 16:27:43](https://github.com/leanprover-community/mathlib/commit/9913860)
feat(ring_theory/tensor_product): add assoc for tensor product as an algebra homomorphism ([#13309](https://github.com/leanprover-community/mathlib/pull/13309))
By speeding up a commented out def, this goes from from ~100s to ~7s on my machine .

### [2022-04-13 10:56:42](https://github.com/leanprover-community/mathlib/commit/0c3f75b)
feat(analysis/normed_space/basic): normed division algebras over ℝ are also normed algebras over ℚ ([#13384](https://github.com/leanprover-community/mathlib/pull/13384))
This results shows that `algebra_rat` respects the norm in ` ℝ`-algebras that respect the norm.
The new instance carries no new data, as the norm and algebra structure are already defined elsewhere.
Probably there is a weaker requirement for compatibility, but I have no idea what it is, and the weakening can come later.

### [2022-04-13 10:56:41](https://github.com/leanprover-community/mathlib/commit/50ff59a)
feat(model_theory/skolem, satisfiability): A weak Downward Loewenheim Skolem ([#13141](https://github.com/leanprover-community/mathlib/pull/13141))
Defines a language and structure with built-in Skolem functions for a particular language
Proves a weak form of Downward Loewenheim Skolem: every structure has a small (in the universe sense) elementary substructure
Shows that `T` having a model in any universe implies `T.is_satisfiable`.

### [2022-04-13 10:56:40](https://github.com/leanprover-community/mathlib/commit/647aa5b)
feat(model_theory/fraisse): Defines ultrahomogeneous structures, fixes Fraïssé limit definition ([#12994](https://github.com/leanprover-community/mathlib/pull/12994))
Defines ultrahomogeneous structures
Fixes the definition of a Fraïssé limit to require ultrahomogeneity
Completes the characterization of when a class is the age of a countable structure.

### [2022-04-13 08:59:52](https://github.com/leanprover-community/mathlib/commit/6f59d77)
feat(order/bounded_order): Basic API for `subtype.order_bot` and  `subtype.order_top` ([#12904](https://github.com/leanprover-community/mathlib/pull/12904))
A few `simp` lemmas that were needed for `subtype.order_bot` and  `subtype.order_top`.

### [2022-04-13 07:30:42](https://github.com/leanprover-community/mathlib/commit/5b8bb9b)
feat(category_theory/monoidal): define monoidal structure on the category of monoids in a braided monoidal category ([#13122](https://github.com/leanprover-community/mathlib/pull/13122))
Building on the preliminary work from the previous PRs, we finally show that monoids in a braided monoidal category form a monoidal category.

### [2022-04-13 04:14:04](https://github.com/leanprover-community/mathlib/commit/1de6ce9)
chore(scripts): update nolints.txt ([#13408](https://github.com/leanprover-community/mathlib/pull/13408))
I am happy to remove some nolints for you!

### [2022-04-13 04:14:03](https://github.com/leanprover-community/mathlib/commit/b0bd771)
fix(combinatorics/simple_graph/connectivity): correctly generalized variables ([#13405](https://github.com/leanprover-community/mathlib/pull/13405))

### [2022-04-13 04:14:02](https://github.com/leanprover-community/mathlib/commit/917fc96)
refactor(set_theory/cofinality): Normalize names ([#13400](https://github.com/leanprover-community/mathlib/pull/13400))
We rename lemmas of the form `is_regular (foo x)` to `is_regular_foo` instead of `foo_is_regular`.

### [2022-04-13 02:38:14](https://github.com/leanprover-community/mathlib/commit/ac7a356)
chore(set_theory/*): Fix lint ([#13399](https://github.com/leanprover-community/mathlib/pull/13399))
Add missing docstrings and `inhabited` instances or a `nolint` when an `inhabited` instance isn't reasonable.

### [2022-04-13 02:38:13](https://github.com/leanprover-community/mathlib/commit/8c9ee31)
feat(order/conditionally_complete_lattice): Add `le_cSup_iff` ([#13321](https://github.com/leanprover-community/mathlib/pull/13321))

### [2022-04-13 00:37:31](https://github.com/leanprover-community/mathlib/commit/fb94880)
refactor(category_theory/shift): tighten scope of local attribute [reducible] ([#13335](https://github.com/leanprover-community/mathlib/pull/13335))
In all the files dealing with shifts on categories, we have a sprinkling of `local attribute [reducible]`, without which we get somewhat mysterious errors.
However with them, we produce some very fragile proof states (recently I was upset to see that shifting by `(0 : A)` and shifting by the tensor unit in `discrete A` were not definitionally commuting...).
I've been attempting to refactor this part of the library so we just never need to use `local attribute [reducible]`, in the hope of making these problems go away.
Having failed so far, this PR simply tightens the scopes of these local attributes as narrowly as possible (or in cases removes them entirely), so it is clearer exactly what is relying on them to work.

### [2022-04-12 23:52:20](https://github.com/leanprover-community/mathlib/commit/f496ef4)
feat(computability/{language/regular_expressions): Map along a function ([#13197](https://github.com/leanprover-community/mathlib/pull/13197))
Define `language.map` and `regular_expression.map`.

### [2022-04-12 23:00:49](https://github.com/leanprover-community/mathlib/commit/7ece83e)
feat(topology/homotopy): Add definition of contractible spaces ([#12731](https://github.com/leanprover-community/mathlib/pull/12731))

### [2022-04-12 22:12:37](https://github.com/leanprover-community/mathlib/commit/94a52c4)
feat(category_theory/monoidal): prove that in a braided monoidal category unitors and associators are monoidal natural transformations ([#13121](https://github.com/leanprover-community/mathlib/pull/13121))
This PR contains proofs of lemmas that are used in the stacked PR to define a monoidal structure on the category of monoids in a braided monoidal category.  The lemmas can be summarised by saying that in a braided monoidal category unitors and associators are monoidal natural transformations.
Note that for these statements to make sense we would need to define monoidal functors that are sources and targets of these monoidal natural transformations.  For example, the morphisms `(α_ X Y Z).hom` are the components of a monoidal natural transformation
```
(tensor.prod (𝟭 C)) ⊗⋙ tensor  ⟶ Α_ ⊗⋙ ((𝟭 C).prod tensor) ⊗⋙ tensor
```
where `Α_ : monoidal_functor ((C × C) × C) (C × (C × C))` is the associator functor given by `λ X, (X.1.1, (X.1.2, X.2))` on objects.  I didn't define the functor `Α_`.  (The easiest way would be to build it up using `prod'` we have already defined from `fst` and `snd`, which we would need to define as monoidal functors.)  Instead, I stated and proved the commutative diagram that expresses the monoidality of the above transformation.  Ditto for unitors.  Please let me know if you'd like me to define all the required functors and monoidal natural transformations.  The monoidal natural transformations themselves are not used in the proof that the category of monoids in a braided monoidal category is monoidal and only provide meaningful names to the lemmas that are used in the proof.

### [2022-04-12 20:53:45](https://github.com/leanprover-community/mathlib/commit/78ea75a)
feat(order/filter/cofinite): add lemmas, golf ([#13394](https://github.com/leanprover-community/mathlib/pull/13394))
* add `filter.comap_le_cofinite`,
  `function.injective.comap_cofinite_eq`, and
  `filter.has_basis.coprod`;
* rename `at_top_le_cofinite` to `filter.at_top_le_cofinite`;
* golf `filter.coprod_cofinite` and `filter.Coprod_cofinite`, move
  them below `filter.comap_cofinite_le`;

### [2022-04-12 20:08:54](https://github.com/leanprover-community/mathlib/commit/da4ec7e)
feat(ring_theory/valuation/valuation_subring): Valuation subrings of a field ([#12741](https://github.com/leanprover-community/mathlib/pull/12741))

### [2022-04-12 18:28:33](https://github.com/leanprover-community/mathlib/commit/e72f275)
feat(number_theory/qudratic_reciprocity): change type of `a` in API lemmas to `int` ([#13393](https://github.com/leanprover-community/mathlib/pull/13393))
This is step 2 in the overhaul of number_theory/qudratic_reciprocity.
The only changes are that the argument `a` is now of type `int` rather than `nat` in a bunch of statements.
This is more natural, since the corresponding (now second) argument of `legendre_symnbol` is of type `int`; it therefore makes the API lemmas more easily useable.

### [2022-04-12 18:28:32](https://github.com/leanprover-community/mathlib/commit/3bbb847)
chore(*): remove instance arguments that are inferrable from earlier ([#13386](https://github.com/leanprover-community/mathlib/pull/13386))
Some lemmas have typeclass arguments that are in fact inferrable from the earlier ones, at least when everything is Prop valued this is unecessary so we clean up a few cases as they likely stem from typos or library changes. 
- `src/field_theory/finiteness.lean` it wasn't known at the time ([#7644](https://github.com/leanprover-community/mathlib/pull/7644)) that a division ring was noetherian, but now it is ([#7661](https://github.com/leanprover-community/mathlib/pull/7661))
- `src/category_theory/simple.lean` any abelian category has all cokernels so no need to assume it seperately
- `src/analysis/convex/extreme.lean` assumed `linear_ordered_field` and `no_smul_zero_divisors` which is unnecessary, we take this as a sign that this and a couple of other convexity results should be generalized to densely ordered linear ordered rings (of which there are examples that are not fields) cc @YaelDillies

### [2022-04-12 18:28:30](https://github.com/leanprover-community/mathlib/commit/116ac71)
feat(analysis/normed_space/exponential): exponentials of negations, scalar actions, and sums ([#13036](https://github.com/leanprover-community/mathlib/pull/13036))
The new lemmas are:
* `exp_invertible_of_mem_ball`
* `exp_invertible`
* `is_unit_exp_of_mem_ball`
* `is_unit_exp`
* `ring.inverse_exp`
* `exp_neg_of_mem_ball`
* `exp_neg`
* `exp_sum_of_commute`
* `exp_sum`
* `exp_nsmul`
* `exp_zsmul`
I don't know enough about the radius of convergence of `exp` to know if `exp_nsmul` holds more generally under extra conditions.

### [2022-04-12 17:21:31](https://github.com/leanprover-community/mathlib/commit/949021d)
feat(ring_theory/algebraic): Rational numbers are algebraic ([#13367](https://github.com/leanprover-community/mathlib/pull/13367))

### [2022-04-12 17:21:10](https://github.com/leanprover-community/mathlib/commit/c994ab3)
feat(category_theory/monoidal): define a monoidal structure on the tensor product functor of a braided monoidal category ([#13150](https://github.com/leanprover-community/mathlib/pull/13150))
Given a braided monoidal category `C`, equip its tensor product functor, viewed as a functor from `C × C` to `C` with a strength that turns it into a monoidal functor.
See [#13033](https://github.com/leanprover-community/mathlib/pull/13033) for a discussion of the motivation of this definition.
(This PR replaces [#13034](https://github.com/leanprover-community/mathlib/pull/13034) which was accidentally closed.)

### [2022-04-12 15:33:18](https://github.com/leanprover-community/mathlib/commit/4c0a274)
doc(model_theory/order): typo in docstrings ([#13390](https://github.com/leanprover-community/mathlib/pull/13390))

### [2022-04-12 15:33:16](https://github.com/leanprover-community/mathlib/commit/0c8b808)
fix(measure_theory/function/lp_space): fix an instance diamond in `measure_theory.Lp.has_edist` ([#13388](https://github.com/leanprover-community/mathlib/pull/13388))
This also changes the definition of `edist` to something definitionally nicer

### [2022-04-12 15:33:15](https://github.com/leanprover-community/mathlib/commit/c21561a)
feat(algebra/direct_sum): Reindexing direct sums ([#13076](https://github.com/leanprover-community/mathlib/pull/13076))
Lemmas to reindex direct sums, as well as to rewrite direct sums over an option or sigma type.

### [2022-04-12 13:28:12](https://github.com/leanprover-community/mathlib/commit/745099b)
chore(*/parity): Generalize lemmas and clarify names  ([#13268](https://github.com/leanprover-community/mathlib/pull/13268))
Generalizations

### [2022-04-12 12:36:48](https://github.com/leanprover-community/mathlib/commit/4b45a71)
feat(counterexamples/pseudoelement): add counterexample to uniqueness in category_theory.abelian.pseudoelement.pseudo_pullback ([#13387](https://github.com/leanprover-community/mathlib/pull/13387))
Borceux claims that the pseudoelement constructed in `category_theory.abelian.pseudoelement.pseudo_pullback` is unique. We show here that this claim is false.

### [2022-04-12 12:36:47](https://github.com/leanprover-community/mathlib/commit/73ec5b2)
chore(category_theory/closed/monoidal): correct error in doc string ([#13385](https://github.com/leanprover-community/mathlib/pull/13385))
Sorry, should have done this immediately when @b-mehta pointed out my mistake.

### [2022-04-12 12:36:46](https://github.com/leanprover-community/mathlib/commit/ef8e256)
feat(number_theory/cyclotomic): alg-closed fields are cyclotomic extensions over themselves ([#13366](https://github.com/leanprover-community/mathlib/pull/13366))

### [2022-04-12 11:56:25](https://github.com/leanprover-community/mathlib/commit/5534e24)
chore(category_theory/preadditive/biproducts): Speed up `biprod.column_nonzero_of_iso` ([#13383](https://github.com/leanprover-community/mathlib/pull/13383))
From 76s down to 2s. The decidability synthesis in `by_contradiction` is stupidly expensive.

### [2022-04-12 11:56:24](https://github.com/leanprover-community/mathlib/commit/4bcc532)
refactor(control/fold): don't use is_monoid_hom ([#13350](https://github.com/leanprover-community/mathlib/pull/13350))

### [2022-04-12 10:40:32](https://github.com/leanprover-community/mathlib/commit/8b27c45)
feat(order/filter/pointwise): Missing pointwise operations ([#13170](https://github.com/leanprover-community/mathlib/pull/13170))
Define inversion/negation, division/subtraction, scalar multiplication/addition, scaling/translation, scalar subtraction of filters using the new `filter.map₂`. Golf the existing API.

### [2022-04-12 08:46:24](https://github.com/leanprover-community/mathlib/commit/9984960)
fix(counterexamples): typo in module docstring ([#13378](https://github.com/leanprover-community/mathlib/pull/13378))

### [2022-04-12 08:46:23](https://github.com/leanprover-community/mathlib/commit/36bafae)
feat(topology/bornology/basic): review ([#13374](https://github.com/leanprover-community/mathlib/pull/13374))
* add lemmas;
* upgrade some implications to `iff`s.

### [2022-04-12 08:46:23](https://github.com/leanprover-community/mathlib/commit/d065fd4)
feat(ring_theory/ideal): generalize `x mod I ∈ J mod I ↔ x ∈ J` ([#13358](https://github.com/leanprover-community/mathlib/pull/13358))
We already had a lemma like this assuming `I ≤ J`, and we can drop the assumption if we instead change the RHS to `x ∈ J \sup I`.
This also golfs the proof of the original `mem_quotient_iff_mem`.

### [2022-04-12 08:46:22](https://github.com/leanprover-community/mathlib/commit/c883519)
feat(ring_theory/unique_factorization_domain): `factors x = normalized_factors x` ([#13356](https://github.com/leanprover-community/mathlib/pull/13356))
If the group of units is trivial, an arbitrary choice of factors is exactly the unique set of normalized factors.
I made this a `simp` lemma in this direction because `normalized_factors` has a stronger specification than `factors`. I believe currently we actually know less about `normalized_factors` than `factors`, so if it proves too inconvenient I can also remove the `@[simp]`.

### [2022-04-12 08:46:20](https://github.com/leanprover-community/mathlib/commit/85588f8)
feat(data/multiset): lemmas on intersecting a multiset with `repeat x n` ([#13355](https://github.com/leanprover-community/mathlib/pull/13355))
Intersecting a multiset `s` with `repeat x n` gives `repeat x (min n (s.count x))`.

### [2022-04-12 08:46:19](https://github.com/leanprover-community/mathlib/commit/f7fe7dd)
refactor(ring_theory/free_comm_ring): don't use is_ring_hom ([#13352](https://github.com/leanprover-community/mathlib/pull/13352))

### [2022-04-12 08:46:19](https://github.com/leanprover-community/mathlib/commit/fd53ce0)
feat(order/filter/at_top_bot): add more `disjoint` lemmas ([#13351](https://github.com/leanprover-community/mathlib/pull/13351))

### [2022-04-12 08:46:18](https://github.com/leanprover-community/mathlib/commit/708e2de)
chore(group_theory/free_abelian_group): remove is_add_monoid_hom ([#13349](https://github.com/leanprover-community/mathlib/pull/13349))

### [2022-04-12 08:46:17](https://github.com/leanprover-community/mathlib/commit/333e4be)
feat(algebra/group/basic|topology/connected): add two lemmas ([#13345](https://github.com/leanprover-community/mathlib/pull/13345))
* from the sphere eversion project

### [2022-04-12 08:46:16](https://github.com/leanprover-community/mathlib/commit/56d6399)
chore(set_theory/cardinal): Golf `mk_le_mk_mul_of_mk_preimage_le` ([#13329](https://github.com/leanprover-community/mathlib/pull/13329))

### [2022-04-12 08:46:15](https://github.com/leanprover-community/mathlib/commit/670735f)
feat(model_theory/order): The theory of dense linear orders without endpoints ([#13253](https://github.com/leanprover-community/mathlib/pull/13253))
Defines the theory of dense linear orders without endpoints

### [2022-04-12 08:46:14](https://github.com/leanprover-community/mathlib/commit/34853a9)
feat(topology/algebra/algebra): define the topological subalgebra generated by an element ([#13093](https://github.com/leanprover-community/mathlib/pull/13093))
This defines the topological subalgebra generated by a single element `x : A` of an algebra `A` as the topological closure of `algebra.adjoin R {x}`, and show it is commutative.
I called it `algebra.elemental_algebra`; if someone knows if this actually has a name in the literature, or just has a better idea for the name, let me know!

### [2022-04-12 08:46:12](https://github.com/leanprover-community/mathlib/commit/ed919b6)
feat(algebra/algebraic_card): Cardinality of algebraic numbers ([#12869](https://github.com/leanprover-community/mathlib/pull/12869))
We prove the following result: the cardinality of algebraic numbers under an R-algebra is at most `# polynomial R * ω`.

### [2022-04-12 08:46:11](https://github.com/leanprover-community/mathlib/commit/6bc2bd6)
feat(algebraic_geometry/projective_spectrum): Proj as a locally ringed space ([#12773](https://github.com/leanprover-community/mathlib/pull/12773))
This pr is about proving that Proj with its structure sheaf is a locally ringed space

### [2022-04-12 08:46:10](https://github.com/leanprover-community/mathlib/commit/72e1a9e)
feat(ring_theory/valuation/valuation_ring): Valuation rings and their associated valuation. ([#12719](https://github.com/leanprover-community/mathlib/pull/12719))
This PR defines a class `valuation_ring`, stating that an integral domain is a valuation ring.
We also show that valuation rings induce valuations on their fraction fields, that valuation rings are local, and that their lattice of ideals is totally ordered.

### [2022-04-12 07:55:03](https://github.com/leanprover-community/mathlib/commit/b889567)
feat(data/complex/basic): add a few lemmas ([#13354](https://github.com/leanprover-community/mathlib/pull/13354))

### [2022-04-12 05:57:50](https://github.com/leanprover-community/mathlib/commit/0783742)
chore(*): more assumptions to lemmas that are removable ([#13364](https://github.com/leanprover-community/mathlib/pull/13364))
This time I look at assumptions that are actually provable by simp from the earlier assumptions (fortunately there are only a couple of these), and one more from the review of [#13316](https://github.com/leanprover-community/mathlib/pull/13316) that was slightly too nontrivial to be found automatically.

### [2022-04-12 05:57:49](https://github.com/leanprover-community/mathlib/commit/56f6c8e)
chore(algebra/big_operators/intervals): Move and golf sum_range_sub_sum_range ([#13359](https://github.com/leanprover-community/mathlib/pull/13359))
Move sum_range_sub_sum_range to a better file. Also implemented the golf demonstrated in this paper https://arxiv.org/pdf/2202.01344.pdf from @spolu.

### [2022-04-12 05:57:48](https://github.com/leanprover-community/mathlib/commit/603db27)
feat(topology/metric_space/basic): some lemmas about dist ([#13343](https://github.com/leanprover-community/mathlib/pull/13343))
from the sphere eversion project

### [2022-04-12 05:24:39](https://github.com/leanprover-community/mathlib/commit/cbea7e1)
feat(algebra/order/monoid_lemmas_zero_lt): add some lemmas assuming `mul_one_class` `preorder` ([#13299](https://github.com/leanprover-community/mathlib/pull/13299))

### [2022-04-12 05:24:38](https://github.com/leanprover-community/mathlib/commit/e3db2e7)
feat(group_theory/complement): Criterion for complementary subgroups ([#13292](https://github.com/leanprover-community/mathlib/pull/13292))
This lemma gives a criterion for a stabilizer subgroup to be a complementary subgroup.

### [2022-04-12 03:21:18](https://github.com/leanprover-community/mathlib/commit/fdd68d9)
fix(category_theory/elements): speed up `groupoid_of_elements` ([#13372](https://github.com/leanprover-community/mathlib/pull/13372))
from 14.5s to 6s
It's [reported](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Hilbert.20symbol.20over.20.E2.84.9A/near/278592167) that this is causing timeouts in recent bors batches.

### [2022-04-12 03:21:17](https://github.com/leanprover-community/mathlib/commit/bf1b813)
chore(algebra/module/basic): generalize to add_monoid_hom_class ([#13346](https://github.com/leanprover-community/mathlib/pull/13346))
I need some of these lemmas for `ring_hom`.
Additionally, this:
* removes `map_nat_module_smul` (duplicate of `map_nsmul`) and `map_int_module_smul` (duplicate of `map_zsmul`)
* renames `map_rat_module_smul` to `map_rat_smul` for brevity.
* adds the lemmas `inv_nat_cast_smul_comm` and `inv_int_cast_smul_comm`.
* Swaps the order of the arguments to `map_zsmul` and `map_nsmul` to align with the usual rules (`to_additive` emitted them in the wrong order)

### [2022-04-12 03:21:16](https://github.com/leanprover-community/mathlib/commit/955cb8e)
feat(data/list/basic): add a theorem about last and append ([#13336](https://github.com/leanprover-community/mathlib/pull/13336))
When `ys` is not empty, we can conclude that `last (xs ++ ys)` is `last ys`.

### [2022-04-12 03:21:15](https://github.com/leanprover-community/mathlib/commit/10a3faa)
feat(algebra/order/monoid_lemmas_zero_lt): add lemmas assuming `mul_zero_class` `preorder` ([#13297](https://github.com/leanprover-community/mathlib/pull/13297))

### [2022-04-12 03:21:14](https://github.com/leanprover-community/mathlib/commit/fe1c78a)
feat(data/polynomial/algebra_map): remove some lemmas about `aeval`, add `protected` on `polynomial.map_list_prod` ([#13294](https://github.com/leanprover-community/mathlib/pull/13294))
Remove `aeval_sum` which is a duplicate of `map_sum`.
Remove `aeval_prod` which is a duplicate of `map_prod`.

### [2022-04-12 03:21:13](https://github.com/leanprover-community/mathlib/commit/483b7df)
feat(analysis/convex/strict_convex_space): Ray characterization of `∥x - y∥` ([#13293](https://github.com/leanprover-community/mathlib/pull/13293))
`∥x - y∥ = |∥x∥ - ∥y∥|` if and only if `x` and `y` are on the same ray.

### [2022-04-12 03:21:12](https://github.com/leanprover-community/mathlib/commit/f1c98ba)
feat(topology/uniform_space/uniform_convergence_topology): define the uniform structure of uniform convergence ([#13073](https://github.com/leanprover-community/mathlib/pull/13073))

### [2022-04-12 01:13:15](https://github.com/leanprover-community/mathlib/commit/7ba9c3f)
feat(order/basic): More order instances for `subtype` ([#13134](https://github.com/leanprover-community/mathlib/pull/13134))
Add the `has_le`, `has_lt`, `decidable_le`, `decidable_lt`, `bounded_order` instances.
Incorporating the `decidable_le` and `decidable_lt` instances into the `linear_order` one breaks some defeqs with `ite`/`dite`.

### [2022-04-11 23:09:24](https://github.com/leanprover-community/mathlib/commit/0453d60)
feat(algebraic_geometry/projective_spectrum): structure sheaf of Proj of graded ring ([#13072](https://github.com/leanprover-community/mathlib/pull/13072))
Construct the structure sheaf of Proj of a graded algebra.

### [2022-04-11 23:09:23](https://github.com/leanprover-community/mathlib/commit/f94cd0f)
feat(analysis/normed/normed_field): Pi types form a normed ring ([#12912](https://github.com/leanprover-community/mathlib/pull/12912))

### [2022-04-11 20:58:27](https://github.com/leanprover-community/mathlib/commit/887f933)
feat(data/fin/tuple/nat_antidiagonal): add an equiv and some TODO comments. ([#13338](https://github.com/leanprover-community/mathlib/pull/13338))
This follows on from [#13031](https://github.com/leanprover-community/mathlib/pull/13031), and:
* Adds the tuple version of an antidiagonal equiv
* Makes some arguments implicit
* Adds some comments to tie together `finset.nat.antidiagonal_tuple` with the `cut` definition used in one of the 100 Freek problems.

### [2022-04-11 20:58:26](https://github.com/leanprover-community/mathlib/commit/455bc65)
chore(representation_theory/invariants): clean up some simps ([#13337](https://github.com/leanprover-community/mathlib/pull/13337))

### [2022-04-11 20:58:25](https://github.com/leanprover-community/mathlib/commit/e8339bd)
feat(category_theory/fully_faithful): nat_trans_of_comp_fully_faithful ([#13327](https://github.com/leanprover-community/mathlib/pull/13327))
I added `nat_iso_of_comp_fully_faithful` in an earlier PR, but left out the more basic construction.

### [2022-04-11 20:58:24](https://github.com/leanprover-community/mathlib/commit/4a07054)
chore(*): remove numerous edge cases from lemmas ([#13316](https://github.com/leanprover-community/mathlib/pull/13316))
This PR uses the same methodology as [#10774](https://github.com/leanprover-community/mathlib/pull/10774) to use a linter to remove edge case assumptions from lemmas when the result is easy to prove without the assumption.
These are assumptions things like: n \ne 0, 0 < n, p \ne \top, nontrivial R, nonempty R.
Removing these unneeded assumptions makes such lemmas easier to apply, and lets us golf a few other proofs along the way.
The file with the most changes is `src/ring_theory/unique_factorization_domain.lean` where the linter inspired me to allow trivial monoids in many places.
The code I used to find these is in the branch [https://github.com/leanprover-community/mathlib/tree/alexjbest/simple_edge_cases_linter](https://github.com/leanprover-community/mathlib/tree/alexjbest/simple_edge_cases_linter?rgh-link-date=2021-12-13T23%3A53%3A31Z)

### [2022-04-11 20:58:23](https://github.com/leanprover-community/mathlib/commit/a839f4d)
feat(number_theory/quadratic_reciprocity): change order of arguments … ([#13311](https://github.com/leanprover-community/mathlib/pull/13311))
…in legendre_sym
This is the first step in a major overhaul of the contents of number_theory/quadratic_reciprocity.
As a first step, the order of the arguments `a` and `p` to `legendre_sym` is swapped, based on a [poll](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Hilbert.20symbol.20over.20.E2.84.9A) on Zulip.

### [2022-04-11 20:58:22](https://github.com/leanprover-community/mathlib/commit/4e1102a)
feat(probability/integration): characterize indep_fun by expected product of comp ([#13270](https://github.com/leanprover-community/mathlib/pull/13270))
This is the third PR into probability/integration, to characterize independence by the expected product of compositions.

### [2022-04-11 18:49:41](https://github.com/leanprover-community/mathlib/commit/a521a32)
feat(data/set/basic): Missing `set.image_perm` ([#13242](https://github.com/leanprover-community/mathlib/pull/13242))

### [2022-04-11 18:49:39](https://github.com/leanprover-community/mathlib/commit/dee4958)
feat(computability/*): Automata lemmas ([#13194](https://github.com/leanprover-community/mathlib/pull/13194))
A bunch of missing API for `language`, `regular_expression`, `DFA`, `NFA`, `ε_NFA`.

### [2022-04-11 18:49:38](https://github.com/leanprover-community/mathlib/commit/77ae091)
feat(number_theory/cyclotomic/primitive_roots): add `pow_sub_one_norm_prime_pow_ne_two` ([#13152](https://github.com/leanprover-community/mathlib/pull/13152))
We add `pow_sub_one_norm_prime_pow_ne_two`, that computes the norm of `ζ ^ (p ^ s) - 1`, where `ζ` is a primitive `p ^ (k + 1)`-th root of unity. This will be used to compute the discriminant of the `p ^ n`-th cyclotomic field.
From flt-regular

### [2022-04-11 18:49:37](https://github.com/leanprover-community/mathlib/commit/04250c8)
feat(measure_theory/measure/haar): Add the Steinhaus Theorem ([#12932](https://github.com/leanprover-community/mathlib/pull/12932))
This PR proves the [Steinhaus Theorem](https://en.wikipedia.org/wiki/Steinhaus_theorem) in any locally compact group with a Haar measure.

### [2022-04-11 18:49:35](https://github.com/leanprover-community/mathlib/commit/cea5e4b)
feat(data/sign): the sign function ([#12835](https://github.com/leanprover-community/mathlib/pull/12835))

### [2022-04-11 16:38:59](https://github.com/leanprover-community/mathlib/commit/695a2b6)
feat(combinatorics/simple_graph/connectivity): induced maps on walks and paths ([#13310](https://github.com/leanprover-community/mathlib/pull/13310))
Every graph homomorphism gives an induced map on walks.

### [2022-04-11 16:38:58](https://github.com/leanprover-community/mathlib/commit/a447dae)
chore(category_theory/*): reduce imports ([#13305](https://github.com/leanprover-community/mathlib/pull/13305))
An unnecessary import of `tactic.monotonicity` earlier in the hierarchy was pulling in quite a lot. A few compensatory imports are needed later.

### [2022-04-11 16:38:57](https://github.com/leanprover-community/mathlib/commit/5e8d6bb)
feat(combinatorics/simple_graph/{connectivity,adj_matrix}): powers of adjacency matrix ([#13304](https://github.com/leanprover-community/mathlib/pull/13304))
The number of walks of length-n between two vertices is given by the corresponding entry of the n-th power of the adjacency matrix.

### [2022-04-11 16:38:56](https://github.com/leanprover-community/mathlib/commit/bfd5384)
chore(category_theory): switch ulift and filtered in import hierarchy ([#13302](https://github.com/leanprover-community/mathlib/pull/13302))
Many files require `ulift` but not `filtered`, so `ulift` should be lower in the import hierarchy. This avoids needing all of `data/` up to `data/fintype/basic` before we can start defining categorical limits.

### [2022-04-11 16:38:55](https://github.com/leanprover-community/mathlib/commit/dcb6c86)
feat(measure_theory/function/uniform_integrable): Equivalent condition for uniformly integrable in the probability sense ([#12955](https://github.com/leanprover-community/mathlib/pull/12955))
A sequence of functions is uniformly integrable in the probability sense if and only if `∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ i, snorm ({x | C ≤ ∥f i x∥₊}.indicator (f i)) p μ ≤ ennreal.of_real ε`.

### [2022-04-11 16:38:54](https://github.com/leanprover-community/mathlib/commit/797c713)
feat(ring_theory/coprime/lemmas): alternative characterisations of pairwise coprimeness ([#12911](https://github.com/leanprover-community/mathlib/pull/12911))
This provides two condtions equivalent to pairwise coprimeness : 
* each term is coprime to the product of all others
* 1 can be obtained as a linear combination of all products with one term missing.

### [2022-04-11 14:08:55](https://github.com/leanprover-community/mathlib/commit/67d6097)
feat(data/option/basic): add `option.coe_get` ([#13081](https://github.com/leanprover-community/mathlib/pull/13081))
Adds lemma `coe_get {o : option α} (h : o.is_some) : ((option.get h : α) : option α) = o`
Extracted from @huynhtrankhanh's https://github.com/leanprover-community/mathlib/pull/11162, moved here to a separate PR

### [2022-04-11 11:52:38](https://github.com/leanprover-community/mathlib/commit/4139824)
refactor(category_theory/differential_object): simp only -> simp_rw ([#13333](https://github.com/leanprover-community/mathlib/pull/13333))
This is extremely minor; I replace a `simp only` with a `simp_rw`.
This proof is apparently rather fragile with respect to some other changes I'm trying to make, and I worked out the correct `simp_rw` sequence while debugging. May as well preserve it for posterity, or at least until next time I make it break.

### [2022-04-11 11:52:37](https://github.com/leanprover-community/mathlib/commit/c7e76bc)
chore(category_theory/monoidal/discrete): typo in to_additive name ([#13332](https://github.com/leanprover-community/mathlib/pull/13332))

### [2022-04-11 11:52:36](https://github.com/leanprover-community/mathlib/commit/d405955)
feat(analysis/complex/re_im_topology): add `metric.bounded.re_prod_im` ([#13324](https://github.com/leanprover-community/mathlib/pull/13324))
Also add `complex.mem_re_prod_im`.

### [2022-04-11 11:52:34](https://github.com/leanprover-community/mathlib/commit/ebbe763)
feat(measure_theory/constructions/borel_space): a set with `μ (∂ s) = 0` is null measurable ([#13322](https://github.com/leanprover-community/mathlib/pull/13322))

### [2022-04-11 11:52:33](https://github.com/leanprover-community/mathlib/commit/7e69148)
feat(order/conditionally_complete_lattice): Make `cSup_empty` a `simp` lemma ([#13318](https://github.com/leanprover-community/mathlib/pull/13318))

### [2022-04-11 11:52:32](https://github.com/leanprover-community/mathlib/commit/159855d)
feat(set_theory/ordinal_arithmetic): `is_normal.monotone` ([#13314](https://github.com/leanprover-community/mathlib/pull/13314))
We introduce a convenient abbreviation for `is_normal.strict_mono.monotone`.

### [2022-04-11 11:52:31](https://github.com/leanprover-community/mathlib/commit/c5b83f0)
doc(combinatorics/simple_graph/basic): mention half-edge synonym for darts ([#13312](https://github.com/leanprover-community/mathlib/pull/13312))

### [2022-04-11 11:52:30](https://github.com/leanprover-community/mathlib/commit/722c0df)
feat(category_theory/nat_iso): add simp lemmas ([#13303](https://github.com/leanprover-community/mathlib/pull/13303))

### [2022-04-11 11:52:29](https://github.com/leanprover-community/mathlib/commit/f7e862f)
feat(analysis/special_functions/pow): `z ^ w` is continuous in `(z, w)` at `(0, w)` if `0 < re w` ([#13288](https://github.com/leanprover-community/mathlib/pull/13288))
Also add a few supporting lemmas.

### [2022-04-11 11:52:28](https://github.com/leanprover-community/mathlib/commit/57682ff)
feat(data/complex/is_R_or_C): add `polynomial.of_real_eval` ([#13287](https://github.com/leanprover-community/mathlib/pull/13287))

### [2022-04-11 11:52:27](https://github.com/leanprover-community/mathlib/commit/577df07)
feat(analysis/asymptotics): add a few versions of `c=o(x)` as `x→∞` ([#13286](https://github.com/leanprover-community/mathlib/pull/13286))

### [2022-04-11 11:52:26](https://github.com/leanprover-community/mathlib/commit/171e2aa)
feat(group_theory/group_action/basic): A `quotient_action` induces an action on left cosets ([#13283](https://github.com/leanprover-community/mathlib/pull/13283))
A `quotient_action` induces an action on left cosets.

### [2022-04-11 11:52:25](https://github.com/leanprover-community/mathlib/commit/65b5dd8)
feat(group_theory/transversal): A `quotient_action` induces an action on left transversals ([#13282](https://github.com/leanprover-community/mathlib/pull/13282))
A `quotient_action` induces an action on left transversals.
Once [#13283](https://github.com/leanprover-community/mathlib/pull/13283) is merged, I'll PR some more API generalizing the existing lemma `smul_symm_apply_eq_mul_symm_apply_inv_smul`.

### [2022-04-11 11:52:24](https://github.com/leanprover-community/mathlib/commit/2eba524)
chore(topology/algebra/uniform_group): use morphism classes ([#13273](https://github.com/leanprover-community/mathlib/pull/13273))

### [2022-04-11 11:52:23](https://github.com/leanprover-community/mathlib/commit/2b80d4a)
feat(topology/order): if `e` is an equiv, `induced e.symm = coinduced e` ([#13272](https://github.com/leanprover-community/mathlib/pull/13272))

### [2022-04-11 11:52:21](https://github.com/leanprover-community/mathlib/commit/c160083)
feat(algebra/big_operators): `norm_num` plugin for list/multiset/finset prod/sum ([#13005](https://github.com/leanprover-community/mathlib/pull/13005))
This PR provides a plugin for the `norm_num` tactic that can evaluate finite sums and products, over lists, multisets and finsets.
`simp` could already handle some of these operations, but `norm_num` is overall much more suited to dealing with larger numerical operations such as arising from large sums.
I implemented the tactic as a `norm_num` plugin since it's intended to deal with numbers. I'm happy to make it its own tactic (`norm_bigop`?) if you feel this is outside of the `norm_num` scope. Similarly, I could also make a separate tactic for the parts that rewrite a list/multiset/finset into a sequence of `list.cons`es.

### [2022-04-11 09:27:57](https://github.com/leanprover-community/mathlib/commit/e5bd941)
feat(scripts): make style lint script more robust to lines starting with spaces ([#13317](https://github.com/leanprover-community/mathlib/pull/13317))
Currently some banned commands aren't caught if the line is indented.
Because of this I previously snuck in a `set_option pp.all true` by accident

### [2022-04-11 09:27:56](https://github.com/leanprover-community/mathlib/commit/cd616e0)
feat(analysis/special_functions/pow): more versions of `x ^ k = o(exp(b * x))` ([#13285](https://github.com/leanprover-community/mathlib/pull/13285))

### [2022-04-11 09:27:54](https://github.com/leanprover-community/mathlib/commit/706905c)
fix(algebra/indicator_function): fix name of `mul_indicator_eq_one_iff` ([#13284](https://github.com/leanprover-community/mathlib/pull/13284))
It is about `≠`, so call it `mul_indicator_ne_one_iff`/`indicator_ne_zero_iff`.

### [2022-04-11 09:27:53](https://github.com/leanprover-community/mathlib/commit/ff507a3)
feat(model_theory/basic): Structures over the empty language ([#13281](https://github.com/leanprover-community/mathlib/pull/13281))
Any type is a first-order structure over the empty language.
Any function, embedding, or equiv is a first-order hom, embedding or equiv over the empty language.

### [2022-04-11 09:27:52](https://github.com/leanprover-community/mathlib/commit/fe17fee)
feat(topology/algebra/uniform_group): a subgroup of a uniform group is a uniform group ([#13277](https://github.com/leanprover-community/mathlib/pull/13277))

### [2022-04-11 09:27:50](https://github.com/leanprover-community/mathlib/commit/6f428ed)
feat(group_theory/schreier): Finset version of Schreier's lemma ([#13274](https://github.com/leanprover-community/mathlib/pull/13274))
This PR adds a finset version of Schreier's lemma, getting closer to a statement in terms of `group.fg` and `group.rank`.

### [2022-04-11 09:27:48](https://github.com/leanprover-community/mathlib/commit/102311e)
fix(algebra/module/basic,group_theory/group_action/defs): generalize nat and int smul_comm_class instances ([#13174](https://github.com/leanprover-community/mathlib/pull/13174))
The `add_group.int_smul_with_zero` instance appears to be new, everything else is moved and has `[semiring R] [add_comm_monoid M] [module R M]` relaxed to `[monoid R] [add_monoid M] [distrib_mul_action R M]`, with the variables renamed to match the destination file.

### [2022-04-11 04:32:07](https://github.com/leanprover-community/mathlib/commit/4d27ecf)
refactor(order/conditionally_complete_lattice): `csupr_le_csupr` → `csupr_mono` ([#13320](https://github.com/leanprover-community/mathlib/pull/13320))
For consistency with `supr_mono` and `infi_mono`

### [2022-04-11 02:03:03](https://github.com/leanprover-community/mathlib/commit/6f9cb03)
chore(*): make more transitive relations available to calc ([#12860](https://github.com/leanprover-community/mathlib/pull/12860))
Fixed as many possible declarations to have the correct argument order, as per [Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/calc.20with.20.60.E2.89.83*.60). Golfed some random ones while I was at it.

### [2022-04-11 00:55:09](https://github.com/leanprover-community/mathlib/commit/a85958c)
chore(measure_theory/mconstructions/prod): Speed up `finite_spanning_sets_in.prod` ([#13325](https://github.com/leanprover-community/mathlib/pull/13325))
Disable the computability check on `measure_theory.measure.finite_spanning_sets_in.prod` because it was taking 20s of compilation.

### [2022-04-11 00:55:08](https://github.com/leanprover-community/mathlib/commit/a2d09b2)
feat(topology/algebra/order): add `le_on_closure` ([#13290](https://github.com/leanprover-community/mathlib/pull/13290))

### [2022-04-10 23:04:54](https://github.com/leanprover-community/mathlib/commit/e5ae099)
chore(topology/uniform_space/basic): golf a proof ([#13289](https://github.com/leanprover-community/mathlib/pull/13289))
Rewrite a proof using tactic mode and golf it.

### [2022-04-10 23:04:53](https://github.com/leanprover-community/mathlib/commit/8491021)
chore(algebra/invertible): generalise typeclasses ([#13275](https://github.com/leanprover-community/mathlib/pull/13275))

### [2022-04-10 23:04:52](https://github.com/leanprover-community/mathlib/commit/4ded5ca)
fix(field_theory/galois): update docstring ([#13188](https://github.com/leanprover-community/mathlib/pull/13188))

### [2022-04-10 23:04:51](https://github.com/leanprover-community/mathlib/commit/be22d07)
feat(data/sym/basic): some basic lemmas in preparation for stars and bars ([#12479](https://github.com/leanprover-community/mathlib/pull/12479))
Some lemmas extracted from @huynhtrankhanh's [#11162](https://github.com/leanprover-community/mathlib/pull/11162), moved here to a separate PR

### [2022-04-10 23:04:50](https://github.com/leanprover-community/mathlib/commit/609eb59)
feat(set_theory/cofinality): Every ordinal has a fundamental sequence ([#12317](https://github.com/leanprover-community/mathlib/pull/12317))

### [2022-04-10 21:57:11](https://github.com/leanprover-community/mathlib/commit/5bf5740)
chore(category_theory/fin_category): Speed up `as_type_equiv_obj_as_type` ([#13298](https://github.com/leanprover-community/mathlib/pull/13298))
Rename `obj_as_type_equiv_as_type` to `as_type_equiv_obj_as_type` (likely a typo). Use `equivalence.mk` instead of `equivalence.mk'` to build it and split the functors to separate definitions to tag them with `@[simps]` and make `dsimp` go further.
On my machine, this cuts down the compile time from 41s to 3s.

### [2022-04-10 20:28:46](https://github.com/leanprover-community/mathlib/commit/60ccf8f)
feat(linear_algebra): add `adjoint_pair` from `bilinear_form` ([#13203](https://github.com/leanprover-community/mathlib/pull/13203))
Copying the definition and theorem about adjoint pairs from `bilinear_form` to `sesquilinear_form`.
Defines the composition of two linear maps with a bilinear map to form a new bilinear map, which was missing from the `bilinear_map` API.
We also use the new definition of adjoint pairs in `analysis/inner_product_space/adjoint`.

### [2022-04-10 20:28:45](https://github.com/leanprover-community/mathlib/commit/a30cba4)
feat(set_theory/cardinal_ordinal): Simp lemmas for `mk` ([#13119](https://github.com/leanprover-community/mathlib/pull/13119))

### [2022-04-10 19:34:23](https://github.com/leanprover-community/mathlib/commit/965f46d)
feat(category_theory/monoidal): coherence tactic ([#13125](https://github.com/leanprover-community/mathlib/pull/13125))
This is an alternative to [#12697](https://github.com/leanprover-community/mathlib/pull/12697) (although this one does not handle bicategories!)
From the docstring:
```
Use the coherence theorem for monoidal categories to solve equations in a monoidal equation,
where the two sides only differ by replacing strings of "structural" morphisms with
different strings with the same source and target.
That is, `coherence` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `coherence1`.
```
This PR additionally provides a "composition up to unitors+associators" operation, so you can write
```
example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) : U ⟶ Y := f ⊗≫ g
```

### [2022-04-10 19:34:22](https://github.com/leanprover-community/mathlib/commit/0bc2aa9)
feat(data/fin/tuple/nat_antidiagonal): add `antidiagonal_tuple` ([#13031](https://github.com/leanprover-community/mathlib/pull/13031))

### [2022-04-10 15:57:49](https://github.com/leanprover-community/mathlib/commit/6d0984d)
doc(README): improve documentation on how to contribute ([#13116](https://github.com/leanprover-community/mathlib/pull/13116))
Create a new contributing section which highlights the basic steps on how to start contributing to mathlib

### [2022-04-10 13:49:42](https://github.com/leanprover-community/mathlib/commit/6368956)
counterexample(counterexamples/char_p_zero_ne_char_zero.lean): `char_p R 0` and `char_zero R` need not coincide ([#13080](https://github.com/leanprover-community/mathlib/pull/13080))
Following the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F), this counterexample formalizes a `semiring R` for which `char_p R 0` holds, but `char_zero R` does not.
See [#13075](https://github.com/leanprover-community/mathlib/pull/13075) for the PR that lead to this example.

### [2022-04-10 12:36:58](https://github.com/leanprover-community/mathlib/commit/83225b3)
feat(order/monovary): Add missing `monovary` lemmas ([#13243](https://github.com/leanprover-community/mathlib/pull/13243))
Add lemmas for postcomposing monovarying functions with monotone/antitone functions. Protect lemmas that needed it. Fix typos.

### [2022-04-10 12:36:57](https://github.com/leanprover-community/mathlib/commit/32cc868)
feat(measure_theory/measure/measure_space): let measure.map work with ae_measurable functions ([#13241](https://github.com/leanprover-community/mathlib/pull/13241))
Currently, `measure.map f μ` is zero if `f` is not measurable. This means that one can not say that two integrable random variables `X` and `Y` have the same distribution by requiring `measure.map X μ = measure.map Y μ`, as `X` or `Y` might not be measurable. We adjust the definition of `measure.map` to also work with almost everywhere measurable functions. This means that many results in the library that were only true for measurable functions become true for ae measurable functions. We generalize some of the existing code to this more general setting.

### [2022-04-10 09:05:10](https://github.com/leanprover-community/mathlib/commit/ef51d23)
feat(category_theory/shift): restricting shift functors to a subcategory ([#13265](https://github.com/leanprover-community/mathlib/pull/13265))
Given a family of endomorphisms of `C` which are interwined by a fully faithful `F : C ⥤ D`
with shift functors on `D`, we can promote that family to shift functors on `C`.
For LTE.

### [2022-04-10 09:05:09](https://github.com/leanprover-community/mathlib/commit/c916b64)
feat(ring_theory/polynomial/opposites + data/{polynomial/basic + finsupp/basic}): move `op_ring_equiv` to a new file + lemmas ([#13162](https://github.com/leanprover-community/mathlib/pull/13162))
This PR moves the isomorphism `R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X]` to a new file `ring_theory.polynomial.opposites`.
I also proved some basic lemmas about the equivalence.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members)

### [2022-04-10 09:05:08](https://github.com/leanprover-community/mathlib/commit/d70e26b)
feat(analysis/convex/topology): improve some lemmas ([#13136](https://github.com/leanprover-community/mathlib/pull/13136))
Replace some `s` with `closure s` in the LHS of `⊆` in some lemmas.

### [2022-04-10 06:43:20](https://github.com/leanprover-community/mathlib/commit/208ebd4)
feat(algebra/order/monoid_lemmas_zero_lt): port some lemmas from `algebra.order.monoid_lemmas` ([#12961](https://github.com/leanprover-community/mathlib/pull/12961))
Although the names of these lemmas are from `algebra.order.monoid_lemmas`, many of the lemmas in `algebra.order.monoid_lemmas` have incorrect names, and some others may not be appropriate. Also, many lemmas are missing in `algebra.order.monoid_lemmas`. It may be necessary to make some renames and additions.

### [2022-04-10 06:43:19](https://github.com/leanprover-community/mathlib/commit/00980d9)
feat(group_theory/free_product): The ping pong lemma for free groups ([#12916](https://github.com/leanprover-community/mathlib/pull/12916))
We already have the ping-pong-lemma for free products; phrasing it for free groups is
a (potentially) useful corollary, and brings us on-par with the Wikipedia page.
Again, we state it as a lemma that gives a criteria for when `lift` is injective.

### [2022-04-10 06:43:18](https://github.com/leanprover-community/mathlib/commit/dfc1b4c)
feat(topology/algebra/module/character_space): Introduce the character space of an algebra ([#12838](https://github.com/leanprover-community/mathlib/pull/12838))
The character space of a topological algebra is the subset of elements of the weak dual that are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an isomorphism between a commutative C⋆-algebra and continuous functions on the character space of the algebra. This, in turn, is used to construct the continuous functional calculus on C⋆-algebras.

### [2022-04-10 06:43:17](https://github.com/leanprover-community/mathlib/commit/55baab3)
feat(field_theory/krull_topology): added fintype_alg_hom ([#12777](https://github.com/leanprover-community/mathlib/pull/12777))

### [2022-04-10 06:10:08](https://github.com/leanprover-community/mathlib/commit/36fceb9)
feat(data/list/cycle): Define `cycle.chain` analog to `list.chain` ([#12970](https://github.com/leanprover-community/mathlib/pull/12970))
We define `cycle.chain`, which means that a relation holds in all adjacent elements in a cyclic list. We then show that for `r` a transitive relation, `cycle.chain r l` is equivalent to `r` holding for all pairs of elements in `l`.

### [2022-04-10 04:05:20](https://github.com/leanprover-community/mathlib/commit/de0aea4)
feat(topology/uniform_space/uniform_convergence): add lemma `tendsto_locally_uniformly_iff_forall_tendsto` ([#13201](https://github.com/leanprover-community/mathlib/pull/13201))

### [2022-04-10 04:05:19](https://github.com/leanprover-community/mathlib/commit/26729d6)
chore(ring_theory/polynomial/basic): Generalize `polynomial.degree_lt_equiv` to commutative rings ([#13190](https://github.com/leanprover-community/mathlib/pull/13190))
This is a minor PR to generalise degree_lt_equiv to comm_ring.
Its restriction to field appears to be an oversight.

### [2022-04-10 04:05:18](https://github.com/leanprover-community/mathlib/commit/2ff12ea)
feat(linear_algebra/bilinear_form): generalize from is_symm to is_refl ([#13181](https://github.com/leanprover-community/mathlib/pull/13181))
Generalize some lemmas that assumed symmetric bilinear forms to reflexive bilinear forms (which is more general) and update docstring (before the condition 'symmetric' was not mentioned)

### [2022-04-10 01:48:20](https://github.com/leanprover-community/mathlib/commit/8b8f46e)
feat(analysis/complex/arg): link same_ray and complex.arg ([#12764](https://github.com/leanprover-community/mathlib/pull/12764))

### [2022-04-10 01:48:19](https://github.com/leanprover-community/mathlib/commit/7eff233)
feat(set_theory/cofinality): Golf and extend existing results relating `cof` to `sup` and `bsup` ([#12321](https://github.com/leanprover-community/mathlib/pull/12321))

### [2022-04-10 01:48:17](https://github.com/leanprover-community/mathlib/commit/c2d870e)
feat(set_theory/{ordinal_arithmetic, fixed_points}): Next fixed point of families ([#12200](https://github.com/leanprover-community/mathlib/pull/12200))
We define the next common fixed point of a family of normal ordinal functions. We prove these fixed points to be unbounded, and that their enumerator functions are normal.

### [2022-04-10 01:48:16](https://github.com/leanprover-community/mathlib/commit/b2c707c)
feat(group_theory): use generic `subobject_class` lemmas ([#11758](https://github.com/leanprover-community/mathlib/pull/11758))
This subobject class refactor PR follows up from [#11750](https://github.com/leanprover-community/mathlib/pull/11750) by moving the `{zero,one,add,mul,...}_mem_class` lemmas to the root namespace and marking the previous `sub{monoid,group,module,algebra,...}.{zero,one,add,mul,...}_mem` lemmas as `protected`. This is the second part of [#11545](https://github.com/leanprover-community/mathlib/pull/11545) to be split off.
I made the subobject parameter to the `_mem` lemmas implicit if it appears in the hypotheses, e.g.
```lean
lemma mul_mem {S M : Type*} [monoid M] [set_like S M] [submonoid_class S M]
  {s : S} {x y : M} (hx : x ∈ s) (hy : y ∈ s) : x * y ∈ s
```
instead of having `(s : S)` explicit. The generic `_mem` lemmas are not namespaced, so there is no dot notation that requires `s` to be explicit. Also there were already a couple of instances for the same operator where `s` was implicit and others where `s` was explicit, so some change was needed.

### [2022-04-10 01:48:15](https://github.com/leanprover-community/mathlib/commit/d133874)
feat(representation_theory/basic): basics of group representation theory ([#11207](https://github.com/leanprover-community/mathlib/pull/11207))
Some basic lemmas about group representations and some theory regarding the subspace of fixed points of a representation.

### [2022-04-10 01:48:14](https://github.com/leanprover-community/mathlib/commit/3fe5c93)
feat(algebra/ring/boolean_ring): Turning a Boolean algebra into a Boolean ring ([#6476](https://github.com/leanprover-community/mathlib/pull/6476))
Define `as_boolring`, a type synonym to turn a Boolean algebra into a Boolean ring and show that `as_boolring` and `as_boolalg` are "inverse" to each other.

### [2022-04-10 01:48:13](https://github.com/leanprover-community/mathlib/commit/9495b8c)
feat(data/set/intervals/with_bot_top): lemmas about `I??` and `with_top/bot` ([#4273](https://github.com/leanprover-community/mathlib/pull/4273))
Prove theorems about (pre)images of intervals under `coe : α → with_top α` and `coe : α → with_bot α`.

### [2022-04-09 23:54:02](https://github.com/leanprover-community/mathlib/commit/e4f93e6)
feat(group_theory/solvable): Golf some proofs ([#13271](https://github.com/leanprover-community/mathlib/pull/13271))
This PR uses `solvable_of_ker_le_range` to golf some proofs.

### [2022-04-09 23:54:01](https://github.com/leanprover-community/mathlib/commit/b7f7c4a)
feat(combinatorics/simple_graph/clique): Cliques ([#12982](https://github.com/leanprover-community/mathlib/pull/12982))
Define cliques.

### [2022-04-09 22:07:41](https://github.com/leanprover-community/mathlib/commit/e690875)
chore(ring_theory/roots_of_unity): generalise ([#13261](https://github.com/leanprover-community/mathlib/pull/13261))

### [2022-04-09 22:07:40](https://github.com/leanprover-community/mathlib/commit/3879621)
feat(combinatorics/additive/salem_spencer): The sphere does not contain arithmetic progressions ([#13259](https://github.com/leanprover-community/mathlib/pull/13259))
Prove that the frontier of a strictly convex closed set is Salem-Spencer. For this we need
* simple lemmas about `same_ray`. This involves renaming `same_ray.exists_right_eq_smul`/`same_ray.exists_left_eq_smul` to `same_ray.exists_nonneg_left`/`same_ray.exists_nonneg_right`.
* that the norm in a real normed space is injective on rays.
* that the midpoint of two points of equal norm has smaller norm, in a strictly convex space

### [2022-04-09 22:07:39](https://github.com/leanprover-community/mathlib/commit/b3a0f85)
feat(group_theory/coset): Fintype instance for quotient by the right relation ([#13257](https://github.com/leanprover-community/mathlib/pull/13257))
This PR adds a fintype instance for the quotient by the right relation.

### [2022-04-09 22:07:38](https://github.com/leanprover-community/mathlib/commit/e3a8ef1)
feat(algebra/algebra/*): generalise ([#13252](https://github.com/leanprover-community/mathlib/pull/13252))
Some generalisations straight from Alex's generalisation linter, with some care about how to place them. Some `algebra` lemmas are weakened to semirings, allowing us to talk about ℕ-algebras much more easily.

### [2022-04-09 22:07:37](https://github.com/leanprover-community/mathlib/commit/1480161)
feat(group_theory/group_action/basic): Left multiplication satisfies the `quotient_action` axiom ([#13249](https://github.com/leanprover-community/mathlib/pull/13249))
This PR adds an instance `quotient_action α H`, meaning that left multiplication satisfies the `quotient_action` axiom.

### [2022-04-09 22:07:36](https://github.com/leanprover-community/mathlib/commit/22b7d21)
feat(analysis/normed*): if `f → 0` and `g` is bounded, then `f * g → 0` ([#13248](https://github.com/leanprover-community/mathlib/pull/13248))
Also drop `is_bounded_under_of_tendsto`: it's just `h.norm.is_bounded_under_le`.

### [2022-04-09 22:07:35](https://github.com/leanprover-community/mathlib/commit/4c4e5e8)
feat(analysis/locally_convex): every totally bounded set is von Neumann bounded ([#13204](https://github.com/leanprover-community/mathlib/pull/13204))
Add one lemma and some cleanups of previous PR.

### [2022-04-09 19:44:54](https://github.com/leanprover-community/mathlib/commit/cc65716)
refactor(analysis/complex): replace `diff_on_int_cont` with `diff_cont_on_cl` ([#13148](https://github.com/leanprover-community/mathlib/pull/13148))
Use "differentiable on a set and continuous on its closure" instead of "continuous on a set and differentiable on its interior".
There are a few reasons to prefer the latter:
* it has better "composition" lemma;
* it allows us to talk about functions that are, e.g., differentiable on `{z : ℂ | abs z < 1 ∧ (re z < 0 ∨ im z ≠ 0)}` and continuous on the closed unit disk.
Also generalize `eq_on_of_eq_on_frontier` from a compact set to a bounded set (so that it works, e.g., for the unit ball in a Banach space).
This PR does not move the file `diff_on_int_cont` to make the diff more readable; the file will be moved in another PR.

### [2022-04-09 19:44:52](https://github.com/leanprover-community/mathlib/commit/57f382a)
feat(order/bounds): Boundedness of monotone/antitone functions ([#13079](https://github.com/leanprover-community/mathlib/pull/13079))

### [2022-04-09 19:44:50](https://github.com/leanprover-community/mathlib/commit/0dde2cb)
feat(data/list/chain): Lemma for `chain r a (list.range n.succ)` ([#12990](https://github.com/leanprover-community/mathlib/pull/12990))

### [2022-04-09 17:28:10](https://github.com/leanprover-community/mathlib/commit/bc140d2)
feat(data/polynomial/degree/lemmas): add some lemmas and rename some lemmas ([#13235](https://github.com/leanprover-community/mathlib/pull/13235))
rename `nat_degree_mul_C_eq_of_no_zero_divisors` to `nat_degree_mul_C`
rename `nat_degree_C_mul_eq_of_no_zero_divisors` to `nat_degree_C_mul`

### [2022-04-09 17:28:09](https://github.com/leanprover-community/mathlib/commit/f8467aa)
feat(data/polynomial/eval): add some lemmas for `eval₂` ([#13234](https://github.com/leanprover-community/mathlib/pull/13234))

### [2022-04-09 17:28:08](https://github.com/leanprover-community/mathlib/commit/25d28c8)
feat(group_theory/schreier): Add version of Schreier's lemma ([#13231](https://github.com/leanprover-community/mathlib/pull/13231))
This PR adds a version of Schreier's lemma of the form `closure (_ : set H) = ⊤`, as opposed to `closure (_ : set G) = H`. This is closer to saying that `H` is finitely generated.
I also fiddled with the names a bit.

### [2022-04-09 17:28:06](https://github.com/leanprover-community/mathlib/commit/d831478)
feat(computability/encoding): Bounds on cardinality from an encoding ([#13224](https://github.com/leanprover-community/mathlib/pull/13224))
Generalizes universe variables for `computability.encoding`
Uses a `computability.encoding` to bound the cardinality of a type

### [2022-04-09 17:28:05](https://github.com/leanprover-community/mathlib/commit/6abb6de)
feat(category_theory/bicategory): monoidal categories are single object bicategories ([#13157](https://github.com/leanprover-community/mathlib/pull/13157))

### [2022-04-09 17:28:04](https://github.com/leanprover-community/mathlib/commit/823699f)
feat(linear_algebra/general_linear_group): Add some lemmas about SL to GL_pos coercions. ([#12393](https://github.com/leanprover-community/mathlib/pull/12393))

### [2022-04-09 15:37:04](https://github.com/leanprover-community/mathlib/commit/d42f6a8)
chore(algebra/associated): golf irreducible_iff_prime_iff ([#13267](https://github.com/leanprover-community/mathlib/pull/13267))

### [2022-04-09 15:37:03](https://github.com/leanprover-community/mathlib/commit/348b41d)
chore(archive/imo/imo1994_q1): tidy a bit ([#13266](https://github.com/leanprover-community/mathlib/pull/13266))

### [2022-04-09 15:37:02](https://github.com/leanprover-community/mathlib/commit/1d9d153)
chore(algebraic_geometry/pullbacks): replaced some simps by simp onlys ([#13258](https://github.com/leanprover-community/mathlib/pull/13258))
This PR optimizes the file `algebraic_geometry/pullbacks` by replacing some calls to `simp` by `simp only [⋯]`.
This file has a high [`sec/LOC` ratio](https://mathlib-bench.limperg.de/commit/5e98dc1cc915d3226ea293c118d2ff657b48b0dc) and is not very short, which makes it a good candidate for such optimizations attempts.
On my machine, these changes reduced the compile time from 2m30s to 1m20s.

### [2022-04-09 15:37:01](https://github.com/leanprover-community/mathlib/commit/8c7e8a4)
feat(group_theory/commutator): The commutator subgroup is characteristic ([#13255](https://github.com/leanprover-community/mathlib/pull/13255))
This PR adds instances stating that the commutator subgroup is characteristic.

### [2022-04-09 15:37:00](https://github.com/leanprover-community/mathlib/commit/d23fd6f)
refactor(group_theory/solvable): Golf and move `solvable_of_ker_le_range` ([#13254](https://github.com/leanprover-community/mathlib/pull/13254))
This PR moves `solvable_of_ker_le_range` to earlier in the file so that it can be used to golf the proofs of `solvable_of_solvable_injective` and `solvable_of_surjective`.

### [2022-04-09 15:02:56](https://github.com/leanprover-community/mathlib/commit/f24918e)
refactor(group_theory/solvable): Golf some proofs ([#13256](https://github.com/leanprover-community/mathlib/pull/13256))
This PR golfs some proofs in `group_theory/solvable.lean`.

### [2022-04-09 12:31:00](https://github.com/leanprover-community/mathlib/commit/d6ff44e)
feat(category_theory/faithful): map_iso_injective ([#13263](https://github.com/leanprover-community/mathlib/pull/13263))

### [2022-04-09 10:39:57](https://github.com/leanprover-community/mathlib/commit/7a0513d)
feat(data/nat/*): generalize typeclass assumptions ([#13260](https://github.com/leanprover-community/mathlib/pull/13260))

### [2022-04-09 07:19:58](https://github.com/leanprover-community/mathlib/commit/f5ee47b)
feat(category_theory/triangulated): upgrade map_triangle to a functor ([#13262](https://github.com/leanprover-community/mathlib/pull/13262))
Useful for LTE.

### [2022-04-09 06:37:15](https://github.com/leanprover-community/mathlib/commit/a98a26b)
chore(measure_theory): move lemmas about `ae_measurable` to a new file ([#13246](https://github.com/leanprover-community/mathlib/pull/13246))

### [2022-04-09 05:46:44](https://github.com/leanprover-community/mathlib/commit/59cf367)
chore(analysis/special_functions/pow): golf a proof ([#13247](https://github.com/leanprover-community/mathlib/pull/13247))
`complex.continuous_at_cpow_const` follows from `complex.continuous_at_cpow`.

### [2022-04-09 00:02:05](https://github.com/leanprover-community/mathlib/commit/2a04ec0)
feat(data/list/big_operators): More lemmas about alternating product ([#13195](https://github.com/leanprover-community/mathlib/pull/13195))
A few more lemmas about `list.alternating_prod` and `list.alternating_sum` and a proof that 11 divides even length base 10 palindromes.
Also rename `palindrome` to `list.palindrome` (as it should have been).

### [2022-04-08 21:51:39](https://github.com/leanprover-community/mathlib/commit/485d648)
feat(algebra/big_operators): some big operator lemmas ([#13066](https://github.com/leanprover-community/mathlib/pull/13066))
Note that `prod_coe_sort` is essentially `prod_finset_coe` restated with the relatively new `finset.has_coe_to_sort`. I can also place `prod_finset_coe` with `prod_coe_sort` if we prefer.

### [2022-04-08 17:20:39](https://github.com/leanprover-community/mathlib/commit/9498bea)
feat(group_theory/group_action/fixing_subgroup): add lemmas about fixing_subgroup ([#13202](https://github.com/leanprover-community/mathlib/pull/13202))
- pull back here the definition of fixing_subgroup and fixing_submonoid from field_theory.galois
- add lemmas about fixing_subgroup or fixing_submonoid in the context of mul_action
- add Galois connection relating it with fixed_points.

### [2022-04-08 15:41:02](https://github.com/leanprover-community/mathlib/commit/ed266e5)
feat(category_theory/limits/terminal): limit of the constant terminal functor ([#13238](https://github.com/leanprover-community/mathlib/pull/13238))
Needed in LTE.

### [2022-04-08 15:41:01](https://github.com/leanprover-community/mathlib/commit/afa9be2)
feat(category_theory/limits/pullbacks): missing simp lemmas ([#13237](https://github.com/leanprover-community/mathlib/pull/13237))
Absence noted in LTE.

### [2022-04-08 15:40:59](https://github.com/leanprover-community/mathlib/commit/0521344)
feat(analysis/locally_convex/basic): add lemmas about finite unions for absorbs ([#13236](https://github.com/leanprover-community/mathlib/pull/13236))
- Lemma for absorbing sets and addition
- Two Lemmas for absorbing sets as finite unions (set.finite and finset variant)
- Lemma for absorbent sets absorb finite sets.

### [2022-04-08 15:40:58](https://github.com/leanprover-community/mathlib/commit/0831e4f)
feat(data/polynomial/degree/definitions): add `degree_monoid_hom` ([#13233](https://github.com/leanprover-community/mathlib/pull/13233))
It will be used to simplify the proof of some lemmas.

### [2022-04-08 13:45:44](https://github.com/leanprover-community/mathlib/commit/f5d4fa1)
feat(data/fintype/basic): add `fintype_of_{equiv,option}` ([#13086](https://github.com/leanprover-community/mathlib/pull/13086))
`fintype_of_option_equiv` was extracted from @huynhtrankhanh's https://github.com/leanprover-community/mathlib/pull/11162, moved here to a separate PR.  The split into `fintype_of_option` and `fintype_of_equiv` is based on a comment on that PR by @jcommelin.

### [2022-04-08 13:45:43](https://github.com/leanprover-community/mathlib/commit/d96e17d)
feat(data/multiset/basic): add `map_le_map_iff` and `map_embedding` ([#13082](https://github.com/leanprover-community/mathlib/pull/13082))
Adds lemmas `map_le_map_iff : s.map f ≤ t.map f ↔ s ≤ t` and `map_embedding : multiset α ↪o multiset β` for embedding `f`.
Extracted from @huynhtrankhanh's [#11162](https://github.com/leanprover-community/mathlib/pull/11162), moved here to a separate PR

### [2022-04-08 13:45:41](https://github.com/leanprover-community/mathlib/commit/5acaeaf)
chore(computability/language): Golf ([#13039](https://github.com/leanprover-community/mathlib/pull/13039))
Golf the `semiring` instance using the `set.image2` API, add half missing docstring.

### [2022-04-08 13:45:40](https://github.com/leanprover-community/mathlib/commit/2569ad5)
feat(data/set/intervals/basic): An open interval of a dense order has no maximum/minimum ([#12924](https://github.com/leanprover-community/mathlib/pull/12924))

### [2022-04-08 12:12:47](https://github.com/leanprover-community/mathlib/commit/91ce04d)
chore(model_theory/encoding): Move the encoding for terms to its own file ([#13223](https://github.com/leanprover-community/mathlib/pull/13223))
Moves the declarations about encodings and cardinality of terms to their own file, `model_theory/encoding`

### [2022-04-08 12:12:46](https://github.com/leanprover-community/mathlib/commit/ed68854)
feat(model_theory/*): Theory of nonempty structures and bundling elementary substructures ([#13118](https://github.com/leanprover-community/mathlib/pull/13118))
Defines a sentence and theory to indicate a structure is nonempty
Defines a map to turn elementary substructures of a bundled model into bundled models

### [2022-04-08 12:12:45](https://github.com/leanprover-community/mathlib/commit/710fe04)
feat(model_theory/order): Defines ordered languages and structures ([#13088](https://github.com/leanprover-community/mathlib/pull/13088))
Defines ordered languages and ordered structures
Defines the theories of pre-, partial, and linear orders, shows they are modeled by the respective structures.

### [2022-04-08 12:12:44](https://github.com/leanprover-community/mathlib/commit/7340720)
feat(group_theory/group_action/basic): Add typeclass for actions that descend to the quotient ([#12999](https://github.com/leanprover-community/mathlib/pull/12999))
Part of [#12848](https://github.com/leanprover-community/mathlib/pull/12848).

### [2022-04-08 11:40:03](https://github.com/leanprover-community/mathlib/commit/851b320)
feat(ring_theory/localization): b is linear independent over R iff l.i. over `Frac(R)` ([#13041](https://github.com/leanprover-community/mathlib/pull/13041))

### [2022-04-08 07:42:13](https://github.com/leanprover-community/mathlib/commit/7d41715)
feat(archive/imo/imo2008_q3): golf ([#13232](https://github.com/leanprover-community/mathlib/pull/13232))

### [2022-04-08 07:42:12](https://github.com/leanprover-community/mathlib/commit/e85dc17)
feat(group_theory/subgroup/basic): The centralizer of a characteristic subgroup is characteristic ([#13230](https://github.com/leanprover-community/mathlib/pull/13230))
This PR proves that the centralizer of a characteristic subgroup is characteristic.

### [2022-04-08 07:42:10](https://github.com/leanprover-community/mathlib/commit/95ebbad)
refactor(group_theory/commutator): Move `commutator_le_map_commutator` ([#13229](https://github.com/leanprover-community/mathlib/pull/13229))
`commutator_le_map_commutator` is a general lemma about commutators, so it should be moved from `solvable.lean` to `commutator.lean`.

### [2022-04-08 07:42:09](https://github.com/leanprover-community/mathlib/commit/1a4203a)
feat(group_theory/coset): Right cosets are in bijection with left cosets ([#13228](https://github.com/leanprover-community/mathlib/pull/13228))
Right cosets are in bijection with left cosets. This came up in some work involving right transversals.

### [2022-04-08 07:42:08](https://github.com/leanprover-community/mathlib/commit/499a4a8)
feat(group_theory/index): `fintype_of_index_ne_zero` ([#13225](https://github.com/leanprover-community/mathlib/pull/13225))
This PR adds `fintype_of_index_ne_zero`.

### [2022-04-08 06:14:18](https://github.com/leanprover-community/mathlib/commit/ccf3e37)
feat(ring_theory/unique_factorization_domain): alternative specification for `count (normalized_factors x)` ([#13161](https://github.com/leanprover-community/mathlib/pull/13161))
`count_normalized_factors_eq` specifies the number of times an irreducible factor `p` appears in `normalized_factors x`, namely the number of times it divides `x`. This is often easier to work with than going through `multiplicity` since this way we avoid coercing to `enat`.

### [2022-04-08 06:14:17](https://github.com/leanprover-community/mathlib/commit/0c424e9)
refactor(analysis/normed_space/conformal_linear_map): redefine ([#13143](https://github.com/leanprover-community/mathlib/pull/13143))
Use equality of bundled maps instead of coercions to functions in the definition of `is_conformal_map`. Also golf some proofs.

### [2022-04-08 06:14:16](https://github.com/leanprover-community/mathlib/commit/036fc99)
feat(topology/uniform_space/uniform_convergence): add `tendsto_uniformly_iff_seq_tendsto_uniformly` ([#13128](https://github.com/leanprover-community/mathlib/pull/13128))
For countably generated filters, uniform convergence is equivalent to uniform convergence of sub-sequences.

### [2022-04-08 06:14:15](https://github.com/leanprover-community/mathlib/commit/ab60244)
feat(model_theory/basic,bundled): Structures induced by equivalences ([#13124](https://github.com/leanprover-community/mathlib/pull/13124))
Defines `equiv.induced_Structure`, a structure on the codomain of a bijection that makes the bijection an isomorphism.
Defines maps on bundled models to shift them along bijections and up and down universes.

### [2022-04-08 05:13:45](https://github.com/leanprover-community/mathlib/commit/9f3e7fb)
feat(category_theory/limits): further API for commuting limits ([#13215](https://github.com/leanprover-community/mathlib/pull/13215))
Needed for LTE.

### [2022-04-08 02:06:33](https://github.com/leanprover-community/mathlib/commit/5e98dc1)
feat(topology/continuous_function/zero_at_infty): add more instances for zero_at_infty_continuous_map and establish C₀ functorial properties ([#13196](https://github.com/leanprover-community/mathlib/pull/13196))
This adds more instances for the type `C₀(α, β)` of continuous functions vanishing at infinity. Notably, these new instances include its non-unital ring, normed space and star structures, culminating with `cstar_ring` when `β` is a `cstar_ring` which is also a `topological_ring`.
In addition, this establishes functorial properties of `C₀(-, β)` for various choices of algebraic categories involving `β`. The domain of these (contravariant) functors is the category of topological spaces with cocompact continuous maps, and the functor applied to a cocompact map is given by pre-composition.

### [2022-04-08 00:26:57](https://github.com/leanprover-community/mathlib/commit/0719b36)
feat(category_theory/limits/shapes): isomorphisms of (co)spans ([#13216](https://github.com/leanprover-community/mathlib/pull/13216))

### [2022-04-08 00:26:56](https://github.com/leanprover-community/mathlib/commit/b897115)
chore(algebra/associated): generalisation linter ([#13108](https://github.com/leanprover-community/mathlib/pull/13108))

### [2022-04-07 22:31:46](https://github.com/leanprover-community/mathlib/commit/cae5164)
chore(algebra/order/{monoid,ring}): missing typeclasses about `*` and `+` on `order_dual` ([#13004](https://github.com/leanprover-community/mathlib/pull/13004))

### [2022-04-07 20:32:53](https://github.com/leanprover-community/mathlib/commit/02a2560)
feat(analysis/normed_space/add_torsor_bases): add `convex.interior_nonempty_iff_affine_span_eq_top` ([#13220](https://github.com/leanprover-community/mathlib/pull/13220))
Generalize `interior_convex_hull_nonempty_iff_aff_span_eq_top` to any
convex set, not necessarily written as the convex hull of a set.

### [2022-04-07 20:32:52](https://github.com/leanprover-community/mathlib/commit/0f4d0ae)
feat(data/polynomial/identities): golf using `linear_combination` ([#13212](https://github.com/leanprover-community/mathlib/pull/13212))

### [2022-04-07 20:32:51](https://github.com/leanprover-community/mathlib/commit/3b04f48)
feat(number_theory/fermat4): golf using `linear_combination` ([#13211](https://github.com/leanprover-community/mathlib/pull/13211))

### [2022-04-07 20:32:50](https://github.com/leanprover-community/mathlib/commit/82d1e9f)
feat(algebra/quadratic_discriminant): golf using `linear_combination` ([#13210](https://github.com/leanprover-community/mathlib/pull/13210))

### [2022-04-07 18:41:47](https://github.com/leanprover-community/mathlib/commit/4ff75f5)
refactor(category_theory/bicategory): set simp-normal form for 2-morphisms ([#13185](https://github.com/leanprover-community/mathlib/pull/13185))
## Problem
The definition of bicategories contains the following axioms:
```lean
associator_naturality_left : ∀ {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
  (η ▷ g) ▷ h ≫ (α_ f' g h).hom = (α_ f g h).hom ≫ η ▷ (g ≫ h)
associator_naturality_middle : ∀ (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
  (f ◁ η) ▷ h ≫ (α_ f g' h).hom = (α_ f g h).hom ≫ f ◁ (η ▷ h)
associator_naturality_right : ∀ (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
  (f ≫ g) ◁ η ≫ (α_ f g h').hom = (α_ f g h).hom ≫ f ◁ (g ◁ η) 
left_unitor_naturality : ∀ {f g : a ⟶ b} (η : f ⟶ g),
  𝟙 a ◁ η ≫ (λ_ g).hom = (λ_ f).hom ≫ η
right_unitor_naturality : ∀ {f g : a ⟶ b} (η : f ⟶ g) :
  η ▷ 𝟙 b ≫ (ρ_ g).hom = (ρ_ f).hom ≫ η
```
By using these axioms, we can see that, for example, 2-morphisms `(f₁ ≫ f₂) ◁ (f₃ ◁ (η ▷ (f₄ ≫ f₅)))` and `f₁ ◁ ((𝟙_ ≫ f₂ ≫ f₃) ◁ ((η ▷ f₄) ▷ f₅))` are equal up to some associators and unitors. The problem is that the proof of this fact requires tedious rewriting. We should insert appropriate associators and unitors, and then rewrite using the above axioms manually.
This tedious rewriting is also a problem when we use the (forthcoming) `coherence` tactic (bicategorical version of [#13125](https://github.com/leanprover-community/mathlib/pull/13125)), which only works if the non-structural 2-morphisms in the LHS and the RHS are the same.
## Main change
The main proposal of this PR is to introduce a normal form of such 2-morphisms, and put simp attributes to suitable lemmas in order to rewrite any 2-morphism into the normal form. For example, the normal form of the previouse example is `f₁ ◁ (f₂ ◁ (f₃ ◁ ((η ▷ f₄) ▷ f₅)))`. The precise definition of the normal form can be found in the docs in `basic.lean` file. The new simp lemmas introduced in this PR are the following:
```lean
whisker_right_comp : ∀ {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
  η ▷ (g ≫ h) = (α_ f g h).inv ≫ η ▷ g ▷ h ≫ (α_ f' g h).hom 
whisker_assoc : ∀ (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
  (f ◁ η) ▷ h = (α_ f g h).hom ≫ f ◁ (η ▷ h) ≫ (α_ f g' h).inv
comp_whisker_left : ∀ (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
  (f ≫ g) ◁ η = (α_ f g h).hom ≫ f ◁ g ◁ η ≫ (α_ f g h').inv
id_whisker_left : ∀ {f g : a ⟶ b} (η : f ⟶ g),
  𝟙 a ◁ η = (λ_ f).hom ≫ η ≫ (λ_ g).inv
whisker_right_id : ∀ {f g : a ⟶ b} (η : f ⟶ g),
  η ▷ 𝟙 b = (ρ_ f).hom ≫ η ≫ (ρ_ g).inv
```
Logically, these are equivalent to the five axioms presented above. The point is that these equalities have the definite simplification direction.
## Improvement 
Some proofs that had been based on tedious rewriting are now automated. For example, the conditions in `oplax_nat_trans.id`, `oplax_nat_trans.comp`, and several functions in `functor_bicategory.lean` are now proved by `tidy`.
## Specific changes
- The new simp lemmas `whisker_right_comp` etc. actually have been included in the definition of bicategories instead of `associate_naturality_left` etc. so that the latter lemmas are proved in later of the file just by `simp`.
- The precedence of the whiskering notations "infixr ` ◁ `:70" and "infixr ` ◁ `:70" have been changed into "infixr ` ◁ `:81" and "infixr ` ◁ `:81", which is now higher than that of the composition `≫`. This setting is consistent with the normal form introduced in this PR in the sence that an expression is in normal form only if it has the minimal number of parentheses in this setting. For example, the normal form `f₁ ◁ (f₂ ◁ (f₃ ◁ ((η ▷ f₄) ▷ f₅)))` can be written as `f₁ ◁ f₂ ◁ f₃ ◁ η ▷ f₄ ▷ f₅`.
- The unneeded parentheses caused by the precedence change have been removed.
- The lemmas `whisker_right_id` and `whisker_right_comp` have been renamed to `id_whisker_right` and `comp_whisker_right` since these are more consistent with the notation. Note that the name `whisker_right_id` and `whisker_right_comp` are now used for the two of the five simp lemmas presented above.
- The lemmas in `basic.lean` have been rearranged to be more logically consistent.
## Future work
I would like to apply a similar strategy for monoidal categories.

### [2022-04-07 18:41:46](https://github.com/leanprover-community/mathlib/commit/44c31d8)
feat(data/finset/basic): add `map_injective` and `sigma_equiv_option_of_inhabited` ([#13083](https://github.com/leanprover-community/mathlib/pull/13083))
Adds `map_injective (f : α ↪ β) : injective (map f) := (map_embedding f).injective` and `sigma_equiv_option_of_inhabited [inhabited α] : Σ (β : Type u), α ≃ option β`.
Extracted from @huynhtrankhanh's https://github.com/leanprover-community/mathlib/pull/11162, moved here to a separate PR

### [2022-04-07 18:41:45](https://github.com/leanprover-community/mathlib/commit/9d786ce)
feat(topology/metric/basic): construct a bornology from metric axioms and add it to the pseudo metric structure ([#12078](https://github.com/leanprover-community/mathlib/pull/12078))
Every metric structure naturally gives rise to a bornology where the bounded sets are precisely the metric bounded sets. The eventual goal will be to replace the existing `metric.bounded` with one defined in terms of the bornology, so we need to construct the bornology first, as we do here.

### [2022-04-07 16:53:29](https://github.com/leanprover-community/mathlib/commit/2d2d09c)
feat(data/nat/gcd): added gcd_mul_of_dvd_coprime ([#12989](https://github.com/leanprover-community/mathlib/pull/12989))
Added gcd_mul_of_dvd_coprime lemma to gcd.lean.

### [2022-04-07 16:20:47](https://github.com/leanprover-community/mathlib/commit/733aed5)
chore(group_theory/index): Add `to_additive` ([#13191](https://github.com/leanprover-community/mathlib/pull/13191))
This PR adds `to_additive` to the rest of `group_theory/index.lean`.

### [2022-04-07 16:20:46](https://github.com/leanprover-community/mathlib/commit/c522e3b)
feat(data/polynomial/basic): add simp lemmas X_mul_C and X_pow_mul_C ([#13163](https://github.com/leanprover-community/mathlib/pull/13163))
These lemmas are direct applications of `X_mul` and `X_pow_mul`.  However, their more general version cannot be `simp` lemmas since they form loops.  These versions do not, since they involve an explicit `C`.
I golfed slightly a proof in `linear_algebra.eigenspace` since it was timing out.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/polynomial.20op_C/near/277703846)

### [2022-04-07 16:20:44](https://github.com/leanprover-community/mathlib/commit/6a0524f)
feat(category_theory/monoidal): upgrades for monoidal equivalences ([#13158](https://github.com/leanprover-community/mathlib/pull/13158))
(Recall that a "monoidal equivalence" is a functor which is separately monoidal, and an equivalence.
This PR completes the work required to see this is the same as having a monoidal inverse, up to monoidal units and counits.)
* Shows that the unit and counit of a monoidal equivalence have a natural monoidal structure. 
* Previously, when transporting a monoidal structure across a (non-monoidal) equivalence,
we constructed directly the monoidal strength on the inverse functor. In the meantime, @b-mehta has provided a general construction for the monoidal strength on the inverse of any monoidal equivalence, so now we use that.
The proofs of `monoidal_unit` and `monoidal_counit` in `category_theory/monoidal/natural_transformation.lean` are quite ugly. If anyone would like to golf these that would be lovely! :-)

### [2022-04-07 16:20:43](https://github.com/leanprover-community/mathlib/commit/d7ad7d3)
feat(set_theory/cardinal): Upper bound on domain from upper bound on fibers ([#13147](https://github.com/leanprover-community/mathlib/pull/13147))
A uniform upper bound on fibers gives an upper bound on the domain.

### [2022-04-07 16:20:41](https://github.com/leanprover-community/mathlib/commit/47a3cd2)
feat(probability/integration): Bochner integral of the product of independent functions ([#13140](https://github.com/leanprover-community/mathlib/pull/13140))
This is limited to real-valued functions, which is not very satisfactory but it is not clear (to me) what the most general version of each of those lemmas would be.

### [2022-04-07 16:20:40](https://github.com/leanprover-community/mathlib/commit/ab1bf0f)
feat(algebra/order/monoid): add eq_one_or_one_lt ([#13131](https://github.com/leanprover-community/mathlib/pull/13131))
Needed in LTE.

### [2022-04-07 16:20:39](https://github.com/leanprover-community/mathlib/commit/7c04f36)
feat(group_theory/schreier): prove Schreier's lemma ([#13019](https://github.com/leanprover-community/mathlib/pull/13019))
This PR adds a proof of Schreier's lemma.

### [2022-04-07 16:20:37](https://github.com/leanprover-community/mathlib/commit/315bff3)
feat(archive/100-theorems-list/37_solution_of_cubic): golf ([#13012](https://github.com/leanprover-community/mathlib/pull/13012))
Express one of the lemmas for the solution of the cubic as a giant `linear_combination` calculation.

### [2022-04-07 14:25:29](https://github.com/leanprover-community/mathlib/commit/c4f3869)
chore(order/symm_diff): Change the symmetric difference notation ([#13217](https://github.com/leanprover-community/mathlib/pull/13217))
The notation for `symm_diff` was `Δ` (`\D`, `\GD`, `\Delta`). It now is `∆` (`\increment`).

### [2022-04-07 14:25:16](https://github.com/leanprover-community/mathlib/commit/ac5188d)
chore(algebra/char_p/{basic + algebra}): weaken assumptions for char_p_to_char_zero ([#13214](https://github.com/leanprover-community/mathlib/pull/13214))
The assumptions for lemma `char_p_to_char_zero` can be weakened, without changing the proof.
Since the weakening breaks up one typeclass assumption into two, when the lemma was applied with `@`, I inserted an extra `_`.  This happens twice: once in the file where the lemma is, and once in a separate file.

### [2022-04-07 14:25:13](https://github.com/leanprover-community/mathlib/commit/321d159)
feat(algebra/order/monoid): generalize, convert to `to_additive` and iff of `lt_or_lt_of_mul_lt_mul` ([#13192](https://github.com/leanprover-community/mathlib/pull/13192))
I converted a lemma showing
`m + n < a + b →  m < a ∨ n < b`
to the `to_additive` version of a lemma showing
`m * n < a * b →  m < a ∨ n < b`.
I also added a lemma showing `m * n < a * b ↔  m < a ∨ n < b` and its `to_additive` version.

### [2022-04-07 12:26:52](https://github.com/leanprover-community/mathlib/commit/506ad31)
feat(order/monotone): simp lemmas for monotonicity in dual orders ([#13207](https://github.com/leanprover-community/mathlib/pull/13207))
Add 4 lemmas of the kind `antitone_to_dual_comp_iff`
Add their variants for `antitone_on`
Add their strict variants

### [2022-04-07 11:44:37](https://github.com/leanprover-community/mathlib/commit/be147af)
feat(ring_theory/graded_algebra/homogeneous_localization): homogeneous localization ring is local ([#13071](https://github.com/leanprover-community/mathlib/pull/13071))
showed that `local_ring (homogeneous_localization 𝒜 x)` from prime ideal `x`

### [2022-04-07 10:39:20](https://github.com/leanprover-community/mathlib/commit/3e4bf5d)
feat(order/symm_diff): More symmetric difference lemmas ([#13133](https://github.com/leanprover-community/mathlib/pull/13133))
A few more `symm_diff` lemmas.

### [2022-04-07 07:05:52](https://github.com/leanprover-community/mathlib/commit/faa7e52)
chore(group_theory/index): Add `to_additive` ([#13191](https://github.com/leanprover-community/mathlib/pull/13191))
This PR adds `to_additive` to the rest of `group_theory/index.lean`.

### [2022-04-07 07:05:50](https://github.com/leanprover-community/mathlib/commit/45a8f6c)
feat(data/polynomial/basic): add simp lemmas X_mul_C and X_pow_mul_C ([#13163](https://github.com/leanprover-community/mathlib/pull/13163))
These lemmas are direct applications of `X_mul` and `X_pow_mul`.  However, their more general version cannot be `simp` lemmas since they form loops.  These versions do not, since they involve an explicit `C`.
I golfed slightly a proof in `linear_algebra.eigenspace` since it was timing out.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/polynomial.20op_C/near/277703846)

### [2022-04-07 07:05:49](https://github.com/leanprover-community/mathlib/commit/d047eb4)
feat(category_theory/monoidal): upgrades for monoidal equivalences ([#13158](https://github.com/leanprover-community/mathlib/pull/13158))
(Recall that a "monoidal equivalence" is a functor which is separately monoidal, and an equivalence.
This PR completes the work required to see this is the same as having a monoidal inverse, up to monoidal units and counits.)
* Shows that the unit and counit of a monoidal equivalence have a natural monoidal structure. 
* Previously, when transporting a monoidal structure across a (non-monoidal) equivalence,
we constructed directly the monoidal strength on the inverse functor. In the meantime, @b-mehta has provided a general construction for the monoidal strength on the inverse of any monoidal equivalence, so now we use that.
The proofs of `monoidal_unit` and `monoidal_counit` in `category_theory/monoidal/natural_transformation.lean` are quite ugly. If anyone would like to golf these that would be lovely! :-)

### [2022-04-07 07:05:48](https://github.com/leanprover-community/mathlib/commit/91db821)
feat(set_theory/cardinal): Upper bound on domain from upper bound on fibers ([#13147](https://github.com/leanprover-community/mathlib/pull/13147))
A uniform upper bound on fibers gives an upper bound on the domain.

### [2022-04-07 07:05:46](https://github.com/leanprover-community/mathlib/commit/409f5f2)
feat(probability/integration): Bochner integral of the product of independent functions ([#13140](https://github.com/leanprover-community/mathlib/pull/13140))
This is limited to real-valued functions, which is not very satisfactory but it is not clear (to me) what the most general version of each of those lemmas would be.

### [2022-04-07 07:05:45](https://github.com/leanprover-community/mathlib/commit/fabad7e)
feat(order/symm_diff): More symmetric difference lemmas ([#13133](https://github.com/leanprover-community/mathlib/pull/13133))
A few more `symm_diff` lemmas.

### [2022-04-07 07:05:44](https://github.com/leanprover-community/mathlib/commit/2a74d4e)
feat(algebra/order/monoid): add eq_one_or_one_lt ([#13131](https://github.com/leanprover-community/mathlib/pull/13131))
Needed in LTE.

### [2022-04-07 07:05:40](https://github.com/leanprover-community/mathlib/commit/9eff8cb)
feat(group_theory/schreier): prove Schreier's lemma ([#13019](https://github.com/leanprover-community/mathlib/pull/13019))
This PR adds a proof of Schreier's lemma.

### [2022-04-07 07:05:37](https://github.com/leanprover-community/mathlib/commit/45e4e62)
feat(archive/100-theorems-list/37_solution_of_cubic): golf ([#13012](https://github.com/leanprover-community/mathlib/pull/13012))
Express one of the lemmas for the solution of the cubic as a giant `linear_combination` calculation.

### [2022-04-07 06:05:46](https://github.com/leanprover-community/mathlib/commit/f0ee4c8)
feat(topology/metric_space): the product of bounded sets is bounded ([#13176](https://github.com/leanprover-community/mathlib/pull/13176))
Also add an `iff` version.

### [2022-04-07 00:57:22](https://github.com/leanprover-community/mathlib/commit/05820c5)
feat(archive/imo/imo2008_q4): golf using `linear_combination` ([#13209](https://github.com/leanprover-community/mathlib/pull/13209))

### [2022-04-07 00:24:49](https://github.com/leanprover-community/mathlib/commit/c4ced3a)
feat(archive/imo/imo2005_q6): golf using `field_simp` ([#13206](https://github.com/leanprover-community/mathlib/pull/13206))

### [2022-04-06 23:45:15](https://github.com/leanprover-community/mathlib/commit/cc28054)
feat(archive/imo/imo2001_q6): golf using `linear_combination` ([#13205](https://github.com/leanprover-community/mathlib/pull/13205))

### [2022-04-06 15:26:14](https://github.com/leanprover-community/mathlib/commit/06bdd8b)
feat(geometry/manifold/tangent_bundle): adapt the definition to the new vector bundle definition ([#13199](https://github.com/leanprover-community/mathlib/pull/13199))
Also a few tweaks to simplify the defeq behavior of tangent spaces.

### [2022-04-06 12:59:06](https://github.com/leanprover-community/mathlib/commit/138448a)
feat(algebra/parity): introduce `is_square` and, via `to_additive`, also `even` ([#13037](https://github.com/leanprover-community/mathlib/pull/13037))
This PR continues the refactor began in [#12882](https://github.com/leanprover-community/mathlib/pull/12882).  Now that most of the the even/odd lemmas are in the same file, I changed the definition of `even` to become the `to_additive` version of `is_square`.
The reason for the large number of files touched is that the definition of `even` actually changed, from being of the form `2 * n` to being of the form `n + n`.  Thus, I inserted appropriate `two_mul`s and `even_iff_two_dvd`s in a few places where the defeq to the divisibility by 2 was exploited.
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/even.2Fodd)

### [2022-04-06 06:48:08](https://github.com/leanprover-community/mathlib/commit/6930ad5)
feat(topology/continuous_function/zero_at_infty): add the type of continuous functions vanishing at infinity ([#12907](https://github.com/leanprover-community/mathlib/pull/12907))
This adds the type of of continuous functions vanishing at infinity (`zero_at_infty`) with the localized notation `C₀(α, β)` (we also allow `α →C₀ β` but the former has higher priority). This type is defined when `α` and `β` are topological spaces and `β` has a zero element. Elements of this type are continuous functions `f` with the additional property that `tendsto f (cocompact α) (𝓝 0)`. Here we attempt to follow closely the recent hom refactor and so we also create the type class `zero_at_infty_continuous_map_class`.
Various algebraic structures are instantiated on `C₀(α, β)` when corresponding structures exist on `β`. When `β` is a metric space, there is a natural inclusion `zero_at_infty_continuous_map.to_bcf : C₀(α, β) → α →ᵇ β`, which induces a metric space structure on `C₀(α, β)`, and the range of this map is closed. Therefore, when `β` is complete, `α →ᵇ β` is complete, and hence so is `C₀(α, β)`.
- [x] depends on: [#12894](https://github.com/leanprover-community/mathlib/pull/12894)

### [2022-04-06 03:42:41](https://github.com/leanprover-community/mathlib/commit/2841aad)
chore(scripts): update nolints.txt ([#13193](https://github.com/leanprover-community/mathlib/pull/13193))
I am happy to remove some nolints for you!

### [2022-04-06 01:48:21](https://github.com/leanprover-community/mathlib/commit/2e8d269)
feat(data/nat/factorization): Generalize natural factorization recursors. ([#12973](https://github.com/leanprover-community/mathlib/pull/12973))
Switches `rec_on_prime_pow` precondition to allow use of `0 < n`, and strengthens correspondingly `rec_on_pos_prime_pos_coprime` and `rec_on_prime_coprime`.

### [2022-04-05 23:46:08](https://github.com/leanprover-community/mathlib/commit/2504a2b)
chore(data/list/basic): remove axiom of choice assumption in some lemmas ([#13189](https://github.com/leanprover-community/mathlib/pull/13189))

### [2022-04-05 21:26:16](https://github.com/leanprover-community/mathlib/commit/a841361)
refactor(topology/vector_bundle): redefine ([#13175](https://github.com/leanprover-community/mathlib/pull/13175))
The definition of topological vector bundle in [#4658](https://github.com/leanprover-community/mathlib/pull/4658) was (inadvertently) a nonstandard definition, which agreed in finite dimension with the usual definition but not in infinite dimension.
Specifically, it omitted the compatibility condition that for a vector bundle over `B` with model fibre `F`, the transition function `B → F ≃L[R] F` associated to any pair of trivializations be continuous, with respect to to the norm topology on `F →L[R] F`.  (The transition function is automatically continuous with respect to the topology of pointwise convergence, which is why this works in finite dimension.  The discrepancy between these conditions in infinite dimension turns out to be a [classic](https://mathoverflow.net/questions/4943/vector-bundle-with-non-smoothly-varying-transition-functions/4997[#4997](https://github.com/leanprover-community/mathlib/pull/4997))
[gotcha](https://mathoverflow.net/questions/54550/the-third-axiom-in-the-definition-of-infinite-dimensional-vector-bundles-why/54706[#54706](https://github.com/leanprover-community/mathlib/pull/54706)).)
We refactor to add this compatibility condition to the definition of topological vector bundle, and to verify this condition in the existing examples of topological vector bundles (construction via a cocycle, direct sum of vector bundles, tangent bundle).

### [2022-04-05 19:36:21](https://github.com/leanprover-community/mathlib/commit/7ec52a1)
chore(algebraic_topology/simplex_category): removed ulift ([#13183](https://github.com/leanprover-community/mathlib/pull/13183))

### [2022-04-05 19:36:20](https://github.com/leanprover-community/mathlib/commit/960abb5)
chore(algebra/monoid_algebra/grading): fix slow elaboration ([#13169](https://github.com/leanprover-community/mathlib/pull/13169))
There were a couple of lemmas in this file taking multiple seconds to elaborate.  Apart from `squeeze_dsimps`, the main change in this PR is to help the elaborator unfold certain definitions (that it originally did unfold, but only after multiple seconds of trying to unfold other things), by replacing proofs with `by simpa only [some_unfolding_lemma] using the_original_proof`.
The main alternative I discovered for the `simpa` changes was to strategically mark certain definitions irreducible. Those definitions needed to be unfolded in other places in this file, and it's less obviously connected to the source of the slowness: we might keep around the `local attribute [irreducible]` lines even if it's not needed after a refactor.
Zulip thread: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Slow.20defeqs.20in.20.60algebra.2Fmonoid_algebra.2Fgrading.2Elean.60

### [2022-04-05 19:36:19](https://github.com/leanprover-community/mathlib/commit/d34cbcf)
refactor(algebra/homology, category_theory/*): declassify exactness ([#13153](https://github.com/leanprover-community/mathlib/pull/13153))
Having  `exact` be a class was very often somewhat inconvenient, so many lemmas took it as a normal argument while many others had it as a typeclass argument. This PR removes this inconsistency by downgrading `exact` to a structure. We lose very little by doing this, and using typeclass inference as a Prolog-like "automatic theorem prover" is rarely a good idea anyway.

### [2022-04-05 19:36:18](https://github.com/leanprover-community/mathlib/commit/427aae3)
chore(algebra/*): generalisation linter (replacing ring with non_assoc_ring) ([#13106](https://github.com/leanprover-community/mathlib/pull/13106))

### [2022-04-05 19:00:50](https://github.com/leanprover-community/mathlib/commit/e510b20)
feat(group_theory/index): Index of intersection ([#13186](https://github.com/leanprover-community/mathlib/pull/13186))
This PR adds `relindex_inf_le` and `index_inf_le`, which are companion lemmas to `relindex_inf_ne_zero` and `index_inf_ne_zero`.

### [2022-04-05 16:22:19](https://github.com/leanprover-community/mathlib/commit/cf131e1)
feat(data/complex/exponential): add `real.cos_abs` ([#13177](https://github.com/leanprover-community/mathlib/pull/13177))

### [2022-04-05 16:22:18](https://github.com/leanprover-community/mathlib/commit/b011b0e)
feat(ring_theory/unique_factorization_domain): The only divisors of prime powers are prime powers. ([#12799](https://github.com/leanprover-community/mathlib/pull/12799))
The only divisors of prime powers are prime powers in the associates monoid of an UFD.

### [2022-04-05 14:51:10](https://github.com/leanprover-community/mathlib/commit/fd1861c)
fix(tactic/ring): `ring_nf` should descend into subexpressions ([#12430](https://github.com/leanprover-community/mathlib/pull/12430))
Since the lambda passed to `ext_simp_core` was returning `ff`, this means the simplifier didn't descend into subexpressions, so `ring_nf` only tried to use the Horner normal form if the head symbol of the goal/hypothesis was `+`, `*`, `-` or `^`. In particular, since there are no such operations on `Sort`, `ring_nf` was exactly equivalent to `simp only [horner.equations._eqn_1, add_zero, one_mul, pow_one, neg_mul, add_neg_eq_sub]`. Toggling the return value means `ring_nf` will try to simplify all subexpressions, including the left hand side and right hand side of an equality.
@alexjbest discovered the MWE included in `test/ring.lean` while trying to use `ring_nf` to simplify a complicated expression.

### [2022-04-05 12:54:02](https://github.com/leanprover-community/mathlib/commit/91dd3b1)
chore(ring_theory/integral_domain): dedup, tidy ([#13180](https://github.com/leanprover-community/mathlib/pull/13180))

### [2022-04-05 12:54:00](https://github.com/leanprover-community/mathlib/commit/da132ec)
feat(*): define subobject classes from submonoid up to subfield ([#11750](https://github.com/leanprover-community/mathlib/pull/11750))
The next part of my big refactoring plans: subobject classes in the same style as morphism classes.
This PR introduces the following subclasses of `set_like`:
 * `one_mem_class`, `zero_mem_class`, `mul_mem_class`, `add_mem_class`, `inv_mem_class`, `neg_mem_class`
 * `submonoid_class`, `add_submonoid_class`
 * `subgroup_class`, `add_subgroup_class`
 * `subsemiring_class`, `subring_class`, `subfield_class`
The main purpose of this refactor is that we can replace the wide variety of lemmas like `{add_submonoid,add_subgroup,subring,subfield,submodule,subwhatever}.{prod,sum}_mem` with a single `prod_mem` lemma that is generic over all types `B` that extend `submonoid`:
```lean
@[to_additive]
lemma prod_mem {M : Type*} [comm_monoid M] [set_like B M] [submonoid_class B M]
  {ι : Type*} {t : finset ι} {f : ι → M} (h : ∀c ∈ t, f c ∈ S) : ∏ c in t, f c ∈ S
```
## API changes
 * When you extend a `struct subobject`, make sure to create a corresponding `subobject_class` instance.
## Upcoming PRs
This PR splits out the first part of [#11545](https://github.com/leanprover-community/mathlib/pull/11545), namely defining the subobject classes. I am planning these follow-up PRs for further parts of [#11545](https://github.com/leanprover-community/mathlib/pull/11545):
 - [ ] make the subobject consistently implicit in `{add,mul}_mem` [#11758](https://github.com/leanprover-community/mathlib/pull/11758)
 - [ ] remove duplicate instances like `subgroup.to_group` (replaced by the `subgroup_class.to_subgroup` instances that are added by this PR) [#11759](https://github.com/leanprover-community/mathlib/pull/11759)
 - [ ] further deduplication such as `finsupp_sum_mem`
## Subclassing `set_like`
Contrary to mathlib's typical subclass pattern, we don't extend `set_like`, but take a `set_like` instance parameter:
```lean
class one_mem_class (S : Type*) (M : out_param $ Type*) [has_one M] [set_like S M] :=
(one_mem : ∀ (s : S), (1 : M) ∈ s)
```
instead of:
```lean
class one_mem_class (S : Type*) (M : out_param $ Type*) [has_one M]
  extends set_like S M :=
(one_mem : ∀ (s : S), (1 : M) ∈ s)
```
The main reason is that this avoids some big defeq checks when typechecking e.g. `x * y : s`, where `s : S` and `[comm_group G] [subgroup_class S G]`. Namely, the type `coe_sort s` could be given by `subgroup_class → @@submonoid_class _ _ (comm_group.to_group.to_monoid) → set_like → has_coe_to_sort` or by `subgroup_class → @@submonoid_class _ _ (comm_group.to_comm_monoid.to_monoid) → set_like → has_coe_to_sort`. When checking that `has_mul` on the first type is the same as `has_mul` on the second type, those two inheritance paths are unified many times over ([sometimes exponentially many](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Why.20is.20.60int.2Ecast_abs.60.20so.20slow.3F/near/266945077)). So it's important to keep the size of types small, and therefore we avoid `extends`-based inheritance.
## Defeq fixes
Adding instances like `subgroup_class.to_group` means that there are now two (defeq) group instances for `subgroup`. This makes some code more fragile, until we can replace `subgroup.to_group` with its more generic form in a follow-up PR. Especially when taking subgroups of subgroups I needed to help the elaborator in a few places. These should be minimally invasive for other uses of the code.
## Timeout fixes
Some of the leaf files started timing out, so I made a couple of fixes. Generally these can be classed as:
 * `squeeze_simps`
 * Give inheritance `subX_class S M` → `X s` (where `s : S`) a lower prority than `Y s` → `X s` so that `subY_class S M` → `Y s` → `X s` is preferred over `subY_class S M` → `subX_class S M` → `X s`. This addresses slow unifications when `x : s`, `s` is a submonoid of `t`, which is itself a subgroup of `G`: existing code expects to go `subgroup → group → monoid`, which got changed to `subgroup_class → submonoid_class → monoid`; when this kind of unification issue appears in your type this results in slow unification. By tweaking the priorities, we help the elaborator find our preferred instance, avoiding the big defeq checks. (The real fix should of course be to fix the unifier so it doesn't become exponential in these kinds of cases.)
 * Split a long proof with duplication into smaller parts. This was basically my last resort.
I decided to bump the limit for the `fails_quickly` linter for `measure_theory.Lp_meas.complete_space`, which apparently just barely goes over this limit now. The time difference was about 10%-20% for that specific instance.

### [2022-04-05 11:06:01](https://github.com/leanprover-community/mathlib/commit/220f71b)
refactor(data/polynomial/basic): overhaul all the misnamed `to_finsupp` lemmas ([#13139](https://github.com/leanprover-community/mathlib/pull/13139))
`zero_to_finsupp` was the statement `of_finsupp 0 = 0`, which doesn't match the name at all.
This change:
* Renames all those lemmas to `of_finsupp_<foo>`
* Changes the direction of `add_to_finsupp` to be `of_finsupp_add`, so the statement is now `of_finsupp (a + b) = _`
* Adds the missing `to_finsupp_<foo>` lemmas
* Uses the new lemmas to golf the semiring and ring instances
The renames include:
* `zero_to_finsupp` → `of_finsupp_zero`
* `one_to_finsupp` → `of_finsupp_one`
* `add_to_finsupp` → `of_finsupp_add` (direction reversed)
* `neg_to_finsupp` → `of_finsupp_neg` (direction reversed)
* `mul_to_finsupp` → `of_finsupp_mul` (direction reversed)
* `smul_to_finsupp` → `of_finsupp_smul` (direction reversed)
* `sum_to_finsupp` → `of_finsupp_sum` (direction reversed)
* `to_finsupp_iso_monomial` → `to_finsupp_monomial`
* `to_finsupp_iso_symm_single` → `of_finsupp_single`
* `eval₂_to_finsupp_eq_lift_nc` → `eval₂_of_finsupp`
The new lemmas include:
* `of_finsupp_sub`
* `of_finsupp_pow`
* `of_finsupp_erase`
* `of_finsupp_algebra_map`
* `of_finsupp_eq_zero`
* `of_finsupp_eq_one`
* `to_finsupp_zero`
* `to_finsupp_one`
* `to_finsupp_add`
* `to_finsupp_neg`
* `to_finsupp_sub`
* `to_finsupp_mul`
* `to_finsupp_pow`
* `to_finsupp_erase`
* `to_finsupp_algebra_map`
* `to_finsupp_eq_zero`
* `to_finsupp_eq_one`
* `to_finsupp_C`
Note that by marking things like `support` and `coeff` as `@[simp]`, they behave as if they were `support_of_finsupp` or `coeff_of_finsupp` lemma. By making `coeff` pattern match fewer arguments, we encourage it to apply more keenly.
Neither lemma will fire unless our expression contains `polynomial.of_finsupp`.

### [2022-04-05 11:06:00](https://github.com/leanprover-community/mathlib/commit/c108ed4)
feat(topology/algebra): add several lemmas ([#13135](https://github.com/leanprover-community/mathlib/pull/13135))
* add `closure_smul`, `interior_smul`, and `closure_smul₀`;
* add `is_open.mul_closure` and `is_open.closure_mul`.

### [2022-04-05 11:05:59](https://github.com/leanprover-community/mathlib/commit/bb4099b)
feat(analysis/normed/normed_field): add abs_le_floor_nnreal_iff ([#13130](https://github.com/leanprover-community/mathlib/pull/13130))
From LTE.

### [2022-04-05 11:05:57](https://github.com/leanprover-community/mathlib/commit/c7626b7)
feat(analysis/calculus/fderiv_analytic): an analytic function is smooth ([#13127](https://github.com/leanprover-community/mathlib/pull/13127))
This basic fact was missing from the library, but all the nontrivial maths were already there, we are just adding the necessary glue.
Also, replace `ac_refl` by `ring` in several proofs (to go down from 30s to 4s in one proof, for instance). I wonder if we should ban `ac_refl` from mathlib currently.

### [2022-04-05 11:05:56](https://github.com/leanprover-community/mathlib/commit/cbbaef5)
chore(algebra/field_power): generalisation linter ([#13107](https://github.com/leanprover-community/mathlib/pull/13107))
@alexjbest, this one is slightly more interesting, as the generalisation linter detected that two lemmas were stated incorrectly!

### [2022-04-05 11:05:55](https://github.com/leanprover-community/mathlib/commit/225d1ce)
refactor(combinatorics/hall/finite): small simplifications and readability improvements ([#13091](https://github.com/leanprover-community/mathlib/pull/13091))

### [2022-04-05 09:11:51](https://github.com/leanprover-community/mathlib/commit/9ff42fd)
feat(topology/fiber_bundle): lemmas about `e.symm.trans e'` ([#13168](https://github.com/leanprover-community/mathlib/pull/13168))

### [2022-04-05 09:11:50](https://github.com/leanprover-community/mathlib/commit/01a424b)
feat(analysis): continuous_linear_map.prod_mapL ([#13165](https://github.com/leanprover-community/mathlib/pull/13165))
From the sphere eversion project,
Co-authored by Heather Macbeth <25316162+hrmacbeth@users.noreply.github.com>

### [2022-04-05 09:11:49](https://github.com/leanprover-community/mathlib/commit/0e26022)
feat(group_theory/complement): Existence of transversals ([#13016](https://github.com/leanprover-community/mathlib/pull/13016))
This PR constructs transversals containing a specified element. This will be useful for Schreier's lemma (which requires a transversal containing the identity element).

### [2022-04-05 09:11:48](https://github.com/leanprover-community/mathlib/commit/63feb1b)
feat(group_theory/index): Add `relindex_le_of_le_left` and `relindex_le_of_le_right` ([#13015](https://github.com/leanprover-community/mathlib/pull/13015))
This PR adds `relindex_le_of_le_left` and `relindex_le_of_le_right`, which are companion lemmas to `relindex_eq_zero_of_le_left` and `relindex_eq_zero_of_le_right`.

### [2022-04-05 09:11:47](https://github.com/leanprover-community/mathlib/commit/ea1917b)
feat(algebra/group/to_additive + algebra/regular/basic): add to_additive for `is_regular` ([#12930](https://github.com/leanprover-community/mathlib/pull/12930))
This PR add the `to_additive` attribute to most lemmas in the file `algebra.regular.basic`.
I also added `to_additive` support for this: `to_additive` converts
*  `is_regular` to `is_add_regular`;
*  `is_left_regular` to `is_add_left_regular`;
*  `is_right_regular` to `is_add_right_regular`.
~~Currently, `to_additive` converts `regular` to `add_regular`.  This means that, for instance, `is_left_regular` becomes `is_left_add_regular`.~~
~~I have a slight preference for `is_add_left_regular/is_add_right_regular`, but I am not able to achieve this automatically.~~
~~EDIT: actually, the command~~
```
git ls-files | xargs grep -A1 "to\_additive" | grep -B1 regular
```
~~reveals more name changed by `to_additive` that require more thought.~~

### [2022-04-05 08:08:57](https://github.com/leanprover-community/mathlib/commit/21c48e1)
doc(topology/algebra/*): explanation of relation between `uniform_group` and `topological_group` ([#13151](https://github.com/leanprover-community/mathlib/pull/13151))
Adding some comments on how to use `uniform_group` and `topological_group`.

### [2022-04-05 05:20:37](https://github.com/leanprover-community/mathlib/commit/429c6e3)
chore(topology/algebra/infinite_sum): weaken from equiv to surjective ([#13164](https://github.com/leanprover-community/mathlib/pull/13164))

### [2022-04-05 05:20:36](https://github.com/leanprover-community/mathlib/commit/4c83474)
chore(model_theory/basic): Fix namespace on notation for first-order maps ([#13145](https://github.com/leanprover-community/mathlib/pull/13145))
Removes projection notation from the definition of notation for first-order maps

### [2022-04-05 03:53:18](https://github.com/leanprover-community/mathlib/commit/41cd2f8)
chore(data/fin/tuple/basic): lemmas about `cons` ([#13027](https://github.com/leanprover-community/mathlib/pull/13027))

### [2022-04-04 23:36:07](https://github.com/leanprover-community/mathlib/commit/4eee8bc)
chore(order/complete_lattice): Generalize `⨆`/`⨅` lemmas to dependent families ([#13154](https://github.com/leanprover-community/mathlib/pull/13154))
The "bounded supremum" and "bounded infimum" are both instances of nested `⨆`/`⨅`. But they only apply when the inner one runs over a predicate `p : ι → Prop`, and the function couldn't depend on `p`. This generalizes to `κ : ι → Sort*` and allows dependence on `κ i`.
The lemmas are renamed from `bsupr`/`binfi` to `supr₂`/`infi₂` to show that they are more general.
Some lemmas were missing between `⨆` and `⨅` or between `⨆`/`⨅` and nested `⨆`/`⨅`, so I'm adding them as well.
Renames

### [2022-04-04 20:06:50](https://github.com/leanprover-community/mathlib/commit/bae79d0)
chore(number_theory/cyclotomic/discriminant): golf `repr_pow_is_integral` a little ([#13167](https://github.com/leanprover-community/mathlib/pull/13167))
Using nice mathlib tactics instead of doing boilerplate tasks by hand to reduce the verbosity.

### [2022-04-04 20:06:48](https://github.com/leanprover-community/mathlib/commit/a925d1d)
chore(topology/algebra/module/basic): add continuous_linear_map.copy ([#13166](https://github.com/leanprover-community/mathlib/pull/13166))
As suggested by the fun_like docs

### [2022-04-04 18:23:21](https://github.com/leanprover-community/mathlib/commit/05e2fc0)
chore(order/*): generalisation linter ([#13105](https://github.com/leanprover-community/mathlib/pull/13105))

### [2022-04-04 16:21:07](https://github.com/leanprover-community/mathlib/commit/fe21f5d)
feat(group_theory/torsion): define torsion subgroups and show they're torsion ([#12769](https://github.com/leanprover-community/mathlib/pull/12769))
Also tidy up some linter errors and docstring for the module.

### [2022-04-04 16:21:06](https://github.com/leanprover-community/mathlib/commit/2108284)
refactor(order/succ_order/basic): Use `is_min`/`is_max` ([#12597](https://github.com/leanprover-community/mathlib/pull/12597))
Reformulate the `succ a ≤ a` and `a ≤ pred a` conditions to use `is_max` and `is_min`. This simplifies the proofs.
Change namespaces from `succ_order` and `pred_order` to `order`.
Lemma renames

### [2022-04-04 14:28:18](https://github.com/leanprover-community/mathlib/commit/f55d352)
feat(order/filter/n_ary): Binary and ternary maps of filters ([#13062](https://github.com/leanprover-community/mathlib/pull/13062))
Define `filter.map₂` and `filter.map₃`, the binary and ternary maps of filters.

### [2022-04-04 09:32:39](https://github.com/leanprover-community/mathlib/commit/b189be7)
feat(algebra/big_operators): add `commute.*_sum_{left,right}` lemmas ([#13035](https://github.com/leanprover-community/mathlib/pull/13035))
This moves the existing `prod_commute` lemmas into the `commute` namespace for discoverabiliy, and adds the swapped variants.
This also fixes an issue where lemmas about `add_commute` were misnamed using `commute`.

### [2022-04-04 08:56:24](https://github.com/leanprover-community/mathlib/commit/19448a9)
refactor(group_theory/schur_zassenhaus): Some golfing ([#13017](https://github.com/leanprover-community/mathlib/pull/13017))
This PR uses `mem_left_transversals.to_equiv` to golf the start of `schur_zassenhaus.lean`.

### [2022-04-04 08:23:22](https://github.com/leanprover-community/mathlib/commit/0cb9407)
chore(measure_theory/function/locally_integrable): fix typo ([#13160](https://github.com/leanprover-community/mathlib/pull/13160))

### [2022-04-04 06:48:14](https://github.com/leanprover-community/mathlib/commit/6dde651)
feat(algebra/quaternion): Cardinality of quaternion algebras ([#12891](https://github.com/leanprover-community/mathlib/pull/12891))

### [2022-04-04 06:15:27](https://github.com/leanprover-community/mathlib/commit/8cb151f)
feat(number_theory/cyclotomic/discriminant): add discr_zeta_eq_discr_zeta_sub_one ([#12710](https://github.com/leanprover-community/mathlib/pull/12710))
We add `discr_zeta_eq_discr_zeta_sub_one`: the discriminant of the power basis given by a primitive root of unity `ζ` is the same as the
discriminant of the power basis given by `ζ - 1`.
from flt-regular

### [2022-04-03 17:52:03](https://github.com/leanprover-community/mathlib/commit/61e18ae)
fix(data/polynomial/basic): op_ring_equiv docstring ([#13132](https://github.com/leanprover-community/mathlib/pull/13132))

### [2022-04-03 16:42:11](https://github.com/leanprover-community/mathlib/commit/36e1cdf)
feat(topology/uniform_space/basic): constructing a `uniform_space.core` from a filter basis for the uniformity ([#13065](https://github.com/leanprover-community/mathlib/pull/13065))

### [2022-04-03 11:32:25](https://github.com/leanprover-community/mathlib/commit/1212818)
feat(category_theory/abelian): transferring "abelian-ness" across a functor ([#13059](https://github.com/leanprover-community/mathlib/pull/13059))
If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.
See https://stacks.math.columbia.edu/tag/03A3

### [2022-04-03 09:48:57](https://github.com/leanprover-community/mathlib/commit/6e26cff)
feat(analysis/special_functions): add the Gamma function ([#12917](https://github.com/leanprover-community/mathlib/pull/12917))

### [2022-04-03 06:44:02](https://github.com/leanprover-community/mathlib/commit/6e5ca7d)
chore(*): Bump to Lean 3.42.1 ([#13146](https://github.com/leanprover-community/mathlib/pull/13146))

### [2022-04-03 06:44:01](https://github.com/leanprover-community/mathlib/commit/d6731a4)
docs(data/polynomial/basic): Remove commutative from doc-module ([#13144](https://github.com/leanprover-community/mathlib/pull/13144))

### [2022-04-03 04:50:50](https://github.com/leanprover-community/mathlib/commit/4f14d4d)
chore(topology/vector_bundle): split long proof ([#13142](https://github.com/leanprover-community/mathlib/pull/13142))
The construction of the direct sum of two vector bundles is on the verge of timing out, and an upcoming refactor will push it over the edge.  Split it pre-emptively.

### [2022-04-03 04:50:49](https://github.com/leanprover-community/mathlib/commit/410e3d0)
feat(logic/small, model_theory/*): Smallness of vectors, lists, terms, and substructures ([#13123](https://github.com/leanprover-community/mathlib/pull/13123))
Provides instances of `small` on vectors, lists, terms, and `substructure.closure`.

### [2022-04-03 04:50:48](https://github.com/leanprover-community/mathlib/commit/2d22b5d)
chore(algebra/*): generalisation linter ([#13109](https://github.com/leanprover-community/mathlib/pull/13109))

### [2022-04-03 04:50:47](https://github.com/leanprover-community/mathlib/commit/d33ea7b)
chore(ring_theory/polynomial/pochhammer): make semiring implicit in a lemma that I just moved ([#13077](https://github.com/leanprover-community/mathlib/pull/13077))
Moving lemma `pochhammer_succ_eval` to reduce typeclass assumptions ([#13024](https://github.com/leanprover-community/mathlib/pull/13024)), the `semiring` became accidentally explicit.  Since one of the explicit arguments of the lemma is a term in the semiring, I changed the `semiring` to being implicit.
The neighbouring lemmas do not involve terms in their respective semiring, which is why the semiring is explicit throughout the section.

### [2022-04-03 04:50:46](https://github.com/leanprover-community/mathlib/commit/955e95a)
feat(logic/function/basic): add some more API for `injective2` ([#13074](https://github.com/leanprover-community/mathlib/pull/13074))
Note that the new `.left` and `.right` lemmas are weaker than the original ones, but the original lemmas were pretty much useless anyway, as `hf.left h` was the same as `(hf h).left`.

### [2022-04-03 03:07:24](https://github.com/leanprover-community/mathlib/commit/ef7298d)
chore(data/nat/gcd): move nat.coprime.mul_add_mul_ne_mul ([#13022](https://github.com/leanprover-community/mathlib/pull/13022))
I'm not sure if it will be useful elsewhere, but this seems like a better place for it anyway.

### [2022-04-03 02:04:00](https://github.com/leanprover-community/mathlib/commit/e1eb0bd)
feat(algebra/algebra/unitization): add star structure for the unitization of a non-unital algebra ([#13120](https://github.com/leanprover-community/mathlib/pull/13120))
The unitization of an algebra has a natural star structure when the underlying scalar ring and non-unital algebra have suitably interacting star structures.

### [2022-04-03 00:36:47](https://github.com/leanprover-community/mathlib/commit/e41208d)
feat(category_theory/monoidal): define monoidal structures on cartesian products of monoidal categories, (lax) monoidal functors and monoidal natural transformations ([#13033](https://github.com/leanprover-community/mathlib/pull/13033))
This PR contains (fairly straightforward) definitions / proofs of the following facts:
- Cartesian product of monoidal categories is a monoidal category.
- Cartesian product of (lax) monoidal functors is a (lax) monoidal functor.
- Cartesian product of monoidal natural transformations is a monoidal natural transformation.
These are prerequisites to defining a monoidal category structure on the category of monoids in a braided monoidal category (with the approach that I've chosen).  In particular, the first bullet point above is a prerequisite to endowing the tensor product functor, viewed as a functor from `C × C` to `C`, where `C` is a braided monoidal category, with a strength that turns it into a monoidal functor (stacked  PR).
This fits as follows into the general strategy for defining a monoidal category structure on the category of monoids in a braided monoidal category `C`, at least conceptually:
first, define a monoidal category structure on the category of lax monoidal functors into `C`, and then transport this structure to the category `Mon_ C` of monoids along the equivalence between `Mon_ C` and the category `lax_monoid_functor (discrete punit) C`.  All, not necessarily lax monoidal functors into `C` form a monoidal category with "pointwise" tensor product.  The tensor product of two lax monoidal functors equals the composition of their cartesian product, which is lax monoidal, with the tensor product on`C`, which is monoidal if `C` is braided.  This gives a way to define a tensor product of two lax monoidal functors.  The details still need to be fleshed out.

### [2022-04-02 23:29:08](https://github.com/leanprover-community/mathlib/commit/bb5e598)
feat(set_theory/cardinal_ordinal): Add `simp` lemmas for `aleph` ([#13056](https://github.com/leanprover-community/mathlib/pull/13056))

### [2022-04-02 22:23:30](https://github.com/leanprover-community/mathlib/commit/d4b40c3)
feat(measure_theory/measure/haar_lebesgue): measure of an affine subspace is zero ([#13137](https://github.com/leanprover-community/mathlib/pull/13137))
* Additive Haar measure of an affine subspace of a finite dimensional
real vector space is zero.
* Additive Haar measure of the image of a set `s` under `homothety x r` is
  equal to `|r ^ d| * μ s`.

### [2022-04-02 22:23:29](https://github.com/leanprover-community/mathlib/commit/7617942)
feat(order/filter/basic): add `filter.eventually_{eq,le}.prod_map` ([#13103](https://github.com/leanprover-community/mathlib/pull/13103))

### [2022-04-02 19:43:29](https://github.com/leanprover-community/mathlib/commit/a29bd58)
feat(algebra/regular/basic): add lemma commute.is_regular_iff ([#13104](https://github.com/leanprover-community/mathlib/pull/13104))
This lemma shows that an element that commutes with every element is regular if and only if it is left regular.

### [2022-04-02 16:29:33](https://github.com/leanprover-community/mathlib/commit/8e476fa)
chore(topology/vector_bundle): use continuous-linear rather than linear in core construction ([#13053](https://github.com/leanprover-community/mathlib/pull/13053))
The `vector_bundle_core` construction builds a vector bundle from a cocycle, the data of which are an open cover and a choice of transition function between any two elements of the cover.  Currently, for base `B` and model fibre `F`, the transition function has type `ι → ι → B → (F →ₗ[R] F)`.
This PR changes it to type `ι → ι → B → (F →L[R] F)`.  This is no loss of generality since there already were other conditions which forced the transition function to be continuous-linear on each fibre.  Of course, it is a potential loss of convenience since the proof obligation for continuity now occurs upfront.
The change is needed because in the vector bundle refactor to come, the further condition will be imposed that each transition function `B → (F →L[R] F)` is continuous; stating this requires a topology on `F →L[R] F`.

### [2022-04-02 15:55:20](https://github.com/leanprover-community/mathlib/commit/cf6f27e)
refactor(topology/{fiber_bundle, vector_bundle}): make trivializations data rather than an existential ([#13052](https://github.com/leanprover-community/mathlib/pull/13052))
Previously, the construction `topological_vector_bundle` was a mixin requiring the _existence_ of a suitable trivialization at each point.
Change this to a class with data: a choice of trivialization at each point.  This has no effect on the mathematics, but it is necessary for the forthcoming refactor in which a further condition is imposed on the mutual compatibility of the trivializations.
Furthermore, attach to `topological_vector_bundle` and to two other constructions `topological_fiber_prebundle`, `topological_vector_prebundle` a further piece of data: an atlas of "good" trivializations.  This is not really mathematically necessary, since you could always take the atlas of "good" trivializations to be simply the set of canonical trivializations at each point in the manifold.  But sometimes one naturally has this larger "good" class and it's convenient to be able to access it.  The `charted_space` definition in the manifolds library does something similar.

### [2022-04-02 13:47:28](https://github.com/leanprover-community/mathlib/commit/3164b1a)
feat(probability/independence): two lemmas on indep_fun ([#13126](https://github.com/leanprover-community/mathlib/pull/13126))
These two lemmas show that `indep_fun` is preserved under composition by measurable maps and under a.e. equality.

### [2022-04-02 13:47:26](https://github.com/leanprover-community/mathlib/commit/1d5b99b)
feat(group_theory/free_product): add (m)range_eq_supr ([#12956](https://github.com/leanprover-community/mathlib/pull/12956))
and lemmas leading to it as inspired by the corresponding lemmas from
`free_groups.lean`.
As suggested by @ocfnash, polish the free group lemmas a bit as well.

### [2022-04-02 11:56:22](https://github.com/leanprover-community/mathlib/commit/7df5907)
chore(algebra/order/ring): generalisation linter ([#13096](https://github.com/leanprover-community/mathlib/pull/13096))

### [2022-04-02 01:59:06](https://github.com/leanprover-community/mathlib/commit/607f4f8)
feat(model_theory/semantics): A simp lemma for `Theory.model` ([#13117](https://github.com/leanprover-community/mathlib/pull/13117))
Defines `Theory.model_iff` to make it easier to show when a structure models a theory.

### [2022-04-01 22:20:38](https://github.com/leanprover-community/mathlib/commit/6dad5f8)
feat(topology/bornology/basic): alternate way of defining a bornology by its bounded set ([#13064](https://github.com/leanprover-community/mathlib/pull/13064))
More precisely, this defines an alternative to https://leanprover-community.github.io/mathlib_docs/topology/bornology/basic.html#bornology.of_bounded (which is renamed `bornology.of_bounded'`) which expresses the covering condition as containing the singletons, and factors the old version trough it to have a simpler proof.
Note : I chose to add a prime to the old constructor because it's now defined in terms of the new one, so defeq works better this way (i.e lemma about the new constructor can be used whenever the old one is used).

### [2022-04-01 22:20:36](https://github.com/leanprover-community/mathlib/commit/6cf5dc5)
feat(topology/support): add lemma `locally_finite.exists_finset_nhd_mul_support_subset` ([#13006](https://github.com/leanprover-community/mathlib/pull/13006))
When using a partition of unity to glue together a family of functions, this lemma allows
us to pass to a finite family in the neighbourhood of any point.
Formalized as part of the Sphere Eversion project.

### [2022-04-01 20:35:06](https://github.com/leanprover-community/mathlib/commit/912f195)
feat(dynamics/periodic_pts): Lemma about periodic point from periodic point of iterate ([#12940](https://github.com/leanprover-community/mathlib/pull/12940))

### [2022-04-01 19:21:53](https://github.com/leanprover-community/mathlib/commit/196a48c)
feat(set_theory/ordinal_arithmetic): Coefficients of Cantor Normal Form ([#12681](https://github.com/leanprover-community/mathlib/pull/12681))
We prove all coefficients of the base-b expansion of an ordinal are less than `b`. We also tweak the parameters of various other theorems.

### [2022-04-01 17:02:37](https://github.com/leanprover-community/mathlib/commit/a3c753c)
feat(topology/[subset_properties, separation]): bornologies for filter.co[closed_]compact ([#12927](https://github.com/leanprover-community/mathlib/pull/12927))

### [2022-04-01 16:30:59](https://github.com/leanprover-community/mathlib/commit/e8ef744)
docs(probability/martingale): missing word ([#13113](https://github.com/leanprover-community/mathlib/pull/13113))

### [2022-04-01 16:30:58](https://github.com/leanprover-community/mathlib/commit/b365371)
feat(model_theory/syntax,semantics): Sentences for binary relation properties ([#13087](https://github.com/leanprover-community/mathlib/pull/13087))
Defines sentences for basic properties of binary relations
Proves that realizing these sentences is equivalent to properties in the binary relation library

### [2022-04-01 12:39:38](https://github.com/leanprover-community/mathlib/commit/342a4b0)
feat(data/polynomial/coeff): add `char_zero` instance on polynomials ([#13075](https://github.com/leanprover-community/mathlib/pull/13075))
Besides adding the instance, I also added a warning on the difference between `char_zero R` and `char_p R 0` for general semirings.
An example showing the difference is in [#13080](https://github.com/leanprover-community/mathlib/pull/13080).
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F)

### [2022-04-01 12:39:37](https://github.com/leanprover-community/mathlib/commit/89275df)
feat(topology/algebra/uniform_group): add characterization of total boundedness ([#12808](https://github.com/leanprover-community/mathlib/pull/12808))
The main result is `totally_bounded_iff_subset_finite_Union_nhds_one`.
We prove it for noncommutative groups, which involves taking opposites.
Add `uniform_group` instance for the opposite group.
Adds several helper lemmas for
* (co-)map of opposites applied to neighborhood filter
* filter basis of uniformity in a uniform group in terms of neighborhood basis at identity
Simplified proofs for `totally_bounded_of_forall_symm` and `totally_bounded.closure`.

### [2022-04-01 10:46:51](https://github.com/leanprover-community/mathlib/commit/c61f7e8)
chore(model_theory/elementary_maps): Fix Tarski-Vaught Test ([#13102](https://github.com/leanprover-community/mathlib/pull/13102))
Fixes the assumption of the Tarski-Vaught test.

### [2022-04-01 10:46:50](https://github.com/leanprover-community/mathlib/commit/e6a0a26)
chore(algebra/order/*): generalisation linter ([#13098](https://github.com/leanprover-community/mathlib/pull/13098))

### [2022-04-01 10:46:48](https://github.com/leanprover-community/mathlib/commit/8a51798)
chore(order/*): generalisation linter ([#13097](https://github.com/leanprover-community/mathlib/pull/13097))

### [2022-04-01 10:46:47](https://github.com/leanprover-community/mathlib/commit/0e95cad)
chore(algebra/group_power/basic): generalisation linter ([#13095](https://github.com/leanprover-community/mathlib/pull/13095))

### [2022-04-01 10:46:46](https://github.com/leanprover-community/mathlib/commit/6652766)
chore(algebra/ring/basic): generalisation linter ([#13094](https://github.com/leanprover-community/mathlib/pull/13094))

### [2022-04-01 10:46:45](https://github.com/leanprover-community/mathlib/commit/e326fe6)
feat(model_theory/basic,language_map): More about `language.mk₂` ([#13090](https://github.com/leanprover-community/mathlib/pull/13090))
Provides instances on `language.mk₂`
Defines `first_order.language.Lhom.mk₂`, a constructor for maps from languages built with `language.mk₂`.

### [2022-04-01 08:58:07](https://github.com/leanprover-community/mathlib/commit/873f268)
chore(group_theory/group_action/*): generalisation linter ([#13100](https://github.com/leanprover-community/mathlib/pull/13100))

### [2022-04-01 07:06:11](https://github.com/leanprover-community/mathlib/commit/3a0c034)
chore(algebra/*): generalisation linter ([#13099](https://github.com/leanprover-community/mathlib/pull/13099))

### [2022-04-01 03:39:04](https://github.com/leanprover-community/mathlib/commit/9728396)
chore(scripts): update nolints.txt ([#13101](https://github.com/leanprover-community/mathlib/pull/13101))
I am happy to remove some nolints for you!