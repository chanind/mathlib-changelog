### [2021-09-30 22:39:03](https://github.com/leanprover-community/mathlib/commit/a24b496)
feat(analysis/normed_space/add_torsor_bases): add lemma `exists_subset_affine_independent_span_eq_top_of_open` ([#9418](https://github.com/leanprover-community/mathlib/pull/9418))
Also some supporting lemmas about affine span, affine independence.

### [2021-09-30 22:39:00](https://github.com/leanprover-community/mathlib/commit/931cd6d)
feat(data/set/equitable): Equitable functions ([#8509](https://github.com/leanprover-community/mathlib/pull/8509))
Equitable functions are functions whose maximum is at most one more than their minimum. Equivalently, in an additive successor order (`a < b ↔ a +1 ≤ b`), this means that the function takes only values `a` and `a + 1` for some `a`.
From Szemerédi's regularity lemma. Co-authored by @b-mehta

### [2021-09-30 20:25:20](https://github.com/leanprover-community/mathlib/commit/a52a54b)
chore(analysis/convex/basic): instance cleanup ([#9466](https://github.com/leanprover-community/mathlib/pull/9466))
Some lemmas were about `f : whatever → 𝕜`. They are now about `f : whatever → β` + a scalar instance between `𝕜` and `β`.
Some `add_comm_monoid` assumptions are actually promotable to `add_comm_group` directly thanks to [`module.add_comm_monoid_to_add_comm_group`](https://leanprover-community.github.io/mathlib_docs/algebra/module/basic.html#module.add_comm_monoid_to_add_comm_group). [Related Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Convexity.20refactor/near/255268131).

### [2021-09-30 20:25:18](https://github.com/leanprover-community/mathlib/commit/97036e7)
feat(measure_theory/constructions/pi): volume on `α × α` as a map of volume on `fin 2 → α` ([#9432](https://github.com/leanprover-community/mathlib/pull/9432))

### [2021-09-30 20:25:17](https://github.com/leanprover-community/mathlib/commit/64bcb38)
feat(order/succ_pred): define successor orders ([#9397](https://github.com/leanprover-community/mathlib/pull/9397))
A successor order is an order in which every (non maximal) element has a least greater element. A predecessor order is an order in which every (non minimal) element has a greatest smaller element. Typical examples are `ℕ`, `ℕ+`, `ℤ`, `fin n`, `ordinal`. Anytime you want to turn `a < b + 1` into `a ≤ b` or `a < b` into `a + 1 ≤ b`, you want a `succ_order`.

### [2021-09-30 20:25:16](https://github.com/leanprover-community/mathlib/commit/f7795d1)
feat(monoid_algebra/grading): `add_monoid_algebra`s permit an internal grading ([#8927](https://github.com/leanprover-community/mathlib/pull/8927))

### [2021-09-30 18:34:36](https://github.com/leanprover-community/mathlib/commit/b18eedb)
feat(linear_algebra/affine_space/combination): add lemma `finset.map_affine_combination` ([#9453](https://github.com/leanprover-community/mathlib/pull/9453))
The other included lemmas `affine_map.coe_sub`,  `affine_map.coe_neg` are unrelated but are included to reduce PR overhead.

### [2021-09-30 18:34:34](https://github.com/leanprover-community/mathlib/commit/6e6fe1f)
move(category_theory/category/default): rename to `category_theory.basic` ([#9412](https://github.com/leanprover-community/mathlib/pull/9412))

### [2021-09-30 18:34:33](https://github.com/leanprover-community/mathlib/commit/4091f72)
refactor(linear_algebra/free_module): split in two files ([#9407](https://github.com/leanprover-community/mathlib/pull/9407))
We split `linear_algebra/free_module` in `linear_algebra/free_module/basic` and `linear_algebra/free_module/finite`, so one can work with free modules without having to import all the theory of dimension.

### [2021-09-30 18:34:32](https://github.com/leanprover-community/mathlib/commit/6210d98)
feat(*): Clean up some misstated lemmas about analysis/manifolds ([#9395](https://github.com/leanprover-community/mathlib/pull/9395))
A few lemmas whose statement doesn't match the name / docstring about analytical things, all of these are duplicates of other lemmas, so look like copy paste errors.

### [2021-09-30 16:11:19](https://github.com/leanprover-community/mathlib/commit/118e809)
refactor(algebra/module/linear_map): Move elementwise structure from linear_algebra/basic ([#9331](https://github.com/leanprover-community/mathlib/pull/9331))
This helps reduce the size of linear_algebra/basic, and by virtue of being a smaller file makes it easier to spot typeclasses which can be relaxed.
As an example, `linear_map.endomorphism_ring` now requires only `semiring R` not `ring R`.
Having instances available as early as possible is generally good, as otherwise it is hard to even state things elsewhere.

### [2021-09-30 16:11:18](https://github.com/leanprover-community/mathlib/commit/0dca20a)
feat(data/(d)finsupp): update_eq_sub_add_single ([#9184](https://github.com/leanprover-community/mathlib/pull/9184))
Also with `erase_eq_sub_single`.

### [2021-09-30 16:11:16](https://github.com/leanprover-community/mathlib/commit/8ec7fcf)
feat(ring_theory/henselian): Henselian local rings ([#8986](https://github.com/leanprover-community/mathlib/pull/8986))

### [2021-09-30 13:44:22](https://github.com/leanprover-community/mathlib/commit/f184dd7)
feat(group_theory/perm/concrete_cycle): perm.to_list ([#9178](https://github.com/leanprover-community/mathlib/pull/9178))
The conceptual inverse to `list.form_perm`.

### [2021-09-30 13:44:21](https://github.com/leanprover-community/mathlib/commit/3daae2c)
refactor(algebra/abs): add has_abs class ([#9172](https://github.com/leanprover-community/mathlib/pull/9172))
The notion of an "absolute value" occurs both in algebra (e.g. lattice ordered groups) and analysis (e.g. GM and GL-spaces). I introduced a `has_abs` notation class in https://github.com/leanprover-community/mathlib/pull/8673 for lattice ordered groups, along with the notation `|.|` and was asked by @eric-wieser and @jcommelin to add it in a separate PR and retro fit `has_abs` and the notation to mathlib.
I tried to introduce both the `has_abs` class and the `|.|` notation in [#8891](https://github.com/leanprover-community/mathlib/pull/8891) . However, I'm finding such a large and wide-ranging PR unwieldy to work with, so I'm now opening this PR which just replaces the previous definitions of `abs : α → α` in the following locations:
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/algebra/ordered_group.lean#L984
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/topology/continuous_function/basic.lean#L113
Out of scope are the following `abs : α → β`:
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/data/complex/is_R_or_C.lean#L439
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/data/complex/basic.lean#L406
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/data/real/nnreal.lean#L762
https://github.com/leanprover-community/mathlib/blob/f36c98e877dd86af12606abbba5275513baa8a26/src/data/num/basic.lean#L315
Replacing the `abs` notation with `|.|` can be considered in a subsequent PR.

### [2021-09-30 11:12:34](https://github.com/leanprover-community/mathlib/commit/2fd713a)
chore(order/basic): rename monotonicity concepts ([#9383](https://github.com/leanprover-community/mathlib/pull/9383))
This:
* Renames various mono lemmas either to enable dot notation (in some cases for types that don't exist yet) or to reflect they indicate monotonicity within a particular domain.
* Renames `strict_mono.top_preimage_top'` to `strict_mono.maximal_preimage_top'`
* Sorts some imports
* Replaces some `rcases` with `obtain`

### [2021-09-30 11:12:33](https://github.com/leanprover-community/mathlib/commit/09506e6)
feat(ring_theory/finiteness): add finiteness of restrict_scalars ([#9363](https://github.com/leanprover-community/mathlib/pull/9363))
We add `module.finitte.of_restrict_scalars_finite` and related lemmas: if `A` is an `R`-algebra and `M` is an `A`-module that is finite as `R`-module, then it is finite as `A`-module (similarly for `finite_type`).

### [2021-09-30 11:12:32](https://github.com/leanprover-community/mathlib/commit/3b48f7a)
docs(category_theory): provide missing module docs ([#9352](https://github.com/leanprover-community/mathlib/pull/9352))

### [2021-09-30 08:02:28](https://github.com/leanprover-community/mathlib/commit/6d12b2e)
feat(group_theory/complement): Top is complement to every singleton subset ([#9460](https://github.com/leanprover-community/mathlib/pull/9460))
The top subset of G is complement to every singleton subset of G.

### [2021-09-30 08:02:27](https://github.com/leanprover-community/mathlib/commit/f31758a)
chore(linear_algebra/quadratic_form): add missing lemmas, lift instance, and tweak argument implicitness ([#9458](https://github.com/leanprover-community/mathlib/pull/9458))
This adds `{quadratic,bilin}_form.{ext_iff,congr_fun}`, and a `can_lift` instance to promote `bilin_form`s to `quadratic_form`s.
The `associated_*` lemmas should have `Q` and `S` explicit as they are not inferable from the arguments. In particular, with `S` implicit, rewriting any of them backwards introduces a lot of noisy subgoals.

### [2021-09-30 08:02:25](https://github.com/leanprover-community/mathlib/commit/f6d2434)
feat(set_theory/cardinal_ordinal): there is no injective function from ordinals to types in the same universe ([#9452](https://github.com/leanprover-community/mathlib/pull/9452))
Contributed by @rwbarton at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Transfinite.20recursion/near/253614140

### [2021-09-30 08:02:23](https://github.com/leanprover-community/mathlib/commit/089614b)
feat(algebra/star): If `R` is a `star_monoid`/`star_ring` then so is `Rᵒᵖ` ([#9446](https://github.com/leanprover-community/mathlib/pull/9446))
The definition is simply that `op (star r) = star (op r)`

### [2021-09-30 08:02:22](https://github.com/leanprover-community/mathlib/commit/d1f78e2)
feat(order/filter/{basic, cofinite}, topology/subset_properties): filter lemmas, prereqs for [#8611](https://github.com/leanprover-community/mathlib/pull/8611) ([#9419](https://github.com/leanprover-community/mathlib/pull/9419))

### [2021-09-30 08:02:21](https://github.com/leanprover-community/mathlib/commit/f76d019)
chore({field,ring}_theory): generalize `fraction_ring` and `is_separable` to rings ([#9415](https://github.com/leanprover-community/mathlib/pull/9415))
These used to be defined only for `integral_domain`s resp. `field`s, however the construction makes sense even for `comm_ring`s. So we can just do the generalization for free, and moreover it makes certain proof terms in their definition a lot smaller. Together with [#9414](https://github.com/leanprover-community/mathlib/pull/9414), this helps against [timeouts when combining `localization` and `polynomial`](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60variables.60.20doesn't.20time.20out.20but.20inline.20params.20do), although the full test case is still quite slow (going from >40sec to approx 11 sec).

### [2021-09-30 08:02:19](https://github.com/leanprover-community/mathlib/commit/92526c8)
chore(ring_theory/localization): speed up `localization` a bit ([#9414](https://github.com/leanprover-community/mathlib/pull/9414))
Now `nsmul` and `gsmul` are irreducible on `localization`. This helps against [timeouts when combining `localization` and `polynomial`](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60variables.60.20doesn't.20time.20out.20but.20inline.20params.20do), although the full test case is still quite slow (going from >40sec to approx 11 sec).

### [2021-09-30 06:24:50](https://github.com/leanprover-community/mathlib/commit/8b238eb)
refactor(data/mv_polynomial/equiv): simplify option_equiv_left ([#9427](https://github.com/leanprover-community/mathlib/pull/9427))

### [2021-09-30 05:32:29](https://github.com/leanprover-community/mathlib/commit/c7dd27d)
split(analysis/convex/jensen): split Jensen's inequalities off `analysis.convex.function` ([#9445](https://github.com/leanprover-community/mathlib/pull/9445))

### [2021-09-30 02:54:54](https://github.com/leanprover-community/mathlib/commit/d9ed073)
chore(scripts): update nolints.txt ([#9459](https://github.com/leanprover-community/mathlib/pull/9459))
I am happy to remove some nolints for you!

### [2021-09-30 02:06:41](https://github.com/leanprover-community/mathlib/commit/f254c2f)
refactor(analysis/normed_space/{dual, pi_Lp}): split out inner product space parts ([#9388](https://github.com/leanprover-community/mathlib/pull/9388))
This is just moving code, no math changes.
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/New.20folder.20analysis.2Finner_product_space

### [2021-09-29 21:38:23](https://github.com/leanprover-community/mathlib/commit/519ab35)
feat(topology/metric_space/basic): nonempty intersections of balls ([#9448](https://github.com/leanprover-community/mathlib/pull/9448))

### [2021-09-29 21:38:22](https://github.com/leanprover-community/mathlib/commit/acced82)
chore(*): linting ([#9343](https://github.com/leanprover-community/mathlib/pull/9343))

### [2021-09-29 20:27:33](https://github.com/leanprover-community/mathlib/commit/3681b5a)
split(analysis/convex/slope): split slope results off `analysis.convex.function` ([#9444](https://github.com/leanprover-community/mathlib/pull/9444))

### [2021-09-29 18:44:41](https://github.com/leanprover-community/mathlib/commit/eca3fd9)
feat(data/real/ennreal): composition of coercion of natural numbers in ennreal ([#9447](https://github.com/leanprover-community/mathlib/pull/9447))

### [2021-09-29 16:34:59](https://github.com/leanprover-community/mathlib/commit/88e613e)
feat(data/mv_polynomial/cardinal): cardinalities of polynomial rings ([#9384](https://github.com/leanprover-community/mathlib/pull/9384))

### [2021-09-29 16:34:57](https://github.com/leanprover-community/mathlib/commit/2cd1d04)
feat(group_theory/sylow): Sylow's theorems for infinite groups ([#9288](https://github.com/leanprover-community/mathlib/pull/9288))
This PR contains all three of Sylow's theorems for infinite groups, building off the work of @ChrisHughes24 in the `ch_sylow2` branch of mathlib.
Later, I'll PR some consequences (e.g., index of normalizer stuff, maybe a golf of the original sylow stuff using the new results, Frattini's argument, ...).

### [2021-09-29 14:22:40](https://github.com/leanprover-community/mathlib/commit/9535c08)
feat(linear_algebra/affine_space/combination, analysis/convex/combination): basic lemmas about affine combinations, center of mass, centroid ([#9103](https://github.com/leanprover-community/mathlib/pull/9103))

### [2021-09-29 13:14:50](https://github.com/leanprover-community/mathlib/commit/9e91b70)
feat(analysis/convex/function): define strictly convex/concave functions ([#9439](https://github.com/leanprover-community/mathlib/pull/9439))

### [2021-09-29 11:22:48](https://github.com/leanprover-community/mathlib/commit/6f609ba)
feat(data/mv_polynomial/basic): aeval_tower ([#9429](https://github.com/leanprover-community/mathlib/pull/9429))

### [2021-09-29 11:22:47](https://github.com/leanprover-community/mathlib/commit/43c1ab2)
fix(linear_algebra/basic): generalize `linear_map.add_comm_group` to semilinear maps ([#9402](https://github.com/leanprover-community/mathlib/pull/9402))
Also generalizes `coe_mk` and golfs some proofs.

### [2021-09-29 10:20:15](https://github.com/leanprover-community/mathlib/commit/d2463aa)
feat(ring_theory/algebraic): is_algebraic_of_larger_base_of_injective ([#9433](https://github.com/leanprover-community/mathlib/pull/9433))

### [2021-09-29 09:37:26](https://github.com/leanprover-community/mathlib/commit/e150668)
chore(topology/sheaves): fix timeout by splitting proof ([#9436](https://github.com/leanprover-community/mathlib/pull/9436))
In [#7033](https://github.com/leanprover-community/mathlib/pull/7033) we were getting a timeout in `app_surjective_of_stalk_functor_map_bijective`. Since the proof looks like it has two rather natural components, I split out the first half into its own lemma. This is a separate PR since I don't really understand the topology/sheaf library, so I might be doing something very weird.
Timings:
 * original (master): 4.42s
 * original (master + [#7033](https://github.com/leanprover-community/mathlib/pull/7033)): 5.93s
 * new (master + this PR): 4.24s + 316ms
 * new (master + [#7033](https://github.com/leanprover-community/mathlib/pull/7033) + this PR): 5.48s + 212ms

### [2021-09-29 09:37:24](https://github.com/leanprover-community/mathlib/commit/0de5432)
feat(data/W/cardinal): results about cardinality of W-types ([#9210](https://github.com/leanprover-community/mathlib/pull/9210))

### [2021-09-29 08:41:05](https://github.com/leanprover-community/mathlib/commit/c758cec)
chore(analysis/convex/function): change `add_comm_monoid` to `add_comm_group` when carrier type is module of scalars containing -1 ([#9442](https://github.com/leanprover-community/mathlib/pull/9442))
Related [Zulip conversation](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Convexity.20refactor/near/255268131)

### [2021-09-29 04:03:07](https://github.com/leanprover-community/mathlib/commit/d7abdff)
chore(analysis/normed_space/*): prereqs for [#8611](https://github.com/leanprover-community/mathlib/pull/8611) ([#9379](https://github.com/leanprover-community/mathlib/pull/9379))
The functions `abs` and `norm_sq` on `ℂ` are proper.
A matrix with entries in a {seminormed group, normed group, normed space} is itself a {seminormed group, normed group, normed space}.
An injective linear map with finite-dimensional domain is a closed embedding.

### [2021-09-29 04:03:06](https://github.com/leanprover-community/mathlib/commit/8bd75b2)
feat(measure_theory/measure/haar_lebesgue): properties of Haar measure on real vector spaces ([#9325](https://github.com/leanprover-community/mathlib/pull/9325))
We show that any additive Haar measure on a finite-dimensional real vector space is rescaled by a linear map through its determinant, and we compute the measure of balls and spheres.

### [2021-09-29 04:03:04](https://github.com/leanprover-community/mathlib/commit/861d3bc)
chore(order/preorder_hom): more homs, golf a few proofs ([#9256](https://github.com/leanprover-community/mathlib/pull/9256))
### New `preorder_hom`s
* `preorder_hom.curry`: an order isomorphism between `α × β →ₘ γ` and `α →ₘ β →ₘ γ`;
* `preorder_hom.compₘ`: a fully bundled version of `preorder_hom.comp`;
* `preorder_hom.prodₘ`: a fully bundled version of `preorder_hom.prod`;
* `preorder_hom.prod_iso`: Order isomorphism between the space of
  monotone maps to `β × γ` and the product of the spaces +of monotone
  maps to `β` and `γ`;
* `preorder_hom.pi`: construct a bundled monotone map `α →ₘ Π i, π i`
  from a family of monotone maps +`f i : α →ₘ π i`;
* `preorder_hom.pi_iso`: same thing, as an `order_iso`;
* `preorder_hom.dual`: interpret `f : α →ₘ β` as `order_dual α →ₘ order_dual β`;
* `preorder_hom.dual_iso`: same as an `order_iso` (with one more
  `order_dual` to get a monotone map, not an antitone map);
### Renamed/moved `preorder_hom`s
The following `preorder_hom`s were renamed and/or moved from
`order.omega_complete_partial_order` to `order.preorder_hom`.
* `preorder_hom.const` : moved, bundle as `β →ₘ α →ₘ β`;
* `preorder_hom.prod.diag` : `preorder_hom.diag`;
* `preorder_hom.prod.map` : `preorder_hom.prod_map`;
* `preorder_hom.prod.fst` : `preorder_hom.fst`;
* `preorder_hom.prod.snd` : `preorder_hom.snd`;
* `preorder_hom.prod.zip` : `preorder_hom.prod`;
* `pi.monotone_apply` : `pi.eval_preorder_hom`;
* `preorder_hom.monotone_apply` : `preorder_hom.apply`;
* `preorder_hom.to_fun_hom` : moved.
### Other changes
* add an instance `can_lift (α → β) (α →ₘ β)`;
- rename `omega_complete_partial_order.continuous.to_monotone` to
  `omega_complete_partial_order.continuous'.to_monotone` to enable dot
  notation, same with
  `omega_complete_partial_order.continuous.to_bundled`;
* use `order_dual` to get some proofs;
* golf some proofs;
* redefine `has_Inf.Inf` and `has_Sup.Sup` using `infi`/`supr`;
* generalize some `mono` lemmas;
* use notation `→ₘ`.

### [2021-09-29 03:09:45](https://github.com/leanprover-community/mathlib/commit/49805e6)
chore(scripts): update nolints.txt ([#9441](https://github.com/leanprover-community/mathlib/pull/9441))
I am happy to remove some nolints for you!

### [2021-09-28 23:13:37](https://github.com/leanprover-community/mathlib/commit/73afb6c)
chore(data/fintype/basic): add `fintype.card_set` ([#9434](https://github.com/leanprover-community/mathlib/pull/9434))

### [2021-09-28 20:09:13](https://github.com/leanprover-community/mathlib/commit/e2cb9e1)
feat(data/mv_polynomial/supported): subalgebra of polynomials supported by a set of variables ([#9183](https://github.com/leanprover-community/mathlib/pull/9183))

### [2021-09-28 16:57:32](https://github.com/leanprover-community/mathlib/commit/e18b9ca)
feat(set_theory/continuum): define `cardinal.continuum := 2 ^ ω` ([#9354](https://github.com/leanprover-community/mathlib/pull/9354))

### [2021-09-28 14:01:07](https://github.com/leanprover-community/mathlib/commit/15f15a6)
chore(order/*): replace `mono_incr` and `mono_decr` in lemma names wih `monotone` and `antitone` ([#9428](https://github.com/leanprover-community/mathlib/pull/9428))
This change was performed as a find-and-replace. No occurrences of `incr` or `decr` appear as tokens in lemma names after this change.

### [2021-09-28 14:01:05](https://github.com/leanprover-community/mathlib/commit/2d5fd65)
fix(algebra/opposites): add a missing `comm_semiring` instance ([#9425](https://github.com/leanprover-community/mathlib/pull/9425))

### [2021-09-28 14:01:04](https://github.com/leanprover-community/mathlib/commit/84bbb00)
feat(data/set/intervals): add `order_iso.image_Ixx` lemmas ([#9404](https://github.com/leanprover-community/mathlib/pull/9404))

### [2021-09-28 11:33:36](https://github.com/leanprover-community/mathlib/commit/4a02fd3)
refactor(algebra/order/ring,data/complex): redefine `ordered_comm_ring` and complex order ([#9420](https://github.com/leanprover-community/mathlib/pull/9420))
* `ordered_comm_ring` no longer extends `ordered_comm_semiring`.
  We add an instance `ordered_comm_ring.to_ordered_comm_semiring` instead.
* redefine complex order in terms of `re` and `im` instead of existence of a nonnegative real number.
* simplify `has_star.star` on `complex` to `conj`;
* rename `complex.complex_partial_order` etc to `complex.partial_order` etc, make them protected.

### [2021-09-28 11:33:35](https://github.com/leanprover-community/mathlib/commit/06610c7)
feat(data/list/basic): lemmas about tail ([#9259](https://github.com/leanprover-community/mathlib/pull/9259))

### [2021-09-28 11:33:33](https://github.com/leanprover-community/mathlib/commit/c0dbe14)
feat(linear_algebra/matrix/fpow): integer powers of matrices ([#8683](https://github.com/leanprover-community/mathlib/pull/8683))
Since we have an inverse defined for matrices via `nonsing_inv`, we provide a `div_inv_monoid` instance for matrices.
The instance provides the ability to refer to integer power of matrices via the auto-generated `gpow`.
This is done in a new file to allow selective use.
Many API lemmas are provided to facilitate usage of the new `gpow`, many copied in form/content from
`algebra/group_with_zero/power.lean`, which provides a similar API.

### [2021-09-28 07:29:17](https://github.com/leanprover-community/mathlib/commit/01adfd6)
chore(analysis/special_functions): add some `@[simp]` attrs ([#9423](https://github.com/leanprover-community/mathlib/pull/9423))
Add `@[simp]` attrs to `real.sin_add_pi` and similar lemmas.

### [2021-09-28 07:29:16](https://github.com/leanprover-community/mathlib/commit/6108616)
doc(*): remove docstrings from copyright headers ([#9411](https://github.com/leanprover-community/mathlib/pull/9411))
This moves/removes the docs from the copyright header that are enough to make for the missing module docstring/redundant with the module docstring.

### [2021-09-28 07:29:14](https://github.com/leanprover-community/mathlib/commit/36c09f7)
doc(order/*): use "monotone" / "antitone" in place of "monotonically increasing" / "monotonically decreasing" ([#9408](https://github.com/leanprover-community/mathlib/pull/9408))
This PR cleans up the references to monotone and antitone function in lemmas and docstrings.
It doesn't touch anything beyond the docstrings.

### [2021-09-28 07:29:13](https://github.com/leanprover-community/mathlib/commit/22f2409)
chore(measure_theory/integral/interval_integral): change of variables for normed-space target ([#9350](https://github.com/leanprover-community/mathlib/pull/9350))
Re-state change of variables for `interval_integral` for a function with target a real normed space `E`, rather than just `ℝ`.  The proofs are exactly the same.

### [2021-09-28 06:33:23](https://github.com/leanprover-community/mathlib/commit/1db626e)
feat(analysis/normed_space/is_bounded_bilinear_map): direct proof of continuity ([#9390](https://github.com/leanprover-community/mathlib/pull/9390))
Previously `is_bounded_bilinear_map.continuous`, the continuity of a bounded bilinear map, was deduced from its differentiability and lived in `analysis.calculus.fderiv`.  This PR gives a direct proof so it can live in `analysis.normed_space.bounded_linear_maps`.
Two consequences of this lemma are also moved earlier in the hierarchy:
- `continuous_linear_equiv.is_open`, the openness of the set of continuous linear equivalences in the space of continuous linear maps, moves from `analysis.calculus.fderiv` to `analysis.normed_space.bounded_linear_maps`
- `continuous_inner`, the continuity of the inner product, moves from `analysis.inner_product_space.calculus` to `analysis.inner_product_space.basic`.
Previously discussed at
https://github.com/leanprover-community/mathlib/pull/4407#pullrequestreview-506198222

### [2021-09-28 03:23:06](https://github.com/leanprover-community/mathlib/commit/4b5bf56)
feat(measure_theory/integral/interval_integral): one more FTC-2 ([#9409](https://github.com/leanprover-community/mathlib/pull/9409))

### [2021-09-28 01:02:53](https://github.com/leanprover-community/mathlib/commit/8c5d93b)
feat(analysis/special_functions/complex/log): `exp ⁻¹' s` is countable ([#9410](https://github.com/leanprover-community/mathlib/pull/9410))
Also prove that the preimage of a countable set under an injective map
is countable.

### [2021-09-28 01:02:52](https://github.com/leanprover-community/mathlib/commit/b21bc97)
feat(analysis/special_functions): limits of `arg` and `log` at a real negative ([#9406](https://github.com/leanprover-community/mathlib/pull/9406))
Also add a `can_lift ℂ ℝ` instance.

### [2021-09-27 22:35:23](https://github.com/leanprover-community/mathlib/commit/8279510)
feat(*): Clean up some misstated lemmas about algebra ([#9417](https://github.com/leanprover-community/mathlib/pull/9417))
Similar to [#9395](https://github.com/leanprover-community/mathlib/pull/9395) clean up a few lemmas whose statement doesn't match the name / docstring about algebraic things, all of these are duplicates of other lemmas, so look like copy paste errors.

### [2021-09-27 20:53:13](https://github.com/leanprover-community/mathlib/commit/0d37fd6)
feat(data/polynomial/algebra_map): aeval_tower ([#9250](https://github.com/leanprover-community/mathlib/pull/9250))

### [2021-09-27 17:49:20](https://github.com/leanprover-community/mathlib/commit/f181d81)
chore(analysis/special_functions/exp_log): add some missing dot notation lemmas ([#9405](https://github.com/leanprover-community/mathlib/pull/9405))

### [2021-09-27 17:49:19](https://github.com/leanprover-community/mathlib/commit/9175158)
refactor(analysis/convex/function): generalize lemmas about convexity/concavity of functions, prove concave Jensen ([#9356](https://github.com/leanprover-community/mathlib/pull/9356))
`convex_on` and `concave_on` are currently only defined for real vector spaces. This generalizes ℝ to an arbitrary `ordered_semiring`. As a result, we now have the concave Jensen inequality for free.

### [2021-09-27 13:07:20](https://github.com/leanprover-community/mathlib/commit/5dfb76f)
feat(analysis/calculus/fderiv): generalize `const_smul` lemmas ([#9399](https://github.com/leanprover-community/mathlib/pull/9399))

### [2021-09-27 13:07:18](https://github.com/leanprover-community/mathlib/commit/954896a)
feat(data/nat/choose/cast): Cast of binomial coefficients equals a Pochhammer polynomial ([#9394](https://github.com/leanprover-community/mathlib/pull/9394))
This adds some glue between `nat.factorial`/`nat.asc_factorial`/`nat.desc_factorial` and `pochhammer` to provide some API to calculate binomial coefficients in a semiring. For example, `n.choose 2` as a real is `n * (n - 1)/2`.
I also move files as such:
* create `data.nat.choose.cast`
* create `data.nat.factorial.cast`
* rename `data.nat.factorial` to `data.nat.factorial.basic`

### [2021-09-27 13:07:17](https://github.com/leanprover-community/mathlib/commit/9a30f8c)
refactor(data/fin): drop `fin.cast_add_right` ([#9371](https://github.com/leanprover-community/mathlib/pull/9371))
This was a duplicate of `fin.nat_add`. Also simplify some definitions of equivalences.

### [2021-09-27 10:29:19](https://github.com/leanprover-community/mathlib/commit/850784c)
chore(order/*): rename `strict_mono_{incr,decr}_on` to `strict_{mono,anti}_on` ([#9401](https://github.com/leanprover-community/mathlib/pull/9401))
This was done as a direct find and replace

### [2021-09-27 10:29:16](https://github.com/leanprover-community/mathlib/commit/1472799)
chore(order): globally replace "antimono" with "antitone" ([#9400](https://github.com/leanprover-community/mathlib/pull/9400))
This was done with the regex `(?<=\b|_)antimono(?=\b|_)`

### [2021-09-27 10:29:14](https://github.com/leanprover-community/mathlib/commit/d1c68ef)
docs(docker): adjust readme to reflect that the PR was merged ([#9303](https://github.com/leanprover-community/mathlib/pull/9303))

### [2021-09-27 09:34:51](https://github.com/leanprover-community/mathlib/commit/cafd6fb)
chore(measure_theory/decomposition/lebesgue): rename `radon_nikodym_deriv` to `rn_deriv` ([#9386](https://github.com/leanprover-community/mathlib/pull/9386))

### [2021-09-27 04:20:23](https://github.com/leanprover-community/mathlib/commit/a4b92a3)
refactor(analysis/special_functions/trigonometric): split file ([#9340](https://github.com/leanprover-community/mathlib/pull/9340))
Another mammoth file, cut into several pieces.

### [2021-09-26 22:22:00](https://github.com/leanprover-community/mathlib/commit/62abfe5)
refactor(measure_theory/measure/hausdorff): move `dimH` to a new file, redefine ([#9391](https://github.com/leanprover-community/mathlib/pull/9391))
* move definition of the Hausdorff dimension to a new file
  `topology.metric_space.hausdorff_dimension`;
* move `dimH` and related lemmas to the root namespace;
* rewrite the definition so that it no longer requires
  `[measurable_space X] [borel_space X]`; use `rw dimH_def` to get a
  version using `[measurable_space X]` from the environment;
* add `dimH_le`, `set.finite.dimH_zero` and `finset.dimH_zero`;
* make `dimH` irreducible.

### [2021-09-26 22:21:59](https://github.com/leanprover-community/mathlib/commit/432271f)
feat(algebra/pointwise): add smul_set_inter ([#9374](https://github.com/leanprover-community/mathlib/pull/9374))
From [#2819](https://github.com/leanprover-community/mathlib/pull/2819) .

### [2021-09-26 21:40:02](https://github.com/leanprover-community/mathlib/commit/996783c)
feat(topology/sheaves/stalks): Generalize from Type to algebraic categories ([#9357](https://github.com/leanprover-community/mathlib/pull/9357))
Previously, basic lemmas about stalks like `germ_exist` and `section_ext` were only available for `Type`-valued (pre)sheaves. This PR generalizes these to (pre)sheaves valued in any concrete category where the forgetful functor preserves filtered colimits, which includes most algebraic categories like `Group` and `CommRing`. For the statements about stalks maps, we additionally assume that the forgetful functor reflects isomorphisms and preserves limits.

### [2021-09-26 12:40:21](https://github.com/leanprover-community/mathlib/commit/865ad47)
feat(algebra/module/pointwise_pi): add a file with lemmas on smul_pi ([#9369](https://github.com/leanprover-community/mathlib/pull/9369))
Make a new file rather than add an import to either of `algebra.pointwise` or `algebra.module.pi`.
From [#2819](https://github.com/leanprover-community/mathlib/pull/2819)

### [2021-09-26 10:39:54](https://github.com/leanprover-community/mathlib/commit/b3ca07f)
docs(undergrad): Add trigonometric Weierstrass ([#9393](https://github.com/leanprover-community/mathlib/pull/9393))

### [2021-09-26 10:39:53](https://github.com/leanprover-community/mathlib/commit/4ae46db)
feat(field_theory/is_alg_closed): more isomorphisms of algebraic closures ([#9376](https://github.com/leanprover-community/mathlib/pull/9376))

### [2021-09-26 10:39:52](https://github.com/leanprover-community/mathlib/commit/453f218)
refactor(linear_algebra/charpoly): move linear_algebra/charpoly to linear_algebra/matrix/charpoly ([#9368](https://github.com/leanprover-community/mathlib/pull/9368))
We move `linear_algebra/charpoly`to `linear_algebra/matrix/charpoly`, since the results there are for matrices. We also rename some lemmas in `linear_algebra/matrix/charpoly/coeff` to have the namespace `matrix`.

### [2021-09-26 10:39:51](https://github.com/leanprover-community/mathlib/commit/a2517af)
refactor(data/fin,*): redefine `insert_nth`, add lemmas ([#9349](https://github.com/leanprover-community/mathlib/pull/9349))
### `data/fin`
* add `fin.succ_above_cast_lt`, `fin.succ_above_pred`,
  `fin.cast_lt_succ_above`, `fin.pred_succ_above`;
* add `fin.exists_succ_above_eq` and `fin.exists_succ_above_eq_iff`,
  use the latter to prove `fin.range_succ_above`;
* add `@[simp]` to `fin.succ_above_left_inj`;
* add `fin.cases_succ_above` induction principle, redefine
  `fin.insert_nth` to be `fin.cases_succ_above`;
* add lemmas about `fin.insert_nth` and some algebraic operations.
### `data/fintype/basic`
* add `finset.insert_compl_self`;
* add `fin.image_succ_above_univ`, `fin.image_succ_univ`,
  `fin.image_cast_succ` and use them to prove `fin.univ_succ`,
  `fin.univ_cast_succ`, and `fin.univ_succ_above` using `by simp`;
### `data/fintype/card`
* slightly golf the proof of `fin.prod_univ_succ_above`;
* use `@[to_additive]` to generate some proofs.
### `topology/*`
* prove continuity of `fin.insert_nth` in both arguments and add all
  the standard dot-notation `*.fin_insert_nth` lemmas (`*` is one of
  `filter.tendsto`, `continuous_at`, `continuous_within_at`,
  `continuous_on`, `continuous`).

### [2021-09-26 08:35:17](https://github.com/leanprover-community/mathlib/commit/83470af)
feat(algebra/order/ring): add odd_neg, odd_abs, generalize dvd/abs lemmas ([#9362](https://github.com/leanprover-community/mathlib/pull/9362))

### [2021-09-26 07:23:13](https://github.com/leanprover-community/mathlib/commit/def1c02)
refactor(analysis/convex/function): generalize definition of `convex_on`/`concave_on` to allow any (ordered) scalars ([#9389](https://github.com/leanprover-community/mathlib/pull/9389))
`convex_on` and `concave_on` are currently only defined for real vector spaces. This generalizes ℝ to an arbitrary `ordered_semiring` in the definition.

### [2021-09-26 02:41:05](https://github.com/leanprover-community/mathlib/commit/793a598)
chore(scripts): update nolints.txt ([#9392](https://github.com/leanprover-community/mathlib/pull/9392))
I am happy to remove some nolints for you!

### [2021-09-25 17:07:10](https://github.com/leanprover-community/mathlib/commit/9866526)
feat(data/multiset/basic): add lemma that `multiset.map f` preserves `count` under certain assumptions on `f` ([#9117](https://github.com/leanprover-community/mathlib/pull/9117))

### [2021-09-25 16:04:00](https://github.com/leanprover-community/mathlib/commit/168806c)
feat(measure_theory/integral/lebesgue): lintegral is strictly monotone under some conditions ([#9373](https://github.com/leanprover-community/mathlib/pull/9373))

### [2021-09-25 15:05:39](https://github.com/leanprover-community/mathlib/commit/eba2b2e)
feat(measure_theory/function/l1_space): add integrability lemma for `measure.with_density` ([#9367](https://github.com/leanprover-community/mathlib/pull/9367))

### [2021-09-25 09:01:16](https://github.com/leanprover-community/mathlib/commit/6ea8168)
refactor(topology/compact_open): use bundled continuous maps ([#9351](https://github.com/leanprover-community/mathlib/pull/9351))

### [2021-09-25 06:48:09](https://github.com/leanprover-community/mathlib/commit/51ad06e)
refactor(analysis/inner_product_space/*): split big file ([#9382](https://github.com/leanprover-community/mathlib/pull/9382))
This PR makes a new folder `analysis/inner_product_space/*` comprising several files splitting the old `analysis/normed_space/inner_product` (which had reached 2900 lines!).
https://leanprover.zulipchat.com/#narrow/stream/116395-maths

### [2021-09-25 06:48:08](https://github.com/leanprover-community/mathlib/commit/55d8cd0)
chore(scripts): update nolints.txt ([#9381](https://github.com/leanprover-community/mathlib/pull/9381))
I am happy to remove some nolints for you!

### [2021-09-25 06:48:07](https://github.com/leanprover-community/mathlib/commit/42d8243)
feat(data/polynomial/eval): map_equiv ([#9375](https://github.com/leanprover-community/mathlib/pull/9375))

### [2021-09-25 04:13:25](https://github.com/leanprover-community/mathlib/commit/59b9ebb)
feat(algebra/group/to_additive): customize the relevant argument ([#9138](https://github.com/leanprover-community/mathlib/pull/9138))
`@[to_additive]` now automatically checks for each declaration what the first argument is with a multiplicative structure on it. 
This is now the argument that is tested when executing later occurrences of `@[to_additive]` for a fixed type to decide whether this declaration should be translated or not.

### [2021-09-25 01:43:26](https://github.com/leanprover-community/mathlib/commit/64b794a)
chore(analysis/complex/basic): rename `complex/normed_space` ([#9366](https://github.com/leanprover-community/mathlib/pull/9366))
This matches `module.complex_to_real`

### [2021-09-24 21:40:17](https://github.com/leanprover-community/mathlib/commit/b0cd1f9)
chore(algebra/group): move is_unit.inv lemmas ([#9364](https://github.com/leanprover-community/mathlib/pull/9364))

### [2021-09-24 21:40:16](https://github.com/leanprover-community/mathlib/commit/c42aaa3)
chore(data/pi): add missing `pi.{inv,neg}_def` ([#9361](https://github.com/leanprover-community/mathlib/pull/9361))

### [2021-09-24 21:40:15](https://github.com/leanprover-community/mathlib/commit/8ff756c)
feat(group_theory/*/pointwise): Copy set lemmas about pointwise actions to subgroups and submonoids ([#9359](https://github.com/leanprover-community/mathlib/pull/9359))
This is pretty much just a copy-and-paste job. At least the proofs themselves don't need copying. The set lemmas being copied here are:
https://github.com/leanprover-community/mathlib/blob/a9cd8c259d59b0bdbe931a6f8e6084f800bd7162/src/algebra/pointwise.lean#L607-L680
I skipped the `preimage_smul` lemma for now because I couldn't think of a useful statement using `map`.

### [2021-09-24 19:49:10](https://github.com/leanprover-community/mathlib/commit/18f06ec)
chore(measure_theory/integral/interval_integral): generalize `integral_smul` ([#9355](https://github.com/leanprover-community/mathlib/pull/9355))
Make sure that it works for scalar multiplication by a complex number.

### [2021-09-24 19:49:09](https://github.com/leanprover-community/mathlib/commit/7cb7246)
chore(linear_algebra/basic): add `linear_map.neg_comp`, generalize `linear_map.{sub,smul}_comp` ([#9335](https://github.com/leanprover-community/mathlib/pull/9335))
`sub_comp` had unnecessary requirements that the codomain of the right map be an additive group, while `smul_comp` did not support compatible actions.
This also golfs the proofs of all the `comp_*` lemmas to eliminate `simp`.
`smul_comp` and `comp_smul` are also both promoted to instances.

### [2021-09-24 19:49:07](https://github.com/leanprover-community/mathlib/commit/c794c5c)
chore(linear_algebra/basic): split out quotients and isomorphism theorems ([#9332](https://github.com/leanprover-community/mathlib/pull/9332))
`linear_algebra.basic` had become a very large file; I think too unwieldy to even be able to edit.
Fortunately there are some natural splits on content. I moved everything about quotients out to `linear_algebra.quotient`. Happily many files in `linear_algebra/` don't even need this, so we also get some significant import reductions.
I've also moved Noether's three isomorphism theorems for submodules to their own file.

### [2021-09-24 19:49:06](https://github.com/leanprover-community/mathlib/commit/6f2d1ba)
feat(data/dfinsupp): add submodule.bsupr_eq_range_dfinsupp_lsum ([#9202](https://github.com/leanprover-community/mathlib/pull/9202))
Also a version for `add_submonoid`. Unfortunately the proofs are almost identical, but that's consistent with the surrounding bits of the file anyway.
The key result is a dfinsupp version of the lemma in [#8246](https://github.com/leanprover-community/mathlib/pull/8246),
```lean
x ∈ (⨆ i (H : p i), f i) ↔ ∃ v : ι →₀ M, (∀ i, v i ∈ f i) ∧ ∑ i in v.support, v i = x ∧ (∀ i, ¬ p i → v i = 0) :=
```
as
```lean
x ∈ (⨆ i (h : p i), S i) ↔ ∃ f : Π₀ i, S i, dfinsupp.lsum ℕ (λ i, (S i).subtype) (f.filter p) = x
```

### [2021-09-24 13:55:52](https://github.com/leanprover-community/mathlib/commit/981f8ba)
chore(*): remove some `assume`s ([#9365](https://github.com/leanprover-community/mathlib/pull/9365))

### [2021-09-24 12:53:07](https://github.com/leanprover-community/mathlib/commit/e14cf58)
feat(measure_theory/function/conditional_expectation): define the conditional expectation of a function, prove the equality of integrals ([#9114](https://github.com/leanprover-community/mathlib/pull/9114))
This PR puts together the generalized Bochner integral construction of [#8939](https://github.com/leanprover-community/mathlib/pull/8939) and the set function `condexp_ind` of [#8920](https://github.com/leanprover-community/mathlib/pull/8920) to define the conditional expectation of a function.
The equality of integrals that defines the conditional expectation is proven in `set_integral_condexp`.

### [2021-09-24 11:04:41](https://github.com/leanprover-community/mathlib/commit/0db6caf)
feat(linear_algebra/affine_space/affine_map): add missing simp lemma `affine_map.homothety_apply_same` ([#9360](https://github.com/leanprover-community/mathlib/pull/9360))

### [2021-09-24 11:04:40](https://github.com/leanprover-community/mathlib/commit/48883dc)
chore(algebra/basic): split out facts about lmul ([#9300](https://github.com/leanprover-community/mathlib/pull/9300))

### [2021-09-24 11:04:39](https://github.com/leanprover-community/mathlib/commit/854e5c6)
refactor(measure_theory/measure/regular): add `inner_regular`, `outer_regular`, generalize ([#9283](https://github.com/leanprover-community/mathlib/pull/9283))
### Regular measures
* add a non-class predicate `inner_regular` to prove some lemmas once, not twice;
* add TC `outer_regular`, drop primed lemmas;
* consistently use `≠ ∞`, `≠ 0` in the assumptions;
* drop some typeclass requirements.
### Other changes
* add a few lemmas about subtraction to `data.real.ennreal`;
* add `ennreal.add_lt_add_left`, `ennreal.add_lt_add_right`, and use them;

### [2021-09-24 11:04:38](https://github.com/leanprover-community/mathlib/commit/a512db1)
feat(linear_algebra/free_modules): add instances ([#9223](https://github.com/leanprover-community/mathlib/pull/9223))
We add the instances `module.finite` and `module.free` on `(M →+ N)`, for `M` and `N` finite and free abelian groups.
We already have the more general version over any ring, for `(M →ₗ[R] N)`. (They are mathematically more general, but not for Lean.)

### [2021-09-24 08:36:36](https://github.com/leanprover-community/mathlib/commit/6a9ba18)
feat(measure_theory): `ι → α ≃ᵐ α` if `[unique ι]` ([#9353](https://github.com/leanprover-community/mathlib/pull/9353))
* define versions of `equiv.fun_unique` for `order_iso` and
  `measurable_equiv`;
* use the latter to relate integrals over (sets in) `ι → α` and `α`,
  where `ι` is a type with an unique element.

### [2021-09-24 08:36:35](https://github.com/leanprover-community/mathlib/commit/9e59e29)
feat(category_theory/opposites): Add is_iso_op ([#9319](https://github.com/leanprover-community/mathlib/pull/9319))

### [2021-09-24 08:36:34](https://github.com/leanprover-community/mathlib/commit/9618d73)
feat(algebra,group_theory): smul_(g)pow ([#9311](https://github.com/leanprover-community/mathlib/pull/9311))
Rename `smul_pow` to `smul_pow'` to match `smul_mul'`. Instead provide the distributing lemma `smul_pow` where the power distributes onto the scalar as well. Provide the group action `smul_gpow` as well.

### [2021-09-24 06:10:23](https://github.com/leanprover-community/mathlib/commit/a9cd8c2)
feat(linear_algebra): redefine `linear_map` and `linear_equiv` to be semilinear ([#9272](https://github.com/leanprover-community/mathlib/pull/9272))
This PR redefines `linear_map` and `linear_equiv` to be semilinear maps/equivs.
A semilinear map `f` is a map from an `R`-module to an `S`-module with a ring homomorphism `σ` between `R` and `S`, such that `f (c • x) = (σ c) • (f x)`. If we plug in the identity into `σ`, we get regular linear maps, and if we plug in the complex conjugate, we get conjugate linear maps. There are also other examples (e.g. Frobenius-linear maps) where this is useful which are covered by this general formulation. This was discussed on Zulip [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Semilinear.20maps), and a few preliminaries for this have already been merged.
The main issue that we had to overcome involved composition of semilinear maps, and `symm` for linear equivalences: having things like `σ₂₃.comp σ₁₂` in the types of semilinear maps creates major problems. For example, we want the composition of two conjugate-linear maps to be a regular linear map, not a `conj.comp conj`-linear map. To solve this issue, following a discussion from back in January, we created two typeclasses to make Lean infer the right ring hom. The first one is `[ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]` which expresses the fact that `σ₂₃.comp σ₁₂ = σ₁₃`, and the second one is `[ring_hom_inv_pair σ₁₂ σ₂₁]` which states that `σ₁₂` and `σ₂₁` are inverses of each other. There is also `[ring_hom_surjective σ]`, which is a necessary assumption to generalize some basic lemmas (such as `submodule.map`). Note that we have introduced notation to ensure that regular linear maps can still be used as before, i.e. `M →ₗ[R] N` still works as before to mean a regular linear map.
The main changes are in `algebra/module/linear_map.lean`, `data/equiv/module.lean` and `linear_algebra/basic.lean` (and `algebra/ring/basic.lean` for the `ring_hom` typeclasses). The changes in other files fall into the following categories:
1. When defining a regular linear map directly using the structure (i.e. when specifying `to_fun`, `map_smul'` and so on), there is a `ring_hom.id` that shows up in `map_smul'`. This mostly involves dsimping it away.
2. Elaboration seems slightly more brittle, and it fails a little bit more often than before. For example, when `f` is a linear map and `g` is something that can be coerced to a linear map (say a linear equiv), one has to write `↑g` to make `f.comp ↑g` work, or sometimes even to add a type annotation. This also occurs when using `trans` twice (i.e. `e₁.trans (e₂.trans e₃)`). In those places, we use the notation defined in [#8857](https://github.com/leanprover-community/mathlib/pull/8857) `∘ₗ` and `≪≫ₗ`. 
3. It seems to exacerbate the bug discussed [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/odd.20repeated.20type.20class.20search) for reasons that we don't understand all that well right now. It manifests itself in very slow calls to the tactic `ext`, and the quick fix is to manually use the right ext lemma.
4. The PR triggered a few timeouts in proofs that were already close to the edge. Those were sped up.
5. A few random other issues that didn't arise often enough to see a pattern.

### [2021-09-24 04:51:04](https://github.com/leanprover-community/mathlib/commit/a7a9c91)
feat(ring_theory/localization): Localizing at units is isomorphic to the ring ([#9324](https://github.com/leanprover-community/mathlib/pull/9324))

### [2021-09-24 02:10:32](https://github.com/leanprover-community/mathlib/commit/4a8fb6a)
chore(linear_algebra): rename endomorphism multiplicative structures for consistency ([#9336](https://github.com/leanprover-community/mathlib/pull/9336))
This renames:
* `module.endomorphism_semiring` → `module.End.semiring`
* `module.endomorphism_ring` → `module.End.ring`
* `module.endomorphism_algebra` → `module.End.algebra`
* `linear_map.module.End.division_ring` → `module.End.division_ring`
This brings the name in line with the names for `add_monoid.End`.
Since `module.End` is an abbreviation, it does not matter that the instances now use this instead of `M →ₗ[R] M`.

### [2021-09-24 01:29:26](https://github.com/leanprover-community/mathlib/commit/dd519df)
chore(*): linting ([#9342](https://github.com/leanprover-community/mathlib/pull/9342))

### [2021-09-24 00:26:14](https://github.com/leanprover-community/mathlib/commit/1a341fd)
feat(algebra/*): Tensor product is the fibered coproduct in CommRing ([#9338](https://github.com/leanprover-community/mathlib/pull/9338))

### [2021-09-24 00:26:13](https://github.com/leanprover-community/mathlib/commit/2d17f52)
feat(measure_theory/integral/*): integral over map (e : α ≃ᵐ β) μ  ([#9316](https://github.com/leanprover-community/mathlib/pull/9316))

### [2021-09-24 00:26:12](https://github.com/leanprover-community/mathlib/commit/18f0093)
feat(measure_theory/measure/measure_space): add measure_Union_of_null_inter ([#9307](https://github.com/leanprover-community/mathlib/pull/9307))
From [#2819](https://github.com/leanprover-community/mathlib/pull/2819)

### [2021-09-24 00:26:11](https://github.com/leanprover-community/mathlib/commit/7e3256b)
feat(ring_theory/derivation): helper lemma for custom `derivation_ext` lemmas ([#9255](https://github.com/leanprover-community/mathlib/pull/9255))

### [2021-09-24 00:26:10](https://github.com/leanprover-community/mathlib/commit/9b1f0bb)
feat(topology/compact_open): convergence in the compact-open topology can be checked on compact sets ([#9240](https://github.com/leanprover-community/mathlib/pull/9240))

### [2021-09-23 22:18:50](https://github.com/leanprover-community/mathlib/commit/d2f7b24)
feat(algebra/pointwise): more to_additive attributes for new lemmas ([#9348](https://github.com/leanprover-community/mathlib/pull/9348))
Some of these lemmas introduced in [#9226](https://github.com/leanprover-community/mathlib/pull/9226) I believe.
Spun off from [#2819](https://github.com/leanprover-community/mathlib/pull/2819).

### [2021-09-23 22:18:49](https://github.com/leanprover-community/mathlib/commit/88c79e5)
feat(data/fintype/basic): embeddings of fintypes based on cardinal inequalities ([#9346](https://github.com/leanprover-community/mathlib/pull/9346))
From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/mapping.20a.20fintype.20into.20a.20finset/near/254493754, based on suggestions by @kmill  and @eric-wieser and @riccardobrasca.

### [2021-09-23 22:18:48](https://github.com/leanprover-community/mathlib/commit/c950c45)
feat(analysis/calculus/[f]deriv): derivative of pointwise composition/application of continuous linear maps ([#9174](https://github.com/leanprover-community/mathlib/pull/9174))
This introduces useful analogs to the product rule when working with derivatives in spaces of continuous linear maps.

### [2021-09-23 21:18:45](https://github.com/leanprover-community/mathlib/commit/54eb603)
chore(analysis/normed_space/conformal_linear_map): delay dependence on inner products ([#9293](https://github.com/leanprover-community/mathlib/pull/9293))

### [2021-09-23 19:20:02](https://github.com/leanprover-community/mathlib/commit/14bcb2e)
feat(measure_theory/measure/measure_space_def): some simple lemmas about measures and intersection ([#9306](https://github.com/leanprover-community/mathlib/pull/9306))
From [#2819](https://github.com/leanprover-community/mathlib/pull/2819)

### [2021-09-23 19:20:01](https://github.com/leanprover-community/mathlib/commit/ea59c90)
feat(ring_theory/algebraic): is_algebraic_iff_not_injective ([#9254](https://github.com/leanprover-community/mathlib/pull/9254))

### [2021-09-23 16:42:28](https://github.com/leanprover-community/mathlib/commit/9e367ff)
feat(linear_algebra/invariant_basis_number): strong_rank_condition_iff_succ ([#9128](https://github.com/leanprover-community/mathlib/pull/9128))
We add `strong_rank_condition_iff_succ`: a ring satisfies the strong rank condition if and only if, for all `n : ℕ`, there are no
injective linear maps `(fin (n + 1) → R) →ₗ[R] (fin n → R)`. This will be used to prove that any commutative ring satisfies the strong rank condition.
The proof is simple and it uses the natural inclusion `R^n → R^m`, for `n ≤ m` (adding zeros at the end). We provide this in general as `extend_by_zero.linear_map : (ι → R) →ₗ[R] (η → R)` where `ι` and `η` are types endowed with a function `ι → η`.

### [2021-09-23 15:31:34](https://github.com/leanprover-community/mathlib/commit/b365367)
feat(README.md): add Oliver Nash ([#9347](https://github.com/leanprover-community/mathlib/pull/9347))

### [2021-09-23 15:31:33](https://github.com/leanprover-community/mathlib/commit/81f6e88)
chore(analysis/calculus): add 2 simple lemmas ([#9334](https://github.com/leanprover-community/mathlib/pull/9334))
Add `differentiable_on.has_fderiv_at` and `differentiable_on.has_deriv_at`.

### [2021-09-23 15:31:31](https://github.com/leanprover-community/mathlib/commit/0243da3)
feat(ereal): added useful lemmas ([#9313](https://github.com/leanprover-community/mathlib/pull/9313))
Some small addition to the api for ereals.

### [2021-09-23 14:08:43](https://github.com/leanprover-community/mathlib/commit/cc0d839)
feat(measure_theory/measure/haar): cleanup, link with the is_haar_measure typeclass ([#9244](https://github.com/leanprover-community/mathlib/pull/9244))
We show that the Haar measure constructed in `measure_theory/measure/haar` satisfies the `is_haar_measure` typeclass, and use the existence to show a few further properties of all Haar measures. Also weaken a little bit some assumptions in this file.

### [2021-09-23 08:15:13](https://github.com/leanprover-community/mathlib/commit/602ad58)
feat(measure_theory/integral): add a few lemmas ([#9285](https://github.com/leanprover-community/mathlib/pull/9285))

### [2021-09-23 08:15:12](https://github.com/leanprover-community/mathlib/commit/145c5ca)
refactor(topology/category/Top/open_nhds): remove open_nhds.is_filtered ([#9211](https://github.com/leanprover-community/mathlib/pull/9211))
Remove instance that can be inferred automatically.

### [2021-09-23 06:57:23](https://github.com/leanprover-community/mathlib/commit/8a0d60e)
chore(topology): rename compact_ball to is_compact_closed_ball ([#9337](https://github.com/leanprover-community/mathlib/pull/9337))
The old name didn't follow the naming convention at all, which made it hard to discover.

### [2021-09-23 06:06:00](https://github.com/leanprover-community/mathlib/commit/7615f83)
chore(archive/100-theorems-list/42): typo ([#9341](https://github.com/leanprover-community/mathlib/pull/9341))

### [2021-09-23 05:13:45](https://github.com/leanprover-community/mathlib/commit/d238087)
chore(data/real/pi/*): correct authorship data ([#9314](https://github.com/leanprover-community/mathlib/pull/9314))
[#9295](https://github.com/leanprover-community/mathlib/pull/9295) split `data.real.pi` into three files with the naive transferral of authorship and copyright data, this updates it to the actual authorship.

### [2021-09-23 04:17:39](https://github.com/leanprover-community/mathlib/commit/a15ae9c)
chore(measure_theory/measurable_space): add simps config for `measurable_equiv` ([#9315](https://github.com/leanprover-community/mathlib/pull/9315))
Also add `@[ext]` lemma and some standard `equiv` lemmas.

### [2021-09-23 02:22:43](https://github.com/leanprover-community/mathlib/commit/b563e5a)
chore(scripts): update nolints.txt ([#9339](https://github.com/leanprover-community/mathlib/pull/9339))
I am happy to remove some nolints for you!

### [2021-09-23 00:38:17](https://github.com/leanprover-community/mathlib/commit/671b179)
refactor(group_theory/subgroup,linear_algebra/basic): put pointwise actions in their own files to match submonoid ([#9312](https://github.com/leanprover-community/mathlib/pull/9312))

### [2021-09-23 00:38:16](https://github.com/leanprover-community/mathlib/commit/20981be)
feat(linear_algebra/charpoly): add linear_map.charpoly ([#9279](https://github.com/leanprover-community/mathlib/pull/9279))
We add `linear_map.charpoly`, the characteristic polynomial of an endomorphism of a finite free module, and a basic API.

### [2021-09-22 20:20:50](https://github.com/leanprover-community/mathlib/commit/5b3b71a)
chore(data/equiv): rename `bool_to_equiv_prod` to `bool_arrow_equiv_prod` ([#9333](https://github.com/leanprover-community/mathlib/pull/9333))
Other changes:
* use an explicit definition;
* use `@[simps]`.

### [2021-09-22 16:35:13](https://github.com/leanprover-community/mathlib/commit/6eb8d41)
chore(ring_theory/dedekind_domain): speed up `dedekind_domain.lean` ([#9232](https://github.com/leanprover-community/mathlib/pull/9232))
@eric-wieser [noticed that `dedekind_domain.lean`](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Timeouts.20in.20ring_theory.2Fdedekind_domain.2Elean.3A664.3A9) was compiling slowly and on the verge of a timeout. @kbuzzard, @sgouezel and I reworked some definitions to make everything elaborate much faster: `is_dedekind_domain_inv_iff`, `mul_inv_cancel_of_le_one` and `ideal.unique_factorization_monoid` went from over 10 seconds on my machine to less than 3 seconds. No other declaration in that file now takes over 2 seconds on my machine.
Apart from the three declarations getting new proofs, I also made the following changes:
 * The operations on `localization` (`has_add`, `has_mul`, `has_one`, `has_zero`, `has_neg`, `npow` and `localization.inv`) are now `@[irreducible]`
 * `fraction_ring.field` copies its field from `localization.comm_ring` for faster unification (less relevant after the previous change)
 * Added `fractional_ideal.map_mem_map` and `fractional_ideal.map_injective` to simplify the proof of `is_dedekind_domain_inv_iff`.
 * Split the proof of `matrix.exists_mul_vec_eq_zero_iff` into two parts to speed it up

### [2021-09-22 15:37:39](https://github.com/leanprover-community/mathlib/commit/dc5a3db)
feat(algebra/category): Forgetful functors preserve filtered colimits ([#9101](https://github.com/leanprover-community/mathlib/pull/9101))
Shows that forgetful functors of various algebraic categories preserve filtered colimits.

### [2021-09-22 14:37:26](https://github.com/leanprover-community/mathlib/commit/41414a3)
chore(analysis/special_functions): typo in module doc ([#9330](https://github.com/leanprover-community/mathlib/pull/9330))

### [2021-09-22 14:37:25](https://github.com/leanprover-community/mathlib/commit/2b84c4c)
feat(linear_algebra/matrix/basis): add matrix basis change formula ([#9280](https://github.com/leanprover-community/mathlib/pull/9280))
We add `basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix`, the formula for the change of basis.

### [2021-09-22 14:37:23](https://github.com/leanprover-community/mathlib/commit/68dbf27)
feat(number_theory): the class group of an integral closure is finite ([#9059](https://github.com/leanprover-community/mathlib/pull/9059))
This is essentially the proof that the ring of integers of a global field has a finite class group, apart from filling in each hypothesis.

### [2021-09-22 12:11:46](https://github.com/leanprover-community/mathlib/commit/a5d2dbc)
chore(measure_theory/integral/set_integral): generalize, golf ([#9328](https://github.com/leanprover-community/mathlib/pull/9328))
* rename `integrable_on_finite_union` to `integrable_on_finite_Union`;
* rename `integrable_on_finset_union` to `integrable_on_finset_Union`;
* add `integrable_on_fintype_Union`;
* generalize `tendsto_measure_Union` and `tendsto_measure_Inter from
  `s : ℕ → set α` to
  `[semilattice_sup ι] [encodable ι] {s : ι → set α}`;
* add `integral_diff`;
* generalize `integral_finset_bUnion`, `integral_fintype_Union` and
  `has_sum_integral_Union` to require appropriate `integrable_on`
  instead of `integrable`;
* golf some proofs.

### [2021-09-22 12:11:44](https://github.com/leanprover-community/mathlib/commit/a994071)
chore(data/complex/module): rename `complex.smul_coe` to `real_smul` ([#9326](https://github.com/leanprover-community/mathlib/pull/9326))
* the name was misleading b/c there is no `coe` in the LHS;
* add `complex.coe_smul`: given `x : ℝ` and `y : E`, we have
  `(x : ℂ) • y = x • y`;
* add `normed_space.complex_to_real`.

### [2021-09-22 12:11:43](https://github.com/leanprover-community/mathlib/commit/7e350c2)
feat(category_theory/*): Fully faithful functors induces equivalence ([#9322](https://github.com/leanprover-community/mathlib/pull/9322))
Needed for AffineSchemes ≌ CommRingᵒᵖ.

### [2021-09-22 12:11:42](https://github.com/leanprover-community/mathlib/commit/15730e8)
chore(analysis/convex): trivial generalizations of ℝ ([#9298](https://github.com/leanprover-community/mathlib/pull/9298))

### [2021-09-22 12:11:41](https://github.com/leanprover-community/mathlib/commit/eb3d600)
feat(data/{list,multiset}): add `can_lift` instances ([#9262](https://github.com/leanprover-community/mathlib/pull/9262))
* add `can_lift` instances for `set`, `list`, `multiset`, and `finset`;
* use them in `submonoid.{list,multiset}_prod_mem`;
* more `to_additive` attrs in `group_theory.submonoid.membership`.

### [2021-09-22 10:01:07](https://github.com/leanprover-community/mathlib/commit/c9638b9)
chore(measure_theory): add 2 lemmas ([#9329](https://github.com/leanprover-community/mathlib/pull/9329))

### [2021-09-22 10:01:05](https://github.com/leanprover-community/mathlib/commit/6f2cbde)
chore(order/lattice): tidy up pi instances ([#9305](https://github.com/leanprover-community/mathlib/pull/9305))
These were previously defined in the wrong file, and the lemmas were missing the `pi` prefix that is present on `pi.add_apply` etc.
This also removes the instance names as they are autogenerated correctly.
Finally, this adds new `top_def`, `bot_def`, `sup_def`, and `inf_def` lemmas, which are useful for when wanting to rewrite under the lambda. We already have `zero_def`, `add_def`, etc.

### [2021-09-22 10:01:04](https://github.com/leanprover-community/mathlib/commit/f95f216)
feat(linear_algebra/std_basis): add matrix.std_basis_eq_std_basis_matrix ([#9216](https://github.com/leanprover-community/mathlib/pull/9216))
As suggested in [#9072](https://github.com/leanprover-community/mathlib/pull/9072) by @eric-wieser, we modify `matrix.std_basis` to use the more familiar `n × m` as the index of the basis and we prove that the `(i,j)`-th element of this basis is `matrix.std_basis_matrix i j 1`.

### [2021-09-22 07:37:28](https://github.com/leanprover-community/mathlib/commit/5b55a86)
chore(analysis/calculate/fderiv): move results about analytic functions to a new file ([#9296](https://github.com/leanprover-community/mathlib/pull/9296))
These are not necessary for many of the downstream files, so we can speed up compilation a bit by parallelising these.

### [2021-09-22 07:37:27](https://github.com/leanprover-community/mathlib/commit/6d86622)
chore(*): removing unneeded imports ([#9278](https://github.com/leanprover-community/mathlib/pull/9278))

### [2021-09-22 07:37:21](https://github.com/leanprover-community/mathlib/commit/b77aa3a)
feat(linear_algebra/affine_space/affine_subspace): prove that a set whose affine span is top cannot be empty. ([#9113](https://github.com/leanprover-community/mathlib/pull/9113))
The lemma `finset.card_sdiff_add_card` is unrelated but I've been meaning to add it
and now seemed like a good time since I'm touching `data/finset/basic.lean` anyway.

### [2021-09-22 06:45:10](https://github.com/leanprover-community/mathlib/commit/f59dbf2)
chore(data/complex/exponential): add `abs_exp`, golf ([#9327](https://github.com/leanprover-community/mathlib/pull/9327))

### [2021-09-22 02:48:40](https://github.com/leanprover-community/mathlib/commit/7112730)
feat(set_theory/cardinal_ordinal): mul_le_max and others ([#9269](https://github.com/leanprover-community/mathlib/pull/9269))

### [2021-09-22 02:48:39](https://github.com/leanprover-community/mathlib/commit/9c34e80)
chore(linear_algebra/basic): generalize `add_monoid_hom_lequiv_{nat,int}` ([#9233](https://github.com/leanprover-community/mathlib/pull/9233))

### [2021-09-22 01:01:52](https://github.com/leanprover-community/mathlib/commit/5625ec0)
refactor(algebra/module/linear_map): Put linear equivalences in their own file ([#9301](https://github.com/leanprover-community/mathlib/pull/9301))
This is consistent with how we have ring homs and ring equivs in separate files.
By having each of these files smaller than the original, we can split `linear_algebra/basic` more effectively between them.

### [2021-09-21 17:41:00](https://github.com/leanprover-community/mathlib/commit/e0d568e)
feat(analysis/normed_space/basic): the rescaling of a ball is a ball ([#9297](https://github.com/leanprover-community/mathlib/pull/9297))
Also rename all statements with `ball_0` to `ball_zero` for coherence.

### [2021-09-21 15:54:06](https://github.com/leanprover-community/mathlib/commit/56a6ed6)
chore(algebra/algebra/basic): remove a duplicate instance ([#9320](https://github.com/leanprover-community/mathlib/pull/9320))
`algebra.linear_map.module'` is just a special case of `linear_map.module'`.
`by apply_instance` finds this instance provided it's used after the definition of `is_scalar_tower.to_smul_comm_class`.

### [2021-09-21 15:54:04](https://github.com/leanprover-community/mathlib/commit/420f11a)
feat(measure_theory/decomposition/radon_nikodym): Radon-Nikodym and Lebesgue decomposition for signed measures ([#9065](https://github.com/leanprover-community/mathlib/pull/9065))
This PR proves the Radon-Nikodym theorem for signed measures.

### [2021-09-21 14:54:34](https://github.com/leanprover-community/mathlib/commit/c4fbb6f)
refactor(data/real/ereal): replace `.cases` with `.rec` ([#9321](https://github.com/leanprover-community/mathlib/pull/9321))
This provides a nicer spelling than the pile of `rfl`s we use with the old `ereal.cases`, as follows:
```diff
-rcases x.cases with rfl|⟨y, rfl⟩|rfl,
+induction x using ereal.rec with y,
```
As a bonus, the subgoals now end up with names matching the hypotheses.

### [2021-09-21 11:46:50](https://github.com/leanprover-community/mathlib/commit/30617c7)
chore(group_theory/order_of_element): bump up ([#9318](https://github.com/leanprover-community/mathlib/pull/9318))
there may be other lemmas that can similarly be moved around here

### [2021-09-21 09:53:10](https://github.com/leanprover-community/mathlib/commit/b5a6422)
feat(data/finset): add lemmas ([#9209](https://github.com/leanprover-community/mathlib/pull/9209))
* add `finset.image_id'`, a version of `finset.image_id` using `λ x, x` instead of `id`;
* add some lemmas about `finset.bUnion`, `finset.sup`, and `finset.sup'`.

### [2021-09-21 08:03:51](https://github.com/leanprover-community/mathlib/commit/524ded6)
refactor(data/polynomial/{coeff,monomial}): move smul_eq_C_mul ([#9287](https://github.com/leanprover-community/mathlib/pull/9287))
This moves `smul_eq_C_mul` from `monomial.lean` into `coeff.lean` so that the import on `monomial.lean` can be changed from `data.polynomial.coeff` to `data.polynomial.basic`. This should shave about 10 seconds off the [longest pole for parallelized mathlib compilation](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/The.20long.20pole.20in.20mathlib/near/253932389).

### [2021-09-21 08:03:50](https://github.com/leanprover-community/mathlib/commit/4cee743)
feat(measure_theory/measure/vector_measure): add `mutually_singular.neg` ([#9282](https://github.com/leanprover-community/mathlib/pull/9282))

### [2021-09-21 08:03:48](https://github.com/leanprover-community/mathlib/commit/78340e3)
feat(topology/continuous_function/basic): gluing lemmas ([#9239](https://github.com/leanprover-community/mathlib/pull/9239))

### [2021-09-21 06:38:58](https://github.com/leanprover-community/mathlib/commit/49e0bcf)
feat(topology/bases): continuous_of_basis_is_open_preimage ([#9281](https://github.com/leanprover-community/mathlib/pull/9281))
Check continuity on a basis.

### [2021-09-21 02:39:51](https://github.com/leanprover-community/mathlib/commit/13780bc)
chore(scripts): update nolints.txt ([#9317](https://github.com/leanprover-community/mathlib/pull/9317))
I am happy to remove some nolints for you!

### [2021-09-20 20:43:00](https://github.com/leanprover-community/mathlib/commit/46ff449)
feat(data/vector/basic): lemmas, and linting ([#9260](https://github.com/leanprover-community/mathlib/pull/9260))

### [2021-09-20 18:11:00](https://github.com/leanprover-community/mathlib/commit/175afa8)
refactor(analysis/convex/{extreme, exposed}): generalize `is_extreme` and `is_exposed` to semimodules ([#9264](https://github.com/leanprover-community/mathlib/pull/9264))
`is_extreme` and `is_exposed` are currently only defined in real vector spaces. This generalizes ℝ to arbitrary `ordered_semiring`s in definitions and abstracts it away to the correct generality in lemmas. It also generalizes the space from `add_comm_group` to `add_comm_monoid`.

### [2021-09-20 16:39:36](https://github.com/leanprover-community/mathlib/commit/ae726e1)
chore(ring_theory/polynomial/tower): remove a duplicate instance ([#9302](https://github.com/leanprover-community/mathlib/pull/9302))
`apply_instance` already finds a much more general statement of this instance.

### [2021-09-20 16:39:35](https://github.com/leanprover-community/mathlib/commit/c2d8a58)
feat(algebra/algebra/basic): lemmas about alg_hom and scalar towers ([#9249](https://github.com/leanprover-community/mathlib/pull/9249))

### [2021-09-20 14:51:32](https://github.com/leanprover-community/mathlib/commit/866294d)
fix(data/dfinsupp): fix nat- and int- module diamonds ([#9299](https://github.com/leanprover-community/mathlib/pull/9299))
This also defines `has_sub` separately in case it turns out to help with unification

### [2021-09-20 13:42:14](https://github.com/leanprover-community/mathlib/commit/3703ab2)
chore(data/real/pi): split into three files ([#9295](https://github.com/leanprover-community/mathlib/pull/9295))
This is the last file to finish compilation in mathlib, and it naturally splits into three chunks, two of which have simpler dependencies.

### [2021-09-20 13:42:12](https://github.com/leanprover-community/mathlib/commit/8c96c54)
feat(ci): Download all possible caches in gitpod ([#9286](https://github.com/leanprover-community/mathlib/pull/9286))
This requests mathlibtools 1.1.0

### [2021-09-20 13:42:11](https://github.com/leanprover-community/mathlib/commit/72a8cd6)
feat(field_theory/algebraic_closure): any two algebraic closures are isomorphic ([#9231](https://github.com/leanprover-community/mathlib/pull/9231))

### [2021-09-20 11:48:30](https://github.com/leanprover-community/mathlib/commit/cb33f68)
feat(docker): pin version for better reproducibility ([#9304](https://github.com/leanprover-community/mathlib/pull/9304))
Also hopefully force docker rebuild for gitpod

### [2021-09-20 11:48:29](https://github.com/leanprover-community/mathlib/commit/4df2a1b)
feat(topology/instances/ennreal): sum of nonzero constants is infinity ([#9294](https://github.com/leanprover-community/mathlib/pull/9294))

### [2021-09-20 11:48:28](https://github.com/leanprover-community/mathlib/commit/e41e9bc)
chore(group_theory/submonoid/operations): split a file ([#9292](https://github.com/leanprover-community/mathlib/pull/9292))

### [2021-09-20 11:48:27](https://github.com/leanprover-community/mathlib/commit/7389a6b)
feat(linear_algebra/matrix/to_lin): simp lemmas for to_matrix and algebra ([#9267](https://github.com/leanprover-community/mathlib/pull/9267))

### [2021-09-20 11:48:26](https://github.com/leanprover-community/mathlib/commit/ba28234)
feat(algebra/pointwise): more lemmas about pointwise actions ([#9226](https://github.com/leanprover-community/mathlib/pull/9226))
This:
* Primes the existing lemmas about `group_with_zero` and adds their group counterparts
* Adds:
  * `smul_mem_smul_set_iff`
  * `set_smul_subset_set_smul_iff`
  * `set_smul_subset_iff`
  * `subset_set_smul_iff`
* Generalizes `zero_smul_set` to take weaker typeclasses

### [2021-09-20 10:37:41](https://github.com/leanprover-community/mathlib/commit/e29dfc1)
chore(analysis/normed_space/finite_dimensional): restructure imports ([#9289](https://github.com/leanprover-community/mathlib/pull/9289))
Delays importing `linear_algebra.finite_dimensional` in the `analysis/normed_space/` directory until it is really needed.
This reduces the ["long pole"](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/The.20long.20pole.20in.20mathlib) of mathlib compilation by 3 minutes (out of 55).

### [2021-09-20 08:13:28](https://github.com/leanprover-community/mathlib/commit/d93c6a8)
feat(data/vector/basic): induction principles ([#9261](https://github.com/leanprover-community/mathlib/pull/9261))

### [2021-09-20 04:23:41](https://github.com/leanprover-community/mathlib/commit/238d792)
chore(scripts): update nolints.txt ([#9290](https://github.com/leanprover-community/mathlib/pull/9290))
I am happy to remove some nolints for you!

### [2021-09-20 04:23:40](https://github.com/leanprover-community/mathlib/commit/035bd24)
refactor(field_theory/algebraic_closure): Move construction of algebraic closure and lemmas about alg closed fields into seperate files. ([#9265](https://github.com/leanprover-community/mathlib/pull/9265))

### [2021-09-20 04:23:39](https://github.com/leanprover-community/mathlib/commit/acb10a5)
feat(linear_algebra/{multilinear,alternating): add of_subsingleton ([#9196](https://github.com/leanprover-community/mathlib/pull/9196))
This was refactored from the `koszul_cx` branch, something I mentioned doing in [this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/two.20decidable_eq.20instances.20on.20.28fin.201.29.20in.20mathlib.20.3A-.28/near/225596630).
The original version was:
```lean
def multilinear_map.of_subsingleton (ι : Type v) [subsingleton ι] [inhabited ι] {N : Type u}
  [add_comm_group N] [module R N] (f : M →ₗ[R] N) : multilinear_map R (λ (i : ι), M) N :=
{ to_fun := λ x, f (x $ default ι),
  map_add' := λ m i x y, by rw subsingleton.elim i (default ι); simp only
    [function.update_same, f.map_add],
  map_smul' := λ m i r x, by rw subsingleton.elim i (default ι); simp only
    [function.update_same, f.map_smul], }
```
but I decided to remove the `f : M →ₗ[R] N` argument as it can be added later with `(of_subsingleton R M i).comp_linear_map f`.

### [2021-09-20 04:23:38](https://github.com/leanprover-community/mathlib/commit/976b261)
feat(data/{multiset,finset}/basic): card_erase_eq_ite ([#9185](https://github.com/leanprover-community/mathlib/pull/9185))
A generic theorem about the cardinality of a `finset` or `multiset` with an element erased.

### [2021-09-20 01:59:40](https://github.com/leanprover-community/mathlib/commit/f37f57d)
feat(order/lattice): `sup`/`inf`/`max`/`min` of mono functions ([#9284](https://github.com/leanprover-community/mathlib/pull/9284))
* add `monotone.sup`, `monotone.inf`, `monotone.min`, and
  `monotone.max`;
* add `prod.le_def` and `prod.mk_le_mk`.

### [2021-09-19 21:03:01](https://github.com/leanprover-community/mathlib/commit/4887f80)
chore(measure_theory/function/simple_func_dense): distance to `approx_on` is antitone ([#9271](https://github.com/leanprover-community/mathlib/pull/9271))

### [2021-09-19 20:10:14](https://github.com/leanprover-community/mathlib/commit/f7135f1)
feat(group_theory/p_group): `is_p_group` is preserved by `subgroup.comap` ([#9277](https://github.com/leanprover-community/mathlib/pull/9277))
If `H` is a p-subgroup, then `H.comap f` is a p-subgroup, assuming that `f` is injective.

### [2021-09-19 17:47:09](https://github.com/leanprover-community/mathlib/commit/965e457)
feat(measure_theory/measure/lebesgue): a linear map rescales Lebesgue by the inverse of its determinant ([#9195](https://github.com/leanprover-community/mathlib/pull/9195))
Also supporting material to be able to apply Fubini in `ι → ℝ` by separating some coordinates.

### [2021-09-19 16:07:52](https://github.com/leanprover-community/mathlib/commit/180c758)
feat(group_theory/p_group): `is_p_group` is preserved by `subgroup.map` ([#9276](https://github.com/leanprover-community/mathlib/pull/9276))
If `H` is a p-subgroup, then `H.map f` is a p-subgroup.

### [2021-09-19 13:44:55](https://github.com/leanprover-community/mathlib/commit/55a2c1a)
refactor(set_theory/{cardinal,ordinal}): swap the order of universes in `lift` ([#9273](https://github.com/leanprover-community/mathlib/pull/9273))
Swap the order of universe arguments in `cardinal.lift` and `ordinal.lift`. This way (a) they match the order of arguments in `ulift`; (b) usually Lean can deduce the second universe level from the argument.

### [2021-09-19 13:44:53](https://github.com/leanprover-community/mathlib/commit/8df86df)
feat(order/ideal, data/set/lattice): when order ideals are a complete lattice ([#9084](https://github.com/leanprover-community/mathlib/pull/9084))
- Added the `ideal_Inter_nonempty` property, which states that the intersection of all ideals in the lattice is nonempty.
- Proved that when a preorder has the above property and is a `semilattice_sup`, its ideals are a complete lattice
- Added some lemmas about empty intersections in set/lattice, akin to [#9033](https://github.com/leanprover-community/mathlib/pull/9033)

### [2021-09-19 11:34:13](https://github.com/leanprover-community/mathlib/commit/075ff37)
refactor(algebra/order*): move files about ordered algebraic structures into subfolder ([#9024](https://github.com/leanprover-community/mathlib/pull/9024))
There were many files named `algebra/order_*.lean`. There are also `algebra.{module,algebra}.ordered`. The latter are Prop-valued mixins. This refactor moves the data typeclasses into their own subfolder. That should help facilitate organizing further refactoring to provide the full gamut of the order x algebra hierarchy.

### [2021-09-19 10:06:14](https://github.com/leanprover-community/mathlib/commit/383e05a)
feat(measure_theory/integral/lebesgue): add set version of `lintegral_with_density_eq_lintegral_mul` ([#9270](https://github.com/leanprover-community/mathlib/pull/9270))
I also made `measurable_space α` an implicit argument whenever `μ : measure α` is explicit.

### [2021-09-19 07:45:41](https://github.com/leanprover-community/mathlib/commit/25e67dd)
feat(measure_theory/function/lp_space): add mem_Lp_indicator_iff_restrict ([#9221](https://github.com/leanprover-community/mathlib/pull/9221))
We have an equivalent lemma for `integrable`. Here it is generalized to `mem_ℒp`.

### [2021-09-19 06:12:34](https://github.com/leanprover-community/mathlib/commit/f2c162c)
feat(data/dfinsupp): more lemmas about erase, filter, and negation ([#9248](https://github.com/leanprover-community/mathlib/pull/9248))

### [2021-09-19 02:28:42](https://github.com/leanprover-community/mathlib/commit/cbf8788)
chore(scripts): update nolints.txt ([#9275](https://github.com/leanprover-community/mathlib/pull/9275))
I am happy to remove some nolints for you!

### [2021-09-18 23:07:48](https://github.com/leanprover-community/mathlib/commit/fbc9e5e)
feat(measure_theory/function/conditional_expectation): condexp_ind is ae_measurable' ([#9263](https://github.com/leanprover-community/mathlib/pull/9263))

### [2021-09-18 23:07:47](https://github.com/leanprover-community/mathlib/commit/6b96736)
feat(measure_theory/integral/set_to_L1): image of an indicator by set_to_fun (and related functions) ([#9205](https://github.com/leanprover-community/mathlib/pull/9205))
We show the following equality, as well as versions of it for other intermediate `set_to_*` functions:
```
set_to_fun (hT : dominated_fin_meas_additive μ T C) (s.indicator (λ _, x)) = T s x
```

### [2021-09-18 23:07:46](https://github.com/leanprover-community/mathlib/commit/c1d7ee5)
feat(measure_theory/measure/finite_measure_weak_convergence): definitions of types of finite_measures and probability_measures, to be equipped with the topologies of weak convergence ([#8904](https://github.com/leanprover-community/mathlib/pull/8904))
feat(measure_theory/measure/finite_measure_weak_convergence): definitions of types of finite_measures and probability_measures, to be equipped with the topologies of weak convergence
This PR defines the types `probability_measure` and `finite_measure`. The next step is to give a topology instance on these types.

### [2021-09-18 20:45:54](https://github.com/leanprover-community/mathlib/commit/429aaa3)
feat(order/bounded_lattice): coe_unbot simp lemma ([#9258](https://github.com/leanprover-community/mathlib/pull/9258))

### [2021-09-18 20:45:53](https://github.com/leanprover-community/mathlib/commit/811c87a)
chore(order/galois_connection): golf ([#9236](https://github.com/leanprover-community/mathlib/pull/9236))
* add `galois_insertion.is_lub_of_u_image`,
  `galois_insertion.is_glb_of_u_image`,
  `galois_coinsertion.is_glb_of_l_image`, and
  `galois_coinsertion.is_lub_of_l_image`;
* get some proofs in `lift_*` from `order_dual` instances;
* this changes definitional equalities for `Inf` and `Sup` so that we can reuse the same `Inf`/`Sup` for a `conditionally_complete_lattice` later.

### [2021-09-18 19:04:24](https://github.com/leanprover-community/mathlib/commit/e4bf496)
feat(data/set/finite): simple infiniteness lemmas ([#9242](https://github.com/leanprover-community/mathlib/pull/9242))

### [2021-09-18 19:04:23](https://github.com/leanprover-community/mathlib/commit/255862e)
refactor(linear_algebra/char_poly/basic): rename char_poly to matrix.charpoly ([#9230](https://github.com/leanprover-community/mathlib/pull/9230))
We rename `char_matrix` to `charmatrix` and `char_poly` to `matrix.charpoly`, so `M.charpoly` becomes available (and everything is coherent with `minpoly`).

### [2021-09-18 16:39:30](https://github.com/leanprover-community/mathlib/commit/e757936)
chore(data/real/ennreal, measure_theory/): use `≠ ∞` and `≠ 0` in assumptions ([#9219](https://github.com/leanprover-community/mathlib/pull/9219))

### [2021-09-18 15:14:00](https://github.com/leanprover-community/mathlib/commit/33db1c7)
chore(data/mv_polynomial/basic): add ring_hom_ext' and move ext attribute to ring_hom_ext' ([#9235](https://github.com/leanprover-community/mathlib/pull/9235))

### [2021-09-18 13:22:05](https://github.com/leanprover-community/mathlib/commit/10a6201)
feat(set_theory/ordinal): add conditionally_complete_linear_order_bot instance ([#9266](https://github.com/leanprover-community/mathlib/pull/9266))
Currently, it is not possible to talk about `Inf s` when `s` is a set of ordinals. This is fixed by this PR.

### [2021-09-18 12:00:20](https://github.com/leanprover-community/mathlib/commit/d6b4cd7)
chore(ring_theory/adjoin/basic): split ([#9257](https://github.com/leanprover-community/mathlib/pull/9257))
I want to use basic facts about `adjoin` in `polynomial.basic`.

### [2021-09-18 10:03:09](https://github.com/leanprover-community/mathlib/commit/0ee36a3)
feat(order/conditionally_complete_lattice): add lemmas ([#9237](https://github.com/leanprover-community/mathlib/pull/9237))
* add lemmas about `conditionally_complete_linear_order_bot`; in this
  case we can drop some `nonempty` assumptions;
* add lemmas for the case of `[is_well_order α (<)]`; in this case
  infimum of a nonempty set is the least element of this set.

### [2021-09-18 06:53:44](https://github.com/leanprover-community/mathlib/commit/36751e4)
chore(algebra/algebra/tower): golf `algebra.lsmul` ([#9253](https://github.com/leanprover-community/mathlib/pull/9253))

### [2021-09-18 06:53:43](https://github.com/leanprover-community/mathlib/commit/41e152f)
fix(algebra/algebra/tower): remove `subalgebra.res` which duplicates `subalgebra.restrict_scalars` ([#9251](https://github.com/leanprover-community/mathlib/pull/9251))
We use the name `restrict_scalars` everywhere else, so I kept that one instead of `res`.
`res` was here first, but the duplicate was added by [#7949](https://github.com/leanprover-community/mathlib/pull/7949) presumably because the `res` name wasn't discoverable.

### [2021-09-18 06:53:42](https://github.com/leanprover-community/mathlib/commit/5e58247)
feat(algebra/ordered_pi): ordered_comm_monoid and canonically_ordered_monoid instances ([#9194](https://github.com/leanprover-community/mathlib/pull/9194))
Presumably these instances were missing because they were not actually constructible until we fixed the definition of `ordered_monoid` in [#8877](https://github.com/leanprover-community/mathlib/pull/8877)!

### [2021-09-18 02:27:19](https://github.com/leanprover-community/mathlib/commit/0bdd47f)
feat(data/list/basic): add lemmas about list.take list.drop ([#9245](https://github.com/leanprover-community/mathlib/pull/9245))
I added these lemmas about list.take and list.drop, which are present in Coq for example. Note that they are not entirely equivalent to list.take_append and list.drop_append because they also handle the case when `n ≤ l₁.length`

### [2021-09-18 02:27:17](https://github.com/leanprover-community/mathlib/commit/a8f2bab)
chore(set_theory/cardinal): use notation `#`, add notation `ω` ([#9217](https://github.com/leanprover-community/mathlib/pull/9217))
The only API change: rename `cardinal.eq_congr` to `cardinal.mk_congr`.

### [2021-09-18 00:17:26](https://github.com/leanprover-community/mathlib/commit/ec9d520)
feat(order/filter,*): lemmas about `filter.ne_bot` ([#9234](https://github.com/leanprover-community/mathlib/pull/9234))
* add `prod.range_fst`, `prod.range_snd`, `set.range_eval`;
* add `function.surjective_eval`;
* add `filter.*_ne_bot` and/or `filter.*_ne_bot_iff` lemmas for `sup`, `supr`,
  `comap prod.fst _`, `comap prod.snd _`, `coprod`, `Coprod`.

### [2021-09-17 20:09:59](https://github.com/leanprover-community/mathlib/commit/a80e1d7)
chore(topology/metric_space): split `iff` into 2 lemmas ([#9238](https://github.com/leanprover-community/mathlib/pull/9238))
One of the implications of `compact_iff_closed_bounded` doesn't need `t2_space`. Also add `compact_space_iff_bounded_univ`.

### [2021-09-17 20:09:58](https://github.com/leanprover-community/mathlib/commit/c42a9ad)
chore(data/finsupp/basic): lemmas about sub and neg on filter and erase ([#9228](https://github.com/leanprover-community/mathlib/pull/9228))

### [2021-09-17 20:09:57](https://github.com/leanprover-community/mathlib/commit/54217b6)
chore(data/list): make separate lexicographic file ([#9193](https://github.com/leanprover-community/mathlib/pull/9193))
A minor effort to reduce the `data.list.basic` monolithic, today inspired by yet again being annoyed that I couldn't find something.

### [2021-09-17 20:09:56](https://github.com/leanprover-community/mathlib/commit/696db1e)
feat(analysis/convex/topology): add lemma `convex.subset_interior_image_homothety_of_one_lt` ([#9044](https://github.com/leanprover-community/mathlib/pull/9044))

### [2021-09-17 16:23:57](https://github.com/leanprover-community/mathlib/commit/58f26a0)
chore(order/bounded_lattice): trivial generalizations ([#9246](https://github.com/leanprover-community/mathlib/pull/9246))

### [2021-09-17 14:39:08](https://github.com/leanprover-community/mathlib/commit/dfd4bf5)
split(analysis/convex/function): move `convex_on` and `concave_on` to their own file ([#9247](https://github.com/leanprover-community/mathlib/pull/9247))
Convex/concave functions now earn their own file. This cuts down `analysis.convex.basic` by 500 lines.

### [2021-09-17 12:18:09](https://github.com/leanprover-community/mathlib/commit/5f140ab)
chore(*): rename `coe_fn_inj` to `coe_fn_injective` ([#9241](https://github.com/leanprover-community/mathlib/pull/9241))
This also removes some comments about it not being possible to use `function.injective`, since now we use it without problem.

### [2021-09-17 09:52:16](https://github.com/leanprover-community/mathlib/commit/5b75f5a)
chore(algebra/group/basic): add `ite_one_mul` and `ite_zero_add` ([#9227](https://github.com/leanprover-community/mathlib/pull/9227))
We already had the versions with the arguments in the other order.
Follows on from [#3217](https://github.com/leanprover-community/mathlib/pull/3217)

### [2021-09-17 09:00:53](https://github.com/leanprover-community/mathlib/commit/18d031d)
fix(ring_theory/dedekind_domain): Speed up ideal.unique_factorization_monoid ([#9243](https://github.com/leanprover-community/mathlib/pull/9243))
The old proof was causing timeouts in CI.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Timeouts.20in.20ring_theory.2Fdedekind_domain.2Elean.3A664.3A9/near/253579691)

### [2021-09-17 06:22:56](https://github.com/leanprover-community/mathlib/commit/15bf066)
feat(measure_theory/function/l1_space): add integrability lemmas for composition with `to_real` ([#9199](https://github.com/leanprover-community/mathlib/pull/9199))

### [2021-09-16 19:59:45](https://github.com/leanprover-community/mathlib/commit/59cda6d)
feat(measure_theory/group/basic): introduce a class is_haar_measure, and its basic properties ([#9142](https://github.com/leanprover-community/mathlib/pull/9142))
We have in mathlib a construction of Haar measures. But there are many measures which do not come from this construction, and are still Haar measures (Lebesgue measure on a vector space, Hausdorff measure of the right dimension, for instance). We introduce a new class `is_haar_measure` (and its additive analogue) to be able to express facts simultaneously for all these measures, and prove their basic properties.

### [2021-09-16 16:02:06](https://github.com/leanprover-community/mathlib/commit/76f87b7)
feat(group_theory/group_action/basic): Action on an orbit ([#9220](https://github.com/leanprover-community/mathlib/pull/9220))
A `mul_action` restricts to a `mul_action` on an orbit.

### [2021-09-16 13:26:32](https://github.com/leanprover-community/mathlib/commit/ca38357)
feat(group_theory/group_action): add `distrib_mul_action.to_add_aut` and `mul_distrib_mul_action.to_mul_aut` ([#9224](https://github.com/leanprover-community/mathlib/pull/9224))
These can be used to golf the existing `mul_aut_arrow`.
This also moves some definitions out of `algebra/group_ring_action.lean` into a more appropriate file.

### [2021-09-16 13:26:31](https://github.com/leanprover-community/mathlib/commit/17a473e)
feat(group_theory/p_group): Sup of p-subgroups is a p-subgroup ([#9222](https://github.com/leanprover-community/mathlib/pull/9222))
The sup of p-subgroups is a p-subgroup, assuming normality.

### [2021-09-16 13:26:30](https://github.com/leanprover-community/mathlib/commit/b0d961b)
chore(algebra/indicator_function): add `finset.sum_indicator_eq_sum_filter` ([#9208](https://github.com/leanprover-community/mathlib/pull/9208))

### [2021-09-16 13:26:29](https://github.com/leanprover-community/mathlib/commit/fdfe782)
feat(combinatorics/derangements/*): add lemmas about counting derangements ([#9089](https://github.com/leanprover-community/mathlib/pull/9089))
This defines `card_derangements` as the cardinality of the set of derangements of a fintype, and `num_derangements` as a function from N to N, and proves their equality, along with some other lemmas.
Context: PR [#7526](https://github.com/leanprover-community/mathlib/pull/7526) grew too large and had to be split in half. The first half retained the original PR ID, and this is the second half. This adds back the finite.lean and exponential.lean files. Also, added entries back to 100.yaml.

### [2021-09-16 13:26:27](https://github.com/leanprover-community/mathlib/commit/89b0cfb)
refactor(analysis/convex/basic): generalize convexity to vector spaces ([#9058](https://github.com/leanprover-community/mathlib/pull/9058))
`convex` and `convex_hull` are currently only defined in real vector spaces. This generalizes ℝ to arbitrary ordered_semirings in definitions and abstracts it away to the correct generality in lemmas. It also generalizes the space from `add_comm_group` to `add_comm_monoid` where possible.

### [2021-09-16 11:34:14](https://github.com/leanprover-community/mathlib/commit/f536b4f)
fix(group_theory/submonoid/operations): add missing `to_additive` tags on galois lemmas ([#9225](https://github.com/leanprover-community/mathlib/pull/9225))

### [2021-09-16 11:34:13](https://github.com/leanprover-community/mathlib/commit/8a1fc68)
feat(measure_theory/measure/with_density_vector_measure): `with_densityᵥ` of a real function equals the density of the pos part - density of the neg part ([#9215](https://github.com/leanprover-community/mathlib/pull/9215))

### [2021-09-16 11:34:12](https://github.com/leanprover-community/mathlib/commit/232ff44)
feat(measure_theory/measure/measure_space): add mutually singular lemmas ([#9213](https://github.com/leanprover-community/mathlib/pull/9213))

### [2021-09-16 11:34:11](https://github.com/leanprover-community/mathlib/commit/bc7cde8)
feat(data/dfinsupp): add `filter_ne_eq_erase` ([#9182](https://github.com/leanprover-community/mathlib/pull/9182))

### [2021-09-16 11:34:09](https://github.com/leanprover-community/mathlib/commit/86d20e5)
feat(data/dfinsupp): add arithmetic lemmas about filter ([#9175](https://github.com/leanprover-community/mathlib/pull/9175))
This adds `dfinsupp.filter_{zero,add,neg,sub,smul}` and `dfinsupp.subtype_domain_smul`, along with some bundled maps.
This also cleans up some variable explicitness.

### [2021-09-16 10:37:03](https://github.com/leanprover-community/mathlib/commit/b759384)
feat(field_theory/algebraic_closure): map from algebraic extensions into the algebraic closure ([#9110](https://github.com/leanprover-community/mathlib/pull/9110))

### [2021-09-16 05:50:06](https://github.com/leanprover-community/mathlib/commit/18dc1a1)
feat(group_theory/p_group): p-groups are preserved by isomorphisms ([#9203](https://github.com/leanprover-community/mathlib/pull/9203))
Adds three lemmas about transporting `is_p_group` across injective, surjective, and bijective homomorphisms.

### [2021-09-15 23:41:53](https://github.com/leanprover-community/mathlib/commit/519b4e9)
chore(algebra/big_operators): move, golf ([#9218](https://github.com/leanprover-community/mathlib/pull/9218))
move 2 lemmas up and golf the proof of `finset.prod_subset`.

### [2021-09-15 18:42:11](https://github.com/leanprover-community/mathlib/commit/2b589ca)
feat(group_theory/subgroup): Generalize `comap_sup_eq` ([#9212](https://github.com/leanprover-community/mathlib/pull/9212))
The lemma `comap_sup_eq` can be generalized from assuming `function.surjective f` to assuming `≤ f.range`.

### [2021-09-15 18:42:10](https://github.com/leanprover-community/mathlib/commit/8185637)
refactor(data/real/nnreal): use `has_ordered_sub` ([#9167](https://github.com/leanprover-community/mathlib/pull/9167))
* provide a `has_ordered_sub` instance for `nnreal`;
* drop most lemmas about subtraction in favor of lemmas from `algebra/ordered_sub`;
* add `mul_sub'` and `sub_mul'`;
* generalize some lemmas about `has_ordered_sub` to `has_add`;
* add `add_hom.mul_left` and `add_hom.mul_right`.

### [2021-09-15 18:42:09](https://github.com/leanprover-community/mathlib/commit/a4341f9)
refactor(data/set/finite): use a custom inductive type ([#9164](https://github.com/leanprover-community/mathlib/pull/9164))
Currently Lean treats local assumptions `h : finite s` as local instances, so one needs to do something like
```lean
  unfreezingI { lift s to finset α using hs },
```
I change the definition of `set.finite` to an inductive predicate that replicates the definition of `nonempty` and remove `unfreezingI` here and there. Equivalence to the old definition is given by `set.finite_def`.

### [2021-09-15 18:42:07](https://github.com/leanprover-community/mathlib/commit/244285c)
feat(linear_algebra/free_module): add instances ([#9087](https://github.com/leanprover-community/mathlib/pull/9087))
We add some `module.finite` instances. These are in the `linear_algebra/free_module.lean` files since they concern free modules.
From LTE

### [2021-09-15 18:42:06](https://github.com/leanprover-community/mathlib/commit/bab7e99)
docs(data/part): add module docstring ([#8966](https://github.com/leanprover-community/mathlib/pull/8966))

### [2021-09-15 17:09:28](https://github.com/leanprover-community/mathlib/commit/b63c560)
feat(data/set/Union_lift): lift functions to Unions of sets ([#9019](https://github.com/leanprover-community/mathlib/pull/9019))

### [2021-09-15 15:40:39](https://github.com/leanprover-community/mathlib/commit/2597264)
chore(ring_theory/ideal/operations): golf a definition using new actions ([#9152](https://github.com/leanprover-community/mathlib/pull/9152))
This action can be expressed more directly in terms of other actions, without the unfolded definition changing.

### [2021-09-15 13:22:40](https://github.com/leanprover-community/mathlib/commit/3a6340c)
chore(data/dfinsupp): golf using `quotient.map` instead of `quotient.lift_on` ([#9176](https://github.com/leanprover-community/mathlib/pull/9176))

### [2021-09-15 13:22:39](https://github.com/leanprover-community/mathlib/commit/f8d8171)
refactor(logic/relator): turn *_unique and *_total into defs, not classes ([#9135](https://github.com/leanprover-community/mathlib/pull/9135))
We had (almost) no instances for these classes and (almost) no lemmas taking these assumptions as TC arguments.

### [2021-09-15 12:38:53](https://github.com/leanprover-community/mathlib/commit/f1bf7b8)
feat(category_theory/filtered): Special support for bowtie and tulip diagrams ([#9099](https://github.com/leanprover-community/mathlib/pull/9099))
Add special support for two kinds of diagram categories: The "bowtie" and the "tulip". These are convenient when proving that forgetful functors of algebraic categories preserve filtered colimits.

### [2021-09-15 10:33:05](https://github.com/leanprover-community/mathlib/commit/bb38ce9)
feat(ring_theory/artinian): is_nilpotent_jacobson ([#9153](https://github.com/leanprover-community/mathlib/pull/9153))

### [2021-09-15 07:15:07](https://github.com/leanprover-community/mathlib/commit/85dc9f3)
refactor(measure_theory/measure): redefine `measure_theory.sigma_finite` ([#9207](https://github.com/leanprover-community/mathlib/pull/9207))
* don't require in the definition that covering sets are measurable;
* use `to_measurable` in `sigma_finite.out` to get measurable sets.

### [2021-09-15 06:12:44](https://github.com/leanprover-community/mathlib/commit/7492aa6)
refactor(measure_theory/integral/lebesgue): golf a proof ([#9206](https://github.com/leanprover-community/mathlib/pull/9206))
* add `exists_pos_tsum_mul_lt_of_encodable`;
* add `measure.spanning_sets_index` and lemmas about this definition;
* replace the proof of `exists_integrable_pos_of_sigma_finite` with a simpler one.

### [2021-09-15 02:43:59](https://github.com/leanprover-community/mathlib/commit/591ff3a)
feat(group_theory/subgroup): Subgroup of subgroup is isomorphic to itself ([#9204](https://github.com/leanprover-community/mathlib/pull/9204))
If `H ≤ K`, then `H` as a subgroup of `K` is isomorphic to `H`.

### [2021-09-15 02:43:58](https://github.com/leanprover-community/mathlib/commit/463089d)
feat(order/rel_classes): A total relation is trichotomous ([#9181](https://github.com/leanprover-community/mathlib/pull/9181))

### [2021-09-15 02:43:57](https://github.com/leanprover-community/mathlib/commit/23eac53)
chore(*): upgrade to Lean 3.33.0c ([#9165](https://github.com/leanprover-community/mathlib/pull/9165))
My main goal is to fix various diamonds with `sup`/`inf`, see leanprover-community/lean[#609](https://github.com/leanprover-community/mathlib/pull/609). I use lean-master + 1 fixup commit leanprover-community/lean[#615](https://github.com/leanprover-community/mathlib/pull/615).

### [2021-09-15 00:53:15](https://github.com/leanprover-community/mathlib/commit/82dced6)
feat(analysis/normed_space/finite_dimension): Riesz theorem on compact unit ball and finite dimension ([#9147](https://github.com/leanprover-community/mathlib/pull/9147))

### [2021-09-14 20:59:54](https://github.com/leanprover-community/mathlib/commit/27b0a76)
feat(ring_theory/adjoin): adjoin_range_eq_range_aeval ([#9179](https://github.com/leanprover-community/mathlib/pull/9179))

### [2021-09-14 18:16:26](https://github.com/leanprover-community/mathlib/commit/bf0b5df)
chore(combinatorics/simple_graph): fixup docs ([#9161](https://github.com/leanprover-community/mathlib/pull/9161))

### [2021-09-14 17:25:52](https://github.com/leanprover-community/mathlib/commit/ec118dd)
ci(.github/workflows/*): lint PR style on GitHub runners ([#9198](https://github.com/leanprover-community/mathlib/pull/9198))
Since the style linter usually finishes in just a few seconds, we can move it off our self-hosted runners to give PR authors quicker feedback when the build queue is long.
We do this only for PR runs, so that `bors` won't be held up in case the GitHub runners are backed up for whatever reason.

### [2021-09-14 15:08:00](https://github.com/leanprover-community/mathlib/commit/6a6b0a5)
chore(order/pilex): use `*_order_of_*TO` from `order.rel_classes` ([#9129](https://github.com/leanprover-community/mathlib/pull/9129))
This changes definitional equality for `≤` on `pilex` from
`x < y ∨ x = y` to `x = y ∨ x < y`.

### [2021-09-14 13:37:53](https://github.com/leanprover-community/mathlib/commit/91f053e)
chore(*): simplify `data.real.cau_seq` import ([#9197](https://github.com/leanprover-community/mathlib/pull/9197))
Some files were still importing `data.real.cau_seq` when their dependency really was on `is_absolute_value`, which has been moved to `algebra.absolute_value`. Hopefully simplifying the dependency tree slightly reduces build complexity.

### [2021-09-14 12:09:47](https://github.com/leanprover-community/mathlib/commit/e489ca1)
feat(group_theory/p_group): Intersection with p-subgroup is a p-subgroup ([#9189](https://github.com/leanprover-community/mathlib/pull/9189))
Two lemmas stating that the intersection with a p-subgroup is a p-subgroup.
Not sure which one should be called left and which one should be called right though :)

### [2021-09-14 12:09:45](https://github.com/leanprover-community/mathlib/commit/eb20390)
refactor(group_theory/p_group): Move lemmas to is_p_group namespace ([#9188](https://github.com/leanprover-community/mathlib/pull/9188))
Moves `card_modeq_card_fixed_points`, `nonempty_fixed_point_of_prime_not_dvd_card`, and `exists_fixed_point_of_prime_dvd_card_of_fixed_point` to the `is_p_group` namespace. I think this simplifies things, since they already had explicit `hG : is_p_group G` hypotheses anyway.

### [2021-09-14 12:09:44](https://github.com/leanprover-community/mathlib/commit/6309c81)
chore(ring_theory/adjoin) elab_as_eliminator attribute ([#9168](https://github.com/leanprover-community/mathlib/pull/9168))

### [2021-09-14 12:09:43](https://github.com/leanprover-community/mathlib/commit/251e418)
feat(ring_theory/nakayama): Alternative Statements of Nakayama's Lemma ([#9150](https://github.com/leanprover-community/mathlib/pull/9150))

### [2021-09-14 12:09:42](https://github.com/leanprover-community/mathlib/commit/19949a0)
feat(linear_algebra/free_module): add instances ([#9072](https://github.com/leanprover-community/mathlib/pull/9072))
From LTE.
We prove that `M →ₗ[R] N` is free if both `M` and `N` are finite and free. This needs the quite long result that for a finite and free module any basis is finite.
Co-authored with @jcommelin

### [2021-09-14 12:09:41](https://github.com/leanprover-community/mathlib/commit/2a3cd41)
feat(group_theory/free_product): equivalence with reduced words ([#7395](https://github.com/leanprover-community/mathlib/pull/7395))
We show that each element of the free product is represented by a unique reduced word.

### [2021-09-14 10:41:25](https://github.com/leanprover-community/mathlib/commit/7deb32c)
chore(data/fintype/intervals): finiteness of `Ioo`, `Ioc`, and `Icc` over `ℕ` ([#9096](https://github.com/leanprover-community/mathlib/pull/9096))
We already have the analogous lemmas and instance for `ℤ`.

### [2021-09-14 08:41:19](https://github.com/leanprover-community/mathlib/commit/2d57545)
feat(measure_theory/measure/integral): integral over an encodable type ([#9191](https://github.com/leanprover-community/mathlib/pull/9191))

### [2021-09-14 08:41:17](https://github.com/leanprover-community/mathlib/commit/790e98f)
feat(linear_algebra/matrix/is_diag): add a file ([#9010](https://github.com/leanprover-community/mathlib/pull/9010))

### [2021-09-14 06:36:12](https://github.com/leanprover-community/mathlib/commit/9af1db3)
feat(measure_theory/measure/measure_space): The pushfoward measure of a finite measure is a finite measure ([#9186](https://github.com/leanprover-community/mathlib/pull/9186))

### [2021-09-14 06:36:11](https://github.com/leanprover-community/mathlib/commit/ceab0e7)
chore(order/bounded_lattice): make `bot_lt_some` and `some_lt_none` consistent ([#9180](https://github.com/leanprover-community/mathlib/pull/9180))
`with_bot.bot_lt_some` gets renamed to `with_bot.none_lt_some` and now syntactically applies to `none : with_bot α` (`with_bot.bot_le_coe` already applies to `⊥` and `↑a`).
`with_top.some_lt_none` now takes `a` explicit.

### [2021-09-14 06:36:10](https://github.com/leanprover-community/mathlib/commit/ef78b32)
feat(measure_theory/function/lp_space): add lemmas about snorm and mem_Lp ([#9146](https://github.com/leanprover-community/mathlib/pull/9146))
Also move lemma `snorm_add_le` (and related others) out of the borel space section, since `opens_measurable_space` is a sufficient hypothesis.

### [2021-09-14 06:36:09](https://github.com/leanprover-community/mathlib/commit/5aaa5fa)
chore(measure_theory/integral/set_integral): update old lemmas that were in comments at the end of the file ([#9111](https://github.com/leanprover-community/mathlib/pull/9111))
The file `set_integral` had a list of lemmas in comments at the end of the file, which were written for an old implementation of the set integral. This PR deletes the comments, and adds the corresponding results when they don't already exist.
The lemmas `set_integral_congr_set_ae` and `set_integral_mono_set` are also moved to relevant sections.

### [2021-09-14 06:36:08](https://github.com/leanprover-community/mathlib/commit/4b7593f)
feat(data/last/basic): a lemma specifying list.split_on ([#9104](https://github.com/leanprover-community/mathlib/pull/9104))

### [2021-09-14 04:32:20](https://github.com/leanprover-community/mathlib/commit/d3b345d)
feat(group_theory/p_group): Bottom subgroup is a p-group ([#9190](https://github.com/leanprover-community/mathlib/pull/9190))
The bottom subgroup is a p-group.
Name is consistent with `is_p_group.of_card`

### [2021-09-14 04:32:19](https://github.com/leanprover-community/mathlib/commit/8dffafd)
feat(topology): one-point compactification of a topological space ([#8579](https://github.com/leanprover-community/mathlib/pull/8579))
Define `alexandroff X` to be the one-point compactification of a topological space `X` and prove some basic lemmas about this definition.
Co-authored by: Yury G. Kudryashov <urkud@urkud.name>

### [2021-09-14 03:42:22](https://github.com/leanprover-community/mathlib/commit/f88f3a7)
chore(scripts): update nolints.txt ([#9192](https://github.com/leanprover-community/mathlib/pull/9192))
I am happy to remove some nolints for you!

### [2021-09-14 01:19:50](https://github.com/leanprover-community/mathlib/commit/f0a1356)
feat(linear_algebra/matrix/circulant): add a file ([#9011](https://github.com/leanprover-community/mathlib/pull/9011))

### [2021-09-13 23:34:39](https://github.com/leanprover-community/mathlib/commit/103c1ff)
feat(data/(d)finsupp): (d)finsupp.update ([#9015](https://github.com/leanprover-community/mathlib/pull/9015))

### [2021-09-13 18:35:51](https://github.com/leanprover-community/mathlib/commit/d9476d4)
fix(tactic/rcases): Don't parameterize parsers ([#9159](https://github.com/leanprover-community/mathlib/pull/9159))
The parser description generator only unfolds parser constants if they have no arguments, which means that parsers like `rcases_patt_parse tt` and `rcases_patt_parse ff` don't generate descriptions even though they have a `with_desc` clause. We fix this by naming the parsers separately.
Fixes [#9158](https://github.com/leanprover-community/mathlib/pull/9158)

### [2021-09-13 17:45:52](https://github.com/leanprover-community/mathlib/commit/ec5f496)
feat(README.md): add Rémy Degenne ([#9187](https://github.com/leanprover-community/mathlib/pull/9187))

### [2021-09-13 16:19:14](https://github.com/leanprover-community/mathlib/commit/40247bd)
feat(measure_theory/measure/vector_measure): add `vector_measure.trim` ([#9169](https://github.com/leanprover-community/mathlib/pull/9169))

### [2021-09-13 16:19:13](https://github.com/leanprover-community/mathlib/commit/3b4f4da)
feat(linear_algebra/determinant): more on the determinant of linear maps ([#9139](https://github.com/leanprover-community/mathlib/pull/9139))

### [2021-09-13 13:59:40](https://github.com/leanprover-community/mathlib/commit/a9e7d33)
chore(analysis/calculus/[f]deriv): generalize product formula to product in normed algebras ([#9163](https://github.com/leanprover-community/mathlib/pull/9163))

### [2021-09-13 13:59:39](https://github.com/leanprover-community/mathlib/commit/ad62583)
chore(algebra/big_operators): add a lemma ([#9120](https://github.com/leanprover-community/mathlib/pull/9120))
(product over `s.filter p`) * (product over `s.filter (λ x, ¬p x)) = product over s

### [2021-09-13 10:22:39](https://github.com/leanprover-community/mathlib/commit/b0e8ced)
feat(group_theory/nilpotent): add intermediate lemmas ([#9016](https://github.com/leanprover-community/mathlib/pull/9016))
Add two new lemmas on nilpotent groups.

### [2021-09-13 09:34:19](https://github.com/leanprover-community/mathlib/commit/a8a8edc)
feat(group_theory/p_group): Generalize to infinite p-groups ([#9082](https://github.com/leanprover-community/mathlib/pull/9082))
Defines p-groups, and generalizes the results of `p_group.lean` to infinite p-groups. The eventual goal is to generalize Sylow's theorems to infinite groups.

### [2021-09-13 09:34:17](https://github.com/leanprover-community/mathlib/commit/d4f8b92)
feat(measure_theory/measure/with_density_vector_measure): define vector measures by an integral over a function ([#9008](https://github.com/leanprover-community/mathlib/pull/9008))
This PR defined the vector measure corresponding to mapping the set `s` to the integral `∫ x in s, f x ∂μ` given some measure `μ` and some integrable function `f`.

### [2021-09-13 09:34:16](https://github.com/leanprover-community/mathlib/commit/80085fc)
feat(number_theory/padics/padic_integers): Z_p is adically complete ([#8995](https://github.com/leanprover-community/mathlib/pull/8995))

### [2021-09-13 08:46:12](https://github.com/leanprover-community/mathlib/commit/d082001)
feat(analysis/convex/independent): convex independence ([#9018](https://github.com/leanprover-community/mathlib/pull/9018))

### [2021-09-13 06:36:44](https://github.com/leanprover-community/mathlib/commit/1cf1704)
chore(order/filter): more readable proof ([#9173](https://github.com/leanprover-community/mathlib/pull/9173))

### [2021-09-13 06:36:43](https://github.com/leanprover-community/mathlib/commit/1479068)
chore(ring_theory/polynomial/cyclotomic): fix namespacing ([#9116](https://github.com/leanprover-community/mathlib/pull/9116))
@riccardobrasca told me I got it wrong, so I fixed it :)

### [2021-09-13 06:00:30](https://github.com/leanprover-community/mathlib/commit/5651157)
feat(linear_algebra/adic_completion): le_jacobson_bot ([#9125](https://github.com/leanprover-community/mathlib/pull/9125))
This PR proves that in an `I`-adically complete commutative ring `R`, the ideal `I` is contained in the Jacobson radical of `R`.

### [2021-09-13 04:04:40](https://github.com/leanprover-community/mathlib/commit/ca23d52)
feat(set_theory/surreal): add dyadic surreals ([#7843](https://github.com/leanprover-community/mathlib/pull/7843))
We define `surreal.dyadic` using a map from \int localized away from 2 to surreals. As currently we do not have the ring structure on `surreal` we do this "by hand". 
Next steps: 
1. Prove that `dyadic_map` is injective
2. Prove that `dyadic_map` is a group hom
3. Show that \int localized away from 2 is a subgroup of \rat.

### [2021-09-13 02:40:27](https://github.com/leanprover-community/mathlib/commit/f0effbd)
chore(scripts): update nolints.txt ([#9177](https://github.com/leanprover-community/mathlib/pull/9177))
I am happy to remove some nolints for you!

### [2021-09-13 00:53:07](https://github.com/leanprover-community/mathlib/commit/87c1820)
feat(group_theory/perm/concrete_cycle): perms from cycle data structure ([#8866](https://github.com/leanprover-community/mathlib/pull/8866))

### [2021-09-12 22:30:08](https://github.com/leanprover-community/mathlib/commit/f6c8aff)
feat(order/zorn) : `chain_univ` ([#9162](https://github.com/leanprover-community/mathlib/pull/9162))
`univ` is a `r`-chain iff `r` is trichotomous

### [2021-09-12 20:47:08](https://github.com/leanprover-community/mathlib/commit/5b702ec)
chore(linear_algebra/basic): move map_comap_eq into submodule namespace ([#9160](https://github.com/leanprover-community/mathlib/pull/9160))
We change the following lemmas from the `linear_map` namespace into the `submodule` namespace
- map_comap_eq
- comap_map_eq
- map_comap_eq_self
- comap_map_eq_self
This is consistent with `subgroup.map_comap_eq`, and the lemmas are about `submodule.map` so it make sense to keep them in the submodule namespace.

### [2021-09-12 18:41:01](https://github.com/leanprover-community/mathlib/commit/00d570a)
doc(algebra/covariant_and_contravariant): fix parameter documentation… ([#9171](https://github.com/leanprover-community/mathlib/pull/9171))
… in covariant_class and contravariant_class
In the documentation of `algebra.covariant_and_contravariant.covariant_class` and `algebra.covariant_and_contravariant.contravariant_class`, the parameter `r` is described as having type `N → N`. It's actual type is `N → N → Prop`. We change the documentation to give the correct type of `r`.

### [2021-09-12 18:41:00](https://github.com/leanprover-community/mathlib/commit/65f8148)
chore(algebra/field_power): golf some proofs ([#9170](https://github.com/leanprover-community/mathlib/pull/9170))

### [2021-09-12 18:40:59](https://github.com/leanprover-community/mathlib/commit/3366a68)
feat(data/fin): eq_zero_or_eq_succ ([#9136](https://github.com/leanprover-community/mathlib/pull/9136))
Particularly useful with `rcases i.eq_zero_or_eq_succ with rfl|⟨j,rfl⟩`.
Perhaps it not worth having as a separate lemma, but it seems to avoid breaking the flow of a proof I was writing.

### [2021-09-12 17:53:26](https://github.com/leanprover-community/mathlib/commit/a7d872f)
chore(category/abelian/pseudoelements): localize expensive typeclass ([#9156](https://github.com/leanprover-community/mathlib/pull/9156))
Per @fpvandoorn's [new linter](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/type-class.20loops.20in.20category.20theory).

### [2021-09-12 15:14:38](https://github.com/leanprover-community/mathlib/commit/995f481)
feat(logic/basic): a few lemmas ([#9166](https://github.com/leanprover-community/mathlib/pull/9166))

### [2021-09-12 09:48:17](https://github.com/leanprover-community/mathlib/commit/04d2b12)
feat(ring_theory/ideal/operations): annihilator_smul ([#9151](https://github.com/leanprover-community/mathlib/pull/9151))

### [2021-09-12 06:48:16](https://github.com/leanprover-community/mathlib/commit/f863703)
fix(category_theory/concrete_category): remove bad instance ([#9154](https://github.com/leanprover-community/mathlib/pull/9154))
Per @fpvandoorn's [new linter](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/type-class.20loops.20in.20category.20theory).

### [2021-09-12 06:48:15](https://github.com/leanprover-community/mathlib/commit/858e764)
fix(ring_theory/ideal/basic): ideal.module_pi speedup ([#9148](https://github.com/leanprover-community/mathlib/pull/9148))
Eric and Yael were both complaining that `ideal.module_pi` would occasionally cause random timeouts on unrelated PRs. This PR (a) makes the `smul` proof obligation much tidier (factoring out a sublemma) and (b) replaces the `all_goals` trick by 6 slightly more refined proofs (making the new proof longer, but quicker). On my machine the profiler stats are:
```
ORIG
parsing took 74.1ms
elaboration of module_pi took 3.83s
type checking of module_pi took 424ms
decl post-processing of module_pi took 402ms
NEW
parsing took 136ms
elaboration of module_pi took 1.19s
type checking of module_pi took 82.8ms
decl post-processing of module_pi took 82.5ms
```

### [2021-09-12 06:48:14](https://github.com/leanprover-community/mathlib/commit/b55483a)
feat(category_theory/monoidal): rigid (autonomous) monoidal categories ([#8946](https://github.com/leanprover-community/mathlib/pull/8946))
Defines rigid monoidal categories and creates the instance of finite dimensional vector spaces.

### [2021-09-12 05:54:55](https://github.com/leanprover-community/mathlib/commit/e1bed5a)
fix(category_theory/adjunction/limits): remove bad instance ([#9157](https://github.com/leanprover-community/mathlib/pull/9157))
Per @fpvandoorn's [new linter](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/type-class.20loops.20in.20category.20theory).

### [2021-09-12 05:54:54](https://github.com/leanprover-community/mathlib/commit/059eba4)
fix(category/preadditive/single_obj): remove superfluous instance ([#9155](https://github.com/leanprover-community/mathlib/pull/9155))
Per @fpvandoorn's [new linter](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/type-class.20loops.20in.20category.20theory).

### [2021-09-12 02:16:49](https://github.com/leanprover-community/mathlib/commit/96c1d69)
doc(data/list/*): Elaborate module docstrings ([#9076](https://github.com/leanprover-community/mathlib/pull/9076))
Just adding some elaboration that @YaelDillies requested in [#8867](https://github.com/leanprover-community/mathlib/pull/8867), but which didn't get included before it was merged.

### [2021-09-12 01:07:51](https://github.com/leanprover-community/mathlib/commit/f75bee3)
chore(ring_theory/noetherian): fix URL ([#9149](https://github.com/leanprover-community/mathlib/pull/9149))

### [2021-09-11 22:57:24](https://github.com/leanprover-community/mathlib/commit/55aaebe)
feat(data/real/ennreal): add `contravariant_class ennreal ennreal (+) (<)` ([#9143](https://github.com/leanprover-community/mathlib/pull/9143))
## `algebra/ordered_monoid`
* use `≠ ⊤`/`≠ ⊥` instead of `< ⊤`/`⊥ <`  in the assumptions of `with_top.add_lt_add_iff_left`, `with_top.add_lt_add_iff_right`, `with_bot.add_lt_add_iff_left`, and `with_bot.add_lt_add_iff_right`;
* add instances for `contravariant_class (with_top α) (with_top α) (+) (<)` and `contravariant_class (with_bot α) (with_bot α) (+) (<)`.
## `data/real/ennreal`
* use `≠ ∞` instead of `< ∞`  in the assumptions of `ennreal.add_lt_add_iff_left`, `ennreal.add_lt_add_iff_right`, `ennreal.lt_add_right`,
* add an instance `contravariant_class ℝ≥0∞ ℝ≥0∞ (+) (<)`;
* rename `ennreal.sub_infty` to `ennreal.sub_top`.
## `measure_theory/measure/outer_measure`
* use `≠ ∞` instead of `< ∞`  in the assumptions of `induced_outer_measure_exists_set`;
## `topology/metric_space/emetric_space`
* use `≠ ∞` instead of `< ∞`  in the assumptions of `emetric.ball_subset`.

### [2021-09-11 21:56:23](https://github.com/leanprover-community/mathlib/commit/c0693ca)
chore(analysis/calculus/*): add `filter.eventually_eq.deriv` etc. ([#9131](https://github.com/leanprover-community/mathlib/pull/9131))
* add `filter.eventually_eq.deriv` and `filter.eventually_eq.fderiv`;
* add `times_cont_diff_within_at.eventually` and `times_cont_diff_at.eventually`.

### [2021-09-11 20:56:00](https://github.com/leanprover-community/mathlib/commit/1605b85)
feat(data/real/ennreal): add ennreal.to_(nn)real_inv and ennreal.to_(nn)real_div ([#9144](https://github.com/leanprover-community/mathlib/pull/9144))

### [2021-09-11 17:31:41](https://github.com/leanprover-community/mathlib/commit/b9ad733)
split(analysis/convex/combination): split off `analysis.convex.basic` ([#9115](https://github.com/leanprover-community/mathlib/pull/9115))
This moves `finset.center_mass` into its own new file.
About the copyright header, `finset.center_mass` comes from [#1804](https://github.com/leanprover-community/mathlib/pull/1804), which was written by Yury in December 2019.

### [2021-09-11 15:52:14](https://github.com/leanprover-community/mathlib/commit/62de591)
feat(interval_integral): generalize change of variables ([#8869](https://github.com/leanprover-community/mathlib/pull/8869))
* Generalizes `interval_integral.integral_comp_mul_deriv'`.
In this version:
(1) `f` need not be differentiable at the endpoints of `[a,b]`, only continuous,
(2) I removed the `measurable_at_filter` assumption
(3) I assumed that `g` was continuous on `f '' [a,b]`, instead of continuous at every point of `f '' [a,b]` (which differs in the endpoints).
This was possible after @sgouezel's PR [#7978](https://github.com/leanprover-community/mathlib/pull/7978).
The proof was a lot longer/messier than expected. Under these assumptions we have to be careful to sometimes take one-sided derivatives. For example, we cannot take the 2-sided derivative of `λ u, ∫ x in f a..u, g x` when `u` is the maximum/minimum of `f` on `[a, b]`.
@urkud: I needed more `FTC_filter` classes, namely for closed intervals (to be precise: `FTC_filter x (𝓝[[a, b]] x) (𝓝[[a, b]] x)`). Was there a conscious reason to exclude these classes? (The documentation explicitly enumerates the existing instances.)

### [2021-09-11 14:06:54](https://github.com/leanprover-community/mathlib/commit/6823886)
feat(measure_theory/function/conditional_expectation): conditional expectation of an indicator ([#8920](https://github.com/leanprover-community/mathlib/pull/8920))
This PR builds `condexp_ind  (s : set α) : E →L[ℝ] α →₁[μ] E`, which takes `x : E` to the conditional expectation of the indicator of the set `s` with value `x`, seen as an element of `α →₁[μ] E`.
This linear map will be used in a next PR to define the conditional expectation from L1 to L1, by using the same extension mechanism as in the Bochner integral construction.

### [2021-09-11 12:23:38](https://github.com/leanprover-community/mathlib/commit/241ee9e)
feat(data/finsupp): more lemmas about `α →₀ ℕ` ([#9137](https://github.com/leanprover-community/mathlib/pull/9137))

### [2021-09-11 12:23:37](https://github.com/leanprover-community/mathlib/commit/e009354)
chore(data/mv_polynomials): golf, add a lemma ([#9132](https://github.com/leanprover-community/mathlib/pull/9132))
* add `monoid_algebra.support_mul_single`;
* transfer a few more lemmas from `monoid_algebra` to `add_monoid_algebra`
* add `mv_polynomial.support_mul_X`
* reuse a proof.

### [2021-09-11 12:23:36](https://github.com/leanprover-community/mathlib/commit/d72119c)
feat(data/mv_polynomial/equiv): empty_equiv ([#9122](https://github.com/leanprover-community/mathlib/pull/9122))

### [2021-09-11 11:48:10](https://github.com/leanprover-community/mathlib/commit/f318e5d)
chore(ring_theory/artinian): typo ([#9140](https://github.com/leanprover-community/mathlib/pull/9140))

### [2021-09-11 04:25:26](https://github.com/leanprover-community/mathlib/commit/579ca5e)
chore(combinatorics/simple_graph): rename sym to symm ([#9134](https://github.com/leanprover-community/mathlib/pull/9134))
The naming convention for symmetry of a relation in mathlib seems to be symm, so this commit renames the axiom for the symmetry of the adjacency relation of a simple graph to this.

### [2021-09-11 04:25:25](https://github.com/leanprover-community/mathlib/commit/919aad2)
refactor(topology/path_connected): make `path` extend `C(I, X)` ([#9133](https://github.com/leanprover-community/mathlib/pull/9133))

### [2021-09-11 04:25:24](https://github.com/leanprover-community/mathlib/commit/8413622)
chore(algebra/ordered_smul): reduce instance assumptions & delete duplicated instances ([#9130](https://github.com/leanprover-community/mathlib/pull/9130))
These instances all assumed `semiring R` superfluously:
* `order_dual.smul_with_zero`
* `order_dual.mul_action`
* `order_dual.mul_action_with_zero`
* `order_dual.distrib_mul_action`
and these instances were duplicates (with their `opposite.`-less counterparts):
* `opposite.mul_zero_class.to_opposite_smul_with_zero`
* `opposite.monoid_with_zero.to_opposite_mul_action_with_zero`
* `opposite.semiring.to_opposite_module`

### [2021-09-11 04:25:23](https://github.com/leanprover-community/mathlib/commit/2e9f708)
feat(algebra/ordered_monoid): order_embedding.mul_left ([#9127](https://github.com/leanprover-community/mathlib/pull/9127))

### [2021-09-11 03:46:20](https://github.com/leanprover-community/mathlib/commit/4c96b8a)
feat(measure_theory/measure/set_integral): new lemma integral_Union ([#9093](https://github.com/leanprover-community/mathlib/pull/9093))

### [2021-09-11 01:08:22](https://github.com/leanprover-community/mathlib/commit/426227d)
chore(algebra/group/basic): add 3 `simp` attrs ([#9050](https://github.com/leanprover-community/mathlib/pull/9050))

### [2021-09-10 20:31:43](https://github.com/leanprover-community/mathlib/commit/e4ca117)
feat(ring_theory/algebraic): is_algebraic_of_larger_base ([#9109](https://github.com/leanprover-community/mathlib/pull/9109))

### [2021-09-10 18:48:06](https://github.com/leanprover-community/mathlib/commit/7500529)
refactor(analysis/convex/basic): generalize segments to vector spaces ([#9094](https://github.com/leanprover-community/mathlib/pull/9094))
`segment` and `open_segment` are currently only defined in real vector spaces. This generalizes ℝ to arbitrary ordered_semirings in definitions and abstracts it away to the correct generality in lemmas. It also generalizes the space from `add_comm_group` to `add_comm_monoid` where possible.

### [2021-09-10 18:48:05](https://github.com/leanprover-community/mathlib/commit/0e014ba)
feat(combinatorics/simple_graph/adj_matrix): more lemmas ([#9021](https://github.com/leanprover-community/mathlib/pull/9021))

### [2021-09-10 16:18:38](https://github.com/leanprover-community/mathlib/commit/a949b57)
feat(data/mv_polynomial): mv_polynomial.subsingleton ([#9124](https://github.com/leanprover-community/mathlib/pull/9124))

### [2021-09-10 16:18:37](https://github.com/leanprover-community/mathlib/commit/92e7bbe)
refactor(algebra/group/units): better defeq for is_unit.unit ([#9112](https://github.com/leanprover-community/mathlib/pull/9112))
Make sure that, for `x : M` and `h : is_unit M`, then `is_unit.unit x h : M` is defeq to `x`.

### [2021-09-10 16:18:36](https://github.com/leanprover-community/mathlib/commit/574864d)
feat(topology/compact_open): express the compact-open topology as an Inf of topologies ([#9106](https://github.com/leanprover-community/mathlib/pull/9106))
For `f : C(α, β)` and a set `s` in `α`, define `f.restrict s` to be the restriction of `f` as an element of `C(s, β)`.  This PR then proves that the compact-open topology on `C(α, β)` is equal to the infimum of the induced compact-open topologies from the restrictions to compact sets.

### [2021-09-10 16:18:35](https://github.com/leanprover-community/mathlib/commit/d2afdc5)
feat(ring_theory/dedekind_domain): add proof that `I \sup J` is the product of `factors I \inf factors J` for `I, J` ideals in a Dedekind Domain  ([#9055](https://github.com/leanprover-community/mathlib/pull/9055))

### [2021-09-10 15:18:22](https://github.com/leanprover-community/mathlib/commit/6d2cbf9)
feat(ring_theory/artinian): Artinian modules ([#9009](https://github.com/leanprover-community/mathlib/pull/9009))

### [2021-09-10 15:18:21](https://github.com/leanprover-community/mathlib/commit/2410c1f)
feat(topology/homotopy): Define homotopy between functions ([#8947](https://github.com/leanprover-community/mathlib/pull/8947))
More PRs are to come, with homotopy between paths etc. So this will probably become a folder at some point, but for now I've just put it in `topology/homotopy.lean`. There's also not that much API here at the moment, more will be added later on.

### [2021-09-10 13:08:34](https://github.com/leanprover-community/mathlib/commit/5ce9280)
feat(measure_theory/integral/bochner): generalize the Bochner integral construction ([#8939](https://github.com/leanprover-community/mathlib/pull/8939))
The construction of the Bochner integral is generalized to a process extending a set function `T : set α → (E →L[ℝ] F)` from sets to functions in L1. The integral corresponds to `T s` equal to the linear map `E →L[ℝ] E` with value `λ x, (μ s).to_real • x`.
The conditional expectation from L1 to L1 will be defined by taking for `T` the function `condexp_ind : set α → (E →L[ℝ] α →₁[μ] E)` defined in [#8920](https://github.com/leanprover-community/mathlib/pull/8920) .

### [2021-09-10 13:08:33](https://github.com/leanprover-community/mathlib/commit/56ff42b)
feat(linear_algebra/matrix/transvection): matrices are generated by transvections and diagonal matrices ([#8898](https://github.com/leanprover-community/mathlib/pull/8898))
One version of Gauss' pivot: any matrix can be obtained starting from a diagonal matrix and doing elementary moves on rows and columns. Phrased in terms of multiplication by transvections.

### [2021-09-10 10:53:36](https://github.com/leanprover-community/mathlib/commit/a057a8e)
feat(ring_theory/norm): `norm R x = 0 ↔ x = 0` ([#9042](https://github.com/leanprover-community/mathlib/pull/9042))
Nonzero values of `S / R` have nonzero norm over `R`.

### [2021-09-10 07:18:23](https://github.com/leanprover-community/mathlib/commit/37e17c5)
feat(measure_theory/integral/lebesgue): add some lintegral lemmas ([#9064](https://github.com/leanprover-community/mathlib/pull/9064))
This PR contains some lemmas useful for [#9065](https://github.com/leanprover-community/mathlib/pull/9065).

### [2021-09-10 07:18:22](https://github.com/leanprover-community/mathlib/commit/ae86776)
feat(measure_theory/measure/vector_measure): define mutually singular for vector measures ([#8896](https://github.com/leanprover-community/mathlib/pull/8896))

### [2021-09-10 02:16:47](https://github.com/leanprover-community/mathlib/commit/aec02d8)
chore(scripts): update nolints.txt ([#9126](https://github.com/leanprover-community/mathlib/pull/9126))
I am happy to remove some nolints for you!

### [2021-09-09 20:12:35](https://github.com/leanprover-community/mathlib/commit/4d88ae8)
feat(tactic/lint): better fails_quickly linter ([#8932](https://github.com/leanprover-community/mathlib/pull/8932))
This linter catches a lot more loops.

### [2021-09-09 17:58:39](https://github.com/leanprover-community/mathlib/commit/138d98b)
feat(ring_theory/mv_polynomial): linear_independent_X ([#9118](https://github.com/leanprover-community/mathlib/pull/9118))

### [2021-09-09 16:13:53](https://github.com/leanprover-community/mathlib/commit/b9fcf9b)
feat(linear_algebra/matrix/nonsingular_inverse): adjugate_mul_distrib ([#8682](https://github.com/leanprover-community/mathlib/pull/8682))
We prove that the adjugate of a matrix distributes over the product. To do so, a separate file 
`linear_algebra.matrix.polynomial` states some general facts about the polynomial `det (t I + A)`.

### [2021-09-09 14:10:32](https://github.com/leanprover-community/mathlib/commit/2331607)
feat(group_theory/sub{monoid,group}): pointwise actions on `add_sub{monoid,group}`s and `sub{monoid,group,module,semiring,ring,algebra}`s ([#8945](https://github.com/leanprover-community/mathlib/pull/8945))
This adds the pointwise actions characterized by `↑(m • S) = (m • ↑S : set R)` on:
* `submonoid`
* `subgroup`
* `add_submonoid`
* `add_subgroup`
* `submodule` ([Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Lost.20instance/near/249467913))
* `subsemiring`
* `subring`
* `subalgebra`
within the locale `pointwise` (which must be open to state the RHS of the characterization above anyway).

### [2021-09-09 12:54:22](https://github.com/leanprover-community/mathlib/commit/1825671)
feat(ring_theory/unique_factorization_domain): add lemma that a member of `factors a` divides `a` ([#9108](https://github.com/leanprover-community/mathlib/pull/9108))

### [2021-09-09 09:36:30](https://github.com/leanprover-community/mathlib/commit/e597b75)
feat(algebra/algebra/subalgebra): mem_under ([#9107](https://github.com/leanprover-community/mathlib/pull/9107))

### [2021-09-09 09:36:29](https://github.com/leanprover-community/mathlib/commit/694da7e)
feat(ring_theory): the surjective image of a PID is a PID ([#9069](https://github.com/leanprover-community/mathlib/pull/9069))
If the preimage of an ideal/submodule under a surjective map is principal, so is the original ideal. Therefore, the image of a principal ideal domain under a surjective ring hom is again a PID.

### [2021-09-09 09:36:28](https://github.com/leanprover-community/mathlib/commit/1356397)
refactor(linear_algebra/*): linear_equiv.of_bijective over semirings ([#9061](https://github.com/leanprover-community/mathlib/pull/9061))
`linear_equiv.of_injective` and `linear_equiv.of_bijective`
took as assumption `f.ker = \bot`,
which is equivalent to injectivity of `f` over rings,
but not over semirings.
This PR changes the assumption to `injective f`.
For reasons of symmetry,
the surjectivity assumption is also switched to `surjective f`.
As a consequence, this PR also renames:
* `linear_equiv_of_ker_eq_bot` to `linear_equiv_of_injective`
* `linear_equiv_of_ker_eq_bot_apply` to `linear_equiv_of_injective_apply`

### [2021-09-09 07:32:09](https://github.com/leanprover-community/mathlib/commit/f6ccb6b)
chore(ring_theory/polynomial/cyclotomic): golf+remove `nontrivial` ([#9090](https://github.com/leanprover-community/mathlib/pull/9090))

### [2021-09-09 07:32:08](https://github.com/leanprover-community/mathlib/commit/90475a9)
refactor(data/matrix): put std_basis_matrix in its own file ([#9088](https://github.com/leanprover-community/mathlib/pull/9088))
The authors here are recovered from the git history.
I've avoided the temptation to generalize typeclasses in this PR; the lemmas are copied to this file unmodified.

### [2021-09-09 07:32:07](https://github.com/leanprover-community/mathlib/commit/9568977)
fix(group_theory/group_action): generalize assumptions on `ite_smul` and `smul_ite` ([#9085](https://github.com/leanprover-community/mathlib/pull/9085))

### [2021-09-09 07:32:06](https://github.com/leanprover-community/mathlib/commit/3e10324)
feat(data/polynomial/taylor): Taylor expansion of polynomials ([#9000](https://github.com/leanprover-community/mathlib/pull/9000))

### [2021-09-09 06:19:13](https://github.com/leanprover-community/mathlib/commit/e336caf)
chore(algebra/floor): add a trivial lemma ([#9098](https://github.com/leanprover-community/mathlib/pull/9098))
* add `nat_ceil_eq_zero`;
* add `@[simp]` to `nat_ceil_le`.

### [2021-09-09 04:01:05](https://github.com/leanprover-community/mathlib/commit/796efae)
feat(data/real/sqrt): `nnreal.coe_sqrt` and `nnreal.sqrt_eq_rpow` ([#9025](https://github.com/leanprover-community/mathlib/pull/9025))
Also rename a few lemmas:
* `nnreal.mul_sqrt_self` -> `nnreal.mul_self_sqrt` to follow `real.mul_self_sqrt`
* `real.sqrt_le` -> `real.sqrt_le_sqrt_iff`
* `real.sqrt_lt` -> `real.sqrt_lt_sqrt_iff`
and provide a few more for commodity:
* `nnreal.sqrt_sq`
* `nnreal.sq_sqrt`
* `real.sqrt_lt_sqrt`
* `real.sqrt_lt_sqrt_iff_of_pos`
* `nnreal.sqrt_le_sqrt_iff`
* `nnreal.sqrt_lt_sqrt_iff`
Closes [#8016](https://github.com/leanprover-community/mathlib/pull/8016)

### [2021-09-09 02:59:19](https://github.com/leanprover-community/mathlib/commit/15b6c56)
refactor(category_theory/limits/types): Refactor filtered colimits. ([#9100](https://github.com/leanprover-community/mathlib/pull/9100))
- Rename `filtered_colimit.r` into `filtered_colimit.rel`, to match up with `quot.rel`,
- Rename lemma `r_ge`,
- Abstract out lemma `eqv_gen_quot_rel_of_rel` from later proof.

### [2021-09-09 02:09:44](https://github.com/leanprover-community/mathlib/commit/cfc6b48)
chore(scripts): update nolints.txt ([#9105](https://github.com/leanprover-community/mathlib/pull/9105))
I am happy to remove some nolints for you!

### [2021-09-09 00:00:26](https://github.com/leanprover-community/mathlib/commit/49cf386)
feat(measure_theory/measure/vector_measure): add `absolutely_continuous.add` and `absolutely_continuous.smul` ([#9086](https://github.com/leanprover-community/mathlib/pull/9086))

### [2021-09-08 21:47:47](https://github.com/leanprover-community/mathlib/commit/87e7a0c)
feat(linear_algebra/matrix): `M` maps some `v ≠ 0` to zero iff `det M = 0` ([#9041](https://github.com/leanprover-community/mathlib/pull/9041))
A result I have wanted for a long time: the two notions of a "singular" matrix are equivalent over an integral domain. Namely, a matrix `M` is singular iff it maps some nonzero vector to zero, which happens iff its determinant is zero.
Here, I find such a `v` by going through the field of fractions, where everything is a lot easier because all injective endomorphisms are automorphisms. Maybe a bit overkill (and unsatisfying constructively), but it works and is a lot nicer to write out than explicitly finding an element of the kernel.

### [2021-09-08 21:02:02](https://github.com/leanprover-community/mathlib/commit/ab0a295)
feat(linear_algebra/matrix): some bounds on the determinant of matrices ([#9029](https://github.com/leanprover-community/mathlib/pull/9029))
This PR shows that matrices with bounded entries also have bounded determinants.
`matrix.det_le` is the most generic version of these results, which we specialise in two steps to `matrix.det_sum_smul_le`. In a follow-up PR we will connect this to `algebra.left_mul_matrix` to provide an upper bound on `algebra.norm`.

### [2021-09-08 17:50:43](https://github.com/leanprover-community/mathlib/commit/4222c32)
lint(testing/slim_check/*): break long lines ([#9091](https://github.com/leanprover-community/mathlib/pull/9091))

### [2021-09-08 17:50:42](https://github.com/leanprover-community/mathlib/commit/56a59d3)
feat(data/polynomial/hasse_deriv): Hasse derivatives ([#8998](https://github.com/leanprover-community/mathlib/pull/8998))

### [2021-09-08 17:50:41](https://github.com/leanprover-community/mathlib/commit/42dda89)
feat(ring_theory/discrete_valuation_ring): is_Hausdorff ([#8994](https://github.com/leanprover-community/mathlib/pull/8994))
Discrete valuation rings are Hausdorff in the algebraic sense
that the intersection of all powers of the maximal ideal is 0.

### [2021-09-08 16:06:33](https://github.com/leanprover-community/mathlib/commit/f4f1cd3)
feat(algebra/module/ordered): simple `smul` lemmas ([#9077](https://github.com/leanprover-community/mathlib/pull/9077))
These are the negative versions of the lemmas in `ordered_smul`, which suggests that both files should be merged.
Note however that, contrary to those, they need `module k M` instead of merely `smul_with_zero k M`.

### [2021-09-08 16:06:31](https://github.com/leanprover-community/mathlib/commit/76ab749)
feat(analysis/normed_space/operator_norm): variants of continuous_linear_map.lsmul and their properties ([#8984](https://github.com/leanprover-community/mathlib/pull/8984))

### [2021-09-08 14:01:04](https://github.com/leanprover-community/mathlib/commit/146dddc)
feat(measure_theory/group/arithmetic): add more to_additive attributes for actions ([#9032](https://github.com/leanprover-community/mathlib/pull/9032))
Introduce additivised versions of some more smul classes and corresponding instances and lemmas for different types of (measurable) additive actions.

### [2021-09-08 14:01:03](https://github.com/leanprover-community/mathlib/commit/99b70d9)
feat(data/(fin)set/basic): `image` and `mem` lemmas ([#9031](https://github.com/leanprover-community/mathlib/pull/9031))
I rename `set.mem_image_of_injective` to `function.injective.mem_set_image_iff` to allow dot notation and fit the new  `function.injective.mem_finset_image_iff`.

### [2021-09-08 14:01:01](https://github.com/leanprover-community/mathlib/commit/3d31c2d)
chore(linear_algebra/affine_space/independent): allow dot notation on affine_independent ([#8974](https://github.com/leanprover-community/mathlib/pull/8974))
This renames a few lemmas to make dot notation on `affine_independent` possible.

### [2021-09-08 14:00:59](https://github.com/leanprover-community/mathlib/commit/7a2ccb6)
feat(group_theory/group_action): Extract a smaller typeclass out of `mul_semiring_action` ([#8918](https://github.com/leanprover-community/mathlib/pull/8918))
This new typeclass, `mul_distrib_mul_action`, is satisfied by conjugation actions. This PR provides instances for:
* `mul_aut`
* `prod` of two types with a `mul_distrib_mul_action`
* `pi` of types with a `mul_distrib_mul_action`
* `units` of types with a `mul_distrib_mul_action`
* `ulift` of types with a `mul_distrib_mul_action`
* `opposite` of types with a `mul_distrib_mul_action`
* `sub(monoid|group|semiring|ring)`s of types with a `mul_distrib_mul_action`
* anything already satisfying a `mul_semiring_action`

### [2021-09-08 14:00:58](https://github.com/leanprover-community/mathlib/commit/4c7d95f)
feat(analysis/normed_space/inner_product): reflections API ([#8884](https://github.com/leanprover-community/mathlib/pull/8884))
Reflections, as isometries of an inner product space, were defined in [#8660](https://github.com/leanprover-community/mathlib/pull/8660).  In this PR, various elementary lemmas filling out the API:
- Lemmas about reflection through a subspace K, of a point which is in (i) K itself; (ii) the orthogonal complement of K.
- Lemmas relating the orthogonal projection/reflection on the `submodule.map` of a subspace, with the orthogonal projection/reflection on the original subspace.
- Lemma characterizing the reflection in the trivial subspace.

### [2021-09-08 12:15:54](https://github.com/leanprover-community/mathlib/commit/71df310)
chore(*): remove instance binders in exists, for mathport ([#9083](https://github.com/leanprover-community/mathlib/pull/9083))
Per @digama0's request at https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Instance.20binders.20in.20exists.
Instance binders under an "Exists" aren't allowed in Lean4, so we're backport removing them. I've just turned relevant `[X]` binders into `(_ : X)` binders, and it seems to all still work. (i.e. the instance binders weren't actually doing anything).
It turns out two of the problem binders were in `infi` or `supr`, not `Exists`, but I treated them the same way.

### [2021-09-08 12:15:53](https://github.com/leanprover-community/mathlib/commit/3108153)
feat(linear_algebra/affine_space/independent): homotheties preserve affine independence ([#9070](https://github.com/leanprover-community/mathlib/pull/9070))

### [2021-09-08 12:15:52](https://github.com/leanprover-community/mathlib/commit/e4e07ea)
feat(ring_theory): `map f (span s) = span (f '' s)` ([#9068](https://github.com/leanprover-community/mathlib/pull/9068))
We already had this for submodules and linear maps, here it is for ideals and ring homs.

### [2021-09-08 12:15:50](https://github.com/leanprover-community/mathlib/commit/aae2b37)
feat(field_theory/separable): a finite field extension in char 0 is separable ([#9066](https://github.com/leanprover-community/mathlib/pull/9066))

### [2021-09-08 12:15:49](https://github.com/leanprover-community/mathlib/commit/157e99d)
feat(ring_theory): PIDs are Dedekind domains ([#9063](https://github.com/leanprover-community/mathlib/pull/9063))
We had all the ingredients ready for a while, apparently I just forgot to PR the instance itself.
Co-Authored-By: Ashvni <ashvni.n@gmail.com>
Co-Authored-By: Filippo A. E. Nuccio <filippo.nuccio@univ-st-etienne.fr>

### [2021-09-08 12:15:48](https://github.com/leanprover-community/mathlib/commit/c3f2c23)
feat(analysis/convex/basic): the affine image of the convex hull is the convex hull of the affine image ([#9057](https://github.com/leanprover-community/mathlib/pull/9057))

### [2021-09-08 12:15:46](https://github.com/leanprover-community/mathlib/commit/57a0789)
chore(topology/order): relate Sup and Inf of topologies to `generate_from` ([#9045](https://github.com/leanprover-community/mathlib/pull/9045))
Since there is a Galois insertion between `generate_from : set (set α) → topological_space α` and the "forgetful functor" `topological_space α → set (set α)`, all kinds of lemmas about the interaction of `generate_from` and the ordering on topologies automatically follow.  But it is hard to use the Galois insertion lemmas directly, because the Galois insertion is actually provided for the dual order on topologies, which confuses Lean.  Here we re-state most of the Galois insertion API in this special case.

### [2021-09-08 12:15:45](https://github.com/leanprover-community/mathlib/commit/a8c5c5a)
feat(algebra/module/basic): add `module.to_add_monoid_End` ([#8968](https://github.com/leanprover-community/mathlib/pull/8968))
I also removed `smul_add_hom_one` since it's a special case of the ring_hom.
I figured I'd replace a `simp` with a `rw` when fixing `finsupp.to_free_abelian_group_comp_to_finsupp` for this removal.

### [2021-09-08 10:25:38](https://github.com/leanprover-community/mathlib/commit/4e8d966)
feat(algebra/subalgebra): add missing actions by and on subalgebras ([#9081](https://github.com/leanprover-community/mathlib/pull/9081))
For `S : subalgebra R A`, this adds the instances:
* for actions on subalgebras (generalizing the existing `algebra R S`):
  * `module R' S`
  * `algebra R' S`
  * `is_scalar_tower R' R S`
* for actions by subalgebras (generalizing the existing `algebra S α`):
  * `mul_action S α`
  * `smul_comm_class S α β`
  * `smul_comm_class α S β`
  * `is_scalar_tower S α β`
  * `has_faithful_scalar S α`
  * `distrib_mul_action S α`
  * `module S α`
This also removes the commutativity requirement on `A` for the `no_zero_smul_divisors S A` instance.

### [2021-09-08 10:25:37](https://github.com/leanprover-community/mathlib/commit/585c5ad)
feat(data/finset): monotone maps preserve the maximum of a finset ([#9035](https://github.com/leanprover-community/mathlib/pull/9035))

### [2021-09-08 08:23:11](https://github.com/leanprover-community/mathlib/commit/fc75aea)
feat(topology/algebra/ordered): `{prod,pi}.order_closed_topology` ([#9073](https://github.com/leanprover-community/mathlib/pull/9073))

### [2021-09-08 08:23:10](https://github.com/leanprover-community/mathlib/commit/8341d16)
feat(linear_algebra/finite_dimensional): make finite_dimensional_bot an instance ([#9053](https://github.com/leanprover-community/mathlib/pull/9053))
This was previously made into a local instance in several places, but there appears to be no reason it can't be a global instance.
cf discussion at [#8884](https://github.com/leanprover-community/mathlib/pull/8884).

### [2021-09-08 08:23:08](https://github.com/leanprover-community/mathlib/commit/b4a88e2)
feat(data/equiv/derangements/basic): define derangements ([#7526](https://github.com/leanprover-community/mathlib/pull/7526))
This proves two formulas for the number of derangements on _n_ elements, and defines some combinatorial equivalences
involving derangements on α and derangements on certain subsets of α. This proves Theorem 88 on Freek's list.

### [2021-09-08 06:17:22](https://github.com/leanprover-community/mathlib/commit/189fe5b)
feat(data/nat/enat): refactor coe from nat to enat ([#9023](https://github.com/leanprover-community/mathlib/pull/9023))
The coercion from nat to enat was defined to be enat.some. But another
coercion could be inferred from the additive structure on enat, leading to
confusing goals of the form
`↑n = ↑n` where the two sides were not defeq.
We now make the coercion inferred from the additive structure the default, 
even though it is not computable.
A dedicated function `enat.some` is introduced, to be used whenever
computability is important.

### [2021-09-08 06:17:21](https://github.com/leanprover-community/mathlib/commit/cef862d)
feat(ring_theory/noetherian): is_noetherian_of_range_eq_ker ([#8988](https://github.com/leanprover-community/mathlib/pull/8988))

### [2021-09-08 06:17:20](https://github.com/leanprover-community/mathlib/commit/4dc96e4)
feat(group_theory/index): define the index of a subgroup ([#8971](https://github.com/leanprover-community/mathlib/pull/8971))
Defines `subgroup.index` and proves various divisibility properties.

### [2021-09-08 06:17:19](https://github.com/leanprover-community/mathlib/commit/ded0d64)
feat(number_theory): define "admissible" absolute values ([#8964](https://github.com/leanprover-community/mathlib/pull/8964))
We say an absolute value `abv : absolute_value R ℤ` is admissible if it agrees with the Euclidean domain structure on R (see also `is_euclidean` in [#8949](https://github.com/leanprover-community/mathlib/pull/8949)), and large enough sets of elements in `R^n` contain two elements whose remainders are close together.
Examples include `abs : ℤ → ℤ` and `card_pow_degree := λ (p : polynomial Fq), (q ^ p.degree : ℤ)`, where `Fq` is a finite field with `q` elements. (These two correspond to the number field and function field case respectively, in our proof that the class number of a global field is finite.) Proving these two are indeed admissible involves a lot of pushing values between `ℤ` and `ℝ`, but is otherwise not so exciting.

### [2021-09-08 06:17:18](https://github.com/leanprover-community/mathlib/commit/ec51460)
feat(data/finset): define `finset.pimage` ([#8907](https://github.com/leanprover-community/mathlib/pull/8907))

### [2021-09-08 04:46:13](https://github.com/leanprover-community/mathlib/commit/628969b)
chore(linear_algebra/basic): speed up slow decl ([#9060](https://github.com/leanprover-community/mathlib/pull/9060))

### [2021-09-08 02:22:54](https://github.com/leanprover-community/mathlib/commit/782a20a)
chore(scripts): update nolints.txt ([#9079](https://github.com/leanprover-community/mathlib/pull/9079))
I am happy to remove some nolints for you!

### [2021-09-07 23:04:14](https://github.com/leanprover-community/mathlib/commit/dcd8782)
feat(algebra/algebra): lemmas connecting `basis ι R A`, `no_zero_smul_divisors R A` and `injective (algebra_map R A)` ([#9039](https://github.com/leanprover-community/mathlib/pull/9039))
Additions:
 * `basis.algebra_map_injective`
 * `no_zero_smul_divisors.algebra_map_injective`
 * `no_zero_smul_divisors.iff_algebra_map_injective`
Renamed:
 * `algebra.no_zero_smul_divisors.of_algebra_map_injective` → `no_zero_smul_divisors.of_algebra_map_injective`

### [2021-09-07 21:34:33](https://github.com/leanprover-community/mathlib/commit/50f5d8b)
docs(linear_algebra/bilinear_map): fix inconsistency in docstring ([#9075](https://github.com/leanprover-community/mathlib/pull/9075))

### [2021-09-07 21:34:32](https://github.com/leanprover-community/mathlib/commit/b0b0a24)
feat(data/int): absolute values and integers ([#9028](https://github.com/leanprover-community/mathlib/pull/9028))
We prove that an absolute value maps all `units ℤ` to `1`.
I added a new file since there is no neat place in the import hierarchy where this fit (the meet of `algebra.algebra.basic` and `data.int.cast`).

### [2021-09-07 19:33:39](https://github.com/leanprover-community/mathlib/commit/fd453cf)
chore(data/set/basic): add some simp attrs ([#9074](https://github.com/leanprover-community/mathlib/pull/9074))
Also add `set.pairwise_on_union`.

### [2021-09-07 16:31:29](https://github.com/leanprover-community/mathlib/commit/463e753)
feat(linear_algebra/finite_dimensional): generalisations to division_ring ([#8822](https://github.com/leanprover-community/mathlib/pull/8822))
I generalise a few results about finite dimensional modules from fields to division rings. Mostly this is me trying out @alexjbest's `generalisation_linter`. (review: it works really well, and is very helpful for finding the right home for lemmas, but it is slow).

### [2021-09-07 15:17:24](https://github.com/leanprover-community/mathlib/commit/9c886ff)
chore(ring_theory): typo fix ([#9067](https://github.com/leanprover-community/mathlib/pull/9067))
`principal_idea_ring` -> `principal_ideal_ring`

### [2021-09-07 15:17:23](https://github.com/leanprover-community/mathlib/commit/f8cfed4)
feat(algebra/tropical/basic): define tropical semiring ([#8864](https://github.com/leanprover-community/mathlib/pull/8864))
Just the initial algebraic structures. Follow up PRs will provide these with a topology, prove that tropical polynomials can be interpreted as sums of affine maps, and further towards tropical geometry.

### [2021-09-07 13:48:09](https://github.com/leanprover-community/mathlib/commit/eeb4bb6)
feat(algebra/big_operators): absolute values and big operators  ([#9027](https://github.com/leanprover-community/mathlib/pull/9027))
This PR extends `absolute_value.add_le` and `absolute_value.map_mul` to `finset.sum` and `finset.prod` respectively.

### [2021-09-07 11:06:56](https://github.com/leanprover-community/mathlib/commit/6c8203f)
chore(linear_algebra/bilinear_map): split off new file from linear_algebra/tensor_product ([#9054](https://github.com/leanprover-community/mathlib/pull/9054))
The first part of linear_algebra/tensor_product consisted of some basics on bilinear maps that are not directly related to the construction of the tensor product.
This PR moves them to a new file.

### [2021-09-07 11:06:55](https://github.com/leanprover-community/mathlib/commit/0508c7b)
feat(analysis/specific_limits): add `set.countable.exists_pos_has_sum_le` ([#9052](https://github.com/leanprover-community/mathlib/pull/9052))
Add versions of `pos_sum_of_encodable` for countable sets.

### [2021-09-07 11:06:54](https://github.com/leanprover-community/mathlib/commit/98942ab)
feat(ring_theory): non-zero divisors are not zero ([#9043](https://github.com/leanprover-community/mathlib/pull/9043))
I'm kind of suprised we didn't have this before!

### [2021-09-07 11:06:53](https://github.com/leanprover-community/mathlib/commit/812ff38)
docs(algebra/ordered_ring): add module docstring ([#9030](https://github.com/leanprover-community/mathlib/pull/9030))

### [2021-09-07 11:06:52](https://github.com/leanprover-community/mathlib/commit/a84b538)
feat(algebra/algebra/subalgebra): inclusion map of subalgebras ([#9013](https://github.com/leanprover-community/mathlib/pull/9013))

### [2021-09-07 11:06:51](https://github.com/leanprover-community/mathlib/commit/d69c12e)
feat(ring_theory/ideal/local_ring): residue field is an algebra ([#8991](https://github.com/leanprover-community/mathlib/pull/8991))
Also, the kernel of a surjective map to a field is equal to the unique maximal ideal.

### [2021-09-07 11:06:50](https://github.com/leanprover-community/mathlib/commit/58a8853)
doc(data/list/*): Add missing documentation ([#8867](https://github.com/leanprover-community/mathlib/pull/8867))
Fixing the missing module docstrings in `data/list`, as well as documenting some `def`s and `theorem`s.

### [2021-09-07 11:06:49](https://github.com/leanprover-community/mathlib/commit/d366eb3)
feat(ring_theory/ideal/operations): add some theorems about taking the quotient of a ring by a sum of ideals  ([#8668](https://github.com/leanprover-community/mathlib/pull/8668))
The aim of this section is to prove that if `I, J` are ideals of the ring `R`, then the quotients `R/(I+J)` and `(R/I)/J'`are isomorphic, where `J'` is the image of `J` in `R/I`.

### [2021-09-07 08:01:11](https://github.com/leanprover-community/mathlib/commit/d0c02bc)
feat(order/filter/basic): add `supr_inf_principal` and `tendsto_supr` ([#9051](https://github.com/leanprover-community/mathlib/pull/9051))
Also golf a few proofs

### [2021-09-07 08:01:09](https://github.com/leanprover-community/mathlib/commit/6b0c73a)
chore(analysis/normed_space): add `dist_sum_sum_le` ([#9049](https://github.com/leanprover-community/mathlib/pull/9049))

### [2021-09-07 08:01:08](https://github.com/leanprover-community/mathlib/commit/3fdfc8e)
chore(data/bool): add a few lemmas about inequalities and `band`/`bor` ([#9048](https://github.com/leanprover-community/mathlib/pull/9048))

### [2021-09-07 08:01:07](https://github.com/leanprover-community/mathlib/commit/c4f3707)
chore(scripts): update nolints.txt ([#9047](https://github.com/leanprover-community/mathlib/pull/9047))
I am happy to remove some nolints for you!

### [2021-09-07 05:56:36](https://github.com/leanprover-community/mathlib/commit/77f4ed4)
docs(set_theory/lists): add module docstring and def docstrings ([#8967](https://github.com/leanprover-community/mathlib/pull/8967))

### [2021-09-07 05:56:34](https://github.com/leanprover-community/mathlib/commit/0c19d5f)
feat(topology/uniform_space/basic): add corollary of Lebesgue number lemma `lebesgue_number_of_compact_open` ([#8963](https://github.com/leanprover-community/mathlib/pull/8963))

### [2021-09-07 05:56:33](https://github.com/leanprover-community/mathlib/commit/a7be93b)
feat(data/matrix/hadamard): add the Hadamard product ([#8956](https://github.com/leanprover-community/mathlib/pull/8956))

### [2021-09-07 05:56:32](https://github.com/leanprover-community/mathlib/commit/91824e5)
feat(group_theory/subgroup): Normal Core ([#8940](https://github.com/leanprover-community/mathlib/pull/8940))
Defines normal core, and proves lemmas analogous to those for normal closure.

### [2021-09-07 05:56:31](https://github.com/leanprover-community/mathlib/commit/298f231)
feat(*): trivial lemmas from [#8903](https://github.com/leanprover-community/mathlib/pull/8903) ([#8909](https://github.com/leanprover-community/mathlib/pull/8909))

### [2021-09-07 05:56:30](https://github.com/leanprover-community/mathlib/commit/5b29630)
chore(linear_algebra/tensor_product): remove `@[ext]` tag from `tensor_product.mk_compr₂_inj` ([#8868](https://github.com/leanprover-community/mathlib/pull/8868))
This PR removes the `@[ext]` tag from `tensor_product.mk_compr₂_inj` and readds it locally only where it is needed. This is a workaround for the issue discussed [in this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/odd.20repeated.20type.20class.20search): basically, when `ext` tries to apply this lemma to linear maps, it fails only after a very long typeclass search. While this problem is already present to some extent in current mathlib, it is exacerbated by the [upcoming generalization of linear maps to semilinear maps](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Semilinear.20maps).
In addition to this change, a few individual uses of `ext` have been replaced by a manual application of the relevant ext lemma(s) for performance reasons.
For discoverability, the lemma `tensor_product.mk_compr₂_inj` is renamed to `tensor_product.ext` and the former `tensor_product.ext` to `tensor_product.ext'`.

### [2021-09-07 03:50:01](https://github.com/leanprover-community/mathlib/commit/ceb9da6)
feat(analysis/convex/caratheodory): strengthen Caratheodory's lemma to provide affine independence ([#8892](https://github.com/leanprover-community/mathlib/pull/8892))
The changes here are:
- Use hypothesis `¬ affine_independent ℝ (coe : t → E)` instead of `finrank ℝ E + 1 < t.card`
- Drop no-longer-necessary `[finite_dimensional ℝ E]` assumption
- Do not use a shrinking argument but start by choosing an appropriate subset of minimum cardinality via `min_card_finset_of_mem_convex_hull`
- Provide a single alternative form of Carathéodory's lemma `eq_pos_convex_span_of_mem_convex_hull`
- In the alternate form, define the explicit linear combination using elements parameterised by a new `fintype` rather than on the entire ambient space `E` (we thus avoid the issue of junk values outside of the relevant subset)

### [2021-09-07 03:49:59](https://github.com/leanprover-community/mathlib/commit/5eb1918)
feat(group_theory/perm/concrete_cycle): is_cycle_form_perm ([#8859](https://github.com/leanprover-community/mathlib/pull/8859))

### [2021-09-07 03:49:58](https://github.com/leanprover-community/mathlib/commit/f157b6d)
feat(linear_algebra): introduce notation for `linear_map.comp` and `linear_equiv.trans` ([#8857](https://github.com/leanprover-community/mathlib/pull/8857))
This PR introduces new notation for the composition of linear maps and linear equivalences: `∘ₗ` denotes `linear_map.comp` and `≫ₗ` denotes `linear_equiv.trans`. This will be needed by an upcoming PR generalizing linear maps to semilinear maps (see discussion [here](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Semilinear.20maps)): in some places, we need to help the elaborator a bit by telling it that we are composing plain linear maps/equivs as opposed to semilinear ones. We have not made the change systematically throughout the library, only in places where it is needed in our semilinear maps branch.

### [2021-09-07 03:49:57](https://github.com/leanprover-community/mathlib/commit/d262500)
feat(group_theory/nilpotent): add antimono and functorial lemma for lower central series ([#8853](https://github.com/leanprover-community/mathlib/pull/8853))

### [2021-09-07 03:49:56](https://github.com/leanprover-community/mathlib/commit/f0f6c1c)
feat(tactic/lint): reducible non-instance linter ([#8540](https://github.com/leanprover-community/mathlib/pull/8540))
* This linter checks that if an instances uses a non-instance with as type a class, the non-instances is reducible.
* There are many false positives to this rule, which we probably want to allow (that are unlikely to cause problems). To cut down on the many many false positives, the linter currently only consider classes that have either an `add` or a `mul` field. Maybe we want to also include order-structures, but there are (for example) a bunch of `complete_lattice` structures that are derived using Galois insertions that haven't ever caused problems (I think).

### [2021-09-07 01:49:05](https://github.com/leanprover-community/mathlib/commit/d6a1fc0)
feat(algebra/ordered_monoid): correct definition ([#8877](https://github.com/leanprover-community/mathlib/pull/8877))
Our definition of `ordered_monoid` is not the usual one, and this PR corrects that.
The standard definition just says
```
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
```
while we currently have an extra axiom
```
(lt_of_add_lt_add_left : ∀ a b c : α, a + b < a + c → b < c)
```
(This was introduced in ancient times, https://github.com/leanprover-community/mathlib/commit/7d8e3f3a6de70da504406727dbe7697b2f7a62ee, with no indication of where the definition came from. I couldn't find it in other sources.)
As @urkud pointed out a while ago [on Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered_comm_monoid), these really are different.
The second axiom *does* automatically hold for cancellative ordered monoids, however.
This PR simply drops the axiom. In practice this causes no harm, because all the interesting examples are cancellative. There's a little bit of cleanup to do. In `src/algebra/ordered_sub.lean` four lemmas break, so I just added the necessary `[contravariant_class _ _ (+) (<)]` hypothesis. These lemmas aren't currently used in mathlib, but presumably where they are needed this typeclass will be available.

### [2021-09-07 00:33:29](https://github.com/leanprover-community/mathlib/commit/ce31c1c)
feat(order/prime_ideal): prime ideals are maximal ([#9004](https://github.com/leanprover-community/mathlib/pull/9004))
Proved that in boolean algebras:
1. An ideal is prime iff it always contains one of x, x^c
2. A prime ideal is maximal

### [2021-09-07 00:33:28](https://github.com/leanprover-community/mathlib/commit/5431521)
refactor(topology/sheaves/sheaf_condition): Generalize unique gluing API ([#9002](https://github.com/leanprover-community/mathlib/pull/9002))
Previously, the sheaf condition in terms of unique gluings has been defined only for type-valued presheaves. This PR generalizes this to arbitrary concrete categories, whose forgetful functor preserves limits and reflects isomorphisms (e.g. algebraic categories like `CommRing`). As a side effect, this solves a TODO in `structure_sheaf.lean`.

### [2021-09-07 00:33:27](https://github.com/leanprover-community/mathlib/commit/d472c56)
feat(linear_algebra/affine_space/affine_equiv): affine homotheties as equivalences ([#8983](https://github.com/leanprover-community/mathlib/pull/8983))

### [2021-09-06 21:09:20](https://github.com/leanprover-community/mathlib/commit/309674d)
feat(linear_algebra/basis): a nontrivial module has nonempty bases ([#9040](https://github.com/leanprover-community/mathlib/pull/9040))
A tiny little lemma that guarantees the dimension of a nontrivial module is nonzero. Noticeably simplifies the proof that the dimension of a power basis is positive in this case.

### [2021-09-06 21:09:19](https://github.com/leanprover-community/mathlib/commit/3218c37)
feat(linear_algebra/smodeq): sub_mem, eval ([#8993](https://github.com/leanprover-community/mathlib/pull/8993))

### [2021-09-06 21:09:18](https://github.com/leanprover-community/mathlib/commit/fde1fc2)
feat(*): make more non-instances reducible ([#8941](https://github.com/leanprover-community/mathlib/pull/8941))
* Also add some docstrings to `cau_seq_completion`.
* Related PR: [#7835](https://github.com/leanprover-community/mathlib/pull/7835)

### [2021-09-06 17:52:24](https://github.com/leanprover-community/mathlib/commit/bfcf73f)
feat(data/multiset/basic): Add a result on intersection of multiset with `repeat a n` ([#9038](https://github.com/leanprover-community/mathlib/pull/9038))

### [2021-09-06 17:52:23](https://github.com/leanprover-community/mathlib/commit/3148cfe)
feat(field_theory/algebraic_closure): polynomials in an algebraically closed fields have roots ([#9037](https://github.com/leanprover-community/mathlib/pull/9037))

### [2021-09-06 17:52:21](https://github.com/leanprover-community/mathlib/commit/3a62419)
chore(data/nat/mul_ind): make docgen happy ([#9036](https://github.com/leanprover-community/mathlib/pull/9036))

### [2021-09-06 17:52:20](https://github.com/leanprover-community/mathlib/commit/11284f2)
feat(ring_theory): `y ≠ 0` in a UFD has finitely many divisors ([#9034](https://github.com/leanprover-community/mathlib/pull/9034))
This implies ideals in a Dedekind domain are contained in only finitely many larger ideals.

### [2021-09-06 17:52:19](https://github.com/leanprover-community/mathlib/commit/86dd706)
feat(set/lattice): two lemmas about when sInter is empty ([#9033](https://github.com/leanprover-community/mathlib/pull/9033))
- Added sInter_eq_empty_iff
- Added sInter_nonempty_iff

### [2021-09-06 17:52:18](https://github.com/leanprover-community/mathlib/commit/98cbad7)
chore(set_theory/pgame): add protected ([#9022](https://github.com/leanprover-community/mathlib/pull/9022))
Breaks [#7843](https://github.com/leanprover-community/mathlib/pull/7843) into smaller PRs.
These lemmas about `pgame` conflict with the ones for `game` when used in `calc` mode proofs, which confuses Lean.
There is no way to use the lemmas for `game` (required for surreal numbers) without using `_root_` as `game` inherits these lemmas from its abelian group structure.

### [2021-09-06 17:52:17](https://github.com/leanprover-community/mathlib/commit/c83c22d)
feat(measure_theory/measure/vector_measure): zero is absolutely continuous wrt any vector measure ([#9007](https://github.com/leanprover-community/mathlib/pull/9007))

### [2021-09-06 17:52:16](https://github.com/leanprover-community/mathlib/commit/339c2c3)
feat(linear_algebra/affine_space/independent): affine independence is preserved by affine maps ([#9005](https://github.com/leanprover-community/mathlib/pull/9005))

### [2021-09-06 12:26:04](https://github.com/leanprover-community/mathlib/commit/c2e6e62)
feat(algebra/absolute_value): generalize a few results to `linear_ordered_ring`s ([#9026](https://github.com/leanprover-community/mathlib/pull/9026))
The proofs were copied literally from `is_absolute_value`, which was defined on fields, but we can generalize them to rings with only a few tweaks.

### [2021-09-06 12:26:02](https://github.com/leanprover-community/mathlib/commit/448f821)
feat(algebra/pointwise): enable pointwise add_action ([#9017](https://github.com/leanprover-community/mathlib/pull/9017))
Just a little to_additive declaration

### [2021-09-06 12:26:01](https://github.com/leanprover-community/mathlib/commit/f0c3f9e)
feat(linear_algebra/basic): surjective_of_iterate_surjective ([#9006](https://github.com/leanprover-community/mathlib/pull/9006))

### [2021-09-06 12:26:00](https://github.com/leanprover-community/mathlib/commit/d16cb00)
feat(linear_algebra/basic): of_le_injective ([#8977](https://github.com/leanprover-community/mathlib/pull/8977))

### [2021-09-06 12:25:59](https://github.com/leanprover-community/mathlib/commit/c0f01ee)
feat(data/fin): pos_iff_nonempty ([#8975](https://github.com/leanprover-community/mathlib/pull/8975))

### [2021-09-06 12:25:58](https://github.com/leanprover-community/mathlib/commit/de37a6a)
chore(field_theory/fixed): reuse existing `mul_semiring_action.to_alg_hom`  by providing `smul_comm_class` ([#8965](https://github.com/leanprover-community/mathlib/pull/8965))
This removes `fixed_points.to_alg_hom` as this is really just a bundled form of `mul_semiring_action.to_alg_hom` + `mul_semiring_action.to_alg_hom_injective`, once we provide the missing `smul_comm_class`.

### [2021-09-06 12:25:57](https://github.com/leanprover-community/mathlib/commit/2aebabc)
feat(topology/continuous_function/basic): add `continuous_map.Icc_extend` ([#8952](https://github.com/leanprover-community/mathlib/pull/8952))

### [2021-09-06 12:25:55](https://github.com/leanprover-community/mathlib/commit/773b45f)
feat(algebra/module/ordered): redefine `ordered_module` as `ordered_smul` ([#8930](https://github.com/leanprover-community/mathlib/pull/8930))
One would like to talk about `ordered_monoid R (with_top R)`, but the `module` constraint is too strict to allow this.
The definition of `ordered_monoid` works if it is loosened to `has_scalar R M`. Most of the proofs that are part of its API need at most `smul_with_zero`. So it has been loosened to `smul_with_zero`, since a lawless `ordered_monoid` wouldn't do much.
In the `ordered_field` portion, `module` has been loosened to `mul_action_with_zero`.
`order_dual` instances of `smul` instances have also been generalized to better transmit. There are more generalizations possible, but seem out of scope for a single PR.
Unfortunately, these generalizations exposed a gnarly misalignment between `prod.has_lt` and `prod.has_le`, which have incompatible definitions, when inferred through separate paths. In particular, the `lt` definition of generated by `prod.preorder` is different than the core `prod.has_lt`. Due to this, the `prod.ordered_monoid` instance has not been generalized.

### [2021-09-06 12:25:54](https://github.com/leanprover-community/mathlib/commit/e8fff26)
refactor(group_theory/*): Move Cauchy's theorem ([#8916](https://github.com/leanprover-community/mathlib/pull/8916))
Moves Cauchy's theorem from `sylow.lean` to `perm/cycle_type.lean`. Now `perm/cycle_type.lean` no longer depends on `sylow.lean`, and `p_group.lean` can use Cauchy's theorem (e.g. for equivalent characterizations of p-groups).

### [2021-09-06 12:25:53](https://github.com/leanprover-community/mathlib/commit/893c474)
feat(group_theory/submonoid/membership): add log, exp lemmas ([#8870](https://github.com/leanprover-community/mathlib/pull/8870))
Breaking up a previous PR ([#7843](https://github.com/leanprover-community/mathlib/pull/7843)) into smaller ones.
This PR adds lemmas about injectivity of `pow` and `log` functions under appropriate conditions.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.238870)

### [2021-09-06 12:25:52](https://github.com/leanprover-community/mathlib/commit/74373b8)
feat(algebra/lattice_ordered_group): add basic theory of lattice ordered groups ([#8673](https://github.com/leanprover-community/mathlib/pull/8673))

### [2021-09-06 11:10:12](https://github.com/leanprover-community/mathlib/commit/c563692)
feat(data/polynomial/eval): leval, eval as linear map ([#8999](https://github.com/leanprover-community/mathlib/pull/8999))

### [2021-09-06 05:31:16](https://github.com/leanprover-community/mathlib/commit/1f10390)
lint(tactic/*): break long lines ([#8973](https://github.com/leanprover-community/mathlib/pull/8973))
For code lines, the fix was often simple, just break that damn line.
For strings, you shouldn't break a line inside one as this will be a visible change to the tactic's output. When nothing else can be done, I used the trick of breaking the string into two appended strings. "A B" becomes "A" ++ " B", and that's line-breakable.

### [2021-09-06 03:41:00](https://github.com/leanprover-community/mathlib/commit/1bc59c9)
refactor(*): replace `function.swap` by `swap` ([#8612](https://github.com/leanprover-community/mathlib/pull/8612))
This shortens some statements without decreasing legibility (IMO).

### [2021-09-05 23:31:30](https://github.com/leanprover-community/mathlib/commit/a399728)
feat(group_theory/coset): Interaction between quotient_group.mk and right multiplication by elements of the subgroup ([#8970](https://github.com/leanprover-community/mathlib/pull/8970))
Two helpful lemmas regarding the interaction between `quotient_group.mk` and right multiplication by elements of the subgroup.

### [2021-09-05 22:12:20](https://github.com/leanprover-community/mathlib/commit/0a94b29)
feat(data/nat/choose/vandermonde): Vandermonde's identity for binomial coefficients ([#8992](https://github.com/leanprover-community/mathlib/pull/8992))
I place this identity in a new file because the current proof depends on `polynomial`.

### [2021-09-05 02:26:54](https://github.com/leanprover-community/mathlib/commit/9fc45d8)
chore(scripts): update nolints.txt ([#9014](https://github.com/leanprover-community/mathlib/pull/9014))
I am happy to remove some nolints for you!

### [2021-09-04 20:06:15](https://github.com/leanprover-community/mathlib/commit/2ea1650)
fix(algebra/ordered_monoid): slay with_top monoid diamonds caused by irreducibility ([#8926](https://github.com/leanprover-community/mathlib/pull/8926))
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Diamond.20in.20instances.20on.20.60with_top.20R.60
Instead of copying over from `with_zero`, just work through the definitions directly.

### [2021-09-04 18:18:07](https://github.com/leanprover-community/mathlib/commit/fd0cdae)
feat(linear_algebra/pi): pi_option_equiv_prod ([#9003](https://github.com/leanprover-community/mathlib/pull/9003))

### [2021-09-04 18:18:06](https://github.com/leanprover-community/mathlib/commit/8ff139a)
feat(data/equiv/fin): fin_sum_fin_equiv simp lemmas ([#9001](https://github.com/leanprover-community/mathlib/pull/9001))

### [2021-09-04 18:18:05](https://github.com/leanprover-community/mathlib/commit/7729bb6)
feat(algebra): define "Euclidean" absolute values ([#8949](https://github.com/leanprover-community/mathlib/pull/8949))
We say an absolute value `abv : absolute_value R S` is Euclidean if agrees with the Euclidean domain structure on `R`, namely `abv x < abv y ↔ euclidean_domain.r x y`.
Examples include `abs : ℤ → ℤ` and `λ (p : polynomial Fq), (q ^ p.degree : ℤ)`, where `Fq` is a finite field with `q` elements. (These two correspond to the number field and function field case respectively, in our proof that the class number of a global field is finite.)

### [2021-09-04 18:18:04](https://github.com/leanprover-community/mathlib/commit/28592d9)
feat(set_theory/cardinal): cardinal.to_nat_mul ([#8943](https://github.com/leanprover-community/mathlib/pull/8943))
`cardinal.to_nat` distributes over multiplication.

### [2021-09-04 17:05:08](https://github.com/leanprover-community/mathlib/commit/9df3f0d)
feat(data/nat/prime): nat.prime.eq_pow_iff ([#8917](https://github.com/leanprover-community/mathlib/pull/8917))
If a^k=p then a=p and k=1.

### [2021-09-04 15:15:27](https://github.com/leanprover-community/mathlib/commit/a4df460)
feat(linear_algebra/matrix/symmetric): add a file ([#8955](https://github.com/leanprover-community/mathlib/pull/8955))

### [2021-09-04 13:21:59](https://github.com/leanprover-community/mathlib/commit/18d7b74)
feat(data/nat/choose/dvd): generalize to division rings ([#8997](https://github.com/leanprover-community/mathlib/pull/8997))

### [2021-09-04 11:21:20](https://github.com/leanprover-community/mathlib/commit/4435e90)
feat(ring_theory/ideal/operations): ideal.pow_mem_pow ([#8996](https://github.com/leanprover-community/mathlib/pull/8996))

### [2021-09-04 11:21:19](https://github.com/leanprover-community/mathlib/commit/dcc45b4)
feat(order/prime_ideal, order/boolean_algebra): small lemmas about prime ideals ([#8980](https://github.com/leanprover-community/mathlib/pull/8980))
- Added is_prime.mem_or_compl_mem 
- Added is_prime.mem_compl_of_not_mem 
- Added sup_inf_inf_compl

### [2021-09-04 10:04:21](https://github.com/leanprover-community/mathlib/commit/7f7f3d9)
feat(ring_theory/ideal/operations): ring_hom.ker_is_maximal_of_surjective ([#8990](https://github.com/leanprover-community/mathlib/pull/8990))

### [2021-09-04 08:16:53](https://github.com/leanprover-community/mathlib/commit/9d86dad)
feat(linear_algebra/prod): lemmas about ker and range ([#8989](https://github.com/leanprover-community/mathlib/pull/8989))

### [2021-09-04 08:16:52](https://github.com/leanprover-community/mathlib/commit/855613e)
feat(linear_algebra/basic): galois insertion lemmas for map and comap ([#8978](https://github.com/leanprover-community/mathlib/pull/8978))

### [2021-09-04 06:46:17](https://github.com/leanprover-community/mathlib/commit/b57af8a)
feat(category_theory/basic/category): Combine and improve API on preorder categories. ([#8982](https://github.com/leanprover-community/mathlib/pull/8982))
Material on preorders as categories was previously scattered throughout the library. This PR unites this material into a single file `category_theory/category/preorder` and also expands upon it, by relating adjoints to galois connections.

### [2021-09-04 02:26:04](https://github.com/leanprover-community/mathlib/commit/b9d8081)
chore(scripts): update nolints.txt ([#8987](https://github.com/leanprover-community/mathlib/pull/8987))
I am happy to remove some nolints for you!

### [2021-09-04 00:27:12](https://github.com/leanprover-community/mathlib/commit/464c3d7)
chore(group_theory/group_action/defs): weaken assumptions of `mul_smul_comm` and `smul_mul_assoc` ([#8972](https://github.com/leanprover-community/mathlib/pull/8972))

### [2021-09-04 00:27:11](https://github.com/leanprover-community/mathlib/commit/6ab6695)
docs(topology/algebra/floor_ring): add module docstring ([#8969](https://github.com/leanprover-community/mathlib/pull/8969))

### [2021-09-03 22:57:17](https://github.com/leanprover-community/mathlib/commit/66cb5e0)
fix(data/setoid/partition): make def more readable ([#8951](https://github.com/leanprover-community/mathlib/pull/8951))
If we change the statement of `partition.order_iso` from `setoid α ≃o subtype (@is_partition α)` to `setoid α ≃o {C : set (set α) // is_partition C}` then this doesn't change anything up to defeq and it's much easier for a beginner to read, as well as avoiding the `@`. I also change some variable names. Why? I want to show this part of this file to undergraduates and I want to make it look as easy and nice as possible.

### [2021-09-03 22:57:16](https://github.com/leanprover-community/mathlib/commit/93a15d6)
feat(ring_theory/subring): field structure on centers of a division_ring ([#8472](https://github.com/leanprover-community/mathlib/pull/8472))
I've also tidied up the subtitles. Previously there was a mix of h1 and h3s, I've made them all h2s.

### [2021-09-03 20:53:49](https://github.com/leanprover-community/mathlib/commit/3a0dddc)
feat(algebra/order_functions): (min|max)_eq_iff ([#8911](https://github.com/leanprover-community/mathlib/pull/8911))

### [2021-09-03 20:53:48](https://github.com/leanprover-community/mathlib/commit/39cea43)
docs(data/subtype): add module docstring ([#8900](https://github.com/leanprover-community/mathlib/pull/8900))

### [2021-09-03 18:48:25](https://github.com/leanprover-community/mathlib/commit/710a76e)
chore(algebra/divisibility): help dot notation on `dvd` ([#8766](https://github.com/leanprover-community/mathlib/pull/8766))
Add aliases
* `dvd_mul_of_dvd_left` -> `has_dvd.dvd.mul_right`
* `dvd_mul_of_dvd_right` -> `has_dvd.dvd.mul_left`
Add, to help with a few proofs,
* `dvd_rfl`
* `dvd_pow_self`
Use `has_dvd.dvd.trans` more largely.

### [2021-09-03 09:56:24](https://github.com/leanprover-community/mathlib/commit/5e27f50)
feat(analysis/complex/basic): convex_on.sup ([#8958](https://github.com/leanprover-community/mathlib/pull/8958))

### [2021-09-02 21:50:49](https://github.com/leanprover-community/mathlib/commit/fdc24f5)
feat(algebra/ordered_ring): `linear_ordered_semiring` extends `linear_ordered_add_comm_monoid` ([#8961](https://github.com/leanprover-community/mathlib/pull/8961))

### [2021-09-02 19:07:49](https://github.com/leanprover-community/mathlib/commit/d821860)
feat(group_theory/group_action/basic): class formula, Burnside's lemma ([#8801](https://github.com/leanprover-community/mathlib/pull/8801))
This adds class formula and Burnside's lemma for group action, both as an equiv and using cardinals.
I also added a cardinal version of the Orbit-stabilizer theorem.

### [2021-09-02 15:21:36](https://github.com/leanprover-community/mathlib/commit/17747c0)
feat(number_theory): define number fields, function fields and their rings of integers ([#8701](https://github.com/leanprover-community/mathlib/pull/8701))
Co-Authored-By: Ashvni <ashvni.n@gmail.com>

### [2021-09-02 14:35:26](https://github.com/leanprover-community/mathlib/commit/88525a9)
feat(ring_theory/ideal): generalize from `integral_closure` to `is_integral_closure` ([#8944](https://github.com/leanprover-community/mathlib/pull/8944))
This PR restates a couple of lemmas about ideals the integral closure to use an instance of `is_integral_closure` instead. The originals are still available, but their proofs are now oneliners shelling out to `is_integral_closure`.

### [2021-09-02 12:25:11](https://github.com/leanprover-community/mathlib/commit/55a7d38)
feat(group_theory/coset): rw lemmas involving quotient_group.mk ([#8957](https://github.com/leanprover-community/mathlib/pull/8957))
When doing computations with quotient groups, I found these lemmas to be helpful when rewriting.

### [2021-09-02 12:25:09](https://github.com/leanprover-community/mathlib/commit/baefdf3)
fix(group_theory/group_action/defs): deduplicate `const_smul_hom` and `distrib_mul_action.to_add_monoid_hom` ([#8953](https://github.com/leanprover-community/mathlib/pull/8953))
This removes `const_smul_hom` as `distrib_mul_action.to_add_monoid_hom` fits a larger family of similarly-named definitions.
This also renames `distrib_mul_action.hom_add_monoid_hom` to `distrib_mul_action.to_add_monoid_End` to better match its statement.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Definition.20elimination.20contest/near/237347199)

### [2021-09-02 10:34:12](https://github.com/leanprover-community/mathlib/commit/1dddd7f)
feat(algebra/group/hom_instance): additive endomorphisms form a ring ([#8954](https://github.com/leanprover-community/mathlib/pull/8954))
We already have all the data to state this, this just provides the extra proofs.
The multiplicative version is nasty because `monoid.End` has two different multiplicative structures depending on whether `End` is unfolded; so this PR leaves that until someone actually needs it.
With this in place we can provide `module.to_add_monoid_End : R →+* add_monoid.End M` in a future PR.

### [2021-09-02 09:31:58](https://github.com/leanprover-community/mathlib/commit/2fa8251)
refactor(*): rename {topological,smooth}_semiring to {topological,smooth}_ring ([#8902](https://github.com/leanprover-community/mathlib/pull/8902))
A topological semiring that is a ring, is a topological ring.
A smooth semiring that is a ring, is a smooth ring.
This PR renames:
* `topological_semiring` -> `topological_ring`
* `smooth_semiring` -> `smooth_ring`
It drops the existing `topological_ring` and `smooth_ring`.

### [2021-09-02 08:19:17](https://github.com/leanprover-community/mathlib/commit/289e6dc)
feat(category_theory/limits/kan_extension): Prove (co)reflectivity for Kan extensions ([#8962](https://github.com/leanprover-community/mathlib/pull/8962))

### [2021-09-02 08:19:16](https://github.com/leanprover-community/mathlib/commit/8da6699)
chore(analysis/convex/basic): generalize `concave_on.le_on_segment` to monoids ([#8959](https://github.com/leanprover-community/mathlib/pull/8959))
This matches the generalization already present on `convex_on.le_on_segment`.

### [2021-09-02 08:19:14](https://github.com/leanprover-community/mathlib/commit/9d3e3e8)
feat(ring_theory/dedekind_domain): the integral closure of a DD is a DD ([#8847](https://github.com/leanprover-community/mathlib/pull/8847))
Let `L` be a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain. Then any `is_integral_closure C A L` is also a Dedekind domain, in particular for `C := integral_closure A L`.
In combination with the definitions of [#8701](https://github.com/leanprover-community/mathlib/pull/8701), we can conclude that rings of integers are Dedekind domains.

### [2021-09-02 06:16:19](https://github.com/leanprover-community/mathlib/commit/6c24731)
feat(order/bounded_lattice): `ne_(bot|top)_iff_exists` ([#8960](https://github.com/leanprover-community/mathlib/pull/8960))
Like `ne_zero_iff_exists`

### [2021-09-01 19:25:02](https://github.com/leanprover-community/mathlib/commit/07c57b5)
feat(group_theory): Add `monoid_hom.mker` and generalise the codomain for `monoid_hom.ker` ([#8532](https://github.com/leanprover-community/mathlib/pull/8532))
Add `monoid_hom.mker` for `f : M ->* N`, where `M` and `N` are `mul_one_class`es, and `monoid_hom.ker` is now defined for `f : G ->* H`, where `H` is a `mul_one_class`

### [2021-09-01 17:19:33](https://github.com/leanprover-community/mathlib/commit/0b8a858)
feat(tactic/lint): minor linter improvements ([#8934](https://github.com/leanprover-community/mathlib/pull/8934))
* Change `#print foo` with `#check @foo` in the output of the linter
* Include the number of linters in the output message
* add `attribute [nolint syn_taut] rfl`

### [2021-09-01 15:38:10](https://github.com/leanprover-community/mathlib/commit/9b00046)
chore(algebra,group_theory,right_theory,linear_algebra): add missing lemmas ([#8948](https://github.com/leanprover-community/mathlib/pull/8948))
This adds:
* `sub{group,ring,semiring}.map_id`
* `submodule.add_mem_sup`
* `submodule.map_add_le`
And moves `submodule.sum_mem_supr` and `submodule.sum_mem_bsupr` to an earlier file.

### [2021-09-01 14:07:44](https://github.com/leanprover-community/mathlib/commit/2beaa28)
fix(category_theory/adjunction/basic): Fix typo in docstring ([#8950](https://github.com/leanprover-community/mathlib/pull/8950))

### [2021-09-01 14:07:42](https://github.com/leanprover-community/mathlib/commit/510e65d)
feat(topology/algebra/localization): add topological localization ([#8894](https://github.com/leanprover-community/mathlib/pull/8894))
We show that ring topologies on a ring `R` form a complete lattice.
We use this to define the topological localization of a topological commutative ring `R` at a submonoid `M`.

### [2021-09-01 12:16:34](https://github.com/leanprover-community/mathlib/commit/d472e1b)
feat(order/basic): recursor for order_dual ([#8938](https://github.com/leanprover-community/mathlib/pull/8938))

### [2021-09-01 12:16:33](https://github.com/leanprover-community/mathlib/commit/0970d07)
feat(order/well_founded): define `function.argmin`, `function.argmin_on` ([#8895](https://github.com/leanprover-community/mathlib/pull/8895))
Evidently, these are just thin wrappers around `well_founded.min` but I think
this use case is common enough to deserve this specialisation.

### [2021-09-01 12:16:32](https://github.com/leanprover-community/mathlib/commit/faf5e5c)
feat(order/bounded_lattice): unbot and untop ([#8885](https://github.com/leanprover-community/mathlib/pull/8885))
`unbot` sends non-`⊥` elements of `with_bot α` to the corresponding element of `α`. `untop` does the analogous thing for `with_top`.

### [2021-09-01 10:35:59](https://github.com/leanprover-community/mathlib/commit/f3101e8)
feat(group_theory/perm/basic): permutations of a subtype ([#8691](https://github.com/leanprover-community/mathlib/pull/8691))
This is the same as `(equiv.refl _)^.set.compl .symm.trans (subtype_equiv_right $ by simp)` (up to a `compl`) but with better unfolding.

### [2021-09-01 07:45:41](https://github.com/leanprover-community/mathlib/commit/73f50ac)
feat(algebraic_geometry): Redefine Schemes in terms of isos of locally ringed spaces ([#8888](https://github.com/leanprover-community/mathlib/pull/8888))
Addresses the project mentioned in `Scheme.lean` to redefine Schemes in terms of isomorphisms of locally ringed spaces, instead of presheafed spaces.

### [2021-09-01 07:45:39](https://github.com/leanprover-community/mathlib/commit/5b04a89)
feat(measure_theory/conditional_expectation): the integral of the norm of the conditional expectation is lower  ([#8318](https://github.com/leanprover-community/mathlib/pull/8318))
Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable function, such that their integrals coincide on `m`-measurable sets with finite measure. Then `∫ x in s, ∥g x∥ ∂μ ≤ ∫ x in s, ∥f x∥ ∂μ` on all `m`-measurable sets with finite measure.
This PR also defines a notation `measurable[m] f`, to mean that `f : α → β` is measurable with respect to the `measurable_space` `m` on `α`.

### [2021-09-01 05:57:01](https://github.com/leanprover-community/mathlib/commit/f0451d8)
feat(algebra/group/defs): ext lemmas for (semi)groups and monoids ([#8391](https://github.com/leanprover-community/mathlib/pull/8391))
[Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.236476.20boolean_algebra.2Eto_boolean_ring/near/242118386)