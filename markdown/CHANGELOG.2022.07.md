### [2022-07-08 14:49:24](https://github.com/leanprover-community/mathlib/commit/5a5d290)
fix(data/fintype/basic): move card_subtype_mono into the fintype namespace ([#15185](https://github.com/leanprover-community/mathlib/pull/15185))

### [2022-07-08 13:36:19](https://github.com/leanprover-community/mathlib/commit/1937dff)
feat(analysis/normed_space/lp_space): normed_algebra structure ([#15086](https://github.com/leanprover-community/mathlib/pull/15086))
This also golfs the `normed_ring` instance to go via `subring.to_ring`, as this saves us from having to build the power, nat_cast, and int_cast structures manually.
We also rename `lp.lp_submodule` to `lp_submodule` to avoid unhelpful repetition.

### [2022-07-08 11:29:27](https://github.com/leanprover-community/mathlib/commit/e74e534)
doc(tactic/wlog): use markdown lists rather than indentation ([#15113](https://github.com/leanprover-community/mathlib/pull/15113))
The indentation used in this docstring was lost in the web docs.

### [2022-07-08 11:29:26](https://github.com/leanprover-community/mathlib/commit/0bc51f0)
feat(topology/metric_space/hausdorff_distance): Thickening a compact inside an open ([#14926](https://github.com/leanprover-community/mathlib/pull/14926))
If a compact set is contained in an open set, then we can find a (closed) thickening of it still contained in the open.

### [2022-07-08 11:29:25](https://github.com/leanprover-community/mathlib/commit/93be74b)
feat(combinatorics/simple_graph/prod): Box product ([#14867](https://github.com/leanprover-community/mathlib/pull/14867))
Define `simple_graph.box_prod`, the box product of simple graphs. Show that it's commutative and associative, and prove its connectivity properties.

### [2022-07-08 09:53:26](https://github.com/leanprover-community/mathlib/commit/7c070c4)
feat(data/finset/basic): Coercion of a product of finsets ([#15011](https://github.com/leanprover-community/mathlib/pull/15011))
`↑(∏ i in s, f i) : set α) = ∏ i in s, ↑(f i)` for `f : ι → finset α`.

### [2022-07-08 05:24:53](https://github.com/leanprover-community/mathlib/commit/d34b330)
feat(data/set/basic,order/filter/basic): add semiconj lemmas about images and maps ([#14970](https://github.com/leanprover-community/mathlib/pull/14970))
This adds `function.commute` and `function.semiconj` lemmas, and replaces all the uses of `_comm` lemmas with the `semiconj` version as it turns out that only this generality is needed.

### [2022-07-08 05:24:52](https://github.com/leanprover-community/mathlib/commit/563a51a)
chore(topology/algebra/semigroup): golf file ([#14957](https://github.com/leanprover-community/mathlib/pull/14957))

### [2022-07-08 05:24:52](https://github.com/leanprover-community/mathlib/commit/ba9f346)
feat(topology/algebra/uniform_group): `uniform_group` is preserved by Inf and comap ([#14889](https://github.com/leanprover-community/mathlib/pull/14889))
This is the uniform version of [#11720](https://github.com/leanprover-community/mathlib/pull/11720)

### [2022-07-08 02:55:33](https://github.com/leanprover-community/mathlib/commit/6eeb941)
refactor(set_theory/cardinal/basic): migrate from `fintype` to `finite` ([#15175](https://github.com/leanprover-community/mathlib/pull/15175))
* add `finite_iff_exists_equiv_fin`;
* add `cardinal.mk_eq_nat_iff` and `cardinal.lt_aleph_0_iff_finite`;
* rename the old `cardinal.lt_aleph_0_iff_finite` to `cardinal.lt_aleph_0_iff_finite_set`;
* rename `cardinal.lt_aleph_0_of_fintype` to `cardinal.lt_aleph_0_of_finite`, assume `[finite]` instead of `[fintype]`;
* add an alias `set.finite.lt_aleph_0`;
* rename `W_type.cardinal_mk_le_max_aleph_0_of_fintype` to `W_type.cardinal_mk_le_max_aleph_0_of_finite`, fix assumption.

### [2022-07-08 02:55:32](https://github.com/leanprover-community/mathlib/commit/a3c647b)
feat(set_theory/ordinal/arithmetic): tweak theorems about `0` and `1` ([#15174](https://github.com/leanprover-community/mathlib/pull/15174))
We add a few basic theorems on the `0` and `1` ordinals. We rename `one_eq_type_unit` to `type_unit`, and remove `one_eq_lift_type_unit` by virtue of being a trivial consequence of `type_unit` and `lift_one`.

### [2022-07-08 02:55:31](https://github.com/leanprover-community/mathlib/commit/f0f4070)
feat(topology/algebra/infinite_sum): Double sum is equal to a single value ([#15157](https://github.com/leanprover-community/mathlib/pull/15157))
A generalized version of `tsum_eq_single` that works for a double indexed sum, when all but one summand is zero.

### [2022-07-08 02:55:30](https://github.com/leanprover-community/mathlib/commit/8927a02)
chore(tactic/lift): move a proof to `subtype.exists_pi_extension` ([#15098](https://github.com/leanprover-community/mathlib/pull/15098))
* Move `_can_lift` attr to the bottom of the file, just before the
  rest of meta code.
* Use `ι → Sort*` instead of `Π i : ι, Sort*`.
* Move `pi_subtype.can_lift.prf` to a separate lemma.

### [2022-07-08 02:55:29](https://github.com/leanprover-community/mathlib/commit/0e3184f)
feat(data/fin/tuple/basic): add lemmas for rewriting exists and forall over `n+1`-tuples ([#15048](https://github.com/leanprover-community/mathlib/pull/15048))
The lemma names `fin.forall_fin_succ_pi` and `fin.exists_fin_succ_pi` mirror the existing `fin.forall_fin_succ` and `fin.exists_fin_succ`.

### [2022-07-08 02:55:28](https://github.com/leanprover-community/mathlib/commit/2a7ceb0)
perf(linear_algebra): speed up `graded_algebra` instances ([#14967](https://github.com/leanprover-community/mathlib/pull/14967))
Reduce `elaboration of graded_algebra` in:
+ `exterior_algebra.graded_algebra` from ~20s to 3s-
+ `tensor_algebra.graded_algebra` from 7s+ to 2s-
+ `clifford_algebra.graded_algebra` from 14s+ to 4s-
(These numbers were before `lift_ι` and `lift_ι_eq` were extracted from `exterior_algebra.graded_algebra` and `lift_ι_eq` was extracted from `clifford_algebra.graded_algebra` in [#12182](https://github.com/leanprover-community/mathlib/pull/12182).)
Fix [timeout reported on Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/deterministic.20timeout/near/286996731)
Also shorten the statements of the first two without reducing clarity (I think).

### [2022-07-08 02:55:27](https://github.com/leanprover-community/mathlib/commit/a5a6865)
feat(combinatorics/set_family/intersecting): Intersecting families ([#14475](https://github.com/leanprover-community/mathlib/pull/14475))
Define intersecting families, prove that intersecting families in `α` have size at most `card α / 2` and that all maximal intersecting families are this size.

### [2022-07-08 02:55:26](https://github.com/leanprover-community/mathlib/commit/70a2708)
feat(topology/continuous_function): Any T0 space embeds in a product of copies of the Sierpinski space ([#14036](https://github.com/leanprover-community/mathlib/pull/14036))
Any T0 space embeds in a product of copies of the Sierpinski space

### [2022-07-08 00:21:19](https://github.com/leanprover-community/mathlib/commit/646028a)
refactor(data/finset/lattice): finset.{min,max} away from option ([#15163](https://github.com/leanprover-community/mathlib/pull/15163))
Switch to a `with_top`/`with_bot` based API. This avoids exposing `option`
as implementation detail.
Redefines `polynomial.degree` to use `coe` instead of `some`

### [2022-07-07 22:47:30](https://github.com/leanprover-community/mathlib/commit/8a80759)
feat(order/filter/basic): add `map_le_map` and `map_injective` ([#15128](https://github.com/leanprover-community/mathlib/pull/15128))
* Add `filter.map_le_map`, an `iff` version of `filter.map_mono`.
* Add `filter.map_injective`, a `function.injective` version of `filter.map_inj`.

### [2022-07-07 19:22:46](https://github.com/leanprover-community/mathlib/commit/b4979cb)
chore(data/rat): split `field ℚ` instance from definition of `ℚ` ([#14893](https://github.com/leanprover-community/mathlib/pull/14893))
I want to refer to the rational numbers in the definition of a field, meaning we can't define the field structure on `ℚ` in the same file as `ℚ` itself.
This PR moves everything in `data/rat/basic.lean` that does not depend on `algebra/field/basic.lean` into a new file `data/rat/defs.lean`: definition of the type `ℚ`, the operations giving its algebraic structure, and the coercions from integers and natural numbers. Basically, everything except the actual `field ℚ` instance.
It turns out our basic lemmas on rational numbers only require a `comm_ring`, `comm_group_with_zero` and `is_domain` instance, so I defined those instances in `defs.lean` could leave all lemmas intact.
As a consequence, the transitive imports provided by `data.rat.basic` are somewhat smaller: no `linear_ordered_field` is needed until `data.rat.order`. I see this as a bonus but can also re-import `algebra.order.field` in `data.rat.basic` if desired.

### [2022-07-07 16:57:16](https://github.com/leanprover-community/mathlib/commit/7428bd9)
refactor(data/finite/set,data/set/finite): move most contents of one file to another ([#15166](https://github.com/leanprover-community/mathlib/pull/15166))
* move most content of `data.finite.set` to `data.set.finite`;
* use `casesI nonempty_fintype _` instead of `letI := fintype.of_finite`; sometimes it lets us avoid `classical.choice`;
* merge `set.finite.of_fintype`, `set.finite_of_fintype`, and `set.finite_of_finite` into `set.to_finite`;
* rewrite `set.finite_univ_iff` and `finite.of_finite_univ` in terms of `set.finite`;
* replace some assumptions `[fintype (plift _)]` with `[finite _]`;
* generalize `set.cod_restrict` and some lemmas to allow domain in `Sort*`, use it for `finite.of_injective_finite.range`.

### [2022-07-07 16:57:15](https://github.com/leanprover-community/mathlib/commit/691f04f)
feat(order/rel_iso): two reflexive/irreflexive relations on a unique type are isomorphic ([#14760](https://github.com/leanprover-community/mathlib/pull/14760))
We also rename `not_rel` to the more descriptive name `not_rel_of_subsingleton`.

### [2022-07-07 14:49:11](https://github.com/leanprover-community/mathlib/commit/6df59d6)
feat(data/list/basic): nth_le_enum ([#15139](https://github.com/leanprover-community/mathlib/pull/15139))
Fill out some of the `enum` and `enum_from` API
Link the two via `map_fst_add_enum_eq_enum_from`.

### [2022-07-07 13:45:33](https://github.com/leanprover-community/mathlib/commit/5852568)
feat(combinatorics/simple_graph/{basic,subgraph,clique,coloring}): add induced graphs, characterization of cliques, and bounds for colorings ([#14034](https://github.com/leanprover-community/mathlib/pull/14034))
This adds `simple_graph.map`, `simple_graph.comap`, and induced graphs and subgraphs. There are renamings: `simple_graph.subgraph.map` to `simple_graph.subgraph.inclusion`, `simple_graph.subgraph.map_top` to `simple_graph.subgraph.hom`, and `simple_graph.subgraph.map_spanning_top` to `simple_graph.subgraph.spanning_hom`. These changes originated to be able to express that a clique is a set of vertices whose induced subgraph is complete, which gives some clique-based bounds for chromatic numbers.

### [2022-07-07 08:40:00](https://github.com/leanprover-community/mathlib/commit/1422d38)
feat(order/succ_pred): expand API on `with_bot` and `with_top` ([#15016](https://github.com/leanprover-community/mathlib/pull/15016))
We add a bunch of `simp` lemmas for successor and predecessors on `with_bot` and `with_top`, and golf some proofs.

### [2022-07-07 06:45:03](https://github.com/leanprover-community/mathlib/commit/0d18630)
chore(ring_theory/norm): generalise a couple of lemmas ([#15160](https://github.com/leanprover-community/mathlib/pull/15160))
Using the generalisation linter

### [2022-07-07 05:04:33](https://github.com/leanprover-community/mathlib/commit/bf735cd)
chore(set_theory/ordinal/basic): remove `rel_iso_out` ([#15145](https://github.com/leanprover-community/mathlib/pull/15145))
This is just a specific application of `rel_iso.cast`. Moreover, it's unused.

### [2022-07-07 05:04:32](https://github.com/leanprover-community/mathlib/commit/9b2755b)
chore(*): add missing `to_fun → apply` configurations for `simps` ([#15112](https://github.com/leanprover-community/mathlib/pull/15112))
This improves the names of some generated lemmas for `continuous_map` and `quadratic_form`.

### [2022-07-07 05:04:31](https://github.com/leanprover-community/mathlib/commit/ab99fd1)
chore(data/nat): rename oddly named lemma odd_gt_zero ([#13040](https://github.com/leanprover-community/mathlib/pull/13040))

### [2022-07-07 02:38:11](https://github.com/leanprover-community/mathlib/commit/6d02dac)
feat(order/lattice, order/lattice_intervals): coe inf/sup lemmas ([#15136](https://github.com/leanprover-community/mathlib/pull/15136))
This PR adds simp lemmas for coercions of inf/sup in order instances on intervals. We also change the order of some arguments in instances/lemmas, by removing `variables` commands, so that typeclass arguments precede others.

### [2022-07-07 00:12:50](https://github.com/leanprover-community/mathlib/commit/418373e)
feat(combinatorics/simple_graph/basic): `dart.to_prod` is injective ([#15150](https://github.com/leanprover-community/mathlib/pull/15150))

### [2022-07-07 00:12:49](https://github.com/leanprover-community/mathlib/commit/3e52000)
feat(data/quot): `is_equiv` instance for quotient equivalence ([#15148](https://github.com/leanprover-community/mathlib/pull/15148))

### [2022-07-07 00:12:47](https://github.com/leanprover-community/mathlib/commit/e034eb0)
feat(order/rel_iso): add `rel_iso.cast` ([#15144](https://github.com/leanprover-community/mathlib/pull/15144))

### [2022-07-07 00:12:46](https://github.com/leanprover-community/mathlib/commit/e335a41)
refactor(group_theory/congruence): use `quotient.map` ([#15130](https://github.com/leanprover-community/mathlib/pull/15130))
Also add explicit universe levels in `algebra.category.Module.monoidal`.

### [2022-07-07 00:12:45](https://github.com/leanprover-community/mathlib/commit/fdfc222)
feat(measure_theory/integral): Circle integral transform ([#13885](https://github.com/leanprover-community/mathlib/pull/13885))
Some basic definitions and results related to circle integrals of a function. These form part of [#13500](https://github.com/leanprover-community/mathlib/pull/13500)

### [2022-07-06 21:58:37](https://github.com/leanprover-community/mathlib/commit/0a89f18)
chore(set_theory/ordinal/basic): clean up `ordinal.card` API ([#15147](https://github.com/leanprover-community/mathlib/pull/15147))
We tweak some spacing throughout this section of the file, and golf a few theorems/definitions.
Conflicts and is inspired by [#15137](https://github.com/leanprover-community/mathlib/pull/15137).

### [2022-07-06 21:58:36](https://github.com/leanprover-community/mathlib/commit/a54e63d)
feat(set_theory/ordinal/basic): basic lemmas on `ordinal.lift`  ([#15146](https://github.com/leanprover-community/mathlib/pull/15146))
We add some missing instances for preimages, and missing theorems for `ordinal.lift`. We remove `ordinal.lift_type`, as it was just a worse way of stating `ordinal.type_ulift`.
We also tweak some spacing and golf a few theorems.
This conflicts with (and is inspired by) some of the changes of [#15137](https://github.com/leanprover-community/mathlib/pull/15137).

### [2022-07-06 19:18:30](https://github.com/leanprover-community/mathlib/commit/b758104)
feat(order/basic): a symmetric relation implies equality when it implies less-equal ([#15149](https://github.com/leanprover-community/mathlib/pull/15149))

### [2022-07-06 15:08:32](https://github.com/leanprover-community/mathlib/commit/d45a8ac)
refactor(topology/separation): redefine `t0_space` ([#15046](https://github.com/leanprover-community/mathlib/pull/15046))

### [2022-07-06 13:12:54](https://github.com/leanprover-community/mathlib/commit/71b1be6)
feat(analysis/inner_product_space): add simple lemmas for the orthogonal complement ([#15020](https://github.com/leanprover-community/mathlib/pull/15020))
We show that the orthogonal complement of a dense subspace is trivial.

### [2022-07-06 11:16:59](https://github.com/leanprover-community/mathlib/commit/f09322b)
feat(geometry/manifold/local_invariant_properties): simplify definitions and proofs ([#15116](https://github.com/leanprover-community/mathlib/pull/15116))
* Simplify the sets in `local_invariant_prop` and `lift_prop_within_at`
* Simplify many proofs in `local_invariant_properties.lean`
* Reorder the intersection in `cont_diff_within_at_prop` to be more consistent with all lemmas in `smooth_manifold_with_corners.lean`
* New lemmas, such as `cont_mdiff_within_at_iff_of_mem_source` and properties of `local_invariant_prop`
* I expect that some lemmas in `cont_mdiff.lean` can be simplified using the new definitions, but I don't do that in this PR.
* Lemma renamings:
```
cont_mdiff_within_at_iff -> cont_mdiff_within_at_iff'
cont_mdiff_within_at_iff' -> cont_mdiff_within_at_iff_of_mem_source'
cont_mdiff_within_at_iff'' -> cont_mdiff_within_at_iff [or iff.rfl]
```

### [2022-07-06 08:41:41](https://github.com/leanprover-community/mathlib/commit/8ff5e11)
feat(analysis/special_functions/complex/arg): add complex.abs_eq_one_iff ([#15125](https://github.com/leanprover-community/mathlib/pull/15125))
This is a simpler formulation of `complex.range_exp_mul_I` below.

### [2022-07-06 08:41:40](https://github.com/leanprover-community/mathlib/commit/d908bc0)
chore(data/fintype): drop a `decidable_pred` assumption ([#14971](https://github.com/leanprover-community/mathlib/pull/14971))
OTOH, now the proof depends on `classical.choice`.

### [2022-07-06 07:46:32](https://github.com/leanprover-community/mathlib/commit/a95b442)
feat(probability/martingale): Doob's maximal inequality ([#14737](https://github.com/leanprover-community/mathlib/pull/14737))

### [2022-07-06 07:04:08](https://github.com/leanprover-community/mathlib/commit/bd9c307)
doc(overview): add probability theory ([#15114](https://github.com/leanprover-community/mathlib/pull/15114))
Also:
* Add convolutions to overview and undergrad
* Add some other probability notions to undergrad
* Minor cleanup in probability module docs

### [2022-07-06 02:26:24](https://github.com/leanprover-community/mathlib/commit/93e97d1)
feat(analysis/convex/function): Variants of `convex_on.le_right_of_left_le` ([#14821](https://github.com/leanprover-community/mathlib/pull/14821))
This PR adds four variants of `convex_on.le_right_of_left_le` that are useful when dealing with convex functions on the real numbers.

### [2022-07-05 23:18:42](https://github.com/leanprover-community/mathlib/commit/71e11de)
chore(analysis/normed/field/basic): add `@[simp]` to `real.norm_eq_abs ([#15006](https://github.com/leanprover-community/mathlib/pull/15006))
* mark `real.norm_eq_abs` and `abs_nonneg` as `simp` lemmas;
* add `abs` versions of `is_o.norm_left` etc;
* add `inner_product_geometry.angle_smul_smul` and `linear_isometry.angle_map`.

### [2022-07-05 23:18:41](https://github.com/leanprover-community/mathlib/commit/071dc90)
feat(probability/martingale): positive part of a submartingale is also a submartingale ([#14932](https://github.com/leanprover-community/mathlib/pull/14932))

### [2022-07-05 19:14:55](https://github.com/leanprover-community/mathlib/commit/f10d0ab)
feat(*): add lemmas about sigma types ([#15085](https://github.com/leanprover-community/mathlib/pull/15085))
* move `set.range_sigma_mk` to `data.set.sigma`;
* add `set.preimage_image_sigma_mk_of_ne`, `set.image_sigma_mk_preimage_sigma_map_subset`, and `set.image_sigma_mk_preimage_sigma_map`;
* add `function.injective.of_sigma_map` and `function.injective.sigma_map_iff`;
* don't use pattern matching in the definition of `prod.to_sigma`;
* add `filter.map_sigma_mk_comap`

### [2022-07-05 16:26:49](https://github.com/leanprover-community/mathlib/commit/527afb3)
feat(topology/sets/compacts): prod constructions ([#15118](https://github.com/leanprover-community/mathlib/pull/15118))

### [2022-07-05 15:04:58](https://github.com/leanprover-community/mathlib/commit/db9cb46)
feat(analysis/complex): equiv_real_prod_symm_apply ([#15122](https://github.com/leanprover-community/mathlib/pull/15122))
Plus some minor lemmas for [#15106](https://github.com/leanprover-community/mathlib/pull/15106).

### [2022-07-05 15:04:57](https://github.com/leanprover-community/mathlib/commit/68ae182)
feat(measure_theory/group/measure): a product of Haar measures is a Haar measure ([#15120](https://github.com/leanprover-community/mathlib/pull/15120))

### [2022-07-05 12:32:49](https://github.com/leanprover-community/mathlib/commit/365e30d)
chore(data/set/*,order/*): add missing lemmas about `monotone_on` etc ([#14943](https://github.com/leanprover-community/mathlib/pull/14943))
* Add `monotone_on`/`antitone`/`antitone_on` versions of existing `monotone` lemmas for `id`/`const`, `inf`/`sup`/`min`/`max`, `inter`/`union`, and intervals.
* Drop `set.monotone_prod`, leave `monotone.set_prod` only.
* Golf some proofs that were broken by removal of `set.monotone_prod`.

### [2022-07-05 10:10:27](https://github.com/leanprover-community/mathlib/commit/dba3dce)
feat(measure_theory/function/conditional_expectation): monotonicity of the conditional expectation ([#15024](https://github.com/leanprover-community/mathlib/pull/15024))

### [2022-07-05 10:10:26](https://github.com/leanprover-community/mathlib/commit/676e772)
refactor(analysis/convex/specific_functions): Remove hypothesis from `deriv_sqrt_mul_log` ([#15015](https://github.com/leanprover-community/mathlib/pull/15015))
This PR removes the `hx : 0 < x` hypothesis from `deriv_sqrt_mul_log`.

### [2022-07-05 08:48:19](https://github.com/leanprover-community/mathlib/commit/83eda07)
refactor(data/real/ennreal): golf, generalize ([#14996](https://github.com/leanprover-community/mathlib/pull/14996))
## Add new lemmas
* `ennreal.bit0_strict_mono`, `ennreal.bit0_injective`, `ennreal.bit0_lt_bit0`, `ennreal.bit0_le_bit0`, `ennreal.bit0_top`;
* `ennreal.bit1_strict_mono`, `ennreal.bit1_injective`, `ennreal.bit1_lt_bit1`, `ennreal.bit1_le_bit1`, `ennreal.bit1_top`;
* `ennreal.div_eq_inv_mul`, `ennreal.of_real_mul'`;
* `filter.eventually.prod_nhds`.
## Generalize lemmas
* Drop unneeded assumption in `real.to_nnreal_bit0` and `ennreal.of_real_bit0`.
## Rename lemmas
* `ennreal.mul_div_cancel` → `ennreal.div_mul_cancel`, fixing a TODO;
* `prod_is_open.mem_nhds` → `prod_mem_nhds`: there are no open sets in the statement.
## Other changes
* Golf some proofs.
* Avoid non-final `simp`s here and there.
* Move `mul_inv_cancel` etc up to use them in other proofs.
* Move some `to_nnreal` lemmas above `to_real` lemmas, use them in `to_real` lemmas.
* Use `to_dual` in `order_iso.inv_ennreal`.

### [2022-07-04 23:23:06](https://github.com/leanprover-community/mathlib/commit/1886093)
chore(analysis/calculus/deriv): make the exponent explicit in pow lemmas ([#15117](https://github.com/leanprover-community/mathlib/pull/15117))
This is useful to build derivatives for explicit functions using dot notation.

### [2022-07-04 21:37:31](https://github.com/leanprover-community/mathlib/commit/73d15d7)
feat(number_theory/wilson): add Wilson's Theorem ([#14717](https://github.com/leanprover-community/mathlib/pull/14717))
The previous "Wilson's lemma" (zmod.wilsons_lemma) was a single direction of the iff for Wilson's Theorem. This finishes the proof by adding the (admittedly, much simpler) direction where, if the congruence is satisfied for `n`, then `n` is prime.

### [2022-07-04 20:40:33](https://github.com/leanprover-community/mathlib/commit/06ac34b)
feat(analysis/special_functions/complex/arg): `continuous_at_arg_coe_angle` ([#14980](https://github.com/leanprover-community/mathlib/pull/14980))
Add the lemma that `complex.arg`, coerced to `real.angle`, is
continuous except at 0.

### [2022-07-04 19:58:37](https://github.com/leanprover-community/mathlib/commit/8f391f5)
feat(geometry/euclidean/basic): `continuous_at_angle` ([#15021](https://github.com/leanprover-community/mathlib/pull/15021))
Add lemmas that (unoriented) angles are continuous, as a function of a
pair of vectors or a triple of points, except where one of the vectors
is zero or one of the end points equals the middle point.

### [2022-07-04 17:12:28](https://github.com/leanprover-community/mathlib/commit/407f39b)
chore(ring_theory/matrix_algebra): golf using `matrix.map` ([#15040](https://github.com/leanprover-community/mathlib/pull/15040))
This replaces terms of the form `λ i j, a * algebra_map R A (m i j)` with the defeq `a • m.map (algebra_map R A)`, as then we get access to the API about `map`.
This also leverages existing bundled maps to avoid reproving linearity in the auxiliary constructions, removing `to_fun` and `to_fun_right_linear` as we can construct `to_fun_bilinear` directly with ease.

### [2022-07-04 01:38:58](https://github.com/leanprover-community/mathlib/commit/051dffa)
refactor(data/nat/parity): `nat.even_succ` -> `nat.even_add_one` ([#14917](https://github.com/leanprover-community/mathlib/pull/14917))
Change `nat.even_succ` to be analogous to `int.even_add_one`.

### [2022-07-03 17:11:19](https://github.com/leanprover-community/mathlib/commit/46344b4)
feat(category_theory/limits): bilimit from kernel ([#14452](https://github.com/leanprover-community/mathlib/pull/14452))

### [2022-07-03 11:47:31](https://github.com/leanprover-community/mathlib/commit/024a423)
refactor(category_theory): generalise universe levels in preservation statements ([#15067](https://github.com/leanprover-community/mathlib/pull/15067))
This big refactoring of universe levels in the category theory library allows to express limit preservation statements like exactness of functors which are between categories that are not necessarily in the same universe level. For this change to make sense for fixed diagrams (like coequalizers or binary products), the corresponding index categories, the universe of which so far was pinned to the category they were used for, is now fixed to `Type`.

### [2022-07-03 09:05:56](https://github.com/leanprover-community/mathlib/commit/6e8f25e)
chore(ring_theory/dedekind_domain/ideal): fix style of a lemma statement  ([#15097](https://github.com/leanprover-community/mathlib/pull/15097))

### [2022-07-02 14:14:01](https://github.com/leanprover-community/mathlib/commit/9e701b9)
feat(ring_theory/dedekind_domain): If `R/I` is isomorphic to `S/J` then the factorisations of `I` and `J` have the same shape ([#11053](https://github.com/leanprover-community/mathlib/pull/11053))
In this PR, we show that given Dedekind domains `R` and `S` with ideals `I` and `J`respectively, if quotients `R/I` and `S/J` are isomorphic, then the prime factorizations of `I` and `J` have the same shape, i.e. they have the same number of prime factors and up to permutation these prime factors have the same multiplicities. We can then get [the Dedekind-Kummer theorem](https://kconrad.math.uconn.edu/blurbs/gradnumthy/dedekindf.pdf) as a corollary of this statement. 
For previous discussion concerning the structure of this PR and the results it proves, see [#9345](https://github.com/leanprover-community/mathlib/pull/9345)

### [2022-07-02 12:02:23](https://github.com/leanprover-community/mathlib/commit/4823da2)
feat(data/nat/basic): add `mul_div_mul_comm_of_dvd_dvd` ([#15031](https://github.com/leanprover-community/mathlib/pull/15031))
Add lemma `mul_div_mul_comm_of_dvd_dvd (hac : c ∣ a) (hbd : d ∣ b) : (a * b) / (c * d) = (a / c) * (b / d)`
(Compare with `mul_div_mul_comm`, which holds for a `division_comm_monoid`)
Also adds the same lemma for a `euclidean_domain`.

### [2022-07-02 10:12:17](https://github.com/leanprover-community/mathlib/commit/2d76f56)
chore(algebra/associated): make `irreducible` not a class ([#14713](https://github.com/leanprover-community/mathlib/pull/14713))
This functionality was rarely used and doesn't align with how `irreducible` is used in practice.
In a future PR, we can remove some `unfreezingI`s caused by this.

### [2022-07-02 04:29:20](https://github.com/leanprover-community/mathlib/commit/855ed5c)
chore(scripts): update nolints.txt ([#15090](https://github.com/leanprover-community/mathlib/pull/15090))
I am happy to remove some nolints for you!

### [2022-07-01 20:56:46](https://github.com/leanprover-community/mathlib/commit/5654410)
chore(group_theory/group_action/opposite): add a missed smul/scalar rename ([#15082](https://github.com/leanprover-community/mathlib/pull/15082))
…ename

### [2022-07-01 20:56:45](https://github.com/leanprover-community/mathlib/commit/774e680)
feat(data/fintype/basic): add noncomputable equivalences between finsets as fintypes and `fin s.card`, etc. ([#15080](https://github.com/leanprover-community/mathlib/pull/15080))
As `s.card` is not defeq to `fintype.card s`, it is convenient to have these definitions in addition to `fintype.equiv_fin` and others (though we omit the computable ones).

### [2022-07-01 20:56:44](https://github.com/leanprover-community/mathlib/commit/9fcf391)
chore(group_theory/group_action/basic): relax monoid to mul_one_class ([#15051](https://github.com/leanprover-community/mathlib/pull/15051))

### [2022-07-01 20:56:43](https://github.com/leanprover-community/mathlib/commit/e94e5c0)
feat(topology/uniform_space/basic): uniform continuity from/to an infimum of uniform spaces ([#14892](https://github.com/leanprover-community/mathlib/pull/14892))
This adds uniform versions of various topological lemmas about continuity from/to infimas of topological spaces

### [2022-07-01 18:31:15](https://github.com/leanprover-community/mathlib/commit/ff5e97a)
feat(order/lattice, data/set): some helper lemmas ([#14789](https://github.com/leanprover-community/mathlib/pull/14789))
This PR provides lemmas describing when `s ∪ a = t ∪ a`, in both necessary and iff forms, as well as intersection and lattice versions.

### [2022-07-01 18:31:14](https://github.com/leanprover-community/mathlib/commit/7f95e22)
feat(linear_algebra/*): add lemma `linear_independent.finite_of_is_noetherian` ([#14714](https://github.com/leanprover-community/mathlib/pull/14714))
This replaces `fintype_of_is_noetherian_linear_independent` which gave the same
conclusion except demanded `strong_rank_condition R` instead of just `nontrivial R`.
Also some other minor gaps filled.

### [2022-07-01 14:39:25](https://github.com/leanprover-community/mathlib/commit/2ae2065)
chore(data/set,topology): fix 2 lemma names ([#15079](https://github.com/leanprover-community/mathlib/pull/15079))
* rename `set.quot_mk_range_eq` to `set.range_quotient_mk`;
* rename `is_closed_infi_iff` to `is_closed_supr_iff`.

### [2022-07-01 14:39:24](https://github.com/leanprover-community/mathlib/commit/8b69a4b)
feat(ring_theory): Some missing lemmas ([#15064](https://github.com/leanprover-community/mathlib/pull/15064))

### [2022-07-01 14:39:22](https://github.com/leanprover-community/mathlib/commit/36ee9af)
feat(topology/separation): `separation_quotient α` is a T₀ space ([#15043](https://github.com/leanprover-community/mathlib/pull/15043))

### [2022-07-01 14:39:20](https://github.com/leanprover-community/mathlib/commit/0369f20)
feat(order/locally_finite): make `fintype.to_locally_finite_order` computable ([#14733](https://github.com/leanprover-community/mathlib/pull/14733))

### [2022-07-01 12:26:35](https://github.com/leanprover-community/mathlib/commit/0522ee0)
refactor(ring_theory/jacobson): remove unnecessary `fintype.trunc_equiv_fin` ([#15077](https://github.com/leanprover-community/mathlib/pull/15077))

### [2022-07-01 12:26:34](https://github.com/leanprover-community/mathlib/commit/640955c)
refactor(ring_theory/finiteness): remove unnecessary `fintype.trunc_equiv_fin` ([#15076](https://github.com/leanprover-community/mathlib/pull/15076))

### [2022-07-01 12:26:33](https://github.com/leanprover-community/mathlib/commit/f9b939c)
feat(data/nat/enat): simple lemmas on `enat` ([#15029](https://github.com/leanprover-community/mathlib/pull/15029))

### [2022-07-01 12:26:32](https://github.com/leanprover-community/mathlib/commit/6e362f6)
chore(algebra/order/monoid): golf proofs, fix docs ([#14728](https://github.com/leanprover-community/mathlib/pull/14728))

### [2022-07-01 10:20:04](https://github.com/leanprover-community/mathlib/commit/9e97baa)
feat(data/list/basic): add filter_map_join ([#14777](https://github.com/leanprover-community/mathlib/pull/14777))

### [2022-07-01 10:20:03](https://github.com/leanprover-community/mathlib/commit/e73ac94)
feat (analysis/normed_space/lp_space):add l_infinity ring instances ([#14104](https://github.com/leanprover-community/mathlib/pull/14104))
We define pointwise multiplication on `lp E ∞` and give it has_mul, non_unital_ring, non_unital_normed_ring, ring, normed_ring, comm_ring and normed_comm_ring instances under the appropriate assumptions.

### [2022-07-01 08:11:22](https://github.com/leanprover-community/mathlib/commit/ce332c1)
refactor(algebra/group_power): split ring lemmas into a separate file ([#15032](https://github.com/leanprover-community/mathlib/pull/15032))
This doesn't actually stop `algebra.ring.basic` being imported into `group_power.basic` yet, but it makes it easier to make that change in future. Two ~300 line files are also slightly easier to manage than one ~600 line file, and ring/add_group feels like a natural place to draw the line
All lemmas have just been moved, and none have been renamed. Some lemmas have had their `R` variables renamed to `M` to better reflect that they apply to monoids with zero.
By grouping together the `monoid_with_zero` lemmas from separate files, it become apparent that there's some overlap.
This PR does not attempt to clean this up, in the interest of limiting the the scope of this change to just moves.

### [2022-07-01 04:21:43](https://github.com/leanprover-community/mathlib/commit/7e244d8)
feat(algebra/category/Module): upgrade `free : Type ⥤ Module R` to a monoidal functor ([#14328](https://github.com/leanprover-community/mathlib/pull/14328))