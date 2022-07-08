### [2021-11-30 16:52:36](https://github.com/leanprover-community/mathlib/commit/49f8b6b)
chore(analysis/mean_inequalities[_pow]): use vector notation ([#10546](https://github.com/leanprover-community/mathlib/pull/10546))
Several elementary inequalities in the library are expressed both in arbitrary n-ary versions and in explicit binary, ternary etc versions, with the latter deduced from the former.  This PR introduces vector notation to the proof terms deducing the latter from the former, which shortens them, and also makes them more readable.

### [2021-11-30 16:52:35](https://github.com/leanprover-community/mathlib/commit/b876e76)
feat(algebra/char_p/two): couple more lemmas + 🏌️ ([#10467](https://github.com/leanprover-community/mathlib/pull/10467))

### [2021-11-30 15:07:49](https://github.com/leanprover-community/mathlib/commit/cd69351)
doc(data/stream/defs): add docstrings to most defs ([#10547](https://github.com/leanprover-community/mathlib/pull/10547))
Also move 1 def from `basic` to `defs`.

### [2021-11-30 15:07:48](https://github.com/leanprover-community/mathlib/commit/8bce7eb)
refactor(algebra/group/basic): Migrate `add_group` section into `group` section ([#10532](https://github.com/leanprover-community/mathlib/pull/10532))

### [2021-11-30 13:24:44](https://github.com/leanprover-community/mathlib/commit/41fa32b)
feat(data/nat/pairing): add an `equiv` version of `nat.mkpair`/`nat.unpair` ([#10520](https://github.com/leanprover-community/mathlib/pull/10520))

### [2021-11-30 13:24:43](https://github.com/leanprover-community/mathlib/commit/af5c778)
feat(topology/[continuous_function, path_connected]): add bundled versions of prod_mk and prod_map ([#10512](https://github.com/leanprover-community/mathlib/pull/10512))
I also added a definition for pointwise addition of paths, but I'm not sure it would be really useful in general (my use case is the Sphere eversion project, where I need to add together two paths living in complement subspaces of a real TVS).

### [2021-11-30 13:24:41](https://github.com/leanprover-community/mathlib/commit/4d90ff9)
feat(topology/connected): Connectedness in sum and sigma type ([#10511](https://github.com/leanprover-community/mathlib/pull/10511))
This provides the `compact_space` and `totally_disconnected_space` instances for `α ⊕ β` and `Σ i, π i`.

### [2021-11-30 13:24:39](https://github.com/leanprover-community/mathlib/commit/7356269)
feat(linear_algebra/affine_space/basis): upgrade `affine_basis.coords` to an affine map ([#10452](https://github.com/leanprover-community/mathlib/pull/10452))
Formalized as part of the Sphere Eversion project.

### [2021-11-30 12:39:15](https://github.com/leanprover-community/mathlib/commit/35574bb)
fix(*): replace "the the" by "the" ([#10548](https://github.com/leanprover-community/mathlib/pull/10548))

### [2021-11-30 11:49:06](https://github.com/leanprover-community/mathlib/commit/1077f34)
feat(algebraic_geometry): Generalized basic open for arbitrary sections ([#10515](https://github.com/leanprover-community/mathlib/pull/10515))

### [2021-11-30 10:08:21](https://github.com/leanprover-community/mathlib/commit/6102d77)
feat(group_theory/submonoid/pointwise): pointwise inverse of a submonoid ([#10451](https://github.com/leanprover-community/mathlib/pull/10451))
This also adds `order_iso.map_{supr,infi,Sup,Inf}` which are used here to provide some short proofs.

### [2021-11-30 07:29:05](https://github.com/leanprover-community/mathlib/commit/4a9aa27)
feat(analysis/normed_space/spectrum and algebra/algebra/spectrum): prove properties of spectrum in a Banach algebra ([#10530](https://github.com/leanprover-community/mathlib/pull/10530))
Prove that the `spectrum` of an element in a Banach algebra is closed and bounded, hence compact when the scalar field is                               
proper. Compute the derivative of the `resolvent a` function in preparation for showing that the spectrum is nonempty when  the base field is ℂ. Define the `spectral_radius` and prove that it is bounded by the norm. Also rename the resolvent set to `resolvent_set` instead of `resolvent` so that it doesn't clash with the function name.

### [2021-11-30 06:50:40](https://github.com/leanprover-community/mathlib/commit/f11d505)
feat(category_theory/sites/compatible_*): Compatibility of plus and sheafification with composition. ([#10510](https://github.com/leanprover-community/mathlib/pull/10510))
Compatibility of sheafification with composition. This will be used later to obtain adjunctions between categories of sheaves.

### [2021-11-30 02:52:47](https://github.com/leanprover-community/mathlib/commit/396351b)
chore(scripts): update nolints.txt ([#10545](https://github.com/leanprover-community/mathlib/pull/10545))
I am happy to remove some nolints for you!

### [2021-11-29 21:29:13](https://github.com/leanprover-community/mathlib/commit/04fc415)
feat(algebra/char_p/two): lemmas about characteristic two ([#10442](https://github.com/leanprover-community/mathlib/pull/10442))

### [2021-11-29 19:42:43](https://github.com/leanprover-community/mathlib/commit/f798f22)
refactor(order/filter/bases): drop `p` in `has_antitone_basis` ([#10499](https://github.com/leanprover-community/mathlib/pull/10499))
We never use `has_antitone_basis` for `p ≠ λ _, true` in `mathlib`.

### [2021-11-29 17:49:24](https://github.com/leanprover-community/mathlib/commit/da6aceb)
chore(order): fix-ups after [#9891](https://github.com/leanprover-community/mathlib/pull/9891) ([#10538](https://github.com/leanprover-community/mathlib/pull/10538))

### [2021-11-29 17:49:23](https://github.com/leanprover-community/mathlib/commit/7545909)
chore(logic/function): allow `Sort*` in `function.inv_fun` ([#10526](https://github.com/leanprover-community/mathlib/pull/10526))

### [2021-11-29 17:49:21](https://github.com/leanprover-community/mathlib/commit/3ac9ae7)
chore(data/stream): dedup `take` and `approx` ([#10525](https://github.com/leanprover-community/mathlib/pull/10525))
`stream.take` and `stream.approx` were propositionally equal. Merge
them into one function `stream.take`; the definition comes from the old `stream.approx`.

### [2021-11-29 17:49:20](https://github.com/leanprover-community/mathlib/commit/bc4ed5c)
chore(*): cleanup unneeded uses of by_cases across the library ([#10523](https://github.com/leanprover-community/mathlib/pull/10523))
Many proofs in the library do case splits but then never use the introduced assumption in one of the cases, meaning the case split can be removed and replaced with the general argument.
Its easy to either accidentally introduce these more complicated than needed arguments when writing proofs, or in some cases presumably refactors made assumptions unnecessary, we golf / simplify several of these to simplify these proofs.
Similar things happen for `split_ifs` and explicit `if ... then` proofs.
Rather remarkably the changes to `uniformly_extend_spec` make the separated space assumption unnecessary too, and removing this removes this assumption from around 10 other lemmas in the library too.
Some more random golfs were added in the review process
Found with a work in progress linter.

### [2021-11-29 17:49:19](https://github.com/leanprover-community/mathlib/commit/5601833)
chore(*): a few facts about `pprod` ([#10519](https://github.com/leanprover-community/mathlib/pull/10519))
Add `equiv.pprod_equiv_prod` and `function.embedding.pprod_map`.

### [2021-11-29 17:49:18](https://github.com/leanprover-community/mathlib/commit/be48f95)
refactor(algebra.order.group): Convert abs_eq_sup_neg to multiplicative form ([#10505](https://github.com/leanprover-community/mathlib/pull/10505))
refactor(algebra.order.group): Convert abs_eq_sup_neg to multiplicative form

### [2021-11-29 17:49:17](https://github.com/leanprover-community/mathlib/commit/2ed7c0f)
doc(field_theory/galois): add comment that separable extensions are a… ([#10500](https://github.com/leanprover-community/mathlib/pull/10500))
…lgebraic
I teach my students that a Galois extension is algebraic, normal and separable, and was
just taken aback when I read the mathlib definition which omits "algebraic". Apparently
there are two conventions for the definition of separability, one implying algebraic and the other not:
https://en.wikipedia.org/wiki/Separable_extension#Separability_of_transcendental_extensions .
Right now we have separability implies algebraic in mathlib so mathematically we're fine; I just
add a note to clarify what's going on. In particular if we act on the TODO in
the separability definition, we may (perhaps unwittingly) break the definition of
`is_galois`; hopefully this note lessens the chance that this happens.

### [2021-11-29 17:49:15](https://github.com/leanprover-community/mathlib/commit/fcbe714)
refactor(data/nat/fib): use `nat.iterate` ([#10489](https://github.com/leanprover-community/mathlib/pull/10489))
The main drawback of the new definition is that `fib (n + 2) = fib n + fib (n + 1)` is no longer `rfl` but I think that we should have one API for iterates.
See discussion at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60nat.2Eiterate.60.20vs.20.60stream.2Eiterate.60

### [2021-11-29 17:11:51](https://github.com/leanprover-community/mathlib/commit/b849b3c)
feat(number_theory/padics/padic_norm): prime powers in divisors ([#10481](https://github.com/leanprover-community/mathlib/pull/10481))

### [2021-11-29 09:57:02](https://github.com/leanprover-community/mathlib/commit/957fa4b)
feat(order/locally_finite): `with_top α`/`with_bot α` are locally finite orders ([#10202](https://github.com/leanprover-community/mathlib/pull/10202))
This provides the two instances `locally_finite_order (with_top α)` and `locally_finite_order (with_bot α)`.

### [2021-11-29 06:52:12](https://github.com/leanprover-community/mathlib/commit/202ca0b)
feat(*/is_R_or_C): deduplicate ([#10522](https://github.com/leanprover-community/mathlib/pull/10522))
I noticed that the same argument, that in a normed space over `is_R_or_C` an element can be normalized, appears in a couple of different places in the library.  I have deduplicated and placed it in `analysis/normed_space/is_R_or_C`.

### [2021-11-29 06:52:11](https://github.com/leanprover-community/mathlib/commit/a53da16)
feat(data/int/basic): `nat_abs_dvd_iff_dvd` ([#10469](https://github.com/leanprover-community/mathlib/pull/10469))

### [2021-11-29 06:04:28](https://github.com/leanprover-community/mathlib/commit/50cc57b)
chore(category_theory/limits/shapes/wide_pullbacks): speed up `wide_cospan` ([#10535](https://github.com/leanprover-community/mathlib/pull/10535))

### [2021-11-29 01:36:13](https://github.com/leanprover-community/mathlib/commit/16daabf)
chore(algebra/group_power): golf a few proofs ([#10498](https://github.com/leanprover-community/mathlib/pull/10498))
* move `pow_lt_pow_of_lt_one` and `pow_lt_pow_iff_of_lt_one` from
  `algebra.group_power.lemmas` to `algebra.group_power.order`;
* add `strict_anti_pow`, use it to golf the proofs of the two lemmas
  above;
* golf a few other proofs;
* add `nnreal.exists_pow_lt_of_lt_one`.

### [2021-11-28 23:50:39](https://github.com/leanprover-community/mathlib/commit/77ba0c4)
chore(logic): allow `Sort*` args in 2 lemmas ([#10517](https://github.com/leanprover-community/mathlib/pull/10517))

### [2021-11-28 23:50:38](https://github.com/leanprover-community/mathlib/commit/c058607)
chore(order): generalize `min_top_left` ([#10486](https://github.com/leanprover-community/mathlib/pull/10486))
As well as its relative `min_top_right`.
Also provide `max_bot_(left|right)`.

### [2021-11-28 23:50:37](https://github.com/leanprover-community/mathlib/commit/43519fc)
feat(tactic/lint/misc): unused arguments checks for more sorry's ([#10431](https://github.com/leanprover-community/mathlib/pull/10431))
* The `unused_arguments` linter now checks whether `sorry` occurs in any of the `_proof_i` declarations and will not raise an error if this is the case
* Two minor changes: `open tactic` in all of `meta.expr` and fix a typo.
* I cannot add a test without adding a `sorry` to the test suite, but this succeeds without linter warning:
```lean
import tactic.lint
/-- dummy doc -/
def one (h : 0 < 1) : {n : ℕ // 0 < n} := ⟨1, sorry⟩
#lint
```

### [2021-11-28 22:06:26](https://github.com/leanprover-community/mathlib/commit/dfa98e0)
chore(algebra/opposites): split out lemmas about rings and groups ([#10457](https://github.com/leanprover-community/mathlib/pull/10457))
All these lemmas are just moved.
The advantage of this is that `algebra.opposites` becomes a much lighter-weight import, allowing us to use the `has_mul` and `has_scalar` instance on opposite types earlier in the import hierarchy.
It also matches how we structure the instances on `prod` and `pi` types.
This follows on from [#10383](https://github.com/leanprover-community/mathlib/pull/10383)

### [2021-11-28 20:23:10](https://github.com/leanprover-community/mathlib/commit/f684721)
chore(data/nat/prime): `fact (2.prime)` ([#10441](https://github.com/leanprover-community/mathlib/pull/10441))

### [2021-11-28 19:36:10](https://github.com/leanprover-community/mathlib/commit/a2e6bf8)
chore(algebraic_topology/cech_nerve): An attempt to speed up the proofs... ([#10521](https://github.com/leanprover-community/mathlib/pull/10521))
Let's hope this works!
See [zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2310312.20timeouts.20in.20cech_nerve/near/262587999)

### [2021-11-28 07:21:28](https://github.com/leanprover-community/mathlib/commit/044f532)
chore(analysis/normed_space/hahn_banach): remove `norm'` ([#10527](https://github.com/leanprover-community/mathlib/pull/10527))
For a normed space over `ℝ`-algebra `𝕜`, `norm'` is currently defined to be `algebra_map ℝ 𝕜 ∥x∥`.  I believe this was introduced before the `is_R_or_C` construct (including the coercion from `ℝ` to `𝕜` for `[is_R_or_C 𝕜]`) joined mathlib.  Now that we have these things, it's easy to just say `(∥x∥ : 𝕜)` instead of `norm' 𝕜 ∥x∥`, so I don't really think `norm'` needs to exist any more.
(In principle, `norm'` is more general, since it works for all `ℝ`-algebras `𝕜` rather than just `[is_R_or_C 𝕜]`.  But I can only really think of applications in the`is_R_or_C` case, and that's the only way it's used in the library.)

### [2021-11-28 07:21:27](https://github.com/leanprover-community/mathlib/commit/099fb0f)
feat(data/nat/prime): lemma eq_of_eq_count_factors ([#10493](https://github.com/leanprover-community/mathlib/pull/10493))

### [2021-11-28 06:12:10](https://github.com/leanprover-community/mathlib/commit/45d45ef)
feat(data/nat/prime): lemma count_factors_mul_of_coprime ([#10492](https://github.com/leanprover-community/mathlib/pull/10492))
Adding lemma `count_factors_mul_of_coprime` and using it to simplify the proof of `factors_count_eq_of_coprime_left`.

### [2021-11-28 03:39:40](https://github.com/leanprover-community/mathlib/commit/b1f9067)
feat(group_theory/group_action/units): add a `mul_distrib_mul_action` instance ([#10480](https://github.com/leanprover-community/mathlib/pull/10480))
This doesn't add any new "data" instances, it just shows the existing instance satisfies stronger properties with stronger assumptions.

### [2021-11-27 09:46:17](https://github.com/leanprover-community/mathlib/commit/b8af491)
feat(category_theory/sites/whiskering): Functors between sheaf categories induced by compositiion ([#10496](https://github.com/leanprover-community/mathlib/pull/10496))
We construct the functor `Sheaf J A` to `Sheaf J B` induced by a functor `A` to `B` which preserves the appropriate limits.

### [2021-11-27 08:42:32](https://github.com/leanprover-community/mathlib/commit/fcb3790)
feat(topology/algebra/matrix): the determinant is a continuous map ([#10503](https://github.com/leanprover-community/mathlib/pull/10503))
Formalized as part of the Sphere Eversion project.

### [2021-11-27 07:02:21](https://github.com/leanprover-community/mathlib/commit/d36a67c)
feat(ring_theory/euclidean_domain): generalize lemmas to PIDs ([#10324](https://github.com/leanprover-community/mathlib/pull/10324))
This moves the existing lemmas to the `euclidean_domain` namespace.

### [2021-11-27 02:49:59](https://github.com/leanprover-community/mathlib/commit/150b217)
chore(scripts): update nolints.txt ([#10513](https://github.com/leanprover-community/mathlib/pull/10513))
I am happy to remove some nolints for you!

### [2021-11-26 23:08:10](https://github.com/leanprover-community/mathlib/commit/7a19aa1)
feat(group_theory/order_of_element): linear ordered rings ([#10473](https://github.com/leanprover-community/mathlib/pull/10473))

### [2021-11-26 21:40:36](https://github.com/leanprover-community/mathlib/commit/7348f1b)
Adding a matching TODO back ([#10506](https://github.com/leanprover-community/mathlib/pull/10506))
Because we were careless and removed it too early:
https://github.com/leanprover-community/mathlib/pull/10210#discussion_r757640946

### [2021-11-26 17:50:35](https://github.com/leanprover-community/mathlib/commit/deb5692)
refactor(combinatorics/simple_graph): use subgraphs to represent matchings ([#10210](https://github.com/leanprover-community/mathlib/pull/10210))

### [2021-11-26 16:20:00](https://github.com/leanprover-community/mathlib/commit/dabb58b)
chore(algebra/module/pi): split out `group_theory/group_action/pi` to match `group_theory/group_action/prod` ([#10485](https://github.com/leanprover-community/mathlib/pull/10485))
These declarations are copied without modification.

### [2021-11-26 16:19:59](https://github.com/leanprover-community/mathlib/commit/ea52ec1)
feat(ring_theory/ideal/operations): add lemmas about comap ([#10418](https://github.com/leanprover-community/mathlib/pull/10418))
This also adds `ring_hom.to_semilinear_map` and `ring_equiv.to_semilinear_equiv`.

### [2021-11-26 15:44:03](https://github.com/leanprover-community/mathlib/commit/9cfa33a)
feat(algebra/lie): implement `set_like` for `lie_submodule` ([#10488](https://github.com/leanprover-community/mathlib/pull/10488))
This PR provides a `set_like` instance for `lie_submodule` and uses it to define `has_mem` and `has_le` for Lie submodules / ideals.

### [2021-11-26 12:59:28](https://github.com/leanprover-community/mathlib/commit/83bce9f)
feat(category_theory/adjunction/whiskering): Whiskering adjunctions. ([#10495](https://github.com/leanprover-community/mathlib/pull/10495))
Construct adjunctions between functor categories induced by whiskering (both left and right).
This will be used later to construct adjunctions between categories of sheaves.

### [2021-11-26 11:59:16](https://github.com/leanprover-community/mathlib/commit/61e8aa8)
feat(topology/algebra/[X]): sub[X] of a topological [X] is itself a topological [X] ([#10491](https://github.com/leanprover-community/mathlib/pull/10491))

### [2021-11-26 11:04:50](https://github.com/leanprover-community/mathlib/commit/36f33d0)
chore(category_theory/limits): Generalize universes for limits ([#10243](https://github.com/leanprover-community/mathlib/pull/10243))

### [2021-11-26 07:20:19](https://github.com/leanprover-community/mathlib/commit/0b9d332)
feat(data/complex/basic): `of_real_injective` ([#10464](https://github.com/leanprover-community/mathlib/pull/10464))

### [2021-11-26 07:20:18](https://github.com/leanprover-community/mathlib/commit/e742fce)
feat(data/nat/prime): `nat.{eq/ne}_one_iff` ([#10463](https://github.com/leanprover-community/mathlib/pull/10463))

### [2021-11-26 07:20:17](https://github.com/leanprover-community/mathlib/commit/71bc7f4)
feat(set_theory/ordinal_notation): nonote is well founded ([#10462](https://github.com/leanprover-community/mathlib/pull/10462))

### [2021-11-26 07:20:16](https://github.com/leanprover-community/mathlib/commit/cdb3819)
feat(algebraic_geometry): `of_restrict` is mono. ([#10460](https://github.com/leanprover-community/mathlib/pull/10460))

### [2021-11-26 07:20:15](https://github.com/leanprover-community/mathlib/commit/757aa6f)
chore(data/stream): move most defs to a new file ([#10458](https://github.com/leanprover-community/mathlib/pull/10458))

### [2021-11-26 07:20:14](https://github.com/leanprover-community/mathlib/commit/3dfa349)
feat(topology/uniform_space/completion) : add injective_coe ([#10454](https://github.com/leanprover-community/mathlib/pull/10454))

### [2021-11-26 07:20:13](https://github.com/leanprover-community/mathlib/commit/cbe1d37)
feat(ring_theory/valuation/basic): add valuation.map_zpow ([#10453](https://github.com/leanprover-community/mathlib/pull/10453))

### [2021-11-26 07:20:12](https://github.com/leanprover-community/mathlib/commit/9249e1e)
chore(linear_algebra/affine_space/barycentric_coords): rename file `barycentric_coords` to `basis` ([#10449](https://github.com/leanprover-community/mathlib/pull/10449))
Follow up from https://github.com/leanprover-community/mathlib/pull/10320#discussion_r748936743

### [2021-11-26 07:20:11](https://github.com/leanprover-community/mathlib/commit/28d9a5b)
feat(data/equiv/basic): add lemmas characterising `equiv.Pi_congr` and `equiv.Pi_congr'` ([#10432](https://github.com/leanprover-community/mathlib/pull/10432))
Formalized as part of the Sphere Eversion project.

### [2021-11-26 06:45:43](https://github.com/leanprover-community/mathlib/commit/be9b96e)
feat(computablility/halting): halting problem is r.e. ([#10459](https://github.com/leanprover-community/mathlib/pull/10459))
This is a minor oversight from the original formalization, pointed out by Keji Neri.

### [2021-11-26 02:32:10](https://github.com/leanprover-community/mathlib/commit/f55a284)
feat(topology): normal topological space with second countable topology is metrizable ([#10402](https://github.com/leanprover-community/mathlib/pull/10402))
Also prove that a regular topological space with second countable topology is a normal space.

### [2021-11-25 18:25:14](https://github.com/leanprover-community/mathlib/commit/ee71ddf)
feat(ring_theory/graded_algebra): definition of type class `graded_algebra` ([#10115](https://github.com/leanprover-community/mathlib/pull/10115))
This is largely written by @eric-wieser. Thank you.

### [2021-11-25 16:03:28](https://github.com/leanprover-community/mathlib/commit/644591f)
chore(algebra/group/basic): + 2 simp lemmas about `a - b` ([#10478](https://github.com/leanprover-community/mathlib/pull/10478))

### [2021-11-25 12:14:38](https://github.com/leanprover-community/mathlib/commit/7d8a1e0)
feat(data/polynomial/eval): random `eval` lemmas ([#10470](https://github.com/leanprover-community/mathlib/pull/10470))
note that the `geom_sum` import only adds the `geom_sum` file itself; all other files were imported already

### [2021-11-25 07:53:00](https://github.com/leanprover-community/mathlib/commit/5b767aa)
feat(measure_theory/integral/integral_eq_improper): weaken measurability assumptions  ([#10387](https://github.com/leanprover-community/mathlib/pull/10387))
As suggested by @fpvandoorn, this removes a.e. measurability assumptions which could be deduced from integrability assumptions. More of them could be removed assuming the codomain is a `borel_space` and not only an `open_measurable_space`, but I’m not sure wether or not it would be a good idea.

### [2021-11-25 03:11:34](https://github.com/leanprover-community/mathlib/commit/7dfd7e8)
chore(scripts): update nolints.txt ([#10484](https://github.com/leanprover-community/mathlib/pull/10484))
I am happy to remove some nolints for you!

### [2021-11-25 01:40:31](https://github.com/leanprover-community/mathlib/commit/d04f5a5)
feat(algebra/pointwise): lemmas about multiplication of finsets ([#10455](https://github.com/leanprover-community/mathlib/pull/10455))

### [2021-11-24 18:18:56](https://github.com/leanprover-community/mathlib/commit/daf30fd)
feat(analysis/asymptotics): Generalize superpolynomial decay using limits instead of big O ([#10296](https://github.com/leanprover-community/mathlib/pull/10296))
This PR generalizes the definition of `superpolynomial_decay` in terms of `filter.tendsto` instead of `asymptotics.is_O`.

### [2021-11-24 14:56:57](https://github.com/leanprover-community/mathlib/commit/18e5510)
fix(tactic/cancel_denoms): remove debug code ([#10434](https://github.com/leanprover-community/mathlib/pull/10434))
This code must not be used -- worth keeping, as it's a potentially useful function, but it shouldn't trace anything.

### [2021-11-24 12:24:42](https://github.com/leanprover-community/mathlib/commit/b29b952)
feat(measure_theory/group/fundamental_domain): prove equality of integrals ([#10448](https://github.com/leanprover-community/mathlib/pull/10448))

### [2021-11-24 12:24:41](https://github.com/leanprover-community/mathlib/commit/563f8c4)
feat(measure_theory/integral): dominated convergence for a series ([#10398](https://github.com/leanprover-community/mathlib/pull/10398))

### [2021-11-24 10:42:43](https://github.com/leanprover-community/mathlib/commit/132833b)
refactor(algebra.abs): Introduce `has_pos_part` and `has_neg_part` classes ([#10420](https://github.com/leanprover-community/mathlib/pull/10420))
refactor(algebra.abs): Introduce `has_pos_part` and `has_neg_part` classes

### [2021-11-24 09:23:46](https://github.com/leanprover-community/mathlib/commit/09b4bfc)
feat(linear_algebra/multilinear/basic): multilinear maps with respect to an empty family are all constant ([#10433](https://github.com/leanprover-community/mathlib/pull/10433))
This seemingly-innocuous statement is valuable as a base case for induction.
Formalized as part of the Sphere Eversion project.

### [2021-11-24 07:49:21](https://github.com/leanprover-community/mathlib/commit/d487d65)
refactor(topology,algebraic_geometry): use bundled maps here and there ([#10447](https://github.com/leanprover-community/mathlib/pull/10447))
* `opens.comap` now takes a `continuous_map` and returns a `preorder_hom`;
* `prime_spectrum.comap` is now a bundled `continuous_map`.

### [2021-11-24 07:49:20](https://github.com/leanprover-community/mathlib/commit/3590dc2)
feat(topology/uniform_space/uniform_convergence): slightly generalize theorems ([#10444](https://github.com/leanprover-community/mathlib/pull/10444))
* add `protected` to some theorems;
* assume `∀ᶠ n, continuous (F n)` instead of `∀ n, continuous (F n)`;
* get rid of `F n` in lemmas like `continuous_within_at_of_locally_uniform_approx_of_continuous_within_at`; instead, assume that there exists a continuous `F` that approximates `f`.

### [2021-11-24 07:49:19](https://github.com/leanprover-community/mathlib/commit/8d07dbf)
feat(topology/sheaves): Generalized some lemmas. ([#10440](https://github.com/leanprover-community/mathlib/pull/10440))
Generalizes some lemmas and explicitly stated that for `f` to be an iso on `U`, it suffices that the stalk map is an iso for all `x : U`.

### [2021-11-24 07:49:18](https://github.com/leanprover-community/mathlib/commit/a086daa)
chore(ring_theory/polynomial/cyclotomic): use `ratfunc` ([#10421](https://github.com/leanprover-community/mathlib/pull/10421))

### [2021-11-24 07:49:17](https://github.com/leanprover-community/mathlib/commit/6cb52e6)
feat(category_theory/limits): Results about (co)limits in Top ([#9985](https://github.com/leanprover-community/mathlib/pull/9985))
- Provided the explicit topologies for limits and colimits, and specialized this result onto some shapes.
- Provided the isomorphism between the (co)limits and the constructions in `topology/constructions.lean`.
- Provided conditions about whether `prod.map` and `pullback_map` are inducing, embedding, etc.

### [2021-11-24 06:51:50](https://github.com/leanprover-community/mathlib/commit/d267b6c)
chore(topology): add 2 missing `inhabited` instances ([#10446](https://github.com/leanprover-community/mathlib/pull/10446))
Also add an instance from `discrete_topology` to `topological_ring`.

### [2021-11-24 03:16:10](https://github.com/leanprover-community/mathlib/commit/1c00179)
chore(scripts): update nolints.txt ([#10445](https://github.com/leanprover-community/mathlib/pull/10445))
I am happy to remove some nolints for you!

### [2021-11-24 02:33:03](https://github.com/leanprover-community/mathlib/commit/f578d1d)
feat(measure_theory): TC for smul-invariant measures ([#10325](https://github.com/leanprover-community/mathlib/pull/10325))

### [2021-11-23 22:42:46](https://github.com/leanprover-community/mathlib/commit/0cbba1a)
feat(ring_theory/adjoin/basic): add adjoin_induction' and adjoin_adjoin_coe_preimage ([#10427](https://github.com/leanprover-community/mathlib/pull/10427))
From FLT-regular.

### [2021-11-23 22:42:45](https://github.com/leanprover-community/mathlib/commit/c192937)
feat(analysis): derivative of a parametric interval integral ([#10404](https://github.com/leanprover-community/mathlib/pull/10404))

### [2021-11-23 21:34:42](https://github.com/leanprover-community/mathlib/commit/ac283c2)
feat(data/nat/prime): some lemmas about prime factors ([#10385](https://github.com/leanprover-community/mathlib/pull/10385))
A few small lemmas about prime factors, for use in future PRs on prime factorisations and the Euler product formula for totient

### [2021-11-23 20:50:39](https://github.com/leanprover-community/mathlib/commit/eb8b1b8)
feat(linear_algebra/affine_space/barycentric_coords): characterise affine bases in terms of coordinate matrices ([#10370](https://github.com/leanprover-community/mathlib/pull/10370))
Formalized as part of the Sphere Eversion project.

### [2021-11-23 19:47:54](https://github.com/leanprover-community/mathlib/commit/fb82d0a)
feat(data/mv_polynomial/basic): add a symmetric version of coeff_X_mul and generalize to monomials ([#10429](https://github.com/leanprover-community/mathlib/pull/10429))

### [2021-11-23 19:47:53](https://github.com/leanprover-community/mathlib/commit/ba43124)
feat(category_theory/sites/*): Comparison lemma ([#9785](https://github.com/leanprover-community/mathlib/pull/9785))

### [2021-11-23 18:21:04](https://github.com/leanprover-community/mathlib/commit/a779f6c)
feat(topology/algebra/ordered): convergent sequence is bounded above/below ([#10424](https://github.com/leanprover-community/mathlib/pull/10424))
Also move lemmas `Ixx_mem_nhds` up to generalize them from
`[linear_order α] [order_topology α]` to
`[linear_order α] [order_closed_topology α]`.

### [2021-11-23 18:21:02](https://github.com/leanprover-community/mathlib/commit/1dd3ae1)
feat(algebra/big_operators/order): Bounding on a sum of cards by double counting ([#10389](https://github.com/leanprover-community/mathlib/pull/10389))
If every element of `s` is in at least/most `n` finsets of `B : finset (finset α)`, then the sum of `(s ∩ t).card` over `t ∈ B` is at most/least `s.card * n`.

### [2021-11-23 16:49:25](https://github.com/leanprover-community/mathlib/commit/b14f22e)
chore(algebra/algebra and group_theory/group_action): move a lemma ([#10425](https://github.com/leanprover-community/mathlib/pull/10425))
Move a lemma about the action of a group on the units of a monoid
to a more appropriate place. It accidentally ended up in
`algebra/algebra/spectrum` but a better place is
`group_theory/group_action/units`.

### [2021-11-23 16:49:24](https://github.com/leanprover-community/mathlib/commit/7c4f395)
feat(measure_theory): add `is_R_or_C.measurable_space` ([#10417](https://github.com/leanprover-community/mathlib/pull/10417))
Don't remove specific instances because otherwise Lean fails to generate `borel_space (ι → ℝ)`.

### [2021-11-23 16:49:23](https://github.com/leanprover-community/mathlib/commit/a1338d6)
feat(linear_algebra/affine_space/barycentric_coords): affine bases exist over fields ([#10333](https://github.com/leanprover-community/mathlib/pull/10333))
Formalized as part of the Sphere Eversion project.

### [2021-11-23 16:49:22](https://github.com/leanprover-community/mathlib/commit/7a6e6d8)
feat(group_theory/schur_zassenhaus): Prove the full Schur-Zassenhaus theorem ([#10283](https://github.com/leanprover-community/mathlib/pull/10283))
Previously, the Schur-Zassenhaus theorem was only proved for abelian normal subgroups. This PR removes the abelian assumption.

### [2021-11-23 16:49:21](https://github.com/leanprover-community/mathlib/commit/97186fe)
feat(combinatorics): Hindman's theorem on finite sums ([#10029](https://github.com/leanprover-community/mathlib/pull/10029))
A short proof of Hindman's theorem using idempotent ultrafilters.

### [2021-11-23 15:06:10](https://github.com/leanprover-community/mathlib/commit/050482c)
doc(measure_theory/decomposition/jordan): typo ([#10430](https://github.com/leanprover-community/mathlib/pull/10430))

### [2021-11-23 15:06:08](https://github.com/leanprover-community/mathlib/commit/53bd9d7)
feat(field_theory): generalize `ratfunc K` to `comm_ring K`/`is_domain K` ([#10428](https://github.com/leanprover-community/mathlib/pull/10428))
Fixes one of the TODO's from the original ratfunc PR: apply all the easy generalizations where `K` doesn't need to be a field, only a `is_domain K` or even just `comm_ring K`.
This would allow us to use `ratfunc` in [#10421](https://github.com/leanprover-community/mathlib/pull/10421).

### [2021-11-23 15:06:07](https://github.com/leanprover-community/mathlib/commit/7958251)
doc(field_theory/abel_ruffini): update module doc ([#10426](https://github.com/leanprover-community/mathlib/pull/10426))

### [2021-11-23 15:06:06](https://github.com/leanprover-community/mathlib/commit/2b75493)
refactor(algebra.group.basic): Convert sub_add_cancel and neg_sub to multaplicative form ([#10419](https://github.com/leanprover-community/mathlib/pull/10419))
Currently mathlib has a rich set of lemmas connecting the addition, subtraction and negation additive group operations, but a far thinner collection of results for multiplication, division and inverse multiplicative group operations, despite the fact that the former can be generated easily from the latter via `to_additive`.
In  [#9548](https://github.com/leanprover-community/mathlib/pull/9548) I require multiplicative forms of the existing `sub_add_cancel` and `neg_sub` lemmas. This PR refactors them as the equivalent multiplicative results and then recovers `sub_add_cancel` and `neg_sub` via `to_additive`. There is a complication in that unfortunately `group_with_zero` already has lemmas named `inv_div` and `div_mul_cancel`. I have worked around this by naming the lemmas in this PR `inv_div'` and `div_mul_cancel'` and then manually overriding the names generated by `to_additive`. Other suggestions as to how to approach this welcome.

### [2021-11-23 15:06:04](https://github.com/leanprover-community/mathlib/commit/d0e454a)
feat(logic/function/basic): add `function.{in,sur,bi}jective.comp_left` ([#10406](https://github.com/leanprover-community/mathlib/pull/10406))
As far as I can tell we don't have these variations.
Note that the `surjective` and `bijective` versions do not appear next to the other composition statements, as they require `surj_inv` to concisely prove.

### [2021-11-23 13:11:55](https://github.com/leanprover-community/mathlib/commit/d9e40b4)
chore(measure_theory/integral): generalize `interval_integral.norm_integral_le_integral_norm` ([#10412](https://github.com/leanprover-community/mathlib/pull/10412))
It was formulated only for functions `f : α → ℝ`; generalize to `f : α → E`.

### [2021-11-23 13:11:54](https://github.com/leanprover-community/mathlib/commit/2817788)
chore(measure_theory/integral): add `integrable_const` for `interval_integral` ([#10410](https://github.com/leanprover-community/mathlib/pull/10410))

### [2021-11-23 13:11:53](https://github.com/leanprover-community/mathlib/commit/3b13744)
chore(measure_theory/integral): more versions of `integral_finset_sum` ([#10394](https://github.com/leanprover-community/mathlib/pull/10394))
* fix assumptions in existing lemmas (`∀ i ∈ s` instead of `∀ i`);
* add a version for interval integrals.

### [2021-11-23 13:11:52](https://github.com/leanprover-community/mathlib/commit/2ec6de7)
feat(topology/connected): sufficient conditions for the preimage of a connected set to be connected ([#10289](https://github.com/leanprover-community/mathlib/pull/10289))
and other simple connectedness results

### [2021-11-23 13:11:50](https://github.com/leanprover-community/mathlib/commit/e8386bd)
feat(group_theory/exponent): Define the exponent of a group ([#10249](https://github.com/leanprover-community/mathlib/pull/10249))
This PR provides the definition and some very basic API for the exponent of a group/monoid.

### [2021-11-23 13:11:48](https://github.com/leanprover-community/mathlib/commit/cf91773)
refactor(*): split `order_{top,bot}` from `lattice` hierarchy ([#9891](https://github.com/leanprover-community/mathlib/pull/9891))
Rename `bounded_lattice` to `bounded_order`.
Split out `order_{top,bot}` and `bounded_order` from the order hierarchy.
That means that we no longer have `semilattice_{sup,inf}_{top,bot}`, but use the `[order_top]` as a mixin to `semilattice_inf`, for example.
Similarly, `lattice` and `bounded_order` instead of what was before `bounded_lattice`.
Similarly, `distrib_lattice` and `bounded_order` instead of what was before `bounded_distrib_lattice`.

### [2021-11-23 11:49:18](https://github.com/leanprover-community/mathlib/commit/3fee4b9)
chore(control/random): Move from `system.random.basic` ([#10408](https://github.com/leanprover-community/mathlib/pull/10408))
The top folder `system` contains a single file, apparently because it mimics Lean core's organisation. This moves it under `control.` and gets rid of one top folder.

### [2021-11-23 11:49:16](https://github.com/leanprover-community/mathlib/commit/b1a9c2e)
feat(analysis/normed_space/multilinear): add `norm_mk_pi_field` ([#10396](https://github.com/leanprover-community/mathlib/pull/10396))
Also upgrade the corresponding equivalence to a `linear_isometry`.

### [2021-11-23 11:49:15](https://github.com/leanprover-community/mathlib/commit/87b0084)
chore(field_theory/separable): generalize theorems ([#10337](https://github.com/leanprover-community/mathlib/pull/10337))

### [2021-11-23 11:49:14](https://github.com/leanprover-community/mathlib/commit/9cf6766)
feat(order/filter/pi): define `filter.pi` and prove some properties ([#10323](https://github.com/leanprover-community/mathlib/pull/10323))

### [2021-11-23 11:49:13](https://github.com/leanprover-community/mathlib/commit/33ea401)
feat(linear_algebra/affine_space/barycentric_coords): barycentric coordinates are ratio of determinants ([#10320](https://github.com/leanprover-community/mathlib/pull/10320))
The main goal of this PR is the new lemma `affine_basis.det_smul_coords_eq_camer_coords`
A secondary goal is a minor refactor of barycentric coordinates so that they are associated to a new structure `affine_basis`. As well as making the API for affine spaces more similar to that of modules, this enables an extremely useful dot notation.
The work here could easily be split into two PRs and I will happily do so if requested.
Formalized as part of the Sphere Eversion project.

### [2021-11-23 11:49:12](https://github.com/leanprover-community/mathlib/commit/d94772b)
feat(algebra/big_operators/finprod): add finprod_div_distrib and finsum_sub_distrib ([#10044](https://github.com/leanprover-community/mathlib/pull/10044))

### [2021-11-23 09:38:33](https://github.com/leanprover-community/mathlib/commit/ac71292)
chore(measure_theory/integral): generalize `integral_smul_const` ([#10411](https://github.com/leanprover-community/mathlib/pull/10411))
* generalize to `is_R_or_C`;
* add an `interval_integral` version.

### [2021-11-23 09:38:32](https://github.com/leanprover-community/mathlib/commit/8f681f1)
chore(data/complex): add a few simp lemmas ([#10395](https://github.com/leanprover-community/mathlib/pull/10395))

### [2021-11-23 09:38:31](https://github.com/leanprover-community/mathlib/commit/4d5d770)
feat(data/complex/exponential): Add lemma add_one_le_exp ([#10358](https://github.com/leanprover-community/mathlib/pull/10358))
This PR resolves https://github.com/leanprover-community/mathlib/blob/master/src/data/complex/exponential.lean#L1140

### [2021-11-23 07:23:05](https://github.com/leanprover-community/mathlib/commit/6050f9d)
feat(algebraic_geometry, category_theory): SheafedSpace has colimits ([#10401](https://github.com/leanprover-community/mathlib/pull/10401))

### [2021-11-23 07:23:04](https://github.com/leanprover-community/mathlib/commit/ca7347c)
refactor(ring_theory/sub[semi]ring): move pointwise instances to their own file ([#10347](https://github.com/leanprover-community/mathlib/pull/10347))
This matches how we have separate pointwise files for `submonoid` and `subgroup`.
All the new lemmas are direct copies of the subgroup lemmas.

### [2021-11-23 07:23:02](https://github.com/leanprover-community/mathlib/commit/a586681)
feat(category_theory/limits/shapes): Multiequalizer is the equalizer ([#10267](https://github.com/leanprover-community/mathlib/pull/10267))

### [2021-11-23 05:35:13](https://github.com/leanprover-community/mathlib/commit/6dddef2)
feat(topology/metric_space): range of a cauchy seq is bounded ([#10423](https://github.com/leanprover-community/mathlib/pull/10423))

### [2021-11-23 01:33:14](https://github.com/leanprover-community/mathlib/commit/f684f61)
feat(algebra/algebra/spectrum): define spectrum and prove basic prope... ([#10390](https://github.com/leanprover-community/mathlib/pull/10390))
…rties
Define the resolvent set and the spectrum of an element of an algebra as
a set of elements in the scalar ring. We prove a few basic facts
including that additive cosets of the spectrum commute with the
spectrum, that is, r + σ a = σ (r ⬝ 1 + a). Similarly, multiplicative
cosets of the spectrum also commute when the element r is a unit of
the scalar ring R. Finally, we also show that the units of R in
σ (a*b) coincide with those of σ (b*a).

### [2021-11-22 22:48:19](https://github.com/leanprover-community/mathlib/commit/e59e03f)
feat(measure_theory/integral/interval_integral): add an alternative definition ([#10380](https://github.com/leanprover-community/mathlib/pull/10380))
Prove that `∫ x in a..b, f x ∂μ = sgn a b • ∫ x in Ι a b, f x ∂μ`,
where `sgn a b = if a ≤ b then 1 else -1`.

### [2021-11-22 19:46:14](https://github.com/leanprover-community/mathlib/commit/2f5af98)
feat(data/nat/prime): prime divisors ([#10318](https://github.com/leanprover-community/mathlib/pull/10318))
Adding some basic lemmas about `factors` and `factors.to_finset`

### [2021-11-22 18:50:52](https://github.com/leanprover-community/mathlib/commit/317483a)
feat(analysis/calculus/parametric_integral): generalize, rename ([#10397](https://github.com/leanprover-community/mathlib/pull/10397))
* add `integral` to lemma names;
* a bit more general
  `has_fderiv_at_integral_of_dominated_loc_of_lip'`: only require an
  estimate on `∥F x a - F x₀ a∥` instead of `∥F x a - F y a∥`;
* generalize the `deriv` lemmas to `F : 𝕜 → α → E`, `[is_R_or_C 𝕜]`.

### [2021-11-22 16:51:24](https://github.com/leanprover-community/mathlib/commit/d2ebcad)
fix(undergrad.yaml): reinstate deleted entry ([#10416](https://github.com/leanprover-community/mathlib/pull/10416))
Revert an (I assume accidental?) deletion in [#10415](https://github.com/leanprover-community/mathlib/pull/10415).
cc @PatrickMassot

### [2021-11-22 13:14:41](https://github.com/leanprover-community/mathlib/commit/c896162)
feat(data/finset/basic) eq_of_mem_singleton ([#10414](https://github.com/leanprover-community/mathlib/pull/10414))
The `finset` equivalent of [set.eq_of_mem_singleton](https://leanprover-community.github.io/mathlib_docs/find/set.eq_of_mem_singleton/src)

### [2021-11-22 11:23:11](https://github.com/leanprover-community/mathlib/commit/d8d0c59)
chore(algebra/opposites): split group actions and division_ring into their own files ([#10383](https://github.com/leanprover-community/mathlib/pull/10383))
This splits out `group_theory.group_action.opposite` and `algebra.field.opposite` from `algebra.opposites`.
The motivation is to make opposite actions available slightly earlier in the import graph.
We probably want to split out `ring` at some point too, but that's likely a more annoying change so I've left it for future work.
These lemmas are just moved, and some `_root_` prefixes eliminated by removing the surrounding `namespace`.

### [2021-11-22 11:23:10](https://github.com/leanprover-community/mathlib/commit/2aea996)
feat(data): define a `fun_like` class of bundled homs (function + proofs) ([#10286](https://github.com/leanprover-community/mathlib/pull/10286))
This PR introduces a class `fun_like` for types of bundled homomorphisms, like `set_like` is for bundled subobjects. This should be useful by itself, but an important use I see for it is the per-morphism class refactor, see [#9888](https://github.com/leanprover-community/mathlib/pull/9888).
Also, `coe_fn_coe_base` now has an appropriately low priority, so it doesn't take precedence over `fun_like.has_coe_to_fun`.

### [2021-11-22 09:54:52](https://github.com/leanprover-community/mathlib/commit/7a5fac3)
feat(ring_theory/roots_of_unity): primitive root lemmas ([#10356](https://github.com/leanprover-community/mathlib/pull/10356))
From the flt-regular project.

### [2021-11-22 08:59:57](https://github.com/leanprover-community/mathlib/commit/9f07579)
docs(undergrad): add urls in linear algebra ([#10415](https://github.com/leanprover-community/mathlib/pull/10415))
This uses the new possibility to put urls in `undergrad.yaml` hoping to help describing what is meant to be formalized. We should probably create wiki pages for some cases that are not so clear even with a url. There is one case where I could find only a French page and some cases where I couldn't find anything. Amazingly "endormorphism exponential" is such a case, but hopefully this example is already clear. Another kind of problematic item is the "example" item in the representation section. Presumably it should be removed and replaced with a couple of explicit examples such as "standard representation of a matrix group" or "permutation representation".

### [2021-11-22 00:26:55](https://github.com/leanprover-community/mathlib/commit/9277d4b)
chore(data/finset/basic): finset.prod -> finset.product in module docstring ([#10413](https://github.com/leanprover-community/mathlib/pull/10413))

### [2021-11-21 22:33:27](https://github.com/leanprover-community/mathlib/commit/d17db71)
chore(*): golf proofs about `filter.Coprod` ([#10400](https://github.com/leanprover-community/mathlib/pull/10400))
Also add some supporting lemmas.

### [2021-11-21 22:33:26](https://github.com/leanprover-community/mathlib/commit/d98b8e0)
feat(linear_algebra/bilinear_map): semilinearize bilinear maps ([#10373](https://github.com/leanprover-community/mathlib/pull/10373))
This PR generalizes most of `linear_algebra/bilinear_map` to semilinear maps. Along the way, we introduce an instance for `module S (E →ₛₗ[σ] F)`, with `σ : R →+* S`. This allows us to define "semibilinear" maps of type `E →ₛₗ[σ] F →ₛₗ[ρ] G`, where `E`, `F` and `G` are modules over `R₁`, `R₂` and `R₃` respectively, and `σ : R₁ →+* R₃` and `ρ : R₂ →+* R₃`. See `mk₂'ₛₗ` to see how to construct such a map.

### [2021-11-21 21:47:34](https://github.com/leanprover-community/mathlib/commit/8f07d75)
feat(measure_theory/covering/differentiation): differentiation of measures ([#10101](https://github.com/leanprover-community/mathlib/pull/10101))
If `ρ` and `μ` are two Radon measures on a finite-dimensional normed real vector space, then for `μ`-almost every `x`, the ratio `ρ (B (x, r)) / μ (B(x,r))` converges when `r` tends to `0`, towards the Radon-Nikodym derivative of `ρ` with respect to `μ`. This is the main theorem on differentiation of measures.
The convergence in fact holds for more general families of sets than balls, called Vitali families (the fact that balls form a Vitali family is a restatement of the Besicovitch covering theorem). The general version of the differentation of measures theorem is proved in this PR, following [Federer, geometric measure theory].

### [2021-11-21 20:56:17](https://github.com/leanprover-community/mathlib/commit/8ee634b)
feat(measure_theory): define volume on `complex` ([#10403](https://github.com/leanprover-community/mathlib/pull/10403))

### [2021-11-21 18:40:48](https://github.com/leanprover-community/mathlib/commit/2168297)
feat(analysis/inner_product_space/projection): orthogonal group is generated by reflections ([#10381](https://github.com/leanprover-community/mathlib/pull/10381))

### [2021-11-21 16:46:44](https://github.com/leanprover-community/mathlib/commit/e0c0d84)
feat(topology/separation): removing a finite set from a dense set preserves density ([#10405](https://github.com/leanprover-community/mathlib/pull/10405))
Also add the fact that one can find a dense set containing neither top nor bottom in a nontrivial dense linear order.

### [2021-11-21 11:11:05](https://github.com/leanprover-community/mathlib/commit/55b81f8)
feat(measure_theory): measure preserving maps and integrals ([#10326](https://github.com/leanprover-community/mathlib/pull/10326))
If `f` is a measure preserving map, then `∫ y, g y ∂ν = ∫ x, g (f x) ∂μ`. It was two rewrites with the old API (`hf.map_eq`, then a lemma about integral over map measure); it's one `rw` now.
Also add versions for special cases when `f` is a measurable embedding (in this case we don't need to assume measurability of `g`).

### [2021-11-20 23:37:29](https://github.com/leanprover-community/mathlib/commit/2a28652)
feat(data/finset/basic): add filter_erase ([#10384](https://github.com/leanprover-community/mathlib/pull/10384))
Like `filter_insert`, but for `erase`

### [2021-11-20 21:22:54](https://github.com/leanprover-community/mathlib/commit/32c0507)
feat(data/nat/interval): add Ico_succ_left_eq_erase ([#10386](https://github.com/leanprover-community/mathlib/pull/10386))
Adds `Ico_succ_left_eq_erase`. Also adds a few order lemmas needed for this.
See [this discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Ico_succ_left_eq_erase_Ico/near/259180476)

### [2021-11-20 13:22:08](https://github.com/leanprover-community/mathlib/commit/b3538bf)
feat(topology/algebra/infinite_sum): add `has_sum.smul_const` etc ([#10393](https://github.com/leanprover-community/mathlib/pull/10393))
Rename old `*.smul` to `*.const_smul`.

### [2021-11-20 11:30:32](https://github.com/leanprover-community/mathlib/commit/618447f)
feat(analysis/special_functions/complex/arg): review, golf, lemmas ([#10365](https://github.com/leanprover-community/mathlib/pull/10365))
* add `|z| * exp (arg z * I) = z`;
* reorder theorems to help golfing;
* prove formulas for `arg z` in terms of `arccos (re z / abs z)` in cases `0 < im z` and `im z < 0`;
* use them to golf continuity of `arg`.

### [2021-11-20 02:42:14](https://github.com/leanprover-community/mathlib/commit/bd6c6d5)
chore(scripts): update nolints.txt ([#10391](https://github.com/leanprover-community/mathlib/pull/10391))
I am happy to remove some nolints for you!

### [2021-11-19 15:45:43](https://github.com/leanprover-community/mathlib/commit/db926f0)
chore(category_theory/limits/shapes/pullbacks): fix diagrams in docs ([#10379](https://github.com/leanprover-community/mathlib/pull/10379))

### [2021-11-19 14:34:11](https://github.com/leanprover-community/mathlib/commit/7638fe2)
doc(topology/separation): two typos ([#10382](https://github.com/leanprover-community/mathlib/pull/10382))

### [2021-11-19 12:03:57](https://github.com/leanprover-community/mathlib/commit/e8858fd)
refactor(algebra/opposites): use mul_opposite for multiplicative opposite ([#10302](https://github.com/leanprover-community/mathlib/pull/10302))
Split out `mul_opposite` from `opposite`, to leave room for an `add_opposite` in future.
Multiplicative opposites are now spelt `Aᵐᵒᵖ` instead of `Aᵒᵖ`. `Aᵒᵖ` now refers to the categorical opposite.

### [2021-11-19 10:10:47](https://github.com/leanprover-community/mathlib/commit/d6814c5)
feat(*): Reduce imports to only those necessary in the entire library ([#10349](https://github.com/leanprover-community/mathlib/pull/10349))
We reduce imports of many files in the library to only those actually needed by the content of the file, this is done by inspecting the declarations and attributes used by declarations in a file, and then computing a minimal set of imports that includes all of the necessary content. (A tool to do this was written by @jcommelin and I for this purpose).
The point of doing this is to reduce unnecessary recompilation when files that aren't needed for some file higher up the import graph are changed and everything in between gets recompiled. 
Another side benefit might be slightly faster simp / library_searches / tc lookups in some files as there may be less random declarations in the environment that aren't too relevant to the file.
The exception is that we do not remove any tactic file imports (in this run at least) as that requires more care to get right.
We also skip any `default.lean` files as the point of these is to provide a convenient way of importing a large chunk of the library (though arguably no mathlib file should import a default file that has no non-import content).
Some OLD statistics (not 100% accurate as several things changed since then):
The average number of imports of each file in the library reduces by around 2, (this equals the average number of dependencies of each file) raw numbers are `806748 / 2033` (total number of transitive links/total number files before) to `802710 / 2033` (after)
The length of the longest chain of imports in mathlib decreases from 139 to 130.
The imports (transitively) removed from the most from other files are as follows (file, decrease in number of files importing):
```
data.polynomial.degree.trailing_degree 13
linear_algebra.quotient 13
ring_theory.principal_ideal_domain 13
data.int.gcd 14
data.polynomial.div 14
data.list.rotate 15
data.nat.modeq 15
data.fin.interval 17
data.int.interval 17
data.pnat.interval 17
```
The original script generated by an import-reducing tool is at https://github.com/alexjbest/dag-tools though I did clean up the output and some weirdness after running this script
In touched files the imports are put into alphabetical order, we tried not to touch too many files that don't have their imports changed, but some were in the many merges and iterations on this.
There are a couple of changes to mathlib not to an import line (compared to master) that I couldn't resist doing that became apparent when the tool recommended deletions of imports containing named simp lemmas in the file, that weren't firing and so the tool was right to remove the import.
Another sort of issue  is discussed in https://github.com/leanprover-community/mathlib/blob/master/src/algebraic_geometry/presheafed_space/has_colimits.lean#L253, this is discussed at https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Reordering.20ext.20lemmas/near/261581547 and there seems to be currently no good way to avoid this so we just fix the proof. One can verify this with the command ` git diff origin/master -I import`
At a later point we hope to modify this tooling to suggest splits in long files by their prerequisites, but getting the library into a more minimal state w.r.t file imports seems to be important for such a tool to work well.

### [2021-11-19 08:56:27](https://github.com/leanprover-community/mathlib/commit/5000fb0)
feat(data/polynomial/eval): is_root_(prod/map) ([#10360](https://github.com/leanprover-community/mathlib/pull/10360))

### [2021-11-19 08:01:42](https://github.com/leanprover-community/mathlib/commit/784fe06)
feat(analysis/calculus/deriv): generalize lemmas about deriv and `smul` ([#10378](https://github.com/leanprover-community/mathlib/pull/10378))
Allow scalar multiplication by numbers from a different field.

### [2021-11-18 21:48:21](https://github.com/leanprover-community/mathlib/commit/f3f4442)
feat(logic/basic): define exists_unique_eq as a simp lemma ([#10364](https://github.com/leanprover-community/mathlib/pull/10364))

### [2021-11-18 20:52:43](https://github.com/leanprover-community/mathlib/commit/d5d2c4f)
feat(field_theory/splitting_field): add a more general algebra instance as a def ([#10220](https://github.com/leanprover-community/mathlib/pull/10220))
Unfortunately this def results in the following non-defeq diamonds in `splitting_field_aux.algebra` and `splitting_field.algebra`:
```lean
example
  (n : ℕ) {K : Type u} [field K] {f : polynomial K} (hfn : f.nat_degree = n) :
    (add_comm_monoid.nat_module : module ℕ (splitting_field_aux n f hfn)) =
  @algebra.to_module _ _ _ _ (splitting_field_aux.algebra n _ hfn) :=
rfl --fail
example : (add_comm_group.int_module _ : module ℤ (splitting_field_aux n f hfn)) =
  @algebra.to_module _ _ _ _ (splitting_field_aux.algebra f) :=
rfl --fail
```
For this reason, we do not make `splitting_field.algebra` an instance by default. The `splitting_field_aux.algebra` instance is less harmful as it is an implementation detail.
However, the new def is still perfectly good for recovering the old less-general instance, and avoids the need for `restrict_scalars.algebra`.

### [2021-11-18 17:07:15](https://github.com/leanprover-community/mathlib/commit/9654071)
feat(topology/algebra/module): add `is_scalar_tower` and `smul_comm_class` instances for `continuous_linear_map` ([#10375](https://github.com/leanprover-community/mathlib/pull/10375))
Also generalize some instances about `smul`.

### [2021-11-18 15:50:36](https://github.com/leanprover-community/mathlib/commit/0d09e99)
feat(measure_theory/integral/{set_to_l1,bochner}): generalize results about integrals to `set_to_fun` ([#10369](https://github.com/leanprover-community/mathlib/pull/10369))
The Bochner integral is a particular case of the `set_to_fun` construction. We generalize some lemmas which were proved for integrals to `set_to_fun`, notably the Lebesgue dominated convergence theorem.

### [2021-11-18 14:41:58](https://github.com/leanprover-community/mathlib/commit/0ededd5)
chore(analysis/calculus): use `is_R_or_C` in several lemmas ([#10376](https://github.com/leanprover-community/mathlib/pull/10376))

### [2021-11-18 12:48:11](https://github.com/leanprover-community/mathlib/commit/198ed6b)
doc(order/monotone): fix 2 typos ([#10377](https://github.com/leanprover-community/mathlib/pull/10377))

### [2021-11-18 02:36:10](https://github.com/leanprover-community/mathlib/commit/2f3b185)
chore(scripts): update nolints.txt ([#10374](https://github.com/leanprover-community/mathlib/pull/10374))
I am happy to remove some nolints for you!

### [2021-11-17 19:11:23](https://github.com/leanprover-community/mathlib/commit/f8cbb3e)
chore(.docker): don't install unnecessary toolchains ([#10363](https://github.com/leanprover-community/mathlib/pull/10363))

### [2021-11-17 19:11:22](https://github.com/leanprover-community/mathlib/commit/5d1363e)
feat(data/nat/parity): add lemmas ([#10352](https://github.com/leanprover-community/mathlib/pull/10352))
From FLT-regular.

### [2021-11-17 18:15:31](https://github.com/leanprover-community/mathlib/commit/276ab17)
feat(linear_algebra/bilinear_form): add lemmas ([#10353](https://github.com/leanprover-community/mathlib/pull/10353))
From FLT-regular.

### [2021-11-17 15:37:37](https://github.com/leanprover-community/mathlib/commit/6f793bb)
chore(measure_theory/group/basic): drop measurability assumption ([#10367](https://github.com/leanprover-community/mathlib/pull/10367))

### [2021-11-17 14:46:00](https://github.com/leanprover-community/mathlib/commit/e14e87a)
chore(category_theory/filtered): slightly golf two proofs ([#10368](https://github.com/leanprover-community/mathlib/pull/10368))

### [2021-11-17 09:02:09](https://github.com/leanprover-community/mathlib/commit/c7441af)
feat(linear_algebra/bilinear_form): add lemmas about congr ([#10362](https://github.com/leanprover-community/mathlib/pull/10362))
With these some of the `nondegenerate` proofs can be golfed to oblivion, rather than reproving variants of the same statement over and over again.

### [2021-11-17 09:02:08](https://github.com/leanprover-community/mathlib/commit/568435c)
chore(analysis/inner_product_space/projection): typeclass inference for completeness ([#10357](https://github.com/leanprover-community/mathlib/pull/10357))
As of [#5408](https://github.com/leanprover-community/mathlib/pull/5408), most lemmas about orthogonal projection onto a subspace `K` / reflection through a subspace `K` / orthogonal complement of `K` which require `K` to be complete phrase this in terms of `complete_space K` rather than `is_complete K`, so that it can be found by typeclass inference.  A few still used the old way; this PR completes the switch.

### [2021-11-17 09:02:07](https://github.com/leanprover-community/mathlib/commit/d5c2b34)
chore(analysis/mean_inequalities): split mean_inequalities into two files ([#10355](https://github.com/leanprover-community/mathlib/pull/10355))
This PR puts all results related to power functions into a new file.
Currently, we prove convexity of `exp` and `pow`, then use those properties in `mean_inequalities`. I am refactoring some parts of the analysis library to reduce the use of derivatives. I want to prove convexity of exp without derivatives (in a future PR), prove Holder's inequality, then use it to prove the convexity of pow. This requires Holder's inequality to be in a file that does not use convexity of pow, hence the split.
I needed to change the proof of Holder's inequality since it used the generalized mean inequality (hence `pow`). I switched to the second possible proof mentioned in the file docstring.
I also moved some lemmas in `mean_inequalities` to have three main sections: AM-GM, then Young and a final section with Holder and Minkowski.

### [2021-11-17 09:02:05](https://github.com/leanprover-community/mathlib/commit/60363a4)
feat(finset/basic): Adding `list.to_finset_union` and `list.to_finset_inter` ([#10351](https://github.com/leanprover-community/mathlib/pull/10351))
Two tiny lemmas, matching their counterparts for `multiset`

### [2021-11-17 07:06:12](https://github.com/leanprover-community/mathlib/commit/8f6fd1b)
lint(*): curly braces linter ([#10280](https://github.com/leanprover-community/mathlib/pull/10280))
This PR:
1. Adds a style linter for curly braces: a line shall never end with `{` or start with `}` (modulo white space)
2. Adds `scripts/cleanup-braces.{sh,py}` to reflow lines that violate (1)
3. Runs the scripts from (2) to generate a boatload of changes in mathlib
4. Fixes one line that became to long due to (3)

### [2021-11-17 04:51:54](https://github.com/leanprover-community/mathlib/commit/2bdadb4)
feat(order/imp): define `lattice.imp` and `lattice.biimp` ([#10327](https://github.com/leanprover-community/mathlib/pull/10327))

### [2021-11-16 23:48:06](https://github.com/leanprover-community/mathlib/commit/0a2a922)
feat(combinatorics/set_family/shadow): Shadow of a set family ([#10223](https://github.com/leanprover-community/mathlib/pull/10223))
This defines `shadow 𝒜` where `𝒜 : finset (finset α))`.

### [2021-11-16 23:48:05](https://github.com/leanprover-community/mathlib/commit/7fec401)
feat(topology/metric_space/hausdorff_distance): add definition and lemmas about open thickenings of subsets ([#10188](https://github.com/leanprover-community/mathlib/pull/10188))
Add definition and basic API about open thickenings of subsets in metric spaces, in preparation for the portmanteau theorem on characterizations of weak convergence of Borel probability measures.

### [2021-11-16 21:57:02](https://github.com/leanprover-community/mathlib/commit/bce0ede)
feat(number_theory/divisors): mem_divisors_self ([#10359](https://github.com/leanprover-community/mathlib/pull/10359))
From flt-regular.

### [2021-11-16 21:57:00](https://github.com/leanprover-community/mathlib/commit/8f7971a)
refactor(linear_algebra/bilinear_form): Change namespace of is_refl, is_symm, and is_alt ([#10338](https://github.com/leanprover-community/mathlib/pull/10338))
The propositions `is_refl`, `is_symm`, and `is_alt` are now in the
namespace `bilin_form`. Moreover, `is_sym` is now renamed to `is_symm`.

### [2021-11-16 21:56:59](https://github.com/leanprover-community/mathlib/commit/698eb1e)
feat(data/fin/basic): add lemmas about fin.cast ([#10329](https://github.com/leanprover-community/mathlib/pull/10329))

### [2021-11-16 18:44:35](https://github.com/leanprover-community/mathlib/commit/9fa14a6)
feat(topology/uniform_space): properties of uniform convergence ([#9958](https://github.com/leanprover-community/mathlib/pull/9958))
* From the sphere eversion project
* multiple proofs were golfed by @PatrickMassot 
* Probably some proofs can be golfed quite heavily
Co-authored by: Patrick Massot <patrickmassot@free.fr>

### [2021-11-16 18:44:34](https://github.com/leanprover-community/mathlib/commit/d6b83d8)
feat(number_theory): define the class number ([#9071](https://github.com/leanprover-community/mathlib/pull/9071))
We instantiate the finiteness proof of the class group for rings of integers, and define the class number of a number field, or of a separable function field, as the finite cardinality of the class group.
Co-Authored-By: Ashvni <ashvni.n@gmail.com>
Co-Authored-By: Filippo A. E. Nuccio <filippo.nuccio@univ-st-etienne.fr>

### [2021-11-16 15:57:33](https://github.com/leanprover-community/mathlib/commit/f780788)
feat(dynamics): define `{mul,add}_action.is_minimal` ([#10311](https://github.com/leanprover-community/mathlib/pull/10311))

### [2021-11-16 12:48:56](https://github.com/leanprover-community/mathlib/commit/d36f17f)
feat(linear_algebra/sesquilinear_form): Add is_refl for sesq_form.is_alt ([#10341](https://github.com/leanprover-community/mathlib/pull/10341))
Lemma `is_refl` shows that an alternating sesquilinear form is reflexive.
Refactored `sesquilinear_form` in a similar way as `bilinear_form` will be in [#10338](https://github.com/leanprover-community/mathlib/pull/10338).

### [2021-11-16 12:48:55](https://github.com/leanprover-community/mathlib/commit/7f4b91b)
feat(linear_algebra/determinant): the determinant associated to the standard basis of the free module is the usual matrix determinant ([#10278](https://github.com/leanprover-community/mathlib/pull/10278))
Formalized as part of the Sphere Eversion project.

### [2021-11-16 12:48:54](https://github.com/leanprover-community/mathlib/commit/e20af15)
feat(field_theory): define the field of rational functions `ratfunc` ([#9563](https://github.com/leanprover-community/mathlib/pull/9563))
This PR defines `ratfunc K` as the field of rational functions over a field `K`, in terms of `fraction_ring (polynomial K)`. I have been careful to use `structure`s and `@[irreducible] def`s. Not only does that make for a nicer API, it also helps quite a bit with unification since the check can stop at `ratfunc` and doesn't have to start unfolding along the lines of `fraction_field.field → localization.comm_ring → localization.comm_monoid → localization.has_mul` and/or `polynomial.integral_domain → polynomial.comm_ring → polynomial.ring → polynomial.semiring`.
Most of the API is automatically derived from the (components of the) `is_fraction_ring` instance: the map `polynomial K → ratpoly K` is `algebra_map`, the isomorphism to `fraction_ring (polynomial K)` is `is_localization.alg_equiv`, ...
As a first application to verify that the definitions work, I rewrote `function_field` in terms of `ratfunc`.

### [2021-11-16 08:37:36](https://github.com/leanprover-community/mathlib/commit/f01399c)
chore(order/filter/basic): add 2 trivial `simp` lemmas ([#10344](https://github.com/leanprover-community/mathlib/pull/10344))

### [2021-11-16 08:37:35](https://github.com/leanprover-community/mathlib/commit/1181c99)
feat(algebra/order/archimedean): upgrade some `∃` to `∃!` ([#10343](https://github.com/leanprover-community/mathlib/pull/10343))

### [2021-11-16 06:43:17](https://github.com/leanprover-community/mathlib/commit/30abde6)
chore(*): clean up some unused open statements and extra simps ([#10342](https://github.com/leanprover-community/mathlib/pull/10342))
We clean up some specific statements that are essentially no-ops in the library, i.e. opening a namespace and then never using it and using a simp-set larger than actually needed.
This is a preparatory miscellany of small fixes for a larger PR upcoming from me and Johan to reduce imports in the library.
Hopefully merging this first will make the content of that PR clearer.

### [2021-11-16 04:55:57](https://github.com/leanprover-community/mathlib/commit/979f0e8)
feat(data/fin/basic): extract `div_nat`  and `mod_nat` from `fin_prod_fin_equiv` ([#10339](https://github.com/leanprover-community/mathlib/pull/10339))
This makes it a little easier to tell which component is div and which is mod from the docs alone, and also makes these available earlier than `data/equiv/fin`.

### [2021-11-16 03:17:25](https://github.com/leanprover-community/mathlib/commit/bd80b33)
chore(ring_theory/subring): fix stale docstring ([#10340](https://github.com/leanprover-community/mathlib/pull/10340))
Oversight from https://github.com/leanprover-community/mathlib/pull/10332

### [2021-11-16 02:30:50](https://github.com/leanprover-community/mathlib/commit/9264f30)
feat(analysis/calculus/times_cont_diff): continuous affine maps are smooth ([#10335](https://github.com/leanprover-community/mathlib/pull/10335))
Formalized as part of the Sphere Eversion project.

### [2021-11-16 00:29:07](https://github.com/leanprover-community/mathlib/commit/bff69c9)
feat(data/nat/lattice): add ```Inf_add``` lemma  ([#10008](https://github.com/leanprover-community/mathlib/pull/10008))
Adds a lemma about Inf on natural numbers. It will be needed for the count PR.

### [2021-11-16 00:29:05](https://github.com/leanprover-community/mathlib/commit/ddb6c75)
feat(algebra/homology/exact): preadditive.exact_iff_exact_of_iso ([#9979](https://github.com/leanprover-community/mathlib/pull/9979))

### [2021-11-15 22:46:44](https://github.com/leanprover-community/mathlib/commit/9074095)
chore(linear_algebra/pi_tensor_product): add reindex_reindex ([#10336](https://github.com/leanprover-community/mathlib/pull/10336))

### [2021-11-15 22:46:43](https://github.com/leanprover-community/mathlib/commit/a0f2c47)
feat(logic/relation): induction principles for `trans_gen` ([#10331](https://github.com/leanprover-community/mathlib/pull/10331))
Corresponding induction principles already exist for `refl_trans_gen`.

### [2021-11-15 22:46:41](https://github.com/leanprover-community/mathlib/commit/65ff54c)
feat(data/fintype/basic): add fin_injective ([#10330](https://github.com/leanprover-community/mathlib/pull/10330))

### [2021-11-15 21:01:46](https://github.com/leanprover-community/mathlib/commit/93047c5)
feat(linear_algebra/determinant): linear coordinates are ratio of determinants ([#10261](https://github.com/leanprover-community/mathlib/pull/10261))
Formalized as part of the Sphere Eversion project.

### [2021-11-15 21:01:45](https://github.com/leanprover-community/mathlib/commit/7ccc7ae)
feat(topology/homotopy/fundamental_groupoid): The functor from `Top` to `Groupoid` ([#10195](https://github.com/leanprover-community/mathlib/pull/10195))
I have no idea if the ways I've done things is the right way, eg. I don't know if I need to be thinking about universes when defining the functor, so comments about that are definitely welcome.

### [2021-11-15 21:01:44](https://github.com/leanprover-community/mathlib/commit/9c03e9d)
feat(data/fintype): computable trunc bijection from fin ([#10141](https://github.com/leanprover-community/mathlib/pull/10141))
When a type `X` lacks decidable equality, there is still computably a bijection `fin (card X) -> X` using `trunc`.
Also, move `fintype.equiv_fin_of_forall_mem_list` to `list.nodup.nth_le_equiv_of_forall_mem_list`.

### [2021-11-15 19:12:05](https://github.com/leanprover-community/mathlib/commit/7b60768)
feat(ring_theory/subring): weaken typeclass assumption for `units.pos_subgroup` ([#10332](https://github.com/leanprover-community/mathlib/pull/10332))

### [2021-11-15 19:12:03](https://github.com/leanprover-community/mathlib/commit/7803884)
feat(data/pi): Composition of addition/subtraction/... of functions ([#10305](https://github.com/leanprover-community/mathlib/pull/10305))

### [2021-11-15 19:12:01](https://github.com/leanprover-community/mathlib/commit/43ef578)
feat(category_theory/limits): Random results about limits. ([#10285](https://github.com/leanprover-community/mathlib/pull/10285))

### [2021-11-15 19:11:58](https://github.com/leanprover-community/mathlib/commit/1a47cfc)
feat(data/finset/basic): A finset has card two iff it's `{x, y}` for some `x ≠ y` ([#10252](https://github.com/leanprover-community/mathlib/pull/10252))
and the similar result for card three. Dumb but surprisingly annoying!

### [2021-11-15 19:11:56](https://github.com/leanprover-community/mathlib/commit/9fe0cbc)
feat(category_theory/preadditive/additive_functor): map_zero' is a redundant field, remove it ([#10229](https://github.com/leanprover-community/mathlib/pull/10229))
The map_zero' field in the definition of an additive functor can be deduced from the map_add' field. So we remove it.

### [2021-11-15 17:27:15](https://github.com/leanprover-community/mathlib/commit/64418d7)
fix(logic/basic): remove `noncomputable lemma` ([#10292](https://github.com/leanprover-community/mathlib/pull/10292))
It's been three years since this was discussed according to the zulip archive link in the library note.
According to CI, the reason is no longer relevant. Leaving these as `noncomputable lemma` is harmful as it results in non-defeq instance diamonds sometimes as lean was not able to unfold the lemmas to get to the data underneath.
Since these are now `def`s, the linter requires them to have docstrings.

### [2021-11-15 17:27:13](https://github.com/leanprover-community/mathlib/commit/d5d6071)
chore(analysis/special_functions/trigonometric/arctan): put lemmas about derivatives into a new file ([#10157](https://github.com/leanprover-community/mathlib/pull/10157))

### [2021-11-15 16:52:02](https://github.com/leanprover-community/mathlib/commit/02100d8)
feat(category_theory/sites/limits): `Sheaf J D` has colimits. ([#10334](https://github.com/leanprover-community/mathlib/pull/10334))
We show that the category of sheaves has colimits obtained by sheafifying colimits on the level of presheaves.

### [2021-11-15 14:41:25](https://github.com/leanprover-community/mathlib/commit/bf06854)
feat(algebra/big_operators/basic): Sum over a product of finsets, right version ([#10124](https://github.com/leanprover-community/mathlib/pull/10124))
This adds `finset.sum_prod_right` and renames `finset.sum_prod` to `finset.sum_prod_left`.

### [2021-11-15 12:56:47](https://github.com/leanprover-community/mathlib/commit/ca5c4b3)
feat(group_theory/group_action): add a few instances ([#10310](https://github.com/leanprover-community/mathlib/pull/10310))
* regular and opposite regular actions of a group on itself are transitive;
* the action of a group on an orbit is transitive.

### [2021-11-15 10:57:56](https://github.com/leanprover-community/mathlib/commit/ca61dbf)
feat(order/sup_indep): Finite supremum independence ([#9867](https://github.com/leanprover-community/mathlib/pull/9867))
This defines supremum independence of indexed finsets.

### [2021-11-15 08:05:28](https://github.com/leanprover-community/mathlib/commit/60bc370)
feat(category_theory/sites/limits): `Sheaf_to_presheaf` creates limits ([#10328](https://github.com/leanprover-community/mathlib/pull/10328))
As a consequence, we obtain that sheaves have limits (of a given shape) when the target category does, and that these limit sheaves are computed on each object of the site "pointwise".

### [2021-11-15 05:07:52](https://github.com/leanprover-community/mathlib/commit/189e066)
feat(category_theory/sites/sheafification): The sheafification of a presheaf. ([#10303](https://github.com/leanprover-community/mathlib/pull/10303))
We construct the sheafification of a presheaf `P` taking values in a concrete category `D` with enough (co)limits, where the forgetful functor preserves the appropriate (co)limits and reflects isomorphisms.
We follow the construction on the stacks project https://stacks.math.columbia.edu/tag/00W1
**Note:** There are two very long proofs here, so I added several comments explaining what's going on.

### [2021-11-15 04:19:49](https://github.com/leanprover-community/mathlib/commit/62992fa)
feat(analysis/inner_product_space/spectrum): more concrete diagonalization theorem ([#10317](https://github.com/leanprover-community/mathlib/pull/10317))
This is a second version of the diagonalization theorem for self-adjoint operators on finite-dimensional inner product spaces, stating that a self-adjoint operator admits an orthonormal basis of eigenvectors, and deducing the standard consequences (when expressed with respect to this basis the operator acts diagonally).
I have also updated `undergrad.yaml` and `overview.yaml` to cover the diagonalization theorem and other things proved in the library about Hilbert spaces.

### [2021-11-14 20:27:17](https://github.com/leanprover-community/mathlib/commit/0c8f53e)
feat(linear_algebra/trace): add lemmas about trace of linear maps ([#10279](https://github.com/leanprover-community/mathlib/pull/10279))
Lemmas for the trace of the identity and the trace of a conjugation

### [2021-11-14 18:03:48](https://github.com/leanprover-community/mathlib/commit/1b51fe0)
feat(linear_algebra/alternating): add alternating_map.comp_linear_map ([#10314](https://github.com/leanprover-community/mathlib/pull/10314))

### [2021-11-14 17:03:13](https://github.com/leanprover-community/mathlib/commit/8728e85)
feat(measure_theory): drop some unneeded assumptions ([#10319](https://github.com/leanprover-community/mathlib/pull/10319))
Prove that for a nontrivial countably generated filter there exists a sequence that converges to this filter. Use this lemma to drop some assumptions.

### [2021-11-14 15:22:16](https://github.com/leanprover-community/mathlib/commit/5307dc1)
feat(data/equiv/module): add module.to_module_End ([#10300](https://github.com/leanprover-community/mathlib/pull/10300))
The new definitions are:
* `distrib_mul_action.to_module_End`
* `distrib_mul_action.to_module_aut`
* `module.to_module_End`
Everything else is a move.
This also moves the group structure on linear_equiv earlier in the import heirarchy.
This is more consistent with where it is for `linear_map`.

### [2021-11-14 15:22:15](https://github.com/leanprover-community/mathlib/commit/299af47)
chore(data/fin/basic): move tuple stuff to a new file ([#10295](https://github.com/leanprover-community/mathlib/pull/10295))
There are almost 600 lines of tuple stuff, which is definitely sufficient to justify a standalone file.
The author information has been guessed from the git history.
Floris is responsible for `cons` and `tail` which came first in [#1294](https://github.com/leanprover-community/mathlib/pull/1294), Chris added find, and Yury and Sébastien were involved all over the place.
This is simply a cut-and-paste job, with the exception of the new module docstring which has been merged with the docstring for the tuple subheading.

### [2021-11-14 15:22:14](https://github.com/leanprover-community/mathlib/commit/7dc33bf)
feat(data/nat/basic): Some `nat.find` lemmas ([#10263](https://github.com/leanprover-community/mathlib/pull/10263))
This proves `nat.find_le` and `nat.find_add` and renames the current `nat.find_le` to `nat.find_mono`.

### [2021-11-14 13:46:33](https://github.com/leanprover-community/mathlib/commit/dd72ebc)
feat(data/list/big_operators): When `list.sum` is strictly positive ([#10282](https://github.com/leanprover-community/mathlib/pull/10282))

### [2021-11-14 09:32:09](https://github.com/leanprover-community/mathlib/commit/bca8278)
feat(algebra/lie/basic): add missing `@[ext]` and `@[simp]` lemmas ([#10316](https://github.com/leanprover-community/mathlib/pull/10316))

### [2021-11-13 21:34:57](https://github.com/leanprover-community/mathlib/commit/3b5edd0)
refactor(set_theory/cardinal_ordinal): use TC assumptions instead of inequalities ([#10313](https://github.com/leanprover-community/mathlib/pull/10313))
Assume `[fintype α]` or `[infinite α]` instead of `#α < ω` or `ω ≤ #α`.

### [2021-11-13 19:05:20](https://github.com/leanprover-community/mathlib/commit/d8c8725)
feat(ring_theory,algebraic_geometry): Miscellaneous lemmas/def/typo corrections ([#10307](https://github.com/leanprover-community/mathlib/pull/10307))
Split out from [#9802](https://github.com/leanprover-community/mathlib/pull/9802) since I'm aiming at more general version.

### [2021-11-13 17:25:11](https://github.com/leanprover-community/mathlib/commit/ca56c5a)
feat(measure_theory/group): define a few `measurable_equiv`s ([#10299](https://github.com/leanprover-community/mathlib/pull/10299))

### [2021-11-13 16:06:16](https://github.com/leanprover-community/mathlib/commit/3578403)
feat(*/{group,mul}_action): more lemmas ([#10308](https://github.com/leanprover-community/mathlib/pull/10308))
* add several lemmas about orbits and pointwise scalar multiplication;
* generalize `mul_action.orbit.mul_action` to a monoid action;
* more lemmas about pretransitive actions, use `to_additive` more;
* add dot notation lemmas `is_open.smul` and `is_closed.smul`.

### [2021-11-13 14:24:59](https://github.com/leanprover-community/mathlib/commit/b91d344)
chore(data/equiv/*): rename `trans_symm` and `symm_trans` to `self_trans_symm` and `symm_trans_self`. ([#10309](https://github.com/leanprover-community/mathlib/pull/10309))
This frees up `symm_trans` to state `(a.trans b).symm = a.symm.trans b.symm`.
These names are consistent with `self_comp_symm` and `symm_comp_self`.

### [2021-11-13 10:27:54](https://github.com/leanprover-community/mathlib/commit/869cb32)
chore(measure_theory/probability_mass_function): Refactor the `pmf` file into a definitions file and a constructions file ([#10298](https://github.com/leanprover-community/mathlib/pull/10298))

### [2021-11-13 09:09:36](https://github.com/leanprover-community/mathlib/commit/a7e38a0)
feat(linear_algebra/bilinear_form): add is_refl and ortho_sym for alt_bilin_form ([#10304](https://github.com/leanprover-community/mathlib/pull/10304))
Lemma `is_refl` shows that every alternating bilinear form is reflexive.
Lemma `ortho_sym` shows that being orthogonal with respect to an alternating bilinear form is symmetric.

### [2021-11-13 02:46:06](https://github.com/leanprover-community/mathlib/commit/a232366)
feat(analysis/inner_product_space/projection): orthonormal basis subordinate to an `orthogonal_family` ([#10208](https://github.com/leanprover-community/mathlib/pull/10208))
In a finite-dimensional inner product space of `E`, there exists an orthonormal basis subordinate to a given direct sum decomposition into an `orthogonal_family` of subspaces `E`.

### [2021-11-12 23:21:30](https://github.com/leanprover-community/mathlib/commit/8bb0b6f)
feat(category_theory/sites/plus): If P is a sheaf, then the map from P to P^+ is an isomorphism. ([#10297](https://github.com/leanprover-community/mathlib/pull/10297))
Also adds some simple results about (co)limits where the morphisms in the diagram are isomorphisms.

### [2021-11-12 21:42:51](https://github.com/leanprover-community/mathlib/commit/55534c4)
feat(data/nat/basic): recursion for set nat ([#10273](https://github.com/leanprover-community/mathlib/pull/10273))
Adding a special case of `nat.le_rec_on` where the predicate is membership of a subset.

### [2021-11-12 20:02:20](https://github.com/leanprover-community/mathlib/commit/6afda88)
feat(analysis/inner_product_space/spectrum): diagonalization of self-adjoint endomorphisms (finite dimension) ([#9995](https://github.com/leanprover-community/mathlib/pull/9995))
Diagonalization of a self-adjoint endomorphism `T` of a finite-dimensional inner product space `E` over either `ℝ` or `ℂ`:  construct a linear isometry `T.diagonalization` from `E` to the direct sum of `T`'s eigenspaces, such that `T` conjugated by `T.diagonalization` is diagonal:
```lean
lemma diagonalization_apply_self_apply (v : E) (μ : eigenvalues T) :
  hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ
```

### [2021-11-12 17:48:18](https://github.com/leanprover-community/mathlib/commit/f0a9849)
feat(category_theory/sites/sheaf): Add sheaf conditions in terms of multiforks/multiequalizers. ([#10294](https://github.com/leanprover-community/mathlib/pull/10294))
Another PR toward sheafification.

### [2021-11-12 17:08:23](https://github.com/leanprover-community/mathlib/commit/adb5c2d)
chore(analysis/special_functions/trigonometric/complex): put results about derivatives into a new file ([#10156](https://github.com/leanprover-community/mathlib/pull/10156))

### [2021-11-12 16:30:34](https://github.com/leanprover-community/mathlib/commit/6262165)
feat(analysis/normed_space/continuous_affine_map): isometry from space of continuous affine maps to product of codomain with space of continuous linear maps ([#10201](https://github.com/leanprover-community/mathlib/pull/10201))
Formalized as part of the Sphere Eversion project.

### [2021-11-12 15:38:34](https://github.com/leanprover-community/mathlib/commit/b9f7b4d)
fix(algebra/graded_monoid): correct nonexistent names in tactic defaults ([#10293](https://github.com/leanprover-community/mathlib/pull/10293))
These were left by a bad rename by me in the past, and resulted in the default values not actually working.

### [2021-11-12 15:38:33](https://github.com/leanprover-community/mathlib/commit/d7b5ffa)
chore(linear_algebra/multilinear): add const_of_is_empty ([#10291](https://github.com/leanprover-community/mathlib/pull/10291))
This is extracted from `pi_tensor_product.is_empty_equiv`

### [2021-11-12 15:38:31](https://github.com/leanprover-community/mathlib/commit/c5027c9)
doc(field_theory/separable): typo ([#10290](https://github.com/leanprover-community/mathlib/pull/10290))

### [2021-11-12 15:04:38](https://github.com/leanprover-community/mathlib/commit/6cd6320)
feat(group_theory/complement): `is_complement'.sup_eq_top` ([#10230](https://github.com/leanprover-community/mathlib/pull/10230))
If `H` and `K` are complementary subgroups, then `H ⊔ K = ⊤`.

### [2021-11-12 12:24:46](https://github.com/leanprover-community/mathlib/commit/07be904)
doc(README): add list of emeritus maintainers ([#10288](https://github.com/leanprover-community/mathlib/pull/10288))

### [2021-11-12 11:49:22](https://github.com/leanprover-community/mathlib/commit/b51335c)
feat(category_theory/sites/plus): `P⁺` for a presheaf `P`. ([#10284](https://github.com/leanprover-community/mathlib/pull/10284))
This file adds the construction of `P⁺`, for a presheaf `P : Cᵒᵖ ⥤ D`, whenever `C` has a Grothendieck topology `J` and `D` has the appropriate (co)limits.
Later, we will show that `P⁺⁺` is the sheafification of `P`, under certain additional hypotheses on `D`.
See https://stacks.math.columbia.edu/tag/00W1

### [2021-11-12 10:27:58](https://github.com/leanprover-community/mathlib/commit/e679093)
feat(measure_theory): define `measurable_space` instance on a quotient ([#10275](https://github.com/leanprover-community/mathlib/pull/10275))

### [2021-11-12 09:37:57](https://github.com/leanprover-community/mathlib/commit/c45e70a)
chore(analysis/special_functions/pow): put lemmas about derivatives into a new file ([#10153](https://github.com/leanprover-community/mathlib/pull/10153))
In order to keep results about continuity of the power function in the original file, we prove some continuity results directly (these were previously proved using derivatives).

### [2021-11-12 07:59:47](https://github.com/leanprover-community/mathlib/commit/75207e9)
refactor(linear_algebra/eigenspace): refactor `eigenvectors_linearly_independent` ([#10198](https://github.com/leanprover-community/mathlib/pull/10198))
This refactors the proof of the lemma
```lean
lemma eigenvectors_linear_independent (f : End K V) (μs : set K) (xs : μs → V)
  (h_eigenvec : ∀ μ : μs, f.has_eigenvector μ (xs μ)) :
  linear_independent K xs
```
to extract the formulation
```lean
lemma eigenspaces_independent (f : End K V) : complete_lattice.independent f.eigenspace
```
from which `eigenvectors_linear_independent` follows as a 1-liner.
I don't need this for anything (although it might have applications -- for example, cardinality lemmas) -- just think it's a possibly more elegant statement.

### [2021-11-12 07:59:46](https://github.com/leanprover-community/mathlib/commit/1019dd6)
feat(measure_theory/probability_mass_function): Define a measure assosiated to a pmf ([#9966](https://github.com/leanprover-community/mathlib/pull/9966))
This PR defines `pmf.to_outer_measure` and `pmf.to_measure`, where the measure of a set is given by the total probability of elements of the set, and shows that this is a probability measure.

### [2021-11-12 07:25:31](https://github.com/leanprover-community/mathlib/commit/9e1e4f0)
feat(category_theory/sites/*): Dense subsite ([#9694](https://github.com/leanprover-community/mathlib/pull/9694))
Defined `cover_dense` functors as functors into sites such that each object can be covered by images of the functor.
Proved that for a `cover_dense` functor `G`, any morphisms of presheaves `G ⋙ ℱ ⟶ G ⋙ ℱ'` can be glued into a 
morphism `ℱ ⟶ ℱ'`.

### [2021-11-12 04:52:56](https://github.com/leanprover-community/mathlib/commit/6fd688b)
chore(measure_theory): move `mutually_singular` to a new file ([#10281](https://github.com/leanprover-community/mathlib/pull/10281))

### [2021-11-12 04:52:54](https://github.com/leanprover-community/mathlib/commit/d7e320e)
feat(category_theory/limits): Cone limiting iff terminal. ([#10266](https://github.com/leanprover-community/mathlib/pull/10266))

### [2021-11-12 03:51:22](https://github.com/leanprover-community/mathlib/commit/e5a79a7)
feat(analysis/normed_space/star): introduce C*-algebras ([#10145](https://github.com/leanprover-community/mathlib/pull/10145))
This PR introduces normed star rings/algebras and C*-rings/algebras, as well as a version of `star` bundled as a linear isometric equivalence.

### [2021-11-12 00:55:58](https://github.com/leanprover-community/mathlib/commit/d6056ee)
feat(field_theory/splitting_field): add eval_root_derivative_of_split ([#10224](https://github.com/leanprover-community/mathlib/pull/10224))
From flt-regular.

### [2021-11-12 00:19:41](https://github.com/leanprover-community/mathlib/commit/73b2b65)
feat(category_theory/limits/concrete_category): A lemma about concrete multiequalizers ([#10277](https://github.com/leanprover-community/mathlib/pull/10277))

### [2021-11-11 23:18:38](https://github.com/leanprover-community/mathlib/commit/0b4c540)
feat(field_theory/separable): X^n - 1 is separable iff ↑n ≠ 0. ([#9779](https://github.com/leanprover-community/mathlib/pull/9779))
Most of the proof actually due to @Vierkantor!

### [2021-11-11 19:35:48](https://github.com/leanprover-community/mathlib/commit/8cd5f0e)
chore(category_theory/isomorphisms): Adjust priority for is_iso.comp_is_iso ([#10276](https://github.com/leanprover-community/mathlib/pull/10276))
[See Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/iso.20to.20is_iso.20for.20types/near/261122457)
Given `f : X ≅ Y` with `X Y : Type u`, without this change, typeclass inference cannot deduce `is_iso f.hom` because `f.hom` is defeq to `(λ x, x) ≫ f.hom`, triggering a loop.

### [2021-11-11 19:35:47](https://github.com/leanprover-community/mathlib/commit/d686025)
feat(linear_algebra/pi_tensor_product): add subsingleton_equiv ([#10274](https://github.com/leanprover-community/mathlib/pull/10274))
This is useful for constructing the tensor product of a single module, which we will ultimately need to show an isomorphism to `tensor_algebra`.
This also refactors `pempty_equiv` to use `is_empty`, which probably didn't exist at the time. This eliminates a surprising universe variable that was parameterizing `pempty`.

### [2021-11-11 19:35:45](https://github.com/leanprover-community/mathlib/commit/f99d638)
feat(measure_theory): integral over a family of pairwise a.e. disjoint sets ([#10268](https://github.com/leanprover-community/mathlib/pull/10268))
Also golf a few proofs

### [2021-11-11 19:35:44](https://github.com/leanprover-community/mathlib/commit/12c868a)
refactor(group_theory/complement): Generalize `card_mul` to from subgroups to subsets ([#10264](https://github.com/leanprover-community/mathlib/pull/10264))
Adds `is_complement.card_mul`, which generalizes `is_complement'.card_mul`.

### [2021-11-11 19:35:42](https://github.com/leanprover-community/mathlib/commit/72ca0d3)
feat(linear_algebra/pi_tensor_prod): generalize actions and provide missing smul_comm_class and is_scalar_tower instance ([#10262](https://github.com/leanprover-community/mathlib/pull/10262))
Also squeezes some `simp`s.

### [2021-11-11 19:35:41](https://github.com/leanprover-community/mathlib/commit/c7f3e5c)
feat(group_theory/submonoid/membership): `exists_multiset_of_mem_closure` ([#10256](https://github.com/leanprover-community/mathlib/pull/10256))
Version of `exists_list_of_mem_closure` for `comm_monoid`.

### [2021-11-11 19:35:40](https://github.com/leanprover-community/mathlib/commit/9a30dcf)
feat(data/finset/pairwise): Interaction of `set.pairwise_disjoint` with `finset` ([#10244](https://github.com/leanprover-community/mathlib/pull/10244))
This proves a few results about `set.pairwise_disjoint` and `finset` that couldn't go `data.set.pairwise` because of cyclic imports.

### [2021-11-11 19:35:38](https://github.com/leanprover-community/mathlib/commit/820f8d7)
feat(group_theory/index): Index of `subgroup.map` ([#10232](https://github.com/leanprover-community/mathlib/pull/10232))
Proves `(H.map f).index = H.index`, assuming `function.surjective f` and `f.ker ≤ H`.

### [2021-11-11 19:35:37](https://github.com/leanprover-community/mathlib/commit/4b1a057)
feat(algebra/order/sub): An `add_group` has ordered subtraction ([#10225](https://github.com/leanprover-community/mathlib/pull/10225))
This wraps up `sub_le_iff_le_add` in an `has_ordered_sub` instance.

### [2021-11-11 19:35:36](https://github.com/leanprover-community/mathlib/commit/a9c3ab5)
feat(data/polynomial): assorted lemmas on division and gcd of polynomials ([#9600](https://github.com/leanprover-community/mathlib/pull/9600))
This PR provides a couple of lemmas involving the division and gcd operators of polynomials that I needed for [#9563](https://github.com/leanprover-community/mathlib/pull/9563). The ones that generalized to `euclidean_domain` and/or `gcd_monoid` are provided in the respective files.

### [2021-11-11 19:02:03](https://github.com/leanprover-community/mathlib/commit/01e7b20)
feat(analysis/subadditive): prove that, if u_n is subadditive, then u_n / n converges. ([#10258](https://github.com/leanprover-community/mathlib/pull/10258))

### [2021-11-11 14:48:45](https://github.com/leanprover-community/mathlib/commit/4df3cd7)
chore(analysis/special_functions/complex/log): move results about derivatives to a new file ([#10117](https://github.com/leanprover-community/mathlib/pull/10117))

### [2021-11-11 14:04:29](https://github.com/leanprover-community/mathlib/commit/6e268cd)
chore(probability_theory/notation): change `volume` to `measure_theory.measure.volume` ([#10272](https://github.com/leanprover-community/mathlib/pull/10272))

### [2021-11-11 13:22:36](https://github.com/leanprover-community/mathlib/commit/270c644)
feat(measure_theory): add `ae_measurable.sum_measure` ([#10271](https://github.com/leanprover-community/mathlib/pull/10271))
Also add a few supporting lemmas.

### [2021-11-11 11:44:13](https://github.com/leanprover-community/mathlib/commit/c062d9e)
feat(*): more bundled versions of `(fin 2 → α) ≃ (α × α)` ([#10214](https://github.com/leanprover-community/mathlib/pull/10214))
Also ensure that the inverse function uses vector notation when possible.

### [2021-11-11 10:26:15](https://github.com/leanprover-community/mathlib/commit/e4a882d)
feat(measure_theory): a file about null measurable sets/functions ([#10231](https://github.com/leanprover-community/mathlib/pull/10231))
* Move definitions and lemmas about `null_measurable` to a new file.
* Redefine, rename, review API.

### [2021-11-11 09:29:24](https://github.com/leanprover-community/mathlib/commit/d5964a9)
feat(measure_theory): `int.floor` etc are measurable ([#10265](https://github.com/leanprover-community/mathlib/pull/10265))
## API changes
### `algebra/order/archimedean`
* rename `rat.cast_floor` to `rat.floor_cast` to reflect the order of operations;
* same for `rat.cast_ceil` and `rat.cast_round`;
* add `rat.cast_fract`.
### `algebra/order/floor`
* add `@[simp]` to `nat.floor_eq_zero`;
* add `nat.floor_eq_iff'`, `nat.preimage_floor_zero`, and `nat.preimage_floor_of_ne_zero`;
* add `nat.ceil_eq_iff`, `nat.preimage_ceil_zero`, and `nat.preimage_ceil_of_ne_zero`;
* add `int.preimage_floor_singleton`;
* add `int.self_sub_floor`, `int.fract_int_add`, `int.preimage_fract`, `int.image_fract`;
* add `int.preimage_ceil_singleton`.
### `measure_theory/function/floor`
New file. Prove that the functions defined in `algebra.order.floor` are measurable.

### [2021-11-11 07:23:55](https://github.com/leanprover-community/mathlib/commit/8c1fa70)
feat(category_theory/limits/concrete_category): Some lemmas about filtered colimits ([#10270](https://github.com/leanprover-community/mathlib/pull/10270))
This PR adds some lemmas about (filtered) colimits in concrete categories which are preserved under the forgetful functor.
This will be used later for the sheafification construction.

### [2021-11-10 21:52:09](https://github.com/leanprover-community/mathlib/commit/dfa7363)
feat(analysis/normed_space/finite_dimension): finite-dimensionality of spaces of continuous linear map ([#10259](https://github.com/leanprover-community/mathlib/pull/10259))

### [2021-11-10 20:44:38](https://github.com/leanprover-community/mathlib/commit/3c2bc2e)
lint(scripts/lint-style.py): add indentation linter ([#10257](https://github.com/leanprover-community/mathlib/pull/10257))

### [2021-11-10 17:25:44](https://github.com/leanprover-community/mathlib/commit/6f10557)
refactor(order): order_{top,bot} as mixin ([#10097](https://github.com/leanprover-community/mathlib/pull/10097))
This changes `order_top α` / `order_bot α` to _require_ `has_le α` instead of _extending_ `partial_order α`.
As a result, `order_top` can be combined with other lattice typeclasses. This lends itself to more refactors downstream, such as phrasing lemmas that currently require orders/semilattices and top/bot to provide them as separate TC inference, instead of "bundled" classes like `semilattice_inf_top`.
This refactor also provides the basis for making more consistent the "extended" algebraic classes, like "e(nn)real", "enat", etc. Some proof terms for lemmas about `nnreal` and `ennreal` have been switched to rely on more direct coercions from the underlying non-extended type or other (semi)rings.
Modify `semilattice_{inf,sup}_{top,bot}` to not directly inherit from
`order_{top,bot}`. Instead, they are now extending from `has_{top,bot}`. Extending `order_{top,bot}` is now only possible is `has_le` is provided to the TC cache at `extends` declaration time, when using `old_structure_cmd true`. That is,
```
set_option old_structure_cmd true
class mnwe (α : Type u) extends semilattice_inf α, order_top α.
```
errors with
```
type mismatch at application
  @semilattice_inf.to_partial_order α top
term
  top
has type
  α
but is expected to have type
  semilattice_inf α
```
One can make this work through one of three ways:
No `old_structure_cmd`, which is unfriendly to the rest of the class hierarchy
Require `has_le` in `class mwe (α : Type u) [has_le α] extends semilattice_inf α, order_top α.`, which is unfriendly to the existing hierarchy and how lemmas are stated.
Provide an additional axiom on top of a "data-only" TC and have a low-priority instance:
```
class semilattice_inf_top (α : Type u) extends semilattice_inf α, has_top α :=
(le_top : ∀ a : α, a ≤ ⊤)
@[priority 100]
instance semilattice_inf_top.to_order_top : order_top α :=
{ top := ⊤,  le_top := semilattice_inf_top.le_top }
```
The third option is chosen in this refactor.
Pulled out from [#9891](https://github.com/leanprover-community/mathlib/pull/9891), without the semilattice refactor.

### [2021-11-10 16:26:10](https://github.com/leanprover-community/mathlib/commit/cd5cb44)
chore(set_theory/cardinal_ordinal): golf some proofs ([#10260](https://github.com/leanprover-community/mathlib/pull/10260))

### [2021-11-10 14:52:29](https://github.com/leanprover-community/mathlib/commit/8aadbcb)
feat(linear_algebra/*_algebra): add some simp lemmas about the algebra map and generators of free constructions ([#10247](https://github.com/leanprover-community/mathlib/pull/10247))
These are quite repetitive, but I'm not sure how to generalize

### [2021-11-10 14:52:28](https://github.com/leanprover-community/mathlib/commit/543fcef)
chore(algebra/group_power/lemmas): minimize imports ([#10246](https://github.com/leanprover-community/mathlib/pull/10246))
Most of these were imported transitively anyway, but `data.list.basic` is unneeded.

### [2021-11-10 14:52:26](https://github.com/leanprover-community/mathlib/commit/444b596)
doc(ring_theory/norm) `norm_eq_prod_embeddings` docstring ([#10242](https://github.com/leanprover-community/mathlib/pull/10242))

### [2021-11-10 14:52:24](https://github.com/leanprover-community/mathlib/commit/bbbefe4)
feat(measure_theory/constructions/{pi,prod}): drop some measurability assumptions ([#10241](https://github.com/leanprover-community/mathlib/pull/10241))
Some lemmas (most notably `prod_prod` and `pi_pi`) are true for non-measurable sets as well.

### [2021-11-10 14:52:23](https://github.com/leanprover-community/mathlib/commit/eadd440)
feat(group_theory/index): `card_mul_index` ([#10228](https://github.com/leanprover-community/mathlib/pull/10228))
Proves `nat.card H * H.index = nat.card G` as the special case of `K.relindex H * H.index = K.index` when `K = ⊥`.

### [2021-11-10 14:52:21](https://github.com/leanprover-community/mathlib/commit/2b57ee7)
fix(*): fix many indentation mistakes ([#10163](https://github.com/leanprover-community/mathlib/pull/10163))

### [2021-11-10 14:52:20](https://github.com/leanprover-community/mathlib/commit/f41854e)
feat(ring_theory/ideal/over): algebra structure on R/p → S/P for `P` lying over `p` ([#9858](https://github.com/leanprover-community/mathlib/pull/9858))
This PR shows `P` lies over `p` if there is an injective map completing the square `R/p ← R —f→ S → S/P`, and conversely that there is a (not necessarily injective, since `f` doesn't have to be) map completing the square if `P` lies over `p`. Then we specialize this to the case where `P = map f p` to provide an `algebra p.quotient (map f p).quotient` instance.
This algebra instance is useful if you want to study the extension `R → S` locally at `p`, e.g. to show `R/p : S/pS` has the same dimension as `Frac(R) : Frac(S)` if `p` is prime.

### [2021-11-10 14:52:18](https://github.com/leanprover-community/mathlib/commit/e1fea3a)
feat(ring_theory/ideal): the product and infimum of principal ideals ([#9852](https://github.com/leanprover-community/mathlib/pull/9852))
Three useful lemmas for applying the Chinese remainder theorem when an ideal is generated by one, non-prime, element.

### [2021-11-10 13:12:51](https://github.com/leanprover-community/mathlib/commit/bfd3a89)
doc(algebra/ring/basic): fix typo ([#10250](https://github.com/leanprover-community/mathlib/pull/10250))

### [2021-11-10 06:43:42](https://github.com/leanprover-community/mathlib/commit/18412ef)
feat(data/nat/cast): Cast of natural division is less than division of casts ([#10251](https://github.com/leanprover-community/mathlib/pull/10251))

### [2021-11-10 02:49:27](https://github.com/leanprover-community/mathlib/commit/3f173e1)
feat(group_theory/complement): iff-lemmas for when bottom and top subgroups are complementary ([#10143](https://github.com/leanprover-community/mathlib/pull/10143))
Adds iff lemmas for when bottom and top subgroups are complementary.

### [2021-11-09 23:52:35](https://github.com/leanprover-community/mathlib/commit/64289fe)
chore(group_theory/order_of_element): fix weird lemma name ([#10245](https://github.com/leanprover-community/mathlib/pull/10245))

### [2021-11-09 23:52:33](https://github.com/leanprover-community/mathlib/commit/10d3d25)
chore(set_theory/cardinal): fix name & reorder universes ([#10236](https://github.com/leanprover-community/mathlib/pull/10236))
* add `cardinal.lift_injective`, `cardinal.lift_eq_zero`;
* reorder universe arguments in `cardinal.lift_nat_cast` to match
`cardinal.lift` and `ulift`;
* rename `cardinal.nat_eq_lift_eq_iff` to `cardinal.nat_eq_lift_iff`;
* add `@[simp]` to `cardinal.lift_eq_zero`,
`cardinal.lift_eq_nat_iff`, and `cardinal.nat_eq_lift_iff`.

### [2021-11-09 23:52:32](https://github.com/leanprover-community/mathlib/commit/7bdb6b3)
feat(algebra/module/linear_map,linear_algebra/alternating,linear_algebra/multilinear/basic): no_zero_smul_divisors instances ([#10234](https://github.com/leanprover-community/mathlib/pull/10234))
Add `no_zero_smul_divisors` instances for linear, multilinear and alternating maps, given such instances for the codomain of the maps.
This also adds some missing `coe_smul` lemmas on these types.

### [2021-11-09 17:02:26](https://github.com/leanprover-community/mathlib/commit/a2810d9)
feat(data/int/basic): coercion subtraction inequality ([#10054](https://github.com/leanprover-community/mathlib/pull/10054))
Adding to simp a subtraction inequality over coercion from int to nat

### [2021-11-09 14:26:32](https://github.com/leanprover-community/mathlib/commit/35d574e)
feat(linear_algebra/determinant): alternating maps as multiples of determinant ([#10233](https://github.com/leanprover-community/mathlib/pull/10233))
Add the lemma that any alternating map with the same type as the
determinant map with respect to a basis is a multiple of the
determinant map (given by the value of the alternating map applied to
the basis vectors).

### [2021-11-09 10:46:44](https://github.com/leanprover-community/mathlib/commit/00d9b9f)
feast(ring_theory/norm): add norm_eq_prod_embeddings ([#10226](https://github.com/leanprover-community/mathlib/pull/10226))
We prove that the norm equals the product of the embeddings in an algebraically closed field.
Note that we follow a slightly different path than for the trace, since transitivity of the norm is more delicate, and we avoid it.
From flt-regular.

### [2021-11-09 09:20:22](https://github.com/leanprover-community/mathlib/commit/11ced18)
feat(algebra/lie/classical): Use computable matrix inverses where possible ([#10218](https://github.com/leanprover-community/mathlib/pull/10218))

### [2021-11-09 09:20:21](https://github.com/leanprover-community/mathlib/commit/8614615)
refactor(data/nat/interval): simp for Ico_zero_eq_range ([#10211](https://github.com/leanprover-community/mathlib/pull/10211))
This PR makes two changes: It refactors `nat.Ico_zero_eq_range` from `Ico 0 a = range a` to `Ico 0 = range`, and makes the lemma a simp lemma.
These changes feel good to me, but feel free to close this if this is not the direction we want to go with this lemma.

### [2021-11-09 07:29:49](https://github.com/leanprover-community/mathlib/commit/0b093e6)
feat(order/bounded_lattice): a couple of basic instances about with_bot still not having a top if the original preorder didn't and vice versa ([#10215](https://github.com/leanprover-community/mathlib/pull/10215))
Used in the flt-regular project.

### [2021-11-09 03:25:48](https://github.com/leanprover-community/mathlib/commit/6af6f67)
chore(scripts): update nolints.txt ([#10240](https://github.com/leanprover-community/mathlib/pull/10240))
I am happy to remove some nolints for you!

### [2021-11-09 03:25:47](https://github.com/leanprover-community/mathlib/commit/9d49c4a)
doc(data/finset/fold): fix typo ([#10239](https://github.com/leanprover-community/mathlib/pull/10239))

### [2021-11-09 03:25:45](https://github.com/leanprover-community/mathlib/commit/223f659)
chore(linear_algebra/basic): remove a duplicate proof, generalize map_span_le ([#10219](https://github.com/leanprover-community/mathlib/pull/10219))

### [2021-11-09 01:42:52](https://github.com/leanprover-community/mathlib/commit/424012a)
chore(*): bump to Lean 3.35.1 ([#10237](https://github.com/leanprover-community/mathlib/pull/10237))

### [2021-11-08 22:17:41](https://github.com/leanprover-community/mathlib/commit/440163b)
chore(topology/algebra/mul_action): define `has_continuous_vadd` using `to_additive` ([#10227](https://github.com/leanprover-community/mathlib/pull/10227))
Make additive version of the theory of `has_continuous_smul`, i.e., `has_continuous_vadd`, using `to_additive`.  I've been fairly conservative in adding `to_additive` tags -- I left them off lemmas that didn't seem like they'd be relevant for typical additive actions, like those about `units` or `group_with_zero`.
Also make `normed_add_torsor` an instance of `has_continuous_vadd` and use this to establish some of its continuity API.

### [2021-11-08 16:03:11](https://github.com/leanprover-community/mathlib/commit/2e4813d)
feat(linear_algebra/matrix/nonsingular_inverse): add invertible_equiv_det_invertible ([#10222](https://github.com/leanprover-community/mathlib/pull/10222))

### [2021-11-08 16:03:10](https://github.com/leanprover-community/mathlib/commit/1519cd7)
chore(set_theory/cardinal): more simp, fix LHS/RHS ([#10212](https://github.com/leanprover-community/mathlib/pull/10212))
While `coe (fintype.card α)` is a larger expression than `#α`, it allows us to compute the cardinality of a finite type provided that we have a `simp` lemma for `fintype.card α`. It also plays well with lemmas about coercions from `nat` and `cardinal.lift`.
* rename `cardinal.fintype_card` to `cardinal.mk_fintype`, make it a `@[simp]` lemma;
* deduce other cases (`bool`, `Prop`, `unique`, `is_empty`) from it;
* rename `cardinal.finset_card` to `cardinal.mk_finset`, swap LHS/RHS;
* rename `ordinal.fintype_card` to `ordinal.type_fintype`.

### [2021-11-08 16:03:09](https://github.com/leanprover-community/mathlib/commit/66dea29)
feat(analysis/convex/specific_functions): Strict convexity of `exp`, `log` and `pow` ([#10123](https://github.com/leanprover-community/mathlib/pull/10123))
This strictifies the results of convexity/concavity of `exp`/`log` and add the strict versions for `pow`, `zpow`, `rpow`.
I'm also renaming `convex_on_pow_of_even` to `even.convex_on_pow` for dot notation.

### [2021-11-08 16:03:08](https://github.com/leanprover-community/mathlib/commit/ef68f55)
feat(linear_algebra/multilinear/basis): multilinear maps on basis vectors ([#10090](https://github.com/leanprover-community/mathlib/pull/10090))
Add two versions of the fact that a multilinear map on finitely many
arguments is determined by its values on basis vectors.  The precise
requirements for each version follow from the results used in the
proof: `basis.ext_multilinear_fin` uses the `curry` and `uncurry`
results to deduce it from `basis.ext` and thus works for multilinear
maps on a family of modules indexed by `fin n`, while
`basis.ext_multilinear` works for an arbitrary `fintype` index type
but is limited to the case where the modules for all the arguments
(and the bases used for those modules) are the same, since it's
derived from the previous result using `dom_dom_congr` which only
handles the case where all the modules are the same.
This is in preparation for proving a corresponding result for
alternating maps, for which the case of all argument modules the same
suffices.
There is probably room for making results more general.

### [2021-11-08 14:15:15](https://github.com/leanprover-community/mathlib/commit/eb67834)
chore(ring_theory/noetherian): golf and generalize map_fg_of_fg ([#10217](https://github.com/leanprover-community/mathlib/pull/10217))

### [2021-11-08 14:15:14](https://github.com/leanprover-community/mathlib/commit/5ba41d8)
feat(algebra/direct_sum): specialize `submodule_is_internal.independent` to add_subgroup ([#10108](https://github.com/leanprover-community/mathlib/pull/10108))
This adds the lemmas `disjoint.map_order_iso` and `complete_lattice.independent.map_order_iso` (and `iff` versions), and uses them to transfer some results on `submodule`s to `add_submonoid`s and `add_subgroup`s.

### [2021-11-08 13:14:28](https://github.com/leanprover-community/mathlib/commit/0dabcb8)
chore(ring_theory/ideal/operations): relax the base ring of algebras from comm_ring to comm_semiring ([#10024](https://github.com/leanprover-community/mathlib/pull/10024))
This also tidies up some variables and consistently uses `B` instead of `S` for the second algebra.
One proof in `ring_theory/finiteness.lean` has to be redone because typeclass search times out where it previously did not.
Thankfully, the new proof is shorter anyway.

### [2021-11-08 11:43:24](https://github.com/leanprover-community/mathlib/commit/b4a5b01)
feat(data/finset/basic): add card_insert_eq_ite ([#10209](https://github.com/leanprover-community/mathlib/pull/10209))
Adds the lemma `card_insert_eq_ite` combining the functionality of `card_insert_of_not_mem` and `card_insert_of_mem`, analogous to how `card_erase_eq_ite`.

### [2021-11-08 11:43:23](https://github.com/leanprover-community/mathlib/commit/2fd6a77)
chore(algebra/algebra/basic): add `algebra.coe_linear_map` ([#10204](https://github.com/leanprover-community/mathlib/pull/10204))

### [2021-11-08 11:43:20](https://github.com/leanprover-community/mathlib/commit/4dd7eca)
feat(analysis/{seminorm, convex/specific_functions}): A seminorm is convex ([#10203](https://github.com/leanprover-community/mathlib/pull/10203))
This proves `seminorm.convex_on`, `convex_on_norm` (which is morally a special case of the former) and leverages it to golf `seminorm.convex_ball`.
This also fixes the explicitness of arguments of `convex_on.translate_left` and friends.

### [2021-11-08 11:43:19](https://github.com/leanprover-community/mathlib/commit/e44aa6e)
feat(linear_algebra/basic): some lemmas about span and restrict_scalars ([#10167](https://github.com/leanprover-community/mathlib/pull/10167))

### [2021-11-08 11:43:18](https://github.com/leanprover-community/mathlib/commit/fb0cfbd)
feat(measure_theory/measure/complex): define complex measures ([#10166](https://github.com/leanprover-community/mathlib/pull/10166))
Complex measures was defined to be a vector measure over ℂ without any API. This PR adds some basic definitions about complex measures and proves the complex version of the Lebesgue decomposition theorem.

### [2021-11-08 11:43:17](https://github.com/leanprover-community/mathlib/commit/e4a1e80)
feat(analysis/convex/combination): Convex hull of a `set.prod` and `set.pi` ([#10125](https://github.com/leanprover-community/mathlib/pull/10125))
This proves
* `(∀ i, convex 𝕜 (t i)) → convex 𝕜 (s.pi t)`
* `convex_hull 𝕜 (s.prod t) = (convex_hull 𝕜 s).prod (convex_hull 𝕜 t)`
* `convex_hull 𝕜 (s.pi t) = s.pi (convex_hull 𝕜 ∘ t)`

### [2021-11-08 11:43:16](https://github.com/leanprover-community/mathlib/commit/1fac00e)
feat(analysis): lemmas about `arg` and `exp_map_circle` ([#10066](https://github.com/leanprover-community/mathlib/pull/10066))

### [2021-11-08 11:43:15](https://github.com/leanprover-community/mathlib/commit/48abaed)
feat(analysis/special_functions/complex/arg): continuity of arg outside of the negative real half-line ([#9500](https://github.com/leanprover-community/mathlib/pull/9500))

### [2021-11-08 10:06:42](https://github.com/leanprover-community/mathlib/commit/32c8445)
split(data/list/*): split off `data.list.basic` ([#10164](https://github.com/leanprover-community/mathlib/pull/10164))
Killing the giants. This moves 700 lines off `data.list.basic` that were about
* `list.sum` and `list.product` into `data.list.big_operators`
* `list.countp` and `list.count` into `data.list.count`
* `list.sigma` and `list.prod` into `data.list.sigma_prod`

### [2021-11-08 08:27:27](https://github.com/leanprover-community/mathlib/commit/380d6ca)
chore(algebra/direct_sum/module): extract out common `variables` ([#10207](https://github.com/leanprover-community/mathlib/pull/10207))
Slight reorganization to extract out repeatedly-used variable declarations, and update module docstring.  No changes to the content.

### [2021-11-08 08:27:25](https://github.com/leanprover-community/mathlib/commit/bf242b7)
feat(algebra/order/with_zero): add le lemmas ([#10183](https://github.com/leanprover-community/mathlib/pull/10183))

### [2021-11-08 08:27:23](https://github.com/leanprover-community/mathlib/commit/e0aa9f0)
refactor(linear_algebra/matrix/nonsingular_inverse): clean up ([#10175](https://github.com/leanprover-community/mathlib/pull/10175))
This file is a mess, and switches back and forth between three different inverses, proving the same things over and over again.
This pulls all the `invertible` versions of these statements to the top, and uses them here and there to golf proofs.
The lemmas `nonsing_inv_left_right` and `nonsing_inv_right_left` are merged into a single lemma `mul_eq_one_comm`.
The lemma `inv_eq_nonsing_inv_of_invertible` has been renamed to `inv_of_eq_nonsing_inv`
This also adds two new lemmas `inv_of_eq` and `det_inv_of`, both of which have trivial proofs.

### [2021-11-08 08:27:21](https://github.com/leanprover-community/mathlib/commit/bc55cd7)
feat(archive/imo) : Add solution to IMO 1994 Q1 ([#10171](https://github.com/leanprover-community/mathlib/pull/10171))
IMO 1994 Q1

### [2021-11-08 08:27:20](https://github.com/leanprover-community/mathlib/commit/62f94ad)
feat(measure_theory/measurable_space): define `measurable_embedding` ([#10023](https://github.com/leanprover-community/mathlib/pull/10023))
This way we can generalize our theorems about `measurable_equiv` and `closed_embedding`s.

### [2021-11-08 06:58:20](https://github.com/leanprover-community/mathlib/commit/c50c2c3)
docs(algebra/big_operators): correct documentation for prod ([#10206](https://github.com/leanprover-community/mathlib/pull/10206))

### [2021-11-07 10:12:36](https://github.com/leanprover-community/mathlib/commit/ae98aad)
chore(measure_theory/measure): review API of `mutually_singular` ([#10186](https://github.com/leanprover-community/mathlib/pull/10186))

### [2021-11-07 09:34:49](https://github.com/leanprover-community/mathlib/commit/7a8a914)
refactor(measure_theory/function/l1_space): remove hypothesis ([#10185](https://github.com/leanprover-community/mathlib/pull/10185))
* from `tendsto_lintegral_norm_of_dominated_convergence`
* Missed this in [#10181](https://github.com/leanprover-community/mathlib/pull/10181)
* Add comment about the ability to weaker `bound_integrable`.

### [2021-11-07 05:17:04](https://github.com/leanprover-community/mathlib/commit/7d240ce)
chore(data/matrix/notation): split into 2 files ([#10199](https://github.com/leanprover-community/mathlib/pull/10199))
I want to use `![a, b]` notation in some files that don't need to import `data.matrix.basic`.

### [2021-11-06 22:22:28](https://github.com/leanprover-community/mathlib/commit/daac854)
feat(analysis/special_functions/log): Relating `log`-inequalities and `exp`-inequalities ([#10191](https://github.com/leanprover-community/mathlib/pull/10191))
This proves `log x ≤ y ↔ x ≤ exp y` and `x ≤ log y ↔ exp x ≤ y`.

### [2021-11-06 20:27:44](https://github.com/leanprover-community/mathlib/commit/169bb29)
feat(algebra/group/with_one): cleanup algebraic instances ([#10194](https://github.com/leanprover-community/mathlib/pull/10194))
This:
* adds a `has_neg (with_zero α)` instance which sends `0` to `0` and otherwise uses the underlying negation (and the same for `has_inv (with_one α)`).
* replaces the `has_div (with_zero α)`,  `has_pow (with_zero α) ℕ`, and `has_pow (with_zero α) ℤ` instances in order to produce better definitional properties than the previous default ones.

### [2021-11-06 20:27:43](https://github.com/leanprover-community/mathlib/commit/56a9228)
feat(analysis/normed_space/continuous_affine_map): define bundled continuous affine maps ([#10161](https://github.com/leanprover-community/mathlib/pull/10161))
I want to use the result the evaluation map `Hom(E, F) × E → F` is smooth in a category with continuous affine maps as morphisms. It is convenient to have a bundled type for this, despite the necessary boilerplate (proposed here).
Formalized as part of the Sphere Eversion project.

### [2021-11-06 20:27:42](https://github.com/leanprover-community/mathlib/commit/26c0c23)
feat(algebra/homology/image_to_kernel): homology.map_iso ([#9978](https://github.com/leanprover-community/mathlib/pull/9978))

### [2021-11-06 18:49:17](https://github.com/leanprover-community/mathlib/commit/f18278d)
chore(algebra/opposites): use `injective.*` constructors ([#10200](https://github.com/leanprover-community/mathlib/pull/10200))

### [2021-11-06 18:49:16](https://github.com/leanprover-community/mathlib/commit/38caa50)
feat(data/nat/basic): `a < a / b * b + b` ([#10193](https://github.com/leanprover-community/mathlib/pull/10193))

### [2021-11-06 18:49:15](https://github.com/leanprover-community/mathlib/commit/ebe7951)
feat(algebra/big_operators/order): Bound on a product from a pointwise bound ([#10190](https://github.com/leanprover-community/mathlib/pull/10190))
This proves `finset.le_prod_of_forall_le` which is the dual of `finset.prod_le_of_forall_le`.

### [2021-11-06 18:49:14](https://github.com/leanprover-community/mathlib/commit/be412c3)
fix(README): update specialties of maintainers ([#10086](https://github.com/leanprover-community/mathlib/pull/10086))

### [2021-11-06 18:15:19](https://github.com/leanprover-community/mathlib/commit/0c54c57)
feat(data/set/equitable): A singleton is equitable ([#10192](https://github.com/leanprover-community/mathlib/pull/10192))
Prove `set.subsingleton.equitable_on` and `set.equitable_on_singleton`.

### [2021-11-06 12:54:31](https://github.com/leanprover-community/mathlib/commit/af36f1a)
chore(algebra/group/ulift): use injective.* to define instances ([#10172](https://github.com/leanprover-community/mathlib/pull/10172))
Also rename `ulift.mul_equiv` to `mul_equiv.ulift` and add some
missing instances.

### [2021-11-06 11:24:11](https://github.com/leanprover-community/mathlib/commit/4b14ef4)
feat(data/fintype): instances for `infinite (α ⊕ β)` and `infinite (α × β)` ([#10196](https://github.com/leanprover-community/mathlib/pull/10196))

### [2021-11-06 09:47:22](https://github.com/leanprover-community/mathlib/commit/239bf05)
feat(data/list/basic): list products ([#10184](https://github.com/leanprover-community/mathlib/pull/10184))
Adding a couple of lemmas about list products. The first is a simpler variant of `head_mul_tail_prod'` in the case where the list is not empty.  The other is a variant of `list.prod_ne_zero` for `list ℕ`.

### [2021-11-06 08:31:55](https://github.com/leanprover-community/mathlib/commit/051cb61)
feat(data/sym/sym2): Induction on `sym2` ([#10189](https://github.com/leanprover-community/mathlib/pull/10189))
A few basics about `sym2` that were blatantly missing.

### [2021-11-06 02:12:53](https://github.com/leanprover-community/mathlib/commit/4341fff)
chore(set_theory/cardinal_ordinal): use notation ω ([#10197](https://github.com/leanprover-community/mathlib/pull/10197))

### [2021-11-05 23:39:17](https://github.com/leanprover-community/mathlib/commit/8174bd0)
feat(analysis/inner_product_space/rayleigh): Rayleigh quotient produces eigenvectors ([#9840](https://github.com/leanprover-community/mathlib/pull/9840))
Define `self_adjoint` for an operator `T` to mean `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.  (This doesn't require a definition of `adjoint`, although that will come soon.). Prove that a local extremum of the Rayleigh quotient of a self-adjoint operator on the unit sphere is an eigenvector, and use this to prove that in finite dimension a self-adjoint operator has an eigenvector.

### [2021-11-05 19:40:53](https://github.com/leanprover-community/mathlib/commit/6cd6975)
feat(order/lattice): add `inf_lt_sup` ([#10178](https://github.com/leanprover-community/mathlib/pull/10178))
Also add `inf_le_sup`, `lt_or_lt_iff_ne`, and `min_lt_max`.

### [2021-11-05 19:40:52](https://github.com/leanprover-community/mathlib/commit/85f6420)
feat(algebra/group/inj_surj): add `injective.monoid_pow` etc ([#10152](https://github.com/leanprover-community/mathlib/pull/10152))
Add versions of some constructors that take `pow`/`zpow`/`nsmul`/`zsmul` as explicit arguments.

### [2021-11-05 19:07:04](https://github.com/leanprover-community/mathlib/commit/d69501f)
feat(category_theory/limits/shapes/multiequalizer): Multi(co)equalizers ([#10169](https://github.com/leanprover-community/mathlib/pull/10169))
This PR adds another special shape to the limits library, which directly generalizes shapes for many other special limits (like pullbacks, equalizers, etc.).  A `multiequalizer` can be thought of an an equalizer of two maps between two products. This will be used later on in the context of sheafification.
I don't know if there is a standard name for the gadgets this PR introduces. I would be happy to change the names if needed.

### [2021-11-05 17:51:20](https://github.com/leanprover-community/mathlib/commit/cc59673)
chore(*complex*): add a few simp lemmas ([#10187](https://github.com/leanprover-community/mathlib/pull/10187))

### [2021-11-05 17:51:18](https://github.com/leanprover-community/mathlib/commit/a71bfdc)
feat(analysis/calculus/times_cont_diff): `equiv.prod_assoc` is smooth. ([#10165](https://github.com/leanprover-community/mathlib/pull/10165))
Formalized as part of the Sphere Eversion project.

### [2021-11-05 17:51:17](https://github.com/leanprover-community/mathlib/commit/d9a80ee)
refactor(data/multiset/locally_finite): Generalize `multiset.Ico` to locally finite orders ([#10031](https://github.com/leanprover-community/mathlib/pull/10031))
This deletes `data.multiset.intervals` entirely, redefines `multiset.Ico` using `locally_finite_order` and restores the lemmas in their correct generality:
* `multiset.Ico.map_add` → `multiset.map_add_left_Ico`, `multiset.map_add_right_Ico`
* `multiset.Ico.eq_zero_of_le` → `multiset.Ico_eq_zero_of_le `
* `multiset.Ico.self_eq_zero` → `multiset.Ico_self`
* `multiset.Ico.nodup` → `multiset.nodup_Ico`
* `multiset.Ico.mem` → `multiset.mem_Ico`
* `multiset.Ico.not_mem_top` → `multiset.right_not_mem_Ico`
* `multiset.Ico.inter_consecutive` → `multiset.Ico_inter_Ico_of_le`
* `multiset.Ico.filter_something` → `multiset.filter_Ico_something`
* `multiset.Ico.eq_cons` → `multiset.Ioo_cons_left`
* `multiset.Ico.succ_top` →`multiset.Ico_cons_right`
`open set multiset` now causes a (minor) clash. This explains the changes to `analysis.box_integral.divergence_theorem` and `measure_theory.integral.divergence_theorem`

### [2021-11-05 16:25:14](https://github.com/leanprover-community/mathlib/commit/5f5ce2b)
feat(combinatorics/simple_graph): adding simple_graph.support and mem_support / support_mono lemmas ([#10176](https://github.com/leanprover-community/mathlib/pull/10176))

### [2021-11-05 15:19:39](https://github.com/leanprover-community/mathlib/commit/8ac2fa0)
chore(linear_algebra/affine_space/affine_map): make `affine_map.coe_sub` true by definition ([#10182](https://github.com/leanprover-community/mathlib/pull/10182))
This makes life slightly easier in some work following on from https://github.com/leanprover-community/mathlib/pull/10161
Formalized as part of the Sphere Eversion project.

### [2021-11-05 15:19:38](https://github.com/leanprover-community/mathlib/commit/b22a7c7)
refactor(measure_theory/integral/bochner): remove superfluous hypothesis ([#10181](https://github.com/leanprover-community/mathlib/pull/10181))
* Remove hypothesis from `tendsto_integral_of_dominated_convergence` that was superfluous
* This results in simplifying some proofs, and removing some hypotheses from other lemmas
* Also remove some `ae_measurable` hypotheses for functions that were also assumed to be `integrable`.

### [2021-11-05 15:19:37](https://github.com/leanprover-community/mathlib/commit/88b4ce7)
feat(algebra/order/with_zero): add with_zero.linear_ordered_comm_grou… ([#10180](https://github.com/leanprover-community/mathlib/pull/10180))
…p_with_zero

### [2021-11-05 13:33:49](https://github.com/leanprover-community/mathlib/commit/b31af6d)
refactor(algebra/group): move `monoid.has_pow` etc to `algebra.group.defs` ([#10147](https://github.com/leanprover-community/mathlib/pull/10147))
This way we can state theorems about `pow`/`nsmul` using notation `^` and `•` right away.
Also move some `ext` lemmas to a new file and rewrite proofs using properties of `monoid_hom`s.

### [2021-11-05 10:08:26](https://github.com/leanprover-community/mathlib/commit/16af388)
feat(data/quot): add `quotient.lift₂_mk` ([#10173](https://github.com/leanprover-community/mathlib/pull/10173))

### [2021-11-05 08:27:18](https://github.com/leanprover-community/mathlib/commit/35d3628)
chore(data/bool): add `bool.lt_iff` ([#10179](https://github.com/leanprover-community/mathlib/pull/10179))

### [2021-11-05 06:48:59](https://github.com/leanprover-community/mathlib/commit/8991f28)
feat(measure_theory/covering/vitali_family): define Vitali families ([#10057](https://github.com/leanprover-community/mathlib/pull/10057))
Vitali families are families of sets (for instance balls around each point in vector spaces) that satisfy covering theorems. Their main feature is that differentiation of measure theorems hold along Vitali families. This PR is a stub defining Vitali families, and giving examples of them thanks to the Besicovitch and Vitali covering theorems.
The differentiation theorem is left for another PR.

### [2021-11-05 06:00:09](https://github.com/leanprover-community/mathlib/commit/6f9ec12)
doc(group_theory/sylow): Expand Frattini's argument docstring ([#10174](https://github.com/leanprover-community/mathlib/pull/10174))
Expands the docstring for Frattini's argument.

### [2021-11-05 02:24:22](https://github.com/leanprover-community/mathlib/commit/8490f2a)
chore(scripts): update nolints.txt ([#10177](https://github.com/leanprover-community/mathlib/pull/10177))
I am happy to remove some nolints for you!

### [2021-11-05 00:43:55](https://github.com/leanprover-community/mathlib/commit/41a820d)
feat(number_theory/lucas_primality): Add theorem for Lucas primality test ([#8820](https://github.com/leanprover-community/mathlib/pull/8820))
This is a PR for adding the [Lucas primality test](https://en.wikipedia.org/wiki/Lucas_primality_test) to mathlib. This tells us that a number `p` is prime when an element `a : zmod p` has order `p-1` .

### [2021-11-04 22:36:42](https://github.com/leanprover-community/mathlib/commit/d6a57f8)
feat(data/finset/prod): When `finset.product` is nonempty ([#10170](https://github.com/leanprover-community/mathlib/pull/10170))
and two lemmas about how it interacts with the union.

### [2021-11-04 22:36:40](https://github.com/leanprover-community/mathlib/commit/b064622)
feat(data/fin/interval): Cardinality of `finset.Ixi`/`finset.Iix` in `fin` ([#10168](https://github.com/leanprover-community/mathlib/pull/10168))
This proves `(Ici a).card = n + 1 - a`, `(Ioi a).card = n - a`, `(Iic b).card = b + 1`, `(Iio b).card = b` where `a b : fin (n + 1)` (and also `a b : ℕ` for the last two).

### [2021-11-04 22:36:39](https://github.com/leanprover-community/mathlib/commit/fab61c9)
chore(topology/continuous_function/bounded): add simple lemmas ([#10149](https://github.com/leanprover-community/mathlib/pull/10149))

### [2021-11-04 22:36:37](https://github.com/leanprover-community/mathlib/commit/466fd27)
feat(algebra/group_with_zero/basic): relax some commutativity assumptions ([#10075](https://github.com/leanprover-community/mathlib/pull/10075))
Moving some lemmas so they require group_with_zero instead of comm_group_with_zero, using the generalization linter.

### [2021-11-04 22:36:36](https://github.com/leanprover-community/mathlib/commit/ce0e058)
feat(data/equiv/mul_add): add lemmas about multiplication and addition on a group being bijective and finite cancel_monoid_with_zeros ([#10046](https://github.com/leanprover-community/mathlib/pull/10046))

### [2021-11-04 21:07:34](https://github.com/leanprover-community/mathlib/commit/773a7a4)
feat(analysis/ODE): prove Picard-Lindelöf/Cauchy-Lipschitz Theorem ([#9791](https://github.com/leanprover-community/mathlib/pull/9791))

### [2021-11-04 20:30:13](https://github.com/leanprover-community/mathlib/commit/74c27b2)
feat(topology/sheaves): Pullback of presheaf ([#9961](https://github.com/leanprover-community/mathlib/pull/9961))
Defined the pullback of a presheaf along a continuous map, and proved that it is adjoint to pushforwards
and it preserves stalks.

### [2021-11-04 18:49:13](https://github.com/leanprover-community/mathlib/commit/79eb934)
chore(data/mv_polynomial/basic): add `map_alg_hom_coe_ring_hom` ([#10158](https://github.com/leanprover-community/mathlib/pull/10158))

### [2021-11-04 18:49:11](https://github.com/leanprover-community/mathlib/commit/11439d8)
chore(algebra/direct_sum/internal): add missing simp lemmas ([#10154](https://github.com/leanprover-community/mathlib/pull/10154))
These previously weren't needed when these were `@[reducible] def`s as `simp` saw right through them.

### [2021-11-04 18:49:10](https://github.com/leanprover-community/mathlib/commit/828e100)
feat(data/finset/interval): `finset α` is a locally finite order ([#9963](https://github.com/leanprover-community/mathlib/pull/9963))

### [2021-11-04 17:11:43](https://github.com/leanprover-community/mathlib/commit/cf2ff03)
feat(group_theory/sylow): Sylow subgroups are nontrivial! ([#10144](https://github.com/leanprover-community/mathlib/pull/10144))
These lemmas (finally!) connect the work of @ChrisHughes24 with the recent definition of Sylow subgroups, to show that Sylow subgroups are actually nontrivial!

### [2021-11-04 17:11:42](https://github.com/leanprover-community/mathlib/commit/52cd445)
refactor(data/set/pairwise): Indexed sets as arguments to `set.pairwise_disjoint` ([#9898](https://github.com/leanprover-community/mathlib/pull/9898))
This will allow to express the bind operation: you can't currently express that the pairwise disjoint union of pairwise disjoint sets pairwise disjoint. Here's the corresponding statement with `finset.sup_indep` (defined in [#9867](https://github.com/leanprover-community/mathlib/pull/9867)):
```lean
lemma sup_indep.sup {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.sup g).sup_indep f :=
```
You currently can't do `set.pairwise_disjoint s (λ i, ⋃ x ∈ g i, f x)`.

### [2021-11-04 15:29:36](https://github.com/leanprover-community/mathlib/commit/5187a42)
feat(linear_algebra/affine_space/affine_map): decomposition of an affine map between modules as an equiv ([#10162](https://github.com/leanprover-community/mathlib/pull/10162))
Formalized as part of the Sphere Eversion project.

### [2021-11-04 15:29:34](https://github.com/leanprover-community/mathlib/commit/22ec295)
chore(data/set): lemmas about `disjoint` ([#10148](https://github.com/leanprover-community/mathlib/pull/10148))

### [2021-11-04 15:29:33](https://github.com/leanprover-community/mathlib/commit/69189d4)
split(data/finset/prod): split off `data.finset.basic` ([#10142](https://github.com/leanprover-community/mathlib/pull/10142))
Killing the giants. This moves `finset.product`, `finset.diag`, `finset.off_diag` to their own file, the theme being "finsets on `α × β`".
The copyright header now credits:
* Johannes Hölzl for ba95269a65a77c8ab5eae075f842fdad0c0a7aaf
* Mario Carneiro
* Oliver Nash for [#4502](https://github.com/leanprover-community/mathlib/pull/4502)

### [2021-11-04 13:04:54](https://github.com/leanprover-community/mathlib/commit/de79226)
feat(ring_theory/polynomial/basic): `polynomial.ker_map_ring_hom` and `mv_polynomial.ker_map` ([#10160](https://github.com/leanprover-community/mathlib/pull/10160))

### [2021-11-04 13:04:53](https://github.com/leanprover-community/mathlib/commit/2129d05)
chore(measure_theory/function/special_functions): import inner_product_space.basic instead of inner_product_space.calculus ([#10159](https://github.com/leanprover-community/mathlib/pull/10159))
Right now this changes almost nothing because other imports like `analysis.special_functions.pow` depend on calculus, but I am changing that in other PRs. `measure_theory/function/special_functions` will soon not depend on calculus at all.

### [2021-11-04 13:04:51](https://github.com/leanprover-community/mathlib/commit/b890836)
chore(analysis/calculus/times_cont_diff): rename `linear_isometry_map.times_cont_diff`; drop `_map` ([#10155](https://github.com/leanprover-community/mathlib/pull/10155))
I think the old name is a typo; the new name enables dot notation.

### [2021-11-04 13:04:50](https://github.com/leanprover-community/mathlib/commit/3cbe0fe)
feat(linear_algebra/matrix/nonsingular_inverse): determinant of inverse is inverse of determinant ([#10038](https://github.com/leanprover-community/mathlib/pull/10038))

### [2021-11-04 13:04:48](https://github.com/leanprover-community/mathlib/commit/17afc5c)
feat(topology/algebra/group_with_zero): continuity lemma for division ([#9959](https://github.com/leanprover-community/mathlib/pull/9959))
* This even applies when dividing by `0`.
* From the sphere eversion project.
* This PR mentions `filter.tendsto_prod_top_iff` which is added by [#9958](https://github.com/leanprover-community/mathlib/pull/9958)

### [2021-11-04 11:24:16](https://github.com/leanprover-community/mathlib/commit/211bdff)
feat(data/nat/choose/basic): add some inequalities showing that choose is monotonic in the first argument ([#10102](https://github.com/leanprover-community/mathlib/pull/10102))
From flt-regular

### [2021-11-04 11:24:14](https://github.com/leanprover-community/mathlib/commit/1f0d878)
feat(data/list): standardize list prefixes and suffixes ([#10052](https://github.com/leanprover-community/mathlib/pull/10052))

### [2021-11-04 11:24:13](https://github.com/leanprover-community/mathlib/commit/4c0b6ad)
feat(topology/homotopy/basic): add `homotopic` for `continuous_map`s. ([#9865](https://github.com/leanprover-community/mathlib/pull/9865))

### [2021-11-04 09:43:52](https://github.com/leanprover-community/mathlib/commit/d219e6b)
chore(data/equiv/mul_add): DRY ([#10150](https://github.com/leanprover-community/mathlib/pull/10150))
use `units.mul_left`/`units.mul_right` to define
`equiv.mul_left₀`/`equiv.mul_right₀`.

### [2021-11-04 09:43:51](https://github.com/leanprover-community/mathlib/commit/76ba1b6)
chore(ring_theory/finiteness): make `finite_presentation.{quotient,mv_polynomial}` protected ([#10091](https://github.com/leanprover-community/mathlib/pull/10091))
This lets us clean up some `_root_`s
This also golfs a proof

### [2021-11-04 07:56:27](https://github.com/leanprover-community/mathlib/commit/8658f40)
feat(algebra/group_power/order): Sign of an odd/even power without linearity ([#10122](https://github.com/leanprover-community/mathlib/pull/10122))
This proves that `a < 0 → 0 < a ^ bit0 n` and `a < 0 → a ^ bit1 n < 0` in an `ordered_semiring`.

### [2021-11-04 02:36:27](https://github.com/leanprover-community/mathlib/commit/4770a6a)
chore(scripts): update nolints.txt ([#10146](https://github.com/leanprover-community/mathlib/pull/10146))
I am happy to remove some nolints for you!

### [2021-11-04 00:15:53](https://github.com/leanprover-community/mathlib/commit/0fac080)
refactor(analysis/calculus/mean_value): Remove useless hypotheses ([#10129](https://github.com/leanprover-community/mathlib/pull/10129))
Because the junk value of `deriv` is `0`, assuming `∀ x, 0 < deriv f x` implies that `f` is derivable. We thus remove all those redundant derivability assumptions.

### [2021-11-03 22:10:14](https://github.com/leanprover-community/mathlib/commit/fed57b5)
refactor(algebra/direct_sum): rework internally-graded objects ([#10127](https://github.com/leanprover-community/mathlib/pull/10127))
This is a replacement for the `graded_ring.core` typeclass in [#10115](https://github.com/leanprover-community/mathlib/pull/10115), which is called `set_like.graded_monoid` here. The advantage of this approach is that we can use the same typeclass for graded semirings, graded rings, and graded algebras.
Largely, this change replaces a bunch of `def`s with `instances`, by bundling up the arguments to those defs to a new typeclass. This seems to make life easier for the few global `gmonoid` instance we already provide for direct sums of submodules, suggesting this API change is a useful one.
In principle the new `[set_like.graded_monoid A]` typeclass is useless, as the same effect can be achieved with `[set_like.has_graded_one A] [set_like.has_graded_mul A]`; pragmatically though this is painfully verbose, and probably results in larger term sizes. We can always remove it later if it causes problems.

### [2021-11-03 20:00:44](https://github.com/leanprover-community/mathlib/commit/6433c1c)
feat(group_theory/sylow): Sylow subgroups are isomorphic ([#10059](https://github.com/leanprover-community/mathlib/pull/10059))
Constructs `sylow.mul_equiv`.

### [2021-11-03 20:00:42](https://github.com/leanprover-community/mathlib/commit/5541b25)
refactor(group_theory/complement): Introduce abbreviation for subgroups ([#10009](https://github.com/leanprover-community/mathlib/pull/10009))
Introduces abbreviation for `is_complement (H : set G) (K : set G)`.

### [2021-11-03 17:56:43](https://github.com/leanprover-community/mathlib/commit/3a0b0d1)
chore(order/lattice): add `exists_lt_of_sup/inf` ([#10133](https://github.com/leanprover-community/mathlib/pull/10133))

### [2021-11-03 17:56:42](https://github.com/leanprover-community/mathlib/commit/8f7ffec)
chore(analysis/special_functions/trigonometric/inverse): move results about derivatives to a new file ([#10110](https://github.com/leanprover-community/mathlib/pull/10110))
This is part of a refactor of the `analysis/special_functions` folder, in which I will isolate all lemmas about derivatives. The result will be a definition of Lp spaces that does not import derivatives.

### [2021-11-03 17:56:41](https://github.com/leanprover-community/mathlib/commit/00a1022)
chore(logic/relation): rename to permit dot notation ([#10105](https://github.com/leanprover-community/mathlib/pull/10105))

### [2021-11-03 17:56:40](https://github.com/leanprover-community/mathlib/commit/6993e6f)
feat(measure_theory/constructions/borel_space): decomposing the measure of a set into slices ([#10096](https://github.com/leanprover-community/mathlib/pull/10096))
Also add the fact that `μ (to_measurable μ t ∩ s) = μ (t ∩ s)`, and useful variations around this fact.

### [2021-11-03 17:56:38](https://github.com/leanprover-community/mathlib/commit/b51f18f)
feat(topology): properties about intervals and paths ([#9914](https://github.com/leanprover-community/mathlib/pull/9914))
* From the sphere eversion project
* Properties about paths, the interval, and `proj_Icc`

### [2021-11-03 16:54:02](https://github.com/leanprover-community/mathlib/commit/8d52be4)
feat(measure_theory/function/ae_measurable_order): an ae measurability criterion for ennreal-valued functions ([#10072](https://github.com/leanprover-community/mathlib/pull/10072))

### [2021-11-03 16:10:04](https://github.com/leanprover-community/mathlib/commit/4f033b7)
feat(analysis/seminorm): define the Minkowski functional ([#9097](https://github.com/leanprover-community/mathlib/pull/9097))
This defines the gauge of a set, aka the Minkowski functional, in a vector space over a real normed field.

### [2021-11-03 14:39:55](https://github.com/leanprover-community/mathlib/commit/95cdeba)
doc(linear_algebra): fix wrong docstring ([#10139](https://github.com/leanprover-community/mathlib/pull/10139))

### [2021-11-03 14:39:53](https://github.com/leanprover-community/mathlib/commit/2b87435)
feat(ring_theory/trace): remove a useless assumption ([#10138](https://github.com/leanprover-community/mathlib/pull/10138))
We remove an assumption that is always true.

### [2021-11-03 14:39:52](https://github.com/leanprover-community/mathlib/commit/93cec25)
chore(*): replace `exact calc` by `calc` ([#10137](https://github.com/leanprover-community/mathlib/pull/10137))
This PR is the result of a sed script that replaces
* `exact calc` by `calc`
* `refine calc` by `calc`

### [2021-11-03 13:35:53](https://github.com/leanprover-community/mathlib/commit/eaf2a16)
fix(scripts/lint-style.py): typo in error reporting ([#10135](https://github.com/leanprover-community/mathlib/pull/10135))

### [2021-11-03 13:35:52](https://github.com/leanprover-community/mathlib/commit/1e7f3ca)
feat(data/zmod/basic): add nat_coe_eq_nat_coe_iff' ([#10128](https://github.com/leanprover-community/mathlib/pull/10128))
To match the int version, from flt-regular

### [2021-11-03 09:01:33](https://github.com/leanprover-community/mathlib/commit/e5c66a0)
chore(topology/continuous_function/bounded): add `comp_continuous` ([#10134](https://github.com/leanprover-community/mathlib/pull/10134))

### [2021-11-03 07:31:37](https://github.com/leanprover-community/mathlib/commit/e5acda4)
chore(order/conditionally_complete_lattice): drop an unneeded `nonempty` assumption ([#10132](https://github.com/leanprover-community/mathlib/pull/10132))

### [2021-11-03 02:56:05](https://github.com/leanprover-community/mathlib/commit/5f2e527)
chore(scripts): update nolints.txt ([#10130](https://github.com/leanprover-community/mathlib/pull/10130))
I am happy to remove some nolints for you!

### [2021-11-02 23:57:01](https://github.com/leanprover-community/mathlib/commit/123db5e)
feat(linear_algebra/determinant): basis.det_ne_zero ([#10126](https://github.com/leanprover-community/mathlib/pull/10126))
Add the trivial lemma that the determinant with respect to a basis is
not the zero map (if the ring is nontrivial).

### [2021-11-02 23:57:00](https://github.com/leanprover-community/mathlib/commit/86ed02f)
chore(algebra/order/floor): add a few trivial lemmas ([#10120](https://github.com/leanprover-community/mathlib/pull/10120))

### [2021-11-02 23:56:58](https://github.com/leanprover-community/mathlib/commit/1dec85c)
doc(topology): three module docstrings ([#10107](https://github.com/leanprover-community/mathlib/pull/10107))

### [2021-11-02 21:57:35](https://github.com/leanprover-community/mathlib/commit/d49636e)
doc(topology/open_subgroup): add module docstring ([#10111](https://github.com/leanprover-community/mathlib/pull/10111))
Also add a lattice instance.

### [2021-11-02 21:57:34](https://github.com/leanprover-community/mathlib/commit/70ed9dc)
chore(analysis/special_functions/trigonometric/basic): move results about derivatives to a new file ([#10109](https://github.com/leanprover-community/mathlib/pull/10109))
This is part of a refactor of the `analysis/special_functions` folder, in which I will isolate all lemmas about derivatives. The result will be a definition of Lp spaces that does not import derivatives.

### [2021-11-02 21:57:33](https://github.com/leanprover-community/mathlib/commit/d43daf0)
feat(algebra/big_operators/order): add unbundled is_absolute_value.sum_le and map_prod ([#10104](https://github.com/leanprover-community/mathlib/pull/10104))
Add unbundled versions of two existing lemmas.
Additionally generalize a few typeclass assumptions in an earlier file.
From the flt-regular project

### [2021-11-02 21:57:32](https://github.com/leanprover-community/mathlib/commit/3accc5e)
feat(data/bool): bnot_iff_not ([#10095](https://github.com/leanprover-community/mathlib/pull/10095))

### [2021-11-02 19:48:57](https://github.com/leanprover-community/mathlib/commit/00064bd)
feat(logic/relation): add equivalence.comap ([#10103](https://github.com/leanprover-community/mathlib/pull/10103))

### [2021-11-02 19:05:42](https://github.com/leanprover-community/mathlib/commit/2d8be73)
chore(measure_theory/probability_mass_function): avoid non-terminal simp in coe_le_one ([#10112](https://github.com/leanprover-community/mathlib/pull/10112))

### [2021-11-02 16:26:32](https://github.com/leanprover-community/mathlib/commit/6df3143)
chore(combinatorics/choose/bounds): move to nat namespace ([#10106](https://github.com/leanprover-community/mathlib/pull/10106))
There are module docstrings elsewhere that expect this to be in the `nat` namespace with the other `choose` lemmas.

### [2021-11-02 15:51:48](https://github.com/leanprover-community/mathlib/commit/0dcb184)
style(testing/slim_check): fix line length ([#10114](https://github.com/leanprover-community/mathlib/pull/10114))

### [2021-11-02 14:14:07](https://github.com/leanprover-community/mathlib/commit/796a051)
feat(measure_theory/decomposition/lebesgue): more on Radon-Nikodym derivatives ([#10070](https://github.com/leanprover-community/mathlib/pull/10070))
We show that the density in the Lebesgue decomposition theorem (aka the Radon-Nikodym derivative) is unique. Previously, uniqueness of the absolutely continuous part was known, but not of its density. We also show that the Radon-Nikodym derivative is almost everywhere finite. Plus some cleanup of the whole file.

### [2021-11-02 12:07:49](https://github.com/leanprover-community/mathlib/commit/da6706d)
feat(data/mv_polynomial/basic): lemmas about map ([#10092](https://github.com/leanprover-community/mathlib/pull/10092))
This adds `map_alg_hom`, which fills the gap between `map` and `map_alg_equiv`.
The only new proof here is `map_surjective`; everything else is just a reworked existing proof.

### [2021-11-02 10:26:34](https://github.com/leanprover-community/mathlib/commit/80dc445)
refactor(order/bounded_lattice): generalize le on with_{top,bot} ([#10085](https://github.com/leanprover-community/mathlib/pull/10085))
Before, some lemmas assumed `preorder` even when they were true for
just the underlying `le`. In the case of `with_bot`, the missing
underlying `has_le` instance is defined.
For both `with_{top,bot}`, a few lemmas are generalized accordingly.

### [2021-11-02 10:26:33](https://github.com/leanprover-community/mathlib/commit/658a3d7)
refactor(algebra/algebra): remove subalgebra.under ([#10081](https://github.com/leanprover-community/mathlib/pull/10081))
This removes `subalgebra.under`, and replaces `subalgebra.of_under` with `subalgebra.of_restrict_scalars`.
Lemmas associated with `under` have been renamed accordingly.

### [2021-11-02 10:26:32](https://github.com/leanprover-community/mathlib/commit/541df8a)
feat(topology/algebra/ordered/liminf_limsup): convergence of a sequence which does not oscillate infinitely ([#10073](https://github.com/leanprover-community/mathlib/pull/10073))
If, for all `a < b`, a sequence is not frequently below `a` and frequently above `b`, then it has to converge. This is a useful convergence criterion (called no upcrossings), used for instance in martingales.
Also generalize several statements on liminfs and limsups from complete linear orders to conditionally complete linear orders.

### [2021-11-02 10:26:31](https://github.com/leanprover-community/mathlib/commit/880182d)
chore(analysis/normed/group): add `cauchy_seq_finset_of_norm_bounded_eventually` ([#10060](https://github.com/leanprover-community/mathlib/pull/10060))
Add `cauchy_seq_finset_of_norm_bounded_eventually`, use it to golf some proofs.

### [2021-11-02 10:26:30](https://github.com/leanprover-community/mathlib/commit/fc12ca8)
feat(measure_theory/probability_mass_function): Define uniform pmf on an inhabited fintype ([#9920](https://github.com/leanprover-community/mathlib/pull/9920))
This PR defines uniform probability mass functions on nonempty finsets and inhabited fintypes.

### [2021-11-02 09:31:35](https://github.com/leanprover-community/mathlib/commit/f6894c4)
chore(ring_theory/adjoin/fg): generalize ring to semiring in a few places ([#10089](https://github.com/leanprover-community/mathlib/pull/10089))

### [2021-11-02 08:23:22](https://github.com/leanprover-community/mathlib/commit/26bdcac)
chore(coinductive_predicates): remove private and use of import_private ([#10084](https://github.com/leanprover-community/mathlib/pull/10084))
Remove a `private` modifier (I think this had previously been ported from core by @bryangingechen).
Then remove the only use of `import_private` from the library. (Besides another use in `tests/`, which we're not porting.)
(In mathlib4 we have `OpenPrivate` as an alternative. Removing `import_private` is one less thing for mathport to care about.)

### [2021-11-02 08:23:21](https://github.com/leanprover-community/mathlib/commit/1852840)
feat(analysis/calculus/mean_value): Strict convexity from derivatives ([#10034](https://github.com/leanprover-community/mathlib/pull/10034))
This duplicates all the results relating convex/concave function and their derivatives to strictly convex/strictly concave functions.

### [2021-11-02 06:43:08](https://github.com/leanprover-community/mathlib/commit/6d2af9a)
chore(data/list/defs): remove unneeded open ([#10100](https://github.com/leanprover-community/mathlib/pull/10100))

### [2021-11-02 02:55:19](https://github.com/leanprover-community/mathlib/commit/d926ac7)
chore(scripts): update nolints.txt ([#10098](https://github.com/leanprover-community/mathlib/pull/10098))
I am happy to remove some nolints for you!

### [2021-11-01 21:07:30](https://github.com/leanprover-community/mathlib/commit/fd783e3)
chore(algebra/free_algebra): remove a heavy and unecessary import ([#10093](https://github.com/leanprover-community/mathlib/pull/10093))
`transfer_instance` pulls in category theory, which is overkill

### [2021-11-01 20:14:44](https://github.com/leanprover-community/mathlib/commit/b1d5446)
chore(analysis/normed_space/operator_norm): remove an import to data.equiv.transfer_instance ([#10094](https://github.com/leanprover-community/mathlib/pull/10094))
This import isn't needed, and the spelling without it is shorter.

### [2021-11-01 12:55:31](https://github.com/leanprover-community/mathlib/commit/0144b6c)
chore({data/finset,data/multiset,order}/locally_finite): Better line wraps ([#10087](https://github.com/leanprover-community/mathlib/pull/10087))

### [2021-11-01 12:22:20](https://github.com/leanprover-community/mathlib/commit/fef1535)
chore(category_theory/limits): reuse a previous result ([#10088](https://github.com/leanprover-community/mathlib/pull/10088))

### [2021-11-01 11:06:34](https://github.com/leanprover-community/mathlib/commit/9ef310f)
chore(algebra/algebra): implement subalgebra.under in terms of restrict_scalars ([#10080](https://github.com/leanprover-community/mathlib/pull/10080))
We should probably remove `subalgebra.under` entirely, but that's likely a lot more work.

### [2021-11-01 11:06:33](https://github.com/leanprover-community/mathlib/commit/17ebcf0)
chore(ring_theory/algebra_tower): relax typeclasses ([#10078](https://github.com/leanprover-community/mathlib/pull/10078))
This generalizes some `comm_ring`s to `comm_semiring`s.
Split from [#10024](https://github.com/leanprover-community/mathlib/pull/10024)

### [2021-11-01 10:12:40](https://github.com/leanprover-community/mathlib/commit/23892a0)
chore(analysis/normed_space/operator_norm): semilinearize part of the file ([#10076](https://github.com/leanprover-community/mathlib/pull/10076))
This PR generalizes part of the `operator_norm` file to semilinear maps. Only the first section (`semi_normed`) is done, which allows us to construct continuous semilinear maps using `linear_map.mk_continuous`.
The rest of the file is trickier, since we need specify how the ring hom interacts with the norm. I'd rather leave it to a future PR since I don't need the rest now.

### [2021-11-01 07:01:57](https://github.com/leanprover-community/mathlib/commit/85fe90e)
feat(algebra/direct_sum/module) : coe and internal ([#10004](https://github.com/leanprover-community/mathlib/pull/10004))
This extracts the following `def`s from within the various `is_internal` properties:
* `direct_sum.add_submonoid_coe`
* `direct_sum.add_subgroup_coe`
* `direct_sum.submodule_coe`
Packing these into a def makes things more concise, and avoids some annoying elaboration issues.

### [2021-11-01 05:31:03](https://github.com/leanprover-community/mathlib/commit/acc504e)
docs(category_theory/*): add missing module docs ([#9990](https://github.com/leanprover-community/mathlib/pull/9990))

### [2021-11-01 02:38:33](https://github.com/leanprover-community/mathlib/commit/e8fa232)
chore(scripts): update nolints.txt ([#10083](https://github.com/leanprover-community/mathlib/pull/10083))
I am happy to remove some nolints for you!

### [2021-11-01 00:38:30](https://github.com/leanprover-community/mathlib/commit/cd457a5)
fix(data/{rbtree,rbmap}): fix some lint errors ([#10036](https://github.com/leanprover-community/mathlib/pull/10036))

### [2021-11-01 00:38:28](https://github.com/leanprover-community/mathlib/commit/bf82122)
feat(algebra/direct_sum/basic): some lemmas about `direct_sum.of` ([#10003](https://github.com/leanprover-community/mathlib/pull/10003))
Some small lemmas about `direct_sum.of` that are handy.