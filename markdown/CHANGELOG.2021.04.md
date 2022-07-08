### [2021-04-30 20:11:22](https://github.com/leanprover-community/mathlib/commit/16c8f7f)
feat(algebraic_geometry/prime_spectrum): Basic opens are compact ([#7411](https://github.com/leanprover-community/mathlib/pull/7411))
This proves that basic opens are compact in the zariski topology. Compactness of the whole space is then realized as a special case. Also adds a few lemmas about zero loci.

### [2021-04-30 20:11:21](https://github.com/leanprover-community/mathlib/commit/aebe755)
refactor(algebra/group_power): put lemmas about order and power in their own file ([#7398](https://github.com/leanprover-community/mathlib/pull/7398))
This means `group_power/basic` has fewer dependencies, making it accessible earlier in the import graph.
The first two lemmas in this `basic` were moved to the end of `order`, but otherwise lemmas have been moved without modification and kept in the same order.
The new imports added in other files are the ones needed to make this build.

### [2021-04-30 20:11:19](https://github.com/leanprover-community/mathlib/commit/6d5a120)
refactor(linear_algebra/eigenspace): cleanup proof ([#7337](https://github.com/leanprover-community/mathlib/pull/7337))
At some point we changed the proof of `exists_eigenvalue` so that it used the fact that any endomorphism of a vector space is integral. This means we don't actually need to pick a nonzero vector at any point, but the proof had been left in a hybrid state, which I've now cleaned up.
In a later PR I'll generalise this proof so it proves Schur's lemma.

### [2021-04-30 20:11:18](https://github.com/leanprover-community/mathlib/commit/5800f69)
feat(category_theory/Quiv): the free/forgetful adjunction between Cat and Quiv ([#7158](https://github.com/leanprover-community/mathlib/pull/7158))

### [2021-04-30 14:55:00](https://github.com/leanprover-community/mathlib/commit/64fdfc7)
feat(category_theory/sites): construct a presieve from an indexed family of arrows ([#7413](https://github.com/leanprover-community/mathlib/pull/7413))
For the LTE: alternate constructors for presieves which can be more convenient.

### [2021-04-30 10:14:07](https://github.com/leanprover-community/mathlib/commit/4722dd4)
feat(ring_theory/finiteness): add add_monoid_algebra.ft_of_fg ([#7265](https://github.com/leanprover-community/mathlib/pull/7265))
This is from `lean_liquid`. We prove `add_monoid_algebra.ft_of_fg`: if `M` is a finitely generated monoid then `add_monoid_algebra R M` if finitely generated as `R-alg`.
The converse is also true, but the proof is longer and I wanted to keep the PR small.
- [x] depends on: [#7279](https://github.com/leanprover-community/mathlib/pull/7279)

### [2021-04-30 10:14:06](https://github.com/leanprover-community/mathlib/commit/4a94b28)
feat(category_theory/sites): Sheaves of structures ([#5927](https://github.com/leanprover-community/mathlib/pull/5927))
Define sheaves on a site taking values in an arbitrary category.
Joint with @kbuzzard. cc: @jcommelin, this is a step towards condensed abelian groups.
I don't love the names here, design advice (particularly from those who'll use this) more than appreciated.
The main points are:
- An `A`-valued presheaf `P : C^op => A` is defined to be a sheaf (for the topology J) iff for every `X : A`, the type-valued presheaves of sets given by sending `U : C^op` to `Hom_{A}(X, P U)` are all sheaves of sets.
- When `A = Type`, this recovers the basic definition of sheaves of sets.
- An alternate definition when `C` is small, has pullbacks and `A` has products is given by an equalizer condition `is_sheaf'`.
- This is equivalent to the earlier definition.
- When `A = Type`, this is definitionally equal to the equalizer condition for presieves in sheaf_of_types.lean
- When `A` has limits and there is a functor `s : A => Type` which is faithful, reflects isomorphisms and preserves limits, then `P : C^op => A` is a sheaf iff the underlying presheaf of types `P >>> s : C^op => Type` is a sheaf. (cf https://stacks.math.columbia.edu/tag/0073, which is a weaker version of this statement (it's only over spaces, not sites) and https://stacks.math.columbia.edu/tag/00YR (a), which additionally assumes filtered colimits).
A couple of questions for reviewers:
- We've now got a ton of equivalent ways of showing something's a sheaf, and it's not the easiest to navigate between them. Is there a nice way around this? I think it's still valuable to have all the ways, since each can be helpful in different contexts but it makes the API a bit opaque. There's also a bit of inconsistency - there's a definition `yoneda_sheaf_condition` which is the same as `is_sheaf_for` but the equalizer conditions at the bottom of sheaf_of_types aren't named, they're just some `nonempty (is_limit (fork.of_ι _ (w P R)))` even though they're also equivalent.
- The name `presieve.is_sheaf` is stupid, I think I was just lazy with namespaces. I think `presieve.family_of_elements` and `presieve.is_sheaf_for` are still sensible, since they are relative to a presieve, but `is_sheaf` doesn't have any reference to presieves in its type. 
- The equalizer condition of sheaves of types is definitionally the same as the equalizer condition for sheaves of structures, so is there any point in having the former version in the library - the latter is just more general (the same doesn't apply to the actual def of sheaves of structures since that's defined in terms of sheaves of types). The main downside I can see is that it might make the proofs of `equalizer_sheaf_condition` a bit trickier, but that's about it

### [2021-04-30 05:44:03](https://github.com/leanprover-community/mathlib/commit/f36cc16)
chore(topology/category): some lemmas for Profinite functions ([#7414](https://github.com/leanprover-community/mathlib/pull/7414))
Adds `concrete_category`  and `has_forget₂` instances for Profinite, and `id_app` and `comp_app` lemmas.

### [2021-04-30 05:44:02](https://github.com/leanprover-community/mathlib/commit/c914e8f)
refactor(data/fin): define neg like sub ([#7408](https://github.com/leanprover-community/mathlib/pull/7408))
Define negation on fin in the same way as subtraction, i.e., using nat.mod (instead of computing it in the integers).

### [2021-04-30 05:44:01](https://github.com/leanprover-community/mathlib/commit/39a1cf0)
feat(group/hom_instances): add composition operators ([#7407](https://github.com/leanprover-community/mathlib/pull/7407))
This adds the analogous definitions to those we have for `linear_map`, namely:
* `monoid_hom.comp_hom'` (c.f. `linear_map.lcomp`, `l` = `linear`)
* `monoid_hom.compl₂` (c.f. `linear_map.compl₂`, `l` = `left`)
* `monoid_hom.compr₂` (c.f. `linear_map.compr₂`, `r` = `right`)
We already have `monoid_hom.comp_hom` (c.f. `linear_map.llcomp`, `ll` = `linear linear`)
It also adds an `ext_iff₂` lemma, which is occasionally useful (but not present for any other time at the moment).
The order of definitions in the file has been shuffled slightly to permit addition of a subheading to group things in doc-gen

### [2021-04-30 00:14:20](https://github.com/leanprover-community/mathlib/commit/413b426)
feat(finset/basic): fill in holes in the finset API ([#7386](https://github.com/leanprover-community/mathlib/pull/7386))
add basic lemmas about finsets

### [2021-04-29 23:00:13](https://github.com/leanprover-community/mathlib/commit/6a796d0)
refactor(algebraic_geometry/structure_sheaf): Remove redundant isomorphism ([#7410](https://github.com/leanprover-community/mathlib/pull/7410))
Removes `stalk_iso_Type`, which is redundant since we also have `structure_sheaf.stalk_iso`, which is the same isomorphism in `CommRing`

### [2021-04-29 14:43:39](https://github.com/leanprover-community/mathlib/commit/ca5176c)
feat(linear_algebra/tensor_product): add definition `tensor_product.map_incl` and `simp` lemmas related to powers of `tensor_product.map` ([#7406](https://github.com/leanprover-community/mathlib/pull/7406))

### [2021-04-29 14:43:38](https://github.com/leanprover-community/mathlib/commit/966b3b1)
feat(set_theory/{surreal, pgame}): `mul_comm` for surreal numbers  ([#7376](https://github.com/leanprover-community/mathlib/pull/7376))
This PR adds a proof of commutativity of multiplication for surreal numbers. 
We also add `mul_zero` and `zero_mul` along with several useful lemmas.
Finally, this renames a handful of lemmas about `relabelling` in order to enable dot notation.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers)

### [2021-04-29 12:50:46](https://github.com/leanprover-community/mathlib/commit/c956353)
chore(.docker): remove alpine build, too fragile ([#7401](https://github.com/leanprover-community/mathlib/pull/7401))
If this is approved I'll remove the automatic builds of the `alpine` based images over on `hub.docker.com`.

### [2021-04-29 12:50:45](https://github.com/leanprover-community/mathlib/commit/91604cb)
feat(data/finsupp/to_dfinsupp): add equivalences between finsupp and dfinsupp ([#7311](https://github.com/leanprover-community/mathlib/pull/7311))
A rework of [#7217](https://github.com/leanprover-community/mathlib/pull/7217), that adds a more elementary equivalence.

### [2021-04-29 08:23:27](https://github.com/leanprover-community/mathlib/commit/fda4d3d)
feat(data/rat): add `@[simp]` to `rat.num_div_denom` ([#7393](https://github.com/leanprover-community/mathlib/pull/7393))
I have an equation in rational numbers that I want to turn into an equation in integers, and everything `simp`s away nicely except the equation `x.num / x.denom = x`. Marking `rat.num_div_denom` as `simp` should fix that, and I don't expect it will break anything. (`rat.num_denom : rat.mk x.num x.denom = x` is already a `simp` lemma.)
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60x.2Enum.20.2F.20x.2Edenom.20.3D.20x.60

### [2021-04-28 19:37:48](https://github.com/leanprover-community/mathlib/commit/c50cb7a)
feat(data/fintype/basic): add decidable_eq_(bundled-hom)_fintype ([#7394](https://github.com/leanprover-community/mathlib/pull/7394))
Using the proof of `decidable_eq_equiv_fintype` for guidance, this adds equivalent statements about:
* `function.embedding`
* `zero_hom`
* `one_hom`
* `add_hom`
* `mul_hom`
* `add_monoid_hom`
* `monoid_hom`
* `monoid_with_zero_hom`
* `ring_hom`
It also fixes a typo that swaps `left` and `right` between two definition names.

### [2021-04-28 19:37:47](https://github.com/leanprover-community/mathlib/commit/abf1c20)
feat(linear_algebra/free_module): free of finite torsion free ([#7381](https://github.com/leanprover-community/mathlib/pull/7381))
This is a reformulation of module.free_of_finite_type_torsion_free in terms of `ring_theory.finiteness` (combining my recent algebra PRs). Note this adds an import but it seems ok to me.

### [2021-04-28 19:37:46](https://github.com/leanprover-community/mathlib/commit/b9c80c9)
chore(*): use `sq` as convention for "squared" ([#7368](https://github.com/leanprover-community/mathlib/pull/7368))
This PR establishes `sq x` as the notation for `x ^ 2`. See [this Zulip conversation](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/sqr.20vs.20sq.20vs.20pow_two/near/224972795).
A breakdown of the refactor:
- All instances of `square` and `sqr` are changed to `sq` (except where `square` means something other than "to the second power")
- All instances of `pow_two` are changed to `sq`, though many are kept are aliases
- All instances of `sum_of_two_squares` are changed to `sq_add_sq`
n.b. I did NOT alter any instances of:
- `squarefree`
- `sum_of_four_squares`
- `fpow_two` or `rpow_two`
<!-- The text above the `

### [2021-04-28 19:37:44](https://github.com/leanprover-community/mathlib/commit/2401d99)
feat(group_theory/finiteness): add group.fg ([#7338](https://github.com/leanprover-community/mathlib/pull/7338))
Basic facts about finitely generated groups.
- [x] depends on: [#7279](https://github.com/leanprover-community/mathlib/pull/7279)

### [2021-04-28 19:37:43](https://github.com/leanprover-community/mathlib/commit/4328cc3)
feat(topology/continuous_function): abstract statement of Weierstrass approximation ([#7303](https://github.com/leanprover-community/mathlib/pull/7303))

### [2021-04-28 14:47:13](https://github.com/leanprover-community/mathlib/commit/e6a4c81)
chore(algebra/module/submodule): mem_to_add_subgroup ([#7392](https://github.com/leanprover-community/mathlib/pull/7392))

### [2021-04-28 14:47:12](https://github.com/leanprover-community/mathlib/commit/052447d)
feat(algebra/group/hom_instance): add add_monoid_hom.mul ([#7382](https://github.com/leanprover-community/mathlib/pull/7382))

### [2021-04-28 13:06:40](https://github.com/leanprover-community/mathlib/commit/a1b695a)
feat(algbera/lie/submodule): add `simp` lemmas `lie_submodule.map_sup`, `lie_ideal.map_sup` ([#7384](https://github.com/leanprover-community/mathlib/pull/7384))

### [2021-04-28 09:40:47](https://github.com/leanprover-community/mathlib/commit/105935c)
feat(linear_algebra/finite_dimensional): characterizations of finrank = 1 and ≤ 1 ([#7354](https://github.com/leanprover-community/mathlib/pull/7354))

### [2021-04-28 06:27:58](https://github.com/leanprover-community/mathlib/commit/f952dd1)
refactor(algebra/big_operators/finprod, ring_theory/hahn_series): summable families now use `finsum` ([#7388](https://github.com/leanprover-community/mathlib/pull/7388))
Adds a few `finprod/finsum` lemmas
Uses them to refactor `hahn_series.summable_family` to use `finsum`

### [2021-04-28 01:28:28](https://github.com/leanprover-community/mathlib/commit/db89082)
chore(.): remove stray file ([#7390](https://github.com/leanprover-community/mathlib/pull/7390))
I accidentally committed a stray pdf file generated by `leanproject import-graph` during [#7250](https://github.com/leanprover-community/mathlib/pull/7250), and it accidentally got merged into master!

### [2021-04-28 01:28:27](https://github.com/leanprover-community/mathlib/commit/97118b4)
fix(algebra/group/commute): use the right typeclass ([#7389](https://github.com/leanprover-community/mathlib/pull/7389))
This section is called `mul_one_class`, but I forgot to actually make it use `mul_one_class` instead of `monoid` in a previous PR...

### [2021-04-28 01:28:26](https://github.com/leanprover-community/mathlib/commit/d40a60c)
feat(logic/embedding): add function.embedding.coe_injective ([#7383](https://github.com/leanprover-community/mathlib/pull/7383))
Prior art for this lemma name: `linear_map.coe_injective`

### [2021-04-27 20:07:51](https://github.com/leanprover-community/mathlib/commit/c562caf)
fix(tactic/itauto): reset after or split ([#7387](https://github.com/leanprover-community/mathlib/pull/7387))
Fixes a bug [reported on zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.60ring.60.20tactic.20for.20types/near/236368947)

### [2021-04-27 20:07:50](https://github.com/leanprover-community/mathlib/commit/a24d480)
chore(.docker): fix alpine docker build ([#7374](https://github.com/leanprover-community/mathlib/pull/7374))
A dependency for building mathlibtools had gained a requirement of having `make` available, so we install that.
This doesn't affect the produced image, and we only install `make` in an intermediate image.

### [2021-04-27 20:07:49](https://github.com/leanprover-community/mathlib/commit/1ff56a0)
feat(analysis/analytic): a few lemmas about summability and radius ([#7365](https://github.com/leanprover-community/mathlib/pull/7365))
This PR adds a few lemmas relating the radius of a formal multilinear series `p` to the summability of `Σ ∥pₙ∥ ∥y∥ⁿ` (in both ways). There isn't anything incredibly new as these are mostly special cases of existing lemmas, but I think they could be simpler to find and use. I also modified the docstring of `formal_multilinear_series.radius` to emphasize the difference between "`Σ pₙ yⁿ`converges" and "`Σ ∥pₙ∥ ∥y∥ⁿ` converges".

### [2021-04-27 15:04:08](https://github.com/leanprover-community/mathlib/commit/5247d00)
feat(algebra/group_with_zero): add semigroup_with_zero ([#7346](https://github.com/leanprover-community/mathlib/pull/7346))
Split from [#6786](https://github.com/leanprover-community/mathlib/pull/6786). By putting the new typeclass _before_ `mul_zero_one_class`, it doesn't need any annotations on `zero_ne_one` as the original PR did.

### [2021-04-27 15:04:06](https://github.com/leanprover-community/mathlib/commit/78a20ff)
feat(data/buffer/parser/basic): nat_eq_done ([#6340](https://github.com/leanprover-community/mathlib/pull/6340))
The `nat` parser gives the maximal possible numeral.

### [2021-04-27 11:31:38](https://github.com/leanprover-community/mathlib/commit/5263ea3)
chore(algebra/lie/{abelian,tensor_product}): rename `maximal_trivial_submodule` → `max_triv_submodule` ([#7385](https://github.com/leanprover-community/mathlib/pull/7385))
cf https://github.com/leanprover-community/mathlib/pull/7313#discussion_r619995552

### [2021-04-27 11:31:37](https://github.com/leanprover-community/mathlib/commit/e7bd3ca)
docs(overview): Add some recent work by Yury ([#7378](https://github.com/leanprover-community/mathlib/pull/7378))
Hausdorff measure and Urysohn's lemma

### [2021-04-27 11:31:36](https://github.com/leanprover-community/mathlib/commit/efeeaca)
feat(analysis/special_functions/integrals): integral of `sin x ^ n` ([#7372](https://github.com/leanprover-community/mathlib/pull/7372))
The reduction of `∫ x in a..b, sin x ^ n`, ∀ n ∈ ℕ, 2 ≤ n.
We had this for the integral over [0, π] but I don't see any reason not to generalize it to any [a, b].
This also allows for the derivation of the integral of `sin x ^ 2` as a special case.

### [2021-04-27 11:31:35](https://github.com/leanprover-community/mathlib/commit/18403ac)
feat(topology/separation): change regular_space definition, added t1_characterisation and definition of Urysohn space ([#7367](https://github.com/leanprover-community/mathlib/pull/7367))
This PR changes the definition of regular_space becouse the previous definition requests t1_space and it's posible to only require t0_space as a condition. Due to that change, we had to reformulate the prove of the lemma separed_regular in src/topology/uniform_space/separation.lean adding the t0 condition.
We've also define the Uryson space , with his respectives lemmas about the relation with `T_2` and `T_3`, and prove the relation between the definition of t1_space from mathlib and the common definition with open sets.

### [2021-04-27 07:21:32](https://github.com/leanprover-community/mathlib/commit/287492c)
refactor(ring_theory/hahn_series): non-linearly-ordered Hahn series ([#7377](https://github.com/leanprover-community/mathlib/pull/7377))
Refactors Hahn series to use `set.is_pwo` instead of `set.is_wf`, allowing them to be defined on non-linearly-ordered monomial types

### [2021-04-27 07:21:31](https://github.com/leanprover-community/mathlib/commit/57cc384)
chore(integration): missing lemmas ([#7364](https://github.com/leanprover-community/mathlib/pull/7364))
These are still preliminaries for derivation of parametric integrals.
From the sphere eversion project

### [2021-04-27 07:21:30](https://github.com/leanprover-community/mathlib/commit/241400f)
feat(analysis/seminorm): lemmas on balanced sets ([#7358](https://github.com/leanprover-community/mathlib/pull/7358))
Adds lemmas about operations on balanced sets and golfs a proof.

### [2021-04-27 07:21:29](https://github.com/leanprover-community/mathlib/commit/20c520a)
feat(algebra/opposite): inversion is a mul_equiv to the opposite group ([#7330](https://github.com/leanprover-community/mathlib/pull/7330))
This also splits out `monoid_hom.to_opposite` from `ring_hom.to_opposite`, and adds `add_equiv.neg` and `mul_equiv.inv` for the case when the `(add_)group` is commutative.

### [2021-04-27 07:21:28](https://github.com/leanprover-community/mathlib/commit/465cf5a)
feat(category_theory/abelian): biproducts of projective objects are projective ([#7319](https://github.com/leanprover-community/mathlib/pull/7319))
Also all objects of `Type` are projective.

### [2021-04-27 07:21:26](https://github.com/leanprover-community/mathlib/commit/874780f)
feat(data/quot): rec_on_subsingleton2' ([#7294](https://github.com/leanprover-community/mathlib/pull/7294))

### [2021-04-27 07:21:25](https://github.com/leanprover-community/mathlib/commit/a3f589c)
feat(analysis/calculus/deriv): `has_deriv_at.continuous_on` ([#7260](https://github.com/leanprover-community/mathlib/pull/7260))
See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/has_deriv_at.2Econtinuous_on/near/235034547).

### [2021-04-27 07:21:24](https://github.com/leanprover-community/mathlib/commit/4f9543b)
feat(data/polynomial): lemma about aeval on functions, and on subalgebras ([#7252](https://github.com/leanprover-community/mathlib/pull/7252))

### [2021-04-27 07:21:23](https://github.com/leanprover-community/mathlib/commit/89c27cc)
feat(category/subobjects): more API on limit subobjects ([#7203](https://github.com/leanprover-community/mathlib/pull/7203))

### [2021-04-27 07:21:22](https://github.com/leanprover-community/mathlib/commit/40b15f2)
feat(algebra/direct_sum): state what it means for a direct sum to be internal ([#7190](https://github.com/leanprover-community/mathlib/pull/7190))
The goal here is primarily to tick off the item in undergrad.yml.
We'll want some theorems relating this statement to independence / spanning of the submodules, but I'll leave those for someone else to follow-up with.
We end up needing three variants of this - one for each of add_submonoids, add_subgroups, and submodules.

### [2021-04-27 05:47:11](https://github.com/leanprover-community/mathlib/commit/2d8ed1f)
chore(group_theory/eckmann_hilton): use `mul_one_class` and `is_(left|right)_id` ([#7370](https://github.com/leanprover-community/mathlib/pull/7370))
This ties these theorems slightly more to the rest of mathlib.
The changes are:
* `eckmann_hilton.comm_monoid` now promotes a `mul_one_class` to a `comm_monoid` rather than taking two `is_unital` objects. This makes it consistent with `eckmann_hilton.comm_group`.
* `is_unital` is no longer a `class`, since it never had any instances and was never used as a typeclass argument.
* `is_unital` is now defined in terms of `is_left_id` and `is_right_id`.
* `add_group.is_unital` has been renamed to `eckmann_hilton.add_zero_class.is_unital` - the missing namespace was an accident, and the definition works much more generally than it was originally stated for.

### [2021-04-27 04:33:28](https://github.com/leanprover-community/mathlib/commit/1742443)
refactor(archive/imo) shorten imo1013_q5 using pow_unbounded_of_one_lt ([#7373](https://github.com/leanprover-community/mathlib/pull/7373))
Replaces a usage of `one_add_mul_sub_le_pow` with the more direct `pow_unbounded_of_one_lt`.

### [2021-04-26 22:18:45](https://github.com/leanprover-community/mathlib/commit/3093fd8)
chore(algebra/category/*): use by apply to speed up elaboration ([#7360](https://github.com/leanprover-community/mathlib/pull/7360))
A few more speed ups.

### [2021-04-26 18:22:46](https://github.com/leanprover-community/mathlib/commit/a5cb13a)
feat(order/zorn): upward inclusion variant of Zorn's lemma ([#7362](https://github.com/leanprover-community/mathlib/pull/7362))
add zorn_superset
This also add various missing bits of whitespace throughout the file.

### [2021-04-26 13:34:11](https://github.com/leanprover-community/mathlib/commit/5ac79a6)
feat(algebra/lie/tensor_product): prove `lie_submodule.lie_ideal_oper_eq_tensor_map_range` ([#7313](https://github.com/leanprover-community/mathlib/pull/7313))
The lemma `coe_lift_lie_eq_lift_coe` also introduced here is an unrelated change but is a stronger form of `lift_lie_apply` that is worth having.
See also this [Zulip remark](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60linear_map.2Erange_eq_map.60.20vs.20.60submodule.2Emap_top.60/near/235845192) concerning the proposed library note.

### [2021-04-26 13:34:10](https://github.com/leanprover-community/mathlib/commit/35b9d9c)
feat(group_theory/finiteness): add submonoid.fg ([#7279](https://github.com/leanprover-community/mathlib/pull/7279))
I introduce here the notion of a finitely generated monoid (not necessarily commutative) and I prove that the notion is preserved by `additive`/`multiplicative`.
A natural continuation is of course to introduce the same notion for groups.

### [2021-04-26 09:22:21](https://github.com/leanprover-community/mathlib/commit/5258669)
feat(topology/unit_interval): affine homeomorphisms of intervals ([#7250](https://github.com/leanprover-community/mathlib/pull/7250))

### [2021-04-26 06:03:18](https://github.com/leanprover-community/mathlib/commit/c22de3f)
chore(algebra/lie/nilpotent): make proof of `module.derived_series_le_lower_central_series` less refl-heavy ([#7359](https://github.com/leanprover-community/mathlib/pull/7359))
According to the list in [this Zulip remark](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/mathlib.20repo.20GitHub.20actions.20queue/near/235996204)
this lemma was the slowest task for Leanchecker.
The changes here should help. Using `set_option profiler true`, I see
about a ten-fold speedup in elaboration time for Lean, from approximately
2.4s to 0.24s

### [2021-04-25 19:05:15](https://github.com/leanprover-community/mathlib/commit/9526061)
feat(data/nat/fib): add a strict monotonicity lemma. ([#7317](https://github.com/leanprover-community/mathlib/pull/7317))
Prove strict monotonicity of `fib (n + 2)`.
With thanks to @b-mehta and @dwarn.

### [2021-04-25 15:13:07](https://github.com/leanprover-community/mathlib/commit/4e0c460)
chore(analysis/special_functions/integrals): reorganize file ([#7351](https://github.com/leanprover-community/mathlib/pull/7351))

### [2021-04-25 15:13:06](https://github.com/leanprover-community/mathlib/commit/dbc9cf9)
feat(data/matrix/basic): transform vec_mul to mul_vec ([#7348](https://github.com/leanprover-community/mathlib/pull/7348))

### [2021-04-25 15:13:05](https://github.com/leanprover-community/mathlib/commit/d5cb403)
chore(ring_theory/ideal/operations): golf and remove @ ([#7347](https://github.com/leanprover-community/mathlib/pull/7347))
Instead of passing all these arguments explicitly, it's sufficient to just use `(... : _)` to get the elaborator to do the right thing.
This makes this proof less fragile to argument changes to `pi.ring_hom`, such as the planned generalization to non-associative rings

### [2021-04-25 15:13:04](https://github.com/leanprover-community/mathlib/commit/3821d31)
feat(ring_theory): fg_iff_exists_fin_generating_fam ([#7343](https://github.com/leanprover-community/mathlib/pull/7343))

### [2021-04-25 15:13:03](https://github.com/leanprover-community/mathlib/commit/9cc3d80)
feat(linear_algebra): free_of_finite_type_torsion_free ([#7341](https://github.com/leanprover-community/mathlib/pull/7341))
A finite type torsion free module over a PID is free.
There are also some tiny preliminaries, and I moved `submodule.map_span` to `linear_map.map_span` to allow using the dot notation more often.

### [2021-04-25 10:09:22](https://github.com/leanprover-community/mathlib/commit/8e4ef23)
refactor(*): kill int multiplication diamonds ([#7255](https://github.com/leanprover-community/mathlib/pull/7255))
Insert a data field `gsmul` in `add_comm_group` containing a Z-action, and use it to make sure that all diamonds related to `Z` -actions disappear.
Followup to [#7084](https://github.com/leanprover-community/mathlib/pull/7084)

### [2021-04-25 05:29:14](https://github.com/leanprover-community/mathlib/commit/d052c52)
feat(order/extension): extend partial order to linear order ([#7142](https://github.com/leanprover-community/mathlib/pull/7142))
Adds a construction to extend a partial order to a linear order. Also fills in a missing Zorn variant.

### [2021-04-25 03:55:19](https://github.com/leanprover-community/mathlib/commit/d5330fe)
chore(algebra/category): remove duplicated proofs ([#7349](https://github.com/leanprover-community/mathlib/pull/7349))
The results added in [#7100](https://github.com/leanprover-community/mathlib/pull/7100) already exist. I moved them to the place where Scott added the duplicates. Hopefully that will make them more discoverable.

### [2021-04-24 22:17:12](https://github.com/leanprover-community/mathlib/commit/6b2bb8a)
feat(data/finsupp): to_multiset symm apply ([#7356](https://github.com/leanprover-community/mathlib/pull/7356))
Adds a lemma and golfs a proof.

### [2021-04-24 22:17:11](https://github.com/leanprover-community/mathlib/commit/beb694b)
feat(data/list/basic): assorted list lemmas ([#7296](https://github.com/leanprover-community/mathlib/pull/7296))

### [2021-04-24 22:17:10](https://github.com/leanprover-community/mathlib/commit/7716870)
feat(data/list/forall2): defines sublist_forall2 relation ([#7165](https://github.com/leanprover-community/mathlib/pull/7165))
Defines the `sublist_forall₂` relation, indicating that one list is related by `forall₂` to a sublist of another.
Provides two lemmas, `head_mem_self` and `mem_of_mem_tail`, which will be useful when proving Higman's Lemma about the `sublist_forall₂` relation.

### [2021-04-24 19:36:55](https://github.com/leanprover-community/mathlib/commit/2ecd65e)
feat(archive/imo): IMO 2001 Q2 ([#7238](https://github.com/leanprover-community/mathlib/pull/7238))
Formalization of IMO 2001/2

### [2021-04-24 19:36:54](https://github.com/leanprover-community/mathlib/commit/8f8b194)
feat(linear_algebra): Lagrange formulas for expanding `det` along a row or column ([#6897](https://github.com/leanprover-community/mathlib/pull/6897))
This PR proves the full Lagrange formulas for writing the determinant of a `n+1 × n+1` matrix as an alternating sum of minors. @pechersky and @eric-wieser already put together enough of the pieces so that `simp` could apply this formula to matrices of a known size. In the end I still had to apply a couple of permutations (`fin.cycle_range` defined in [#6815](https://github.com/leanprover-community/mathlib/pull/6815)) to the entries to get to the "official" formula.

### [2021-04-24 19:36:54](https://github.com/leanprover-community/mathlib/commit/f83ae59)
feat(group_theory/nielsen_schreier): subgroup of free group is free ([#6840](https://github.com/leanprover-community/mathlib/pull/6840))
Prove that a subgroup of a free group is itself free

### [2021-04-24 15:20:39](https://github.com/leanprover-community/mathlib/commit/46ceb36)
refactor(*): rename `semimodule` to `module`, delete typeclasses `module` and `vector_space` ([#7322](https://github.com/leanprover-community/mathlib/pull/7322))
Splitting typeclasses between `semimodule`, `module` and `vector_space` was causing many (small) issues, so why don't we just get rid of this duplication?
This PR contains the following changes:
 * delete the old `module` and `vector_space` synonyms for `semimodule`
 * find and replace all instances of `semimodule` and `vector_space` to `module`
 * (thereby renaming the previous `semimodule` typeclass to `module`)
 * rename `vector_space.dim` to `module.rank` (in preparation for generalizing this definition to all modules)
 * delete a couple `module` instances that have now become redundant
This find-and-replace has been done extremely naïvely, but it seems there were almost no name clashes and no "clbuttic mistakes". I have gone through the full set of changes, finding nothing weird, and I'm fixing any build issues as they come up (I expect less than 10 declarations will cause conflicts).
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/module.20from.20semimodule.20over.20a.20ring
A good example of a workaround required by the `module` abbreviation is the [`triv_sq_zero_ext.module` instance](https://github.com/leanprover-community/mathlib/blob/3b8cfdc905c663f3d99acac325c7dff1a0ce744c/src/algebra/triv_sq_zero_ext.lean#L164).

### [2021-04-24 10:16:02](https://github.com/leanprover-community/mathlib/commit/f15887a)
chore(docs/100.yaml): mention "Erdős–Szekeres" by name ([#7353](https://github.com/leanprover-community/mathlib/pull/7353))

### [2021-04-24 10:16:00](https://github.com/leanprover-community/mathlib/commit/767c8c5)
feat(data/int/basic): add nat_abs_ne_zero ([#7350](https://github.com/leanprover-community/mathlib/pull/7350))

### [2021-04-24 02:33:48](https://github.com/leanprover-community/mathlib/commit/27cd5c1)
feat(group_theory/{perm/cycle_type, specific_groups/alternating_group}): the alternating group is generated by 3-cycles ([#6949](https://github.com/leanprover-community/mathlib/pull/6949))
Moves the alternating group to a new file, renames `alternating_subgroup` to `alternating_group`
Proves that any permutation whose support has cardinality 3 is a cycle
Defines `equiv.perm.is_three_cycle`
Shows that the alternating group is generated by 3-cycles

### [2021-04-23 20:45:18](https://github.com/leanprover-community/mathlib/commit/bbd9362)
feat(topology/algebra): uniform continuity from 0 ([#7318](https://github.com/leanprover-community/mathlib/pull/7318))
From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Linear.20map.20is.20continuous.20if.20it's.20continuous.20at.20zero/near/234714207, thanks to @PatrickMassot.

### [2021-04-23 15:54:59](https://github.com/leanprover-community/mathlib/commit/d89f93a)
refactor(field_theory/algebraic_closure): move complex.is_alg_closed ([#7344](https://github.com/leanprover-community/mathlib/pull/7344))
This avoids having to import half of analysis in order to talk about eigenspaces.

### [2021-04-23 15:54:58](https://github.com/leanprover-community/mathlib/commit/bb2e7f9)
feat(algebra/star/pi): star operates elementwise on pi types ([#7342](https://github.com/leanprover-community/mathlib/pull/7342))

### [2021-04-23 15:54:57](https://github.com/leanprover-community/mathlib/commit/a5b5f6c)
chore(algebra/opposite): add missing `monoid_with_zero` instance ([#7339](https://github.com/leanprover-community/mathlib/pull/7339))
Along with the `mul_zero_one_class` and `mul_zero_class` instances needed to build it

### [2021-04-23 15:54:56](https://github.com/leanprover-community/mathlib/commit/6c09295)
feat(analysis/specific_limits): basic ratio test for summability of a nat-indexed family ([#7277](https://github.com/leanprover-community/mathlib/pull/7277))

### [2021-04-23 11:02:02](https://github.com/leanprover-community/mathlib/commit/33ea698)
feat(linear_algebra/tensor_product): characterise range of tensor product of two linear maps ([#7340](https://github.com/leanprover-community/mathlib/pull/7340))

### [2021-04-23 11:02:00](https://github.com/leanprover-community/mathlib/commit/227c42d)
doc(field_theory/minpoly): improve some doc-strings ([#7336](https://github.com/leanprover-community/mathlib/pull/7336))

### [2021-04-23 11:01:59](https://github.com/leanprover-community/mathlib/commit/3a8f9db)
feat(logic/function/basic): function.involutive.eq_iff ([#7332](https://github.com/leanprover-community/mathlib/pull/7332))
The lemma name matches the brevity of `function.injective.eq_iff`.
The fact the definitions differ isn't important, as both are accessible from `hf : involutive f` as `hf.eq_iff` and `hf.injective.eq_iff`.

### [2021-04-23 11:01:58](https://github.com/leanprover-community/mathlib/commit/15b4fe6)
chore(algebra/iterate_hom): generalize `iterate_map_one` and `iterate_map_mul` to mul_one_class ([#7331](https://github.com/leanprover-community/mathlib/pull/7331))

### [2021-04-23 11:01:57](https://github.com/leanprover-community/mathlib/commit/4b065bf)
feat(data/matrix/basic): add lemma for assoc of mul_vec w.r.t. smul ([#7310](https://github.com/leanprover-community/mathlib/pull/7310))
Add a new lemma for the other direction of smul_mul_vec_assoc, which works on commutative rings.

### [2021-04-23 07:17:04](https://github.com/leanprover-community/mathlib/commit/6f3d905)
refactor(ring_theory/polynomial/content): Define is_primitive more generally ([#7316](https://github.com/leanprover-community/mathlib/pull/7316))
The lemma `is_primitive_iff_is_unit_of_C_dvd` shows that `polynomial.is_primitive` can be defined without the `gcd_monoid` assumption.

### [2021-04-23 07:17:03](https://github.com/leanprover-community/mathlib/commit/5bd96ce)
feat(algebra/group/pi): pow_apply ([#7302](https://github.com/leanprover-community/mathlib/pull/7302))

### [2021-04-23 07:17:02](https://github.com/leanprover-community/mathlib/commit/85df3a3)
refactor(group_theory/submonoid/basic): merge together similar lemmas and definitions ([#7280](https://github.com/leanprover-community/mathlib/pull/7280))
This uses `simps` to generate lots of uninteresting coe lemmas, and removes the less-bundled versions of definitions.
The main changes are:
* `add_submonoid.to_submonoid_equiv` is now just called `add_submonoid.to_submonoid`. This means we can remove the `add_submonoid.to_submonoid_mono` lemma, as that's available as `add_submonoid.to_submonoid.monotone`. Ditto for the multiplicative version.
* `simps` now knows how to handled `(add_)submonoid` objects. Unfortunately it uses `coe` as a suffix rather than a prefix, so we can't use it everywhere yet. For now we restrict its use to just these additive / multiplicative lemmas which already had `coe` as a suffix.
* `submonoid.of_add_submonoid` has been renamed to `add_submonoid.to_submonoid'` to enable dot notation.
* `add_submonoid.of_submonoid` has been renamed to `submonoid.to_add_submonoid'` to enable dot notation.
* The above points, but applied to `(add_)subgroup`
* Two new variants of the closure lemmas about `add_submonoid` (`add_submonoid.to_submonoid'_closure` and `submonoid.to_add_submonoid'_closure`), taken from [#7279](https://github.com/leanprover-community/mathlib/pull/7279)

### [2021-04-23 07:17:01](https://github.com/leanprover-community/mathlib/commit/0070d22)
feat(algebra/category/Module): mono_iff_injective ([#7100](https://github.com/leanprover-community/mathlib/pull/7100))
We should also prove `epi_iff_surjective` at some point. In the `Module` case this doesn't fall out of an adjunction, but it's still true.

### [2021-04-23 06:00:43](https://github.com/leanprover-community/mathlib/commit/b77916d)
feat(algebraic_geometry/Scheme): improve cosmetics of definition ([#7325](https://github.com/leanprover-community/mathlib/pull/7325))
Purely cosmetic, but the definition is going on a poster, so ...

### [2021-04-23 04:34:57](https://github.com/leanprover-community/mathlib/commit/40bb51e)
chore(scripts): update nolints.txt ([#7334](https://github.com/leanprover-community/mathlib/pull/7334))
I am happy to remove some nolints for you!

### [2021-04-23 00:41:31](https://github.com/leanprover-community/mathlib/commit/2bd09f0)
chore(geometry/manifold/instances/circle): provide instance ([#7333](https://github.com/leanprover-community/mathlib/pull/7333))
Assist typeclass inference when proving the circle is a Lie group, by providing an instance.
(Mostly cosmetic, but as this proof is going on a poster I wanted to streamline.)

### [2021-04-23 00:41:30](https://github.com/leanprover-community/mathlib/commit/1e1e93a)
feat(data/list/zip): distributive lemmas ([#7312](https://github.com/leanprover-community/mathlib/pull/7312))

### [2021-04-22 20:22:25](https://github.com/leanprover-community/mathlib/commit/b401f07)
feat(src/group_theory/subgroup): add closure.submonoid.closure ([#7328](https://github.com/leanprover-community/mathlib/pull/7328))
`subgroup.closure S` equals `submonoid.closure (S ∪ S⁻¹)`.

### [2021-04-22 20:22:24](https://github.com/leanprover-community/mathlib/commit/aff758e)
feat(data/nat/gcd, ring_theory/int/basic): add some basic lemmas ([#7314](https://github.com/leanprover-community/mathlib/pull/7314))
This also reduces the dependency on definitional equalities a but

### [2021-04-22 20:22:23](https://github.com/leanprover-community/mathlib/commit/f8464e3)
chore(computability/language): golf some proofs ([#7301](https://github.com/leanprover-community/mathlib/pull/7301))

### [2021-04-22 20:22:22](https://github.com/leanprover-community/mathlib/commit/0521e2b)
feat(data/list/nodup): nodup.ne_singleton_iff ([#7298](https://github.com/leanprover-community/mathlib/pull/7298))

### [2021-04-22 20:22:21](https://github.com/leanprover-community/mathlib/commit/1c07dc0)
feat(algebra/big_operators): `prod_ite_of_{true, false}`. ([#7291](https://github.com/leanprover-community/mathlib/pull/7291))

### [2021-04-22 20:22:20](https://github.com/leanprover-community/mathlib/commit/a104211)
feat(data/list): suffix_cons_iff ([#7287](https://github.com/leanprover-community/mathlib/pull/7287))

### [2021-04-22 20:22:19](https://github.com/leanprover-community/mathlib/commit/98ccc66)
feat(algebra/lie/tensor_product): define (binary) tensor product of Lie modules ([#7266](https://github.com/leanprover-community/mathlib/pull/7266))

### [2021-04-22 20:22:18](https://github.com/leanprover-community/mathlib/commit/fa49a63)
feat(set/lattice): nonempty_of_union_eq_top_of_nonempty ([#7254](https://github.com/leanprover-community/mathlib/pull/7254))
I have no idea where these lemmas belong. This is the earliest possible point. But perhaps they are too specific, and only belong at the point of use? I'm not certain here.

### [2021-04-22 20:22:16](https://github.com/leanprover-community/mathlib/commit/1585b14)
feat(group_theory/perm/*): Generating S_n ([#7211](https://github.com/leanprover-community/mathlib/pull/7211))
This PR proves several lemmas about generating S_n, culminating in the following result:
If H is a subgroup of S_p, and if H has cardinality divisible by p, and if H contains a transposition, then H is all of S_p.

### [2021-04-22 20:22:15](https://github.com/leanprover-community/mathlib/commit/6929740)
refactor(algebra/big_operators/finprod) move finiteness assumptions to be final parameters ([#7196](https://github.com/leanprover-community/mathlib/pull/7196))
This PR takes all the finiteness hypotheses in `finprod.lean` and moves them back to be the last parameters of their lemmas. this only affects a handful of them because the API is small, and nothing else relies on it yet. This change is to allow for easier rewriting in cases where finiteness goals can be easily discharged, such as where a `fintype` instance is present. 
I also added `t` as an explicit parameter in `finprod_mem_inter_mul_diff` and the primed version, since it may be useful to invoke the lemma in cases where it can't be inferred, such as when rewriting in reverse.

### [2021-04-22 20:22:14](https://github.com/leanprover-community/mathlib/commit/a1f3ff8)
feat(algebra/lie/nilpotent): basic lemmas about nilpotency ([#7181](https://github.com/leanprover-community/mathlib/pull/7181))

### [2021-04-22 14:56:29](https://github.com/leanprover-community/mathlib/commit/a28012c)
feat(algebra/monoid_algebra): add mem.span_support ([#7323](https://github.com/leanprover-community/mathlib/pull/7323))
A (very) easy lemma about `monoid_algebra`.

### [2021-04-22 14:56:28](https://github.com/leanprover-community/mathlib/commit/3d2fec5)
feat(algebra/group_power/basic): `pow_ne_zero_iff` and `pow_pos_iff` ([#7307](https://github.com/leanprover-community/mathlib/pull/7307))
For natural `n > 0`, 
- `a ^ n ≠ 0 ↔ a ≠ 0`
- `0 < a ^ n ↔ 0 < a` where `a` is a member of a `linear_ordered_comm_monoid_with_zero`

### [2021-04-22 14:56:27](https://github.com/leanprover-community/mathlib/commit/1f65e42)
feat(category_theory/adjunction): reflective adjunction induces partial bijection ([#7286](https://github.com/leanprover-community/mathlib/pull/7286))

### [2021-04-22 14:56:26](https://github.com/leanprover-community/mathlib/commit/e5e0ae7)
chore(data/set/intervals/image_preimage): remove unnecessary add_comm in lemmas ([#7276](https://github.com/leanprover-community/mathlib/pull/7276))
These lemmas introduce an unexpected flip of the addition, whereas without these lemmas the simplification occurs as you might expect. Since these lemmas aren't otherwise used in mathlib, it seems simplest to just remove them.
Let me know if I'm missing something, or some reason to prefer flipping the addition.

### [2021-04-22 14:56:25](https://github.com/leanprover-community/mathlib/commit/56bedb4)
feat(analysis/special_functions/exp_log): `continuous_on_exp`/`pow` ([#7243](https://github.com/leanprover-community/mathlib/pull/7243))

### [2021-04-22 14:56:24](https://github.com/leanprover-community/mathlib/commit/918aea7)
refactor(algebra/ring_quot.lean): make ring_quot irreducible ([#7120](https://github.com/leanprover-community/mathlib/pull/7120))
The quotient of a ring by an equivalence relation which is compatible with the operations is still a ring. This is used to define several objects such as tensor algebras, exterior algebras, and so on, but the details of the construction are irrelevant. This PR makes `ring_quot` irreducible to keep the complexity down.

### [2021-04-22 10:34:46](https://github.com/leanprover-community/mathlib/commit/5ac093c)
fix(.github/workflows): missing closing parentheses in add_label_from_*.yml ([#7320](https://github.com/leanprover-community/mathlib/pull/7320))

### [2021-04-22 10:34:45](https://github.com/leanprover-community/mathlib/commit/2deda90)
feat(data/fin): help `simp` reduce expressions containing `fin.succ_above` ([#7308](https://github.com/leanprover-community/mathlib/pull/7308))
With these `simp` lemmas, in combination with [#6897](https://github.com/leanprover-community/mathlib/pull/6897), `simp; ring` can almost automatically compute the determinant of matrices like `![![a, b], ![c, d]]`.

### [2021-04-22 10:34:43](https://github.com/leanprover-community/mathlib/commit/8b7014b)
fix(data/finset/lattice): sup'/inf' docstring ([#7281](https://github.com/leanprover-community/mathlib/pull/7281))
Made proper reference to `f` in the doc string.

### [2021-04-22 10:34:41](https://github.com/leanprover-community/mathlib/commit/8c05ff8)
feat(set_theory/surreal): add ordered_add_comm_group instance for surreal numbers ([#7270](https://github.com/leanprover-community/mathlib/pull/7270))
[Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers/near/235213851)
Add ordered_add_comm_group instance for surreal numbers.

### [2021-04-22 10:34:39](https://github.com/leanprover-community/mathlib/commit/96d5730)
feat(topology/continuous_function): lemmas about pointwise sup/inf ([#7249](https://github.com/leanprover-community/mathlib/pull/7249))

### [2021-04-22 10:34:37](https://github.com/leanprover-community/mathlib/commit/4591eb5)
chore(category_theory): replace has_hom with quiver ([#7151](https://github.com/leanprover-community/mathlib/pull/7151))

### [2021-04-22 10:34:36](https://github.com/leanprover-community/mathlib/commit/8830a20)
refactor(geometry/manifold): redefine some instances ([#7124](https://github.com/leanprover-community/mathlib/pull/7124))
* Turn `unique_diff_within_at` into a `structure`.
* Generalize `tangent_cone_at`, `unique_diff_within_at`, and `unique_diff_on` to a `semimodule` that is a `topological_space`.
* Redefine `model_with_corners_euclidean_half_space` and `model_with_corners_euclidean_quadrant` to reuse more generic lemmas, including `unique_diff_on.pi` and `unique_diff_on.univ_pi`.
* Make `model_with_corners.unique_diff'` use `target` instead of `range I`; usually it has better defeq.

### [2021-04-22 06:38:11](https://github.com/leanprover-community/mathlib/commit/767d248)
doc(data/finset/basic): fix confusing typo ([#7315](https://github.com/leanprover-community/mathlib/pull/7315))

### [2021-04-22 06:38:10](https://github.com/leanprover-community/mathlib/commit/3fb9823)
feat(topology/subset_properties): variant of elim_nhds_subcover for compact_space ([#7304](https://github.com/leanprover-community/mathlib/pull/7304))
I put this in the `compact_space` namespace, although dot notation won't work so if preferred I can move it back to `_root_`.

### [2021-04-22 06:38:09](https://github.com/leanprover-community/mathlib/commit/b3b74f8)
feat(data/finset/basic): list.to_finset on list ops ([#7297](https://github.com/leanprover-community/mathlib/pull/7297))

### [2021-04-22 06:38:08](https://github.com/leanprover-community/mathlib/commit/55a1e65)
feat(category_theory/adjunction): construct an adjunction on the over category ([#7290](https://github.com/leanprover-community/mathlib/pull/7290))
Pretty small PR in preparation for later things.

### [2021-04-22 06:38:07](https://github.com/leanprover-community/mathlib/commit/d9df8fb)
chore(category_theory/subterminal): update docstring ([#7289](https://github.com/leanprover-community/mathlib/pull/7289))

### [2021-04-22 06:38:05](https://github.com/leanprover-community/mathlib/commit/07e9dd4)
feat(data/nat/prime): nat.factors_eq_nil and other trivial simp lemmas ([#7284](https://github.com/leanprover-community/mathlib/pull/7284))

### [2021-04-22 01:02:34](https://github.com/leanprover-community/mathlib/commit/6deafc2)
chore(.github/workflows): add delegated tag on comment ([#7251](https://github.com/leanprover-community/mathlib/pull/7251))
This automation should hopefully add the "delegated" tag if a maintainer types `bors d+` or `bors d=`. (In fact, it will apply the label if it sees any line starting with `bors d`, since `bors delegate+`, etc. are also allowed).

### [2021-04-22 01:02:33](https://github.com/leanprover-community/mathlib/commit/f68645f)
feat(topology/continuous_function): change formulation of separates points strongly ([#7248](https://github.com/leanprover-community/mathlib/pull/7248))

### [2021-04-22 01:02:32](https://github.com/leanprover-community/mathlib/commit/22f96fc)
chore(topology/algebra/affine): add @continuity to line_map_continuous ([#7246](https://github.com/leanprover-community/mathlib/pull/7246))

### [2021-04-22 01:02:31](https://github.com/leanprover-community/mathlib/commit/afa6b72)
feat(geometry/euclidean): proof of Freek thm 55 - product of chords ([#7139](https://github.com/leanprover-community/mathlib/pull/7139))
proof of thm 55

### [2021-04-22 01:02:29](https://github.com/leanprover-community/mathlib/commit/dac1da3)
feat(analysis/special_functions/bernstein): Weierstrass' theorem: polynomials are dense in C([0,1]) ([#6497](https://github.com/leanprover-community/mathlib/pull/6497))
# Bernstein approximations and Weierstrass' theorem
We prove that the Bernstein approximations
```
∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.
Our proof follows Richard Beals' *Analysis, an introduction*, §7D.
The original proof, due to Bernstein in 1912, is probabilistic,
and relies on Bernoulli's theorem,
which gives bounds for how quickly the observed frequencies in a
Bernoulli trial approach the underlying probability.
The proof here does not directly rely on Bernoulli's theorem,
but can also be given a probabilistic account.
* Consider a weighted coin which with probability `x` produces heads,
  and with probability `1-x` produces tails.
* The value of `bernstein n k x` is the probability that
  such a coin gives exactly `k` heads in a sequence of `n` tosses.
* If such an appearance of `k` heads results in a payoff of `f(k / n)`,
  the `n`-th Bernstein approximation for `f` evaluated at `x` is the expected payoff.
* The main estimate in the proof bounds the probability that
  the observed frequency of heads differs from `x` by more than some `δ`,
  obtaining a bound of `(4 * n * δ^2)⁻¹`, irrespective of `x`.
* This ensures that for `n` large, the Bernstein approximation is (uniformly) close to the
  payoff function `f`.
(You don't need to think in these terms to follow the proof below: it's a giant `calc` block!)
This result proves Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`,
although we defer an abstract statement of this until later.

### [2021-04-21 19:58:09](https://github.com/leanprover-community/mathlib/commit/f2984d5)
fix(data/{finsupp,polynomial,mv_polynomial}/basic): add missing decidable arguments ([#7309](https://github.com/leanprover-community/mathlib/pull/7309))
Lemmas with an `ite` in their conclusion should not use `classical.dec` or similar, instead inferring an appropriate decidability instance from their context. This eliminates a handful of converts elsewhere.
The linter in [#6485](https://github.com/leanprover-community/mathlib/pull/6485) should eventually find these automatically.

### [2021-04-21 19:58:08](https://github.com/leanprover-community/mathlib/commit/120be3d)
feat(data/list/zip): map_zip_with ([#7295](https://github.com/leanprover-community/mathlib/pull/7295))

### [2021-04-21 19:58:07](https://github.com/leanprover-community/mathlib/commit/253d4f5)
feat(analysis/normed_space/dual): generalize to seminormed space ([#7262](https://github.com/leanprover-community/mathlib/pull/7262))
We generalize here the Hahn-Banach theorem and the notion of dual space to `semi_normed_space`.

### [2021-04-21 19:58:06](https://github.com/leanprover-community/mathlib/commit/700d477)
feat(analysis/special_functions/integrals): integral_comp for `f : ℝ → ℝ` ([#7216](https://github.com/leanprover-community/mathlib/pull/7216))
In [#7103](https://github.com/leanprover-community/mathlib/pull/7103) I added lemmas to deal with integrals of the form `c • ∫ x in a..b, f (c * x + d)`. However, it came to my attention that, with those lemmas, `simp` can only handle such integrals if they use `•`, not `*`. To solve this problem and enable computation of these integrals by `simp`, I add versions of the aforementioned `integral_comp` lemmas specialized with `f : ℝ → ℝ` and label them with `simp`.

### [2021-04-21 19:58:05](https://github.com/leanprover-community/mathlib/commit/721e0b9)
feat(order/complete_lattice): independence of an indexed family ([#7199](https://github.com/leanprover-community/mathlib/pull/7199))
This PR reclaims the concept of `independent` for elements of a complete lattice. 
Right now it's defined on subsets -- a subset of a complete lattice L is independent if every
element of it is disjoint from (i.e. bot is the meet of it with) the Sup of all the other elements. 
The problem with this is that if you have an indexed family f:I->L of elements of L then
duplications get lost if you ask for the image of f to be independent (rather like the issue
with a basis of a vector space being a subset rather than an indexed family). This is
an issue when defining gradings on rings, for example: if M is a monoid and R is
a ring, then I don't want the map which sends every m to (top : subgroup R) to
be independent. 
I have renamed the set-theoretic version of `independent` to `set_independent`

### [2021-04-21 19:58:03](https://github.com/leanprover-community/mathlib/commit/66220ac)
chore(tactic/elementwise): fixes ([#7188](https://github.com/leanprover-community/mathlib/pull/7188))
These fixes, while an improvement, still don't fix the problem @justus-springer observed in [#7092](https://github.com/leanprover-community/mathlib/pull/7092).
Really we should generate a second copy of the `_apply` lemma, with the category specialized to `Type u`, and in that one remove all the coercions. Maybe later.

### [2021-04-21 09:38:17](https://github.com/leanprover-community/mathlib/commit/f08fe5f)
doc(data/quot): promote a comment to a docstring ([#7306](https://github.com/leanprover-community/mathlib/pull/7306))

### [2021-04-21 09:38:16](https://github.com/leanprover-community/mathlib/commit/7db1181)
feat(data/dfinsupp): copy map_range defs from finsupp ([#7293](https://github.com/leanprover-community/mathlib/pull/7293))
This adds the bundled homs:
* `dfinsupp.map_range.add_monoid_hom`
* `dfinsupp.map_range.add_equiv`
* `dfinsupp.map_range.linear_map`
* `dfinsupp.map_range.linear_equiv`
and lemmas
* `dfinsupp.map_range_zero`
* `dfinsupp.map_range_add`
* `dfinsupp.map_range_smul`
For which we already have identical lemmas for `finsupp`.
Split from [#7217](https://github.com/leanprover-community/mathlib/pull/7217), since `map_range.add_equiv` can be used in conjunction with `submonoid.mrange_restrict`

### [2021-04-21 09:38:15](https://github.com/leanprover-community/mathlib/commit/80028f3)
feat(data/finset/lattice): add `comp_sup'_eq_sup'_comp`, golf some proofs ([#7275](https://github.com/leanprover-community/mathlib/pull/7275))
The proof is just a very marginally generalized version of the previous proof for `sup'_apply`.

### [2021-04-21 04:20:35](https://github.com/leanprover-community/mathlib/commit/9b8d6e4)
feat(category_theory/monoidal): Drinfeld center ([#7186](https://github.com/leanprover-community/mathlib/pull/7186))
# Half braidings and the Drinfeld center of a monoidal category
We define `center C` to be pairs `⟨X, b⟩`, where `X : C` and `b` is a half-braiding on `X`.
We show that `center C` is braided monoidal,
and provide the monoidal functor `center.forget` from `center C` back to `C`.
## Future work
Verifying the various axioms here is done by tedious rewriting.
Using the `slice` tactic may make the proofs marginally more readable.
More exciting, however, would be to make possible one of the following options:
1. Integration with homotopy.io / globular to give "picture proofs".
2. The monoidal coherence theorem, so we can ignore associators
   (after which most of these proofs are trivial;
   I'm unsure if the monoidal coherence theorem is even usable in dependent type theory).
3. Automating these proofs using `rewrite_search` or some relative.

### [2021-04-21 04:20:34](https://github.com/leanprover-community/mathlib/commit/923314f)
refactor(order/well_founded_set): partially well ordered sets using relations other than `has_le.le` ([#7131](https://github.com/leanprover-community/mathlib/pull/7131))
Introduces `set.partially_well_ordered_on` to generalize `set.is_partially_well_ordered` to relations that do not necessarily come from a `has_le` instance
Renames `set.is_partially_well_ordered` to `set.is_pwo` in analogy with `set.is_wf`
Prepares to refactor Hahn series to use `set.is_pwo` and avoid the assumption of a linear order

### [2021-04-21 04:20:32](https://github.com/leanprover-community/mathlib/commit/02a3133)
feat(group_theory/{order_of_element, perm/cycles}): two cycles are conjugate iff their supports have the same size ([#7024](https://github.com/leanprover-community/mathlib/pull/7024))
Separates out the `equiv`s from several proofs in `group_theory/order_of_element`.
The equivs defined: `fin_equiv_powers`, `fin_equiv_gpowers`, `powers_equiv_powers`, `gpowers_equiv_gpowers`.
Shows that two cyclic permutations are conjugate if and only if their supports have the same `finset.card`.

### [2021-04-21 00:48:48](https://github.com/leanprover-community/mathlib/commit/8481bf4)
feat(algebra/algebra/basic): add alg_hom.apply ([#7278](https://github.com/leanprover-community/mathlib/pull/7278))
This also renames some variables from α to R for readability

### [2021-04-21 00:48:47](https://github.com/leanprover-community/mathlib/commit/4abf961)
feat(algebra/big_operators): product over coerced fintype ([#7236](https://github.com/leanprover-community/mathlib/pull/7236))

### [2021-04-21 00:48:46](https://github.com/leanprover-community/mathlib/commit/ad58861)
refactor(group_theory/submonoid): adjust definitional unfolding of add_monoid_hom.mrange to match set.range ([#7227](https://github.com/leanprover-community/mathlib/pull/7227))
This changes the following to unfold to `set.range`:
* `monoid_hom.mrange`
* `add_monoid_hom.mrange`
* `linear_map.range`
* `lie_hom.range`
* `ring_hom.range`
* `ring_hom.srange`
* `ring_hom.field_range`
* `alg_hom.range`
For example:
```lean
import ring_theory.subring
variables (R : Type*) [ring R] (f : R →+* R)
-- before this PR, these required `f '' univ` on the RHS
example : (f.range : set R) = set.range f := rfl
example : (f.srange : set R) = set.range f := rfl
example : (f.to_monoid_hom.mrange : set R) = set.range f := rfl
-- this one is unchanged by this PR
example : (f.to_add_monoid_hom.range : set R) = set.range f := rfl
```
The motivations behind this change are that
* It eliminates a lot of `∈ set.univ` hypotheses and goals that are just annoying
* it means that an equivalence like `A ≃ set.range f` is defeq to `A ≃ f.range`, with no need to insert awkward `equiv.cast`-like terms to translate between different approaches
* `monoid_hom.range` (as opposed to `mrange`) already used this pattern.
The number of lines has gone up a bit, but most of those are comments explaining the design choice.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60set.2Erange.20f.60.20vs.20.60f.20''.20univ.60/near/234893679)

### [2021-04-20 11:17:03](https://github.com/leanprover-community/mathlib/commit/9bdc555)
feat(algebraic_geometry/prime_spectrum): More lemmas ([#7244](https://github.com/leanprover-community/mathlib/pull/7244))
Adding and refactoring some lemmas about zero loci and basic opens. Also adds three lemmas in `ideal/basic.lean`.

### [2021-04-20 11:17:02](https://github.com/leanprover-community/mathlib/commit/39d23b8)
feat(logic/basic): exists_or_eq_{left,right} ([#7224](https://github.com/leanprover-community/mathlib/pull/7224))

### [2021-04-20 09:55:49](https://github.com/leanprover-community/mathlib/commit/bf22ab3)
feat(linear_algebra/bilinear_form): Unique adjoints with respect to a nondegenerate bilinear form ([#7071](https://github.com/leanprover-community/mathlib/pull/7071))

### [2021-04-20 07:56:28](https://github.com/leanprover-community/mathlib/commit/a4f59bd)
feat(category_theory/subobject): easy facts about the top subobject ([#7267](https://github.com/leanprover-community/mathlib/pull/7267))

### [2021-04-20 07:56:27](https://github.com/leanprover-community/mathlib/commit/0c721d5)
feat(algebra/lie/abelian): expand API for `lie_module.maximal_trivial_submodule` ([#7235](https://github.com/leanprover-community/mathlib/pull/7235))

### [2021-04-20 07:56:26](https://github.com/leanprover-community/mathlib/commit/944ffff)
chore(combinatorics/quiver): make quiver a class ([#7150](https://github.com/leanprover-community/mathlib/pull/7150))

### [2021-04-20 07:56:25](https://github.com/leanprover-community/mathlib/commit/5e188d2)
feat(category_theory/abelian): definition of projective object ([#7108](https://github.com/leanprover-community/mathlib/pull/7108))
This is extracted from @TwoFX's `projective` branch, with some slight tweaks (make things `Prop` valued classes), and documentation.
This is just the definition of `projective` and `enough_projectives`, with no attempt to construct projective resolutions. I want this in place because constructing projective resolutions will hopefully be a good test of experiments with chain complexes.

### [2021-04-20 03:28:21](https://github.com/leanprover-community/mathlib/commit/013a84e)
chore(scripts): update nolints.txt ([#7272](https://github.com/leanprover-community/mathlib/pull/7272))
I am happy to remove some nolints for you!

### [2021-04-20 03:28:20](https://github.com/leanprover-community/mathlib/commit/8bf9fd5)
chore(data/list): drop `list.is_nil` ([#7269](https://github.com/leanprover-community/mathlib/pull/7269))
We have `list.empty` in Lean core.

### [2021-04-20 00:10:36](https://github.com/leanprover-community/mathlib/commit/3ad4dab)
chore(algebra/*): add back nat_algebra_subsingleton and add_comm_monoid.nat_semimodule.subsingleton ([#7263](https://github.com/leanprover-community/mathlib/pull/7263))
As suggested in https://github.com/leanprover-community/mathlib/pull/7084#discussion_r613195167.
Even if we now have a design solution that makes this unnecessary, it still feels like a result worth stating.

### [2021-04-19 14:03:21](https://github.com/leanprover-community/mathlib/commit/0dfac6e)
chore(*): speed up slow proofs ([#7253](https://github.com/leanprover-community/mathlib/pull/7253))
Proofs that are too slow for the forthcoming `gsmul` refactor. I learnt that `by convert ...` is extremely useful even to close a goal, when elaboration using the expected type is a bad idea.

### [2021-04-19 14:03:20](https://github.com/leanprover-community/mathlib/commit/829d773)
feat(algebra/module/submodule_lattice): add lemmas for nat submodules ([#7221](https://github.com/leanprover-community/mathlib/pull/7221))
This has been suggested by @eric-wieser (who also wrote everything) in [#7200](https://github.com/leanprover-community/mathlib/pull/7200).
This also:
* Merges `span_nat_eq_add_group_closure` and `submodule.span_eq_add_submonoid.closure` which are the same statement into `submodule.span_nat_eq_add_submonoid_closure`, which generalizes the former from `semiring` to `add_comm_monoid`.
* Renames `span_int_eq_add_group_closure` to `submodule.span_nat_eq_add_subgroup_closure`, and generalizes it from `ring` to `add_comm_group`.

### [2021-04-19 09:07:23](https://github.com/leanprover-community/mathlib/commit/6f0c4fb)
feat(data/{int, nat}/parity): rename `ne_of_odd_sum` ([#7261](https://github.com/leanprover-community/mathlib/pull/7261))
`ne_of_odd_sum` becomes `ne_of_odd_add`.

### [2021-04-19 09:07:22](https://github.com/leanprover-community/mathlib/commit/fc5e8cb)
chore(algebra/group): missed generalizations to mul_one_class ([#7259](https://github.com/leanprover-community/mathlib/pull/7259))
This adds a missing `ulift` instance, relaxes some lemmas about `semiconj` and `commute` to apply more generally, and broadens the scope of the definitions `monoid_hom.apply` and `ulift.mul_equiv`.

### [2021-04-19 09:07:20](https://github.com/leanprover-community/mathlib/commit/184e0fe)
fix(equiv/ring): fix bad typeclasses on ring_equiv.trans_apply ([#7258](https://github.com/leanprover-community/mathlib/pull/7258))
`ring_equiv.trans` had weaker typeclasses than the lemma which unfolds it.

### [2021-04-19 09:07:19](https://github.com/leanprover-community/mathlib/commit/77f5fb3)
feat(linear_algebra/eigenspace): `mem_maximal_generalized_eigenspace` ([#7162](https://github.com/leanprover-community/mathlib/pull/7162))

### [2021-04-19 09:07:16](https://github.com/leanprover-community/mathlib/commit/15a64f5)
feat(algebra/module/projective): add projective module ([#6813](https://github.com/leanprover-community/mathlib/pull/6813))
Definition and universal property of projective modules; free modules are projective.

### [2021-04-19 09:07:14](https://github.com/leanprover-community/mathlib/commit/272e2d2)
feat(data/{int, nat, rat}/cast): extensionality lemmas ([#6788](https://github.com/leanprover-community/mathlib/pull/6788))
Extensionality lemmas

### [2021-04-19 06:54:49](https://github.com/leanprover-community/mathlib/commit/43f63d9)
feat(topology/algebra/ordered): IVT for the unordered interval ([#7237](https://github.com/leanprover-community/mathlib/pull/7237))
A version of the Intermediate Value Theorem for `interval`.
Co-authored by @ADedecker

### [2021-04-19 02:29:20](https://github.com/leanprover-community/mathlib/commit/5993b90)
feat(tactic/simps): use new options in library ([#7095](https://github.com/leanprover-community/mathlib/pull/7095))

### [2021-04-18 22:03:44](https://github.com/leanprover-community/mathlib/commit/dbc6574)
chore(data/set/basic): add `set.subsingleton.pairwise_on` ([#7257](https://github.com/leanprover-community/mathlib/pull/7257))
Also add `set.pairwise_on_singleton`.

### [2021-04-18 22:03:43](https://github.com/leanprover-community/mathlib/commit/f6132e4)
feat(data/nat/parity): update to match int/parity ([#7156](https://github.com/leanprover-community/mathlib/pull/7156))
A couple of lemmas existed for `int` but not for `nat`, so I add them. I also tidy some lemmas I added in prior PRs and add a file-level docstring.

### [2021-04-18 22:03:41](https://github.com/leanprover-community/mathlib/commit/969c6a3)
feat(data/int/parity): update to match nat/parity (where applicable) ([#7155](https://github.com/leanprover-community/mathlib/pull/7155))
We had a number of lemmas for `nat` but not for `int`, so I add them. I also globalize variables in the file and add a module docstring.

### [2021-04-18 18:41:38](https://github.com/leanprover-community/mathlib/commit/30ee691)
feat(group_theory/submonoid/operations): add lemmas ([#7219](https://github.com/leanprover-community/mathlib/pull/7219))
Some lemmas about the interaction between additive and multiplicative submonoids.
I provided the two version (from additive to multiplicative and the other way), I am not sure if `@[to_additive]` can automatize this.

### [2021-04-18 18:41:37](https://github.com/leanprover-community/mathlib/commit/d107d82)
feat(data/complex): numerical bounds on log 2 ([#7146](https://github.com/leanprover-community/mathlib/pull/7146))
Upper and lower bounds on log 2. Presumably these could be made faster but I don't know the tricks - the proof of `log_two_near_10` (for me) doesn't take longer than `exp_one_near_20` to compile.
I also strengthened the existing bounds slightly.

### [2021-04-18 14:42:50](https://github.com/leanprover-community/mathlib/commit/7f541b4)
feat(topology/continuous_function): on a subsingleton X, there is only one subalgebra R C(X,R) ([#7247](https://github.com/leanprover-community/mathlib/pull/7247))

### [2021-04-18 14:42:49](https://github.com/leanprover-community/mathlib/commit/cab0481)
feat(data/finset/lattice): mem_sup, mem_sup' ([#7245](https://github.com/leanprover-community/mathlib/pull/7245))
Sets with `bot` and closed under `sup` are closed under `finset.sup`, and variations for `inf`, `sup'`, and `inf'`.

### [2021-04-18 14:42:48](https://github.com/leanprover-community/mathlib/commit/3953378)
feat(set_theory/surreal): add add_monoid instance ([#7228](https://github.com/leanprover-community/mathlib/pull/7228))
This PR is a part of a project for putting ordered abelian group structure on surreal numbers.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers/near/234694758)
We construct add_monoid instance for surreal numbers.
The "term_type" proofs suggested on the above Zulip thread are not working nicely as Lean is unable to infer the type of the setoid.

### [2021-04-18 10:59:52](https://github.com/leanprover-community/mathlib/commit/a6f62a7)
feat(topology/algebra/mul_action.lean): add smul_const ([#7242](https://github.com/leanprover-community/mathlib/pull/7242))
add filter.tendsto.smul_const

### [2021-04-18 10:59:52](https://github.com/leanprover-community/mathlib/commit/4d4b501)
chore(data/set/finite): rename some lemmas ([#7241](https://github.com/leanprover-community/mathlib/pull/7241))
### Revert some name changes from [#5813](https://github.com/leanprover-community/mathlib/pull/5813)
* `set.fintype_set_bUnion` → `set.fintype_bUnion`;
* `set.fintype_set_bUnion'` → `set.fintype_bUnion'`;
* `set.fintype_bUnion` → `set.fintype_bind`;
* `set.fintype_bUnion'` → `set.fintype_bind'`;
* `set.finite_bUnion` → `set.finite.bind`;
### Add a few lemmas
* `set.finite_Union_Prop`;
* add `set.seq` versions of lemmas/defs about `<*>` (they work for `α`, `β` in different universes).

### [2021-04-17 23:26:52](https://github.com/leanprover-community/mathlib/commit/043d046)
feat(algebra/lie/basic): define the `module` and `lie_module` structures on morphisms of Lie modules ([#7225](https://github.com/leanprover-community/mathlib/pull/7225))
Also sundry `simp` lemmas

### [2021-04-17 23:26:51](https://github.com/leanprover-community/mathlib/commit/aa44de5)
feat(data/real): Inf is nonneg ([#7223](https://github.com/leanprover-community/mathlib/pull/7223))

### [2021-04-17 23:26:50](https://github.com/leanprover-community/mathlib/commit/c68e718)
feat(linear_algebra): maximal linear independent ([#7160](https://github.com/leanprover-community/mathlib/pull/7160))
Co-authored by Anne Baanen and Kevin Buzzard

### [2021-04-17 20:12:47](https://github.com/leanprover-community/mathlib/commit/ce667c4)
chore(.github/workflows/build.yml): update elan script URL ([#7234](https://github.com/leanprover-community/mathlib/pull/7234))
`elan` moved to the `leanprover` organization: http://github.com/leanprover/elan

### [2021-04-17 20:12:46](https://github.com/leanprover-community/mathlib/commit/20db2fb)
refactor(topology/algebra/module): `map_smul` argument swap ([#7233](https://github.com/leanprover-community/mathlib/pull/7233))
swap the arguments of map_smul to make dot notation work

### [2021-04-17 20:12:45](https://github.com/leanprover-community/mathlib/commit/b2e7f40)
feat(analysis/convex/basic): convex hull and empty set ([#7232](https://github.com/leanprover-community/mathlib/pull/7232))
added convex_hull_empty

### [2021-04-17 20:12:44](https://github.com/leanprover-community/mathlib/commit/2292463)
doc(group_theory): fix `normalizer` docstring ([#7231](https://github.com/leanprover-community/mathlib/pull/7231))
The _smallest_ subgroup of `G` inside which `H` is normal is `H` itself.
The _largest_ subgroup of `G` inside which `H` is normal is the normalizer.
Also confirmed by Wikipedia (see the 5th bullet point under "Groups" at [the list of properties of the centralizer and normalizer](https://en.wikipedia.org/wiki/Centralizer_and_normalizer#Properties)), because it's good to have independent confirmation for something so easy to confuse.

### [2021-04-17 14:18:38](https://github.com/leanprover-community/mathlib/commit/21d74c7)
feat(data/equiv/mul_add): use `@[simps]` ([#7213](https://github.com/leanprover-community/mathlib/pull/7213))
Add some `@[simps]` for some algebra maps. This came up in [#6795](https://github.com/leanprover-community/mathlib/pull/6795).

### [2021-04-17 09:45:21](https://github.com/leanprover-community/mathlib/commit/9363a64)
feat(data/nat/choose/sum): Add lower bound lemma for central binomial coefficient ([#7214](https://github.com/leanprover-community/mathlib/pull/7214))
This lemma complements the one above it, and will be useful in proving Bertrand's postulate from the 100 theorems list.

### [2021-04-17 09:45:20](https://github.com/leanprover-community/mathlib/commit/e9a11f6)
feat(analysis/normed_space/operator_norm): generalize to seminormed space ([#7202](https://github.com/leanprover-community/mathlib/pull/7202))
This PR is part of a series of PRs to have seminormed stuff in mathlib.
We generalize here `operator_norm` to `semi_normed_space`. I didn't do anything complicated, essentially I only generalized what works out of the box, without trying to modify the proofs that don't work.

### [2021-04-17 05:06:55](https://github.com/leanprover-community/mathlib/commit/206ecce)
chore(category_theory/subobject): different proof of le_of_comm ([#7229](https://github.com/leanprover-community/mathlib/pull/7229))
This is certainly a shorter proof of `le_of_comm`; whether it is "cleaner" like the comment asked for is perhaps a matter of taste.

### [2021-04-17 05:06:54](https://github.com/leanprover-community/mathlib/commit/0f6c1f1)
feat(order/conditionally_complete_lattice): conditional Inf of intervals ([#7226](https://github.com/leanprover-community/mathlib/pull/7226))
Some new simp lemmas for cInf/cSup of intervals. I tried to use the minimal possible assumptions that I could - some lemmas are therefore in the linear order section and others are just for lattices.

### [2021-04-17 05:06:53](https://github.com/leanprover-community/mathlib/commit/560a009)
feat(category_theory): formally adjoined initial objects are strict ([#7222](https://github.com/leanprover-community/mathlib/pull/7222))

### [2021-04-17 02:40:11](https://github.com/leanprover-community/mathlib/commit/89c16a7)
chore(ring_theory/adjoin.basic): use submodule.closure in algebra.adjoin_eq_span ([#7194](https://github.com/leanprover-community/mathlib/pull/7194))
`algebra.adjoin_eq_span` uses `monoid.closure` that is deprecated. We modify it to use `submonoid.closure`.

### [2021-04-17 02:40:10](https://github.com/leanprover-community/mathlib/commit/b7a3d4e)
feat(test/integration): improve an example ([#7169](https://github.com/leanprover-community/mathlib/pull/7169))
With [#7103](https://github.com/leanprover-community/mathlib/pull/7103), I am able to improve one of my examples.

### [2021-04-16 22:20:07](https://github.com/leanprover-community/mathlib/commit/6b182fc)
feat(category_theory/triangulated/pretriangulated): add definition of pretriangulated categories and triangulated functors between them  ([#7153](https://github.com/leanprover-community/mathlib/pull/7153))
Adds a definition of pretriangulated categories and triangulated functors between them.

### [2021-04-16 22:20:06](https://github.com/leanprover-community/mathlib/commit/110541d)
feat(data/list/basic): fold[rl] recursion principles ([#7079](https://github.com/leanprover-community/mathlib/pull/7079))

### [2021-04-16 17:35:16](https://github.com/leanprover-community/mathlib/commit/49040e5)
feat(data/set): sep true/false simp lemmas ([#7215](https://github.com/leanprover-community/mathlib/pull/7215))

### [2021-04-16 17:35:15](https://github.com/leanprover-community/mathlib/commit/24013e2)
feat(data/finsupp/basic): add finsupp.single_left_injective and docstrings ([#7207](https://github.com/leanprover-community/mathlib/pull/7207))

### [2021-04-16 17:35:14](https://github.com/leanprover-community/mathlib/commit/0688612)
feat(order/rel_iso): constructors for rel embeddings ([#7046](https://github.com/leanprover-community/mathlib/pull/7046))
Alternate constructors for relation and order embeddings which require slightly less to prove.

### [2021-04-16 17:35:13](https://github.com/leanprover-community/mathlib/commit/ea4dce0)
feat(category_theory): the additive envelope, Mat_ C ([#6845](https://github.com/leanprover-community/mathlib/pull/6845))
# Matrices over a category.
When `C` is a preadditive category, `Mat_ C` is the preadditive categoriy
whose objects are finite tuples of objects in `C`, and
whose morphisms are matrices of morphisms from `C`.
There is a functor `Mat_.embedding : C ⥤ Mat_ C` sending morphisms to one-by-one matrices.
`Mat_ C` has finite biproducts.
## The additive envelope
We show that this construction is the "additive envelope" of `C`,
in the sense that any additive functor `F : C ⥤ D` to a category `D` with biproducts
lifts to a functor `Mat_.lift F : Mat_ C ⥤ D`,
Moreover, this functor is unique (up to natural isomorphisms) amongst functors `L : Mat_ C ⥤ D`
such that `embedding C ⋙ L ≅ F`.
(As we don't have 2-category theory, we can't explicitly state that `Mat_ C` is
the initial object in the 2-category of categories under `C` which have biproducts.)
As a consequence, when `C` already has finite biproducts we have `Mat_ C ≌ C`.

### [2021-04-16 14:09:23](https://github.com/leanprover-community/mathlib/commit/108b923)
chore(algebra): add `sub{_mul_action,module,semiring,ring,field,algebra}.copy` ([#7220](https://github.com/leanprover-community/mathlib/pull/7220))
We already have this for sub{monoid,group}. With this in place, we can make `coe subalgebra.range` defeq to `set.range` and similar (left for a follow-up).

### [2021-04-16 14:09:22](https://github.com/leanprover-community/mathlib/commit/e00d688)
chore(group_theory/subgroup): rename `monoid_hom.to_range` to `monoid_hom.range_restrict` ([#7218](https://github.com/leanprover-community/mathlib/pull/7218))
This makes it match:
* `monoid_hom.mrange_restrict`
* `linear_map.range_restrict`
* `ring_hom.range_restrict`
* `ring_hom.srange_restrict`
* `alg_hom.range_restrict`
This also adds a missing simp lemma.

### [2021-04-16 11:48:29](https://github.com/leanprover-community/mathlib/commit/b1acb58)
chore(data/mv_polynomial/basic): golf some proofs ([#7209](https://github.com/leanprover-community/mathlib/pull/7209))

### [2021-04-16 05:10:03](https://github.com/leanprover-community/mathlib/commit/bb9b850)
feat(data/multiset/basic): some multiset lemmas, featuring sum inequalities ([#7090](https://github.com/leanprover-community/mathlib/pull/7090))
Proves some lemmas about `rel` and about inequalities between sums of multisets.

### [2021-04-16 03:40:55](https://github.com/leanprover-community/mathlib/commit/148760e)
feat(category_theory/kernels): missing instances ([#7204](https://github.com/leanprover-community/mathlib/pull/7204))

### [2021-04-16 03:40:54](https://github.com/leanprover-community/mathlib/commit/9d1ab69)
refactor(category_theory/images): improvements ([#7198](https://github.com/leanprover-community/mathlib/pull/7198))
Some improvements to the images API, from `homology2`.

### [2021-04-16 01:12:09](https://github.com/leanprover-community/mathlib/commit/81b8873)
doc(topology/bases): add module + theorem docstrings ([#7193](https://github.com/leanprover-community/mathlib/pull/7193))

### [2021-04-15 20:50:28](https://github.com/leanprover-community/mathlib/commit/8742be7)
fix(.github/PULL_REQUEST_TEMPLATE.md): revert gitpod button URL ([#7210](https://github.com/leanprover-community/mathlib/pull/7210))
Reverts [#7096](https://github.com/leanprover-community/mathlib/pull/7096) since the URL was changed back.

### [2021-04-15 20:50:27](https://github.com/leanprover-community/mathlib/commit/37ab34e)
doc(tactic/congr): example where congr fails, but exact works ([#7208](https://github.com/leanprover-community/mathlib/pull/7208))
As requested on zulip:
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.237084/near/234652967

### [2021-04-15 20:50:26](https://github.com/leanprover-community/mathlib/commit/b4201e7)
chore(group/ring_hom): fix a nat nsmul diamond ([#7201](https://github.com/leanprover-community/mathlib/pull/7201))
The space of additive monoid should be given a proper `nat`-action, by the pointwise action, to avoid diamonds.

### [2021-04-15 15:46:19](https://github.com/leanprover-community/mathlib/commit/50a843e)
chore(algebra/module/submodule): add missing coe lemmas ([#7205](https://github.com/leanprover-community/mathlib/pull/7205))

### [2021-04-15 15:46:18](https://github.com/leanprover-community/mathlib/commit/14c625e)
feat(linear_algebra/basic): add span_eq_add_submonoid.closure ([#7200](https://github.com/leanprover-community/mathlib/pull/7200))
The `ℕ` span equals `add_submonoid.closure`.

### [2021-04-15 15:46:16](https://github.com/leanprover-community/mathlib/commit/0f3ca67)
feat(number_theory/bernoulli): golf ([#7197](https://github.com/leanprover-community/mathlib/pull/7197))
I golf the file to improve scannability and stylistic uniformity.

### [2021-04-15 15:46:15](https://github.com/leanprover-community/mathlib/commit/6a4d298)
chore(topology/vector_bundle): generalize to topological semimodules ([#7183](https://github.com/leanprover-community/mathlib/pull/7183))

### [2021-04-15 15:46:13](https://github.com/leanprover-community/mathlib/commit/f92dc6c)
feat(algebra/group_with_zero): non-associative monoid_with_zero ([#7176](https://github.com/leanprover-community/mathlib/pull/7176))
This introduces a new `mul_zero_one_class` which is `monoid_with_zero` without associativity, just as `mul_one_class` is `monoid` without associativity.
This would help expand the scope of [#6786](https://github.com/leanprover-community/mathlib/pull/6786) to include ring_homs, something that was previously blocked by `monoid_with_zero` and the `non_assoc_semiring` having no common ancestor with `0`, `1`, and `*`.
Using [#6865](https://github.com/leanprover-community/mathlib/pull/6865) as a template for what to cover, this PR includes;
* Generalizing `monoid_with_zero_hom` to require the weaker `mul_zero_one_class`. This has a slight downside, in that `some_mwzh.to_monoid_hom` now holds as its typeclass argument `mul_zero_one_class.to_mul_one_class` instead of `monoid_with_zero.to_monoid`. This means that lemmas about `monoid_hom`s with associate multiplication no longer always elaborate correctly without type annotations, as the `monoid` instance has to be found by typeclass search instead of unification.
* `function.(in|sur)jective.mul_zero_one_class`
* `equiv.mul_zero_one_class`
* Adding instances for:
  * `prod`
  * `pi`
  * `set_semiring`
  * `with_zero`
  * `locally_constant`
  * `monoid_algebra`
  * `add_monoid_algebra`

### [2021-04-15 15:46:12](https://github.com/leanprover-community/mathlib/commit/adfeb24)
refactor(algebra/big_operators/order): use `to_additive` ([#7173](https://github.com/leanprover-community/mathlib/pull/7173))
* Replace many lemmas about `finset.sum` with lemmas about `finset.prod` + `@[to_additive]`;
* Avoid `s \ t` in `finset.sum_lt_sum_of_subset`.
* Use `M`, `N` instead of `α`, `β` for types with algebraic structures.

### [2021-04-15 15:46:11](https://github.com/leanprover-community/mathlib/commit/5806a94)
feat(data/nat/basic, data/nat/prime): add various lemmas ([#7171](https://github.com/leanprover-community/mathlib/pull/7171))

### [2021-04-15 08:26:50](https://github.com/leanprover-community/mathlib/commit/4b835cc)
feat(category_theory/subobject): proof golf and some API ([#7170](https://github.com/leanprover-community/mathlib/pull/7170))

### [2021-04-15 08:26:48](https://github.com/leanprover-community/mathlib/commit/dbd468d)
feat(analysis/special_functions/trigonometric): periodicity of sine, cosine ([#7107](https://github.com/leanprover-community/mathlib/pull/7107))
Previously we only had `sin (x + 2 * π) = sin x` and `cos (x + 2 * π) = cos x`. I extend those results to cover shifts by any integer multiple of `2 * π`, not just `2 * π`. I also provide corresponding `sub` lemmas.

### [2021-04-15 04:42:22](https://github.com/leanprover-community/mathlib/commit/3a64d11)
chore(scripts): update nolints.txt ([#7195](https://github.com/leanprover-community/mathlib/pull/7195))
I am happy to remove some nolints for you!

### [2021-04-15 04:42:20](https://github.com/leanprover-community/mathlib/commit/c73b165)
chore(data/fin,data/finset): a few lemmas ([#7168](https://github.com/leanprover-community/mathlib/pull/7168))
* `fin.heq_fun_iff`: use `Sort*` instead of `Type*`;
* `fin.cast_refl`: take `h : n = n := rfl` as an argument;
* `fin.cast_to_equiv`, `fin.cast_eq_cast`: relate `fin.cast` to `_root_.cast`;
* `finset.map_cast_heq`: new lemma;
* `finset.subset_univ`: add `@[simp]`;
* `card_finset_fin_le`, `fintype.card_finset_len`, `fin.prod_const` : new lemmas;
* `order_iso.refl`: new definition.

### [2021-04-14 23:14:49](https://github.com/leanprover-community/mathlib/commit/f74213b)
feat(algebra/ordered_group): proof of le without density ([#7191](https://github.com/leanprover-community/mathlib/pull/7191))

### [2021-04-14 23:14:48](https://github.com/leanprover-community/mathlib/commit/60060c3)
feat(field_theory/algebraic_closure): define `is_alg_closed.splits_codomain` ([#7187](https://github.com/leanprover-community/mathlib/pull/7187))
Let `p : polynomial K` and `k` be an algebraically closed extension of `K`. Showing that `p` splits in `k` used to be a bit awkward because `is_alg_closed.splits` only gives `splits (p.map (f : k →+* K)) id`, which you still have to `simp` to `splits p f`.
This PR defines `is_alg_closed.splits_codomain`, showing `splits p f` directly by doing the `simp`ing for you. It also renames `polynomial.splits'` to `is_alg_closed.splits_domain`, for symmetry.
Zulip discussion starts [here](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Complex.20numbers.20sums/near/234481576)

### [2021-04-14 23:14:47](https://github.com/leanprover-community/mathlib/commit/3d67b69)
chore(algebra/group_power/basic): `pow_abs` does not need commutativity ([#7178](https://github.com/leanprover-community/mathlib/pull/7178))

### [2021-04-14 23:14:46](https://github.com/leanprover-community/mathlib/commit/e4843ea)
chore(category_theory/subobject): split off specific subobjects ([#7167](https://github.com/leanprover-community/mathlib/pull/7167))

### [2021-04-14 23:14:44](https://github.com/leanprover-community/mathlib/commit/74e1e83)
feat(topological/homeomorph): the image of a set ([#7147](https://github.com/leanprover-community/mathlib/pull/7147))

### [2021-04-14 23:14:43](https://github.com/leanprover-community/mathlib/commit/5052ad9)
feat(data/nat/basic): (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n ([#7132](https://github.com/leanprover-community/mathlib/pull/7132))
... and the dual statement
`(∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n`
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/semilattice.2C.20dvd.2C.20associated

### [2021-04-14 23:14:42](https://github.com/leanprover-community/mathlib/commit/4605b55)
feat(algebra/big_operators/finprod): add a few lemmas ([#7130](https://github.com/leanprover-community/mathlib/pull/7130))
* add `finprod_nonneg`, `finprod_cond_nonneg`, and `finprod_eq_zero`;
* use `α → Prop` instead of `set α` in
`finprod_mem_eq_prod_of_mem_iff`, rename to `finprod_cond_eq_prod_of_cond_iff`.

### [2021-04-14 23:14:41](https://github.com/leanprover-community/mathlib/commit/49fd719)
feat(topology/algebra,geometry/manifold): continuity and smoothness of locally finite products of functions ([#7128](https://github.com/leanprover-community/mathlib/pull/7128))

### [2021-04-14 23:14:40](https://github.com/leanprover-community/mathlib/commit/d820a9d)
feat(algebra/big_operators): some lemmas on big operators and `fin` ([#7119](https://github.com/leanprover-community/mathlib/pull/7119))
A couple of lemmas that I needed for `det_vandermonde` ([#7116](https://github.com/leanprover-community/mathlib/pull/7116)).
I put them in a new file because I didn't see any obvious point that they fit in the import hierarchy. `big_operators/basic.lean` would be the alternative, but that file is big enough as it is.

### [2021-04-14 23:14:39](https://github.com/leanprover-community/mathlib/commit/8d3e8b5)
feat(archive/imo): IMO 1977 Q6 ([#7097](https://github.com/leanprover-community/mathlib/pull/7097))
Formalization of IMO 1977/6

### [2021-04-14 23:14:38](https://github.com/leanprover-community/mathlib/commit/456e5af)
feat(order/filter/*, topology/subset_properties): Filter Coprod ([#7073](https://github.com/leanprover-community/mathlib/pull/7073))
Define the "coproduct" of many filters (not just two) as
`protected def Coprod (f : Π d, filter (κ d)) : filter (Π d, κ d) :=
⨆ d : δ, (f d).comap (λ k, k d)`
and prove the three lemmas which motivated this construction: (finite!) coproduct of cofinite filters is the cofinite filter, coproduct of cocompact filters is the cocompact filter, and monotonicity; see also [#6372](https://github.com/leanprover-community/mathlib/pull/6372)
Co-authored by: Heather Macbeth @hrmacbeth

### [2021-04-14 23:14:37](https://github.com/leanprover-community/mathlib/commit/89196b2)
feat(group_theory/perm/cycle_type): Cycle type of a permutation ([#6999](https://github.com/leanprover-community/mathlib/pull/6999))
This PR defines the cycle type of a permutation.
At some point we should prove the bijection between partitions and conjugacy classes.

### [2021-04-14 23:14:36](https://github.com/leanprover-community/mathlib/commit/5775ef7)
feat(order/ideal, order/pfilter, order/prime_ideal): added `ideal_inter_nonempty`, proved that a maximal ideal is prime ([#6924](https://github.com/leanprover-community/mathlib/pull/6924))
- `ideal_inter_nonempty`: the intersection of any two ideals is nonempty. A preorder with joins and this property satisfies that its ideal poset is a lattice.
- An ideal is prime iff `x \inf y \in I` implies `x \in I` or `y \in I`.
- A maximal ideal in a distributive lattice is prime.

### [2021-04-14 18:40:20](https://github.com/leanprover-community/mathlib/commit/3df0f77)
feat(topology/sheaves): Induced map on stalks ([#7092](https://github.com/leanprover-community/mathlib/pull/7092))
This PR defines stalk maps for morphisms of presheaves. We prove that a morphism of type-valued sheaves is an isomorphism if and only if all the stalk maps are isomorphisms.
A few more lemmas about unique gluing are also added, as well as docstrings.

### [2021-04-14 18:40:15](https://github.com/leanprover-community/mathlib/commit/98c483b)
feat(ring_theory/hahn_series): a `finsupp` of Hahn series is a `summable_family` ([#7091](https://github.com/leanprover-community/mathlib/pull/7091))
Defines `summable_family.of_finsupp`

### [2021-04-14 18:40:13](https://github.com/leanprover-community/mathlib/commit/f444128)
chore(algebra/direct_sum_graded): golf proofs ([#7029](https://github.com/leanprover-community/mathlib/pull/7029))
Simplify the proofs of mul_assoc and mul_comm, and speed up all the
proofs that were slow.
Total elaboration time for this file is reduced from 12.9s to 1.7s
(on my machine), and total CPU time is reduced from 19.8s to 6.8s.
All the remaining elaboration times are under 200ms.
The main idea is to explicitly construct bundled homomorphisms
corresponding to `λ a b c, a * b * c` and `λ a b c, a * (b * c)`
respectively.  Then in proving the equality between those, we can
unpack all the arguments immediately, and the remaining rewrites
needed become simpler.

### [2021-04-14 18:40:11](https://github.com/leanprover-community/mathlib/commit/3379f3e)
feat(archive/100-theorems-list): add proof of Heron's formula ([#6989](https://github.com/leanprover-community/mathlib/pull/6989))
This proves Heron's Formula for triangles, which happens to be Theorem 57 on Freek's 100 Theorems.

### [2021-04-14 18:40:10](https://github.com/leanprover-community/mathlib/commit/2715769)
feat(geometry/manifold/instances/units_of_normed_algebra): the units of a normed algebra are a topological group and a smooth manifold ([#6981](https://github.com/leanprover-community/mathlib/pull/6981))
I decided to make a small PR now with only a partial result because Heather suggested proving GL^n is a Lie group on Zulip, and I wanted to share the work I did so that whoever wants to take over the task does not have to start from scratch.
Most of the ideas in this PR are by @hrmacbeth, as I was planning on doing a different proof, but I agreed Heather's one was better.
What remains to do in a future PR to prove GLn is a Lie group is to add and prove the following instance to the file `geometry/manifold/instances/units_of_normed_algebra.lean`:
```
instance units_of_normed_algebra.lie_group
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] :
  lie_group (model_with_corners_self 𝕜 R) (units R) :=
{
  smooth_mul := begin
    sorry,
  end,
  smooth_inv := begin
    sorry,
  end,
  ..units_of_normed_algebra.smooth_manifold_with_corners, /- Why does it not find the instance alone? -/
}
```

### [2021-04-14 18:40:08](https://github.com/leanprover-community/mathlib/commit/e4edf46)
feat(algebra/direct_sum_graded): `A 0` is a ring, `A i` is an `A 0`-module, and `direct_sum.of A 0` is a ring_hom ([#6851](https://github.com/leanprover-community/mathlib/pull/6851))
In a graded ring, grade 0 is itself a ring, and grade `i` (and therefore, the overall direct_sum) is a module over elements of grade 0.
This stops just short of the structure necessary to make a graded ring a graded algebra over elements of grade 0; this requires some extra assumptions and probably a new typeclass, so is best left to its own PR.
The main results here are `direct_sum.grade_zero.comm_ring`, `direct_sum.grade_zero.semimodule`, and `direct_sum.of_zero_ring_hom`.
Note that we have no way to let the user provide their own ring structure on `A 0`, as `[Π i, add_comm_monoid (A i)] [semiring (A 0)]` provides `add_comm_monoid (A 0)` twice.

### [2021-04-14 18:40:07](https://github.com/leanprover-community/mathlib/commit/24dc410)
feat(field_theory/separable_degree): introduce the separable degree ([#6743](https://github.com/leanprover-community/mathlib/pull/6743))
We introduce the definition of the separable degree of a polynomial. We prove that every irreducible polynomial can be contracted to a separable polynomial. We show that the separable degree divides the degree of the polynomial.
This formalizes a lemma in the Stacks Project, cf. https://stacks.math.columbia.edu/tag/09H0 
We also show that the separable degree is unique.

### [2021-04-14 18:40:05](https://github.com/leanprover-community/mathlib/commit/f12575e)
feat(topology/topological_fiber_bundle): topological fiber bundle over `[a, b]` is trivial ([#6555](https://github.com/leanprover-community/mathlib/pull/6555))

### [2021-04-14 16:58:05](https://github.com/leanprover-community/mathlib/commit/b3eabc1)
hack(ci): run lean make twice ([#7192](https://github.com/leanprover-community/mathlib/pull/7192))
At the moment running `lean --make src` after `leanproject up` will recompile some files.  Merging this PR should have the effect of uploading these newly compiled olean files.
This also makes github actions call `lean --make src` twice to prevent this problem from happening in the first place.

### [2021-04-14 08:29:46](https://github.com/leanprover-community/mathlib/commit/6380155)
refactor(*): kill nat multiplication diamonds ([#7084](https://github.com/leanprover-community/mathlib/pull/7084))
An `add_monoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`polynomial R` has a natural `R`-action defined by multiplication on the coefficients. This means
that `polynomial ℕ` has two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself). This is the case on current
mathlib, with such non-defeq diamonds all over the place.
To solve this issue, we embed an `ℕ`-action in the definition of an `add_monoid` (which is by
default the naive action `a + ... + a`, but can be adjusted when needed -- it should always be equal 
to this one, but not necessarily definitionally), and declare
a `has_scalar ℕ α` instance using this action. This is yet another example of the forgetful inheritance
pattern that we use in metric spaces, embedding a topology and a uniform structure in it (except that
here the functor from additive monoids to nat-modules is faithful instead of forgetful, but it doesn't 
make a difference).
More precisely, we define
```lean
def nsmul_rec [has_add M] [has_zero M] : ℕ → M → M
| 0     a := 0
| (n+1) a := nsmul_rec n a + a
class add_monoid (M : Type u) extends add_semigroup M, add_zero_class M :=
(nsmul : ℕ → M → M := nsmul_rec)
(nsmul_zero' : ∀ x, nsmul 0 x = 0 . try_refl_tac)
(nsmul_succ' : ∀ (n : ℕ) x, nsmul n.succ x = nsmul n x + x . try_refl_tac)
```
For example, when we define `polynomial R`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `add_monoid`). In this way, the two natural `has_scalar ℕ (polynomial ℕ)` instances are defeq.
The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.
With this refactor, all the diamonds are gone. Or rather, all the diamonds I noticed are gone, but if
there are still some diamonds then they can be fixed, contrary to before.
Also, the notation `•ℕ` is gone, just use `•`.

### [2021-04-14 03:47:14](https://github.com/leanprover-community/mathlib/commit/3ec54df)
feat(data/finset/lattice): le_sup_iff and lt_sup_iff ([#7182](https://github.com/leanprover-community/mathlib/pull/7182))
A few changes and additions to finset/lattice in response to this Zulip thread https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/finset.2Esup'

### [2021-04-14 03:47:13](https://github.com/leanprover-community/mathlib/commit/500301e)
feat(algebra/group/hom): `monoid_with_zero_hom.to_monoid_hom_injective` and co. ([#7174](https://github.com/leanprover-community/mathlib/pull/7174))
This came up in [#6788](https://github.com/leanprover-community/mathlib/pull/6788).

### [2021-04-14 03:47:12](https://github.com/leanprover-community/mathlib/commit/4d19f5f)
feat(algebraic_geometry): Basic opens form basis of zariski topology ([#7152](https://github.com/leanprover-community/mathlib/pull/7152))
Fills in a few lemmas in `prime_spectrum.lean`, in particular that basic opens form a basis

### [2021-04-13 23:14:15](https://github.com/leanprover-community/mathlib/commit/724f804)
refactor(src/analysis/normed_space/linear_isometry): generalize to semi_normed_group ([#7122](https://github.com/leanprover-community/mathlib/pull/7122))
This is part of a series of PR to include the theory of seminormed things in mathlib.

### [2021-04-13 19:58:08](https://github.com/leanprover-community/mathlib/commit/06f7d3f)
feat(src/set_theory/surreal): add numeric_add and numeric_omega lemmas ([#7179](https://github.com/leanprover-community/mathlib/pull/7179))
Adds a couple of lemmas about surreal numbers: proving that natural numbers and omega are numeric.
[Zulip](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Surreal.20numbers/near/234243582)

### [2021-04-12 23:25:53](https://github.com/leanprover-community/mathlib/commit/46302c7)
refactor(algebra/group/defs): remove left-right_cancel_comm_monoids ([#7134](https://github.com/leanprover-community/mathlib/pull/7134))
There were 6 distinct classes
* `(add_)left_cancel_comm_monoid`,
* `(add_)right_cancel_comm_monoid`,
* `(add_)cancel_comm_monoid`.
I removed them all, except for the last 2:
* `(add_)cancel_comm_monoid`.
The new typeclass `cancel_comm_monoid` requires only `a * b = a * c → b = c`, and deduces the other version from commutativity.

### [2021-04-12 19:13:54](https://github.com/leanprover-community/mathlib/commit/92d5cab)
feat(logic/function/iterate): `f^[n]^[m] = f^[m]^[n]` ([#7121](https://github.com/leanprover-community/mathlib/pull/7121))
Prove `f^[n]^[m]=f^[m]^[n]` and improve some docs.

### [2021-04-12 15:23:30](https://github.com/leanprover-community/mathlib/commit/2af0147)
chore(data/equiv/basic): add simps attribute to some defs ([#7137](https://github.com/leanprover-community/mathlib/pull/7137))

### [2021-04-12 12:44:29](https://github.com/leanprover-community/mathlib/commit/a1c2bb7)
feat(data/zsqrtd/basic): add coe_int_dvd_iff lemma ([#7161](https://github.com/leanprover-community/mathlib/pull/7161))

### [2021-04-12 12:44:28](https://github.com/leanprover-community/mathlib/commit/16e2c6c)
chore(data/matrix/basic): lemmas for `minor` about `diagonal`, `one`, and `mul` ([#7133](https://github.com/leanprover-community/mathlib/pull/7133))
The `minor_mul` lemma here has weaker hypotheses than the previous `reindex_mul`, as it only requires one mapping to be bijective.

### [2021-04-12 08:44:54](https://github.com/leanprover-community/mathlib/commit/f9c787d)
refactor(algebra/big_operators, *): specialize `finset.prod_bij` to `fintype.prod_equiv` ([#7109](https://github.com/leanprover-community/mathlib/pull/7109))
Often we want to apply `finset.prod_bij` to the case where the product is taken over `finset.univ` and the bijection is already a bundled `equiv`. This PR adds `fintype.prod_equiv` as a specialization for exactly these cases, filling in most of the arguments already.

### [2021-04-12 08:44:53](https://github.com/leanprover-community/mathlib/commit/001628b)
feat(category_theory/subobject/factor_thru): lemmas in a preadditive category ([#7104](https://github.com/leanprover-community/mathlib/pull/7104))
More side effects of recent reworking of homology.

### [2021-04-12 08:44:51](https://github.com/leanprover-community/mathlib/commit/68e894d)
feat(finset/lattice): sup' is to sup as max' is to max ([#7087](https://github.com/leanprover-community/mathlib/pull/7087))
Introducing `finset.sup'`, modelled on `finset.max'` but having no need for a `linear_order`. I wanted this for functions so also provide `sup_apply` and `sup'_apply`. By using `cons` instead of `insert` the axiom of choice is avoided throughout and I have replaced the proofs of three existing lemmas (`sup_lt_iff`, `comp_sup_eq_sup_comp`, `sup_closed_of_sup_closed`) that didn't need it. I have removed `sup_subset` entirely as it was surely introduced in ignorance of `sup_mono`.

### [2021-04-12 05:36:40](https://github.com/leanprover-community/mathlib/commit/193dd5b)
feat(algebra/{algebra, module}/basic): make 3 smultiplication by 1 `simp` lemmas ([#7166](https://github.com/leanprover-community/mathlib/pull/7166))
The three lemmas in the merged PR [#7094](https://github.com/leanprover-community/mathlib/pull/7094) could be simp lemmas.  This PR makes this suggestion.
While I was at it,
* I moved one of the lemmas outside of the `alg_hom` namespace,
* I fixed a typo in a doc string of a tutorial.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/trying.20out.20a.20.60simp.60.20lemma

### [2021-04-11 12:32:54](https://github.com/leanprover-community/mathlib/commit/5694309)
feat(algebra/algebra/basic algebra/module/basic): add 3 lemmas m • (1 : R) = ↑m ([#7094](https://github.com/leanprover-community/mathlib/pull/7094))
Three lemmas asserting `m • (1 : R) = ↑m`, where `m` is a natural number, an integer or a rational number.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.60smul_one_eq_coe.60

### [2021-04-11 11:08:53](https://github.com/leanprover-community/mathlib/commit/fbf6219)
feat(analysis/special_functions/exp_log): add `continuity` attribute to `continuous_exp` ([#7157](https://github.com/leanprover-community/mathlib/pull/7157))

### [2021-04-11 10:03:43](https://github.com/leanprover-community/mathlib/commit/1442f70)
feat(measure_theory/interval_integral): variants of integral_comp lemmas ([#7103](https://github.com/leanprover-community/mathlib/pull/7103))
Alternate versions of some of our `integral_comp` lemmas which work even when `c = 0`.

### [2021-04-11 05:39:27](https://github.com/leanprover-community/mathlib/commit/fc8e18c)
feat(topology/continuous_function): comp_right_* ([#7145](https://github.com/leanprover-community/mathlib/pull/7145))
We setup variations on `comp_right_* f`, where `f : C(X, Y)`
(that is, precomposition by a continuous map),
as a morphism `C(Y, T) → C(X, T)`, respecting various types of structure.
In particular:
* `comp_right_continuous_map`, the bundled continuous map (for this we need `X Y` compact).
* `comp_right_homeomorph`, when we precompose by a homeomorphism.
* `comp_right_alg_hom`, when `T = R` is a topological ring.

### [2021-04-11 04:38:14](https://github.com/leanprover-community/mathlib/commit/383f591)
chore(scripts): update nolints.txt ([#7154](https://github.com/leanprover-community/mathlib/pull/7154))
I am happy to remove some nolints for you!

### [2021-04-11 01:51:24](https://github.com/leanprover-community/mathlib/commit/c6e62cf)
feat(analysis/normed_space/finite_dimension): set of `f : E →L[𝕜] F` of rank `≥n` is open ([#7022](https://github.com/leanprover-community/mathlib/pull/7022))

### [2021-04-10 14:43:35](https://github.com/leanprover-community/mathlib/commit/a83230e)
feat(linear_algebra/eigenspace): define the maximal generalized eigenspace ([#7125](https://github.com/leanprover-community/mathlib/pull/7125))
And prove that it is of the form kernel of `(f - μ • id) ^ k` for some finite `k` for endomorphisms of Noetherian modules.

### [2021-04-10 14:43:34](https://github.com/leanprover-community/mathlib/commit/026150f)
feat(geometry/manifold): a manifold with σ-countable topology has second countable topology ([#6948](https://github.com/leanprover-community/mathlib/pull/6948))

### [2021-04-10 12:50:55](https://github.com/leanprover-community/mathlib/commit/6b3803d)
chore(analysis/normed_space/inner_product): simplify two proofs ([#7149](https://github.com/leanprover-community/mathlib/pull/7149))

### [2021-04-10 12:50:54](https://github.com/leanprover-community/mathlib/commit/363a286)
chore(*): speedup slow proofs ([#7148](https://github.com/leanprover-community/mathlib/pull/7148))
Some proofs using heavy `rfl` or heavy `obviously` can be sped up considerably. Done in this PR for some outstanding examples.

### [2021-04-10 08:01:57](https://github.com/leanprover-community/mathlib/commit/7e93367)
feat(analysis/normed_space/banach): a range with closed complement is itself closed ([#6972](https://github.com/leanprover-community/mathlib/pull/6972))
If the range of a continuous linear map has a closed complement, then it is itself closed. For instance, the range can not be a dense hyperplane. We prove it when, additionally, the map has trivial kernel. The general case will follow from this particular case once we have quotients of normed spaces, which are currently only in Lean Liquid.
Along the way, we fill several small gaps in the API of continuous linear maps.

### [2021-04-10 06:53:21](https://github.com/leanprover-community/mathlib/commit/d39c3a2)
feat(data/zsqrtd/basic): add some lemmas about norm ([#7114](https://github.com/leanprover-community/mathlib/pull/7114))

### [2021-04-10 06:53:20](https://github.com/leanprover-community/mathlib/commit/7ae2af6)
feat(group_theory/is_free_group): promote `is_free_group.lift'` to an equiv ([#7110](https://github.com/leanprover-community/mathlib/pull/7110))
While non-computable, this makes the API of `is_free_group` align more closely with `free_group`.
Based on discussion in the original PR, this doesn't go as far as changing the definition of `is_free_group` to take the equiv directly.
This additionally:
* adds the definition `lift`, a universe polymorphic version of `lift'`
* adds the lemmas:
  * `lift'_eq_free_group_lift`
  * `lift_eq_free_group_lift`
  * `of_eq_free_group_of`
  * `ext_hom'`
  * `ext_hom`
* renames `is_free_group.iso_free_group_of_is_free_group` to the shorter `is_free_group.to_free_group`
* removes lemmas absent from the `free_group` API that are no longer needed for the proofs here:
  * `end_is_id`
  * `eq_lift`

### [2021-04-10 03:46:26](https://github.com/leanprover-community/mathlib/commit/575b791)
chore(scripts): update nolints.txt ([#7144](https://github.com/leanprover-community/mathlib/pull/7144))
I am happy to remove some nolints for you!

### [2021-04-10 03:46:25](https://github.com/leanprover-community/mathlib/commit/7138d35)
feat(category_theory/action): currying ([#7085](https://github.com/leanprover-community/mathlib/pull/7085))
A functor from an action category can be 'curried' to an ordinary group homomorphism. Also defines transitive group actions.

### [2021-04-10 00:01:44](https://github.com/leanprover-community/mathlib/commit/e269dbc)
feat(tactic/itauto): Complete intuitionistic prover ([#7057](https://github.com/leanprover-community/mathlib/pull/7057))
[As requested on Zulip.](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/tauto.20is.20a.20decision.20procedure.3F/near/233222469)

### [2021-04-10 00:01:43](https://github.com/leanprover-community/mathlib/commit/8efb93b)
feat(combinatorics/simple_graph/strongly_regular): add definition of strongly regular graph and proof that complete graph is SRG ([#7044](https://github.com/leanprover-community/mathlib/pull/7044))
Add definition of strongly regular graph and proof that complete graphs are strongly regular. Part of [#5698](https://github.com/leanprover-community/mathlib/pull/5698) to prove facts about strongly regular graphs.

### [2021-04-09 22:57:37](https://github.com/leanprover-community/mathlib/commit/309e3b0)
feat(category_theory/subobjects): improvements to API ([#6932](https://github.com/leanprover-community/mathlib/pull/6932))
These additions have been useful while setting up homology.

### [2021-04-09 18:56:37](https://github.com/leanprover-community/mathlib/commit/763c5c3)
chore(data/list/basic): avoid the axiom of choice ([#7135](https://github.com/leanprover-community/mathlib/pull/7135))

### [2021-04-09 12:24:51](https://github.com/leanprover-community/mathlib/commit/fe5d660)
feat(algebra/category/Module): arbitrary colimits ([#7099](https://github.com/leanprover-community/mathlib/pull/7099))
This is just the "semi-automated" construction of arbitrary colimits in the category or `R`-modules, following the same model as for `Mon`, `AddCommGroup`, etc.
We already have finite colimits from the `abelian` instance. One could also give definitionally nicer colimits as quotients of finitely supported functions. But this is better than nothing!

### [2021-04-09 12:24:50](https://github.com/leanprover-community/mathlib/commit/0ec9cd8)
chore(data/fin): add simp lemmas about 1 and cast_{pred, succ} ([#7067](https://github.com/leanprover-community/mathlib/pull/7067))

### [2021-04-09 12:24:49](https://github.com/leanprover-community/mathlib/commit/dd2466c)
chore(data/set_like): Add coe_strict_mono and coe_mono ([#7004](https://github.com/leanprover-community/mathlib/pull/7004))
This adds the following monotonicity lemmas:
* `set_like.coe_mono`, `set_like.coe_strict_mono`
* `submodule.to_add_submonoid_mono`, `submodule.to_add_submonoid_strict_mono`
* `submodule.to_add_subgroup_mono`, `submodule.to_add_subgroup_strict_mono`
* `subsemiring.to_submonoid_mono`, `submodule.to_submonoid_strict_mono`
* `subsemiring.to_add_submonoid_mono`, `submodule.to_add_submonoid_strict_mono`
* `subring.to_subsemiring_mono`, `subring.to_subsemiring_strict_mono`
* `subring.to_add_subgroup_mono`, `subring.to_add_subgroup_strict_mono`
* `subring.to_submonoid_mono`, `subring.to_submonoid_strict_mono`
This also makes `tactic.monotonicity.basic` a lighter-weight import, so that the `@[mono]` attribute is accessible in more places.

### [2021-04-09 12:24:48](https://github.com/leanprover-community/mathlib/commit/362844d)
feat(category_theory/preadditive): a category induced from a preadditive category is preadditive ([#6883](https://github.com/leanprover-community/mathlib/pull/6883))

### [2021-04-09 08:28:56](https://github.com/leanprover-community/mathlib/commit/aa1fa0b)
feat(data/option/basic): option valued choice operator ([#7101](https://github.com/leanprover-community/mathlib/pull/7101))

### [2021-04-09 04:34:52](https://github.com/leanprover-community/mathlib/commit/6610e8f)
feat(data/fintype): golf, move and dualise proof ([#7126](https://github.com/leanprover-community/mathlib/pull/7126))
This PR moves `fintype.exists_max` higher up in the import tree, and golfs it, and adds the dual version, `fintype.exists_min`. The name and statement are unchanged.

### [2021-04-09 04:34:51](https://github.com/leanprover-community/mathlib/commit/991dc26)
chore(linear_algebra/multilinear): relax requirements on `multilinear_map.pi_ring_equiv` ([#7117](https://github.com/leanprover-community/mathlib/pull/7117))

### [2021-04-09 04:34:50](https://github.com/leanprover-community/mathlib/commit/0b52522)
feat(test/integration): update with new examples ([#7105](https://github.com/leanprover-community/mathlib/pull/7105))
Add examples made possible by [#6787](https://github.com/leanprover-community/mathlib/pull/6787), [#6795](https://github.com/leanprover-community/mathlib/pull/6795), [#7010](https://github.com/leanprover-community/mathlib/pull/7010).

### [2021-04-09 04:34:49](https://github.com/leanprover-community/mathlib/commit/6dd9a54)
feat(tactic/simps): allow composite projections  ([#7074](https://github.com/leanprover-community/mathlib/pull/7074))
* Allows custom simps-projections that are compositions of multiple projections. This is useful when extending structures without the `old_structure_cmd`.
* Coercions that are compositions of multiple projections are *not* automatically recognized, and should be declared manually (coercions that are definitionally equal to a single projection are still automatically recognized).
* Custom simps projections should now be declared using the name used by `simps`. E.g. `equiv.simps.symm_apply` instead of `equiv.simps.inv_fun`.
* You can disable a projection `proj` being generated by default by `simps` using `initialize_simps_projections (-proj)`

### [2021-04-09 03:28:24](https://github.com/leanprover-community/mathlib/commit/29b834d)
feat(category_theory, algebra/category): AddCommGroup is well-powered ([#7006](https://github.com/leanprover-community/mathlib/pull/7006))

### [2021-04-09 02:29:48](https://github.com/leanprover-community/mathlib/commit/4e607eb)
chore(scripts): update nolints.txt ([#7129](https://github.com/leanprover-community/mathlib/pull/7129))
I am happy to remove some nolints for you!

### [2021-04-09 02:29:47](https://github.com/leanprover-community/mathlib/commit/505ffa9)
feat(analysis/special_functions/integrals): integral of `cos x ^ 2 - sin x ^ 2` ([#7012](https://github.com/leanprover-community/mathlib/pull/7012))
An example of a direct application of integration by parts.

### [2021-04-08 22:31:17](https://github.com/leanprover-community/mathlib/commit/92ec949)
feat(data/equiv/basic): swap_apply_eq_iff ([#7102](https://github.com/leanprover-community/mathlib/pull/7102))

### [2021-04-08 15:56:48](https://github.com/leanprover-community/mathlib/commit/379dd7d)
chore(algebra/ring_quot): Provide `sub` explicitly to `ring_quot` ([#7112](https://github.com/leanprover-community/mathlib/pull/7112))
This means that using `ring_quot.mk (A - B) = ring_quot.mk A - ring_quot.mk B` is true by definition, even if `A - B = A + -B` is not true by definition.

### [2021-04-08 15:56:47](https://github.com/leanprover-community/mathlib/commit/54ac48a)
chore(data/matrix/basic): add simp lemmas about `minor`, move `reindex` to `matrix.basic` since it knows nothing about linear algebra ([#7083](https://github.com/leanprover-community/mathlib/pull/7083))

### [2021-04-08 15:56:46](https://github.com/leanprover-community/mathlib/commit/fb74f98)
chore(data/set/finite): set.finite.sup ([#7080](https://github.com/leanprover-community/mathlib/pull/7080))

### [2021-04-08 15:56:45](https://github.com/leanprover-community/mathlib/commit/bcf5b1a)
feat(data/fintype/basic): to_finset lattice lemmas ([#7077](https://github.com/leanprover-community/mathlib/pull/7077))
While we do not have lattice homomorphisms, we can still provide some similar API.

### [2021-04-08 15:56:44](https://github.com/leanprover-community/mathlib/commit/56e5248)
feat(order/order_iso_nat): add another flavour of well-foundedness for partial orders ([#5434](https://github.com/leanprover-community/mathlib/pull/5434))

### [2021-04-08 14:49:49](https://github.com/leanprover-community/mathlib/commit/f474756)
chore(category_theory/abelian): enable instances ([#7106](https://github.com/leanprover-community/mathlib/pull/7106))
This PR is extracted from Markus' `projective` branch. It just turns on, as global instances, various instances provided by an `abelian` category. In the past these weren't instances, because `has_limit` carried data which could conflict.

### [2021-04-08 06:49:07](https://github.com/leanprover-community/mathlib/commit/8e7028c)
feat(topology/unit_interval): abstract out material about [0,1] ([#7056](https://github.com/leanprover-community/mathlib/pull/7056))
Separates out some material about `[0,1]` from `topology/path_connected.lean`, and adds a very simple tactic.

### [2021-04-08 06:49:06](https://github.com/leanprover-community/mathlib/commit/c6b0636)
feat(archive/imo): formalize IMO 2008 Q3 ([#7025](https://github.com/leanprover-community/mathlib/pull/7025))

### [2021-04-08 06:49:05](https://github.com/leanprover-community/mathlib/commit/9c2a3e7)
refactor(analysis/normed_space/add_torsor): generalize to semi_normed_space ([#7016](https://github.com/leanprover-community/mathlib/pull/7016))
This part of a series of PR to include the theory of `semi_normed_space` in mathlib.

### [2021-04-08 06:49:04](https://github.com/leanprover-community/mathlib/commit/c5ea4cd)
feat(group_theory/perm): define the permutation `(0 1 ... (i : fin n))` ([#6815](https://github.com/leanprover-community/mathlib/pull/6815))
I tried a number of definitions and it looks like this is the least awkward one to prove with. In any case, using the API should allow you to avoid unfolding the definition.

### [2021-04-08 05:45:01](https://github.com/leanprover-community/mathlib/commit/def9671)
feat(group_theory/is_free_group): the property of being a free group ([#7086](https://github.com/leanprover-community/mathlib/pull/7086))

### [2021-04-08 03:58:52](https://github.com/leanprover-community/mathlib/commit/e8b217b)
chore(scripts): update nolints.txt ([#7098](https://github.com/leanprover-community/mathlib/pull/7098))
I am happy to remove some nolints for you!

### [2021-04-08 03:58:51](https://github.com/leanprover-community/mathlib/commit/b9d9bf0)
fix(.github/PULL_REQUEST_TEMPLATE.md): Fix the gitpod button link, looks like it moved with an update ([#7096](https://github.com/leanprover-community/mathlib/pull/7096))
I'll hold off for a couple of days on this as I'm not sure if the breakage was intentional or temporary on the gitpod side.

### [2021-04-08 00:15:24](https://github.com/leanprover-community/mathlib/commit/99c7d22)
chore(*): fixup docs that don't parse/cause linting errors ([#7088](https://github.com/leanprover-community/mathlib/pull/7088))
A couple docs had errors in the way that they were written, leading to them not displaying properly, or causing linting errors. This aims to make the [style_exceptions.txt](https://github.com/leanprover-community/mathlib/blob/master/scripts/style-exceptions.txt) file smaller, and also make the webdocs display them properly, c.f. [here](https://leanprover-community.github.io/mathlib_docs/topology/metric_space/basic.html).

### [2021-04-07 22:32:23](https://github.com/leanprover-community/mathlib/commit/c356c1f)
chore(ring_theory/tensor_product): golf proofs ([#7089](https://github.com/leanprover-community/mathlib/pull/7089))
Cherry-picked from [#4773](https://github.com/leanprover-community/mathlib/pull/4773), entirely written by @jcommelin

### [2021-04-07 22:32:22](https://github.com/leanprover-community/mathlib/commit/f4214de)
feat(measure_theory/group, measure_theory/bochner_integration): left translate of an integral ([#6936](https://github.com/leanprover-community/mathlib/pull/6936))
Translating a function on a topological group by left- (right-) multiplication by a constant does not change its integral with respect to a left- (right-) invariant measure.

### [2021-04-07 19:05:13](https://github.com/leanprover-community/mathlib/commit/68bd325)
feat(topology/category/Profinite): Profinite_to_Top creates limits. ([#7070](https://github.com/leanprover-community/mathlib/pull/7070))
This PR adds a proof that `Profinite` has limits by showing that the forgetful functor to `Top` creates limits.

### [2021-04-07 19:05:12](https://github.com/leanprover-community/mathlib/commit/08aff2c)
feat(algebra/big_operators/basic): edit `finset.sum/prod_range_succ` ([#6676](https://github.com/leanprover-community/mathlib/pull/6676))
- Change the RHS of the statement of `sum_range_succ` from `f n + ∑ x in range n, f x` to `∑ x in range n, f x + f n`
-  Change the RHS of the statement of `prod_range_succ` from `f n * ∑ x in range n, f x` to `∑ x in range n, f x * f n`
The old versions of those lemmas are now called `sum_range_succ_comm` and `prod_range_succ_comm`, respectively.
See [this conversation](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/break.20off.20last.20term.20of.20summation/near/229634503) on Zulip.

### [2021-04-07 15:23:49](https://github.com/leanprover-community/mathlib/commit/d76b649)
feat(dynamics/fixed_points/basic): fixed_points_id simp lemma ([#7078](https://github.com/leanprover-community/mathlib/pull/7078))

### [2021-04-07 15:23:48](https://github.com/leanprover-community/mathlib/commit/4a37c28)
feat(data/fintype/basic): set.to_finset_eq_empty_iff ([#7075](https://github.com/leanprover-community/mathlib/pull/7075))

### [2021-04-07 15:23:46](https://github.com/leanprover-community/mathlib/commit/c3c7c34)
feat(data/matrix/basic): dependently-typed block diagonal ([#7068](https://github.com/leanprover-community/mathlib/pull/7068))
This allows constructing block diagonal matrices whose blocks are different sizes. A notable example of such a matrix is the one from the Jordan Normal Form.
This duplicates all of the API for `block_diagonal` from this file. Most of the proofs copy across cleanly, but the proof for `block_diagonal_mul'` required lots of hand-holding that `simp` could solve by itself for the non-dependent case.

### [2021-04-07 15:23:45](https://github.com/leanprover-community/mathlib/commit/8459d0a)
feat(continuous_function/compact): lemmas characterising norm and dist ([#7054](https://github.com/leanprover-community/mathlib/pull/7054))
Transport lemmas charactering the norm and distance on bounded continuous functions, to continuous maps with compact domain.

### [2021-04-07 15:23:44](https://github.com/leanprover-community/mathlib/commit/919b4e3)
feat(algebra/category/Module): free module functor is lax monoidal ([#6906](https://github.com/leanprover-community/mathlib/pull/6906))

### [2021-04-07 15:23:43](https://github.com/leanprover-community/mathlib/commit/893173d)
feat(category/subobject): complete_lattice instance ([#6809](https://github.com/leanprover-community/mathlib/pull/6809))

### [2021-04-07 10:30:59](https://github.com/leanprover-community/mathlib/commit/9157b57)
refactor(topology/algebra/normed_group): generalize to semi_normed_group ([#7066](https://github.com/leanprover-community/mathlib/pull/7066))
The completion of a `semi_normed_group` is a `normed_group` (and similarly for `pseudo_metric_space`).

### [2021-04-07 10:30:58](https://github.com/leanprover-community/mathlib/commit/d89bfc4)
feat(field_theory/minpoly): remove `is_integral` requirement from `unique'` ([#7064](https://github.com/leanprover-community/mathlib/pull/7064))
`unique'` had an extraneous requirement on `is_integral`, which could be inferred from the other arguments.
This is a small step towards [#5258](https://github.com/leanprover-community/mathlib/pull/5258), but is a breaking change; `unique'` now needs one less argument, which will break all current code using `unique'`.

### [2021-04-07 10:30:56](https://github.com/leanprover-community/mathlib/commit/36649f8)
chore(linear_algebra/basic): add linear_map.one_eq_id ([#7063](https://github.com/leanprover-community/mathlib/pull/7063))
Cherry-picked from [#4773](https://github.com/leanprover-community/mathlib/pull/4773)

### [2021-04-07 10:30:55](https://github.com/leanprover-community/mathlib/commit/104fb22)
chore(logic/basic): generalize eq_iff_true_of_subsingleton to Sort ([#7061](https://github.com/leanprover-community/mathlib/pull/7061))

### [2021-04-07 10:30:54](https://github.com/leanprover-community/mathlib/commit/b8414e7)
feat(logic/function/basic): add injectivity/surjectivity of functions from/to subsingletons ([#7060](https://github.com/leanprover-community/mathlib/pull/7060))
In the surjective lemma (`function.surjective.to_subsingleton`), ~~I had to assume `Type*`, instead of `Sort*`, since I was not able to make the proof work in the more general case.~~ [Edit: Eric fixed the proof so that now they work in full generality.] 🎉
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/lemmas.20on.20int.20and.20subsingleton

### [2021-04-07 10:30:53](https://github.com/leanprover-community/mathlib/commit/df8ef37)
feat(data/int/basic algebra/associated): is_unit (a : ℤ) iff a = ±1 ([#7058](https://github.com/leanprover-community/mathlib/pull/7058))
Besides the title lemma, this PR also moves lemma `is_unit_int` from `algebra/associated` to `data/int/basic`.

### [2021-04-07 10:30:52](https://github.com/leanprover-community/mathlib/commit/a6024f1)
feat(archive/imo): formalize IMO 2008 Q4 ([#7039](https://github.com/leanprover-community/mathlib/pull/7039))
feat(archive/imo): formalize IMO 2008 Q4

### [2021-04-07 10:30:50](https://github.com/leanprover-community/mathlib/commit/7e71849)
feat(to_additive): copy _refl_lemma attribute ([#7011](https://github.com/leanprover-community/mathlib/pull/7011))
also warn user if if `simps` and `to_additive` are provided out of order.

### [2021-04-07 10:30:49](https://github.com/leanprover-community/mathlib/commit/c488997)
feat(analysis/special_functions/polynomial): polynomials are big O of polynomials of higher degree ([#6714](https://github.com/leanprover-community/mathlib/pull/6714))

### [2021-04-07 06:34:06](https://github.com/leanprover-community/mathlib/commit/05c491c)
feat(big_operators): single out one term from prod ([#7040](https://github.com/leanprover-community/mathlib/pull/7040))

### [2021-04-07 06:34:05](https://github.com/leanprover-community/mathlib/commit/ec6f5d1)
feat(data/*set): some finite sets lemmas ([#7037](https://github.com/leanprover-community/mathlib/pull/7037))

### [2021-04-07 06:34:04](https://github.com/leanprover-community/mathlib/commit/6048b6f)
feat(tactic/monotonicity): Allow `@[mono]` on `strict_mono` lemmas ([#7017](https://github.com/leanprover-community/mathlib/pull/7017))
A follow-up to [#3310](https://github.com/leanprover-community/mathlib/pull/3310)

### [2021-04-07 06:34:02](https://github.com/leanprover-community/mathlib/commit/21a96ef)
feat(ring_theory/hahn_series): summable families of Hahn series ([#6997](https://github.com/leanprover-community/mathlib/pull/6997))
Defines `hahn_series.summable_family`
Defines the formal sum `hahn_series.summable_family.hsum` and its linear map version, `hahn_series.summable_family.lsum`

### [2021-04-07 06:34:01](https://github.com/leanprover-community/mathlib/commit/6161a1f)
feat(category_theory/types): add explicit pullbacks in `Type u` ([#6973](https://github.com/leanprover-community/mathlib/pull/6973))
Add an explicit construction of binary pullbacks in the
category of types.
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/pullbacks.20in.20Type.20u

### [2021-04-07 02:18:23](https://github.com/leanprover-community/mathlib/commit/77e90da)
chore(scripts): update nolints.txt ([#7072](https://github.com/leanprover-community/mathlib/pull/7072))
I am happy to remove some nolints for you!

### [2021-04-07 02:18:22](https://github.com/leanprover-community/mathlib/commit/d904c8d)
chore(algebra/ring/prod): add missing `prod.distrib` instance ([#7069](https://github.com/leanprover-community/mathlib/pull/7069))

### [2021-04-07 02:18:21](https://github.com/leanprover-community/mathlib/commit/8b33d74)
chore(group_theory/specific_groups/*): new folder specific_groups ([#7018](https://github.com/leanprover-community/mathlib/pull/7018))
This creates a new folder `specific_groups` analogous to `analysis.special_functions`. So far, I have put `cyclic` (split from `order_of_element`), `dihedral`, and `quaternion` there.
Related Zulip discussion: 
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/group_theory.2Especific_groups

### [2021-04-07 02:18:20](https://github.com/leanprover-community/mathlib/commit/758d322)
feat(measure_theory/interval_integral): make integral_comp lemmas computable by simp ([#7010](https://github.com/leanprover-community/mathlib/pull/7010))
A follow-up to [#6795](https://github.com/leanprover-community/mathlib/pull/6795),  enabling the computation of integrals of the form `∫ x in a..b, f (c * x + d)` by `simp`, where `f` is a function whose integral is already in mathlib and `c` and `d` are any real constants such that `c ≠ 0`.

### [2021-04-07 02:18:19](https://github.com/leanprover-community/mathlib/commit/97832da)
chore(logic/function/basic): remove classical decidable instance from a lemma statement ([#6488](https://github.com/leanprover-community/mathlib/pull/6488))
Found using [#6485](https://github.com/leanprover-community/mathlib/pull/6485)
This means that this lemma can be use in reverse against any `ite`, not just one that uses `classical.decidable`.

### [2021-04-07 02:18:17](https://github.com/leanprover-community/mathlib/commit/a1057a3)
feat(data/finsum): sums over sets and types with no finiteness hypotheses ([#6355](https://github.com/leanprover-community/mathlib/pull/6355))
This rather large PR is mostly work of Jason KY. It is all an API for `finsum` and `finsum_in`, sums over sets with no finiteness assumption, and which return zero if the sum is infinite.

### [2021-04-06 18:32:51](https://github.com/leanprover-community/mathlib/commit/6ea4e9b)
feat(linear_algebra/eigenspace): generalized eigenvalues are just eigenvalues ([#7059](https://github.com/leanprover-community/mathlib/pull/7059))

### [2021-04-06 18:32:50](https://github.com/leanprover-community/mathlib/commit/9b4f0cf)
feat(data/basic/lean): add lemmas finset.subset_iff_inter_eq_{left, right} ([#7053](https://github.com/leanprover-community/mathlib/pull/7053))
These lemmas are the analogues of `set.subset_iff_inter_eq_{left, right}`, except stated for `finset`s.
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/finset.2Esubset_iff_inter_eq_left.20.2F.20right

### [2021-04-06 18:32:49](https://github.com/leanprover-community/mathlib/commit/6a9bf98)
doc(undergrad.yaml): add equiv.perm.trunc_swap_factors ([#7021](https://github.com/leanprover-community/mathlib/pull/7021))
This looks to me like the definition being asked for
```lean
def equiv.perm.trunc_swap_factors {α : Type u} [decidable_eq α] [fintype α] (f : equiv.perm α) :
trunc {l // l.prod = f ∧ ∀ (g : equiv.perm α), g ∈ l → g.is_swap}
```
I suppose the trunc could be considered a problem, but sorting the list is an easy way out, as is `trunc.out` for undergrads who don't care about computability.

### [2021-04-06 18:32:48](https://github.com/leanprover-community/mathlib/commit/aa5ec52)
feat(group_theory/perm/cycles): Applying cycle_of to an is_cycle ([#7000](https://github.com/leanprover-community/mathlib/pull/7000))
Applying cycle_of to an is_cycle gives you either the original cycle or 1.

### [2021-04-06 18:32:47](https://github.com/leanprover-community/mathlib/commit/ae6d77b)
feat(linear_algebra/free_module): a set of linearly independent vectors over a ring S is also linearly independent over a subring R of S ([#6993](https://github.com/leanprover-community/mathlib/pull/6993))
Zulip:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/.60algebra_map.2Einjective.2Elinear_independent.60

### [2021-04-06 18:32:46](https://github.com/leanprover-community/mathlib/commit/5f0dbf6)
feat(algebra/group/conj): `is_conj` for `monoid`s, `is_conj.setoid`, and `conj_classes` ([#6896](https://github.com/leanprover-community/mathlib/pull/6896))
Refactors `is_conj` to work in a `monoid`
Defines `is_conj.setoid` and its quotient type, `conj_classes`

### [2021-04-06 18:32:45](https://github.com/leanprover-community/mathlib/commit/41137fe)
feat(algebra/add_submonoid_closure): the additive closure of a multiplicative submonoid is a subsemiring ([#6860](https://github.com/leanprover-community/mathlib/pull/6860))
This file is extracted from PR [#6705](https://github.com/leanprover-community/mathlib/pull/6705)

### [2021-04-06 13:27:27](https://github.com/leanprover-community/mathlib/commit/5254ef1)
feat(topology/continuous_function): lemmas about coe ([#7055](https://github.com/leanprover-community/mathlib/pull/7055))

### [2021-04-06 13:27:25](https://github.com/leanprover-community/mathlib/commit/43aee09)
feat(algebra/pointwise): improve instances on `set_semiring` ([#7050](https://github.com/leanprover-community/mathlib/pull/7050))
If `α` is weaker than a semiring, then `set_semiring α` inherits an appropriate weaker typeclass.

### [2021-04-06 13:27:23](https://github.com/leanprover-community/mathlib/commit/7928ca0)
feat(algebra/lie/subalgebra): define the restriction of a Lie module to a Lie subalgebra ([#7036](https://github.com/leanprover-community/mathlib/pull/7036))

### [2021-04-06 13:27:20](https://github.com/leanprover-community/mathlib/commit/2b7b1e7)
refactor(algebra/group/inj_surj): eliminate the versions of the definitions without `has_div` / `has_sub`. ([#7035](https://github.com/leanprover-community/mathlib/pull/7035))
The variables without the `_sub` / `_div` suffix were vestigial definitions that existed in order to prevent the already-large `div_inv_monoid` refactor becoming larger. This change removes all their remaining usages, allowing the `_sub` / `_div` versions to lose their suffix.
This changes the division operation on `α →ₘ[μ] γ` and the subtraction operator on `truncated_witt_vector p n R` to definitionally match the division operation on their components. In practice, this just shuffles some uses of `sub_eq_add_neg` around.

### [2021-04-06 13:27:19](https://github.com/leanprover-community/mathlib/commit/0007c4a)
feat(topology/constructions): `function.update` is continuous in both arguments ([#7023](https://github.com/leanprover-community/mathlib/pull/7023))

### [2021-04-06 09:41:40](https://github.com/leanprover-community/mathlib/commit/d7f6bd6)
feat(data/finsupp,linear_algebra/finsupp): `finsupp`s and sum types ([#6992](https://github.com/leanprover-community/mathlib/pull/6992))
This PR contains a few definitions relating sum types and `finsupp`. The main result is `finsupp.sum_arrow_equiv_prod_arrow`, a `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. This is turned into a `linear_equiv` by `finsupp.sum_arrow_lequiv_prod_arrow`.

### [2021-04-06 09:41:39](https://github.com/leanprover-community/mathlib/commit/82b0b30)
refactor(analysis/normed_space/normed_group_hom): generalize to semi_normed_group ([#6977](https://github.com/leanprover-community/mathlib/pull/6977))
This is part of a series of PR to have the theory of `semi_normed_group` (and related concepts) in mathlib.
We generalize here `normed_group_hom` to `semi_normed_group` (keeping the old name to avoid too long names).
- [x] depends on: [#6910](https://github.com/leanprover-community/mathlib/pull/6910)

### [2021-04-06 09:41:37](https://github.com/leanprover-community/mathlib/commit/02058ed)
feat(group_theory/perm/*): facts about the cardinality of the support of a permutation ([#6951](https://github.com/leanprover-community/mathlib/pull/6951))
Proves lemmas about the cardinality of the support of a permutation

### [2021-04-06 09:41:36](https://github.com/leanprover-community/mathlib/commit/07aa34e)
feat(algebra/category/Module): compare concrete and abstract kernels ([#6938](https://github.com/leanprover-community/mathlib/pull/6938))

### [2021-04-06 09:41:35](https://github.com/leanprover-community/mathlib/commit/3a99001)
feat(category_theory): Type u is well-powered ([#6812](https://github.com/leanprover-community/mathlib/pull/6812))
A minor test of the `well_powered` API: we can verify that `Type u` is well-powered, and show `subobject α ≃o set α`.

### [2021-04-06 05:50:28](https://github.com/leanprover-community/mathlib/commit/2daf2ff)
chore(scripts): update nolints.txt ([#7052](https://github.com/leanprover-community/mathlib/pull/7052))
I am happy to remove some nolints for you!

### [2021-04-06 05:50:27](https://github.com/leanprover-community/mathlib/commit/6f38c14)
chore(data/finsupp/pointwise): add missing `finsupp.mul_zero_class` ([#7049](https://github.com/leanprover-community/mathlib/pull/7049))

### [2021-04-06 05:50:26](https://github.com/leanprover-community/mathlib/commit/aa665b1)
feat(linear_algebra/finsupp): add refl/trans/symm lemmas for dom_lcongr ([#7048](https://github.com/leanprover-community/mathlib/pull/7048))
These are just copies of the lemmas for `dom_congr`

### [2021-04-06 05:50:24](https://github.com/leanprover-community/mathlib/commit/8b34e00)
feat(order/complete_lattice): le_Sup and Inf_le iff lemmas ([#7047](https://github.com/leanprover-community/mathlib/pull/7047))

### [2021-04-06 05:50:21](https://github.com/leanprover-community/mathlib/commit/ba264c4)
chore(group_theory/group_action):  cleanup ([#7045](https://github.com/leanprover-community/mathlib/pull/7045))
Clean up stabilizers and add a missing simp lemma.

### [2021-04-06 05:50:21](https://github.com/leanprover-community/mathlib/commit/5312895)
chore(group_theory/order_of_element): move some lemmas ([#7031](https://github.com/leanprover-community/mathlib/pull/7031))
I moved a few lemmas to `group_theory.subgroup` and to `group_theory.coset` and to `data.finset.basic`. Feel free to suggest different locations if they don't quite fit. This resolves [#1563](https://github.com/leanprover-community/mathlib/pull/1563).
Renamed `card_trivial` to `subgroup.card_bot`

### [2021-04-06 05:50:20](https://github.com/leanprover-community/mathlib/commit/dbb2b55)
feat(measure_theory/interval_integral): more on integral_comp ([#7030](https://github.com/leanprover-community/mathlib/pull/7030))
I replace `integral_comp_mul_right_of_pos`, `integral_comp_mul_right_of_neg`, and `integral_comp_mul_right` with a single lemma.

### [2021-04-06 05:50:19](https://github.com/leanprover-community/mathlib/commit/82fd6e1)
feat(logic/girard): Girard's paradox  ([#7026](https://github.com/leanprover-community/mathlib/pull/7026))
A proof of Girard's paradox in lean, based on the LF proof: http://www.cs.cmu.edu/~kw/research/hurkens95tlca.elf

### [2021-04-06 05:50:18](https://github.com/leanprover-community/mathlib/commit/415b369)
feat(linear_algebra): `c ≤ dim K E` iff there exists a linear independent `s : set E`, `card s = c` ([#7014](https://github.com/leanprover-community/mathlib/pull/7014))

### [2021-04-06 05:50:17](https://github.com/leanprover-community/mathlib/commit/4192612)
chore(data/fintype/basic): add `card_unique` and a warning note to `card_of_subsingleton` ([#7008](https://github.com/leanprover-community/mathlib/pull/7008))

### [2021-04-06 05:50:16](https://github.com/leanprover-community/mathlib/commit/975f533)
chore(topology/continuous_function/algebra): add simp lemmas for smul coercion, move names out of global namespace ([#7007](https://github.com/leanprover-community/mathlib/pull/7007))
The two new lemmas proposed are:
- `continuous_map.smul_coe`
- `continuous_functions.smul_coe`

### [2021-04-06 05:50:15](https://github.com/leanprover-community/mathlib/commit/90e265e)
feat(algebra/category): the category of R-modules is well-powered ([#7002](https://github.com/leanprover-community/mathlib/pull/7002))

### [2021-04-06 05:50:13](https://github.com/leanprover-community/mathlib/commit/030a704)
feat(group_theory/perm/sign): Order of product of disjoint permutations ([#6998](https://github.com/leanprover-community/mathlib/pull/6998))
The order of the product of disjoint permutations is the lcm of the orders.

### [2021-04-06 05:50:12](https://github.com/leanprover-community/mathlib/commit/fe16235)
feat(category_theory): equivalences preserve epis and monos ([#6994](https://github.com/leanprover-community/mathlib/pull/6994))
Note that these don't follow from the results in `limits/constructions/epi_mono.lean`, since the results in that file are less universe polymorphic.

### [2021-04-06 05:50:11](https://github.com/leanprover-community/mathlib/commit/89ea423)
feat(archive/imo): formalize IMO 2005 Q3 ([#6984](https://github.com/leanprover-community/mathlib/pull/6984))
feat(archive/imo): formalize IMO 2005 Q3

### [2021-04-06 05:50:10](https://github.com/leanprover-community/mathlib/commit/b05affb)
chore(group_theory/subgroup): translate map comap lemmas from linear_map ([#6979](https://github.com/leanprover-community/mathlib/pull/6979))
Introduce the analogues of `linear_map.map_comap_eq` and `linear_map.comap_map_eq` to subgroups.
Also add `subgroup.map_eq_comap_of_inverse` which is a translation of `set.image_eq_preimage_of_inverse`.

### [2021-04-06 05:50:09](https://github.com/leanprover-community/mathlib/commit/6aa0e30)
feat(category_theory/preadditive): additive functors preserve biproducts ([#6882](https://github.com/leanprover-community/mathlib/pull/6882))
An additive functor between preadditive categories creates and preserves biproducts.
Also, renames `src/category_theory/abelian/additive_functor.lean` to `src/category_theory/preadditive/additive_functor.lean` as it so far doesn't actually rely on anything being abelian. 
Also, moves the `.map_X` lemmas about additive functors into the `functor` namespace, so we can use dot notation `F.map_add` etc, when `[functor.additive F]` is available.

### [2021-04-06 01:49:51](https://github.com/leanprover-community/mathlib/commit/4ddbdc1)
refactor(topology/sheaves): Refactor sheaf condition proofs ([#6962](https://github.com/leanprover-community/mathlib/pull/6962))
This PR adds two convenience Lemmas for working with the sheaf condition in terms of unique gluing and then uses them to greatly simplify the proofs of the sheaf condition for sheaves of functions (with and without a local predicate). Basically, all the categorical jargon gets outsourced and the actual proofs of the sheaf condition can now work in a very concrete setting. This drastically reduced the size of the proofs and eliminated any uses of `simp`.
Note that I'm effectively translating the sheaf condition from `Type` into a `Prop`, i.e. using `∃!` instead of using an instance of `unique`. I guess this diverts slightly from the original design in which the sheaf condition was always a `Type`. I found this to work quite well but maybe there is a way to phrase it differently.

### [2021-04-06 01:49:50](https://github.com/leanprover-community/mathlib/commit/1e1eaae)
feat(archive/imo): formalize IMO 2008 Q2 ([#6958](https://github.com/leanprover-community/mathlib/pull/6958))

### [2021-04-06 01:49:48](https://github.com/leanprover-community/mathlib/commit/0cc1fee)
feat(linear_algebra/finsupp): lemmas for finsupp_tensor_finsupp ([#6905](https://github.com/leanprover-community/mathlib/pull/6905))

### [2021-04-06 01:49:47](https://github.com/leanprover-community/mathlib/commit/108fa6f)
feat(order/bounded_lattice): min/max commute with coe ([#6900](https://github.com/leanprover-community/mathlib/pull/6900))
to with_bot and with_top

### [2021-04-06 01:49:46](https://github.com/leanprover-community/mathlib/commit/13f7910)
feat(category_theory/limits/kan_extension): Right and Left Kan extensions of a functor ([#6820](https://github.com/leanprover-community/mathlib/pull/6820))
This PR adds the left and right Kan extensions of a functor, and constructs the associated adjunction.
coauthored by @b-mehta 
A followup PR should prove that the adjunctions in this file are (co)reflective when \iota is fully faithful.
The current PR proves certain objects are initial/terminal, which will be useful for this.

### [2021-04-06 01:49:45](https://github.com/leanprover-community/mathlib/commit/8e2db7f)
refactor(order/boolean_algebra): generalized Boolean algebras ([#6775](https://github.com/leanprover-community/mathlib/pull/6775))
We add ["generalized Boolean algebras"](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations), following a [suggestion](https://github.com/leanprover-community/mathlib/pull/6469#issuecomment-787521935) of @jsm28. Now `boolean_algebra` extends `generalized_boolean_algebra` and `boolean_algebra.core`:
```lean
class generalized_boolean_algebra (α : Type u) extends semilattice_sup_bot α, semilattice_inf_bot α,
  distrib_lattice α, has_sdiff α :=
(sup_inf_sdiff : ∀a b:α, (a ⊓ b) ⊔ (a \ b) = a)
(inf_inf_sdiff : ∀a b:α, (a ⊓ b) ⊓ (a \ b) = ⊥)
class boolean_algebra.core (α : Type u) extends bounded_distrib_lattice α, has_compl α :=
(inf_compl_le_bot : ∀x:α, x ⊓ xᶜ ≤ ⊥)
(top_le_sup_compl : ∀x:α, ⊤ ≤ x ⊔ xᶜ)
class boolean_algebra (α : Type u) extends generalized_boolean_algebra α, boolean_algebra.core α :=
(sdiff_eq : ∀x y:α, x \ y = x ⊓ yᶜ)
```
I also added a module doc for `order/boolean_algebra`.
Many lemmas about set difference both for `finset`s and `set`s now follow from their `generalized_boolean_algebra` counterparts and I've removed the (fin)set-specific proofs.
`finset.sdiff_subset_self` was removed in favor of the near-duplicate `finset.sdiff_subset` (the latter has more explicit arguments).

### [2021-04-06 01:49:44](https://github.com/leanprover-community/mathlib/commit/61d2ad0)
chore(algebra/char_p/basic): uniformise notation and weaken some assumptions ([#6765](https://github.com/leanprover-community/mathlib/pull/6765))
I had looked at this file in an earlier PR and decided to come back to uniformise the notation, using always `R` and never `α` for the generic type of the file.
While I was at it, I started also changing
* some `semiring` assumptions to `add_monoid + has_one`,
* some `ring` assumptions to `add_group + has_one`.
In the long run, I think that the characteristic of a ring should be defined as the order of `1` in the additive submonoid, but this is not what I am doing at the moment!
Here is a related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/char_zero

### [2021-04-05 20:54:32](https://github.com/leanprover-community/mathlib/commit/1a45a56)
feat(logic/basic): subsingleton_of_not_nonempty ([#7043](https://github.com/leanprover-community/mathlib/pull/7043))
Also generalize `not_nonempty_iff_imp_false` to `Sort *`.

### [2021-04-05 15:31:11](https://github.com/leanprover-community/mathlib/commit/04af8ba)
feat(logic/small): instances for Pi and sigma types ([#7042](https://github.com/leanprover-community/mathlib/pull/7042))
Add some instances to prove basic type formers preserve smallness.

### [2021-04-05 15:31:10](https://github.com/leanprover-community/mathlib/commit/e0e56ee)
feat(tactic/simps): trace with @[simps?] ([#6995](https://github.com/leanprover-community/mathlib/pull/6995))
also trace with initialize_simps_projections?
trace when to_additive is applied to generated lemmas
with @[simps?] projection information is not printed (since that is often not as useful)

### [2021-04-05 12:18:25](https://github.com/leanprover-community/mathlib/commit/5be4463)
fix(fintype/basic): typo in docstring ([#7041](https://github.com/leanprover-community/mathlib/pull/7041))

### [2021-04-05 05:18:28](https://github.com/leanprover-community/mathlib/commit/d36d766)
chore(scripts): update nolints.txt ([#7038](https://github.com/leanprover-community/mathlib/pull/7038))
I am happy to remove some nolints for you!

### [2021-04-05 01:27:16](https://github.com/leanprover-community/mathlib/commit/530e7e3)
chore(data/quot): rename `nonempty_of_trunc` to enable dot notation ([#7034](https://github.com/leanprover-community/mathlib/pull/7034))

### [2021-04-04 21:07:11](https://github.com/leanprover-community/mathlib/commit/c7d7d83)
chore(data/nat): use notation `n!`, minor golf ([#7032](https://github.com/leanprover-community/mathlib/pull/7032))

### [2021-04-04 21:07:10](https://github.com/leanprover-community/mathlib/commit/92869e2)
chore(data/real/nnreal): use `function.injective.*` constructors ([#7028](https://github.com/leanprover-community/mathlib/pull/7028))

### [2021-04-04 14:00:36](https://github.com/leanprover-community/mathlib/commit/338331e)
feat(topology/urysohns_lemma): Urysohn's lemma ([#6967](https://github.com/leanprover-community/mathlib/pull/6967))

### [2021-04-04 11:19:18](https://github.com/leanprover-community/mathlib/commit/ee58d66)
feat(topology): variations on the intermediate value theorem ([#6789](https://github.com/leanprover-community/mathlib/pull/6789))

### [2021-04-04 06:41:15](https://github.com/leanprover-community/mathlib/commit/155b315)
chore(data/set/function): minor style fixes ([#7027](https://github.com/leanprover-community/mathlib/pull/7027))

### [2021-04-03 22:50:59](https://github.com/leanprover-community/mathlib/commit/44f34ee)
feat(group_theory/perm/sign): the alternating group ([#6913](https://github.com/leanprover-community/mathlib/pull/6913))
Defines `alternating_subgroup` to be `sign.ker`
Proves a few basic lemmas about its cardinality

### [2021-04-03 16:38:16](https://github.com/leanprover-community/mathlib/commit/a5b7de0)
chore(linear_algebra): fix/add `coe_fn` simp lemmas ([#7015](https://github.com/leanprover-community/mathlib/pull/7015))
* move `@[simp]` from `linear_map.comp_apply` to new
  `linear_map.coe_comp`;
* rename `linear_map.comp_coe` to `linear_map.coe_comp`, swap LHS&RHS;
* add `linear_map.coe_proj`, move `@[simp]` from `linear_map.proj_apply`.

### [2021-04-03 14:32:04](https://github.com/leanprover-community/mathlib/commit/fc87598)
chore(data/polynomial/eval): add `map_ring_hom_{id,comp}` lemmas ([#7019](https://github.com/leanprover-community/mathlib/pull/7019))

### [2021-04-03 11:15:54](https://github.com/leanprover-community/mathlib/commit/76a3b82)
feat(topology/sheaves/sheaf_condition): Sheaf condition in terms of unique gluing ([#6940](https://github.com/leanprover-community/mathlib/pull/6940))
As in
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Sheaf.20condition.20for.20type-valued.20sheaf
This PR adds an equivalent sheaf condition for type-valued presheaves, which is hopefully more "hands-on" and easier to work
with for concrete type-valued presheaves. I tried to roughly follow the design of the other sheaf conditions.

### [2021-04-03 11:15:53](https://github.com/leanprover-community/mathlib/commit/0041898)
feat(category_theory/preadditive): single_obj α is preadditive when α is a ring ([#6884](https://github.com/leanprover-community/mathlib/pull/6884))

### [2021-04-03 07:42:13](https://github.com/leanprover-community/mathlib/commit/51c9b60)
feat(category_theory/biproducts): additional lemmas ([#6881](https://github.com/leanprover-community/mathlib/pull/6881))

### [2021-04-03 03:51:07](https://github.com/leanprover-community/mathlib/commit/6c59845)
doc(algebra/module/basic): update module doc ([#7009](https://github.com/leanprover-community/mathlib/pull/7009))

### [2021-04-03 03:51:06](https://github.com/leanprover-community/mathlib/commit/eedc9da)
chore(linear_algebra/basic, algebra/lie/basic): fix erroneous doc string, add notation comment ([#7005](https://github.com/leanprover-community/mathlib/pull/7005))

### [2021-04-03 03:51:05](https://github.com/leanprover-community/mathlib/commit/b00d9be)
chore(data/finset/basic, ring_theory/hahn_series): mostly namespace changes ([#6996](https://github.com/leanprover-community/mathlib/pull/6996))
Added the line `open finset` and removed unneccesary `finset.`s from `ring_theory/hahn_series`
Added a small lemma to `data.finset.basic` that will be useful for an upcoming Hahn series PR

### [2021-04-03 03:51:03](https://github.com/leanprover-community/mathlib/commit/b630c51)
feat(category_theory/kernels): mild generalization of lemma ([#6930](https://github.com/leanprover-community/mathlib/pull/6930))
Relaxes some `is_iso` assumptions to `mono` or `epi`.
I've also added some TODOs about related generalizations and instances which could be provided. I don't intend to get to them immediately.

### [2021-04-03 03:51:02](https://github.com/leanprover-community/mathlib/commit/9c6fe3c)
feat(linear_algebra/bilinear_form): Bilinear form restricted on a subspace is nondegenerate under some condition ([#6855](https://github.com/leanprover-community/mathlib/pull/6855))
The main result is `restrict_nondegenerate_iff_is_compl_orthogonal` which states that: a subspace is complement to its orthogonal complement with respect to some bilinear form if and only if that bilinear form restricted on to the subspace is nondegenerate.
To prove this, I also introduced `dual_annihilator_comap`. This is a definition that allows us to treat the dual annihilator of a dual annihilator as a subspace in the original space.

### [2021-04-03 03:51:01](https://github.com/leanprover-community/mathlib/commit/2a9c21c)
feat(measure_theory/interval_integral): improve integral_comp lemmas ([#6795](https://github.com/leanprover-community/mathlib/pull/6795))
I expand our collection of `integral_comp` lemmas so that they can handle all interval integrals of the form
`∫ x in a..b, f (c * x + d)`, for any function `f : ℝ → E`  and any real constants `c` and `d` such that `c ≠ 0`.
This PR now also removes the `ae_measurable` assumptions from the preexisting `interval_comp` lemmas (thank you @sgouezel!).

### [2021-04-02 21:56:53](https://github.com/leanprover-community/mathlib/commit/36e5ff4)
feat(category_theory/with_term): formally adjoin terminal / initial objects. ([#6966](https://github.com/leanprover-community/mathlib/pull/6966))
Adds the construction which formally adjoins a terminal resp. initial object to a category.

### [2021-04-02 21:56:51](https://github.com/leanprover-community/mathlib/commit/267e660)
refactor(algebra/add_torsor): use `to_additive` for `add_action` ([#6914](https://github.com/leanprover-community/mathlib/pull/6914))

### [2021-04-02 21:56:50](https://github.com/leanprover-community/mathlib/commit/278ad33)
refactor(topology/metric_space/isometry): generalize to pseudo_metric ([#6910](https://github.com/leanprover-community/mathlib/pull/6910))
This is part of a series of PR to have the theory of `semi_normed_group` (and related concepts) in mathlib.
We generalize here `isometry` to `pseudo_emetric_space` and `pseudo_metric_space`.

### [2021-04-02 21:56:49](https://github.com/leanprover-community/mathlib/commit/cb1e888)
feat(category_theory/limits): is_iso_π_of_is_initial ([#6908](https://github.com/leanprover-community/mathlib/pull/6908))
From [zulip](https://leanprover.zulipchat.com/#narrow/stream/267928-condensed-mathematics/topic/Simplicial.20stuff/near/231346653)

### [2021-04-02 21:56:48](https://github.com/leanprover-community/mathlib/commit/fe4ea3d)
chore(docs/undergrad.yaml): a few updates to the undergrad list ([#6904](https://github.com/leanprover-community/mathlib/pull/6904))
Adds entries for Schur's Lemma and several infinite series concepts

### [2021-04-02 21:56:47](https://github.com/leanprover-community/mathlib/commit/7b52617)
feat(data/nat/multiplicity): weaken hypothesis on set bounds ([#6903](https://github.com/leanprover-community/mathlib/pull/6903))

### [2021-04-02 16:17:31](https://github.com/leanprover-community/mathlib/commit/fead60f)
chore(data/finsupp/basic): add a lemma for `map_domain` applied to equivs ([#7001](https://github.com/leanprover-community/mathlib/pull/7001))

### [2021-04-02 09:16:15](https://github.com/leanprover-community/mathlib/commit/394719f)
chore(data/finsupp): lemmas about map_range and map_domain ([#6976](https://github.com/leanprover-community/mathlib/pull/6976))
This proves some functorial properties:
* `finsupp.map_range_id`
* `finsupp.map_range_comp`
Adds the new definitions to match `finsupp.map_range.add_monoid_hom`, and uses them to golf some proofs:
* `finsupp.map_range.zero_hom`, which is `map_domain` as a `zero_hom`
* `finsupp.map_range.add_equiv`, which is `map_range` as an `add_equiv`
* `finsupp.map_range.linear_map`, which is `map_range` as a `linear_map`
* `finsupp.map_range.linear_equiv`, which is `map_range` as a `linear_equiv`
* `finsupp.map_domain.add_monoid_hom`, which is `map_domain` as an `add_monoid_hom`
Shows the functorial properties of these bundled definitions:
* `finsupp.map_range.zero_hom_id`, `finsupp.map_range.zero_hom_comp`
* `finsupp.map_range.add_monoid_hom_id`, `finsupp.map_range.add_monoid_hom_comp`
* `finsupp.map_range.add_equiv_refl`, `finsupp.map_range.add_equiv_trans`
* `finsupp.map_range.linear_map_id`, `finsupp.map_range.linear_map_comp`
* `finsupp.map_range.linear_equiv_refl`, `finsupp.map_range.linear_equiv_trans`
* `finsupp.map_domain.add_monoid_hom_id`, `finsupp.map_domain.add_monoid_hom_comp`
And shows that `map_range` and `map_domain` commute when the range-map preserves addition:
* `finsupp.map_domain_map_range`

### [2021-04-02 08:15:10](https://github.com/leanprover-community/mathlib/commit/6e5c07b)
feat(category_theory/subobject): well-powered categories ([#6802](https://github.com/leanprover-community/mathlib/pull/6802))

### [2021-04-02 04:59:38](https://github.com/leanprover-community/mathlib/commit/19483ae)
feat(data/finset): inj on of image card eq ([#6785](https://github.com/leanprover-community/mathlib/pull/6785))

### [2021-04-02 01:20:16](https://github.com/leanprover-community/mathlib/commit/7337702)
feat(data/equiv/fintype): computable bijections and perms from/to fintype ([#6959](https://github.com/leanprover-community/mathlib/pull/6959))
Using exhaustive search, we can upgrade embeddings from fintypes into
equivs, and transport perms across embeddings. The computational
performance is poor, so the docstring suggests alternatives when an
explicit inverse is known.

### [2021-04-01 18:49:17](https://github.com/leanprover-community/mathlib/commit/d8de567)
feat(group_theory/order_of_element): generalised to add_order_of ([#6770](https://github.com/leanprover-community/mathlib/pull/6770))
This PR defines `add_order_of` for an additive monoid. If someone sees how to do this with more automation, let me know. 
This gets one step towards closing issue [#1563](https://github.com/leanprover-community/mathlib/pull/1563).
Coauthored by: Yakov Pechersky @pechersky

### [2021-04-01 17:47:25](https://github.com/leanprover-community/mathlib/commit/1e27fba)
admin(README.md): add @adamtopaz to the maintainers list ([#6987](https://github.com/leanprover-community/mathlib/pull/6987))

### [2021-04-01 17:47:24](https://github.com/leanprover-community/mathlib/commit/c35e9f6)
admin(README.md): add @b-mehta to the maintainers list ([#6986](https://github.com/leanprover-community/mathlib/pull/6986))

### [2021-04-01 17:47:23](https://github.com/leanprover-community/mathlib/commit/cea8c65)
feat(algebra/char_p/exp_char): basics about the exponential characteristic ([#6671](https://github.com/leanprover-community/mathlib/pull/6671))
This file contains the definition and a few basic facts pertaining to the exponential characteristic of an integral domain.

### [2021-04-01 15:06:29](https://github.com/leanprover-community/mathlib/commit/396602b)
feat(algebra/module/hom): Add missing smul instances on add_monoid_hom ([#6891](https://github.com/leanprover-community/mathlib/pull/6891))
These are defeq to the smul instances on `linear_map`, in `linear_algebra/basic.lean`.

### [2021-04-01 13:55:22](https://github.com/leanprover-community/mathlib/commit/a690ce7)
admin(README.md): add @TwoFX to the maintainers list ([#6985](https://github.com/leanprover-community/mathlib/pull/6985))

### [2021-04-01 12:44:31](https://github.com/leanprover-community/mathlib/commit/132ae2b)
fix(algebraic_topology): fix a typo ([#6991](https://github.com/leanprover-community/mathlib/pull/6991))

### [2021-04-01 09:03:10](https://github.com/leanprover-community/mathlib/commit/a9b6230)
feat(combinatorics/quiver): weakly connected components ([#6847](https://github.com/leanprover-community/mathlib/pull/6847))
Define composition of paths and the weakly connected components of a directed graph. Two vertices are in the same weakly connected component if there is a zigzag of arrows from one to the other.

### [2021-04-01 05:03:20](https://github.com/leanprover-community/mathlib/commit/21cc806)
feat(data/equiv/basic): `perm_congr` group lemmas ([#6982](https://github.com/leanprover-community/mathlib/pull/6982))

### [2021-04-01 01:24:57](https://github.com/leanprover-community/mathlib/commit/3365c44)
feat(data/equiv/basic): `equiv.swap_eq_refl_iff` ([#6983](https://github.com/leanprover-community/mathlib/pull/6983))

### [2021-04-01 01:24:56](https://github.com/leanprover-community/mathlib/commit/64abe48)
refactor(topology/metric_space/pi_Lp): generalize to pseudo_metric ([#6978](https://github.com/leanprover-community/mathlib/pull/6978))
We generalize here the Lp distance to `pseudo_emetric` and similar concepts.

### [2021-04-01 01:24:55](https://github.com/leanprover-community/mathlib/commit/b7fbc17)
chore(data/equiv/add_equiv): missing simp lemmas ([#6975](https://github.com/leanprover-community/mathlib/pull/6975))
These lemmas already exist for `equiv`, this just copies them to `add_equiv`.

### [2021-04-01 01:24:54](https://github.com/leanprover-community/mathlib/commit/e540c2f)
feat(data/set/basic): default_coe_singleton ([#6971](https://github.com/leanprover-community/mathlib/pull/6971))

### [2021-04-01 01:24:53](https://github.com/leanprover-community/mathlib/commit/ec9476f)
chore(data/fintype/basic): add card_le_of_surjective and card_quotient_le ([#6964](https://github.com/leanprover-community/mathlib/pull/6964))
Add two natural lemmas that were missing from `fintype.basic`.

### [2021-04-01 01:24:52](https://github.com/leanprover-community/mathlib/commit/71c3e71)
refactor(topology/bases): use `structure` for `is_topological_basis ([#6947](https://github.com/leanprover-community/mathlib/pull/6947))
* turn `topological_space.is_topological_basis` into a `structure`;
* rename `mem_nhds_of_is_topological_basis` to `is_topological_basis.mem_nhds_iff`;
* rename `is_open_of_is_topological_basis` to `is_topological_basis.is_open`;
* rename `mem_basis_subset_of_mem_open` to `is_topological_basis.exists_subset_of_mem_open`;
* rename `sUnion_basis_of_is_open` to `is_topological_basis.open_eq_sUnion`, add prime version;
* add `is_topological_basis.prod`;
* add convenience lemma `is_topological_basis.second_countable_topology`;
* rename `is_open_generated_countable_inter` to `exists_countable_basis`;
* add `topological_space.countable_basis` and API around it;
* add `@[simp]` to `opens.mem_supr`, add `opens.mem_Sup`;
* golf